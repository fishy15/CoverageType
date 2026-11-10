open Prop
open Zutils
open Zdatatype

let product_map (f : 'a -> 'b list) (xs : 'a list) : 'b list list =
  let rec aux = function
    | [] -> [ [] ]
    | x :: xs ->
        let rest = aux xs in
        let vs = f x in
        List.concat_map (fun v -> List.map (fun r -> v :: r) rest) vs
  in
  aux xs

let dup_tys ty n =
  match ty with
  | Nt.Ty_constructor (name, args) ->
      List.init n (fun i -> Nt.Ty_constructor (spf "%s_%d" name i, args))
  | _ -> _die [%here]

let get_all_type_substs ty new_tys nt =
  let open Nt in
  let ( let* ) x f = List.concat_map f x in
  let return x = [ x ] in
  let rec aux nt =
    match nt with
    | _ when equal_nt nt ty -> new_tys
    | Ty_constructor (name, args) ->
        let* args = product_map aux args in
        return @@ Ty_constructor (name, args)
    | Ty_arrow (a, b) ->
        let* a = aux a in
        let* b = aux b in
        return @@ Ty_arrow (a, b)
    | Ty_tuple l ->
        let* l = product_map aux l in
        return @@ Ty_tuple l
    | Ty_record { alias; fds } ->
        let conv_field fd =
          let* ty = aux fd.ty in
          return @@ { fd with ty }
        in
        let* fds = product_map conv_field fds in
        return @@ Ty_record { alias; fds }
    | Ty_poly (y, body) ->
        let* body = aux body in
        return @@ Ty_poly (y, body)
    | _ -> return nt
  in
  aux nt

(* all the variables have been substituted, but the functions still have the argument types.
   since the return type cannot be the current type we are replacing, we can leave it the same *)
let rec fix_lit = function
  | (AC _ | AVar _) as x -> x
  | ATu l -> ATu (List.map fix_typed_lit l)
  | AProj (l, i) -> AProj (fix_typed_lit l, i)
  | ARecord fds -> ARecord (List.map (fun (n, l) -> (n, fix_typed_lit l)) fds)
  | AField (l, n) -> AField (fix_typed_lit l, n)
  | AAppOp (f, args) ->
      let args = List.map fix_typed_lit args in
      let _, retty = Nt.destruct_arr_tp f.ty in
      let arg_tys = List.map (fun arg -> arg.ty) args in
      let fty = Nt.construct_arr_tp (arg_tys, retty) in
      AAppOp ({ f with ty = fty }, args)

and fix_typed_lit lit = lit_to_tlit (fix_lit lit.x)

let multi_subst_prop ty new_tys prop =
  let ( let* ) x f = List.concat_map f x in
  let return x = [ x ] in
  let rec aux_qv constructor qv body =
    let* new_ty = get_all_type_substs ty new_tys qv.ty in
    let new_qv = { qv with ty = new_ty } in
    let body = subst_prop_instance qv.x (AVar new_qv) body in
    let* body = aux body in
    return @@ constructor new_qv body
  and aux = function
    | Lit lit -> return @@ Lit (fix_typed_lit lit)
    | Forall { qv; body } -> aux_qv (fun qv body -> Forall { qv; body }) qv body
    | Exists { qv; body } -> aux_qv (fun qv body -> Exists { qv; body }) qv body
    | Implies (p1, p2) ->
        let* p1 = aux p1 in
        let* p2 = aux p2 in
        return @@ Implies (p1, p2)
    | Ite (p1, p2, p3) ->
        let* p1 = aux p1 in
        let* p2 = aux p2 in
        let* p3 = aux p3 in
        return @@ Ite (p1, p2, p3)
    | Iff (p1, p2) ->
        let* p1 = aux p1 in
        let* p2 = aux p2 in
        return @@ Iff (p1, p2)
    | Not p ->
        let* p = aux p in
        return @@ Not p
    | And ps ->
        let* ps = product_map aux ps in
        return @@ And ps
    | Or ps ->
        let* ps = product_map aux ps in
        return @@ Or ps
  in
  aux prop

let nt_mentions ty nt =
  Nt.fold_nt (fun acc nt -> acc || Nt.equal_nt nt ty) false nt

let returns_ty ty prop =
  fold_prop
    (fun acc -> function
      | Lit { x = AAppOp (f, _); _ } ->
          let _, retty = Nt.destruct_arr_tp f.ty in
          acc || nt_mentions ty retty
      | _ -> acc)
    false prop

let check_eq_calls prop =
  let equality_fns = [ "=="; "!=" ] in
  let is_eq_fn fn = List.exists (String.equal fn) equality_fns in
  fold_prop
    (fun acc -> function
      | Lit { x = AAppOp (f, args); ty = retty } when is_eq_fn f.x -> (
          match args with
          | [ arg1; arg2 ] ->
              acc && Nt.equal_nt arg1.ty arg2.ty && Nt.equal_nt retty Nt.bool_ty
          | _ -> false)
      | _ -> acc)
    true prop

let duplicate_axiom_for_ty ty (name, prop) =
  (* for now, we skip duplicating axioms which contain a function
    that returns the type we are duplicating, for simplicitly *)
  if returns_ty ty prop then []
  else
    let new_props = multi_subst_prop ty (dup_tys ty 2) prop in
    let new_props = List.filter check_eq_calls new_props in
    List.mapi
      (fun i p -> (spf "%s_%s_%d" name (Nt.layout_nt ty) i, p))
      new_props

let duplicate_axiom (name, prop) =
  let qv_tys =
    fold_prop
      (fun acc -> function
        | Forall { qv; _ } | Exists { qv; _ } -> qv.ty :: acc | _ -> acc)
      [] prop
  in
  let retrieve_constructors =
    Nt.fold_nt
      (fun acc -> function
        | Ty_constructor _ as ty
          when not (List.exists (Nt.equal_nt ty) Nt.builtin_base_nts) ->
            ty :: acc
        | _ -> acc)
      []
  in
  let qv_tys =
    List.concat_map retrieve_constructors qv_tys |> List.slow_rm_dup Nt.equal_nt
  in
  let res =
    List.concat_map (fun ty -> duplicate_axiom_for_ty ty (name, prop)) qv_tys
  in
  ( TypecheckerLog.preprocess @@ fun _ ->
    Pp.printf "duplicating for %s: %s\n" name (layout_prop prop);
    Pp.printf "types to dupl: ";
    List.iter (fun ty -> Pp.printf "%s " (Nt.layout ty)) qv_tys;
    Pp.printf "\n";
    List.iter
      (fun (name, prop) ->
        Pp.printf "dupl %s ::: %s\n" name (layout_prop_source prop))
      res );
  res
