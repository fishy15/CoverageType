open Language
open Zutils

(* solver already knows that all values exist, so we can optimize out the existential *)
let no_exists_needed_ty rty =
  match rty with
  | RtyBase { cty = { nty; _ }; _ } ->
      nty = Nt.int_ty || nty = Nt.bool_ty || nty = Nt.nat_ty || nty = Nt.char_ty
      || nty = Nt.float_ty
  | _ -> false

let exists_fresh_v_prop cty =
  let { phi = prop; nty; eqv } = cty in
  let var = (Rename.different_var default_v)#:nty in
  let prop = subst_prop_instance default_v (AVar var) prop in
  match eqv with
  | None -> Exists { qv = var; body = prop }
  | Some eqv ->
      let var' = (Rename.different_var default_v)#:nty in
      let prop = subst_prop_instance default_v (AVar var) prop in
      let eqv_prop = Eqv.eqv_prop eqv var var' in
      smart_forall_phi (var, prop) @@ Exists { qv = var'; body = eqv_prop }

let remove_duplicates xs =
  let rec aux acc xs =
    match xs with
    | [] -> List.rev acc
    | x :: xs -> if List.mem x acc then aux acc xs else aux (x :: acc) xs
  in
  aux [] xs

let relevant_fvs_in_ctx rty_ctx rty =
  let rec aux varname rty acc =
    match varname with
    | Some name when List.mem_assoc name acc -> acc
    | _ ->
        let acc =
          match varname with Some name -> (name, rty) :: acc | None -> acc
        in
        let fvs = remove_duplicates (fv_rty rty) in
        let fvs =
          List.filter
            (fun fv -> match varname with Some x -> x <> fv.x | None -> true)
            fvs
        in
        List.fold_left
          (fun acc fv ->
            match Typectx.get_opt rty_ctx fv.x with
            | Some rty -> aux (Some fv.x) rty acc
            | None -> _die_with [%here] (spf "cannot find %s in rty ctx\n" fv.x))
          acc fvs
  in
  aux None rty [] |> List.map (fun (x, rty) -> x#:rty)

let constrain_by_fvs fvs prop =
  let fv_prop =
    List.fold_left
      (fun acc fv ->
        let { ty = { phi; _ }; _ } = fv in
        let phi = subst_prop_instance default_v (AVar fv#=>erase_cty) phi in
        smart_and [ acc; phi ])
      Prop.mk_true fvs
  in
  let prop = smart_implies fv_prop prop in
  List.fold_left
    (fun acc { x; ty } ->
      let fv = x#:(erase_cty ty) in
      Forall { qv = fv; body = acc })
    prop fvs

let construct_call_ret_exists rctx localctx retty =
  if no_exists_needed_ty retty then Prop.mk_true
  else
    (* prefer local context over global context *)
    let rty_ctx = Typectx.concat_update rctx.rty_ctx localctx intersect_rty in
    let fvs = relevant_fvs_in_ctx rty_ctx retty in
    let under_fvs_ctys =
      List.filter_map
        (fun { x; ty } ->
          match ty with RtyBase { ou = Under; cty } -> Some x#:cty | _ -> None)
        fvs
    in
    let retcty =
      match retty with
      | RtyBase { ou = Under; cty } -> cty
      | _ -> _die_with [%here] "unimp"
    in
    let prop = exists_fresh_v_prop retcty in
    fresh_name_prop @@ constrain_by_fvs under_fvs_ctys prop
