open Ast
open Prop
open Sugar
open Zdatatype
open Preprocess

let measure = "measure"
let dup_level_sort ty level = List.nth (Duplication.dup_tys ty 2) level
let level0_sort ty = dup_level_sort ty 0
let level1_sort ty = dup_level_sort ty 1

let retype_var x new_x prop =
  subst_prop_instance x (AVar new_x) prop |> map_prop_lit Duplication.fix_lit

let freshen_and_retype_var x ty prop =
  let new_x = (Rename.unique_var x)#:ty in
  (new_x, retype_var x new_x prop)

let is_relevant_axiom { output; _ } ~ty = Nt.equal_nt output.ty ty

let get_relevant_gated_axioms { gated_axioms; _ } ~ty =
  StrMap.to_kv_list gated_axioms
  |> List.filter (fun (_, ax) -> is_relevant_axiom ax ~ty)

let measure_call { x; ty } =
  let measure = measure#:Nt.(mk_arr ty int_ty) in
  let input_lit = (AVar x#:ty)#:ty in
  (AAppOp (measure, [ input_lit ]))#:Nt.int_ty

let cmp op x y =
  let op = match op with `Eq -> "==" | `Geq -> ">=" | `Lt -> "<" in
  let op = op#:Nt.(mk_arr int_ty (mk_arr int_ty bool_ty)) in
  lit_to_prop @@ AAppOp (op, [ x; y ])

let bound_v_by_sz op x sz =
  let measure_value = measure_call x in
  let sz_lit = int_var sz in
  cmp op measure_value sz_lit

let instantiate_gated_axiom { inputs; output; phi } bound_var =
  let add_input input prop =
    if Nt.equal_nt input.ty output.ty then
      let input', prop =
        freshen_and_retype_var input.x (level0_sort input.ty) prop
      in
      smart_forall_phi (input', bound_v_by_sz `Lt input' bound_var) prop
    else
      let input', prop = freshen_prop_typed_instance input prop in
      Forall { qv = input'; body = prop }
  in
  let output', phi =
    freshen_and_retype_var output.x (level1_sort output.ty) phi
  in
  List.fold_right add_input inputs @@ Exists { qv = output'; body = phi }

let geq_zero v =
  let zero = (AC (I 0))#:Nt.int_ty in
  let v_lit = int_var v in
  cmp `Geq v_lit zero

let assume_smaller_exist_prop vty prop bound_var =
  let smaller_bound_var, prop = freshen_prop_instance bound_var prop in
  let v, prop = freshen_and_retype_var default_v (level0_sort vty) prop in
  let prop = smart_and [ bound_v_by_sz `Eq v smaller_bound_var; prop ] in
  fresh_name_prop
  @@ smart_forall_phi
       ( smaller_bound_var#:Nt.int_ty,
         smart_and
           [
             geq_zero smaller_bound_var;
             cmp `Lt (int_var smaller_bound_var) (int_var bound_var);
           ] )
       (Exists { qv = v; body = prop })

let assert_no_free_vars_of_ty ~vty prop =
  let others =
    fv_prop prop
    |> List.filter (fun x ->
           Nt.equal_nt x.ty vty && not (String.equal x.x default_v))
    |> List.map (fun x -> x.x)
  in
  Zutils._assert [%here]
    (Printf.sprintf
       "free variables of type %s other than %s would need to be at level 0: %s"
       (Nt.layout_nt vty) default_v
       (String.concat ", " others))
    (List.is_empty others)

(* Move every context variable of type [vty] to level 0, including inside the
   refinements that mention them. *)
let level0_ctx ~vty ctx =
  let level0 = level0_sort vty in
  let ctx_vars =
    List.filter_map
      (fun (x, cty) -> if Nt.equal_nt cty.nty vty then Some x else None)
      ctx
  in
  let to_level0 phi =
    List.fold_left (fun phi x -> retype_var x x#:level0 phi) phi ctx_vars
  in
  List.map
    (fun (x, cty) ->
      if Nt.equal_nt cty.nty vty then
        (* [default_v] has type [vty] only in the refinement of a [vty] entry *)
        let phi = retype_var default_v default_v#:level0 (to_level0 cty.phi) in
        (x, { nty = level0; phi })
      else (x, { cty with phi = to_level0 cty.phi }))
    ctx

let gate_with_axioms bctx prop ~measure_arg ~vty =
  assert_no_free_vars_of_ty ~vty prop;
  let bound_var, prop = freshen_prop_instance measure_arg prop in
  let axioms =
    get_relevant_gated_axioms bctx ~ty:vty
    |> List.map (fun (_, ax) -> instantiate_gated_axiom ax bound_var)
  in
  let smaller_prop = assume_smaller_exist_prop vty prop bound_var in
  let exists_v_of_sort sort =
    let v, prop = freshen_and_retype_var default_v sort prop in
    let prop = fresh_name_prop prop in
    smart_exists_phi (v, bound_v_by_sz `Eq v bound_var) prop
  in
  let prop =
    smart_or
      [
        exists_v_of_sort (level0_sort vty); exists_v_of_sort (level1_sort vty);
      ]
  in
  let prop = smart_implies (smart_and (smaller_prop :: axioms)) prop in
  smart_forall_phi (bound_var#:Nt.int_ty, geq_zero bound_var) prop
