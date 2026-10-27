open Ast
open Prop
open Sugar
open Zdatatype

let measure_var = "_sz"

let is_relevant_axiom { measure = m; output; _ } ~measure ~ty =
  String.equal measure m && Nt.equal_nt output.ty ty

let get_relevant_gated_axioms { gated_axioms; _ } ~measure ~ty =
  StrMap.to_kv_list gated_axioms
  |> List.filter (fun (_, ax) -> is_relevant_axiom ax ~measure ~ty)

let measure_call measure { x; ty } =
  let measure = measure#:Nt.(mk_arr ty int_ty) in
  let input_lit = (AVar x#:ty)#:ty in
  (AAppOp (measure, [ input_lit ]))#:Nt.int_ty

let cmp op x y =
  let op = match op with `Eq -> "==" | `Geq -> ">=" | `Lt -> "<" in
  let op = op#:Nt.(mk_arr int_ty (mk_arr int_ty bool_ty)) in
  lit_to_prop @@ AAppOp (op, [ x; y ])

let bound_v_by_sz op measure x sz =
  let measure_value = measure_call measure x in
  let sz_lit = int_var sz in
  cmp op measure_value sz_lit

let instantiate_gated_axiom { measure; inputs; output; phi } bound_var =
  let add_input input prop =
    let input', prop = freshen_prop_typed_instance input prop in
    if Nt.equal_nt input'.ty output.ty then
      smart_forall_phi (input', bound_v_by_sz `Lt measure input' bound_var) prop
    else Forall { qv = input'; body = prop }
  in
  List.fold_right add_input inputs @@ Exists { qv = output; body = phi }

let geq_zero v =
  let zero = (AC (I 0))#:Nt.int_ty in
  let v_lit = int_var v in
  cmp `Geq v_lit zero

let assume_smaller_exist_prop measure vty prop bound_var =
  let bound_var' = Rename.unique_var measure_var in
  let v, prop = freshen_prop_typed_instance default_v#:vty prop in
  let prop = smart_and [ bound_v_by_sz `Eq measure v bound_var'; prop ] in
  smart_forall_phi
    ( bound_var'#:Nt.int_ty,
      smart_and
        [
          geq_zero bound_var'; cmp `Lt (int_var bound_var') (int_var bound_var);
        ] )
    (Exists { qv = v; body = prop })

let gate_with_axioms bctx prop ~measure ~vty =
  let bound_var = Rename.unique_var measure_var in
  let axioms =
    get_relevant_gated_axioms bctx ~measure ~ty:vty
    |> List.map (fun (_, ax) -> instantiate_gated_axiom ax bound_var)
  in
  let smaller_prop = assume_smaller_exist_prop measure vty prop bound_var in
  let v, prop = freshen_prop_typed_instance default_v#:vty prop in
  let bound_v = bound_v_by_sz `Eq measure v bound_var in
  let prop = smart_exists_phi (v, bound_v) prop in
  let prop = smart_implies (smart_and (smaller_prop :: axioms)) prop in
  smart_forall_phi (bound_var#:Nt.int_ty, geq_zero bound_var) prop
