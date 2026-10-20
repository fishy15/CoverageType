open Ast
open Prop
open Sugar

let gated_axiom_of_prop ~measure prop =
  let rec aux = function
    | Forall { qv; body } ->
        let inps, retty = aux body in
        (qv :: inps, retty)
    | _ -> ([], prop)
  in
  let inputs, prop = aux prop in
  let output, prop =
    match prop with
    | Exists { qv; body } -> (qv, body)
    | _ -> _die_with [%here] "gated axiom must have an output"
  in
  _assert [%here]
    "gated axiom should be some inputs (forall) followed by one output \
     (exists) only"
    (not (has_quantifiers prop));
  { measure; inputs; output; phi = prop }

let gated_axiom_of_expr ~measure expr =
  let prop = prop_of_expr expr in
  gated_axiom_of_prop ~measure prop

let gated_axiom_to_prop { inputs; output; phi; _ } =
  Exists { qv = output; body = phi }
  |> List.fold_right (fun qv acc -> Forall { qv; body = acc }) inputs

let layout_gated_axiom axiom = layout_prop (gated_axiom_to_prop axiom)
