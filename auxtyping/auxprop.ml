open Language
open Zutils

let smart_dependent_forall (x, { nty; phi; _ }) query =
  (* if we have an eqv relation, then any potential value satisfying phi 
     is still possible, so we ignore the eqv relation *)
  let phi = subst_prop_instance default_v (AVar x#:nty) phi in
  smart_forall_phi (x#:nty, phi) query

let smart_dependent_exists (x, { nty; phi; _ }) query =
  (* TODO: check if this is valid in the eqv case *)
  let phi = subst_prop_instance default_v (AVar x#:nty) phi in
  smart_exists_phi (x#:nty, phi) query
