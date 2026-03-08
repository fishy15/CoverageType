open Language
open Zutils

let smart_dependent_forall (x, { nty; phi; eqv }) query =
  match eqv with
  | None ->
      let phi = subst_prop_instance default_v (AVar x#:nty) phi in
      smart_forall_phi (x#:nty, phi) query
  | _ -> _die_with [%here] "eqv unimpl"

let smart_dependent_exists (x, { nty; phi; eqv }) query =
  match eqv with
  | None ->
      let phi = subst_prop_instance default_v (AVar x#:nty) phi in
      (* let query = fresh_name_prop query in *)
      (* Exists { qv = x#:nty; body = smart_add_to phi query } *)
      smart_exists_phi (x#:nty, phi) query
  | _ -> _die_with [%here] "eqv unimpl"
