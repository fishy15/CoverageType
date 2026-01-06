open Language
open Zutils

let eqv_prop eqv x y =
  let nty =
    if Nt.equal_nt x.ty y.ty then x.ty
    else _die_with [%here] "eqv_prop: type mismatch"
  in
  let args = List.map tvar_to_lit [ x; y ] in
  let functy = Nt.Ty_arrow (nty, Nt.Ty_arrow (nty, Nt.bool_ty)) in
  lit_to_prop (AAppOp (eqv#:functy, args))

let eqv_to_phi nty phi eqv =
  let phi = subst_prop_instance default_v (AVar default_v'#:nty) phi in
  let eqv_call = eqv_prop eqv default_v#:nty default_v'#:nty in
  smart_exists_phi (default_v'#:nty, eqv_call) phi
