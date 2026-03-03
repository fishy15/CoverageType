open Language
open Zutils

let exists_fresh_v_prop cty =
  let prop, nty = (cty.phi, cty.nty) in
  let var = Rename.fresh_var () in
  let var = var#:nty in
  let prop = subst_prop_instance default_v (AVar var) prop in
  Exists { qv = var; body = prop }

let possible_value_fv prop fv fvrty =
  let fv = fv.x in
  match fvrty with
  | RtyBase { ou = Under; cty } ->
      let var = (Rename.unique_var fv)#:cty.nty in
      let prop = subst_prop_instance fv (AVar var) prop in
      smart_forall_phi (var, cty.phi) prop
  | _ -> _die_with [%here] "unimp"

let construct_call_ret_exists rctx fty retty =
  if is_arr_ret_arr fty then None
  else (
    Pp.printf "retty: %s\n" (layout_rty retty);
    let fvs = fv_rty retty in
    let fvrtys =
      List.map
        (fun fv ->
          match Typectx.get_opt rctx.rty_ctx fv.x with
          | Some rty -> rty
          | None -> _die_with [%here] (spf "cannot find %s in rty ctx\n" fv.x))
        fvs
    in
    Pp.printf "fvs: ";
    List.iter2
      (fun fv fvrty -> Printf.printf "%s <%s> " fv.x (layout_rty fvrty))
      fvs fvrtys;
    print_newline ();
    let retcty =
      match retty with
      | RtyBase { ou = Under; cty } -> cty
      | _ -> _die_with [%here] "unimp"
    in
    let prop = exists_fresh_v_prop retcty in
    Some (List.fold_left2 possible_value_fv prop fvs fvrtys))
