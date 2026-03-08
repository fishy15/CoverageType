open Auxprop
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
      let var = Rename.unique_var fv in
      let prop = subst_prop_instance fv (AVar var#:cty.nty) prop in
      smart_dependent_forall (var, cty) prop
  | RtyBase { ou = Over; _ } ->
      (* let variable refer to that same value *)
      prop
  | _ -> _die_with [%here] "unimp"

let merge_keep_snd xs ys =
  Pp.printf "xs: ";
  List.iter (fun x -> Printf.printf "%s " x.x) xs;
  print_newline ();
  Pp.printf "ys: ";
  List.iter (fun y -> Printf.printf "%s " y.x) ys;
  print_newline ();
  let xs = List.filter (fun x -> not (List.mem x ys)) xs in
  let res = xs @ ys in
  Pp.printf "res: ";
  List.iter (fun y -> Printf.printf "%s " y.x) res;
  print_newline ();
  res

let relevant_fvs_in_ctx rctx rty =
  let rec aux rty =
    let fvs = fv_rty rty in
    let fvs_of_fvs =
      List.map
        (fun fv ->
          match Typectx.get_opt rctx.rty_ctx fv.x with
          | Some rty -> aux rty
          | None -> _die_with [%here] (spf "cannot find %s in rty ctx\n" fv.x))
        fvs
    in
    List.fold_left merge_keep_snd fvs fvs_of_fvs
  in
  aux rty

let construct_call_ret_exists rctx retty =
  let fvs = relevant_fvs_in_ctx rctx retty in
  let fvrtys =
    List.map
      (fun fv ->
        match Typectx.get_opt rctx.rty_ctx fv.x with
        | Some rty -> rty
        | None -> _die_with [%here] (spf "cannot find %s in rty ctx\n" fv.x))
      fvs
  in
  Pp.printf "retty: %s\n" (layout_rty retty);
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
  List.fold_left2 possible_value_fv prop fvs fvrtys
