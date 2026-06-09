open Auxprop
open Eqv
open Language
open Zutils
open Myconfig
open Zdatatype

let _log_auxtyping = _log "auxtyping"
let layout_qt = function Nt.Fa -> "∀" | Nt.Ex -> "∃"

let layout_qv { x = qt, x; ty } =
  spf "%s%s:{%s}" (layout_qt qt) x @@ layout_cty ty

let layout_vs qt uqvs =
  List.split_by_comma layout_qv
  @@ List.map (fun { x; ty } -> { x = (qt, x); ty }) uqvs

let layout_prop_ = layout_prop

let report_unclosed loc query =
  let fvs = fv_prop query in
  _assert loc
    (spf "the cty query has free variables %s"
       (List.split_by_comma
          (function { x; ty } -> spf "%s:%s" x (Nt.layout ty))
          fvs))
    (0 == List.length fvs)

let check_valid (task, query) =
  let () =
    _log_debug @@ fun _ ->
    Printf.printf "check valid: %s\n" (layout_prop_ query)
  in
  let () = report_unclosed [%here] query in
  Prover.check_valid (task, query)

let simplify_sub_typectx ctx (rty1, rty2) exists_prop =
  let ctx = Typectx.ctx_to_list ctx in
  let rec aux (prefix, rest) (rty1, rty2) exists_prop =
    match rest with
    | [] -> (prefix, rty1, rty2, exists_prop)
    | { x; ty } :: rest -> (
        match ty with
        | RtyBase { cty = { nty; phi; eqv = None }; _ } -> (
            match is_eq_phi default_v#:nty phi with
            | Some lit ->
                let rty1 = subst_cty_instance x lit rty1 in
                let rty2 = subst_cty_instance x lit rty2 in
                let rest =
                  List.map
                    (fun y -> { x = y.x; ty = subst_rty_instance x lit y.ty })
                    rest
                in
                let exists_prop = subst_prop_instance x lit exists_prop in
                aux (prefix, rest) (rty1, rty2) exists_prop
            | None ->
                aux (prefix @ [ { x; ty } ], rest) (rty1, rty2) exists_prop)
        | _ -> aux (prefix @ [ { x; ty } ], rest) (rty1, rty2) exists_prop)
  in
  aux ([], ctx) (rty1, rty2) exists_prop

let sub_cty ou rctx cty1 cty2 exists_prop =
  let ctx_list, cty1, cty2, exists_prop =
    simplify_sub_typectx rctx.rty_ctx (cty1, cty2) exists_prop
  in
  let () =
    _log_auxtyping @@ fun _ ->
    Printf.printf "exists_prop: %s\n" (layout_prop exists_prop)
  in
  let overctx, underctx = build_wf_ctx ctx_list in
  let () =
    _log_auxtyping @@ fun _ ->
    let overctx =
      List.map (fun (x, cty) -> x#:(RtyBase { ou = Over; cty })) overctx
    in
    let underctx =
      List.map (fun (x, cty) -> x#:(RtyBase { ou = Under; cty })) underctx
    in
    let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
    Typectx.pprint_ctx layout_rty ctx';
    print_newline ()
  in
  let () =
    let dom = List.map fst (overctx @ underctx) in
    if not (is_close_cty dom cty1) then (
      Printf.printf
        "left-hand-side type %s\n\
         %s should be closed under over + under ctx: [ %s ]\n"
        (* (layout_rty (RtyBase { ou; cty = cty1 })) *)
        (show_prop cty1.phi)
        (StrList.to_string (fv_cty_id cty1))
        (StrList.to_string dom);
      _die [%here])
  in
  let () =
    let dom = List.map fst (overctx @ underctx) in
    if not (is_close_cty dom cty2) then (
      Printf.printf
        "right-hand-side type %s\n\
        \ %s should be closed under over + under ctx: [ %s ]\n"
        (layout_rty (RtyBase { ou; cty = cty2 }))
        (StrList.to_string (fv_cty_id cty2))
        (StrList.to_string dom);
      _die [%here])
  in
  let nty = if Nt.equal_nt cty1.nty cty2.nty then cty1.nty else _die [%here] in
  let overctx = (default_v, mk_top_cty nty) :: overctx in
  let query =
    match (ou, cty1.eqv, cty2.eqv) with
    | Over, None, None ->
        let prop = smart_implies cty1.phi cty2.phi in
        let prop = smart_implies exists_prop prop in
        List.fold_right smart_fresh_dependent_forall
          (overctx @ [ (default_v, mk_top_cty cty1.nty) ])
          prop
    | Under, None, None ->
        let rhs =
          List.fold_right smart_fresh_dependent_exists underctx
            (fresh_name_prop cty1.phi)
        in
        let prop = smart_implies cty2.phi rhs in
        let prop = smart_implies exists_prop prop in
        List.fold_right smart_fresh_dependent_forall
          (overctx @ [ (default_v, mk_top_cty cty2.nty) ])
          prop
    | Under, None, Some eqv ->
        let underctx = underctx in
        let phi = eqv_to_phi nty cty1.phi eqv in
        let rhs = List.fold_right smart_fresh_dependent_exists underctx phi in
        let prop = smart_implies cty2.phi rhs in
        let prop = smart_implies exists_prop prop in
        List.fold_right smart_fresh_dependent_forall
          (overctx @ [ (default_v, mk_top_cty cty2.nty) ])
          prop
    | _ -> _die_with [%here] "unsupported eqv"
  in
  let () = Statistic.stat_query_formula (rctx.task_name, query) in
  let time, res =
    clock (fun () ->
        let () =
          _log_auxtyping @@ fun _ ->
          Printf.printf "before simp:\n%s\n\n" (layout_prop query)
        in
        let query = SimplProp.simpl_query query in
        let () = Statistic.stat_query_formula (rctx.task_name, query) in
        let () =
          _log_auxtyping @@ fun _ ->
          Printf.printf "check valid:\n%s\n\n" (layout_prop query)
        in
        let () =
          _log_auxtyping @@ fun _ ->
          Printf.printf "let[@axiom] tmp = %s\n" (layout_prop__raw query)
        in
        check_valid (Some rctx.task_name, query))
  in
  let () = Statistic.stat_query_time (rctx.task_name, time) in
  (* let () = if not res then _die [%here] in *)
  res

(* NOTE: after exists the constraints into the return type, the emptiness can be checked final stage;
   It may cause the more branch analysis.
*)
let lazy_emptiness_check = false

let non_emptiness_cty rctx cty =
  if lazy_emptiness_check then true
  else
    let overctx, underctx = build_wf_ctx (Typectx.ctx_to_list rctx.rty_ctx) in
    let underctx = underctx @ [ (default_v, mk_top_cty cty.nty) ] in
    let () =
      _log_auxtyping @@ fun _ ->
      let overctx =
        List.map (fun (x, cty) -> x#:(RtyBase { ou = Over; cty })) overctx
      in
      let underctx =
        List.map (fun (x, cty) -> x#:(RtyBase { ou = Under; cty })) underctx
      in
      let ctx' = Typectx.ctx_from_list (overctx @ underctx) in
      Typectx.pprint_ctx layout_rty ctx';
      print_newline ()
    in
    let () =
      _assert [%here]
        "left-hand-side type should be closed under over + under ctx"
        (is_close_cty (List.map fst (overctx @ underctx)) cty)
    in
    let overctx = (default_v, mk_top_cty cty.nty) :: overctx in
    let query =
      List.fold_right smart_dependent_exists (overctx @ underctx) cty.phi
    in
    let () = Statistic.stat_query_formula (rctx.task_name, query) in
    let time, res =
      clock (fun () ->
          let () =
            _log_auxtyping @@ fun _ ->
            Printf.printf "check sat: %s\n" (layout_prop_ query)
          in
          let () =
            _log_auxtyping @@ fun _ ->
            Printf.printf "let[@axiom] tmp = %s\n" (layout_prop__raw query)
          in
          Prover.check_sat (Some rctx.task_name, query))
    in
    let () = Statistic.stat_query_time (rctx.task_name, time) in
    let res =
      match res with SmtUnsat -> false | SmtSat _ -> true | Timeout -> true
      (* NOTE: we cannot decide if this control flow is unreachable, thus continue *)
    in
    (* let () = if List.length underctx > 1 then _die [%here] in *)
    (* let () = if not res then _die [%here] in *)
    res
