open Language
open Zutils
open Sugar
open Auxtyping
open Common
open HandlePred

type value_infer_mode = TopParam | PolyPredParam

let value_infer_mode = PolyPredParam

type 'a fconstraints = (Nt.t lit * Nt.t prop) list
type 'a fctx = (Nt.t lit * 'a fconstraints) list

type 'a infer_result = {
  term : 'a;
  exists_prop : Nt.t prop;
  call_constraints : 'a fconstraints;
}

let infer_result_default term =
  { term; exists_prop = Prop.mk_true; call_constraints = [] }

let infer_result term exists_prop call_constraints =
  { term; exists_prop; call_constraints }

let result_map f res = { res with term = f res.term }

let result_list_to_list_result xs =
  let vs = List.map (fun v -> v.term) xs in
  let exists_prop = smart_and (List.map (fun v -> v.exists_prop) xs) in
  let call_constraints =
    List.concat (List.map (fun v -> v.call_constraints) xs)
  in
  infer_result vs exists_prop call_constraints

let type_check_group (bctx : built_in_ctx) =
  let _find_in_ctx loc (rctx : rctx) (id : (Nt.t, string) typed) =
    let res = lookup_ctxs [ rctx.rty_ctx; bctx.builtin_ctx ] id.x in
    match res with
    | Some res ->
        let rty = fresh_name_rty res in
        let _, rty = instantiate_rty_by_nty [%here] rty id.ty in
        rty
    | None -> _die_with loc (spf "cannot find %s in type context" id.x)
  in
  let _id_type_infer loc (rctx : rctx) (id : (Nt.t, string) typed) : Nt.t rty =
    let rty = _find_in_ctx loc rctx id in
    (* NOTE: both over and under type will induce under type *)
    if is_base_rty rty then mk_eq_tvar_underrty id.x#:(erase_rty rty) else rty
  in
  let subtyping rctx (rty1, rty2) exists_prop call_constraints =
    pprint_typing_subtyping rctx (rty1, rty2);
    sub_rty rctx (rty1, rty2) exists_prop call_constraints
  in
  let rec value_type_infer (rctx : rctx) (fctx : 'a fctx)
      (v : (Nt.t, Nt.t value) typed) :
      (Nt.t rty, Nt.t rty value) typed infer_result option =
    let res =
      match v.x with
      | VVar id ->
          let () = if String.equal id.x "None" then _die [%here] in
          let rty = _id_type_infer [%here] rctx id in
          let res = (VVar id.x#:rty)#:rty in
          if Myconfig.get_bool_option "show_type_infer_variable_judgement" then
            pprint_typing_infer_value_after rctx (v, Some res);
          let fconstraint =
            List.assoc_opt (AVar id) fctx |> Option.value ~default:[]
          in
          Some (infer_result res Prop.mk_true fconstraint)
      | VConst U ->
          let res = (VConst U)#:(mk_top_underrty Nt.unit_ty) in
          if Myconfig.get_bool_option "show_type_infer_constant_judgement" then
            pprint_typing_infer_value_after rctx (v, Some res);
          Some (infer_result_default res)
      | VConst c ->
          let res = (VConst c)#:(mk_eq_c_underrty c) in
          if Myconfig.get_bool_option "show_type_infer_constant_judgement" then
            pprint_typing_infer_value_after rctx (v, Some res);
          Some (infer_result_default res)
      | VTuple vs ->
          let* infer_results =
            opt_list_to_list_opt @@ List.map (value_type_infer rctx fctx) vs
          in
          let vs = List.map (fun v -> v.term) infer_results in
          let phis =
            List.mapi
              (fun idx x ->
                match x.ty with
                | RtyBase { ou = Under; cty = { phi; eqv = None; _ } } ->
                    let y =
                      mk_nth_lit [%here] (AVar default_v#:v.ty)#:v.ty idx
                    in
                    let phi = subst_prop_instance default_v y.x phi in
                    phi
                | _ -> _die_with [%here] "unimp")
              vs
          in
          let rty =
            RtyBase
              {
                ou = Under;
                cty = { nty = v.ty; phi = smart_and phis; eqv = None };
              }
          in
          let res = (VTuple vs)#:rty in
          let exists_prop =
            smart_and @@ List.map (fun v -> v.exists_prop) infer_results
          in
          let constraints =
            List.concat (List.map (fun v -> v.call_constraints) infer_results)
          in
          pprint_typing_infer_value_after rctx (v, Some res);
          Some (infer_result res exists_prop constraints)
      | VLam { lamarg; body } ->
          let nty = lamarg.ty in
          let res =
            if Nt.is_base_tp nty then
              match value_infer_mode with
              | PolyPredParam ->
                  let pred =
                    (Rename.unique_var "p")#:(Nt.construct_arr_tp
                                                ([ nty ], Nt.bool_ty))
                  in
                  let open Prop in
                  let phi =
                    Lit
                      (AAppOp (pred, [ tvar_to_lit default_v#:nty ]))#:Nt
                                                                       .bool_ty
                  in
                  let rty = cty_to_overrty { nty; phi; eqv = None } in
                  let lamarg = lamarg.x#:rty in
                  let rctx' = Rctx.add_pred rctx pred in
                  let rctx' = Rctx.add_var rctx' lamarg in
                  (* TODO: propagate exists_prop up *)
                  let* body = term_type_infer rctx' [] body in
                  let frty =
                    construct_poly_pred_rty
                      ([ pred ], construct_rty ([ lamarg ], body.term.ty))
                  in
                  Some (VLam { lamarg; body = body.term })#:frty
              | TopParam ->
                  let lamarg = lamarg.x#:(mk_top_overrty nty) in
                  (* TODO: propagate exists_prop up *)
                  let* body =
                    term_type_infer (Rctx.add_var rctx lamarg) [] body
                  in
                  let frty = construct_rty ([ lamarg ], body.term.ty) in
                  Some (VLam { lamarg; body = body.term })#:frty
            else _die_with [%here] "unimp"
          in
          pprint_typing_infer_value_after rctx (v, res);
          Option.map infer_result_default res
      | VFix { fixname; _ } -> (
          match Typectx.get_opt rctx.inv_ctx fixname.x with
          | None ->
              _die_with [%here]
                (spf "inductive invaraint of %s is missing" fixname.x)
          | Some rty ->
              let () = Pp.printf "@{<bold>inv:@} %s\n" (layout_rty rty) in
              Option.map infer_result_default
              @@ value_type_check rctx fctx v rty)
    in
    res
  and value_type_check (rctx : rctx) (fctx : 'a fctx)
      (v : (Nt.t, Nt.t value) typed) (rty : Nt.t rty) :
      (Nt.t rty, Nt.t rty value) typed option =
    let () = pprint_typing_check_value rctx (v, rty) in
    match (v.x, rty) with
    | _, RtyPolyType { pt; rty } ->
        value_type_check (Rctx.add_tvar rctx pt) fctx v rty
    | _, RtyPolyPred { pred; rty } ->
        value_type_check (Rctx.add_pred rctx pred) fctx v rty
    | VConst _, _ | VVar _, _ | VTuple _, _ ->
        let* e = value_type_infer rctx fctx v in
        if subtyping rctx (e.term.ty, rty) e.exists_prop e.call_constraints then
          Some e.term
        else (
          _warinning_subtyping_error [%here] (e.term.ty, rty);
          _warinning_typing_error [%here] (layout_typed_value v, rty);
          None)
    | VLam { lamarg; body }, RtyArr { argrty; arg; retty } ->
        Pp.printf "in lam case\n";
        (* NOTE: unify the name of parameter type and lambda variable *)
        let retty = subst_rty_instance arg (AVar lamarg) retty in
        let lamarg = lamarg.x#:argrty in
        let rctx' = Rctx.add_var rctx lamarg in
        let* body = term_type_check rctx' fctx body retty in
        Some (VLam { lamarg; body })#:(RtyArr { argrty; arg; retty })
    | VLam _, _ -> _die [%here]
    | VFix { fixname; fixarg; body }, RtyArr { argrty; arg; retty } ->
        (* NOTE: we force the first argument to be the decreasing argument *)
        let measure_cty =
          match argrty with
          | RtyBase { ou = Over; cty } -> cty
          | _ ->
              _die_with [%here]
                "the first parameter of recursive function must be a \
                 decreasing base type"
        in
        let fixarg =
          fixarg #=> (fun t ->
          (* let () = *)
          (*   Printf.printf "%s =? %s\n" (Nt.layout t) (Nt.layout measure_cty.nty) *)
          (* in *)
          Nt.unify_two_types [%here] [] (t, measure_cty.nty))
        in
        (* NOTE: make sure the name of paramater of refinement type is different from the one in the implementation. *)
        (* let () = Printf.printf "fix retty %s\n" (layout_rty retty) in *)
        let arg, retty =
          if String.equal arg fixarg.x then
            let arg' = Rename.unique_var arg in
            (arg', subst_rty_instance arg (AVar arg'#:fixarg.ty) retty)
          else (arg, retty)
        in
        (* let () = Printf.printf "fix retty %s\n" (layout_rty retty) in *)
        let rty' =
          let phi = smart_add_to (mk_self_wf_dec fixarg) measure_cty.phi in
          let argrty = cty_to_overrty { nty = fixarg.ty; phi; eqv = None } in
          RtyArr { argrty; arg; retty }
        in
        (* let () = Printf.printf "fix rty' %s\n" (layout_rty rty') in *)
        let retty = subst_rty_instance arg (AVar fixarg) retty in
        let rctx' = Rctx.add_vars rctx [ fixarg.x#:argrty; fixname.x#:rty' ] in
        (* TODO: add to fctx *)
        let* body = term_type_check rctx' fctx body retty in
        Some
          (VFix { fixname = fixname.x#:rty; fixarg = fixarg.x#:argrty; body })#:rty
    | VFix _, _ -> _die [%here]
  and arrow_subarrow_rtys (appf_rty : Nt.t rty) : Nt.t rty list =
    let rec aux rty =
      match rty with
      | RtyArr { retty; _ } -> rty :: aux retty
      | RtyBase _ -> []
      | _ -> _die_with [%here] "unexpected rty type"
    in
    aux appf_rty
  and arrow_type_arg_prop appf_rty (apparg : (Nt.t rty, Nt.t value) typed) :
      Nt.t lit * Nt.t prop =
    let argrty, _, _ = destruct_arr_rty [%here] appf_rty in
    let () =
      Pp.printf "app basic type check: %s vs %s\n" (layout_rty argrty)
        (layout_rty apparg.ty);
      _assert [%here] "application basic type check"
        (Nt.equal_nt (erase_rty argrty) (erase_rty apparg.ty))
    in
    match argrty with
    | RtyBase { ou = Over; cty } ->
        let arglit = value_to_lit [%here] apparg.x in
        (arglit, subst_prop_instance default_v arglit cty.phi)
    | _ -> _die [%here]
  and over_arrow_type_apply (_ : rctx) appf_rty
      (apparg : (Nt.t rty, Nt.t value) typed) : Nt.t rty option =
    let argrty, arg, retty = destruct_arr_rty [%here] appf_rty in
    let () =
      _assert [%here] "application basic type check"
        (Nt.equal_nt (erase_rty argrty) (erase_rty apparg.ty))
    in
    Pp.printf "old retty: %s\n" (layout_rty retty);
    match argrty with
    | RtyBase { ou = Over; cty } ->
        let arglit = value_to_lit [%here] apparg.x in
        let retty = subst_rty_instance arg arglit retty in
        Pp.printf "mid retty: %s\n" (layout_rty retty);
        let tmp_rty =
          mk_unit_underrty (subst_prop_instance default_v arglit cty.phi)
        in
        let retty = exists_rty (Rename.fresh_var ())#:tmp_rty retty in
        Pp.printf "new retty: %s\n" (layout_rty retty);
        Some retty
    | _ -> _die [%here]
  and arrow_arrow_type_apply (rctx : rctx) appf_rty
      (apparg : (Nt.t rty, Nt.t value) typed) : Nt.t rty option =
    let argrty, arg, retty = destruct_arr_rty [%here] appf_rty in
    let () =
      let _nt1 = erase_rty argrty in
      let _nt2 = erase_rty apparg.ty in
      if not (Nt.equal_nt _nt1 _nt2) then (
        Printf.printf "%s != %s\n" (Nt.layout _nt1) (Nt.layout _nt2);
        _assert [%here] "application basic type check" false)
    in
    match argrty with
    | RtyArr _ ->
        if not (subtyping rctx (apparg.ty, argrty) Prop.mk_true []) then (
          _warinning_subtyping_error [%here] (apparg.ty, argrty);
          _warinning_typing_error [%here]
            (layout_typed_value @@ (apparg#=>erase_rty), argrty);
          None)
        else if is_free_rty arg retty then (
          Printf.printf "%s\n" (layout_rty retty);
          _die_with [%here]
            (spf "arrow typed variable cannot be refered (%s)" arg))
        else Some retty
    | _ -> _die [%here]
  and term_type_infer (rctx : rctx) (fctx : 'a fctx)
      (e : (Nt.t, Nt.t term) typed) :
      (Nt.t rty, Nt.t rty term) typed infer_result option =
    match e.x with
    | CVal v ->
        let* v = value_type_infer rctx fctx v in
        Some (result_map (fun v -> (CVal v)#:v.ty) v)
    | _ ->
        let () = pprint_typing_infer_term_before rctx e in
        let res =
          match e.x with
          | CVal _ -> _die [%here]
          | CErr ->
              _assert [%here]
                (spf "err can only has base type, not %s" (Nt.layout_nt e.ty))
                (Nt.is_base_tp e.ty);
              Some (infer_result_default CErr#:(mk_bot_underrty e.ty))
          | CRecord vs ->
              let fields, vs = List.split vs in
              let* vs =
                opt_list_to_list_opt @@ List.map (value_type_infer rctx fctx) vs
              in
              let { term = vs; exists_prop; call_constraints } =
                result_list_to_list_result vs
              in
              let vs = List.combine fields vs in
              let self = default_v#:e.ty in
              let phis =
                List.map
                  (fun (x, v) ->
                    let cty = as_under_base_rty [%here] v.ty in
                    let lit = AField (lit_to_tlit (AVar self), x) in
                    let phi = subst_prop_instance default_v lit cty.phi in
                    phi)
                  vs
              in
              let cty = { nty = e.ty; phi = smart_and phis; eqv = None } in
              let rty = RtyBase { ou = Under; cty } in
              Some (infer_result (CRecord vs)#:rty exists_prop call_constraints)
          | CField { rd; field } ->
              let lit = value_to_lit [%here] rd.x in
              let lit = (AField (lit_to_tlit lit, field))#:e.ty in
              let* rd = value_type_infer rctx fctx rd in
              let rty = RtyBase { ou = Under; cty = mk_eq_lit_cty lit } in
              Some (result_map (fun rd -> (CField { rd; field })#:rty) rd)
          | CLetE { rhs; lhs; body } ->
              let* rhs' = term_type_infer rctx fctx rhs in
              if not (non_emptiness_rty rctx rhs'.term.ty) then (
                _warinning_nonemptiness_error [%here] rhs'.term.ty;
                _warinning_typing_error [%here] (layout_term rhs.x, rhs'.term.ty);
                None)
              else
                let fctx' = (AVar lhs, rhs'.call_constraints) :: fctx in
                let rhs = rhs' in
                let lhs = lhs.x#:rhs.term.ty in
                let rctx' = Rctx.add_var rctx lhs in
                let* body = term_type_infer rctx' fctx' body in
                let rty =
                  Rctx.diff_exists_rty [%here] rctx' rctx body.term.ty
                in
                let exists_prop =
                  smart_and [ rhs.exists_prop; body.exists_prop ]
                in
                let call_constraints =
                  body.call_constraints @ rhs.call_constraints
                in
                Some
                  (infer_result
                     (CLetE { rhs = rhs.term; lhs; body = body.term })#:rty
                     exists_prop call_constraints)
          (* (\* Lambda function to let binding *\) *)
          (* | CApp { appf = { x = VLam { lamarg; body }; _ }; apparg } -> *)
          (*     let apparg = value_type_infer rctx apparg in *)
          (*     let lamarg = lamarg.x#:apparg.ty in *)
          (*     let rctx' = Rctx.add_var rctx lamarg in *)
          (*     let* body = term_type_infer rctx' body in *)
          (*     let rty = Rctx.diff_exists_rty [%here] rctx' rctx body.ty in *)
          (*     let frty = *)
          (*       RtyArr { argrty = lamarg.ty; arg = lamarg.x; retty = rty } *)
          (*     in *)
          (*     let appf = (VLam { lamarg; body })#:frty in *)
          (*     Some (CApp { appf; apparg })#:rty *)
          | CApp { appf; apparg } ->
              (* let () = Printf.printf "Application : %s\n" (layout_term e.x) in *)
              Pp.printf "inferring appf\n";
              let* appf = value_type_infer rctx fctx appf in
              Pp.printf "inferring apparg\n";
              let* apparg' = value_type_infer rctx fctx apparg in
              Pp.printf "done inferring\n";
              let () =
                Pp.printf "appf_ty : %s | apparg %s \n"
                  (layout_rty appf.term.ty)
                  (layout_rty apparg'.term.ty)
              in
              let poly_preds, appf_ty, apparg_rty =
                instantiate_poly_pred_rty rctx.pred_ctx appf.term.ty
                  apparg'.term.ty
              in
              let rctx' = Rctx.add_preds rctx poly_preds in
              (* let () = Printf.printf "appf_ty : %s\n" (layout_rty appf_ty) in *)
              let* retty =
                if is_over_arr_rty appf_ty then
                  over_arrow_type_apply rctx' appf_ty apparg.x#:apparg_rty
                else if is_arr_arr_rty appf_ty then
                  arrow_arrow_type_apply rctx' appf_ty apparg.x#:apparg_rty
                else
                  let () =
                    Printf.printf "cannot handle function type: %s\n"
                      (layout_rty appf_ty)
                  in
                  _die [%here]
              in
              let call_constraint =
                arrow_type_arg_prop appf_ty apparg.x#:apparg_rty
              in
              let call_constraints =
                call_constraint
                :: (appf.call_constraints @ apparg'.call_constraints)
              in
              let exists_prop =
                let prop =
                  if is_arr_ret_arr appf_ty then None
                  else
                    Some (construct_call_ret_exists rctx retty call_constraints)
                in
                match prop with
                | Some p ->
                    Pp.printf "ret exists: %s\n" (layout_prop p);
                    p
                | None -> Prop.mk_true
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              let retty =
                remove_redundant_poly_pred
                @@ construct_poly_pred_rty (poly_preds, retty)
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              Some
                (infer_result
                   (CApp { appf = appf.term; apparg = apparg'.term })#:retty
                   exists_prop [ call_constraint ])
          | CAppOp { op; appopargs } ->
              let op =
                op.x#:(_find_in_ctx [%here] rctx op#->op_name_for_typectx)
              in
              (* let () = Printf.printf "op_ty : %s\n" (layout_rty op.ty) in *)
              let* appopargs =
                opt_list_to_list_opt
                @@ List.map
                     (fun v ->
                       let* v' = value_type_infer rctx fctx v in
                       Some (v, v'))
                     appopargs
              in
              let exists_prop =
                List.map (fun (_, v') -> v'.exists_prop) appopargs |> smart_and
              in
              let call_constraints =
                List.map (fun (_, v') -> v'.call_constraints) appopargs
                |> List.concat
              in
              let appopargs =
                List.map (fun (v, v') -> (v, v'.term)) appopargs
              in
              let* retty =
                List.fold_left
                  (fun res (apparg, apparg') ->
                    let* rty = res in
                    over_arrow_type_apply rctx rty apparg.x#:apparg'.ty)
                  (Some op.ty) appopargs
              in
              let op_arg_rtys = arrow_subarrow_rtys op.ty in
              let new_call_constraints =
                List.map2
                  (fun (apparg, apparg') argrty ->
                    arrow_type_arg_prop argrty apparg.x#:apparg'.ty)
                  appopargs op_arg_rtys
              in
              let call_constraints = new_call_constraints @ call_constraints in
              let exists_prop =
                let p =
                  smart_and
                    [
                      construct_call_ret_exists rctx retty call_constraints;
                      exists_prop;
                    ]
                in
                Pp.printf "ret exists: %s\n" (layout_prop p);
                p
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              Some
                (infer_result
                   (CAppOp { op; appopargs = List.map snd appopargs })#:retty
                   exists_prop call_constraints)
          | CMatch { matched; match_cases } ->
              (* NOTE: we drop unreachable cases *)
              let match_cases =
                List.filter_map
                  (match_case_type_infer rctx fctx matched)
                  match_cases
              in
              (* TODO: might need to add branch conditions here? *)
              let exists_prop =
                smart_and (List.map (fun x -> x.exists_prop) match_cases)
              in
              let call_constraints =
                List.map (fun x -> x.call_constraints) match_cases
                |> List.flatten
              in
              let unioned_ty =
                union_rtys
                @@ List.map
                     (function { term = CMatchcase { exp; _ }; _ } -> exp.ty)
                     match_cases
              in
              let* matched = value_type_infer rctx fctx matched in
              let exists_prop =
                smart_and [ matched.exists_prop; exists_prop ]
              in
              let call_constraints =
                matched.call_constraints @ call_constraints
              in
              let match_cases = List.map (fun x -> x.term) match_cases in
              Some
                (infer_result
                   (CMatch { matched = matched.term; match_cases })#:unioned_ty
                   exists_prop call_constraints)
          | CLetDeTuple { turhs; tulhs; body } ->
              let* turhs' = value_type_infer rctx fctx turhs in
              let tmp = (Rename.fresh_var ())#:turhs.ty in
              let tulhs =
                List.mapi
                  (fun idx x ->
                    let lit = lit_to_tlit (AProj (tvar_to_lit tmp, idx)) in
                    let rty = mk_eq_lit_underrty lit in
                    x.x#:rty)
                  tulhs
              in
              let tmp = tmp.x#:turhs'.term.ty in
              let rctx' = Rctx.add_vars rctx (tmp :: tulhs) in
              (* TODO : add to fctx *)
              let* body = term_type_infer rctx' fctx body in
              let rty = Rctx.diff_exists_rty [%here] rctx' rctx body.term.ty in
              let exists_prop =
                smart_and [ turhs'.exists_prop; body.exists_prop ]
              in
              let call_constraints =
                turhs'.call_constraints @ body.call_constraints
              in
              Some
                (infer_result
                   (CLetDeTuple { turhs = turhs'.term; tulhs; body = body.term })
                   #:rty
                   exists_prop call_constraints)
          (* | CLetE { rhs; lhs; body } -> *)
          (*     let* rhs = term_type_infer rctx rhs in *)
          (*     let lhs = lhs.x#:rhs.ty in *)
          (*     let rctx' = Rctx.add_var rctx lhs in *)
          (*     let* body = term_type_infer rctx' body in *)
          (*     Some *)
          (*       (CLetE { rhs; lhs; body })#:(Rctx.diff_exists_rty [%here] rctx' rctx *)
          (*                                      body.ty) *)
        in
        pprint_typing_infer_term_after rctx
          ( e,
            let* res = res in
            Some res.term.ty );
        res
  and term_type_check (rctx : rctx) (fctx : 'a fctx)
      (e : (Nt.t, Nt.t term) typed) (rty : Nt.t rty) :
      (Nt.t rty, Nt.t rty term) typed option =
    match e.x with
    | CVal v ->
        let* v = value_type_check rctx fctx v rty in
        Some (CVal v)#:v.ty
    | _ -> (
        let () = pprint_typing_check_term rctx (e, rty) in
        match e.x with
        | CVal _ -> _die [%here]
        | CErr -> Some CErr#:rty
        | CLetDeTuple _ -> failwith "unimp"
        | CApp _ | CAppOp _ | CMatch _ | CLetE _ | CRecord _ | CField _ ->
            let* e' = term_type_infer rctx fctx e in
            if sub_rty rctx (e'.term.ty, rty) e'.exists_prop e'.call_constraints
            then Some e'.term.x#:rty
            else (
              _warinning_subtyping_error [%here] (e'.term.ty, rty);
              _warinning_typing_error [%here] (layout_typed_term e, rty);
              None))
  (* | CLetE { rhs; lhs; body } -> *)
  (*     let* rhs = term_type_infer rctx rhs in *)
  (*     let rctx', lhs = Rctx.add_var rctx lhs.x #: rhs.ty in *)
  (*     let* body = term_type_check rctx' body rty in *)
  (*     Some (CLetE { rhs; lhs; body }) #: rty *)
  and match_case_type_infer (rctx : rctx) (fctx : 'a fctx)
      (matched : (Nt.t, Nt.t value) typed) (x : Nt.t match_case) :
      Nt.t rty match_case infer_result option =
    match x with
    | CMatchcase { constructor; args; exp } ->
        let constructor_rty =
          _find_in_ctx [%here] rctx constructor#->dt_name_for_typectx
        in
        (* let () = *)
        (*   Printf.printf "constructor.ty : %s\n" (layout_rty constructor_rty) *)
        (* in *)
        let args, retty =
          List.fold_left
            (fun (args, rty) x ->
              match rty with
              | RtyArr { argrty; arg; retty } ->
                  let retty = subst_rty_instance arg (AVar x) retty in
                  (args @ [ x.x#:(flip_rty argrty) ], retty)
              | _ -> _die [%here])
            ([], constructor_rty) args
        in
        let retty =
          match retty with
          | RtyBase { ou = Under; cty = { phi; _ } } ->
              let phi =
                subst_prop_instance default_v
                  (value_to_lit [%here] matched.x)
                  phi
              in
              RtyBase
                { ou = Under; cty = { nty = Nt.unit_ty; phi; eqv = None } }
          | _ ->
              Printf.printf "retty: %s\n" (layout_rty retty);
              _die [%here]
        in
        let rctx' =
          Rctx.add_vars rctx (args @ [ (Rename.fresh_var ())#:retty ])
        in
        (* TODO: add to fctx *)
        let* exp' = term_type_infer rctx' fctx exp in
        let exp' =
          {
            exp' with
            term = exp'.term#=>(Rctx.diff_exists_rty [%here] rctx' rctx);
          }
        in
        let () =
          pprint_typing_infer_match_case rctx constructor (exp, exp'.term.ty)
        in
        Some
          (infer_result
             (CMatchcase
                {
                  constructor = constructor.x#:constructor_rty;
                  args;
                  exp = exp'.term;
                })
             exp'.exists_prop exp'.call_constraints)
  in
  (value_type_check, term_type_check)

let value_type_check bctx ctx (value, rty) =
  (fst @@ type_check_group bctx) ctx [] value rty

let term_type_check bctx ctx (value, rty) =
  (snd @@ type_check_group bctx) ctx [] value rty
