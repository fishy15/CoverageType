open Language
open Zutils
open Sugar
open Auxtyping
open Common
open HandlePred

type value_infer_mode = TopParam | PolyPredParam

let value_infer_mode = PolyPredParam

type localctx = Nt.t rty Typectx.ctx

let intersect_rty rty1 rty2 =
  assert (Nt.equal_nt (erase_rty rty1) (erase_rty rty2));
  match (rty1, rty2) with
  | RtyBase { ou = Under; cty = cty1 }, RtyBase { ou = Under; cty = cty2 } ->
      let phi = smart_and [ cty1.phi; cty2.phi ] in
      RtyBase { ou = Under; cty = { cty1 with phi } }
  | _ -> _die_with [%here] "can only take intersection of base rty"

module InferResult = struct
  type 'a t = { term : 'a; exists_prop : Nt.t prop; localctx : localctx }

  let mk term exists_prop localctx = { term; exists_prop; localctx }

  let default term =
    { term; exists_prop = Prop.mk_true; localctx = Typectx.emp }

  let map f v = { v with term = f v.term }

  let combine { term = term1; exists_prop = exists_prop1; localctx = localctx1 }
      { term = term2; exists_prop = exists_prop2; localctx = localctx2 } =
    let term = (term1, term2) in
    let exists_prop = smart_and [ exists_prop1; exists_prop2 ] in
    let localctx = Typectx.concat_update localctx1 localctx2 intersect_rty in
    { term; exists_prop; localctx }

  let result_list_to_list_result vs =
    let acc =
      { term = []; exists_prop = Prop.mk_true; localctx = Typectx.emp }
    in
    List.fold_left
      (fun acc v ->
        let { term = h, t; exists_prop; localctx } = combine v acc in
        { term = h :: t; exists_prop; localctx })
      acc vs

  let replace_term (newterm : 'a) (old : 'b t) = { old with term = newterm }
end

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
  let subtyping rctx (rty1, rty2) exists_prop =
    pprint_typing_subtyping rctx (rty1, rty2);
    sub_rty rctx (rty1, rty2) exists_prop
  in
  let rec value_type_infer (rctx : rctx) (lctx : localctx Typectx.ctx)
      (v : (Nt.t, Nt.t value) typed) :
      (Nt.t rty, Nt.t rty value) typed InferResult.t option =
    let res =
      match v.x with
      | VVar id ->
          Pp.printf "infer variable %s\n" id.x;
          let () = if String.equal id.x "None" then _die [%here] in
          let rty = _find_in_ctx [%here] rctx id in
          let res = Some (VVar id.x#:rty)#:rty in
          if Myconfig.get_bool_option "show_type_infer_variable_judgement" then
            pprint_typing_infer_value_after rctx (v, res);
          let localctx =
            Typectx.get_opt lctx id.x |> Option.value ~default:Typectx.emp
          in
          Option.map (fun res -> InferResult.mk res Prop.mk_true localctx) res
      | VConst U ->
          Pp.printf "infer unit\n";
          let res = Some (VConst U)#:(mk_top_underrty Nt.unit_ty) in
          if Myconfig.get_bool_option "show_type_infer_constant_judgement" then
            pprint_typing_infer_value_after rctx (v, res);
          Option.map InferResult.default res
      | VConst c ->
          Pp.printf "infer constant\n";
          let res = Some (VConst c)#:(mk_eq_c_underrty c) in
          if Myconfig.get_bool_option "show_type_infer_constant_judgement" then
            pprint_typing_infer_value_after rctx (v, res);
          Option.map InferResult.default res
      | VTuple vs ->
          Pp.printf "infer tuple\n";
          let* vs =
            opt_list_to_list_opt @@ List.map (value_type_infer rctx lctx) vs
          in
          let vs = InferResult.result_list_to_list_result vs in
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
              vs.term
          in
          let rty =
            RtyBase
              {
                ou = Under;
                cty = { nty = v.ty; phi = smart_and phis; eqv = None };
              }
          in
          let res = Some (VTuple vs.term)#:rty in
          pprint_typing_infer_value_after rctx (v, res);
          Option.map (fun res -> InferResult.replace_term res vs) res
      | VLam { lamarg; body } ->
          Pp.printf "infer lambda\n";
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
                  let* body = term_type_infer rctx' lctx body in
                  let frty =
                    construct_poly_pred_rty
                      ([ pred ], construct_rty ([ lamarg ], body.term.ty))
                  in
                  let res =
                    InferResult.map
                      (fun body -> (VLam { lamarg; body })#:frty)
                      body
                  in
                  Some res
              | TopParam ->
                  let lamarg = lamarg.x#:(mk_top_overrty nty) in
                  (* TODO: propagate exists_prop up *)
                  let* body =
                    term_type_infer (Rctx.add_var rctx lamarg) lctx body
                  in
                  let frty = construct_rty ([ lamarg ], body.term.ty) in
                  let res =
                    InferResult.map
                      (fun body -> (VLam { lamarg; body })#:frty)
                      body
                  in
                  Some res
            else _die_with [%here] "unimp"
          in
          (* TODO: there is some bad cache i think, can be replaced with the version below *)
          let _ =
            match res with
            | Some r -> pprint_typing_infer_value_after rctx (v, Some r.term)
            | None -> pprint_typing_infer_value_after rctx (v, None)
          in
          (* pprint_typing_infer_value_after rctx *)
          (*   (v, Option.map (fun res -> res.term) res); *)
          res
      | VFix { fixname; _ } -> (
          Pp.printf "infer fix\n";
          match Typectx.get_opt rctx.inv_ctx fixname.x with
          | None ->
              _die_with [%here]
                (spf "inductive invaraint of %s is missing" fixname.x)
          | Some rty ->
              let () = Pp.printf "@{<bold>inv:@} %s\n" (layout_rty rty) in
              Option.map InferResult.default (value_type_check rctx lctx v rty))
    in
    res
  and value_type_check (rctx : rctx) (lctx : localctx Typectx.ctx)
      (v : (Nt.t, Nt.t value) typed) (rty : Nt.t rty) :
      (Nt.t rty, Nt.t rty value) typed option =
    let () = pprint_typing_check_value rctx (v, rty) in
    match (v.x, rty) with
    | _, RtyPolyType { pt; rty } ->
        value_type_check (Rctx.add_tvar rctx pt) lctx v rty
    | _, RtyPolyPred { pred; rty } ->
        value_type_check (Rctx.add_pred rctx pred) lctx v rty
    | VConst _, _ | VVar _, _ | VTuple _, _ ->
        let* { term = e; exists_prop; _ } = value_type_infer rctx lctx v in
        if subtyping rctx (e.ty, rty) exists_prop then Some e
        else (
          _warinning_subtyping_error [%here] (e.ty, rty);
          _warinning_typing_error [%here] (layout_typed_value v, rty);
          None)
    | VLam { lamarg; body }, RtyArr { argrty; arg; retty } ->
        (* NOTE: unify the name of parameter type and lambda variable *)
        let retty = subst_rty_instance arg (AVar lamarg) retty in
        let lamarg = lamarg.x#:argrty in
        let rctx' = Rctx.add_var rctx lamarg in
        let* body = term_type_check rctx' lctx body retty in
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
        let* body = term_type_check rctx' lctx body retty in
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
      Nt.t rty =
    let argrty, _, _ = destruct_arr_rty [%here] appf_rty in
    let () =
      Pp.printf "app basic type check: %s vs %s\n" (layout_rty argrty)
        (layout_rty apparg.ty);
      _assert [%here] "application basic type check"
        (Nt.equal_nt (erase_rty argrty) (erase_rty apparg.ty))
    in
    match argrty with
    | RtyBase { ou = Over; cty } ->
        let appargrty = apparg.ty in
        map_rty_retty
          (fun cty' ->
            let phi = smart_and [ cty.phi; cty'.phi ] in
            { cty with phi })
          appargrty
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
        if not (subtyping rctx (apparg.ty, argrty) Prop.mk_true) then (
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
  and term_type_infer (rctx : rctx) (lctx : localctx Typectx.ctx)
      (e : (Nt.t, Nt.t term) typed) :
      (Nt.t rty, Nt.t rty term) typed InferResult.t option =
    match e.x with
    | CVal v ->
        let* v = value_type_infer rctx lctx v in
        Some (InferResult.map (fun v -> (CVal v)#:v.ty) v)
    | _ ->
        let () = pprint_typing_infer_term_before rctx e in
        let res =
          match e.x with
          | CVal _ -> _die [%here]
          | CErr ->
              _assert [%here]
                (spf "err can only has base type, not %s" (Nt.layout_nt e.ty))
                (Nt.is_base_tp e.ty);
              Some (InferResult.default CErr#:(mk_bot_underrty e.ty))
          | CRecord vs ->
              let fields, vs = List.split vs in
              let* vs =
                opt_list_to_list_opt @@ List.map (value_type_infer rctx lctx) vs
              in
              let vs =
                InferResult.result_list_to_list_result vs
                |> InferResult.map (List.combine fields)
              in
              let self = default_v#:e.ty in
              let phis =
                List.map
                  (fun (x, v) ->
                    let cty = as_under_base_rty [%here] v.ty in
                    let lit = AField (lit_to_tlit (AVar self), x) in
                    let phi = subst_prop_instance default_v lit cty.phi in
                    phi)
                  vs.term
              in
              let cty = { nty = e.ty; phi = smart_and phis; eqv = None } in
              let rty = RtyBase { ou = Under; cty } in
              Some (InferResult.map (fun vs -> (CRecord vs)#:rty) vs)
          | CField { rd; field } ->
              let lit = value_to_lit [%here] rd.x in
              let lit = (AField (lit_to_tlit lit, field))#:e.ty in
              let* rd = value_type_infer rctx lctx rd in
              let rty = RtyBase { ou = Under; cty = mk_eq_lit_cty lit } in
              Some (InferResult.map (fun rd -> (CField { rd; field })#:rty) rd)
          | CLetE { rhs; lhs; body } ->
              let* rhs' = term_type_infer rctx lctx rhs in
              if not (non_emptiness_rty rctx rhs'.term.ty) then (
                _warinning_nonemptiness_error [%here] rhs'.term.ty;
                _warinning_typing_error [%here] (layout_term rhs.x, rhs'.term.ty);
                None)
              else
                let rhs = rhs' in
                let lhs = lhs.x#:rhs.term.ty in
                let rctx' = Rctx.add_var rctx lhs in
                let* body = term_type_infer rctx' lctx body in
                let rty =
                  Rctx.diff_exists_rty [%here] rctx' rctx body.term.ty
                in
                let exists_prop =
                  smart_and [ rhs.exists_prop; body.exists_prop ]
                in
                let localctx = Typectx.concat rhs.localctx body.localctx in
                Some
                  (InferResult.mk
                     (CLetE { rhs = rhs.term; lhs; body = body.term })#:rty
                     exists_prop localctx)
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
              let* appf = value_type_infer rctx lctx appf in
              Pp.printf "inferring apparg\n";
              let* apparg' = value_type_infer rctx lctx apparg in
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
              (* TODO: add the constraint here *)
              let localctx =
                let localctx = Typectx.concat appf.localctx apparg'.localctx in
                let call_constraint =
                  arrow_type_arg_prop appf_ty apparg.x#:apparg_rty
                in
                Pp.printf "app arg rty: %s\n" (layout_rty call_constraint);
                match apparg.x with
                | VVar { x = v; _ } ->
                    let localctx =
                      Typectx.update_or_add localctx intersect_rty
                        v#:call_constraint
                    in
                    localctx
                | VConst _ -> localctx
                | _ -> _die_with [%here] "unimp"
              in
              let exists_prop =
                let prop =
                  if is_arr_ret_arr appf_ty then None
                  else Some (construct_call_ret_exists rctx localctx retty)
                in
                match prop with
                | Some p ->
                    Pp.printf "ret exists: %s\n" (layout_prop p);
                    p
                | None -> Prop.mk_true
              in
              let exists_prop =
                smart_and [ exists_prop; appf.exists_prop; apparg'.exists_prop ]
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              let retty =
                remove_redundant_poly_pred
                @@ construct_poly_pred_rty (poly_preds, retty)
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              Some
                (InferResult.mk
                   (CApp { appf = appf.term; apparg = apparg'.term })#:retty
                   exists_prop localctx)
          | CAppOp { op; appopargs } ->
              let op =
                op.x#:(_find_in_ctx [%here] rctx op#->op_name_for_typectx)
              in
              (* let () = Printf.printf "op_ty : %s\n" (layout_rty op.ty) in *)
              let* appopargs =
                opt_list_to_list_opt
                @@ List.map
                     (fun v ->
                       let* v' = value_type_infer rctx lctx v in
                       Some (InferResult.map (fun v' -> (v, v')) v'))
                     appopargs
              in
              let appopargs =
                InferResult.result_list_to_list_result appopargs
              in
              let* retty =
                List.fold_left
                  (fun res (apparg, apparg') ->
                    let* rty = res in
                    over_arrow_type_apply rctx rty apparg.x#:apparg'.ty)
                  (Some op.ty) appopargs.term
              in
              let op_arg_rtys = arrow_subarrow_rtys op.ty in
              let _call_constraints =
                List.map2
                  (fun (apparg, apparg') argrty ->
                    arrow_type_arg_prop argrty apparg.x#:apparg'.ty)
                  appopargs.term op_arg_rtys
              in
              let exists_prop =
                let p = construct_call_ret_exists rctx Typectx.emp retty in
                Pp.printf "ret exists: %s\n" (layout_prop p);
                p
              in
              (* TODO: add constraints in here *)
              let localctx = appopargs.localctx in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              Some
                (InferResult.mk
                   (CAppOp { op; appopargs = List.map snd appopargs.term })#:retty
                   exists_prop localctx)
          | CMatch { matched; match_cases } ->
              (* NOTE: we drop unreachable cases *)
              let match_cases =
                InferResult.result_list_to_list_result
                @@ List.filter_map
                     (match_case_type_infer rctx lctx matched)
                     match_cases
              in
              (* TODO: might need to add branch conditions here? *)
              let unioned_ty =
                union_rtys
                @@ List.map
                     (function CMatchcase { exp; _ } -> exp.ty)
                     match_cases.term
              in
              let* matched = value_type_infer rctx lctx matched in
              let exists_prop =
                smart_and [ match_cases.exists_prop; matched.exists_prop ]
              in
              let localctx =
                Typectx.concat match_cases.localctx matched.localctx
              in
              Some
                (InferResult.mk
                   (CMatch
                      { matched = matched.term; match_cases = match_cases.term })
                   #:unioned_ty
                   exists_prop localctx)
          | CLetDeTuple { turhs; tulhs; body } ->
              let* turhs' = value_type_infer rctx lctx turhs in
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
              let* body = term_type_infer rctx' lctx body in
              let rty = Rctx.diff_exists_rty [%here] rctx' rctx body.term.ty in
              Some
                (InferResult.replace_term
                   (CLetDeTuple { turhs = turhs'.term; tulhs; body = body.term })
                   #:rty
                   body)
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
  and term_type_check (rctx : rctx) (lctx : localctx Typectx.ctx)
      (e : (Nt.t, Nt.t term) typed) (rty : Nt.t rty) :
      (Nt.t rty, Nt.t rty term) typed option =
    match e.x with
    | CVal v ->
        let* v = value_type_check rctx lctx v rty in
        Some (CVal v)#:v.ty
    | _ -> (
        let () = pprint_typing_check_term rctx (e, rty) in
        match e.x with
        | CVal _ -> _die [%here]
        | CErr -> Some CErr#:rty
        | CLetDeTuple _ -> failwith "unimp"
        | CApp _ | CAppOp _ | CMatch _ | CLetE _ | CRecord _ | CField _ ->
            let* e' = term_type_infer rctx lctx e in
            if sub_rty rctx (e'.term.ty, rty) e'.exists_prop then
              Some e'.term.x#:rty
            else (
              _warinning_subtyping_error [%here] (e'.term.ty, rty);
              _warinning_typing_error [%here] (layout_typed_term e, rty);
              None))
  (* | CLetE { rhs; lhs; body } -> *)
  (*     let* rhs = term_type_infer rctx rhs in *)
  (*     let rctx', lhs = Rctx.add_var rctx lhs.x #: rhs.ty in *)
  (*     let* body = term_type_check rctx' body rty in *)
  (*     Some (CLetE { rhs; lhs; body }) #: rty *)
  and match_case_type_infer (rctx : rctx) (lctx : localctx Typectx.ctx)
      (matched : (Nt.t, Nt.t value) typed) (x : Nt.t match_case) :
      Nt.t rty match_case InferResult.t option =
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
        let* exp' = term_type_infer rctx' lctx exp in
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
          (InferResult.replace_term
             (CMatchcase
                {
                  constructor = constructor.x#:constructor_rty;
                  args;
                  exp = exp'.term;
                })
             exp')
  in
  (value_type_check, term_type_check)

let value_type_check bctx ctx (value, rty) =
  (fst @@ type_check_group bctx) ctx Typectx.emp value rty

let term_type_check bctx ctx (value, rty) =
  (snd @@ type_check_group bctx) ctx Typectx.emp value rty
