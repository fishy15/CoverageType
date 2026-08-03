open Language
open Zutils

let run_subtype_check source_file =
  let code = Preprocess.preprocess [ source_file ] in
  let _, rty1 = get_rty_by_name code "rty1" in
  let _, rty2 = get_rty_by_name code "rty2" in
  let ctx = Typectx.emp in
  let _ =
    pprint_subtyping
      (fun () -> Typectx.pprint_ctx layout_rty Typectx.emp)
      (rty1, rty2) ()
  in
  let _ = Preprocess.load_bctx () in
  let () = Statistic.create_subtyping_stat () in
  Auxtyping.sub_rty (Typing.Rctx.emp "subtyping" [] []) (rty1, rty2)

let run_nonemptiness_check source_file =
  let code = Preprocess.preprocess [ source_file ] in
  let _, rty = get_rty_by_name code "rty" in
  let rec base_rty_and_rctx rty rctx =
    match rty with
    | RtyBase _ -> (rty, rctx)
    | RtyArr { arg; argrty; retty } ->
        let rctx = Typing.Rctx.add_var rctx arg#:argrty in
        base_rty_and_rctx retty rctx
    | _ ->
        _die_with [%here]
          (spf "type should be base or arrow only, but got %s\n"
             (layout_rty rty))
  in
  let rty, rctx = base_rty_and_rctx rty (Typing.Rctx.emp "nonempty" [] []) in
  let _ = Preprocess.load_bctx () in
  let () = Statistic.create_ignored_stat "nonempty" in
  Auxtyping.non_emptiness_rty rctx rty
