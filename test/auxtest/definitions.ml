open Ast
open Zdatatype
open Sugar

(* An inline test's cwd is its stanza's build dir, e.g. [_build/default/test/fast],
   two levels below the project root. *)
let project_root = Filename.dirname (Filename.dirname (Sys.getcwd ()))

let reset_state () =
  Statistic.clear ();
  Rename.reset ()

let run_test source_file =
  reset_state ();
  Sys.chdir project_root;
  let cfg_root = Yojson.Safe.from_file "test/meta-config.json" in
  TypecheckerConfig.bootstrap cfg_root;
  let code = Preprocess.preprocess [ source_file ] in
  let _, passed, failed = Typing.struc_check (Preprocess.load_bctx ()) code in
  Printf.printf "passing: %s\n" (List.split_by_comma Fun.id passed);
  Printf.printf "failing: %s\n" (List.split_by_comma Fun.id failed)

let run_strict_nonemptiness_check ~expected source_file =
  reset_state ();
  Sys.chdir project_root;
  let cfg_root = Yojson.Safe.from_file "test/meta-config.json" in
  TypecheckerConfig.bootstrap cfg_root;
  let code = Preprocess.preprocess [ source_file ] in
  let _, rty = get_rty_by_name code "rty" in
  let bctx = Preprocess.load_bctx () in
  let () = Statistic.create_empty_stat "strict-nonemptiness" () in
  let res =
    Auxtyping.strict_non_emptiness_rty bctx
      (Typing.Rctx.emp "strict-nonemptiness" [] [])
      rty
  in
  res == expected
