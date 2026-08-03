open Checks

let run_nonempty_test source_file =
  Statistic.clear ();
  let root = Sys.getenv "DUNE_SOURCEROOT" in
  Sys.chdir root;
  Myconfig.meta_config_path := "test/meta-config.json";
  let source_file = Filename.concat root source_file in
  run_nonemptiness_check source_file

let%test "[v: int | true]" = run_nonempty_test "data/nonempty/v_true.ml"

let%test "[v: int | false]" =
  not @@ run_nonempty_test "data/nonempty/v_false.ml"

let%test "[v: bool | v == (x > 0)]" =
  run_nonempty_test "data/nonempty/is_geq_zero.ml"
