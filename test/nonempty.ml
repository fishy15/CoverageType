open Checks

let run_nonempty_test source_file ~expected =
  Statistic.clear ();
  let root = Sys.getenv "DUNE_SOURCEROOT" in
  Sys.chdir root;
  Myconfig.meta_config_path := "test/meta-config.json";
  let source_file = Filename.concat root source_file in
  expected == run_nonemptiness_check source_file

let%test "[v: int | true]" =
  run_nonempty_test "data/nonempty/v_true.ml" ~expected:true

let%test "[v: int | false]" =
  run_nonempty_test "data/nonempty/v_false.ml" ~expected:false

let%test "[v: bool | v == (x > 0)]" =
  run_nonempty_test "data/nonempty/is_geq_zero.ml" ~expected:true
