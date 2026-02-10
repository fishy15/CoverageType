open Language
open Zutils
open Bidirect
open Zdatatype

let _log = Myconfig._log_result

type 'a task =
  | TypeCheck of string * 'a rty
  | ValidCheck of string * 'a prop
  | SatCheck of string * 'a prop

let _type_check_info name rty =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Check %s:@}\n" name;
  Pp.printf "@{<bold>check against with:@} %s\n" (layout_rty rty)

let _type_check_succ name =
  _log @@ fun _ ->
  Pp.printf "@{<bold>@{<yellow>Task %s, type check succeeded@}@}\n" name

let _type_check_fail name =
  _log @@ fun _ ->
  Pp.printf "@{<bold>@{<red>Task %s, type check failed@}@}\n" name

let _valid_succ name prop =
  Pp.printf "@{<bold>@{<yellow>Query %s (%s) is valid.@}@}\n" name
    (layout_prop prop)

let _valid_fail name prop =
  Pp.printf "@{<bold>@{<red>Query %s (%s) is invalid.@}@}\n" name
    (layout_prop prop)

let _sat_succ name prop =
  Pp.printf "@{<bold>@{<yellow>Query %s (%s) is sat.@}@}\n" name
    (layout_prop prop)

let _sat_fail name prop =
  Pp.printf "@{<bold>@{<red>Query %s (%s) is unsat.@}@}\n" name
    (layout_prop prop)

let _task_fail task =
  match task with
  | TypeCheck (name, _) -> _type_check_fail name
  | ValidCheck (name, prop) -> _valid_fail name prop
  | SatCheck (name, prop) -> _sat_fail name prop

let mk_imp_m bctx items =
  List.fold_left
    (fun (bctx, imp_m) item ->
      match item with
      | MFuncImp { name; body; _ } -> (bctx, StrMap.add name.x body imp_m)
      | MRty { is_assumption = true; name; rty } ->
          (rty_add_to_right bctx name#:rty, imp_m)
      | _ -> (bctx, imp_m))
    (bctx, StrMap.empty) items

let mk_invs items =
  List.fold_left
    (fun m -> function
      | MLocalRty { host_name; name; rty; _ } ->
          StrMap.update host_name
            (function
              | None -> Some [ name#:rty ] | Some l -> Some ((name#:rty) :: l))
            m
      | _ -> m)
    StrMap.empty items

let mk_tasks items =
  List.filter_map
    (function
      | MRty { is_assumption = false; name; rty } ->
          Some (TypeCheck (name, rty))
      | MCheckValid { name; prop } -> Some (ValidCheck (name, prop))
      | MCheckSat { name; prop } -> Some (SatCheck (name, prop))
      | _ -> None)
    items

type resu = Suc of built_in_ctx | Fai

let item_check bctx inv_m imp_m (name, rty) =
  let imp =
    StrMap.find
      (spf "The source code of given refinement type '%s' is missing." name)
      imp_m name
  in
  let () = Pp.printf "@{<bold>imp_m(%s)@}\n%s\n" name (layout_typed_term imp) in
  let () = Statistic.create_stat name imp in
  let () = Statistic.stat_update_rty (name, counter_rty_qt_qpred rty) in
  let invs = match StrMap.find_opt inv_m name with None -> [] | Some l -> l in
  let sol, rty = instantiate_rty_by_nty [%here] rty imp.ty in
  let invs = List.map (fun x -> x#=>(map_rty (Nt.msubst_nt sol))) invs in
  let () = _type_check_info name rty in
  let time, res =
    clock (fun () ->
        term_type_check bctx (Common.Rctx.emp name [] invs) (imp, rty))
  in
  let () = Statistic.stat_total_time (name, time) in
  let () = Statistic.store_stat stat_file in
  match res with
  | Some _ ->
      _type_check_succ name;
      Suc (rty_add_to_right bctx name#:rty)
  | None ->
      _type_check_fail name;
      (* let () = _die [%here] in *)
      Fai

let _check_prop_valid name prop =
  let res = Prover.check_valid (Some name, prop) in
  (match res with
  | true -> _valid_succ name prop
  | false -> _valid_fail name prop);
  res

let _check_prop_sat name prop =
  let res = Prover.check_sat_bool (Some name, prop) in
  (match res with true -> _sat_succ name prop | false -> _sat_fail name prop);
  res

let check_task bctx inv_m imp_m task =
  match task with
  | TypeCheck (name, rty) -> item_check bctx inv_m imp_m (name, rty)
  | ValidCheck (name, prop) -> (
      match _check_prop_valid name prop with true -> Suc bctx | false -> Fai)
  | SatCheck (name, prop) -> (
      match _check_prop_sat name prop with true -> Suc bctx | false -> Fai)

let struc_check bctx items =
  let bctx, imp_m = mk_imp_m bctx items in
  let inv_m = mk_invs items in
  let tasks = mk_tasks items in
  let _, res =
    List.fold_left
      (fun (bctx, failed) task ->
        match check_task bctx inv_m imp_m task with
        | Suc bctx -> (bctx, failed)
        | Fai -> (bctx, failed @ [ task ]))
      (bctx, []) tasks
  in
  let () =
    _log @@ fun _ ->
    Pp.printf "@{<bold>Summary (total %i tasks):@}\n" (List.length tasks)
  in
  let () =
    match res with
    | [] ->
        _log @@ fun _ -> Pp.printf "@{<bold>@{<yellow>All tasks succeeded@}@}\n"
    | _ -> _log @@ fun _ -> List.iter _task_fail res
  in
  Some bctx
