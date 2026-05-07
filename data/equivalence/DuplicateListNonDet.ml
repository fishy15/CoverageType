let rec duplicate_list_gen_nondet (s : int) (x : int) : int list =
    let h : int = if bool_gen () then x else x + 1 in
    if s == 1 then [h] else h :: duplicate_list_gen_nondet (s - 1) x

let[@assert] duplicate_list_gen_nondet ?r:(s = ((0 < v : [%v: int]) [@over])) ?r:(x : int) =
  (((list_len v > 0) && (fun (u : int) -> (list_mem v u) #==> (u == x))
    : [%v: int list]) [@eqv eqv_set])
