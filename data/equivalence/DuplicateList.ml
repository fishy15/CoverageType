let rec duplicate_list_gen (s : int) (x : int) : int list =
    if s == 1 then [x] else cons_eqv_set x (duplicate_list_gen (s - 1) x)

let[@assert] duplicate_list_gen ?r:(s = ((0 < v : [%v: int]) [@over])) ?r:(x : int) =
  (((list_len v > 0) && (fun (u : int) -> (list_mem v u) #==> (u == x))
    : [%v: int list]) [@eqv eqv_set])
