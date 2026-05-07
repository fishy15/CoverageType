let list_gen (n : int) : int list = [n; n]

let[@assert] list_gen ?r:(n : int) =
  (((fun (x : int) -> (list_len v > 0) && ((list_mem v x) #==> (x == n))) : [%v: int list]) [@eqv eqv_set])
