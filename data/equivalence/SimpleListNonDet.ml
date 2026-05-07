let list_gen_nondet (n : int) : int list = 
  if bool_gen () then [n] else [n+1]

let[@assert] list_gen_nondet ?r:(n : int) =
  (((fun (x : int) -> (list_len v > 0) && ((list_mem v x) #==> (x == n))) : [%v: int list]) [@eqv eqv_set])
