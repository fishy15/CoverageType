let list_gen (n : int) : int list = [n]

let[@assert] list_gen ?r:(n : int) =
  (((fun (x : int) (len : int) -> ((list_mem v x) #==> (x == n) && list_len v == len)) : [%v: int list]) [@eqv eqv_sort])
  (* (((fun (x : int) -> (list_mem v x) #==> (x == n)) : [%v: int list]) [@eqv eqv_sort]) *)
