let rec ord_gen (n : int) (lo : int) (hi : int) : int list =
  if n == 0 then []
  else
    let x : int = int_range_inc lo hi in
    x :: ord_gen (n - 1) x hi

let[@assert] ord_gen ?r:(n = ((v >= 0 : [%v: int])) [@over]) ?r:(lo : int) ?r:(hi = ((lo == v : [%v: int]) [@over])) =
  (((list_len v == n && fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi))
    : [%v: int list]) [@eqv eqv_set])
