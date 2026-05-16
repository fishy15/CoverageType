let rec ord_gen (n : int) (lo : int) (hi : int) : int list =
  if n == 0 then []
  else if bool_gen () || lo == hi then
    cons_eqv_set lo (ord_gen (n - 1) lo hi)
  else
    ord_gen n (lo + 1) hi

let[@assert] ord_gen ?r:(n = ((v >= 0 : [%v: int]) [@over])) ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) =
  (((list_len v == n && fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi))
    : [%v: int list]) [@eqv eqv_set])
