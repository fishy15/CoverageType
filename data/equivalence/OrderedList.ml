let choose (xs : int list) (ys : int list) : int list =
  if bool_gen () then xs else ys

let[@assert] choose ?r:(xs : int list) ?r:(ys : int list) =
  (v == xs || v == ys : [%v: int list]) 

let rec list_gen (lo : int) (hi : int) : int list =
  if lo == hi then choose [] [hi]
  else
    let (rest : int list) = list_gen (lo + 1) hi in
    choose rest (lo :: rest)

let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) =
  (((fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi))
    : [%v: int list]) [@eqv eqv_sort])
