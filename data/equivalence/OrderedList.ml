let[@library] int_range ?r:(a = ((true : [%v: int]) [@over]))
    ?r:(b = ((a <= v : [%v: int]) [@over])) =
  M (a <= v && v <= b : [%v: int])

let choose (xs : int list) (ys : int list) : int list =
  if bool_gen () then xs else ys

let[@assert] choose ?r:(xs : int list) ?r:(ys : int list) =
  (v == xs || v == ys : [%v: int list]) 

let rec list_gen (lo : int) (hi : int) : int list =
  if lo == hi then choose [] [lo]
  else
    let (rest : int list) = list_gen lo (hi - 1) in
    choose rest (hi :: rest)

let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) =
  (((fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi))
    : [%v: int list]) [@eqv eqv_sort])

(* let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) = *)
(*   ((fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi)) *)
(*     : [%v: int list]) *)
