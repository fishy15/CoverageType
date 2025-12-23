let[@library] int_range ?r:(a = ((true : [%v: int]) [@over]))
    ?r:(b = ((a <= v : [%v: int]) [@over])) =
  M (a <= v && v <= b : [%v: int])

val eqv_sort : int list -> int list -> bool

let[@library] eqv_definition
    ?r:(l1 = ((true : [%v: int list]) [@over]))
    ?r:(l2 = ((true : [%v: int list]) [@over])) =
  M (iff (eqv_sort l1 l2) (fun (x : int) -> iff (list_mem l1 x) (list_mem l2 x)) : [%v: int])

let choose (xs : int list) (ys : int list) : int list =
  if bool_gen () then xs else ys

let[@assert] choose ?r:(xs = ((true : [%v: int list]) [@over]))
    ?r:(ys = ((true : [%v: int list]) [@over])) =
  (v == xs || v == ys : [%v: int list]) 

let rec list_gen (lo : int) (hi : int) : int list =
  if lo == hi then choose [] [lo]
  else
    let (rest : int list) = list_gen lo (hi - 1) in
    choose rest (hi :: rest)

let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) =
  (((fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi))
    : [%v: int list]) [@eqv eqv_sort])
