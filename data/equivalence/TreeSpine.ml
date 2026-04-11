let rec gen_spine (dep : int) : int tree =
  if dep == 0 then
    Leaf
  else if bool_gen () then
    gen_spine (dep - 1)
  else
    let ltree : int tree = gen_spine (dep - 1) in
    let rtree : int tree = gen_spine (dep - 1) in
    Node (1, ltree, rtree)

let[@assert] gen_spine ?r:(dep = (v >= 0 : [%v: int]) [@over]) =
  (depth v <= dep : [%v: int tree]) [@eqv eqv_spine]
