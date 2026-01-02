val eqv_sort : int list -> int list -> bool

let[@library] eqv_definition
    ?r:(l1 = ((true : [%v: int list]) [@over]))
    ?r:(l2 = ((true : [%v: int list]) [@over])) =
  M (iff (eqv_sort l1 l2) (fun (x : int) -> iff (list_mem l1 x) (list_mem l2 x)) : [%v: int])

let list_gen: int list = [1; 2; 3]

let[@assert] list_gen =
  (((fun (x : int) -> (1 <= x && x <= 3) #==> (list_mem v x)) : [%v: int list]) [@eqv eqv_sort])
