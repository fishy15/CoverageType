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

(* let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) = *)
(*   ((fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi)) *)
(*     : [%v: int list]) *)

(* let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) = *)
(*   (fun (x : int) (a : int) (b : int) (v1 : int) (v2 : int) ->  *)
(*     ((list_mem v x) #==> (lo <= x && x <= hi)) && ((0 <= a && a < b && b < list_len v && list_nth_pred v a v1 && list_nth_pred v b v2) #==> (v1 > v2)) *)
(*       : [%v: int list]) *)

(* let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo <= v : [%v: int]) [@over])) = *)
(*   (fun (x : int) (a : int) (b : int) ->  *)
(*     (list_mem v x) #==> (lo <= x && x <= hi) && sorted v [%v: int list]) *)
