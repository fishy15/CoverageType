let choose (xs : int list) (ys : int list) : int list =
  if bool_gen () then xs else ys

let[@assert] choose ?r:(xs : int list) ?r:(ys : int list) =
  (v == xs || v == ys : [%v: int list]) 

let rec list_gen (lo : int) (hi : int) : int list =
  if lo == hi then choose [] [hi]
  else
    let (rest : int list) = list_gen (lo + 1) hi in
    choose rest (lo :: rest)

(*
let[@assert] list_gen ?r:(lo : int) ?r:(hi = ((lo == v : [%v: int]) [@over])) =
  (((fun (x : int) -> (list_mem v x) #==> (lo <= x && x <= hi))
    : [%v: int list]) [@eqv eqv_sort])
*)

(* ∀lo, (∀v, ((∀x, (list_mem v x => (lo <= x 𐌡 x <= lo))) => (∃v', (eqv_sort v v' 𐌡 (∃_x_12, ((list_len _x_12) == 0 𐌡 (∃_x_13, ((list_len _x_13) == 0 𐌡 (∃_x_14, (hd _x_14 lo 𐌡 tl _x_14 _x_13 𐌡 (v' == _x_12 ᐯ v' == _x_14))))))))))) *)

let[@valid] init =
	fun (lo : int) (v : int list) (v' : int list) ->
		(fun (x : int) -> (list_mem v x)#==>(lo <= x && x <= lo))#==>
		 ((fun (_x_12 : int list) (_x_13 : int list) (_x_14 : int list) -> (list_len _x_12 == 0 && list_len _x_13 == 0 && hd _x_14 lo && tl _x_14 _x_13) && (v' == _x_12 || v' == _x_14))#==>
			(eqv_sort v v'))

let[@valid] init =
	fun (lo : int) (v : int list) ->
    (fun (x : int) -> (list_mem v x)#==>(lo <= x && x <= lo))#==>
    (fun ((v' [@ex]) : int list) ->
      eqv_sort v v' &&
      fun ((_x_12 [@ex]) : int list) ((_x_13 [@ex]) : int list) ((_x_14 [@ex]) : int list) ->
        list_len _x_12 == 0 &&
        list_len _x_13 == 0 &&
        hd _x_14 lo &&
        tl _x_14 _x_13 &&
        (v' == _x_12 || v' == _x_14))

let[@valid] init =
	fun (lo : int) (v : int list) ->
    ((fun (x : int) -> (list_mem v x)#==>(lo <= x && x <= lo)) && (list_len v > 0))#==>
    (fun ((v' [@ex]) : int list) ->
      fun ((_x_13 [@ex]) : int list) ((_x_14 [@ex]) : int list) ->
        list_len _x_13 == 0 &&
        hd _x_14 lo &&
        tl _x_14 _x_13 &&
        v' == _x_14 &&
        eqv_sort v v')

let[@valid] init = false

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
