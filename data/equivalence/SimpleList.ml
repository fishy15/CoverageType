let list_gen (n : int) : int list = [n]

let[@library] rand_int ?r:(x : unit) = (true : [%v : int])

let[@assert] list_gen ?r:(n : int) =
  (((fun (x : int) -> (list_len v > 0) && ((list_mem v x) #==> (x == n))) : [%v: int list]) [@eqv eqv_sort])

(* let[@assert] list_gen ?r:(n : int) = *)
(*   (((fun (x : int) -> (list_mem v x) #==> (x == n)) : [%v: int list]) [@eqv eqv_sort]) *)

let check : int = 1
(* let check : int = rand_int () *)

(* let[@assert] check = *)
(*   ((fun (x : int) *)
(*         ((_x_0 [@exists]) : int list) ((_x_1 [@exists]) : int list) *)
(*         ((_y_0 [@exists]) : int list) ((_y_1 [@exists]) : int list) ((_y_2 [@exists]) : int list) -> *)
(*        tl _x_1 _x_0 *)
(*     && tl _y_2 _y_1 *)
(*     && tl _y_1 _y_0 *)
(*     && hd _x_1 x *)
(*     && hd _y_2 x *)
(*     && hd _y_1 x *)
(*     && eqv_sort _x_1 _y_2) : [%v: int]) *)

(* ∀n, (∀v, ((∀x, ((list_len v) > 0 𐌡 (list_mem v x => x == n))) => (∃v', (eqv_sort v v' 𐌡 (∃_x_0, ((list_len _x_0) == 0 𐌡 hd v' n 𐌡 tl v' _x_0)))))) *)
(* let[@assert] check = *)
(*   ((fun (n : int) *)
(*         (ys : int list) *)
(*         ((_x_0 [@exists]) : int list) ((_x_1 [@exists]) : int list) *)
(*         (x : int)  *)
(*         ((_x_0' [@exists]) : int list) -> *)
(*        tl _x_1 _x_0 *)
(*     && hd _x_1 n *)
(*     && ((((list_len ys > 0) && ((list_mem ys x) #==> (x == n))) #==> (eqv_sort _x_1 ys && hd _x_1 n && tl _x_1 _x_0')))) *)
(*       : [%v: int]) *)
let[@assert] check =
  ((fun (n : int)
        (v1 : int list) ->
    (fun (x : int) -> (list_len v1 > 0) && ((list_mem v1 x) #==> (x == n))) #==>
    (fun (v2 : int list) -> 
      ((list_len v2 == 1) && (hd v2 n)) #==>
      (eqv_sort v1 v2 &&
        (fun ((_x_0 [@exists]) : int list) -> (list_len _x_0 == 0 && hd v2 n && tl v2 _x_0))))) : [%v: int])
