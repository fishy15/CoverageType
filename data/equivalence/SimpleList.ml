let list_gen (n : int) : int list = [n]

let list_gen_nondet (n : int) : int list = 
  if bool_gen () then [n] else [n+1]

let[@assert] list_gen ?r:(n : int) =
  (((fun (x : int) -> (list_len v > 0) && ((list_mem v x) #==> (x == n))) : [%v: int list]) [@eqv eqv_set])

(* let[@assert] list_gen_nondet ?r:(n : int) = *)
(*   (((fun (x : int) -> (list_len v > 0) && ((list_mem v x) #==> (x == n))) : [%v: int list]) [@eqv eqv_set]) *)

(* let[@valid] list_gen_check  = *)
(*   fun (n : int) ->  *)
(*   (fun ((v'' [@ex]) : int list) -> fun ((nil [@ex]) : int list) -> (list_len nil == 0 && hd v'' n && tl v'' nil))#==> *)
(*   (fun (v : int list) -> *)
(*     implies *)
(*       (fun (x : int) -> *)
(*          ((list_len v) > 0) && (implies (list_mem v x) (x == n))) *)
(*       (fun (((v')[@exists ]) : int list) -> *)
(*          (eqv_set v v') && *)
(*            (fun (((_x_2)[@exists ]) : int list) -> *)
(*               ((list_len _x_2) == 0) && ((hd v' n) && (tl v' _x_2))))) *)
(**)
(* let[@valid] list_gen_nondet = fun (n : int) -> *)
(*   (fun (h : int) -> (h == n || h == n+1)#==>(fun ((v'' : int list)) ((nil [@ex]) : int list) -> (hd v'' h && tl v'' nil)))#==> *)
(*   (fun (v : int list) -> *)
(*     implies *)
(*       (fun (x : int) -> *)
(*          ((list_len v) > 0) && (implies (list_mem v x) (x == n))) *)
(*       (fun (((v')[@exists ]) : int list) -> *)
(*          (eqv_set v v') && *)
(*            ((fun (((_x_9)[@exists ]) : int list) -> *)
(*                ((list_len _x_9) == 0) && ((hd v' n) && (tl v' _x_9))) *)
(*               || *)
(*               (fun (((_x_12)[@exists ]) : int list) -> *)
(*                  ((list_len _x_12) == 0) && *)
(*                    ((hd v' (n + 1)) && (tl v' _x_12)))))) *)
