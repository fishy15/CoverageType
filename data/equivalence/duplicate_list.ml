let rec duplicate_list_gen (s : int) (x : int) : int list =
  if s == 0 then [] else x :: duplicate_list_gen (s - 1) x

(* let[@assert] duplicate_list_gen = *)
(*   let s = (v >= 0 : [%v: int]) [@over] in *)
(*   let x = (true : [%v: int]) [@over] in *)
(*   (((list_len v == s && fun (u : int) -> (list_mem v u) #==> (u == x) *)
(*     : [%v: int list]) *)
(*     [@under]) [@eqv eq]) *)

let[@valid] test = 
 fun (s : int) ->
  implies (s >= 0)
    (fun (x : int) ->
       fun (v : int list) ->
         implies
           (((list_len v) == s) &&
              (fun (u : int) -> implies (list_mem v u) (u == x)))
           (
              (eqv_sort v v) &&
                (((s == 0) && ((list_len v) == 0)) ||
                   ((not (s == 0)) &&
                      (fun (((_x_7)[@exists ]) : int list) ->
                         (
                            (eqv_sort _x_7 _x_7) &&
                              (((s - 1) < s) &&
                                 (((s - 1) >= 0) &&
                                    (((list_len _x_7) == (s - 1)) &&
                                       (fun (u_3 : int) ->
                                          implies (list_mem _x_7 u_3)
                                            (u_3 == x))))))
                           && ((hd v x) && (tl v _x_7)))))))

(* let[@assert] duplicate_list_gen = *)
(*   let s = (v >= 0 : [%v: int]) [@over] in *)
(*   let x = (true : [%v: int]) [@over] in *)
(*   (((fun (u : int) -> (list_mem v u) #==> (u == x) *)
(*     : [%v: int list]) *)
(*     [@under]) [@eqv eqv_sort]) *)
