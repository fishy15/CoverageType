let f (x : int list) : int list =
  let x' : int list = 1 :: x in
  match x' with h :: t -> t | [] -> []

let[@assert] f ?r:(x : int list) = (v == x : [%v: int list])

let[@valid] tmp = fun (x : int list) ->
  (fun ((v' [@ex]) : int list) -> (hd v' 1 && tl v' x))#==>
  (fun (v : int list) ->
    implies (v == x)
      (fun (((x')[@exists ]) : int list) ->
         (hd x' 1) &&
           ((tl x' x) &&
              ((fun (((h)[@exists ]) : int) -> (hd x' h) && (tl x' v)) ||
                 (((list_len x') == 0) && ((list_len v) == 0))))))
