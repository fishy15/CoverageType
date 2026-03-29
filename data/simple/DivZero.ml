(* both of these should fail *)

let bad_div (x : int) : int = 
  let y : int = int_gen () in
  x / y

let safe_div (x : int) : int = 
  let y : int = int_gen () in
  if y == 0 then 0 else x / y

let safe2_div (x : int) : int = 
  let y' : int = int_gen () in
  let y : int = if y' == 0 then 1 else y' in
  x / y

let bad2_div (x : int) : int = 
  let y : int = int_gen () in
  x / (y + 1)

(* let[@assert] bad_div ?r:(x : int) = (true : [%v : int]) *)
(* let[@assert] safe_div ?r:(x : int) = (true : [%v : int]) *)
(* let[@assert] safe2_div ?r:(x : int) = (true : [%v : int]) *)
let[@assert] bad2_div ?r:(x : int) = (true : [%v : int])
