let f (x : int list) : int list =
  let x' : int list = 1 :: x in
  match x' with h :: t -> t | [] -> []

let[@assert] f ?r:(x : int list) = (v == x : [%v: int list])
