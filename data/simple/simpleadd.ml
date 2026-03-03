let f (x : int) : int =
    let y : int = if bool_gen () then 1 else 2 in
    let z : int = if bool_gen () then 3 else 4 in
    y + z

let[@assert] f ?r:(x : int) =
  (4 <= v && v <= 6 : [%v: int])
