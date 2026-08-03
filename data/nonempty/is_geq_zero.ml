let[@assert] rty =
  let size = ((v >= 0 : [%v: int]) [@over]) in
  ((v == (size == 0) : [%v: bool]) [@under])
