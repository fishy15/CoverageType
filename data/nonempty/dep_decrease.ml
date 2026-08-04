let[@assert] rty =
  let dep = (v >= 0 : [%v: int]) [@over] in
  let _x_0 = (v == (dep == 0) : [%v: bool]) [@under] in
  let tmp_2 = (not _x_0 : [%v: bool]) [@under] in
  (v == (dep - 1) : [%v: int])
