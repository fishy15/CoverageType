let rec repeat (n : int) : int list = if n = 0 then [] else 1 :: repeat (n - 1)

let[@assert] repeat ?r:(n = ((v >= 0 : [%v: int]) [@over])) =
  (list_len v == n && (n > 0) #==> (fun (u : int) -> list_mem v u == (u == 1))
    : [%v: int list])
    [@under]
