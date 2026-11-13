(* let rec gen_line (dep : int) : int tree = *)
(*   if dep == 0 then Leaf *)
(*   else *)
(*     let rest : int tree = gen_line (dep - 1) in *)
(*     if bool_gen () then Node (int_gen (), Leaf, rest) *)
(*     else Node (int_gen (), rest, Leaf) *)

let[@assert] rty ?r:(dep = ((v >= 0 : [%v: int]) [@over])) =
  (depth v == dep && tree_num_leaf v == dep + 1 : [%v: int tree])
