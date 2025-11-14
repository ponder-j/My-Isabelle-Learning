theory DatatypeTest
  imports Main
begin

datatype ITree = Leaf int | Node ITree int ITree
term Leaf
term Node

primrec  ITreeSum :: "ITree \<Rightarrow> int"
  where "ITreeSum (Leaf v) = v" |
       "ITreeSum (Node left v right) = ITreeSum left + v + ITreeSum right"

definition "ITree1 \<equiv> 
  Node 
    (Node 
      (Leaf 4) 
      5 
      (Node 
        (Leaf 1)
        8
        (Leaf 2)))
    10 
    (Node 
      (Leaf 7) 
      9 
      (Leaf 15))"

value "ITreeSum ITree1"

datatype Fruit = APPLE | ORANGE | BANANA
term APPLE
value APPLE

primrec showfruit :: "Fruit \<Rightarrow> string"
  where "showfruit APPLE  = ''it's an apple ''" |
        "showfruit ORANGE = ''it's an orange''" |
        "showfruit BANANA = ''it's a  banana''"
value "showfruit APPLE"

datatype aexp = IF bexp aexp aexp | Add aexp aexp | Sub aexp aexp | Num nat
   and   bexp = Less aexp aexp | And bexp bexp | Neg bexp

primrec evala :: "aexp \<Rightarrow> nat" and
        evalb :: "bexp \<Rightarrow> bool" where
  "evala (IF b a1 a2) = (if (evalb b) then evala a1 else evala a2)" |
  "evala (Add a1 a2) = (evala a1) + (evala a2)" |
  "evala (Sub a1 a2) = (evala a1) - (evala a2)" |
  "evala (Num a) = a" |
  "evalb (Less a1 a2) = (evala a1 < evala a2)" |
  "evalb (And b1 b2) = (evalb b1 \<and> evalb b2)" |
  "evalb (Neg b) = (\<not> evalb b)"

value "evala (IF (Less (Num 10) (Num 20)) (Num 1) (Num 2))"
(* 输出 1::nat *)
value "evalb (Less (Num 50) (Num 100))"
(* 输出 True::bool *)

end