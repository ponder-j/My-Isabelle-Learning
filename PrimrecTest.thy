theory PrimrecTest
  imports Main
begin

primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "add x 0 = x" |
        "add x (Suc y) = Suc (add x y)"

value "add 3 5"

primrec prede :: "nat \<Rightarrow> nat"
  where "prede 0 = 0" |
        "prede (Suc x) = x"

primrec sub :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sub x 0 = x" | 
        "sub x (Suc y) = prede (sub x y)"

value "sub 8 2"

primrec time :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "time x 0 = 0" |
        "time x (Suc y) = add (time x y) x"

value "time 5 6"

primrec fact :: "nat \<Rightarrow> nat"
  where "fact 0 = 1" |
        "fact (Suc x) = time (Suc x) (fact x)"

(* teacher's version*)
(* primrec fact :: "nat \<Rightarrow> nat"
  where "fact 0 = 1" |
        "fact (Suc n) = time (fact n) (add n 1)" *)

value "fact 5"

primrec exp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "exp x 0 = 1" |
        "exp x (Suc y) = time (exp x y) x"

value "exp 2 5"

end