theory tailRecursion
  imports Main
begin

fun fact_help :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "fact_help i a = 
          (if i = 0 then a
           else fact_help (i - 1) (i * a))"

definition fact2 :: "nat \<Rightarrow> nat"
  where "fact2 m \<equiv> fact_help m 1"

end