theory TotalorPartial
  imports Complex_Main
begin

definition sqrt :: "real \<rightharpoonup> real"
  where "sqrt r \<equiv> (if r \<ge> 0 then Some (root 2 r) else None)"

definition Pred :: "nat \<rightharpoonup> nat"
where "Pred n \<equiv> (if n > 0 then  Some (n - 1) else None)"
value "Pred 9"
(* 输出 "Some 8" :: "nat option" *)
value "Pred 0"
(* 输出 "None" :: "nat option" *)

definition minus_nat :: "nat \<Rightarrow> nat \<rightharpoonup> nat"
  where "minus_nat a b \<equiv> (if a \<ge> b then Some (a - b) else None)"

value "minus_nat 6 3"
(* 输出 "Some 3" :: "nat option" *)
value "minus_nat 3 8"
(* 输出 "None" :: "nat option" *)

end