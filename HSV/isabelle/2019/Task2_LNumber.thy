theory Task2_LNumber
imports Main
begin

(* Task 2 : Prove in Isabelle that your closed form and the recursive definition coincide for all n≥0 *)
fun L :: "nat ⇒ nat"
  where "L 0 = 0" | 
        "L (Suc 0) = 1" | 
        "L (Suc (Suc n)) = 2 + L (Suc n)"

thm L.simps

theorem L_closure: "L n = max (2 * n - 1) 0"
  by (induction n rule: L.induct) auto

fun L2 :: "nat ⇒ nat"
  where "L2 n = (if n ≤ 1 then n else 2 + L2 (n - 1))"


theorem L2_closure: "L2 n = (if n = 0 then 0 else 2 * n - 1)"
  by (induction n rule: L2.induct) auto

