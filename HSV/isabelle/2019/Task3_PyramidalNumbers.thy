theory Task3_PyramidalNumbers
imports Main
begin

(* Task 3 :  Pyramidal Numbers *)
fun py :: "nat ⇒ nat"
  where "py 0 = 0" | 
        "py (Suc n) = (Suc n)^2 + py(n)"


lemma py_mult_6: "6 * py n = n * (n + 1) * (2 * n + 1)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case 
    by (simp add: algebra_simps power2_eq_square)
qed

theorem "py n = (2 * n + 1) * (n + 1) * n div 6"
proof -
  have "6 * py n = (2 * n + 1) * (n + 1) * n"
    using py_mult_6 by (simp add: algebra_simps)
  then show ?thesis
    by simp
qed

end