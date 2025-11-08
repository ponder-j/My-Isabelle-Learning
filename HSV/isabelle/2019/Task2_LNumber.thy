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
  apply (induct n)
  apply simp
  by (metis (no_types, lifting) L.simps(2,3) One_nat_def add_2_eq_Suc add_Suc_right add_Suc_shift
    diff_Suc_1' max_0R mult_2 not0_implies_Suc zero_eq_add_iff_both_eq_0)

fun L2 :: "nat ⇒ nat"
  where "L2 n = (if n ≤ 1 then n else 2 + L2 (n - 1))"

(* lemma L2_helper: "L2 (Suc n) = 2 * (Suc n) - 1"
  apply (induct n)
  apply simp
  by auto

theorem L2_closure: "L2 n = (if n = 0 then 0 else 2 * n - 1)"
  apply (cases n)
  apply simp
  using L2_helper by auto *)

lemma L2_helper: "L2 (Suc n) = 2 * (Suc n) - 1"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  assume "L2 (Suc n) = 2 * Suc n - 1"
  hence "L2 (Suc (Suc n)) = 2 + (2 * Suc n - 1)"
    using L2.simps
    by simp
  also have "... = 2 * (1 + Suc n) - 1"
    by simp
  also have "... = 2 * (Suc (Suc n)) - 1"
    by simp
  then show ?case
    by simp
qed

theorem L2_closure: "L2 n = (if n = 0 then 0 else 2 * n - 1)"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc nat)
  then show ?thesis
    using L2_helper
    by simp
qed

(* 错误示范 *)
(* 如果在一开始就使用 induct n, 在 case (Suc n) 中是不能用 n ≥ 1 这个东西的，可能是因为破坏了递归的统一性（？ *)
(* 要分类并使用 n ≥ 1 的话要像上面那样使用 cases 分类 *)
theorem L2_closure2: "L2 n = (if n = 0 then 0 else 2 * n - 1)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  (* have "n ≥ 1"
    Sledgehammering... 
    No proof found *)
  then show ?case sorry
qed

end