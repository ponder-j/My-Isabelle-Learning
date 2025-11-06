theory TriangleNumber
  imports Main
begin

fun triangle :: "nat ⇒ nat" where
  "triangle n = (if n = 0 then 0 else n + triangle (n-1))"

theorem triangle_closed_form: "triangle n = n * (n + 1) div 2"
    apply (induct n)
    apply simp
    by (metis One_nat_def Zero_not_Suc add_Suc_right diff_Suc_Suc diff_zero distrib_left div_mult_self1 mult.commute
    nat_arith.rule0 numeral_2_eq_2 triangle.elims)

fun tet :: "nat ⇒ nat" where
  "tet n = (if n = 0 then 0 else triangle n + tet (n-1))"

theorem tet_closed_form: "tet n = n * (n + 1) * (n + 2) div 6"
proof (induct n)
    case 0
    (* ?case 会自动带入需要证明的变量 n=0 *)
    show ?case by simp
next
    case (Suc n)
    (* IH: Induction Hypothesis *)
    assume IH: "tet n = n * (n + 1) * (n + 2) div 6"

    

end