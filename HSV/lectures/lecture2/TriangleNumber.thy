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

end