theory HSV_tasks_2020 imports Complex_Main begin

section ‹Task 1: proving that "3 / sqrt 2" is irrational.›

(* In case it is helpful, the following theorem is copied from Chapter 3 of the worksheet. *)
theorem sqrt2_irrational: "sqrt 2 ∉ ℚ"
proof auto
  assume "sqrt 2 ∈ ℚ"
  then obtain m n where 
    "n ≠ 0" and "¦sqrt 2¦ = real m / real n" and "coprime m n" 
    by (rule Rats_abs_nat_div_natE)
  hence "¦sqrt 2¦^2 = (real m / real n)^2" by auto 
  hence "2 = (real m / real n)^2" by simp
  hence "2 = (real m)^2 / (real n)^2" unfolding power_divide by auto
  hence "2 * (real n)^2 = (real m)^2"
    by (simp add: nonzero_eq_divide_eq `n ≠ 0`)
  hence "real (2 * n^2) = (real m)^2" by auto
  hence *: "2 * n^2 = m^2"
    using of_nat_power_eq_of_nat_cancel_iff by blast
  hence "even (m^2)" by presburger
  hence "even m" by simp
  then obtain m' where "m = 2 * m'" by auto
  with * have "2 * n^2 = (2 * m')^2" by auto
  hence "2 * n^2 = 4 * m'^2" by simp
  hence "n^2 = 2 * m'^2" by simp
  hence "even (n^2)" by presburger
  hence "even n" by simp
  with `even m` and `coprime m n` show False by auto
qed

theorem "3 / sqrt 2 ∉ ℚ" 
  sorry (* TODO: Complete this proof. *)

section ‹Task 2: Centred pentagonal numbers.›

fun pent :: "nat ⇒ nat" where
  "pent n = (if n = 0 then 1 else 5 * n + pent (n - 1))"

value "pent 0" (* should be 1 *)
value "pent 1" (* should be 6 *)
value "pent 2" (* should be 16 *)
value "pent 3" (* should be 31 *)

theorem "pent n = (5 * n^2 + 5 * n + 2) div 2"
  sorry (* TODO: Complete this proof. *)


section ‹Task 3: Lucas numbers.›

fun fib :: "nat ⇒ nat" where
  "fib n = (if n = 0 then 0 else if n = 1 then 1 else fib (n - 1) + fib (n - 2))"

value "fib 0" (* should be 0 *)
value "fib 1" (* should be 1 *)
value "fib 2" (* should be 1 *)
value "fib 3" (* should be 2 *)

thm fib.induct (* rule induction theorem for fib *)

(* TODO: Complete this task. *)


section ‹Task 4: Balancing circuits.›

(* Here is a datatype for representing circuits, copied from the worksheet *)

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text ‹Delay (assuming all gates have a delay of 1)›

(* The following "delay" function also appeared in the 2019 coursework exercises. *)

fun delay :: "circuit ⇒ nat" where
  "delay (NOT c) = 1 + delay c"
| "delay (AND c1 c2) = 1 + max (delay c1) (delay c2)"
| "delay (OR c1 c2) = 1 + max (delay c1) (delay c2)" 
| "delay _ = 0"

(* TODO: Complete this task. *)


section ‹Task 5: Extending with NAND gates.›

(* TODO: Complete this task. *)

end