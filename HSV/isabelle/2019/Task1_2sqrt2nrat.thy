theory Task1_2sqrt2nrat
  imports Complex_Main
begin

(* Task 1 : Prove that 2sqrt(2) is irrational *)
theorem task1: "2 * sqrt 2 ∉ ℚ"
(* 反证法可以使用 (rule ccontr) *)
proof (rule ccontr)
  assume "¬ 2 * sqrt 2 ∉ ℚ"
  hence "sqrt 2 ∈ ℚ"
    by (metis Rats_divide Rats_number_of add_divide_distrib field_sum_of_halves mult_2)
  then obtain m n
    where "¦sqrt 2¦ = real m / real n"
      and coprimemn: "coprime m n"
      and n_nonzero: "n ≠ 0"
    by (metis Rats_abs_nat_div_natE)
  thm Rats_abs_nat_div_natE
  hence "2 = (real m / real n) ^ 2"
    by (metis abs_numeral real_sqrt_abs real_sqrt_power)
  hence "2 = (real m)^2 / (real n)^2"
    by (simp add: power_divide)
  hence "2 * (real n)^2 = (real m)^2"
    by (metis div_by_0 nonzero_divide_eq_eq zero_neq_numeral)
  hence "2 * n^2 = m^2"
    using of_nat_eq_iff by fastforce
  hence "2 dvd m^2"
    by (metis dvd_triv_left)
  hence "2 dvd m"
    by simp
  then obtain k
    where "m = 2 * k"
    by auto
  hence "2 * n^2 = (2 * k)^2"
    using ‹2 * n^2 = m^2› by auto
  hence "2 * n^2 = 4 * k^2"
    by auto
  hence "n^2 = 2 * k^2"
    by auto
  hence "2 dvd n"
    using dvdI even_power by blast
  hence "¬ coprime m n"
    using ‹even m› by auto
  thus False
    using coprimemn
    by auto
qed

end