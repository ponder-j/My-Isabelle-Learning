theory Sqrt2Irrational
imports Complex_Main
begin

find_theorems "_ ∈ ℚ"
(* 有理数 ration, 简称 rat *)
thm Rats_abs_nat_div_natE

(* ?x ∈ ℚ ⟹ (⋀m n. n ≠ 0 ⟹ ¦?x¦ = real m / real n ⟹ coprime m n ⟹ ?thesis) ⟹ ?thesis *)

theorem sqrt2_irrational: "sqrt 2 ∉ ℚ"
proof
    (* 反证法：先假设 sqrt 2 是有理数 *)
    assume "sqrt 2 ∈ ℚ"
    then obtain m n
        where "¦sqrt 2¦ = real m / real n"
            and coprimemn: "coprime m n"
            and n_nonzero: "n ≠ 0"
        by (rule Rats_abs_nat_div_natE)
    hence "2 = (real m / real n) ^ 2"
        by (metis abs_numeral real_sqrt_abs real_sqrt_power)
    hence "2 = (real m) ^ 2 / (real n) ^ 2"
        by (simp add: power_divide)
    hence omg: "2 * (n^2) = m^2"
        by (metis (mono_tags, lifting) n_nonzero nonzero_eq_divide_eq of_nat_0 of_nat_mult
    of_nat_numeral of_nat_power_eq_of_nat_cancel_iff zero_eq_power2)
    hence "even(m^2)"
        by (metis dvd_triv_left)
    hence "even m"
        by simp
    then obtain k where "m = 2 * k"
        by auto
    hence "m^2 = 4 * k^2"
        by simp
    hence "2 * (n^2) = 4 * k^2"
        using omg
        by presburger
    hence "n^2 = 2 * k^2"
        by simp
    hence "even(n^2)"
        by (metis dvd_triv_left)
    hence "even n"
        by simp
    thus False
        using ‹even m› coprimemn by fastforce
qed

end