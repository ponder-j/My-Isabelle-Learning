theory test
  imports Complex_Main
begin

lemma sqrt2_not_rat: "sqrt 2 ∉ ℚ"
proof
  assume "sqrt 2 ∈ ℚ"
  then obtain m n :: nat where n_nonzero: "n ≠ 0" and abs_sqrt2_eq: "¦sqrt 2¦ = real m / real n" and coprime_mn: "coprime m n"
    by (rule Rats_abs_nat_div_natE)
  
  have "sqrt 2 = real m / real n" using abs_sqrt2_eq by auto
  hence "sqrt 2 ^ 2 = (real m / real n) ^ 2" by simp
  hence "2 = (real m ^ 2) / (real n ^ 2)" by (simp add: power_divide)
  hence "2 * (real n ^ 2) = real m ^ 2" using n_nonzero by (simp add: nonzero_eq_divide_eq)
  hence "real (2 * n ^ 2) = real (m ^ 2)" by simp
  hence eq_nat: "2 * n ^ 2 = m ^ 2" by (subst (asm) of_nat_eq_iff)
  
  have "even (2 * n^2)" by simp
  hence "even (m^2)" using eq_nat by simp
  hence "even m" by simp
  then obtain k where m_def: "m = 2 * k" by (auto elim: evenE)
  
  have "2 * n ^ 2 = (2 * k) ^ 2" using eq_nat m_def by simp
  hence "2 * n ^ 2 = 4 * k ^ 2" by simp
  hence "n ^ 2 = 2 * k ^ 2" by simp
  hence "2 dvd n^2" by simp
  hence "2 dvd n" by simp
  hence "even n" by simp
  
  have "2 dvd gcd m n" using `even m` `even n` by simp
  hence "2 dvd 1" using coprime_mn by simp
  thus False by (auto dest: dvd_imp_le)
qed

theorem three_div_sqrt2_not_rat: "3 / sqrt 2 ∉ ℚ"
proof
  assume "3 / sqrt 2 ∈ ℚ"
  then obtain q where "3 / sqrt 2 = q" and "q ∈ ℚ" by blast
  
  have "q ≠ 0" 
  proof
    assume "q = 0"
    hence "3 / sqrt 2 = 0" using `3 / sqrt 2 = q` by simp
    thus False by simp
  qed
  
  have "sqrt 2 = 3 / q" using `3 / sqrt 2 = q` `q ≠ 0` by (simp add: field_simps)
  moreover have "3 / q ∈ ℚ" using `q ∈ ℚ` `q ≠ 0` by (simp add: Rats_divide)
  ultimately have "sqrt 2 ∈ ℚ" by simp
  thus False using sqrt2_not_rat by simp
qed

end
