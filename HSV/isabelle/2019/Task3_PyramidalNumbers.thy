theory Task3_PyramidalNumbers
imports Main
begin

(* Task 3 :  Pyramidal Numbers *)
fun py :: "nat ⇒ nat"
  where "py 0 = 0" | 
        "py (Suc n) = (Suc n)^2 + py(n)"

lemma lemma1: "⋀k::nat. 2 dvd (k + 1) * k"
  by simp

lemma lemma2: "⋀k::nat. 2 dvd (2 * k + 1) * (k + 1) * k"
  using lemma1
  by simp

lemma lemma3: "⋀k::nat. 3 dvd (2 * k + 1) * (k + 1) * k"
  proof -
    fix k :: nat (* 必须先固定变量！否则使用到的是全称量词的 k，无法正常分类推理 *)
    {
      assume "k mod 3 = 0"
      hence "3 dvd k" by presburger
      hence "3 dvd (2 * k + 1) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 1"
      hence "3 dvd (2 * k + 1)" by presburger
      hence "3 dvd (2 * k + 1) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 2"
      hence "3 dvd (k + 1)" by presburger
      hence "3 dvd (2 * k + 1) * (k + 1) * k" by fastforce
    } moreover {
        (* 如果这条不手动给出，那么在 ultimately 中使用 sledgehammer 出不了结果 *)
        (* 但是不给这条，直接在最后使用 by linarith 也能证出来 *)
        have "((k mod 3 = 0) ∨ (k mod 3 = 1) ∨ (k mod 3 = 2))"
            by fastforce
    }
    ultimately
    show "3 dvd (2 * k + 1) * (k + 1) * k"
        by argo
  qed

lemma divide_6: "⋀k::nat. 6 dvd (2 * k + 1) * (k + 1) * k"
proof -
  fix k :: nat
  have "2 dvd (2 * k + 1) * (k + 1) * k" using lemma2 by simp
  moreover have "3 dvd (2 * k + 1) * (k + 1) * k" using lemma3 by simp
  ultimately show "6 dvd (2 * k + 1) * (k + 1) * k" by presburger
qed

(* 错误示范 *)
(* 直接应用 lemma2 和 lemma3, 仍然会有 k 是全称量词的问题导致不能继续证明 *)
lemma divide_6_wtf: "⋀k::nat. 6 dvd (2 * k + 1) * (k + 1) * k"
    using lemma2 lemma3
    sorry

lemma simpify: "⋀n::nat. (n + 1)^2 * 6 + (2 * n + 1) * (n + 1) * n = 6 * n^2 + 12 * n + 6 + 2 * n^3 + 3 * n^2 + n"
  by (simp add: add_mult_distrib2 mult.commute numeral_Bit0 numeral_Bit1_eq_inc_double)

lemma recombine: "⋀n::nat. (2 * (n+1) + 1) * ((n+1) + 1) * (n+1) = 6 * n^2 + 12 * n + 6 + 2 * n^3 + 3 * n^2 + n"
  by (metis add.assoc add.commute add.left_commute add_mult_distrib add_mult_distrib2 left_add_twice mult.assoc
    mult.left_commute mult_2 nat_mult_1 nat_mult_1_right numeral_Bit0 numeral_Bit0_eq_double
    numeral_Bit1_eq_inc_double numeral_One one_add_one one_plus_numeral_commute power2_eq_square power3_eq_cube
    semiring_norm(3))


theorem "py n = (2 * n + 1) * (n + 1) * n div 6"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume IH: "py n = (2 * n + 1) * (n + 1) * n div 6"
  hence "py (Suc n) = (Suc n)^2 + py n"
    by auto
  also have "... = (Suc n)^2 + (2 * n + 1) * (n + 1) * n div 6"
    using IH
    by auto
  also have "... = (n + 1)^2 + (2 * n + 1) * (n + 1) * n div 6"
    by auto
  also have "... = (n + 1)^2 * 6 div 6 + (2 * n + 1) * (n + 1) * n div 6"
    by auto
  also have "... = ((n + 1)^2 * 6 + (2 * n + 1) * (n + 1) * n) div 6"
    using divide_6
    by auto
  also have "... = (6 * n^2 + 12 * n + 6 + 2 * n^3 + 3 * n^2 + n) div 6"
    using simpify by presburger
  also have "... = (2 * (Suc n) + 1) * ((Suc n) + 1) * (Suc n) div 6"
    using recombine
    using Suc_eq_plus1 by presburger
  then show ?case
    using calculation by presburger
qed

end