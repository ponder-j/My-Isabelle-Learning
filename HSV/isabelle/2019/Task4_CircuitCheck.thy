theory Task4_CircuitCheck
imports Main
begin

(* Write a function that checks whether a circuit contains two consecutive NOT gates. Use this function to state and prove a theorem that whenever opt_NOT is applied to a circuit, the resultant circuit never contains two consecutive NOT gates *)

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

fun simulate where
  "simulate (AND c1 c2) ρ = ((simulate c1 ρ) ∧ (simulate c2 ρ))"
| "simulate (OR c1 c2) ρ = ((simulate c1 ρ) ∨ (simulate c2 ρ))"
| "simulate (NOT c) ρ = (¬ (simulate c ρ))"
| "simulate TRUE ρ = True"
| "simulate FALSE ρ = False"
| "simulate (INPUT i) ρ = ρ i"

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

thm opt_NOT.induct

fun check_double_not where
  "check_double_not (NOT (NOT c)) = True" | 
  "check_double_not (NOT c) = check_double_not c" | 
  "check_double_not (AND c1 c2) = ((check_double_not c1) ∨ (check_double_not c2))" | 
  "check_double_not (OR c1 c2) = ((check_double_not c1) ∨ (check_double_not c2))" | 
  "check_double_not _ = False" (* _ 用于代表其他情况 *)

theorem no_double_not_after_opt_NOT: "check_double_not (opt_NOT c) = False"
  apply (induct c rule:opt_NOT.induct) (* 重要：对 c 应用 opt_NOT 函数递归结构的归纳 *)
  apply simp+
  done
(* 
Isabelle 自动根据 opt_NOT 生成 11 条规则，只要证明前面 11 条成立，则对所有情况都成立

(⋀c. ?P c ⟹ ?P (NOT (NOT c))) ⟹
(⋀v va. ?P (AND v va) ⟹ ?P (NOT (AND v va))) ⟹
(⋀v va. ?P (OR v va) ⟹ ?P (NOT (OR v va))) ⟹
(?P TRUE ⟹ ?P (NOT TRUE)) ⟹
(?P FALSE ⟹ ?P (NOT FALSE)) ⟹
(⋀v. ?P (INPUT v) ⟹ ?P (NOT (INPUT v))) ⟹
(⋀c1 c2. ?P c1 ⟹ ?P c2 ⟹ ?P (AND c1 c2)) ⟹
(⋀c1 c2. ?P c1 ⟹ ?P c2 ⟹ ?P (OR c1 c2)) ⟹
?P TRUE ⟹
?P FALSE ⟹
(⋀i. ?P (INPUT i))

⟹ ?P ?a0.0 *)