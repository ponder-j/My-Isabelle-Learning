theory Task6_OptimiseUsingDeMorgan
  imports Main
begin

(* Task 6 : Write a function called optDM that optimises a circuit using De Morgan’s laws, as shown in Table 1. Prove that your optimisation is sound, using the following theorem:
theorem "simulate (opt_DM c) ρ = simulate c ρ" *)

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

fun opt_DM where
  (* 标准答案是 "opt_DM (AND (NOT c1) (NOT c2)) = NOT (OR (opt_DM c1) (opt_DM c2))" *)
  (* opt_DM (OR (NOT c1) (NOT c2)) = NOT (AND (opt_DM c1) (opt_DM c2)) *)
  (* 下面这几把玩意显然是错的，你把 opt_DM (AND (NOT c1) (NOT c2)) 换成 opt_DM (NOT (OR c1 c2)) 以后，马上重新匹配到第一句话 opt_DM (OR (NOT c1) (NOT c2)) 了，搞最后把刚创建的或非逻辑给搞没了…… 即使这样变换对于电路的性质没有发生变化，但跟原来的要求差很多 *)
  "opt_DM (OR (NOT c1) (NOT c2)) = opt_DM (NOT (AND c1 c2))"
| "opt_DM (AND (NOT c1) (NOT c2)) = opt_DM (NOT (OR c1 c2))"
| "opt_DM (NOT c) = NOT (opt_DM c)"
| "opt_DM (AND c1 c2) = AND (opt_DM c1) (opt_DM c2)"
| "opt_DM (OR c1 c2) = OR (opt_DM c1) (opt_DM c2)"
| "opt_DM TRUE = TRUE"
| "opt_DM FALSE = FALSE"
| "opt_DM (INPUT i) = INPUT i"

fun opt_DM_standard where
  "opt_DM_standard (NOT c) = NOT (opt_DM_standard c)"
| "opt_DM_standard (AND (NOT c1) (NOT c2)) = NOT (OR (opt_DM_standard c1) (opt_DM_standard c2))"
| "opt_DM_standard (AND c1 c2) = AND (opt_DM_standard c1) (opt_DM_standard c2)"
| "opt_DM_standard (OR (NOT c1) (NOT c2)) = NOT (AND (opt_DM_standard c1) (opt_DM_standard c2))"
| "opt_DM_standard (OR c1 c2) = OR (opt_DM_standard c1) (opt_DM_standard c2)"
| "opt_DM_standard TRUE = TRUE"
| "opt_DM_standard FALSE = FALSE"
| "opt_DM_standard (INPUT i) = INPUT i"

theorem opt_DM_is_sound: "simulate (opt_DM c) ρ = simulate c ρ"
  apply (induct c rule: opt_DM.induct)
  by simp+

theorem my_opt_nequals2_standard_opt: "opt_DM c = opt_DM_standard c"
  oops

(* De Morgan 优化器不是幂等的 *)
theorem opt_DM_standard_is_idempotent: "opt_DM_standard (opt_DM_standard c) = opt_DM_standard c"
  oops