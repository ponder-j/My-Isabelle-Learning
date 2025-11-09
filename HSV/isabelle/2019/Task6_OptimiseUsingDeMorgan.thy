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
  "opt_DM (OR (NOT c1) (NOT c2)) = opt_DM (NOT (AND c1 c2))"
| "opt_DM (AND (NOT c1) (NOT c2)) = opt_DM (NOT (OR c1 c2))"
| "opt_DM (NOT c) = NOT (opt_DM c)"
| "opt_DM (AND c1 c2) = AND (opt_DM c1) (opt_DM c2)"
| "opt_DM (OR c1 c2) = OR (opt_DM c1) (opt_DM c2)"
| "opt_DM TRUE = TRUE"
| "opt_DM FALSE = FALSE"
| "opt_DM (INPUT i) = INPUT i"

theorem opt_DM_is_sound: "simulate (opt_DM c) ρ = simulate c ρ"
  apply (induct c rule: opt_DM.induct)
  by simp+