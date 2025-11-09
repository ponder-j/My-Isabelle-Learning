theory Task7_ApplyBothSound
  imports Main
begin

(* Task 7 : Prove that it is sound to apply both of these optimisations successively to any circuit. *)
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
  "opt_DM (NOT c) = NOT (opt_DM c)"
| "opt_DM (AND (NOT c1) (NOT c2)) = NOT (OR (opt_DM c1) (opt_DM c2))"
| "opt_DM (AND c1 c2) = AND (opt_DM c1) (opt_DM c2)"
| "opt_DM (OR (NOT c1) (NOT c2)) = NOT (AND (opt_DM c1) (opt_DM c2))"
| "opt_DM (OR c1 c2) = OR (opt_DM c1) (opt_DM c2)"
| "opt_DM TRUE = TRUE"
| "opt_DM FALSE = FALSE"
| "opt_DM (INPUT i) = INPUT i"

lemma sound1: "simulate c ρ = simulate (opt_DM (c)) ρ"
  apply (induct c rule: opt_DM.induct)
  by simp+

lemma sound2: "simulate c ρ = simulate (opt_NOT c) ρ"
  apply (induct c rule: opt_NOT.induct)
  by simp+

theorem ApplyBothisSound: "simulate c ρ = simulate (opt_DM (opt_NOT c)) ρ"
  apply (induct c rule: opt_DM.induct)
  using sound1 sound2 apply auto
  done
