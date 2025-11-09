theory Task9_NeverIncreaseDelay
imports Main
begin

(* Task 9 : Define a function that calculates the delay of a circuit. We shall say that the delay of circuit is the length of the longest path from the circuit’s output to one of its inputs. Prove that opt_NOT and opt_DM never increase the delay of a circuit *)
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

fun delay :: "circuit ⇒ nat" where
  "delay (NOT c) = 1 + delay c"
| "delay (AND c1 c2) = max (1 + delay c1) (1 + delay c2)"
| "delay (OR c1 c2) = max (1 + delay c1) (1 + delay c2)"
| "delay _ = 0"

theorem opt_NOT_never_increase_delay : "delay c ≥ delay (opt_NOT c)"
  apply (induct c rule: opt_NOT.induct)
  (* by auto *)
  apply simp_all
  using le_max_iff_disj apply blast
  using le_max_iff_disj by blast

theorem opt_DM_never_increase_delay : "delay c ≥ delay (opt_DM c)"
  apply (induct c rule: opt_DM.induct)
  by auto

