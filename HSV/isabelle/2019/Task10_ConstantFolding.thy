theory Task10_ConstantFolding
  imports Main
begin

(* Task 10 : Define a function that performs constant folding. Wherever it seesDefine a function that performs constant folding. Wherever it sees a gate with TRUE or FALSE as one of its inputs, it should try to replace the gate with TRUE, FALSE, or the other input, depending on the gate. *)

(* Prove that constant folding is sound *)
(* it never increases the area or delay of a circuit *)
(* prove that if constant folding is applied to a circuit that has no inputs, the circuit thus obtained must be TRUE or FALSE *)

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

fun area :: "circuit ⇒ nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

fun delay :: "circuit ⇒ nat" where
  "delay (NOT c) = 1 + delay c"
| "delay (AND c1 c2) = max (1 + delay c1) (1 + delay c2)"
| "delay (OR c1 c2) = max (1 + delay c1) (1 + delay c2)"
| "delay _ = 0"


fun opt_CF :: "circuit ⇒ circuit" where
  "opt_CF TRUE = TRUE"
| "opt_CF FALSE = FALSE"
| "opt_CF (INPUT i) = INPUT i"
| "opt_CF (NOT c) = (case opt_CF c of TRUE ⇒ FALSE | FALSE ⇒ TRUE | c' ⇒ NOT c')"
| "opt_CF (AND c1 c2) = (let c1' = opt_CF c1; c2' = opt_CF c2 in
      (case (c1', c2') of
         (FALSE, _) ⇒ FALSE
       | (_, FALSE) ⇒ FALSE
       | (TRUE, x) ⇒ x
       | (x, TRUE) ⇒ x
       | (x, y) ⇒ AND x y))"
| "opt_CF (OR c1 c2) = (let c1' = opt_CF c1; c2' = opt_CF c2 in
      (case (c1', c2') of
         (TRUE, _) ⇒ TRUE
       | (_, TRUE) ⇒ TRUE
       | (FALSE, x) ⇒ x
       | (x, FALSE) ⇒ x
       | (x, y) ⇒ OR x y))"

theorem opt_CF_is_sound : "simulate c ρ = simulate (opt_CF c) ρ"
  by (induct c) (auto simp: simulate.simps opt_CF.simps split: prod.splits)


(* 证明 opt_CF_never_increase_area *)


theorem opt_CF_never_increase_area : "area c ≥ area (opt_CF c)"
  by (induct c) (auto simp: area.simps opt_CF.simps split: prod.splits)

(* 证明 opt_CF_never_increase_delay *)

theorem opt_CF_never_increase_delay : "delay c ≥ delay (opt_CF c)"
  by (induct c) (auto simp: delay.simps opt_CF.simps split: prod.splits)

(* 证明 opt_CF_without_input_leads2_consistant *)
fun has_inputs :: "circuit ⇒ bool" where
    "has_inputs (NOT c) = has_inputs c"
| "has_inputs (AND c1 c2) = ((has_inputs c1) ∨ (has_inputs c2))"
| "has_inputs (OR c1 c2) = ((has_inputs c1) ∨ (has_inputs c2))"
| "has_inputs TRUE = False"
| "has_inputs FALSE = False"
| "has_inputs (INPUT i) = True"

fun is_constant :: "circuit ⇒ bool" where
  "is_constant c = (c = TRUE ∨ c = FALSE)"

theorem opt_CF_without_input_leads2_consistant : "¬ (has_inputs c) ⟹ is_constant (opt_CF c)"
  by (induct c) (auto simp: has_inputs.simps is_constant.simps opt_CF.simps split: prod.splits)