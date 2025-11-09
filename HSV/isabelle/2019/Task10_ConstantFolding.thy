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

(* 错误示范1: 递归逻辑有误，无法实现化简后再化简，NOT (NOT TRUE) 只消去了一层 *)
(* fun opt_CF_incorrect :: "circuit ⇒ circuit" where
  "opt_CF_incorrect (NOT FALSE) = TRUE"
| "opt_CF_incorrect (NOT TRUE) = FALSE"
| "opt_CF_incorrect (NOT c) = NOT (opt_CF_incorrect c)"
| "opt_CF_incorrect (AND FALSE c) = FALSE"
| "opt_CF_incorrect (AND c FALSE) = FALSE"
| "opt_CF_incorrect (AND TRUE c) = c"
| "opt_CF_incorrect (AND c TRUE) = c"
| "opt_CF_incorrect (OR c FALSE) = c"
| "opt_CF_incorrect (OR FALSE c) = c"
| "opt_CF_incorrect (OR TRUE c) = TRUE"
| "opt_CF_incorrect (OR c TRUE) = TRUE"
| "opt_CF_incorrect (AND c1 c2) = AND (opt_CF_incorrect c1) (opt_CF_incorrect c2)"
| "opt_CF_incorrect (OR c1 c2) = OR (opt_CF_incorrect c1) (opt_CF_incorrect c2)"
| "opt_CF_incorrect TRUE = TRUE"
| "opt_CF_incorrect FALSE = FALSE"
| "opt_CF_incorrect (INPUT i) = INPUT i"

(* 错误示范2: 难以证明其 sound 性和两个 never_increase 性质 *)
fun opt_CF_complicated :: "circuit ⇒ circuit" where
  "opt_CF_complicated (NOT c) = (case opt_CF_complicated c of FALSE ⇒ TRUE | TRUE ⇒ FALSE | c' ⇒ NOT c')"
| "opt_CF_complicated (AND c1 c2) = (let c1' = opt_CF_complicated c1; c2' = opt_CF_complicated c2 in
    case (c1', c2') of
      (FALSE, _) ⇒ FALSE
    | (_, FALSE) ⇒ FALSE
    | (TRUE, _) ⇒ c2'
    | (_, TRUE) ⇒ c1'
    | _ ⇒ AND c1' c2')"
| "opt_CF_complicated (OR c1 c2) = (let c1' = opt_CF_complicated c1; c2' = opt_CF_complicated c2 in
    case (c1', c2') of
      (TRUE, _) ⇒ TRUE
    | (_, TRUE) ⇒ TRUE
    | (FALSE, _) ⇒ c2'
    | (_, FALSE) ⇒ c1'
    | _ ⇒ OR c1' c2')"
| "opt_CF_complicated c = c" *)

(* 参考答案的正确方法：将优化器拆成几个部件再合并，逻辑更清晰，证明也更容易 *)
fun opt_CF_NOT :: "circuit ⇒ circuit" where
  "opt_CF_NOT TRUE = FALSE"
| "opt_CF_NOT FALSE = TRUE"
| "opt_CF_NOT c = NOT c"

fun opt_CF_AND :: "circuit ⇒ circuit ⇒ circuit" where
  "opt_CF_AND TRUE c = c"
| "opt_CF_AND c TRUE = c"
| "opt_CF_AND FALSE c = FALSE"
| "opt_CF_AND c FALSE = FALSE"
| "opt_CF_AND c1 c2 = (AND c1 c2)"

fun opt_CF_OR :: "circuit ⇒ circuit ⇒ circuit" where
  "opt_CF_OR TRUE c = TRUE"
| "opt_CF_OR c TRUE = TRUE"
| "opt_CF_OR FALSE c = c"
| "opt_CF_OR c FALSE = c"
| "opt_CF_OR c1 c2 = (OR c1 c2)"

fun opt_CF :: "circuit ⇒ circuit" where
  "opt_CF (NOT c) = opt_CF_NOT(opt_CF c)"
| "opt_CF (AND c1 c2) = opt_CF_AND (opt_CF c1) (opt_CF c2)"
| "opt_CF (OR c1 c2) = opt_CF_OR (opt_CF c1) (opt_CF c2)"
| "opt_CF TRUE = TRUE"
| "opt_CF FALSE = FALSE"
| "opt_CF (INPUT i) = (INPUT i)"

(* 手动测试看看
definition c0 :: "circuit" where
  "c0 ≡ NOT(NOT (AND (OR (NOT TRUE) TRUE) TRUE))"

value "opt_CF c0" *)

(* 欲证 opt_CF is sound, 应先证前面几个辅助函数是 sound 的 *)
lemma opt_CF_NOT_is_sound : "simulate (NOT c) ρ = simulate (opt_CF_NOT c) ρ"
  apply (induct c rule: opt_CF_NOT.induct)
  apply simp_all
  done

lemma opt_CF_AND_is_sound : "simulate (AND c1 c2) ρ = simulate (opt_CF_AND c1 c2) ρ"
  apply (induct c1 c2 rule: opt_CF_AND.induct)
  apply simp_all
  done

lemma opt_CF_OR_is_sound : "simulate (OR c1 c2) ρ = simulate (opt_CF_OR c1 c2) ρ"
  apply (induct c1 c2 rule: opt_CF_OR.induct)
  apply simp_all
  done


theorem opt_CF_is_sound : "simulate c ρ = simulate (opt_CF c) ρ"
  apply (induct c rule: opt_CF.induct)
  using opt_CF_NOT_is_sound apply force
  using opt_CF_AND_is_sound apply force
  using opt_CF_OR_is_sound apply force
  apply simp_all
  done

theorem opt_CF_never_increase_area : "area c ≥ area (opt_CF c)"
  apply (induct c rule: opt_CF.induct)
  apply (smt (verit, ccfv_SIG) Suc_leI area.simps(1,4,5) le_imp_less_Suc nat_less_le opt_CF.simps(1) opt_CF_NOT.elims plus_1_eq_Suc)
  sledgehammer


theorem opt_CF_never_increase_delay : "delay c ≥ delay (opt_CF c)"
  apply (induct c rule: opt_CF.induct)
  by auto

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