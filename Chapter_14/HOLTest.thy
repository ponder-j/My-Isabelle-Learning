theory HOLTest
  imports Main
begin

(* 原始推理规则演示 *)
(* 这些规则构成了 Isabelle/HOL 的逻辑基础 *)

(* ================================================================= *)
(* 1. refl - Reflexivity (反射性) *)
(* ================================================================= *)
(* refl: 任何对象都等于自身 *)
(* 全称：reflexivity of equality *)
lemma refl_example: "x = x"
  by (rule refl)

(* ================================================================= *)
(* 2. subst - Substitution (替换) *)
(* ================================================================= *)
(* subst: 如果两个对象相等，那么在任何谓词中可以互相替换 *)
(* 全称：substitution of equals *)
lemma subst_example: "⟦x = y; P x⟧ ⟹ P y"
  by (erule subst)

(* ================================================================= *)
(* 3. ext - Extensionality (外延性) *)
(* ================================================================= *)
(* ext: 如果两个函数对所有参数都相等，那么这两个函数相等 *)
(* 全称：extensionality of functions *)
lemma ext_example: "(⋀x. f x = g x) ⟹ f = g"
  by (rule ext)

(* ================================================================= *)
(* 4. impI - Implication Introduction (蕴含引入) *)
(* ================================================================= *)
(* impI: 如果从前提P可以推出结论Q，那么P蕴含Q *)
(* 全称：implication introduction *)
lemma impI_example: "(P ⟹ Q) ⟹ P ⟶ Q"
  by (rule impI)

(* ================================================================= *)
(* 5. mp - Modus Ponens (分离规则) *)
(* ================================================================= *)
(* mp: 如果P蕴含Q且P成立，那么Q成立 *)
(* 全称：modus ponens *)
lemma mp_example: "⟦P ⟶ Q; P⟧ ⟹ Q"
  by (rule mp)

(* ================================================================= *)
(* 6. iff - If and Only If (当且仅当) *)
(* ================================================================= *)
(* iff: P当且仅当Q意味着P和Q同时成立或同时不成立 *)
(* 全称：if and only if *)
(* iffI: 当且仅当引入规则 *)
lemma iffI_example: "⟦P ⟶ Q; Q ⟶ P⟧ ⟹ P ⟷ Q"
  by blast

(* iffD1: 当且仅当消除规则1 *)
lemma iffD1_example: "⟦P ⟷ Q; P⟧ ⟹ Q"
  by blast

(* iffD2: 当且仅当消除规则2 *)
lemma iffD2_example: "⟦P ⟷ Q; Q⟧ ⟹ P"
  by blast

(* ================================================================= *)
(* 7. True_or_False - Law of Excluded Middle (排中律) *)
(* ================================================================= *)
(* True_or_False: 任何命题要么为真，要么为假 *)
(* 全称：law of excluded middle *)
lemma True_or_False_example: "P = True ∨ P = False"
  by (rule True_or_False)


(* ================================================================= *)
(* 等式规则演示 *)
(* ================================================================= *)

(* sym - Symmetry (对称性) *)
(* sym: 如果s等于t，那么t也等于s *)
(* 全称：symmetry of equality *)
lemma sym_example: "s = t ⟹ t = s"
  by (rule sym)

(* not_sym - Not Symmetry (不等式对称性) *)
(* not_sym: 如果t不等于s，那么s也不等于t *)
(* 全称：symmetry of inequality *)
lemma not_sym_example: "t ≠ s ⟹ s ≠ t"
  by (rule not_sym)

(* trans - Transitivity (传递性) *)
(* trans: 如果r等于s且s等于t，那么r等于t *)
(* 全称：transitivity of equality *)
lemma trans_example: "⟦r = s; s = t⟧ ⟹ r = t"
  by (rule trans)

(* box_equals - Box Equals (方框等式) *)
(* box_equals: 如果a=b且a=c且b=d，那么c=d *)
(* 全称：box equality (diamond property) *)
lemma box_equals_example: "⟦a = b; a = c; b = d⟧ ⟹ c = d"
  by (rule box_equals)

(* arg_cong - Argument Congruence (参数一致性) *)
(* arg_cong: 如果x等于y，那么f(x)等于f(y) *)
(* 全称：argument congruence *)
lemma arg_cong_example: "x = y ⟹ f x = f y"
  by (rule arg_cong)

(* fun_cong - Function Congruence (函数一致性) *)
(* fun_cong: 如果函数f等于g，那么f(x)等于g(x) *)
(* 全称：function congruence *)
lemma fun_cong_example: "f = g ⟹ f x = g x"
  by (rule fun_cong)

(* cong - Congruence (一致性) *)
(* cong: 如果f等于g且x等于y，那么f(x)等于g(y) *)
(* 全称：congruence *)
lemma cong_example: "⟦f = g; x = y⟧ ⟹ f x = g y"
  by (rule cong)

(* ================================================================= *)
(* 命题逻辑规则演示 *)
(* ================================================================= *)

(* TrueI - True Introduction (真引入) *)
(* TrueI: 真命题总是成立 *)
(* 全称：true introduction *)
lemma TrueI_example: "True"
  by (rule TrueI)

(* FalseE - False Elimination (假消除) *)
(* FalseE: 从假命题可以推出任何命题 *)
(* 全称：false elimination (ex falso quodlibet) *)
lemma FalseE_example: "False ⟹ P"
  by (rule FalseE)

(* conjI - Conjunction Introduction (合取引入) *)
(* conjI: 如果P和Q都成立，那么P∧Q成立 *)
(* 全称：conjunction introduction *)
lemma conjI_example2: "⟦P; Q⟧ ⟹ P ∧ Q"
  by (rule conjI)

(* conjunct1 - Conjunction Elimination 1 (合取消除1) *)
(* conjunct1: 从P∧Q可以推出P *)
(* 全称：conjunction elimination 1 *)
lemma conjunct1_example2: "P ∧ Q ⟹ P"
  by (rule conjunct1)

(* conjunct2 - Conjunction Elimination 2 (合取消除2) *)
(* conjunct2: 从P∧Q可以推出Q *)
(* 全称：conjunction elimination 2 *)
lemma conjunct2_example: "P ∧ Q ⟹ Q"
  by (rule conjunct2)

(* conjE - Conjunction Elimination (合取消除) *)
(* conjE: 从P∧Q和P、Q推出R的规则，可以推出R *)
(* 全称：conjunction elimination *)
lemma conjE_example: "⟦P ∧ Q; ⟦P; Q⟧ ⟹ R⟧ ⟹ R"
  by (rule conjE)

(* disjI1 - Disjunction Introduction 1 (析取引入1) *)
(* disjI1: 如果P成立，那么P∨Q成立 *)
(* 全称：disjunction introduction 1 *)
lemma disjI1_example2: "P ⟹ P ∨ Q"
  by (rule disjI1)

(* disjI2 - Disjunction Introduction 2 (析取引入2) *)
(* disjI2: 如果Q成立，那么P∨Q成立 *)
(* 全称：disjunction introduction 2 *)
lemma disjI2_example: "Q ⟹ P ∨ Q"
  by (rule disjI2)

(* disjE - Disjunction Elimination (析取消除) *)
(* disjE: 如果P∨Q成立，且P推出R，Q也推出R，那么R成立 *)
(* 全称：disjunction elimination *)
lemma disjE_example: "⟦P ∨ Q; P ⟹ R; Q ⟹ R⟧ ⟹ R"
  by (rule disjE)

(* notI - Negation Introduction (否定引入) *)
(* notI: 如果P推出False，那么¬P成立 *)
(* 全称：negation introduction *)
lemma notI_example: "(P ⟹ False) ⟹ ¬ P"
  by (rule notI)

(* notE - Negation Elimination (否定消除) *)
(* notE: 如果¬P且P成立，那么可以推出任何R *)
(* 全称：negation elimination *)
lemma notE_example: "⟦¬ P; P⟧ ⟹ R"
  by (rule notE)

(* impE - Implication Elimination (蕴含消除) *)
(* impE: 如果P⟶Q且P成立，且Q推出R，那么R成立 *)
(* 全称：implication elimination *)
lemma impE_example: "⟦P ⟶ Q; P; Q ⟹ R⟧ ⟹ R"
  by (rule impE)

(* ================================================================= *)
(* 逻辑等价性规则演示 *)
(* ================================================================= *)

(* iffI - If and Only If Introduction (当且仅当引入) *)
(* iffI: 如果P推出Q且Q推出P，那么P等价于Q *)
(* 全称：if and only if introduction *)
lemma iffI_example2: "⟦P ⟹ Q; Q ⟹ P⟧ ⟹ P = Q"
  by (rule iffI)

(* iffD1 - If and Only If Elimination 1 (当且仅当消除1) *)
(* iffD1: 如果Q等价于P且Q成立，那么P成立 *)
(* 全称：if and only if elimination 1 *)
lemma iffD1_example2: "Q = P ⟹ Q ⟹ P"
  by (erule iffD1)

(* rev_iffD1 - Reverse If and Only If Elimination 1 (反向当且仅当消除1) *)
(* rev_iffD1: 如果Q成立且Q等价于P，那么P成立 *)
(* 全称：reverse if and only if elimination 1 *)
lemma rev_iffD1_example: "Q ⟹ Q = P ⟹ P"
  by (erule rev_iffD1)

(* iffD2 - If and Only If Elimination 2 (当且仅当消除2) *)
(* iffD2: 如果P等价于Q且Q成立，那么P成立 *)
(* 全称：if and only if elimination 2 *)
lemma iffD2_example2: "⟦P = Q; Q⟧ ⟹ P"
  by (erule iffD2)

(* rev_iffD2 - Reverse If and Only If Elimination 2 (反向当且仅当消除2) *)
(* rev_iffD2: 如果Q成立且P等价于Q，那么P成立 *)
(* 全称：reverse if and only if elimination 2 *)
lemma rev_iffD2_example: "⟦Q; P = Q⟧ ⟹ P"
  by (erule rev_iffD2)

(* iffE - If and Only If Elimination (当且仅当消除) *)
(* iffE: 如果P等价于Q，且从P⟶Q和Q⟶P可以推出R，那么R成立 *)
(* 全称：if and only if elimination *)
lemma iffE_example: "⟦P = Q; ⟦P ⟶ Q; Q ⟶ P⟧ ⟹ R⟧ ⟹ R"
  by (rule iffE)

(* ================================================================= *)
(* 量词规则演示 *)
(* ================================================================= *)

(* allI - Universal Quantification Introduction (全称量词引入) *)
(* allI: 如果对所有x都有P(x)成立，那么∀x. P(x)成立 *)
(* 全称：universal quantification introduction *)
lemma allI_example2: "(⋀x::'a. P x) ⟹ ∀x. P x"
  by (rule allI)

(* spec - Universal Quantification Elimination (全称量词消除) *)
(* spec: 如果∀x. P(x)成立，那么对特定x也有P(x)成立 *)
(* 全称：universal quantification elimination (specialization) *)
lemma spec_example2: "∀x::'a. P x ⟹ P x"
  by (rule spec)

(* allE - Universal Quantification Elimination (全称量词消除) *)
(* allE: 如果∀x. P(x)成立，且P(x)推出R，那么R成立 *)
(* 全称：universal quantification elimination *)
lemma allE_example: "⟦∀x. P x; P x ⟹ R⟧ ⟹ R"
  by (rule allE)

(* all_dupE - Universal Quantification Duplicate Elimination (全称量词重复消除) *)
(* all_dupE: 如果∀x. P(x)成立，且P(x)和∀x. P(x)一起推出R，那么R成立 *)
(* 全称：universal quantification duplicate elimination *)
lemma all_dupE_example: "⟦∀x. P x; ⟦P x; ∀x. P x⟧ ⟹ R⟧ ⟹ R"
  by (rule all_dupE)

(* exI - Existential Quantification Introduction (存在量词引入) *)
(* exI: 如果存在某个x使得P(x)成立，那么∃x. P(x)成立 *)
(* 全称：existential quantification introduction *)
lemma exI_example2: "P x ⟹ ∃x::'a. P x"
  by (rule exI)

(* exE - Existential Quantification Elimination (存在量词消除) *)
(* exE: 如果∃x. P(x)成立，且对任意x，P(x)都推出Q，那么Q成立 *)
(* 全称：existential quantification elimination *)
lemma exE_example: "⟦∃x::'a. P x; ⋀x. P x ⟹ Q⟧ ⟹ Q"
  by (rule exE)

(* ex1I - Unique Existential Quantification Introduction (唯一存在量词引入) *)
(* ex1I: 如果P(a)成立且对所有x，P(x)推出x=a，那么∃!x. P(x)成立 *)
(* 全称：unique existential quantification introduction *)
lemma ex1I_example: "⟦P a; ⋀x. P x ⟹ x = a⟧ ⟹ ∃!x. P x"
  by (rule ex1I)

(* ex1E - Unique Existential Quantification Elimination (唯一存在量词消除) *)
(* ex1E: 如果∃!x. P(x)成立，且对任意x，如果P(x)且对所有y，P(y)推出y=x，那么R成立 *)
(* 全称：unique existential quantification elimination *)
lemma ex1E_example: "⟦∃!x. P x; ⋀x. ⟦P x; ∀y. P y ⟶ y = x⟧ ⟹ R⟧ ⟹ R"
  by (rule ex1E)

(* ================================================================= *)
(* 经典逻辑规则演示 *)
(* ================================================================= *)

(* ccontr - Classical Contradiction (经典矛盾) *)
(* ccontr: 如果¬P推出False，那么P成立 *)
(* 全称：classical contradiction *)
lemma ccontr_example: "(¬ P ⟹ False) ⟹ P"
  by (rule ccontr)

(* classical - Classical Logic (经典逻辑) *)
(* classical: 如果¬P推出P，那么P成立 *)
(* 全称：classical logic principle *)
lemma classical_example: "(¬ P ⟹ P) ⟹ P"
  by (rule classical)

(* excluded_middle - Law of Excluded Middle (排中律) *)
(* excluded_middle: 任何命题要么成立要么不成立 *)
(* 全称：law of excluded middle *)
lemma excluded_middle_example: "¬ P ∨ P"
  by (rule excluded_middle)

(* disjCI - Disjunction Classical Introduction (经典析取引入) *)
(* disjCI: 如果¬Q推出P，那么P∨Q成立 *)
(* 全称：disjunction classical introduction *)
lemma disjCI_example: "(¬ Q ⟹ P) ⟹ P ∨ Q"
  by (rule disjCI)

(* impCE - Implication Classical Elimination (经典蕴含消除) *)
(* impCE: 如果P⟶Q成立，且¬P推出R，Q也推出R，那么R成立 *)
(* 全称：implication classical elimination *)
lemma impCE_example: "⟦P ⟶ Q; ¬ P ⟹ R; Q ⟹ R⟧ ⟹ R"
  by (rule impCE)

(* exCI - Existential Classical Introduction (经典存在量词引入) *)
(* exCI: 如果对所有x，¬P(x)推出P(a)，那么∃x. P(x)成立 *)
(* 全称：existential classical introduction *)
lemma exCI_example: "(∀x. ¬ P x ⟹ P a) ⟹ ∃x. P x"
  by (rule exCI)

(* iffCE - If and Only If Classical Elimination (经典当且仅当消除) *)
(* iffCE: 如果P等价于Q，且P和Q一起推出R，或¬P和¬Q一起推出R，那么R成立 *)
(* 全称：if and only if classical elimination *)
lemma iffCE_example: "⟦P = Q; ⟦P; Q⟧ ⟹ R; ⟦¬ P; ¬ Q⟧ ⟹ R⟧ ⟹ R"
  by (rule iffCE)

(* notnotD - Double Negation Elimination (双重否定消除) *)
(* notnotD: ¬¬P推出P *)
(* 全称：double negation elimination *)
lemma notnotD_example: "¬ ¬ P ⟹ P"
  by (rule notnotD)

(* swap - Swap (交换) *)
(* swap: 如果¬P成立，且¬R推出P，那么R成立 *)
(* 全称：swap rule *)
lemma swap_example: "¬ P ⟹ (¬ R ⟹ P) ⟹ R"
  by (rule swap)

(* imp_elim - Implication Elimination (蕴含消除) *)
(* imp_elim: 如果P⟶Q成立，且¬R推出P，且Q推出R，那么R成立 *)
(* 全称：implication elimination *)
lemma imp_elim_example: "P ⟶ Q ⟹ (¬ R ⟹ P) ⟹ (Q ⟹ R) ⟹ R"
  by (rule imp_elim)

(* ================================================================= *)
(* 条件规则演示 *)
(* ================================================================= *)

(* if_P - If True (如果为真) *)
(* if_P: 如果P成立，那么条件表达式(if P then x else y)等于x *)
(* 全称：if true branch *)
lemma if_P_example: "P ⟹ (if P then x else y) = x"
  by (rule if_P)

(* if_not_P - If False (如果为假) *)
(* if_not_P: 如果P不成立，那么条件表达式(if P then x else y)等于y *)
(* 全称：if false branch *)
lemma if_not_P_example: "¬ P ⟹ (if P then x else y) = y"
  by (rule if_not_P)

(* if_bool_eq_conj - If Boolean Equality Conjunction (条件布尔等价合取) *)
(* if_bool_eq_conj: 条件表达式等于(P⟶Q)∧(¬P⟶R) *)
(* 全称：if boolean equality conjunction *)
lemma if_bool_eq_conj_example: "(if P then Q else R) = ((P ⟶ Q) ∧ (¬ P ⟶ R))"
  by (rule if_bool_eq_conj)

(* if_split - If Split (条件分裂) *)
(* if_split: P(if Q then x else y)等价于(Q⟶P x)∧(¬Q⟶P y) *)
(* 全称：if split *)
lemma if_split_example: "P (if Q then x else y) = ((Q ⟶ P x) ∧ (¬ Q ⟶ P y))"
  by (rule if_split)

(* ================================================================= *)
(* 等式符号区别演示 *)
(* ================================================================= *)

(* 在 Isabelle/HOL 中，主要的等式和等价符号有： *)

(* 1. P = Q - 通用等式 *)
(* 对于布尔值，表示逻辑等价 *)
lemma equality_example: "(P = Q) = ((P ⟶ Q) ∧ (Q ⟶ P))"
  by blast

(* 2. P ⟷ Q - 逻辑等价 (if and only if) *)
(* 这是 ⟷ 符号，与 P = Q 在布尔类型上等价 *)
lemma iff_symbol_example: "P ⟷ Q ⟷ (P ⟶ Q) ∧ (Q ⟶ P)"
  by blast

(* 3. P ↔ Q 和 P ⇔ Q *)
(* 这些符号在 Isabelle 中通常不被识别为逻辑等价 *)
(* 它们可能需要特殊的导入或在其他上下文中使用 *)

end