theory PeirceLaw
imports Main
begin

theorem peirce: ‹((P ⟶ Q) ⟶ P) ⟶ P›
(* (P ⟶ Q) ⟷ (¬ P) ∨ Q *)
(* subst [(asm)] [(num)] equation *)
(* asm 为可选参数， 若选定则在前提代换，若不选定则在结论代换*)
(* num 为可选参数，指定代换的位置，默认为 1 *)
apply (subst  imp_conv_disj)
(* 1. (¬ P ∨ Q ⟶ P) ⟶ P *)
apply (subst  imp_conv_disj)
(* 1. ¬ (¬ P ∨ Q) ∨ P ⟶ P *)
apply (subst de_Morgan_disj)
(* 1. ¬ ¬ P ∧ ¬ Q ∨ P ⟶ P *)
apply (subst not_not)
(* 1. P ∧ ¬ Q ∨ P ⟶ P *)
apply (rule impI) (* 也可写作 apply rule 让 Isabelle 自动选择*)
(* 使用析取消除 *)
apply (erule disjE)
apply (erule conjE)
apply assumption
apply assumption
done

end