theory PeirceLaw2
imports Main
begin

theorem peirce: ‹((P ⟶ Q) ⟶ P) ⟶ P›
apply (rule impI)
(* 1. (P ⟶ Q) ⟶ P ⟹ P *)

(* 将从某个已知事实提取信息的定理称为析构规则 *)
(* drule 和 frule 两种方法，下面的例子中使用 drule，如果换成 frule 则会保留 (P ⟶ Q) ⟶ P 这一项前提变成 *)
(* (P ⟶ Q) ⟶ P ⟹ ¬ (P ⟶ Q) ∨ P ⟹ P *)

(* Meson.imp_to_disjD 规则：P ⟶ Q ⟹ ¬ P ∨ Q *)
apply (drule Meson.imp_to_disjD)
(* 1. ¬ (P ⟶ Q) ∨ P ⟹ P *)
apply (erule disjE)
(* 1. ¬ (P ⟶ Q) ⟹ P
   2. P ⟹ P *)

(* ¬ (P ⟶ Q) ⟹ P ∧ ¬ Q *)
apply (drule Meson.not_impD)
apply (erule conjE)
apply assumption
apply assumption
done


end