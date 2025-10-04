theory PeirceRule
imports Main
begin

theorem peirce: ‹((P ⟶ Q) ⟶ P) ⟶ P›
(* (P ⟶ Q) ⟷ (¬ P) ∨ Q *)
apply (subst imp_conv_disj)
