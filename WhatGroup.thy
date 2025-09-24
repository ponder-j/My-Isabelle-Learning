theory WhatGroup
    imports Main
begin

(* 半群只需满足结合律 *)
class semigroup =
  fixes op :: "'a ⇒ 'a ⇒ 'a" (infixl "⊗" 70)
  assumes assoc: "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"

(* 整数在加法下构成半群 *)
instantiation int :: semigroup
begin
  definition multi_int_def : "i ⊗ j = i + (j :: int)"
  instance proof
    fix x y z :: int
    show "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
      by (simp add: multi_int_def)
  qed
end

(* 幺半群需要有单位元 *)
class monoidl = semigroup +
  fixes neutral :: 'a ("")

end