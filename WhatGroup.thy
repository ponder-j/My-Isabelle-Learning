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
  fixes neutral :: 'a ("𝟭")
  assumes neutl : "𝟭 ⊗ x = x"

(* 声明左幺半群是半群的子类 *)
subclass (in monoidl) semigroup
  by standard (rule assoc)

(* instantiation nat and int :: monoidl
begin
  definition neutral_nat_def : "𝟭 = (0::nat)"
  definition neutral_int_def : "𝟭 = (0::int)"

  instance proof
    fix x :: nat
    show "𝟭 ⊗ x = x"
      by (simp add: neutral_nat_def multi_int_def)
end *)


end