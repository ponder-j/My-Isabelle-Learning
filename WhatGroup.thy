theory WhatGroup
    imports Main
begin

class semigroup =
  fixes op :: "'a ⇒ 'a ⇒ 'a" (infixl "⊗" 70)
  assumes assoc: "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"

instantiation int :: smigroup
begin
  definition multi_int_def : "i "

end