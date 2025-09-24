theory MonoidTest
  imports Main
begin

class monoid =
  fixes mult :: "'a ⇒ 'a ⇒ 'a" (infixl "⊗" 70) 
  fixes neutral :: 'a ("𝟭")
  assumes assoc : "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
      and  neutr : "x ⊗ 𝟭 = x"
      and  neutl : "𝟭 ⊗ x = x"

(* instantiation int :: monoid
begin
definition mult_int_def : "x ⊗ y = (x :: int) + y"
definition neutral_int_def : "𝟭 = (0::int)"
end

instantiation bool :: monoid
begin
definition mult_bool_def : "x ⊗ y = ((x::bool) ∧ y)"
definition neutral_bool_def : "𝟭 = True"
end

instantiation list :: (type) monoid  
begin
definition mult_list_def : "(x :: 'a list) ⊗ y = x @ y"
definition neutral_list_def : "𝟭 = []"
end

instantiation set :: (type) monoid
begin
definition mult_set_def : "(x :: 'a set) ⊗ y = x ∪ y"
definition neutral_set_def : "𝟭 = {}"
end *)

end