theory meta_logic
  imports Main
begin

typedecl o

axiomatization eq :: "['a, 'a] ⇒ o" (infixl "=" 50)
where 
  refl : "a = a" and
  subst: "a = b ⟹ P(a) ⟹ P(b)"

axiomatization
  False :: o and
  conj :: "[o, o] ⇒ o" (infixr "∧" 35) and
  disj :: "[o, o] ⇒ o" (infixr "∨" 30) and
  imp :: "[o, o] ⇒ o" (infixr "⟶" 25)
where
  conjI : "⟦P; Q⟧ ⟹ P ∧ Q" and
  onjunct1 : "P ∧ Q ⟹ P" and
  onjunct2 : "P ∧ Q ⟹ Q" and
  disjI1 : "P ⟹ P ∨ Q" and
  disjI2 : "Q ⟹ P ∨ Q" and
  disjE : "⟦P ∨ Q; P ⟹ R; Q ⟹ R⟧ ⟹ R" and
  impI : "(P ⟹ Q) ⟹ P ⟶ Q" and
  mp : "⟦P ⟶ Q; P⟧ ⟹ Q" and
  FalseE : "False ⟹ P"

end