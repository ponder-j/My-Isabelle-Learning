theory meta_logic
  imports Main
begin

typedecl o

(* - axiomatization = "我有这些东西"（存在性声明）
   - where = "这些东西有这些性质"（行为规范）
  两者结合起来完整定义了一个公理系统。 *)

axiomatization
  eq :: "['a, 'a] ⇒ o" (infixl "=" 50)
where
  (* 反射性：任何对象都等于自身 *)
  refl : "a = a" and
  (* 替换性：相等的对象可以互相替换 *)
  subst: "a = b ⟹ P(a) ⟹ P(b)"

axiomatization
  (* 假命题 *)
  False :: o and
  (* 合取/与操作 *)
  conj :: "[o, o] ⇒ o" (infixr "∧" 35) and
  (* 析取/或操作 *)
  disj :: "[o, o] ⇒ o" (infixr "∨" 30) and
  (* 蕴含操作 *)
  imp :: "[o, o] ⇒ o" (infixr "⟶" 25)
where
  (* 合取引入：如果P和Q都成立，则P∧Q成立 *)
  conjI : "⟦P; Q⟧ ⟹ P ∧ Q" and
  (* 合取消除1：从P∧Q可以得出P *)
  conjunct1 : "P ∧ Q ⟹ P" and
  (* 合取消除2：从P∧Q可以得出Q *)
  conjunct2 : "P ∧ Q ⟹ Q" and
  (* 析取引入1：如果P成立，则P∨Q成立 *)
  disjI1 : "P ⟹ P ∨ Q" and
  (* 析取引入2：如果Q成立，则P∨Q成立 *)
  disjI2 : "Q ⟹ P ∨ Q" and
  (* 析取消除：若P∨Q成立，且P推出R，Q也推出R，则R成立 *)
  disjE : "⟦P ∨ Q; P ⟹ R; Q ⟹ R⟧ ⟹ R" and
  (* 蕴含引入：如果P推出Q，则P⟶Q成立 *)
  impI : "(P ⟹ Q) ⟹ P ⟶ Q" and
  (* 分离规则：若P⟶Q成立且P成立，则Q成立 *)
  mp : "⟦P ⟶ Q; P⟧ ⟹ Q" and
  (* 假消除（爆炸原理）：从假命题可以推出任何命题 *)
  FalseE : "False ⟹ P"

end