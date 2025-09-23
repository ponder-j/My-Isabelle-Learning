theory ClassAdd
    imports Complex_Main
begin

class additive = 
    fixes add :: "'a ⇒ 'a ⇒ 'a" (infixl "⊕" 70)
    assumes assoc : "(x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)"

instantiation int :: additive
begin
(* ⊕运算重载的定义 *)
definition add_int_def : "x ⊕ y = (x::int) + y"
(* int类型上⊕运算重载定义符合结合律的证明 *)
instance proof
  fix x y z :: int
  show "(x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)"
    by (simp add: add_int_def)
qed
end

datatype Number = Natural nat | Integer int | Real real

instantiation Number :: additive
begin
definition addnum :: "Number ⇒ Number ⇒ Number"
  where "addnum x y ≡ Real ((case x of Real r ⇒ r 
| Natural n ⇒ of_nat n 
| Integer i ⇒ of_int i)
                              + (case y of Real r ⇒ r 
| Natural n ⇒ of_nat n 
| Integer i ⇒ of_int i))"
definition add_Number_def : "x ⊕ y = addnum x y"
instance proof
  fix x y z :: Number
  show "(x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)"
    by (simp add: add_Number_def addnum_def)
qed
end

value "(2::int) ⊕ 12"
(* 输出"14" :: "int" *)
value "True ⊕ False"
(* 输出 "True" :: "bool" *)
value "(Real 2.0) ⊕ (Integer 3)"
(* 输出"Real 5" :: "Number" *)

end