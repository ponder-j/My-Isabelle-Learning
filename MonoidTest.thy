theory MonoidTest
  imports Main
begin

(* 定义幺半群类型类：具有结合律和单位元的代数结构 *)
class monoid =
  fixes mult :: "'a ⇒ 'a ⇒ 'a" (infixl "⊗" 70)
  fixes neutral :: 'a ("𝟭")
  assumes assoc : "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
      and  neutr : "x ⊗ 𝟭 = x"
      and  neutl : "𝟭 ⊗ x = x"

(* 自然数在加法下构成幺半群 *)
instantiation nat :: monoid
begin
definition mult_nat_def : "x ⊗ y = (x :: nat) + y"
definition neutral_nat_def : "𝟭 = (0::nat)"
instance
proof
    fix x y z :: nat
    show "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
        by (simp add: mult_nat_def assoc)
    show "x ⊗ 𝟭 = x"
        by (simp add: mult_nat_def neutral_nat_def neutl neutr)
    show "𝟭 ⊗ x = x"
        by (simp add: mult_nat_def neutral_nat_def neutl neutr)
qed
end

(* 整数在加法下构成幺半群 *)
instantiation int :: monoid
begin
definition mult_int_def : "x ⊗ y = (x :: int) + y"
definition neutral_int_def : "𝟭 = (0::int)"
instance
proof
    fix x y z :: int
    show "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
        by (simp add: mult_int_def assoc)
    show "x ⊗ 𝟭 = x"
        by (simp add: mult_int_def neutral_int_def neutl neutr)
    show "𝟭 ⊗ x = x"
        by (simp add: mult_int_def neutral_int_def neutl neutr)
qed
end

(* 布尔值在逻辑与下构成幺半群 *)
instantiation bool :: monoid
begin
definition mult_bool_def : "x ⊗ y = ((x::bool) ∧ y)"
definition neutral_bool_def : "𝟭 = True"
instance
proof
    fix x y z :: bool
    show "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
        by (simp add: mult_bool_def assoc)
    show "x ⊗ 𝟭 = x"
        by (simp add: mult_bool_def neutral_bool_def neutl neutr)
    show "𝟭 ⊗ x = x"
        by (simp add: mult_bool_def neutral_bool_def neutl neutr)
qed
end

(* 列表在连接操作下构成幺半群 *)
instantiation list :: (type) monoid  
begin
definition mult_list_def : "(x :: 'a list) ⊗ y = x @ y"
definition neutral_list_def : "𝟭 = []"
instance
proof
    fix x y z :: "'a list"
    show "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
        by (simp add: mult_list_def assoc)
    show "x ⊗ 𝟭 = x"
        by (simp add: mult_list_def neutral_list_def neutl neutr)
    show "𝟭 ⊗ x = x"
        by (simp add: mult_list_def neutral_list_def neutl neutr)
qed
end

(* 集合在并集操作下构成幺半群 *)
instantiation set :: (type) monoid
begin
definition mult_set_def : "(x :: 'a set) ⊗ y = x ∪ y"
definition neutral_set_def : "𝟭 = {}"
instance
proof
    fix x y z :: "'a set"
    show "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
        by (simp add: mult_set_def assoc)
    show "x ⊗ 𝟭 = x"
        by (simp add: mult_set_def neutral_set_def neutl neutr)
    show "𝟭 ⊗ x = x"
        by (simp add: mult_set_def neutral_set_def neutl neutr)
qed
end

(* 幺半群的一大特性是可组合性 *)
instantiation prod :: (monoid, monoid) monoid
(* 将积类型'a × 'b实例化为monoid，前提是'a和'b都已经是monoid。 *)
begin
    definition mult_prod_def : "x ⊗ y = (fst x ⊗ fst y, snd x ⊗ snd y)"
    definition neutral_prod_def : "𝟭 = (𝟭, 𝟭)"
    instance
    proof
        fix x y z :: "'a × 'b"
        show "(x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)"
            by (simp add: mult_prod_def assoc)
        show "x ⊗ 𝟭 = x"
            by (simp add: mult_prod_def neutral_prod_def neutl neutr)
        show "𝟭 ⊗ x = x"
            by (simp add: mult_prod_def neutral_prod_def neutl neutr)
    qed
end

(* 测试各种幺半群运算 *)
value "(''aaaa'',{1::int,2,3}) ⊗ (''cccc'',{4,5,6})"
value "(''aa'',{1::int},1::nat) ⊗ (''cc'',{2},2) ⊗ (''ee'',{3},3)"

(* monoid可以和列表关联使用，实现数据的⊗累加运算，也可以通过组合monoid实现多路数据的⊗累加 *)
value "foldl (⊗) 𝟭 [''aa'',''bb'',''cc'']"

end