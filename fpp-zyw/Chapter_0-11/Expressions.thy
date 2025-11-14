theory Expressions
  imports Complex_Main
begin

consts cst1 :: int
specification(cst1) "cst1 = 1" by simp
thm cst1_def

consts cst2 :: int
specification(cst2) "cst2 > 1" using gt_ex by auto
thm cst2_def

definition "cst3 = (3::int)"
thm cst3_def

term "\<lambda>x. True"
value "(\<lambda>x. True) 2"
value "(\<lambda>x. True) ''abc''"
value "(\<lambda>x. True) 2.0"

term "\<lambda>x. Suc x"
value "(\<lambda>x. Suc x) 5"

term "\<lambda>x y. x * y"
value "(\<lambda>x y. x * y)(5::int)(6::int)"
value "(\<lambda>x y. x * y)(5.0::real)(6::int)"
value "(\<lambda>x y. x * y)(5.0::real)(6.5::real)"

term "(\<lambda>f x. f x)"
value "(\<lambda>f x. f x) Suc 1"

term "(\<lambda>f g x y. f (g x y))"
value "(\<lambda>f g x y. f (g x y)) Suc plus 10 20"

definition f :: "nat \<Rightarrow> nat"
  where "f x \<equiv> 2 * x + 1"
definition f1 :: "nat \<Rightarrow> nat"
  where "f1 \<equiv> \<lambda>x. 2 * x + 1"

term "if b then e1 else e2"
definition if1 :: "bool \<Rightarrow> string"
  where "if1 b \<equiv> if b then ''it's true'' else ''it's false''"

value "if1 False"

term "let x = i; y = i + 1 in (x + y) * 2"
definition let1 :: "nat \<Rightarrow> nat"
  where "let1 i = (let x = i; y = i + 1 in (x + y) * 2)"
value "let1 3"

definition let2 :: "nat \<Rightarrow> nat"
  where "let2 i = (let x = i; y = i + 1 in (\<lambda>x. (Suc x) + y) x + (\<lambda>y. (Suc y) + x) y)"
value "let2 3"

definition case1 :: "nat \<Rightarrow> string"
  where "case1 n \<equiv> case n of 0 \<Rightarrow> ''zero'' |
                       (Suc m) \<Rightarrow> ''not zero''"
value "case1 0"
value "case1 1"

end