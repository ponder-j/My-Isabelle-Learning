theory InductionTest0
  imports Main
begin

theorem ‹sum (λx. (2::nat)^x) {x. x<n} = 2^n-1›
(* induct term [arbitrary: variables] [rule: rule] *)
(* 对项 term 使用归纳法。使用归纳规则前，先用全称量词约束每个标记为 arbitrary 的变量。若给出了 rule 选项，则将 rule 作为归纳规则。 *)
apply (induct n)
(* 1. (∑x | x < 0. 2 ^ x) = 2 ^ 0 - 1
   2. ⋀n. (∑x | x < n. 2 ^ x) = 2 ^ n - 1 ⟹ (∑x | x < Suc n. 2 ^ x) = 2 ^ Suc n - 1 *)
apply simp
(* 1. ⋀n. (∑x | x < n. 2 ^ x) = 2 ^ n - 1 ⟹ (∑x | x < Suc n. 2 ^ x) = 2 ^ Suc n - 1 *)
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n}›)
(* apply methods done ≈ by methods *)
by auto

(* cases 方法
语法 cases term [rule: rule]
作用 使用规则 rule（若未给出则自动选择），对项 term 进行分情况讨论。 *)

 (* 这个证明要证明 ∑{x | x < n} 2^x = 2^n - 1。在归纳步骤中，需要从：

  - 归纳假设：∑{x | x < n} 2^x = 2^n - 1
  - 证明目标：∑{x | x < Suc n} 2^x = 2^(Suc n) - 1

  关键在于集合 {x. x < Suc n} 与 {x. x < n} 的关系。

  为什么需要显式提示

  subgoal_tac 显式地告诉 Isabelle：{x. x < Suc n} = insert n {x. x < n}

  这个等式非常关键，因为：

  1. Sum 分解：有了这个等式，可以使用求和性质sum f (insert n A) = f n + sum f A
  2. 自动化局限：虽然 Isabelle 的 auto
  知道这个集合等式和求和性质，但它不会自动想到需要用这个特定的集合转换作为中间步骤
  3. 引导证明方向：subgoal_tac 相当于给 auto 指明了一条路径：
    - 先用这个等式重写集合
    - 再应用 sum 的分解性质
    - 最后用归纳假设和算术 *)

(* 递归定义，将一个列表反转后接入另一个列表前面 *)
primrec rev_append :: ‹'a list ⇒ 'a list ⇒ 'a list› where
  ‹rev_append [] l2 = l2› | 
  ‹rev_append (x#l1) l2 = rev_append l1 (x#l2)›

(* 验证定义的正确性 *)
theorem rev_append_correct: ‹rev_append l1 l2 = rev l1 @ l2›
(* list.induct：?P [] ⟹ (∧x1 x2. ?P x2 ⟹ ?P (x1#x2)) ⟹ ?P ?list *)
(* 对于任意命题 P，若 P([]) 成立，且对任意 x 与 list， 由 P(list) 能推出 P(x#list)，则 P(list) 对任意 list 成立 *)
apply (induct l1 arbitrary: l2)
(* 不加 arbitrary: l2 无法通过 auto 证明 *)
(* 1. rev_append [] l2 = rev [] @ l2
   2. ⋀a l1. rev_append l1 l2 = rev l1 @ l2 ⟹ rev_append (a # l1) l2 = rev (a # l1) @ l2 *)
apply simp
(* 1. ⋀a l1. rev_append l1 l2 = rev l1 @ l2 ⟹ rev_append (a # l1) l2 = rev (a # l1) @ l2 *)
by auto

(* 归纳类型上的证明 *)
(* Leaf 表示空树，不包含任何元素！不只是个叶子节点噢 *)
datatype 'a tree = Leaf | Branch ‹'a tree› 'a ‹'a tree›
(* 中序遍历 *)
primrec inorder :: ‹'a tree ⇒ 'a list› where
  ‹inorder Leaf = []› | 
  ‹inorder (Branch left x right) = inorder left @ (x # inorder right) ›
primrec mirror :: ‹'a tree ⇒ 'a tree› where
  ‹mirror Leaf = Leaf› | 
  ‹mirror (Branch left x right) = Branch (mirror right) x (mirror left)›

(* 下面利用中序遍历证明 mirror 函数的正确性 *)
theorem mirror_correct: ‹rev (inorder t) = inorder (mirror t)›
(* apply (induct t)
apply simp
by auto *)
(* 复合证明方法 *)
by (induct t; simp)

(* 归纳谓词 *)
inductive even_ind :: ‹nat ⇒ bool› where
  even_0: ‹even_ind 0› | 
  even_SS: ‹even_ind n ⟹ even_ind (Suc (Suc n))›

thm even_0 even_SS
thm even_ind.induct

end