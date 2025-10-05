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

end