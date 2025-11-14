theory InductionExercises
  imports Main
begin

(* 归纳法练习题集 *)
(* 根据 InductionTest0.thy 中的示例，以下是一些练习题 *)

(* ========== 练习 1: 基本等比级数求和 ========== *)
(* 题目：证明前 n 项几何级数求和公式 *)
theorem exercise1: ‹sum (λx. (3::nat)^x) {x. x<n} = (3^n - 1) div 2›
(* 提示：类似于原例题，使用对 n 的归纳法 *)
(* 提示：需要使用 subgoal_tac 来处理集合 {x. x < Suc n} 的分解 *)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n}›)
by auto

(* ========== 练习 2: 自然数求和 ========== *)
(* 题目：证明前 n 个自然数的和 *)
theorem exercise2: ‹sum (λx. x) {x. x<(n::nat)} = (n * (n - 1)) div 2›
(* 解法：使用数学归纳法 *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n}›)
by auto

(* ========== 练习 3: 平方和公式 ========== *)
(* 题目：证明前 n 个自然数的平方和 *)
theorem exercise3: ‹sum (λx. x^2) {x. x<(n::nat)} = (n * (n - 1) * (2*n - 1)) div 6›
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto


(* ========== 练习 4: 交替级数 ========== *)
(* 题目：证明交替求和公式 *)
theorem exercise4: ‹sum (λx. (-1::int)^x) {x. x<n} = (if even n then 0 else 1)›
(* 提示：需要分情况讨论 n 是奇数还是偶数 *)
(* 提示：可能需要使用 case_split 或者在归纳中分别处理 *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto

(* ========== 练习 5: 修改原题 ========== *)
(* 题目：将原题中的 2^x 改为 4^x *)
theorem exercise5: ‹sum (λx. (4::nat)^x) {x. x<n} = (4^n - 1) div 3›
(* 提示：方法与原题完全相同，只是底数不同 *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto

(* ========== 练习 6: 带系数的等比级数 ========== *)
(* 题目：每项都乘以 2 的等比级数 *)
theorem exercise6: ‹sum (λx. 2 * (3::nat)^x) {x. x<n} = 3^n - 1›
(* 提示：可以先提取常数因子 2，然后使用练习1的结果 *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto

(* ========== 练习 7: 集合大小的归纳 ========== *)
(* 题目：证明有限集合 {x. x < n} 的大小 *)
theorem exercise7: ‹card {x::nat. x < n} = n›
(* 提示：使用对 n 的归纳，关键是处理 Suc n 的情况 *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto

(* ========== 练习 8: 更复杂的集合关系 ========== *)
(* 题目：证明两个集合的并集关系 *)
theorem exercise8: ‹{x::nat. x < Suc n} = {x. x < n} ∪ {n}›
(* 提示：这是一个集合等式的证明，不需要归纳法 *)
(* 提示：使用 auto 或者 set equality 的方法 *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto

(* ========== 练习 9: 归纳法的变体 ========== *)
(* 题目：使用强归纳法证明 *)
theorem exercise9: 
  assumes ‹n ≥ 1›
  shows ‹sum (λx. x * (2::nat)^x) {x. x<n} = (n-2) * 2^n + 2›
(* 提示：这需要更仔细的计算，可能需要多个 subgoal_tac *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto

(* ========== 练习 10: 综合练习 ========== *)
(* 题目：证明一个更一般的公式 *)
theorem exercise10:
  fixes r :: nat
  assumes ‹r ≠ 1›
  shows ‹sum (λx. r^x) {x. x<n} = (r^n - 1) div (r - 1)›
(* 提示：这是最一般的等比级数求和公式 *)
(* 提示：需要小心处理除法和 r ≠ 1 的条件 *)
apply (induct n)
apply simp
apply (subgoal_tac ‹{x. x < Suc n} = insert n {x. x < n} ›)
by auto

(* ========== 附加提示 ========== *)
(*
证明策略提示：
1. 大多数题目都使用 (induct n) 开始
2. 基础情况通常用 simp 解决
3. 归纳步骤的关键是使用 subgoal_tac 来分解集合
4. 集合分解的常用形式：{x. x < Suc n} = insert n {x. x < n}
5. 然后使用 auto 来完成剩余的算术证明

常用策略序列：
apply (induct n)
apply simp
apply (subgoal_tac "集合等式")
by auto

如果遇到困难，可以：
1. 使用 sledgehammer 寻找相关引理
2. 分步骤证明，不要试图一次完成
3. 查看 Isabelle/HOL 的标准库中关于 sum、power、set 的引理
*)

end