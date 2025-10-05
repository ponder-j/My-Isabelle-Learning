theory SledgehammerDemo
  imports Main
begin

(* ========================================== *)
(*    Sledgehammer 使用演示                     *)
(* ========================================== *)

(*
  什么是 Sledgehammer？
  - Sledgehammer 是 Isabelle 中最强大的自动证明工具
  - 它调用多个外部自动定理证明器（ATP）和SMT求解器
  - 可以自动查找相关的引理并生成证明

  如何使用？
  1. 在证明过程中的任何位置输入 "sledgehammer"
  2. 等待几秒钟，它会返回找到的证明方法
  3. 点击建议的证明命令来插入到你的代码中

  在 Isabelle/jEdit 中：
  - 方式1：直接输入 "sledgehammer" 作为一个 apply 命令
  - 方式2：在 Output 窗口中点击 "sledgehammer" 按钮
*)


(* ========== 示例 1: 简单的列表引理 ========== *)
(*
  问题：证明 append 的结合律
  不使用 sledgehammer 时，我们需要自己找到相关引理
*)

lemma list_append_assoc_manual:
  fixes xs ys zs :: "'a list"
  shows "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by (induct xs) auto
  (* 手动证明：需要对 xs 进行归纳 *)


(* 使用 sledgehammer 的版本 *)
lemma list_append_assoc_sledge:
  fixes xs ys zs :: "'a list"
  shows "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by simp
  (* 在这里输入 "sledgehammer"，它会建议： *)
  (* by (simp add: append_assoc) *)
  (* sledgehammer 找到了标准库中的 append_assoc 引理！ *)


(* ========== 示例 2: 算术性质 ========== *)
(*
  问题：证明一个简单的算术等式
*)

lemma arithmetic_example:
  fixes n :: nat
  shows "n + n = 2 * n"
  (* 输入 sledgehammer，它会建议： *)
  by simp
  (* 或者找到相关的算术引理 *)


(* ========== 示例 3: 列表长度性质 ========== *)
lemma length_append:
  fixes xs ys :: "'a list"
  shows "length (xs @ ys) = length xs + length ys"
  (* 使用 sledgehammer *)
  by simp
  (* sledgehammer 会找到这是 length_append 引理 *)


(* ========== 示例 4: 更复杂的证明 - 需要中间步骤 ========== *)
(*
  当证明较复杂时，sledgehammer 可以在每一步帮助我们
*)

lemma list_rev_append:
  fixes xs ys :: "'a list"
  shows "rev (xs @ ys) = rev ys @ rev xs"
proof (induct xs)
  case Nil
  (* 基础情况：xs = []，需要证明 rev ([] @ ys) = rev ys @ rev [] *)
  (* 在这里可以输入 sledgehammer *)
  show ?case by simp
next
  case (Cons a xs')
  (* 归纳情况：已知 rev (xs' @ ys) = rev ys @ rev xs' *)
  (* 需要证明 rev ((a # xs') @ ys) = rev ys @ rev (a # xs') *)
  (* 在这里可以输入 sledgehammer *)
  show ?case by simp
qed


(* ========== 示例 5: Sledgehammer 的实际应用场景 ========== *)
(*
  场景：你写了一个定义，需要证明一些基本性质
*)

(* 定义一个简单的函数：计算列表元素之和 *)
fun list_sum :: "nat list ⇒ nat" where
  "list_sum [] = 0"
| "list_sum (x # xs) = x + list_sum xs"

(* 性质1：空列表的和是0 *)
lemma list_sum_nil:
  "list_sum [] = 0"
  (* sledgehammer 会建议： *)
  by simp

(* 性质2：单元素列表的和就是该元素 *)
lemma list_sum_single:
  "list_sum [x] = x"
  (* sledgehammer 会建议： *)
  by simp

(* 性质3：append 后的和等于两部分和的和 *)
lemma list_sum_append:
  "list_sum (xs @ ys) = list_sum xs + list_sum ys"
proof (induct xs)
  case Nil
  (* sledgehammer 帮助找到证明 *)
  show ?case by simp
next
  case (Cons a xs')
  (* sledgehammer 帮助找到证明 *)
  show ?case by simp
qed


(* ========== 示例 6: 当 sledgehammer 找到复杂证明时 ========== *)
(*
  有时 sledgehammer 会找到一些你不知道的引理
*)

lemma set_membership:
  fixes x :: nat
  shows "x ∈ {y. y < 10} ⟷ x < 10"
  (* sledgehammer 会建议使用 mem_Collect_eq *)
  by simp


(* ========== 示例 7: Sledgehammer 与归纳法结合 ========== *)
(*
  在你的练习题中使用 sledgehammer
*)

theorem sum_geometric:
  "sum (λx. (2::nat)^x) {x. x < n} = 2^n - 1"
proof (induct n)
  case 0
  (* 在这里输入 sledgehammer *)
  show ?case by simp
next
  case (Suc n)
  (* 这里可能需要手动添加一些 subgoal_tac，然后用 sledgehammer *)
  have "{x. x < Suc n} = insert n {x. x < n}" by auto
  (* 现在用 sledgehammer 来完成剩余部分 *)
  then show ?case using Suc.hyps by auto
qed


(* ========================================== *)
(*    实用技巧总结                              *)
(* ========================================== *)

(*
1. **何时使用 sledgehammer**：
   - 当你不确定需要哪个引理时
   - 当证明看起来应该很简单但你不知道怎么做时
   - 当你想快速验证某个性质是否成立时
   - 当你卡在证明的某一步时

2. **sledgehammer 的输出解释**：
   - "Try this: by simp" - 表示 simp 就够了
   - "Try this: by (metis xxx yyy)" - 需要使用 metis 和指定的引理
   - "Try this: by auto" - auto 可以解决
   - 有时会显示多个建议，选择最简单的

3. **sledgehammer 的限制**：
   - 不是所有定理都能自动证明
   - 复杂的归纳证明仍需手动构建框架
   - 超时可能发生（默认30秒）
   - 可以设置超时时间：sledgehammer [timeout = 60]

4. **高级选项**：
   - sledgehammer [verbose] - 显示详细信息
   - sledgehammer [provers = e spass z3] - 指定使用的证明器
   - sledgehammer [timeout = 60] - 设置超时时间（秒）
   - sledgehammer [isar_proof] - 生成 Isar 风格的证明

5. **调试技巧**：
   如果 sledgehammer 找不到证明：
   - 检查你的目标是否确实成立
   - 尝试分解成更小的引理
   - 手动添加一些中间步骤（subgoal_tac）
   - 增加超时时间
   - 查看相关的库文件，手动引入需要的引理
*)

(* ========================================== *)
(*    练习：尝试使用 sledgehammer               *)
(* ========================================== *)

(* 练习 1：简单的列表性质 *)
lemma exercise1:
  "length (rev xs) = length xs"
  (* 在这里试试 sledgehammer *)
  sorry

(* 练习 2：集合性质 *)
lemma exercise2:
  "x ∈ A ∪ B ⟷ x ∈ A ∨ x ∈ B"
  (* 在这里试试 sledgehammer *)
  sorry

(* 练习 3：算术性质 *)
lemma exercise3:
  fixes n m :: nat
  shows "n + m = m + n"
  (* 在这里试试 sledgehammer *)
  sorry

(* 练习 4：需要归纳的证明 *)
lemma exercise4:
  "length (map f xs) = length xs"
  (* 提示：可能需要归纳，然后在每一步使用 sledgehammer *)
  sorry

(*
  完成这些练习后，回到 InductionExercises.thy，
  在卡住的地方尝试使用 sledgehammer！
*)

end
