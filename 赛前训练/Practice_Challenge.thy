theory Practice_Challenge
  imports Complex_Main
begin

(********************************************************************)
(* 第一部分：基本证明 (Basic Logic & Sets)                         *)
(* 目标：熟悉 Isar 结构化证明风格，练习量词与集合的基本推理。      *)
(********************************************************************)

(* 题目 1: 满射函数的复合性质
  如果 f 和 g 的复合函数 (f \<circ> g) 是满射 (surjective)，那么 f 也是满射。
  
  提示：
  1. 满射定义: surjective f \<longleftrightarrow> (\<forall>y. \<exists>x. f x = y)
  2. 尝试使用 Isar 风格 (proof - ... show ... qed)
  3. 可能需要用到 `fix`, `assume`, `obtain` (用于消除存在量词)
*)

definition surjective :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "surjective f \<longleftrightarrow> (\<forall>y. \<exists>x. f x = y)"

lemma surjective_comp:
  assumes "surjective (f \<circ> g)"
  shows "surjective f"
proof -
  (* 参考答案：结构化 Isar 证明 *)
  (* 目标是证明 surjective f，即对于任意 y，存在 x 使得 f x = y *)
  show "surjective f"
    unfolding surjective_def
  (* proof (rule allI) 引入全称量词规则 *)
  proof
    fix y
    (* 利用假设：f \<circ> g 是满射，所以对于当前的 y，存在某个 x 使得 (f \<circ> g) x = y *)
    from assms have "surjective (f \<circ> g)" .
    then obtain x where "(f \<circ> g) x = y" 
      unfolding surjective_def by blast
    
    (* 展开复合函数定义，得到 f (g x) = y *)
    then have "f (g x) = y" by simp
    
    (* 因为我们找到了 witness (即 g x)，所以存在这样的 x *)
    then show "\<exists>z. f z = y" by blast
  qed
qed
(* proof -
  (* 请在此处填入你的 Isar 证明 *)
  (* 提示思路：
     我们要证明对于任意 y，都存在一个 x 使得 f x = y。
     从假设已知 f(g(x')) = y 对某个 x' 成立... *)
  have "surjective (f \<circ> g)"
    by (simp add: assms)
  hence "\<forall>y. \<exists>x. (f \<circ> g) x = y"
    by (simp add: surjective_def)
  hence "\<forall>y. \<exists>x. f (g x) = y"
    by auto
  hence "\<forall>y. \<exists>x. f x = y"
    by auto
  thus "surjective f"
    using surjective_def by blast
qed *)



(********************************************************************)
(* 第二部分：算法证明 (Algorithm Verification)                     *)
(* 目标：掌握递归函数、归纳法 (Induction) 以及至关重要的“泛化”技巧。 *)
(********************************************************************)

(*
  题目 2: 尾递归反转列表 (Tail Recursive Reverse)
  我们定义了普通的列表反转 `reverse` 和尾递归版本的 `itrev`。
  请证明 `itrev` 和 `reverse` 的逻辑等价性。

  难点提示：
  直接对 `itrev xs [] = reverse xs` 进行归纳会失败！
  你需要找到一个更通用的引理 (Generalization Lemma)，涉及累加器 `ys`。
  策略：apply (induction xs arbitrary: ys)
*)

(* 普通的列表反转 *)
primrec reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = reverse xs @ [x]"

(* 尾递归优化的列表反转 (更高效，因为使用了累加器) *)
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

(* 关键引理：你需要先证明这个性质，主定理才能得证 *)
lemma itrev_generalization: "itrev xs ys = reverse xs @ ys"
  (* 请在此处完成证明 *)
  apply (induct xs arbitrary: ys)
  by simp+

(* 主定理 *)
theorem itrev_correct: "itrev xs [] = reverse xs"
  (* 如果上面的引理证明正确，这里通常只需要 simp *)
  by (simp add: itrev_generalization)


(********************************************************************)
(* 第三部分：数学证明 (Mathematical Proofs)                        *)
(* 目标：练习自然数归纳法以及算术表达式的自动化简化。              *)
(********************************************************************)

(*
  题目 3: 前 n 个奇数之和
  证明：1 + 3 + 5 + ... + (2n-1) = n^2
*)

(* 定义递归求和函数：计算前 n 个奇数的和 *)
fun sum_odds :: "nat \<Rightarrow> nat" where
"sum_odds 0 = 0" |
"sum_odds (Suc n) = sum_odds n + (2 * n + 1)"

lemma sum_of_odds_is_square: "sum_odds n = n * n"
  apply (induct n)
  by simp+

(********************************************************************)
(* 第四部分：程序验证 (Program Verification)                       *)
(* 目标：编译器正确性证明。这是程序验证领域的“Hello World”。        *)
(* 考察：抽象语法树 (AST)、列表操作、结构归纳法。                  *)
(********************************************************************)

(* 背景：
  我们有一个简单的算术表达式语言 (Exp)，只包含常量和加法。
  我们还有一个基于栈的虚拟机 (Stack Machine)，指令集为 Push 和 Add。
  我们要编写一个编译器 (compile)，把表达式编译成指令序列。
  目标：证明执行编译后的指令序列，等同于直接计算表达式的值。
*)

(* 1. 定义算术表达式 *)
datatype expr = 
  Const int          (* 常量，例如 5 *)
| Plus expr expr     (* 加法，例如 5 + 3 *)

(* 2. 定义表达式的“指称语义” (即：它的值是多少) *)
primrec eval :: "expr \<Rightarrow> int" where
"eval (Const i) = i" |
"eval (Plus e1 e2) = eval e1 + eval e2"

(* 3. 定义栈机器的指令 *)
datatype instr = 
  IPush int          (* 将整数压入栈 *)
| IAdd               (* 从栈顶弹出两个数相加，结果压回栈 *)

(* 4. 定义栈机器的执行语义 *)
(* stack 是一个整数列表 *)
fun exec :: "instr list \<Rightarrow> int list \<Rightarrow> int list" where
"exec [] stack = stack" |
"exec (IPush n # ins) stack = exec ins (n # stack)" |
"exec (IAdd # ins) (x # y # stack) = exec ins ((x + y) # stack)" |
"exec (IAdd # ins) _ = []" (* 错误处理：栈元素不足时清空，简化模型 *)

(* 5. 定义编译器：将表达式转换为指令列表 *)
primrec compile :: "expr \<Rightarrow> instr list" where
"compile (Const i) = [IPush i]" |
"compile (Plus e1 e2) = compile e2 @ compile e1 @ [IAdd]"

(* 题目 4: 编译器正确性 (Compiler Correctness)
  证明：执行编译后的代码，栈顶结果就是表达式的值。
  
  难点提示：
  直接证明 `exec (compile e) [] = [eval e]` 会遇到困难。
  因为在递归调用中，compile e2 执行完后，栈并不是空的！
  你需要证明一个更强的性质：exec (compile e @ more) stack = ...
*)

lemma exec_compile_general: "exec (compile e @ ins) stack = exec ins (eval e # stack)"
  (* 提示：对表达式 e 进行归纳 (induction e) *)
  (* 你可能需要用到 append 的结合律 (append_assoc) *)
  apply (induct e arbitrary: ins stack)
  by simp+


theorem compiler_correct: "exec (compile e) [] = [eval e]"
  (* 如果上面的引理证毕，这里就很简单了 *)
  by (metis append.right_neutral exec.simps(1) exec_compile_general)

end