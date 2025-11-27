theory Practice_Monad
  imports Main "HOL-Library.Monad_Syntax"
begin

section \<open>环境搭建：定义 State Monad\<close>

(* 定义 State 类型：一个函数，接收状态 s，返回结果 a 和新状态 s *)
type_synonym ('a, 's) state = "'s \<Rightarrow> 'a * 's"

(* 定义 return (unit): 不改变状态，只返回一个值 *)
definition return :: "'a \<Rightarrow> ('a, 's) state" where
  "return x = (\<lambda>s. (x, s))"

(* 定义 bind: 串联两个计算 *)
definition bind :: "('a, 's) state \<Rightarrow> ('a \<Rightarrow> ('b, 's) state) \<Rightarrow> ('b, 's) state" (infixl ">>=" 60) where
  "bind m f = (\<lambda>s. let (a, s') = m s in f a s')"

(* 关键步骤：告诉 Isabelle 使用我们的 bind 作为 do 语法的后端 *)
adhoc_overloading
  Monad_Syntax.bind bind


section \<open>题目 1：验证单子定律 (Monad Laws)\<close>

(* Monad 必须满足三条定律。这里请证明“左单位元律” (Left Identity)。
   即： do { x <- return a; f x }  等价于  f a
*)
lemma monad_left_identity:
  "(do { x <- return a; f x }) = f a"
  unfolding return_def bind_def
  by auto (* 这个很简单，auto 就能过，重点是理解展开的过程 *)

(* 请尝试证明“结合律” (Associativity) *)
lemma monad_associativity:
  "(do { y <- (do { x <- m; f x }); g y }) = 
   (do { x <- m; y <- f x; g y })"
  unfolding bind_def
  (* 提示：可能需要用 split: prod.splits 来处理 let (a, b) = ... 的情况 *)
  oops


section \<open>题目 2：状态操作验证\<close>

(* 定义 get: 读取当前状态 *)
definition get :: "('s, 's) state" where
  "get = (\<lambda>s. (s, s))"

(* 定义 put: 修改状态为 s' *)
definition put :: "'s \<Rightarrow> (unit, 's) state" where
  "put s' = (\<lambda>_. ((), s'))"

(* 任务：证明如果先把状态置为 5，再读取，得到的一定是 5。
*)
lemma put_get_test:
  "(do {
      put 5;
      x <- get;
      return x
   }) s = (5, 5)"
  unfolding put_def get_def return_def bind_def
  apply auto
  oops


section \<open>题目 3：复杂的业务逻辑\<close>

(* 一个 tick 函数：让状态加 1 *)
definition tick :: "(unit, nat) state" where
  "tick = (\<lambda>s. ((), s + 1))"

(* 任务：编写一个逻辑：
   执行两次 tick，然后如果当前状态是偶数，返回 True，否则 False。
   注意：初始状态是 s。
*)
lemma tricky_logic:
  "run_result (do {
      tick;
      tick;
      cur <- get;
      return (cur mod 2 = 0)
   }) s = ((s + 2) mod 2 = 0, s + 2)"
  (* 为了方便证明，我们可以直接展开左侧 *)
  unfolding tick_def get_def return_def bind_def
  apply auto
  oops

end