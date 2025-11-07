theory HSV_chapter5 imports Main begin

section ‹Representing circuits (cf. worksheet Section 5.1)›

text ‹Defining a data structure to represent fan-out-free circuits with numbered inputs›
(* 定义一个数据结构来表示带有编号输入的无扇出电路 *)

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text ‹A few example circuits›
(* 一些电路示例 *)

definition "circuit1 ≡ AND (INPUT 1) (INPUT 2)"
definition "circuit2 ≡ OR (NOT circuit1) FALSE"
definition "circuit3 ≡ NOT (NOT circuit2)"
definition "circuit4 ≡ AND circuit3 (INPUT 3)"

section ‹Simulating circuits (cf. worksheet Section 5.2)›

text ‹Simulates a circuit given a valuation for each input wire›
(* 给定每个输入线的赋值，模拟电路 *)

fun simulate where
  "simulate (AND c1 c2) ρ = ((simulate c1 ρ) ∧ (simulate c2 ρ))"
| "simulate (OR c1 c2) ρ = ((simulate c1 ρ) ∨ (simulate c2 ρ))"
| "simulate (NOT c) ρ = (¬ (simulate c ρ))"
| "simulate TRUE ρ = True"
| "simulate FALSE ρ = False"
| "simulate (INPUT i) ρ = ρ i"

text ‹A few example valuations›
(* 一些赋值示例 *)
definition "ρ0 ≡ λ_. True"  (* ρ0 为恒真函数 *)
definition "ρ1 ≡ ρ0(1 := True, 2 := False, 3 := True)" (* 基于已有函数 ρ0 定义新函数 ρ1, 其中仅更改自变量 1，2，3 时候的值 *)
(* 与其说是函数，实际上就是一组 1，2，3 INPUT 接口的取值 *)
definition "ρ2 ≡ ρ0(1 := True, 2 := True, 3 := True)"

text ‹Trying out the simulator›
(* 试用模拟器 *)

value "simulate circuit1 ρ1"
value "simulate circuit2 ρ1"
value "simulate circuit3 ρ1"
value "simulate circuit4 ρ1"
value "simulate circuit1 ρ2"
value "simulate circuit2 ρ2"
value "simulate circuit3 ρ2"
value "simulate circuit4 ρ2"

section ‹Structural induction on circuits (cf. worksheet Section 5.3)›
(* 电路的结构归纳法 *)

text ‹A function that switches each pair of wires entering an OR or AND gate›
(* 一个交换进入OR或AND门的每对导线的函数 *)

fun mirror where
  "mirror (NOT c) = NOT (mirror c)"
| "mirror (AND c1 c2) = AND (mirror c2) (mirror c1)"
| "mirror (OR c1 c2) = OR (mirror c2) (mirror c1)"
| "mirror TRUE = TRUE"
| "mirror FALSE = FALSE"
| "mirror (INPUT i) = INPUT i"

value "circuit1"
value "mirror circuit1"
value "circuit2"
value "mirror circuit2"

text ‹The following non-theorem is easily contradicted.›
(* 下面的非定理很容易被反驳。 *)

theorem "mirror c = c" 
  oops

text ‹Proving that mirroring doesn't affect simulation behaviour.›
(* 证明镜像操作不影响模拟行为。 *)

theorem mirror_is_sound: "simulate (mirror c) ρ = simulate c ρ"
  by (induct c, auto)

section ‹A simple circuit optimiser (cf. worksheet Section 5.4)›
(* 一个简单的电路优化器 *)

text ‹A function that optimises a circuit by removing pairs of consecutive NOT gates›
(* 一个通过移除连续的NOT门来优化电路的函数 *)

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text ‹Trying out the optimiser›
(* 试用优化器 *)

value "circuit1"
value "opt_NOT circuit1"
value "circuit2"
value "opt_NOT circuit2"
value "circuit3"
value "opt_NOT circuit3"
value "circuit4"
value "opt_NOT circuit4"

section ‹Rule induction (cf. worksheet Section 5.5)›
(* 规则归纳法 *)

text ‹A Fibonacci function that demonstrates complex recursion schemes›
(* 一个展示复杂递归模式的斐波那契函数 *)

fun fib :: "nat ⇒ nat" where
  "fib (Suc (Suc n)) = fib n + fib (Suc n)"
| "fib (Suc 0) = 1"
| "fib 0 = 1"

thm fib.induct (*  rule induction theorem for fib  *)
(* fib的规则归纳定理 *)

text ‹The nth Fibonacci number is greater than or equal to n›
(* 第n个斐波那契数大于或等于n *)
theorem "fib n ≥ n" 
proof (induct rule: fib.induct[of "λn. fib n ≥ n"])
  case (1 n)
  thus ?case 
    by (metis One_nat_def add_mono_thms_linordered_semiring(1) fib.simps(1) 
              fib.simps(3) le_zero_eq not_less_eq_eq plus_1_eq_Suc)
qed (auto)

section ‹Proving termination (cf. worksheet Section 5.6)›
(* 证明终止性 *)

fun θ :: "nat ⇒ nat" where
  "θ n = 3 - ((n + 3) mod 4)"

value "[θ 0, θ 1, θ 2, θ 3, θ 4, θ 5, θ 6, θ 7, θ 8]"

function g :: "nat ⇒ nat" where
  "g n = (if n mod 4 = 0 then n else g (n + 1))"
  by pat_completeness auto
termination by (relation "measure θ") (auto, presburger)



section ‹Verifying our optimiser (cf. worksheet Section 5.7)›
(* 验证我们的优化器 *)

text ‹The following non-theorem is easily contradicted.›
(* 下面的非定理很容易被反驳。 *)

theorem "opt_NOT c = c" 
  oops

text ‹The following theorem says that the optimiser is sound.›
(* 下面的定理说明优化器是可靠的。 *)

theorem opt_NOT_is_sound: "simulate (opt_NOT c) ρ = simulate c ρ"
  by (induct rule:opt_NOT.induct, auto)


end
