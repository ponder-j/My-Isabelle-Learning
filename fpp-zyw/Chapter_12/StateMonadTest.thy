theory StateMonadTest
  imports Main "HOL-Library.State_Monad"
begin
(* 状态单子基本定义 *)
(* datatype ('s, 'a) state = State (run_state: "'s ⇒ ('a × 's)") *)

(* 带记录选择器的 datatype 定义，拆开来写： *)

(* datatype ('s, 'a) state = State "'s ⇒ ('a × 's)"
fun run_state :: "('s, 'a) state ⇒ 's ⇒ ('a × 's)" where
  "run_state (State f) = f" *)

(* 也即 run_state 能从 State 构造器中取出函数 f，且这个 f 的类型是 's ⇒ ('a × 's) *)


(* 状态单子定义为's ⇒ ('a × 's)的结构，每个状态单子是一个改变状态并返回一个值的语句 *)


end