theory StateMonadTest
  imports Main "HOL-Library.State_Monad"
begin
(* 状态单子基本定义 *)
datatype ('s, 'a) state = State (run_state: "'s ⇒ ('a × 's)")
(* 状态单子定义为's ⇒ ('a × 's)的结构，把每个状态单子看作是一个改变状态并返回一个值的语句 *)


end