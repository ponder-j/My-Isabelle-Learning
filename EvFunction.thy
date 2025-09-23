theory EvFunction
  imports Main
begin

(* 方法一：使用 presburger 策略 *)
function ev :: "nat \<Rightarrow> bool"
  where "ev (2 * n) = True" |
        "ev (2 * n + 1) = False"
  apply atomize_elim
  apply presburger
  done
termination by lexicographic_order