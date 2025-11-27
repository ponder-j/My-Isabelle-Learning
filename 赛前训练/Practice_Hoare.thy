theory Practice_Hoare
  imports Main "HOL-Hoare.Hoare_Logic"
begin

section \<open>第一部分：基础逻辑与条件分支\<close>

(* 题目 1：求最大值
   目标：验证一段包含 IF 的简单代码能正确找到较大值。
   提示：VCG 会自动处理 IF 分支，通常不需要额外的不变式。
*)
lemma find_max:
  "VARS x y m
  { True }
  IF x >= y THEN m := x ELSE m := y FI
  { m = max x y }"
  sorry


section \<open>第二部分：循环不变式 (Partial Correctness)\<close>

(* 题目 2：高斯求和 (1+2+...+n)
   目标：证明 s 最终等于 n*(n+1)/2。
   提示：Invariant 需要描述 s 与 i 的关系，以及 i 的范围。
         INV { s = i * (i + 1) div 2 & i <= n }
*)

(* INV 中是一个强提示，尝试理解为什么是这个 *)
lemma sum_upto_n: 
  "VARS i s
  { n > 0 }
  i := 0;
  s := 0;
  WHILE i < n
  INV { s = i * (i + 1) div 2 & i <= n } 
  DO
    i := i + 1;
    s := s + i
  OD
  { s = n * (n + 1) div 2 }"
  apply vcg
  apply auto
  sorry


(* 题目 3：计算 2 的幂 (Power of 2)
   目标：计算 p = 2^n。
   提示：Invariant 应该描述 p 始终是 2 的 i 次方。
*)
lemma power_of_two: (* 请在 ... 中填空：p = 2^i 且 i <= n *)
  "VARS i p
  { n >= 0 }
  i := 0;
  p := 1;
  WHILE i < n
  INV { p = 2 ^ i & i <= n } 
  DO
    p := 2 * p;
    i := i + 1
  OD
  { p = 2^n }"
  apply vcg
  (* apply auto *)
  sorry


section \<open>第三部分：完全正确性 (Total Correctness)\<close>

(* 题目 4：欧几里得除法 (Euclidean Division)
   目标：证明程序不仅计算正确，而且会停止（使用 VAR）。
   提示：VAR 必须是一个在每次循环中严格减小的自然数。
         在这里，余数 r 在不断减小吗？或者别的什么量？
*)
lemma euclidean_division: (* 变体：r 是自然数且每轮减小 *)
  "VARS r q
  { y > 0 }
  r := (x::nat);
  q := 0;
  WHILE y <= r
  INV { x = q * y + r }
  VAR { r } 
  DO
    r := r - y;
    q := q + 1
  OD
  { x = q * y + r & r < y }"
  apply vcg
  apply auto
  sorry

end