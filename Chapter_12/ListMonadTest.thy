theory ListMonadTest
    imports Main "HOL-Library.Monad_Syntax"
begin

(* List Monad *)
(* 支持错误的计算结果（空列表）和多个成功的返回值 *)
definition bind :: "'a list ⇒ ('a ⇒ 'b list) ⇒ 'b list"
    where "bind xs f = concat (map f xs)"

definition return :: "'a ⇒ 'a list"
    where "return a ≡ [a]"

(* 使用单子可以对列表的每个元素进行处理 *)
definition "sqr_even l ≡
  do {
    x ← l;
    if x mod 2 = 0 then
        return (x * x)
    else
        return x
  }"

value "sqr_even [1..10]"

(* 使用单子，可以很容易实现列表的复制 *)
definition "list_double l ≡
  do {
    x ← l;
    [x, 2 * x]
  }"

value "list_double [1..5]"

(* 采用列表单子实现两个列表元素的任意组合 *)
(* 下面的例子相当于实现了一个 Descartes 积 *)
(* concat (map (λx. concat (map (λy. [(x,y)]) ys)) xs) *)
definition "prod1 xs ys ≡
  do {
    x ← xs;
    y ← ys;
    return (x, y)
  }"

value "prod1 [a,b,c] [e,f,g]"

end