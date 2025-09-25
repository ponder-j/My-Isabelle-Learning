theory MonadTest
imports Main "HOL-Library.Monad_Syntax"
begin
(* 在函数式语言中，单子可以为纯函数式语言提供非函数式语言的一些方便的特性，从而简化程序开发 *)

(* (return v) >>= f ≡ f v
m >>= return ≡ m
(m >>= f) >>= g ≡ m >>= (λx. (f x >>= g)) *)

(* Option Monad *)
(* 这个 bind 的定义可有可无，事实上是 Isabelle 自带的 *)
primrec bind :: "'a option ⇒ ('a ⇒ 'b option) ⇒ 'b option" (infixl ">>=" 70)
    where
        "bind None f = None"
      | "bind (Some x) f = f x"
definition return :: "'a ⇒ 'a option"
where "return x = Some x"

definition add :: "int option ⇒ int option ⇒ int option"
    where "add x y ≡ do {
        mx ← x;
        my ← y;
        return (mx + my)
    }"
value "add (Some 2) None"
value "add (Some 3) (Some 5)"

definition adds :: "int option ⇒ int option"
    where "adds x ≡ do {
        a ← x;
        b ← add (Some a) (Some 1);
        c ← add (Some b) (Some 2);
        d ← add (Some c) (Some 3);
        return d
        }"
value "adds (Some 2)"

definition safe_div :: "int option ⇒ int option ⇒ int option"
    where "safe_div x y ≡
      do {
        mx ← x;
        my ← y;
        if my ≠ 0 then return (mx div my) else None
    }"

value "safe_div (Some 5) (Some 0)"
value "safe_div (Some 6) (Some 4)"

definition comps :: "int option ⇒ int option"
    where "comps x ≡
      do {
        a ← add x (Some (-3));
        b ← safe_div (Some 6) (Some a);
        c ← add (Some b) (Some (-6));
        d ← safe_div (Some 15) (Some c);
        return d
    }"

value "comps (Some 3)"
value "comps (Some 4)"
value "comps (Some 5)"


end