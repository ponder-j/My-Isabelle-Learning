theory FunorFunction
  imports Main
begin

fun fib2 :: "nat \<Rightarrow> nat"
  where "fib2 0 = 1" |
        "fib2 (Suc 0) = 1" |
        "fib2 (Suc (Suc 0)) = 2" |
        "fib2 (Suc (Suc n)) = fib2 n + fib2 (Suc n)"

value "fib2 0"
value "fib2 2"
value "fib2 9"

function fib3 :: "nat \<Rightarrow> nat"
  where "fib3 0 = 1" |
        "fib3 1 = 1" |
        "fib3 (n + 2) = fib3 n + fib3 (n + 1)"
        apply atomize_elim
        apply arith
  by auto
termination by lexicographic_order

function ev :: "nat \<Rightarrow> bool"
  where "ev (2 * n) = True" |
        "ev (2 * n + 1) = False"
        apply atomize_elim
        apply arith
  by auto
termination by lexicographic_order

end