theory ListSepTest
  imports Main
begin

(* datatype 'a list = Nil ("[]") | Cons 'a "'a list" (infixr "#" 65) *)

primrec sep0 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "sep0 [] a = []" |
        "sep0 (x # xs) a = 
          (case xs of [] \<Rightarrow> [x] |
                      _  \<Rightarrow> x # a # (sep0 xs a))"

value "sep0 [a, b, c, d, e] x"
(* "[a, x, b, x, c, x, d, x, e]" :: "'a list" *)

fun sepme :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "sepme [] a = []" |
        "sepme [x] a = [x]" |
        "sepme (x # xs) a = x # a # (sepme xs a)"

fun sep :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where "sep [] a = []" |
        "sep [x] a = [x]" |
        "sep (x#y#zs) a = x # a # sep (y#zs) a"

value "sep [a, b, c, d, e] x"

value "sepme [a,b,c,d] x"
(* "[a, x, b, x, c, x, d, x, e]" :: "'a list" *)

end