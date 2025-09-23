theory FirstHigherOrderFun
  imports Complex_Main
begin

definition fof1 :: "nat \<Rightarrow> nat"
  where "fof1 x \<equiv> x ^ 2"

value "fof1 2"

fun fof2 :: "(nat \<times> nat) \<Rightarrow> nat"
  where "fof2 (x, y) = x + y"

value "fof2 (2, 3)"

fun fof3 :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat"
  where "fof3 (x, y, z) = x + y * z"

value "fof3 (2, 3, 4)"

definition hof1 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  where "hof1 f x y \<equiv> f x y"

value "hof1 plus (1::int) 2"
(* 输出 "3" :: "int" *)
value "hof1 times (3::int) 4"
(* 输出 "12" :: "int" *)
value "hof1 plus (1.5::real) 2"
(* 输出 "3.5" :: "real" *)
value "hof1 append ''hello'' ''world''"
(* 输出 "''helloworld''" :: string *)
value "hof1 append [a,b,c] [e,f,g]"
(* 输出 "[a, b, c, e, f, g]" :: "'a list" *)

end