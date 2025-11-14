theory FunCalc
  imports Main
begin

definition fun1 :: "int \<Rightarrow> int"
  where "fun1 x \<equiv> x + 1"

value "fun1 2"
(* 输出 "3" :: "int" *)
value "(fun1(2 := 2)) 2"
(* 输出 "2" :: "int" *)
value "(fun1(1 := 1, 2 := 2, 3 := 3)) 3"
(* 输出 "3" :: "int" *)

definition fun4 :: "int \<Rightarrow> int"
  where "fun4 x \<equiv> x * 2"

value "fun4 ` {1,2,3}"
(* 输出 "{2, 4, 6}" :: "int set" *)

value "fun4 ` {1..10}"
(* 输出 "{2, 4, 6, 8, 10, 12, 14, 16, 18, 20}" :: "int set" *)


definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "swap a b f = f (a := f b, b:= f a)"

definition "fun5 \<equiv> swap 2 3 fun4"
value "fun4 2"
(* 输出 "4" :: "int" *)
value "fun4 3"
(* 输出 "6" :: "int" *)
value "fun5 2"
(* 输出 "6" :: "int" *)
value "fun5 3"
(* 输出 "4" :: "int" *)

definition suc :: "int \<Rightarrow> int"
  where "suc n \<equiv> n + 1"

definition "suc_inv \<equiv> the_inv suc"

definition pred :: "int \<Rightarrow> int"
  where "pred n \<equiv> n - 1"

definition suc2 :: "nat \<Rightarrow> nat"
  where "suc2 n \<equiv> n + 2"

definition "suc2_inv = the_inv suc2"



end
