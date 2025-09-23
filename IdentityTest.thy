theory IdentityTest
  imports Complex_Main
begin

definition Id :: "('a \<times> 'a) set"
  where "Id = {(x,y). x = y}"

definition "Id_int = (Id :: (int \<times> int) set)"

definition "Id_real = (Id :: (real \<times> real) set)"

definition Id_on :: "'a set \<Rightarrow> 'a rel"
  where "Id_on A = (\<Union>x\<in>A. {(x, x)})"

value "Id_on {''v1'',''v2'',''v3''}"
(* 输出 "{(''v1'', ''v1''), (''v2'', ''v2''), 
			(''v3'', ''v3'')}" :: "(char list \<times> char list) set" *)

lemma "Id_on {x::int. True} = Id_int"

