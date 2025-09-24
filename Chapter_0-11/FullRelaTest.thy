theory FullRelaTest
  imports Main
begin

definition total_on :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
  where "total_on A r \<equiv> (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"

definition set0 :: "int set"
  where "set0 \<equiv> {1, 2}"

value "total_on set0 {(1,1),(1,2)}"
value "total_on set0 {(1,1),(1,2),(2,1)}"
value "total_on set0 {(1,1),(1,2),(2,2)}"

definition "rela0 \<equiv> set0 \<times> set0"
value "rela0"
value "total_on set0 rela0"

end