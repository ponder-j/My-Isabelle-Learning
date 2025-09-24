theory DomainRange
  imports Main
begin

inductive_set Domain :: "('a \<times> 'b) set \<Rightarrow> 'a set" for r :: "('a \<times> 'b) set"
  where "(a, b) \<in> r \<Longrightarrow> a \<in> Domain r"

inductive_set Range :: "('a \<times> 'b) set \<Rightarrow> 'b set" for r :: "('a \<times> 'b) set"
  where "(a, b) \<in> r \<Longrightarrow> b \<in> Range r"

end