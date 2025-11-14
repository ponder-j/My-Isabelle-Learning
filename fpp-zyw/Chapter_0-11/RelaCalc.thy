theory RelaCalc
  imports Main
begin

(* inductive_set converse :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'a) set"  ("(_\<inverse>)") 
	for r :: "('a \<times> 'b) set"
       where "(a, b) \<in> r \<Longrightarrow> (b, a) \<in> r\<inverse>" *)
definition "graph1 \<equiv> {(''v1'', ''v2''), (''v2'', ''v3''), (''v3'', ''v4'')}"
value "graph1\<inverse>"

end