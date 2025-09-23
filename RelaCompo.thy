theory RelaCompo
  imports Main
begin

(* inductive_set relcomp  :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set"  (infixr "O" 75)
  for R :: "('a \<times> 'b) set" and S :: "('b \<times> 'c) set"
  where "(a, b) \<in> R \<Longrightarrow> (b, c) \<in> S \<Longrightarrow> (a, c) \<in> R O S "*)

definition "graph1 \<equiv> {(''v1'', ''v2''), (''v2'', ''v3''), (''v3'', ''v4'')}"

definition "graph2 \<equiv> {(''v1'', ''v1''), (''v2'', ''v2''), (''v1'', ''v3''), 
					  (''v2'', ''v3''), (''v3'', ''v4''), (''v4'', ''v5'')}"

value "graph1 O graph2"
(* "{(''v1'', ''v2''), (''v1'', ''v3''), (''v2'', ''v4''), (''v3'', ''v5'')}" :: "(char list \<times> char list) set" *)

end