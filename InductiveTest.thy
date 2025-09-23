theory InductiveTest
  imports Complex_Main
begin

inductive_set Even :: "int set"
  where zeroe: "0 \<in> Even" |
        plus2: "n \<in> Even \<Longrightarrow> n+2 \<in> Even" |
        minus2:"n \<in> Even \<Longrightarrow> n-2 \<in> Even"

inductive_set even :: "nat set"
  where zeroe: "0 \<in> even" |
        succe: "n \<in> even \<Longrightarrow> Suc (Suc n) \<in> even"

inductive_set trancl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  for R :: "('a \<times> 'a) set" where
  R_into_trancl: "(x, y) \<in> R \<Longrightarrow> (x, y) \<in> trancl R"
| R_trancl:      "(x, y) \<in> trancl R \<and> (y, z) \<in> R \<Longrightarrow> (x, z) \<in> trancl R"

definition "graph1 \<equiv> {(''v1'', ''v2''), (''v2'', ''v3''), (''v3'', ''v4'')}"
(* lemma "trancl graph1 = graph1 \<union> {(''v1'', ''v3''), (''v1'', ''v4''), (''v2'', ''v4'')}" *)

end