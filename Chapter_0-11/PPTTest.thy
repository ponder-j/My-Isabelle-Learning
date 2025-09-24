theory PPTTest
(* Product, Pair and Tuple *)
  imports Main
begin

datatype Vertex = v1 | v2 | v3 | v4 | v5 | v6 | v7
definition rel1 :: "Vertex \<times> Vertex"
  where "rel1 \<equiv> (v1, v2)"

definition rel2 :: "Vertex \<times> Vertex"
  where "rel2 \<equiv> Pair v3 v4"

value "rel1"
(* "(v1, v2)"
  :: "Vertex \<times> Vertex" *)
value "rel2"
(* "(v3, v4)"
  :: "Vertex \<times> Vertex" *)

term Pair
(* "Pair"
  :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b" *)

value "fst rel1"
(* "v1"
  :: "Vertex" *)
value "snd rel2"
(* "v4"
  :: "Vertex" *)

definition Agraph :: "(Vertex \<times> Vertex) set"
  where "Agraph \<equiv> {(v1, v2), (v1, v3), (v2, v4), (v4, v3), (v4, v5), (v3, v6), (v5, v7), (v6, v7)}"

definition "conn1 \<equiv> Pair v1 v2"
lemma "fst conn1 = v1"
  by (simp add: conn1_def)
lemma "snd conn1 = v2"
  by (simp add: conn1_def)

(* n-tuple *)
value "fst ((a,b),c)"
(* output (a,b) *)
value "fst (a,b,c)"
(* output a *)
value "snd ((a,b),c)"
(* output c *)
value "snd (a,b,c)"
(* output (b,c) *)
value "fst (fst ((a,b),c))"
(* output a *)
value "snd (fst ((a,b),c))"
(* output b *)

end