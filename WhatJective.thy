theory WhatJective
  imports Complex_Main
begin

(* definition inj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"  
  where "inj_on f A \<equiv> (\<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y)"
abbreviation inj :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "inj f \<equiv> inj_on f UNIV"

abbreviation surj :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "surj f \<equiv> range f = UNIV"

abbreviation bij :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "bij f \<equiv> inj f \<and> surj f" *)

definition add1 :: "nat \<Rightarrow> nat"
  where "add1 n \<equiv> n + 1"

definition add2 :: "real \<Rightarrow> real"
  where "add2 r \<equiv> r + 1"

lemma "inj add1"
  unfolding inj_def inj_on_def add1_def
  by simp

lemma "\<not>surj add1"
  unfolding surj_def add1_def
  by (metis nat.distinct(1) rangeE)

lemma "inj add2"
  unfolding inj_def inj_on_def add2_def
  by simp

(* lemma "surj add2" *)
(* lemma "bij add2" *)

end