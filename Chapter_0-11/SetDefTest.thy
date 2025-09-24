theory SetDefTest
  imports Complex_Main
begin

definition Set0 :: "nat set"
  where "Set0 \<equiv> {0, 2, 4, 6}"

value "Set0"

definition Set1 :: "nat set"
  where "Set1 \<equiv> {..<100}"

value "Set1"

definition Set2 :: "nat set"
  where "Set2 \<equiv> {10..100}"

value "Set2"

definition Set3 :: "real set"
  where "Set3 \<equiv> {25.0 .. 125.0}"

definition Set4 :: "nat set"
  where "Set4 \<equiv> {n. n mod 2 = 0 \<and> n < 100}"

(* definition Set4 :: "nat set"
  where "Set4 \<equiv> Set.filter (\<lambda>n. n mod 2 = 0) {..<100}"
value "Set4" *)

(* definition Set4 :: "nat set"
  where "Set4 \<equiv> {n \<in> {..<100}. n mod 2 = 0}"
value "Set4" *)

value "2 \<in> Set0"
value "101 \<notin> Set1"

(* \<in> : 'a \<Rightarrow> 'a set \<Rightarrow> bool *)
(*value "1 \<in> \<nat>"*)

lemma "finite Set0 = True"
  unfolding Set0_def by simp

lemma "infinite Set3 = True"
  unfolding Set3_def by simp

value "card Set0"
(* "4"  :: "nat" *)
value "card Set2"
(* "91"  :: "nat" *)

end