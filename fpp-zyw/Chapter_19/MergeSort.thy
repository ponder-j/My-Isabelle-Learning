theory MergeSort
  imports Complex_Main "HOL-Library.Multiset"
begin

fun merge :: "('a::linorder) list ⇒ ('a::linorder) list ⇒ ('a::linorder) list" where
  "merge (x#xs) (y#ys) =(if x ≤ y then  x # merge xs (y#ys) else y # merge (x#xs) ys)"
| "merge xs [] = xs"
| "merge [] ys = ys"

fun msort :: "('a::linorder) list ⇒ ('a::linorder) list" where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = merge (msort (take (size xs div 2) xs)) (msort (drop (size xs div 2) xs))"

lemma mset_merge [simp]: "mset (merge xs ys) = mset xs + mset ys"
  by (induction xs ys rule: merge.induct) auto

lemma set_merge [simp]: "set (merge xs ys) = set xs ∪ set ys"
  by (metis mset_merge set_mset_mset set_mset_union)

lemma sorted_merge [simp]: "sorted xs ⟹ sorted ys ⟹ sorted (merge xs ys)"
  by (induction xs ys rule: merge.induct) (auto simp: sorted_Cons)

lemma mset_msort: "mset (msort xs) = mset xs"
  by (induction xs rule: msort.induct) auto

lemma sorted_msort: "sorted (msort xs)"
  by (induction xs rule: msort.induct) auto

end