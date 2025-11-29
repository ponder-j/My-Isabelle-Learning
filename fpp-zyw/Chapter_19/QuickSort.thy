theory QuickSort
  imports Complex_Main "HOL-Library.Multiset"
begin

fun quicksort :: "('a::linorder) list ⇒ 'a list" where
  "quicksort []     = []"
| "quicksort (x#xs) = quicksort [y←xs. ¬ x≤y] 
                            @ [x] @ 
                           quicksort [y←xs. x≤y]"

(* lemma mset_quicksort: "mset (quicksort xs) = mset xs"
apply(induct xs rule: quicksort.induct)
  apply simp
  by (simp add: add.commute)

lemma sorted_quicksort: "sorted (quicksort xs)"
apply(induct xs rule: quicksort.induct)
  apply simp
  sorry *)

lemma quicksort_mset: "mset (quicksort xs) = mset xs"
proof (induction xs rule: quicksort.induct)
  case (2 x xs)
  have "mset [y←xs. ¬ x≤y] + mset [y←xs. x≤y] = mset xs"
    by (induction xs) auto
  then show ?case using 2 by simp
qed simp

lemma set_quicksort [simp]: "set (quicksort xs) = set xs"
  by (metis quicksort_mset set_mset_mset)

lemma sorted_quicksort: "sorted (quicksort xs)"
proof (induction xs rule: quicksort.induct)
  case (2 x xs)
  let ?lhs = "[y←xs. ¬ x≤y]"
  let ?rhs = "[y←xs. x≤y]"
  
  have "set (quicksort ?lhs) = set ?lhs" by simp
  then have "∀l ∈ set (quicksort ?lhs). l ≤ x" by auto
    
  have "set (quicksort ?rhs) = set ?rhs" by simp
  then have "∀r ∈ set (quicksort ?rhs). x ≤ r" by auto
    
  show ?case
    using 2 `∀l ∈ set (quicksort ?lhs). l ≤ x` `∀r ∈ set (quicksort ?rhs). x ≤ r`
    by (auto simp: sorted_append)
qed simp

end