theory BubbleSort
imports Main "HOL-Library.Multiset"
begin

fun bubble_min :: "'a::linorder list ⇒ 'a list" where
"bubble_min [] = []" |
"bubble_min [x] = [x]" |
"bubble_min (x#y#xs) = (case bubble_min (y#xs) of
                          m#ms ⇒ if x > m then m#x#ms else x#m#ms
                        | [] ⇒ [])"

lemma length_bubble_min: "length (bubble_min xs) = length xs"
  by (induction xs rule: bubble_min.induct) (auto split: list.split)

lemma mset_bubble_min: "mset (bubble_min xs) = mset xs"
  by (induction xs rule: bubble_min.induct) (auto split: list.split)

function bubblesort :: "'a::linorder list ⇒ 'a list" where
"bubblesort [] = []" |
"bubblesort [x] = [x]" |
"bubblesort (x#v#va) = (case bubble_min (x#v#va) of
                          y#ys ⇒ y # bubblesort ys
                        | [] ⇒ [])"
  by pat_completeness auto

termination
  by (relation "measure length") (metis length_bubble_min length_Cons list.size(4) less_Suc_eq)

lemma mset_bubblesort: "mset (bubblesort xs) = mset xs"
proof (induction xs rule: bubblesort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x v va)
  let ?xs = "x # v # va"
  obtain y ys where bub: "bubble_min ?xs = y#ys"
    by (metis length_bubble_min length_0_conv list.exhaust)
  then have "mset ?xs = mset (y#ys)"
    using mset_bubble_min by metis
  then have "mset ?xs = {#y#} + mset ys"
    by simp
  then have "mset ys = mset ?xs - {#y#}"
    by simp
  moreover have "bubblesort ?xs = y # bubblesort ys"
    using bub by simp
  ultimately show ?case
    using 3(1)[OF bub] mset_bubble_min bub by (metis mset.simps(2))
qed

lemma bubble_min_min: "xs ≠ [] ⟹ hd (bubble_min xs) = Min (set xs)"
proof (induction xs rule: bubble_min.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y xs)
  let ?xs = "y # xs"
  obtain m ms where bub: "bubble_min ?xs = m#ms"
    by (metis length_bubble_min length_0_conv list.exhaust)
  
  have "hd (bubble_min ?xs) = Min (set ?xs)"
    using 3(1) by simp
  then have "m = Min (set ?xs)"
    using bub by simp
    
  show ?case
  proof (cases "x > m")
    case True
    then have "min x m = m"
      by (auto simp: min_def)
    then have "bubble_min (x # ?xs) = m # x # ms"
      using bub True by simp
    then have "hd (bubble_min (x # ?xs)) = m"
      by simp
    moreover have "Min (set (x # ?xs)) = min x (Min (set ?xs))"
      by simp
    ultimately show ?thesis
      using `m = Min (set ?xs)` `min x m = m` by simp
  next
    case False
    then have "min x m = x"
      by (auto simp: min_def)
    then have "bubble_min (x # ?xs) = x # m # ms"
      using bub False by simp
    then have "hd (bubble_min (x # ?xs)) = x"
      by simp
    moreover have "Min (set (x # ?xs)) = min x (Min (set ?xs))"
      by simp
    ultimately show ?thesis
      using `m = Min (set ?xs)` `min x m = x` by simp
  qed
qed

lemma sorted_bubblesort: "sorted (bubblesort xs)"
proof (induction xs rule: bubblesort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x v va)
  let ?xs = "x # v # va"
  obtain y ys where bub: "bubble_min ?xs = y#ys"
    by (metis length_bubble_min length_0_conv list.exhaust)
  
  have "bubblesort ?xs = y # bubblesort ys"
    using bub by simp
  
  have "sorted (bubblesort ys)"
    using 3(1)[OF bub] by simp
    
  have "y = Min (set ?xs)"
    using bubble_min_min[of ?xs] bub by simp
    
  have "mset (y#ys) = mset ?xs"
    using mset_bubble_min bub by metis
  then have "set (y#ys) = set ?xs"
    by (metis set_mset_mset)
  then have "set ys ⊆ set ?xs" by auto
  
  have "∀z ∈ set ys. y ≤ z"
  proof
    fix z assume "z ∈ set ys"
    then have "z ∈ set ?xs" using `set ys ⊆ set ?xs` by auto
    then show "y ≤ z" using `y = Min (set ?xs)` by (metis Min_le finite_set list.set(1))
  qed
  
  then have "∀z ∈ set (bubblesort ys). y ≤ z"
    using mset_bubblesort by (metis set_mset_mset)
    
  then show ?case
    using `sorted (bubblesort ys)` `bubblesort ?xs = y # bubblesort ys`
    by (simp add: sorted_wrt.simps)
qed

end