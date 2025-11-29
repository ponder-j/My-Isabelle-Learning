theory LinearSearch
  imports Complex_Main
begin

fun liner_search_iter :: "'a ⇒ 'a list ⇒ nat ⇒ nat option" where
"liner_search_iter _ [] _ = None"|
"liner_search_iter x (x0 # xs) idx = 
	(if x=x0 then (Some idx) else (liner_search_iter x xs (idx+1)))"

fun liner_search :: "'a ⇒ 'a list ⇒ nat option" where
"liner_search a xs = liner_search_iter a xs 0"

lemma liner_search_some: 
"liner_search_iter x xs v = Some vi ⟹ ∃ ui. liner_search_iter x xs u = Some ui"
  proof(induction xs arbitrary: v u) 
(* goal (2 subgoals):
1. ⋀v u. liner_search_iter x [] v = Some vi ⟹ ∃ui. liner_search_iter x [] u = Some ui
 2. ⋀a xs v u.
       (⋀v u. liner_search_iter x xs v = Some vi ⟹ ∃ui. liner_search_iter x xs u = Some ui) ⟹
       liner_search_iter x (a # xs) v = Some vi ⟹ ∃ui. liner_search_iter x (a # xs) u = Some ui *)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case proof(cases "x = a")
      assume "x=a"
      then have " liner_search_iter x (a # xs) u = Some u"
        by simp 
      then show ?case
        by blast 
    next
      assume "¬ x=a"
      then have "liner_search_iter x (a # xs) u = liner_search_iter x xs (u+1)" by simp
      then show ?case
        by (metis Cons.IH Cons.prems liner_search_iter.simps(2)) 
    qed
  qed

lemma liner_search_none: "liner_search_iter x xs v = None ⟹ liner_search_iter x xs u = None"
proof(induction xs) 
(* goal (2 subgoals):
1. liner_search_iter x [] v = None ⟹ liner_search_iter x [] u = None
2. ⋀a xs. (liner_search_iter x xs v = None ⟹ liner_search_iter x xs u = None) ⟹
		liner_search_iter x (a # xs) v = None ⟹ liner_search_iter x (a # xs) u = None  *)
case Nil
  then show ?case by auto
next
case (Cons a xs)
then show ?case
    by (metis liner_search_some option.exhaust option.simps(2)) 
qed

lemma liner_search_iter_correct:
  "liner_search_iter x xs n = Some idx ⟹ idx ≥ n ∧ x = xs ! (idx - n)"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "x = a")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    then have "liner_search_iter x (a # xs) n = liner_search_iter x xs (n + 1)" by simp
    with Cons.prems have "liner_search_iter x xs (n + 1) = Some idx" by simp
    from Cons.IH[OF this] have "idx ≥ n + 1" and "x = xs ! (idx - (n + 1))" by auto
    then show ?thesis using False
      by (simp add: nth_Cons')
  qed
qed

lemma liner_search_idx: "liner_search x xs = Some idx ⟹ x = xs ! idx"
  using liner_search_iter_correct by fastforce

end