theory BinarySearch
  imports Complex_Main
begin

function binary_search_iter :: "'a::linorder ⇒ 'a list ⇒ int ⇒ int ⇒ nat option" where
  "binary_search_iter x xs l r = (
     if l > r then None
     else let mid = (l + r) div 2 in
          if xs ! nat mid < x then binary_search_iter x xs (mid + 1) r
          else if xs ! nat mid > x then binary_search_iter x xs l (mid - 1)
          else Some (nat mid))"
  by auto

termination
  by (relation "measure (λ(_, _, l, r). nat (r - l + 1))") auto

definition binary_search :: "'a::linorder ⇒ 'a list ⇒ nat option" where
  "binary_search x xs = binary_search_iter x xs 0 (int (length xs) - 1)"

lemma binary_search_iter_correct:
  "binary_search_iter x xs l r = Some i ⟹ xs ! i = x"
proof (induction x xs l r rule: binary_search_iter.induct)
  case (1 x xs l r)
  then show ?case
    by (auto split: if_split_asm simp: Let_def)
qed

lemma binary_search_correct:
  "binary_search x xs = Some i ⟹ xs ! i = x"
  unfolding binary_search_def
  using binary_search_iter_correct by blast

lemma binary_search_iter_None:
  assumes "sorted xs"
  shows "binary_search_iter x xs l r = None ⟶ 
         (∀k < length xs. xs ! k = x ⟶ l ≤ int k ∧ int k ≤ r) ⟶ 
         x ∉ set xs"
  using assms
proof (induction x xs l r rule: binary_search_iter.induct)
  case (1 x xs l r)
  show ?case
  proof (intro impI)
    assume none: "binary_search_iter x xs l r = None"
    assume range: "∀k < length xs. xs ! k = x ⟶ l ≤ int k ∧ int k ≤ r"
    
    show "x ∉ set xs"
    proof (cases "l > r")
      case True
      show ?thesis
      proof
        assume "x ∈ set xs"
        then obtain k where k_props: "k < length xs" "xs ! k = x"
          by (metis in_set_conv_nth)
        then have "l ≤ int k ∧ int k ≤ r"
          using range by simp
        then show False
          using True by simp
      qed
    next
      case False
      have le: "l ≤ r" using False by auto
      let ?mid = "(l + r) div 2"
      have mid_eq: "?mid = (l + r) div 2" by simp
      
      show ?thesis
      proof (cases "xs ! nat ?mid < x")
        case True
        have IH: "binary_search_iter x xs (?mid + 1) r = None ⟶ 
                  (∀k < length xs. xs ! k = x ⟶ ?mid + 1 ≤ int k ∧ int k ≤ r) ⟶ 
                  x ∉ set xs"
          using 1(1)[OF le mid_eq True] .
        
        have "binary_search_iter x xs (?mid + 1) r = None"
          using none False True by (simp add: Let_def)
        
        have range_right: "∀k < length xs. xs ! k = x ⟶ ?mid + 1 ≤ int k ∧ int k ≤ r"
        proof (intro allI impI)
          fix k assume k_len: "k < length xs" and k_x: "xs ! k = x"
          have "l ≤ int k ∧ int k ≤ r" using range k_len k_x by simp
          moreover have "int k > ?mid"
          proof -
            have "xs ! nat ?mid < xs ! k" using True k_x by simp
            then have "nat ?mid < k" 
              using sorted_nth_mono[OF `sorted xs`] k_len
              by (metis leI le_less_trans not_le)
            then show ?thesis by simp
          qed
          ultimately show "?mid + 1 ≤ int k ∧ int k ≤ r" by simp
        qed
        
        show ?thesis
          using IH `binary_search_iter x xs (?mid + 1) r = None` range_right by simp
      next
        case False
        then have not_less: "¬ xs ! nat ?mid < x" by simp
        show ?thesis
        proof (cases "xs ! nat ?mid > x")
          case True
          have IH: "binary_search_iter x xs l (?mid - 1) = None ⟶ 
                    (∀k < length xs. xs ! k = x ⟶ l ≤ int k ∧ int k ≤ ?mid - 1) ⟶ 
                    x ∉ set xs"
            using 1(2)[OF le mid_eq not_less True] .

          have "binary_search_iter x xs l (?mid - 1) = None"
            using none False not_less True by (simp add: Let_def)
            
          have range_left: "∀k < length xs. xs ! k = x ⟶ l ≤ int k ∧ int k ≤ ?mid - 1"
          proof (intro allI impI)
            fix k assume k_len: "k < length xs" and k_x: "xs ! k = x"
            have "l ≤ int k ∧ int k ≤ r" using range k_len k_x by simp
            moreover have "int k < ?mid"
            proof -
              have "xs ! k < xs ! nat ?mid" using True k_x by simp
              then have "k < nat ?mid"
                using sorted_nth_mono[OF `sorted xs`]
                by (metis leI le_less_trans not_le nat_int)
              then show ?thesis by simp
            qed
            ultimately show "l ≤ int k ∧ int k ≤ ?mid - 1" by simp
          qed
          
          show ?thesis
            using IH `binary_search_iter x xs l (?mid - 1) = None` range_left by simp
        next
          case False
          then have "xs ! nat ?mid = x" using not_less by auto
          then have "binary_search_iter x xs l r = Some (nat ?mid)"
            using le by (simp add: Let_def)
          then show ?thesis using none by simp
        qed
      qed
    qed
  qed
qed

lemma binary_search_none: "sorted xs ⟹ binary_search x xs = None ⟹ x ∉ set xs"
  unfolding binary_search_def
  apply (rule binary_search_iter_None[where l="0" and r="int (length xs) - 1", THEN mp, THEN mp])
  apply simp
  apply simp
  apply simp
  apply (auto simp: in_set_conv_nth)
  done

end