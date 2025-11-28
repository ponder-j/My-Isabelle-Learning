theory PriorityQueue
  imports Main
begin

(* 'a是元素的类型，'b是优先级的类型 *)
(* xs 是一个列表，所以需要使用 map fst xs 对 xs 中的每一个元素进行 fst 操作 *)
(* 盲猜 distinct 是判断是否有重复元素的意思，数据库里也是这么用的 *)
typedef (overloaded) ('a, 'b::linorder) pri_queue =
  "{xs :: ('a \<times> 'b) list. distinct (map fst xs) \<and> sorted (map snd xs)}"
  morphisms alist_of Abs_pq
proof -
  have "[] \<in> ?pri_queue" by simp
  then show ?thesis by blast
qed

(* 获取优先队列中的所有元素值 *)
definition "values" :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a list" ("|(_)|") where
  "values q = map fst (alist_of q)"

(* 获取优先队列中所有优先级值 *)
definition priorities :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'b list" ("\<parallel>(_)\<parallel>") where
  "priorities q = map snd (alist_of q)"

(* 判空 *)
definition is_empty :: "('a, 'b::linorder) pri_queue \<Rightarrow> bool" where
  "is_empty q \<equiv> alist_of q = []"

(* map_of 构建查找表，对于查找不到的元素可以返回 None *)
definition priority :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "priority q \<equiv> map_of (alist_of q)"

(* 提取最小值 *)
(* hd 即提取列表开头元素 *)
definition min :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a" where
  "min q \<equiv> fst (hd (alist_of q))"

definition ega :: "nat list" where
  "ega \<equiv> [1,2,3]"

(* 定义 empty，即将一个空列表转换为对应的优先队列 *)
definition empty :: "('a, 'b::linorder) pri_queue" where 
  "empty \<equiv> Abs_pq []"

(* 定义出入队列操作 *)
(* 将值为 k，优先级为 p 的元素加入优先队列 q *)
definition push :: "'a \<Rightarrow> 'b::linorder \<Rightarrow> ('a, 'b) pri_queue \<Rightarrow> ('a, 'b) pri_queue" where
  "push k p q \<equiv> Abs_pq (if k \<notin> set (values q)
                             then insort_key snd (k, p) (alist_of q)
                             else alist_of q)"

(* 删除优先级最小的元素 *)
(* tl 是提取一个列表去除开头元素后的子列表操作，不是取末尾元素 *)
definition remove_min :: "('a, 'b::linorder) pri_queue \<Rightarrow> ('a, 'b::linorder) pri_queue" where
"remove_min q \<equiv> (if is_empty q then empty 
else Abs_pq (tl (alist_of q)))"

definition pop :: "('a, 'b::linorder) pri_queue \<Rightarrow> ('a \<times> ('a, 'b) pri_queue) option" where
"pop q = (if is_empty q then None 
else Some (min q, remove_min q))"

thm set_insort_key

(* 辅助引理：证明在一个键互不相同的列表中插入一个新键（该键原先不在列表中），结果列表的键仍然互不相同 *)
lemma distinct_map_fst_insort: 
  "distinct (map fst xs) \<Longrightarrow> k \<notin> set (map fst xs) \<Longrightarrow> distinct (map fst (insort_key snd (k, p) xs))"
  apply (induction xs) 
  by (auto simp: set_insort_key)

(* 辅助引理：证明当元素 k 不在优先队列 q 中时，push 操作后的底层列表等于在原底层列表中按优先级插入 (k, p) *)
lemma alist_of_push_insert:
  assumes "k \<notin> set |q|"
  shows "alist_of (push k p q) = insort_key snd (k, p) (alist_of q)"
proof -
  let ?xs = "alist_of q"
  have inv: "?xs \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
    using alist_of by simp
  let ?ys = "insort_key snd (k, p) ?xs"
  have "sorted (map snd ?ys)" 
    using inv by (auto simp: sorted_insort_key)
  moreover have "distinct (map fst ?ys)"
    using inv assms unfolding values_def
    using distinct_map_fst_insort by blast
  ultimately have ys_inv: "?ys \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
    by simp
    
  have "k \<notin> set (values q)" using assms by simp
  then have "push k p q = Abs_pq ?ys"
    unfolding push_def by simp
    
  then have "alist_of (push k p q) = alist_of (Abs_pq ?ys)" by simp
  also have "... = ?ys"
    using ys_inv by (rule Abs_pq_inverse)
  finally show ?thesis .
qed

(* 证明 push 操作后，优先队列的元素集合等于原集合加上新元素 k *)
lemma alist_of_push: "set |push k p q| = set |q| \<union> {k}"
proof (cases "k \<in> set |q|")
  case True
  then have "push k p q = Abs_pq (alist_of q)"
    unfolding push_def values_def by simp
  then have "alist_of (push k p q) = alist_of (Abs_pq (alist_of q))" by simp
  also have "... = alist_of q"
    by (rule Abs_pq_inverse[OF alist_of])
  finally have "alist_of (push k p q) = alist_of q" .
  then show ?thesis using True unfolding values_def by auto
next
  case False
  then have "alist_of (push k p q) = insort_key snd (k, p) (alist_of q)"
    by (rule alist_of_push_insert)
  then show ?thesis using False unfolding values_def by (auto simp: set_insort_key)
qed

(* 辅助引理：证明在一个键互不相同的列表中插入 (k, v) 后，查找 k 得到的结果是 Some v *)
lemma map_of_insort_key:
  "k \<notin> set (map fst xs) \<Longrightarrow> map_of (insort_key f (k, v) xs) k = Some v"
  by (induction xs) auto

(* 证明如果 k 不在优先队列 q 中，那么 push k p q 后，k 的优先级为 p *)
lemma "k \<notin> set |q| \<Longrightarrow> priority (push k p q) k = Some p"
  unfolding priority_def
  by (simp add: alist_of_push_insert map_of_insort_key values_def)

(* 证明如果 k 已经在优先队列 q 中，那么 push k p q 操作不会改变 k 的优先级（即操作无效） *)
lemma priority_push_duplicate: "k ∈ set |q| ⟹ priority (push k p q) k = priority q k"
  unfolding push_def values_def
  by (simp add: alist_of_inverse)

lemma alist_of_eqI: "alist_of q1 = alist_of q2 \<Longrightarrow> q1 = q2"
  by (metis alist_of_inverse)

(* 证明 push 操作的可交换性：如果两个元素的键不同，那么插入顺序不影响最终结果 *)
lemma push_commute:
  assumes "v ≠ w" "a ≠ b"
  shows "push w b (push v a q) = push v a (push w b q)"
proof -
  have "alist_of (push w b (push v a q)) = alist_of (push v a (push w b q))"
  proof (cases "v ∈ set |q| ∨ w ∈ set |q|")
    case True
    then show ?thesis
    proof (cases "v ∈ set |q| ∧ w ∈ set |q|")
      case True
      then show ?thesis
        unfolding push_def values_def
        by (simp add: alist_of_inverse)
    next
      case False
      then show ?thesis
      proof (cases "v ∈ set |q|")
        case True
        with False have "w ∉ set |q|" by simp
        then have "push w b (push v a q) = push w b q"
          using True priority_push_duplicate unfolding push_def values_def
          by (metis alist_of_inverse alist_of_push insert_iff push_def values_def)
        moreover have "push v a (push w b q) = push w b q"
          using True `w ∉ set |q|`
          by (metis alist_of_push insert_iff priority_push_duplicate push_def values_def)
        ultimately show ?thesis by simp
      next
        case False
        with True have "w ∈ set |q|" by simp
        with False have "v ∉ set |q|" by simp
        (* Symmetric case *)
        then have "push v a (push w b q) = push v a q"
          using `w ∈ set |q|` priority_push_duplicate unfolding push_def values_def
          by (metis alist_of_inverse alist_of_push insert_iff push_def values_def)
        moreover have "push w b (push v a q) = push v a q"
          using `w ∈ set |q|` `v ∉ set |q|`
          by (metis alist_of_push insert_iff priority_push_duplicate push_def values_def)
        ultimately show ?thesis by simp
      qed
    qed
  next
    case False
    then have "v ∉ set |q|" and "w ∉ set |q|" by auto
    
    have eq1: "alist_of (push v a q) = insort_key snd (v, a) (alist_of q)"
      using alist_of_push_insert[OF `v ∉ set |q|`] by simp
    have eq2: "alist_of (push w b q) = insort_key snd (w, b) (alist_of q)"
      using alist_of_push_insert[OF `w ∉ set |q|`] by simp
    
    have "set |push v a q| = set |q| ∪ {v}" by (simp add: alist_of_push)
    then have "w ∉ set |push v a q|" 
      using `w ∉ set |q|` assms by auto
    then have left: "alist_of (push w b (push v a q)) = insort_key snd (w, b) (insort_key snd (v, a) (alist_of q))"
      using alist_of_push_insert eq1 by simp
      
    have "set |push w b q| = set |q| ∪ {w}" by (simp add: alist_of_push)
    then have "v ∉ set |push w b q|"
      using `v ∉ set |q|` assms by auto
    then have right: "alist_of (push v a (push w b q)) = insort_key snd (v, a) (insort_key snd (w, b) (alist_of q))"
      using alist_of_push_insert eq2 by simp
      
    show ?thesis
      unfolding left right
      apply (rule insort_key_left_comm)
      using assms by simp
  qed
  then show ?thesis by (rule alist_of_eqI)
qed

(* 证明：如果 pop 返回 Some (v,q1)，那么返回的值就是队列的最小元素 *)
lemma pop_to_min: "pop q = Some (v, q1) ⟹ v = min q"
  by (simp add: pop_def)

(* 证明：pop 返回 Some (v,q1) 时，v 不在剩余队列 q1 的元素集合中 *)
lemma pop_fresh: "pop q = Some (v, q1) ⟹ v ∉ set |q1|"
proof -
  assume H: "pop q = Some (v, q1)"
  hence "(min q, remove_min q) = (v, q1)"
    by (simp add: pop_def)
  hence Eqv: "v = min q" and Eqq: "q1 = remove_min q"
    by simp_all

  (* alist_of q 必为非空列表，记作 a # xs *)
  have "alist_of q ≠ []"
    using H by (simp add: pop_def)
  then obtain a xs where L: "alist_of q = a # xs"
    by (cases "alist_of q") auto

  (* v = fst a，由 min 的定义 *)
  have "v = fst a"
    using Eqv L unfolding min_def by (simp add: hd_conv_nth)

  (* q1 = Abs_pq xs，由 remove_min 的定义 *)
  have "q1 = Abs_pq xs"
    using Eqq L unfolding remove_min_def is_empty_def by simp

  (* 从类型不变性可得 distinct (map fst (a # xs))，因此 fst a 不在 map fst xs 中 *)
  have "distinct (map fst (a # xs))"
    using alist_of[of q] L by simp
  hence "fst a ∉ set (map fst xs)"
    by (simp add: distinct_conv_nth)

  (* 因此 v 不在 q1 的 values 中，完成证明 *)
  have "distinct (map fst xs) ∧ sorted (map snd xs)"
    using `distinct (map fst (a # xs))` alist_of[of q] L by (auto simp: sorted_Cons)
  then have "alist_of (Abs_pq xs) = xs"
    by (rule Abs_pq_inverse)

  have "v ∉ set (values (Abs_pq xs))"
    using `v = fst a` `fst a ∉ set (map fst xs)` `alist_of (Abs_pq xs) = xs` unfolding values_def by simp
    
  then show ?thesis
    using `q1 = Abs_pq xs` by simp
qed

end