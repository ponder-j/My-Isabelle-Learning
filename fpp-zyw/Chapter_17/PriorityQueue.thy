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

(* 这个没看懂，map_of 和 map 有什么区别？为什么要搞两个函数 *)
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

lemma distinct_map_fst_insort: 
  "distinct (map fst xs) \<Longrightarrow> k \<notin> set (map fst xs) \<Longrightarrow> distinct (map fst (insort_key snd (k, p) xs))"
  by (induction xs) (auto simp: set_insort_key)

lemma alist_of_push: "set |push k p q| = set |q| \<union> {k}"
proof -
  let ?xs = "alist_of q"
  have inv: "?xs \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
    using alist_of by simp
  
  show ?thesis
  proof (cases "k \<in> set |q|")
    case True
    then have "k \<in> set (values q)" by simp
    then have "push k p q = Abs_pq ?xs"
      unfolding push_def by simp
    then have "alist_of (push k p q) = alist_of (Abs_pq ?xs)" by simp
    also have "... = ?xs"
      using inv by (rule Abs_pq_inverse)
    finally have "alist_of (push k p q) = ?xs" .
    then show ?thesis using True unfolding values_def by auto
  next
    case False
    let ?ys = "insort_key snd (k, p) ?xs"
    have "sorted (map snd ?ys)" 
      using inv by (auto simp: sorted_insort_key)
    moreover have "distinct (map fst ?ys)"
      using inv False unfolding values_def
      using distinct_map_fst_insort by blast
    ultimately have ys_inv: "?ys \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
      by simp
      
    have "k \<notin> set (values q)" using False by simp
    then have "push k p q = Abs_pq ?ys"
      unfolding push_def by simp
      
    then have "alist_of (push k p q) = alist_of (Abs_pq ?ys)" by simp
    also have "... = ?ys"
      using ys_inv by (rule Abs_pq_inverse)
    finally have "alist_of (push k p q) = ?ys" .
    
    then show ?thesis
      unfolding values_def
      by (simp add: set_insort_key)
  qed
qed



end