theory FIFOQueue
  imports Main
begin

type_synonym 'a queue = "'a list"

fun enqueue :: "'a queue \<Rightarrow> 'a \<Rightarrow> 'a queue" 
where "enqueue xs x = x # xs"

fun dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue)" 
where "dequeue xs = (last xs, butlast xs)"

definition queue1 :: "nat queue" where
  "queue1 ≡ [1, 2, 3, 4]"

value "snd (dequeue queue1)"

definition queue2 :: "nat queue" where
  "queue2 ≡ []"

definition isempty :: "'a queue \<Rightarrow> bool" 
where "isempty q \<equiv> (q = [])"

value "isempty queue1"
value "isempty queue2"

abbreviation "emptyq \<equiv> []"

(* 将整个 list 中的元素一一入队，得到一个 queue *)
fun listenq :: "'a queue ⇒ 'a list ⇒ 'a queue" where
  "listenq q [] = q" |
  "listenq q (x # xs) = listenq (enqueue q x) xs"

(* 将整个 queue 中的元素一一出队，得到一个 list *)
fun deq2list :: "'a queue ⇒ 'a list ⇒ 'a list" where
  "deq2list [] lst = lst" |
  "deq2list q lst = (let (x, xq) = dequeue(q) in 
                           (deq2list xq (x # lst)))"

(* list_enqueue 即从列表中读入到一个队列 *)
(* dequeue_list 即从队列中弹出一个列表 *)
definition "list_enqueue l ≡ listenq [] l"
definition "dequeue_list q ≡ deq2list q []"

(* 在证明 theorem 之前应该先证两个小引理 *)
lemma listenq_rev: "listenq q xs = (rev xs) @ q"
  apply (induct xs arbitrary: q)
  apply simp
  by auto

lemma deq2list_ind: "deq2list q xs = q @ xs"
  apply (induct q arbitrary: xs)
  apply simp
  by auto

lemma queue_cor_prim : "deq2list (listenq [] xs) [] = rev xs"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (simp add: listenq_rev deq2list_ind)
qed

theorem queue_cor: "dequeue_list (list_enqueue xs) = rev xs"
proof -
  have expand: "dequeue_list (list_enqueue xs) = deq2list (listenq [] xs) []"
    by (simp add: dequeue_list_def list_enqueue_def)
  hence "deq2list (listenq [] xs) [] = rev xs"
    by (simp add: queue_cor_prim)
  hence "dequeue_list (list_enqueue xs) = rev xs" by (simp add: expand)
  then show ?thesis
    by auto
qed

end