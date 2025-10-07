theory BoundedStackTest
  imports Main
begin

typedef (overloaded) 'a bstack = 
  "{xs :: ('a list × nat). length (fst xs) ≤ snd xs}"
  morphisms alist_of Abs_bstack
(* overloaded 参数，允许 bstack 这个新类型参与类型类机制，可以重载已有操作 *)
(* 使用集合的语言构造了 bstack 这个新类型，bstack 元素有两个参数分别为 list 和 nat 类型，且 list 长度小于 nat *)
(* morphism 态射 *)
(* 1. alist_of — 析构函数 (Rep function)
  alist_of :: 'a bstack ⇒ ('a list × nat)
  - 从抽象到具体
  - 将 bstack 类型"拆开"，得到底层的 ('a list × nat)
  - 类似于"解包"、"表示函数" (Representation)

  2. Abs_bstack — 构造函数 (Abs function)
  Abs_bstack :: ('a list × nat) ⇒ 'a bstack
  - 从具体到抽象
  - 将满足条件的 ('a list × nat) "包装"成 bstack
  - 类似于"封装"、"抽象函数" (Abstraction) *)

proof -
(* proof - 手动证明的开始，不使用自动化工具 *)
  have "([],0) ∈ {xs. length (fst xs) ≤ snd xs}" by simp
  then show ?thesis by blast
  (* | shows | 声明要证明的结论 | lemma/theorem 声明时 |
     | show  | 证明当前子目标   | proof 内部          | *)
   (* 且 then show 可以简写为 thus *)
qed

(* 定义有限栈容量 *)
definition capacity :: "'a bstack ⇒ nat"
where "capacity s ≡ snd (alist_of s)"

(* 定义栈当前大小 *)
definition size :: "'a bstack ⇒ nat"
where "size s ≡ length (fst (alist_of s))"

(* 定义栈是否已满 *)
definition isfull :: "'a bstack ⇒ bool"
where "isfull s ≡ size s = capacity s"

(* 定义栈是否为空 *)
definition isempty :: "'a bstack ⇒ bool"
where "isempty s ≡ fst (alist_of s) = []"

(* 证明栈的大小不超过其容量 *)
lemma bstack_valid: "size s ≤ capacity s"
  apply(simp add:capacity_def size_def)
  using alist_of by blast

(* 定义 push 操作 *)
definition push :: "'a ⇒ 'a bstack ⇒ 'a bstack"
where "push v s ≡ 
(if ¬isfull s then 
       Abs_bstack (v # fst (alist_of s), snd (alist_of s)) 
    else s)"

(* 定义 pop 操作 *)
definition pop :: "'a bstack ⇒ ('a option × 'a bstack)"
where "pop s ≡ 
(if ¬ isempty s then 
      (Some (hd (fst (alist_of s))), Abs_bstack (tl (fst (alist_of s)), snd (alist_of s))) 
  else (None, s))"

(* 定义 top 操作 *)
definition top :: "'a bstack ⇒ 'a option"
where "top s ≡ (if ¬ isempty s then 
                       (Some (hd (fst (alist_of s)))) 
                    else None)"

(* | 变量     | 含义             |
   |---------|---------------------|
   | ?thesis | 当前要证明的目标       |
   | ?case   | 在归纳/分类讨论中的当前情况 |
   | ?goal   | 当前子目标（少用）      | *)

(* 有界栈的正确性 *)
lemma "¬ isfull s ⟹ top (push v s) = Some v"
  apply(simp add:push_def top_def isfull_def isempty_def size_def capacity_def)
  by (metis bstack_valid alist_of)


