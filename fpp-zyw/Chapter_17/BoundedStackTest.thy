theory BoundedStackTest
  imports Main
begin

typedef (overloaded) 'a bstack = 
  "{xs :: ('a list \<times> nat). length (fst xs) \<le> snd xs}"
  morphisms alist_of Abs_bstack
(* overloaded 参数，允许 bstack 这个新类型参与类型类机制，可以重载已有操作 *)
(* 使用集合的语言构造了 bstack 这个新类型，bstack 元素有两个参数分别为 list 和 nat 类型，且 list 长度小于 nat *)
(* morphism 态射 *)
(* 1. alist_of — 析构函数 (Rep function)
  alist_of :: 'a bstack \<Rightarrow> ('a list \<times> nat)
  - 从抽象到具体
  - 将 bstack 类型"拆开"，得到底层的 ('a list \<times> nat)
  - 类似于"解包"、"表示函数" (Representation)

  2. Abs_bstack — 构造函数 (Abs function)
  Abs_bstack :: ('a list \<times> nat) \<Rightarrow> 'a bstack
  - 从具体到抽象
  - 将满足条件的 ('a list \<times> nat) "包装"成 bstack
  - 类似于"封装"、"抽象函数" (Abstraction) *)

(* Isabelle 要求证明新类型的集合是非空的（non-empty） *)
proof -
(* proof - 手动证明的开始，不使用自动化工具 *)
  have "([],0) \<in> {xs. length (fst xs) \<le> snd xs}" by simp
  then show ?thesis by blast
  (* | shows | 声明要证明的结论 | lemma/theorem 声明时 |
     | show  | 证明当前子目标   | proof 内部          | *)
   (* 且 then show 可以简写为 thus *)
qed

(* 定义有限栈容量 *)
definition capacity :: "'a bstack \<Rightarrow> nat"
where "capacity s \<equiv> snd (alist_of s)"

(* 定义栈当前大小 *)
definition size :: "'a bstack \<Rightarrow> nat"
where "size s \<equiv> length (fst (alist_of s))"

(* 定义栈是否已满 *)
definition isfull :: "'a bstack \<Rightarrow> bool"
where "isfull s \<equiv> size s = capacity s"

(* 定义栈是否为空 *)
definition isempty :: "'a bstack \<Rightarrow> bool"
where "isempty s \<equiv> fst (alist_of s) = []"

(* 证明栈的大小不超过其容量 *)
lemma bstack_valid: "size s \<le> capacity s"
  apply(simp add:capacity_def size_def)
  using alist_of by blast

(* 定义 push 操作 *)
definition push :: "'a \<Rightarrow> 'a bstack \<Rightarrow> 'a bstack"
where "push v s \<equiv> 
(if \<not>isfull s then 
       Abs_bstack (v # fst (alist_of s), snd (alist_of s)) 
    else s)"

(* 定义 pop 操作 *)
definition pop :: "'a bstack \<Rightarrow> ('a option \<times> 'a bstack)"
where "pop s \<equiv> 
(if \<not> isempty s then 
      (Some (hd (fst (alist_of s))), Abs_bstack (tl (fst (alist_of s)), snd (alist_of s))) 
  else (None, s))"

(* 定义 top 操作 *)
definition top :: "'a bstack \<Rightarrow> 'a option"
where "top s \<equiv> (if \<not> isempty s then 
                       (Some (hd (fst (alist_of s)))) 
                    else None)"

(* | 变量     | 含义             |
   |---------|---------------------|
   | ?thesis | 当前要证明的目标       |
   | ?case   | 在归纳/分类讨论中的当前情况 |
   | ?goal   | 当前子目标（少用）      | *)

(* 有界栈的正确性 *)
lemma "\<not> isfull s \<Longrightarrow> top (push v s) = Some v"
  apply(simp add:push_def top_def isfull_def isempty_def size_def capacity_def)
  by (metis bstack_valid alist_of)


