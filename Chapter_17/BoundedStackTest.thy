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
  have "([],0) ∈ {xs. length (fst xs) ≤ snd xs}" by simp
  then show ?thesis by blast
(* | shows | 声明要证明的结论 | lemma/theorem 声明时 |
   | show  | 证明当前子目标   | proof 内部          | *)

qed

definition capacity :: "'a bstack ⇒ nat"
where "capacity s ≡ snd (alist_of s)"

definition size :: "'a bstack ⇒ nat"
where "size s ≡ length (fst (alist_of s))"

definition isfull :: "'a bstack ⇒ bool"
where "isfull s ≡ size s = capacity s"

definition isempty :: "'a bstack ⇒ bool"
where "isempty s ≡ fst (alist_of s) = []"

lemma bstack_valid: "size s ≤ capacity s"
  apply(simp add:capacity_def size_def)
  using alist_of by blast