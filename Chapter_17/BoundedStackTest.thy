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