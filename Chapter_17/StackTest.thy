theory StackTest
  imports Main
begin

type_synonym 'a stack = "'a list"

definition push :: "'a ⇒ 'a stack ⇒ 'a stack" where
  "push v s = v#s"

primrec pop :: "'a stack ⇒ ('a × 'a stack)" where
  "pop (x#xs) = (x, xs)"

definition top :: "'a stack ⇒ 'a" where
  "top s = hd s" (* head of the list *)

definition "emp s ≡ s = []"

(* 栈的正确性 *)

lemma "pop (push v s) = (v, s)"
  by (simp add: push_def)
(* by simp                    使用默认的化简规则集 *)
(* by (simp add: thm1 thm2)   添加额外的化简规则 *)
(* by (simp del: thm1)        删除某些默认规则 *)
(* by (simp only: thm1 thm2)  只使用指定的规则 *)

end