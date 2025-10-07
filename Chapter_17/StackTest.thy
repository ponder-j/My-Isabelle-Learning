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
(* 注意 Isabelle 中一个等号 = 就表示“判断两者是否相等”，而不需要两个等号 == *)

(* 栈的正确性 *)

lemma "pop (push v s) = (v, s)" (* 隐式量化 *)
  by (simp add: push_def)
(* by simp                    使用默认的化简规则集 *)
(* by (simp add: thm1 thm2)   添加额外的化简规则 *)
(* by (simp del: thm1)        删除某些默认规则 *)
(* by (simp only: thm1 thm2)  只使用指定的规则 *)

lemma "∀v s. pop (push v s) = (v, s)" (* 显式量化 *)
  by (simp add: push_def)

lemma "top (push v s) = v"
  apply (induct s)
  by (simp add: push_def top_def)+
(* + 号表示对所有子目标都应用 proof 方法 *)

lemma "¬ emp s ⟹ top s = fst (pop s)"
  apply (induct s)
  by (simp add: emp_def top_def)+

lemma "¬ emp s ⟹ (v, s0) = pop s ⟹ push v s0 = s"
  apply (simp add: emp_def push_def)
  apply (induct s)
  by auto


end