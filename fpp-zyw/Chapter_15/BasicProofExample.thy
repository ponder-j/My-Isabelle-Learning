theory BasicProofExample
imports Main
begin

(* 语法 (theorem | lemma) [thm_name:] prop

作用 开始证明命题 prop。证明完的定理将被命名为 thm_name。

lemma命令的作用与 theorem 相同， 作用和语法完全相同的命令还有 proposition 和 corollary。 *)

theorem prop1: ‹(A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶ C›
apply (rule impI)
(* 1. A ⟶ B ⟶ C ⟹ (A ⟶ B) ⟶ A ⟶ C *)
apply (rule impI)
(* 1. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟶ C *)
apply (rule impI)
(* 1. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟹ C *)
apply (subgoal_tac ‹B ⟶ C›)
(* 1. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟹ B ⟶ C ⟹ C
   2. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟹ B ⟶ C *)
(* 当你需要证明某个结论，而你有一个蕴含式能够导出这个结论时，你只需要证明蕴含式的前件即可。 *)
apply (erule mp) (* ⟦P ⟶ Q; P⟧ ⟹ Q *)
(* 1. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟹ B
   2. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟹ B ⟶ C *)
apply (erule mp)
(* 1. A ⟶ B ⟶ C ⟹ A ⟹ A
   2. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟹ B ⟶ C *)
(* 当目标命题的前提之一与结论相同时，直接完成证明。 *)
apply assumption
(* 1. A ⟶ B ⟶ C ⟹ A ⟶ B ⟹ A ⟹ B ⟶ C *)
apply (erule mp)
(* 1. A ⟶ B ⟹ A ⟹ A *)
apply assumption
done

thm prop1

end
