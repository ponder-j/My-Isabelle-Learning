theory BasicProofExample
imports Main
begin

(* 语法 (theorem | lemma) [thm_name:] prop

作用 开始证明命题 prop。证明完的定理将被命名为 thm_name。

lemma命令的作用与 theorem 相同， 作用和语法完全相同的命令还有 proposition 和 corollary。 *)

theorem prop1: ‹(A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ A ⟶ C›
apply (rule impI)