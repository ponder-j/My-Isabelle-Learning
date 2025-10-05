theory AutoProof
  imports Main
begin

(* 方法	功能描述
自动化证明
iprover	直觉主义证明搜索
blast/fast	经典推理器（快速 / 深度优先）
simp/simp_all	简化器（处理等式 / 条件）
auto/force	简化器 + 经典推理（批量 / 专注）
arith	算术证明过程
半自动化证明
clarify 等价变换（不拆分目标命题）
clarsimp clarify + simp
try/try0 尝试自动证明
 *)
theorem peirce1: ‹((P ⟶ Q) ⟶ P) ⟶ P›
by blast

theorem peirce2: ‹((P ⟶ Q) ⟶ P) ⟶ P›
by fast

theorem peirce3: ‹((P ⟶ Q) ⟶ P) ⟶ P›
by force

end