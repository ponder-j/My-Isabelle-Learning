theory BasicProofExercise
imports Main
begin

(* 基础证明练习题 
   这些练习题旨在帮助练习基本的逻辑推理规则，包括：
   - impI (蕴含引入)
   - mp (肯定前件)
   - assumption (假设)
   - subgoal_tac (子目标策略)
*)

(* 练习1：简单的传递性 
   提示：这比原题简单一些，用于热身 *)
theorem exercise1: ‹(A ⟶ B) ⟶ (B ⟶ C) ⟶ A ⟶ C›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (erule mp)
apply (erule mp)
apply assumption
done


(* 练习2：组合子 K (常函数)
   提示：这需要忽略第二个参数 *)
theorem exercise2: ‹A ⟶ B ⟶ A›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply assumption
done

(* 练习3：组合子 S 的简化版
   提示：类似原例题，但结构稍有不同 *)
theorem exercise3: ‹(A ⟶ B ⟶ C) ⟶ (A ⟶ B) ⟶ (A ⟶ C)›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (subgoal_tac ‹B ⟶ C›)
apply (erule mp)
apply (erule mp)
apply assumption
apply (erule mp)
apply assumption
done


(* 练习4：双重应用
   提示：需要两次应用 mp 规则 *)
theorem exercise4: ‹(A ⟶ B ⟶ C ⟶ D) ⟶ (A ⟶ B) ⟶ (A ⟶ C) ⟶ A ⟶ D›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (subgoal_tac ‹B ⟶ C ⟶ D›)
apply (subgoal_tac ‹C ⟶ D›)
apply (erule mp)
apply (erule mp)
apply assumption
apply (erule mp)
apply (erule mp)
apply assumption
apply (erule mp)
apply assumption
done

(* 练习5：嵌套蕴含
   提示：小心处理嵌套的蕴含结构 *)
theorem exercise5: ‹A ⟶ (B ⟶ C) ⟶ B ⟶ A ⟶ C›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (erule mp)
apply assumption
done


(* 练习6：自应用
   提示：一个参数同时作为函数和参数使用 *)
theorem exercise6: ‹(A ⟶ A ⟶ B) ⟶ A ⟶ B›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply (subgoal_tac ‹A ⟶ B›)
apply (erule mp)
apply assumption
apply (erule mp)
apply assumption
done


(* 练习7：组合运算
   提示：这是一个稍微复杂的组合子，需要仔细安排证明步骤 *)
theorem exercise7: ‹(A ⟶ B ⟶ C) ⟶ B ⟶ A ⟶ C›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (subgoal_tac ‹B ⟶ C›)
apply (erule mp)
apply assumption
apply (erule mp)
apply assumption
done


(* 练习8：挑战题 - 四元组合子
   提示：这是最难的一个，需要多个 subgoal_tac 和仔细的规划 *)
theorem exercise8: ‹(A ⟶ B ⟶ C ⟶ D) ⟶ (A ⟶ B) ⟶ (A ⟶ C) ⟶ (A ⟶ D)›
(* TODO: 完成证明 *)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (rule impI)
apply (subgoal_tac ‹B ⟶ C ⟶ D›)
apply (subgoal_tac ‹C ⟶ D›)
apply (erule mp)
apply (erule mp)
apply assumption
apply (erule mp)
apply (erule mp)
apply assumption
apply (erule mp)
apply assumption
done

(*
证明技巧提醒：

1. impI 规则：用于引入蕴含 (⟶)
   - 将 P ⟶ Q 转换为假设 P 下证明 Q

2. mp 规则：肯定前件 ⟦P ⟶ Q; P⟧ ⟹ Q
   - 当你有 P ⟶ Q 和 P 时，可以得出 Q

3. erule mp：消除规则版本的 mp
   - 自动从假设中寻找匹配的蕴含式

4. assumption：使用假设
   - 当目标恰好是某个假设时使用

5. subgoal_tac：引入子目标
   - 当你需要一个中间结论来帮助证明时使用
   - 格式：subgoal_tac ‹中间命题›

6. 证明策略：
   - 通常从外层蕴含开始，用 impI 逐层引入假设
   - 识别需要的中间结论，用 subgoal_tac 引入
   - 使用 mp 规则来应用蕴含式
   - 最后用 assumption 完成简单的目标

开始做题吧！记住，如果卡住了，可以参考 BasicProofExample.thy 中的解题思路。
*)

end