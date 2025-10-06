theory StructuredProof
imports Main
begin

inductive even_ind :: ‹nat ⇒ bool› where
  even_0: ‹even_ind 0› | 
  even_SS: ‹even_ind n ⟹ even_ind (Suc (Suc n))›

thm even_0 even_SS
thm even_ind.induct

(* 语法 proof [method]
   作用 应用初始证明方法 method，并进入结构化证明状态。若 method 未给出，将根据目标命题的形式自动选择初始证明方法。也可使用"-"（连字符）作为初始证明方法。"-"可理解为不使用任何证明方法的"空操作"。 *)
theorem ‹even_ind n = even n›
proof
    (* ═══════════════════════════════════════════════════════════════
       结构化证明命令说明：
       ═══════════════════════════════════════════════════════════════

       【assume】引入假设
       - 语法: assume ‹P›
       - 作用: 在当前证明上下文中引入假设 P，用于证明蕴含命题 P ⟹ Q
       - 本例: assume ‹even_ind n› 假设 even_ind n 成立

       【show】证明目标
       - 语法: show ‹Q› proof
       - 作用: 证明当前需要证明的目标 Q
       - 本例: show ‹even n› 需要证明 even n

       【have】中间引理
       - 语法: have ‹P› proof
       - 作用: 证明一个中间引理 P，该引理会被添加到当前上下文中供后续使用
       - 与 show 的区别: show 证明的是当前的目标，have 证明的是辅助性的中间结果

       【obtain】存在性实例化
       - 语法: obtain x where ‹P(x)› proof
       - 作用: 从存在量词 ∃x. P(x) 中提取出具体的 x，并引入性质 P(x)
       - 本例: 从 ∃k. n = k + k 中提取出具体的 k

       【using】引用事实
       - 语法: ... using fact1 fact2 by method
       - 作用: 在证明中引用已知的事实、假设或前面证明的引理
       - 本例: using k 引用了前面 obtain 得到的等式 n = k + k

       ═══════════════════════════════════════════════════════════════
       证明方法说明：
       ═══════════════════════════════════════════════════════════════

       【presburger】Presburger 算术求解器
       - 用途: 解决线性整数算术问题（加法、减法、常数倍乘）
       - 能力: 能处理含有 ∃ ∀ 的线性算术公式
       - 本例: 从 even n 推导出 ∃k. n = k + k

       【blast】表式搜索证明器
       - 用途: 快速的一阶逻辑推理，适合纯逻辑推理
       - 能力: 处理 ∧ ∨ ⟹ ¬ ∀ ∃ 等逻辑连接词，使用表式方法
       - 本例: 从 ∃k. n = k + k 中提取出 k（实例化存在量词）

       【auto】自动证明
       - 用途: 结合化简和经典推理的通用自动证明器
       - 能力: 自动应用化简规则、拆分目标、进行推理
       - intro: 参数，指定额外的引入规则
       - 本例: auto intro: even_ind.intros 使用 even_ind 的构造规则
       ═══════════════════════════════════════════════════════════════ *)

    (* ────── 方向一: even_ind n ⟹ even n ────── *)
    assume ‹even_ind n›
    (* ↑ 假设 even_ind n 成立 *)

    then show ‹even n›
    (* ↑ 需要证明 even n，使用归纳法和自动证明 *)
    by (induct, auto)

next
    (* ────── 方向二: even n ⟹ even_ind n ────── *)
    assume ‹even n›
    (* ↑ 假设 even n 成立 *)

    then have ‹∃k. n = k + k› by presburger
    (* ↑ 中间引理: 从 even n 推出存在 k 使得 n = k + k
         证明方法: presburger 自动处理这个算术推理 *)

    then obtain k where k: ‹n = k + k› by blast
    (* ↑ 存在性实例化: 从 ∃k. n = k + k 中提取具体的 k
         同时引入命名事实 k: n = k + k 供后续使用
         证明方法: blast 处理存在量词的实例化 *)

    have ‹even_ind (k + k)› by (induct k) (auto intro: even_ind.intros)
    (* ↑ 中间引理: 对任意 k，都有 even_ind (k + k)
         证明方法: 对 k 归纳
           - 基础步骤: k = 0，auto 使用 even_0 规则
           - 归纳步骤: auto 使用 even_SS 规则和归纳假设
         intro: even_ind.intros 提供 even_0 和 even_SS 两个构造规则 *)

    then show ‹even_ind n› using k by simp
    (* ↑ 证明最终目标 even_ind n
         using k 引用前面的等式 n = k + k
         由 even_ind (k + k) 和 n = k + k，用 simp 化简得到 even_ind n *)
qed

end