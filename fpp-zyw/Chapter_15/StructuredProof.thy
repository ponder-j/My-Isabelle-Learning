theory StructuredProof
imports Main
begin

(* Example 1 *)
inductive even_ind :: ‹nat ⇒ bool› where
  even_0: ‹even_ind 0› | 
  even_SS: ‹even_ind n ⟹ even_ind (Suc (Suc n))›

thm even_0 even_SS
thm even_ind.induct

(* 语法 proof [method]
   作用 应用初始证明方法 method，并进入结构化证明状态。若 method 未给出，将根据目标命题的形式自动选择初始证明方法。也可使用"-"（连字符）作为初始证明方法。"-"可理解为不使用任何证明方法的"空操作"。 *)
theorem ‹even_ind n = even n›
(* "even n ⟷ (∃k. n = 2 * k)" *)
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
    (* then 表示在证明中使用刚才陈述的假设 *)
    then show ‹even n›
    (* ↑ 需要证明 even n，使用归纳法和自动证明 *)
    apply induct
    apply simp
    apply (auto intro: even_ind.intros)
    done
    (* ↑ 证明完成 *)

next
    (* ────── 方向二: even n ⟹ even_ind n ────── *)
    assume ‹even n›
    (* ↑ 假设 even n 成立 *)

    then have ‹∃k. n = k + k› by presburger
    (* ↑ 中间引理: 从 even n 推出存在 k 使得 n = k + k
         证明方法: presburger 自动处理这个算术推理 *)
    (* Presburger 算术是自然数带有加法的一阶理论 *)

    then obtain k where k_lemma: ‹n = k + k› by blast
    (* obtain 是 Isabelle 中用于存在量词实例化的结构化证明命令 *)
    (* obtain x where [label:] "P(x)" by method *)
     (* 1. obtain - 关键字
     2. 变量列表 - 要引入的新变量（可以是多个）
     3. where - 分隔符
     4. 性质 - 关于这些变量的命题
     5. 标签（可选）- 给性质命名以便后续引用
     6. 证明方法 - 证明存在性的方法 *)
    (* ↑ 存在性实例化: 从 ∃k. n = k + k 中提取具体的 k
         同时引入命名事实 k: n = k + k 供后续使用
         证明方法: blast 处理存在量词的实例化 *)

    have ‹even_ind (k + k)›
    apply (induct k)
    apply (auto intro: even_ind.intros)
    done
    (* ↑ 中间引理: 对任意 k，都有 even_ind (k + k)
         证明方法: 对 k 归纳
           - 基础步骤: k = 0，auto 使用 even_0 规则
           - 归纳步骤: auto 使用 even_SS 规则和归纳假设
         intro: even_ind.intros 提供 even_0 和 even_SS 两个构造规则 *)

    then show ‹even_ind n› using k_lemma by simp
    (* ↑ 证明最终目标 even_ind n
         using k_lemma 引用前面的等式 n = k + k
         由 even_ind (k + k) 和 n = k + k，用 simp 化简得到 even_ind n *)
qed

(* Example 2 *)
theorem
  fixes list :: ‹'a :: order list›
  (* fix 声明变量，'a :: order 表明 'a 必须支持排序操作 *)
  (* 一般情况不需要声明自由变量，但这里用到排序，必须先限定 'a 的类型 *)
  assumes assum: ‹∀i. Suc i < length list ⟶ list!i ≤ list!(Suc i)›
  shows ‹∀i j. j < length list ⟶ i ≤ j ⟶ list!i ≤ list!j›
proof clarify
(* clarify 用于整理命题，将全称量词引入为固定变量 *)
(* 整理后的目标：⋀i j. j < length list ⟹ i ≤ j ⟹ list ! i ≤ list ! j *)

  (* 步骤1: 引入任意的 i 和 j *)
  fix i j :: nat

  (* 步骤2: 假设前提条件 *)
  assume j_less: ‹j < length list›  (* j 在列表范围内 *)
  assume ‹i ≤ j›                     (* i 不大于 j *)

  (* 步骤3: 将 i ≤ j 转化为存在性形式 i + k = j *)
  (* 利用引理 le_Suc_ex: "m ≤ n ⟹ ∃k. n = m + k" *)
  (* 这样可以对距离 k 进行归纳 *)
  then obtain k where k_rule: ‹i + k = j› using le_Suc_ex by blast

  (* from 用于在证明中使用指定的已知事实作为前提，与 using 作用相似 *)
  (* from ... have P using ... by ... *)
  (* from 的内容可以放 using 后面，using 的内容可以放 from 后面 *)
  (* then = from this, this 代指上一个证明或假设的命题 *)
  (* with ... = from ... this *)
  (* hence = then have *)
  (* thus = then show *)

  (* 步骤4: 证明核心引理 list!i ≤ list!(i+k) *)
  (* 策略：对距离 k 进行归纳 *)
  from k_rule j_less have ‹list!i ≤ list!(i+k)›
  proof (induct k arbitrary: j)
    (* 基础情况: k = 0 *)
    (* 需要证明 list!i ≤ list!(i+0)，即 list!i ≤ list!i *)
    (* 这是显然成立的反身性 *)
    show ‹list!i ≤ list!(i+0)› by simp
  next
    (* 归纳步骤: 假设对 k' 成立，证明对 Suc k' 也成立 *)
    fix k' j

    (* 归纳假设：对于距离 k'，性质成立 *)
    assume IH: ‹⋀j. i + k' = j ⟹ j < length list ⟹ list!i ≤ list!(i+k')›

    (* 当前情况的假设 *)
    assume a1: ‹i + Suc k' = j›      (* 当前距离为 k'+1 *)
    assume a2: ‹j < length list›      (* j 在列表范围内 *)

    (* 步骤4.1: 推导 i+k' 也在列表范围内 *)
    from a1 a2 have *: ‹Suc (i + k') < length list› by simp

    (* 步骤4.2: 利用归纳假设得到 list!i ≤ list!(i+k') *)
    with IH have ‹list!i ≤ list!(i+k')› by simp

    (* 步骤4.3: 利用 assum（列表的相邻单调性）得到 list!(i+k') ≤ list!(i+k'+1) *)
    (* assum 的原始形式：∀i. Suc i < length list ⟶ list!i ≤ list!(Suc i) *)
    (* 问题：assum 包含 ∀ 和 ⟶，不是标准的 Isabelle 规则形式 *)
    (* 解决方案：使用定理修饰符进行转换 *)
    (*   [rule_format]: 将定理改写成标准规则形式 *)
    (*                  ∀i. P ⟶ Q  转换为  ⋀i. P ⟹ Q *)
    (*   [OF *]: 将事实 * (即 Suc (i + k') < length list) 作为前提传入 *)
    (*            实例化全称量词并满足前提条件 *)
    (* 转换过程：*)
    (*   原始: ∀i. Suc i < length list ⟶ list!i ≤ list!(Suc i) *)
    (*   rule_format 后: ⋀i. Suc i < length list ⟹ list!i ≤ list!(Suc i) *)
    (*   OF * 后: list!(i+k') ≤ list!Suc(i+k')  (其中 i 被实例化为 i+k') *)
    also from assum[rule_format, OF *] have ‹list!(i+k') ≤ list!Suc(i+k')›.

    (* 步骤4.4: 通过传递性得到 list!i ≤ list!(i+k'+1) *)
    (* finally 自动应用传递性：从 list!i ≤ list!(i+k') 和 list!(i+k') ≤ list!Suc(i+k') *)
    (* 得出 list!i ≤ list!Suc(i+k')，即 list!i ≤ list!(i + Suc k') *)
    finally show ‹list!i ≤ list!(i + Suc k')› by simp
  qed

  (* 步骤5: 将 i+k 替换回 j，完成最终证明 *)
  (* 现在我们有 list!i ≤ list!(i+k) 且 i+k = j *)
  (* 因此 list!i ≤ list!j *)
  with k_rule show ‹list!i ≤ list!j› by simp
qed
(* 15.5 Isar 证明特殊结构 *)
(* also-finally *)
(* moreover-ultimately *)

(* ═══════════════════════════════════════════════════════════════
   定理修饰符详解
   ═══════════════════════════════════════════════════════════════ *)

(* 【rule_format】将定理改写成标准规则形式

   为什么需要 rule_format？
   - Isabelle 的规则推理使用 ⋀ 和 ⟹
   - 但我们常用 ∀ 和 ⟶ 来陈述定理
   - rule_format 将后者转换为前者

   转换规则：
   - ∀x. P     →  ⋀x. P
   - P ⟶ Q    →  P ⟹ Q
   - P ∧ Q ⟶ R →  P ⟹ Q ⟹ R

   示例：
   定理: ∀i. Suc i < length list ⟶ list!i ≤ list!(Suc i)
   rule_format 后: ⋀i. Suc i < length list ⟹ list!i ≤ list!(Suc i)
*)

(* 【OF】给出定理的前提

   语法: theorem [OF fact1 fact2 ...]
   作用: 用给定的事实满足定理的前提，进行前向推理

   示例：
   假设定理 T: ⋀i. P i ⟹ Q i ⟹ R i
   假设事实 f1: P 3
   假设事实 f2: Q 3
   则 T[OF f1 f2] 得到: R 3

   本例中：
   assum[rule_format]: ⋀i. Suc i < length list ⟹ list!i ≤ list!(Suc i)
   事实 *: Suc (i + k') < length list
   assum[rule_format, OF *]: list!(i+k') ≤ list!Suc(i+k')
*)

(* 【of】给出定理中形式变量的取值

   语法: theorem [of t1 t2 ...]
   作用: 实例化定理中的全称量词

   示例：
   定理 T: ⋀x y. P x y
   T[of 1 2] 得到: P 1 2

   区别：
   - of: 手动指定变量的值（显式实例化）
   - OF: 通过前提自动推导（隐式实例化）
*)

(* 【symmetric】交换等式两边

   示例：
   等式 e: a = b
   e[symmetric]: b = a
*)

(* ═══════════════════════════════════════════════════════════════
   为什么不能直接用 assum？
   ═══════════════════════════════════════════════════════════════

   错误示例：from assum have ...

   问题分析：
   1. assum 的形式是: ∀i. Suc i < length list ⟶ list!i ≤ list!(Suc i)
   2. 这不是一个可以直接用于推理的规则
   3. 我们需要：
      a) 将 ∀ 转换为 ⋀（rule_format）
      b) 实例化变量 i 为具体的 i+k'
      c) 满足前提 Suc (i+k') < length list（OF *）

   正确做法：assum[rule_format, OF *]

   完整转换过程：
   assum:                ∀i. Suc i < length list ⟶ list!i ≤ list!(Suc i)
   assum[rule_format]:   ⋀i. Suc i < length list ⟹ list!i ≤ list!(Suc i)
   assum[rule_format, OF *]:  list!(i+k') ≤ list!Suc(i+k')
                              (i 被实例化为 i+k'，前提被事实 * 满足)
   ═══════════════════════════════════════════════════════════════ *)
end