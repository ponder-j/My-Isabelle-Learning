theory IMP_Demo
  imports Main
begin

section \<open>1. 基础定义 (语法与状态)\<close>

text \<open>为了演示，我们定义一个最简化的 IMP 语言。\<close>

― \<open>类型别名：变量名是字符串，值是整数，状态是变量到值的映射\<close>
type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

― \<open>算术表达式 (AExp)\<close>
datatype aexp = N val | V vname | Plus aexp aexp

― \<open>布尔表达式 (BExp)\<close>
datatype bexp = Bc bool | Not bexp | Less aexp aexp

― \<open>指令 (Command) - 核心语法\<close>
datatype com =
  SKIP 
| Assign vname aexp       ("(_ ::= _)" [1000, 61] 61)
| Seq    com  com         ("(_;;/ _)"  [60, 61] 60)
| If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
| While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)

― \<open>辅助函数：计算表达式的值 (这部分通常都是大步的/函数式的)\<close>
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

section \<open>2. 大步语义 (Big-Step Semantics)\<close>

text \<open>
  大步语义关注的是：从 (Command, InitialState) 直接跳到 FinalState。
  符号：(c, s) \<Rightarrow> s' 表示 "命令 c 在状态 s 下执行，最终停止在状态 s'"
\<close>

inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
Skip:  "(SKIP, s) \<Rightarrow> s" |

Assign: "(x ::= a, s) \<Rightarrow> s(x := aval a s)" |

Seq:   "\<lbrakk> (c1, s1) \<Rightarrow> s2; (c2, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1;; c2, s1) \<Rightarrow> s3" |

IfTrue:  "\<lbrakk> bval b s; (c1, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s; (c2, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t" |

― \<open>While 的定义是递归的：如果条件成立，执行一次 body，然后从新状态继续 While\<close>
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk> bval b s1; (c, s1) \<Rightarrow> s2; (WHILE b DO c, s2) \<Rightarrow> s3 \<rbrakk> 
             \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow> s3"

― \<open>示例证明：证明一段简单代码执行后的结果\<close>
lemma big_step_example:
  "let prog = (''x'' ::= N 5;; ''y'' ::= V ''x'') in
   (prog, s) \<Rightarrow> s(''x'' := 5, ''y'' := 5)"
  apply (unfold Let_def)
  apply (rule Seq)    ― \<open>将序列切分为两步\<close>
   apply (rule Assign) ― \<open>处理第一步 x := 5\<close>
  apply (rule Assign) ― \<open>处理第二步 y := x (此时 x 已经是 5 了)\<close>
  done

section \<open>3. 小步语义 (Small-Step Semantics)\<close>

text \<open>
  小步语义关注的是：(Command, State) 如何变成 (RestCommand, NextState)。
  符号：(c, s) \<rightarrow> (c', s')
  注意：为了处理终止，我们通常认为 SKIP 是“空指令”，或者引入一个特殊状态。
  这里我们使用 Concrete Semantics 书中的风格：只是单纯的重写规则。
\<close>

inductive small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
― \<open>赋值：执行完变成了 SKIP，状态更新\<close>
Assign: "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

― \<open>序列：如果前面还没做完，就只做前面的一步\<close>
Seq1:   "(c1, s) \<rightarrow> (c1', s') \<Longrightarrow> (c1;; c2, s) \<rightarrow> (c1';; c2, s')" |
― \<open>序列：如果前面做完了(SKIP)，就扔掉前面，开始做后面\<close>
Seq2:   "(SKIP;; c2, s) \<rightarrow> (c2, s)" |

― \<open>条件分支：一步归约为 c1 或 c2\<close>
IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<rightarrow> (c1, s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<rightarrow> (c2, s)" |

― \<open>While：一步展开为 IF。这是小步语义处理循环的经典方式\<close>
While:   "(WHILE b DO c, s) \<rightarrow> 
          (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"

― \<open>定义：多步执行 (Reflexive Transitive Closure)\<close>
abbreviation small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where
  "x \<rightarrow>* y \<equiv> small_step\<^sup>*\<^sup>* x y"

― \<open>示例证明：手动模拟一步一步的执行\<close>
lemma small_step_example:
  "( ''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<rightarrow>* (SKIP, s(''x'':=5, ''y'':=5))"
  apply (rule rtranclp_trans) ― \<open>我们要走多步，先走第一步\<close>
   apply (rule Seq1)          ― \<open>关注序列左边\<close>
   apply (rule Assign)        ― \<open>左边是赋值 x:=5，执行它\<close>
  apply (rule rtranclp_trans) ― \<open>继续走\<close>
   apply (rule Seq2)          ― \<open>左边变成 SKIP 了，扔掉它\<close>
  apply (rule rtranclp_trans) ― \<open>继续走\<close>
   apply (rule Assign)        ― \<open>现在剩下 y:=x，执行它\<close>
  apply simp                  ― \<open>化简状态更新\<close>
  done

end