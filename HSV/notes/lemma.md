```isabelle
lemma multiple_assumptions_example:
  fixes x y :: nat
  (* 给假设起名为 major 和 minor *)
  assumes major: "x > 0"
  and     minor: "y > x"
  shows   "y > 0"
proof -
  from minor have "y > x" . 
  (* 下面这步利用了 major 和 minor 两个事实 *)
  from this and major show "y > 0" by simp
qed
```

### 2. 能不能合并成箭头形式？(短目标格式)

**完全可以！** 这就是所谓的“短目标格式”。你需要使用 **`⟹`** (Meta-implication，输入符号为 `==>`) 来连接。

```isabelle
(* 等价写法：短目标格式 *)
lemma arrow_style_example: "x > 0 ⟹ y > x ⟹ y > 0"
  apply simp
  done
```

### 3. 两种写法的核心区别 (必读)

虽然逻辑上它们是等价的，但在写证明（特别是 Isar 结构化证明）时，体验完全不同：

| 特性 | `assumes ... shows ...` (长格式) | `A ⟹ B ⟹ C` (短格式) |
| :--- | :--- | :--- |
| **假设的位置** | 假设自动进入**上下文 (Context)**。你可以直接使用 `assumption` 或引用它们。 | 假设还是**目标的一部分**。证明开始时，你需要先用 `intro` 或 `rule impI` 把它们“移入”上下文。 |
| **命名** | 可以方便地给假设命名 (如 `assumes A: ...`)。 | 很难直接给中间的假设命名。 |
| **适用场景** | **推荐**。适合编写人类可读的复杂证明，以及需要多步引用的证明。 | 适合**简短的引理**，或者打算直接用 `apply auto` 一行解决的简单性质。 |

#### 演示区别

**如果你用 `assumes` (推荐):**
```isabelle
lemma
  assumes "A" and "B"
  shows "C"
proof -
  (* 此时，A 和 B 已经是已知事实，可以直接用 *)
  from `A` have ...
```

**如果你用 `==>`:**
```isabelle
lemma "A ⟹ B ⟹ C"
proof -
  (* 此时，目标还是 "A ⟹ B ⟹ C" *)
  (* 你必须先手动把它们变成假设 *)
  show "A ⟹ B ⟹ C"
  proof (rule impI)+ (* 反复引入蕴含 *)
    assume "A" and "B"
    (* 现在才能开始证明 C *)
```
