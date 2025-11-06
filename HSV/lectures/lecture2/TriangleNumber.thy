theory TriangleNumber
  imports Main
begin

thm div_add
(* ?c dvd ?a ⟹ ?c dvd ?b ⟹ (?a + ?b) div ?c = ?a div ?c + ?b div ?c *)
(* a 能被 c 整除，b 能被 c 整除，则 (a + b) 除以 c 得到的商等于各自除以 c 得到的商之和 *)

fun triangle :: "nat ⇒ nat" where
  "triangle n = (if n = 0 then 0 else n + triangle (n-1))"

theorem triangle_closed_form: "triangle n = n * (n + 1) div 2"
    apply (induct n)
    apply simp
    by (metis One_nat_def Zero_not_Suc add_Suc_right diff_Suc_Suc diff_zero distrib_left div_mult_self1 mult.commute
    nat_arith.rule0 numeral_2_eq_2 triangle.elims)

fun tet :: "nat ⇒ nat" where
  "tet n = (if n = 0 then 0 else triangle n + tet (n-1))"

theorem tet_closed_form: "tet n = n * (n + 1) * (n + 2) div 6"
proof (induct n)
    case 0
    (* ?case 会自动带入需要证明的变量 n=0 *)
    show ?case by simp
next
    (* ⋀n. tet n = n * (n + 1) * (n + 2) div 6 ⟹ tet (Suc n) = Suc n * (Suc n + 1) * (Suc n + 2) div 6 *)
    case (Suc n)
    (* IH: Induction Hypothesis *)
    assume IH: "tet n = n * (n + 1) * (n + 2) div 6"
    (* 因为证的是 Suc n 的情况，所以第一时间应该想到把 tet (Suc n) 按定义展开 *)
    have "tet (Suc n) = triangle (Suc n) + tet n"
        by simp
    (* 接下来按 triangle 的定理把 triangle (Suc n) 替换掉 *)
    (* 利用 also ... 的形式简化过程，其中 ... 代表前一个 have 语句结果的右侧 *)
    also have "... = (Suc n) * (Suc n + 1) div 2 + tet n"
        using triangle_closed_form by presburger
    (* 接下来利用归纳假设替换 tet n *)
    also have "... = (Suc n) * (Suc n + 1) div 2 + n * (n + 1) * (n + 2) div 6"
        using Suc by argo
    (* 现在需要进行代数化简，把上面的表达式化简成目标形式 Suc n * (Suc n + 1) * (Suc n + 2) div 6 *)
    (* 显然正常人的思维就是要先通分，然后合并同类项，最后提取公因式 *)
    (* 尝试 sledgehammer 会消耗较长时间，最后给出一坨东西，好在是对的 *)
    also have "... = (3 * (Suc n) * (Suc n + 1) + n * (n + 1) * (n + 2)) div 6"
        by (smt (verit) div_mult2_eq div_plus_div_distrib_dvd_left dvd_triv_left
    even_plus_one_iff mult.assoc mult.commute mult_2 mult_Suc mult_cancel_left
    mult_dvd_mono nonzero_mult_div_cancel_left numeral_Bit0
    numeral_Bit1)
    (* 继续化简 *)
    also have "... = (3 * (Suc n) * (Suc n + 1) + n * (Suc n) * (Suc n + 1)) div 6"
        using Suc_eq_plus1 add_2_eq_Suc' by presburger
    also have "... = (Suc n) * (Suc n + 1) * (3 + n) div 6"
        by (simp add: distrib_left mult.commute)
    also have "... = (Suc n) * (Suc n + 1) * (Suc n + 2) div 6"
        using Suc3_eq_add_3 add_2_eq_Suc' by presburger
    finally show "tet (Suc n) = (Suc n) * (Suc n + 1) * (Suc n + 2) div 6"
        by blast
qed

(* 看看 ICL 讲义中的证法，他为了证明上面 sledgehammer 费劲吧啦搞出来的一坨东西，自己先手动证了两个引理，也就是为了通分需要保持的整除性 *)
(* 因为 div 不是实数除法 / ，而是整除除法！ *)
(* 整数不能用实数除法只能用整除除法！ *)
theorem "tet n = ((n + 2) * (n + 1) * n) div 6"
proof (induct n)
  case 0
  show ?case by simp
next
  (* 换名字便于区分 *)
  case (Suc k) 

  (* induction hypothesis *)
  assume IH: "tet k = (k + 2) * (k + 1) * k div 6"

  (* establish a useful fact and label it "*" *)
  (* 两个引理都在为证明 (k + 2) * (k + 1) div 2 + (k + 2) * (k + 1) * k div 6 = ((k + 2) * (k + 1) * 3 + (k + 2) * (k + 1) * k) div 6 这一步做准备*)
  (* 也就是需要证明等式左边的两个部分都能分别被整除，没有舍去余数，进而才能“通分”合并 *)
  have "2 dvd (k + 2) * (k + 1)"
    by simp
  hence *: "6 dvd (k + 2) * (k + 1) * 3"
    by fastforce

  (* establish another useful fact and label it "**" *)
  (* 思路很简单，能证明同时能被 2 和 3 整除也就能证明整个式子能被 6 整除 *)
  have "2 dvd (k + 2) * (k + 1) * k" by simp
  moreover have "3 dvd (k + 2) * (k + 1) * k"
  (* 证明这一步，sledgehammer 死掉了！它证不出来！所以只能手动 proof *)
  (* 这个 {...} moreover {...} ultimately 结构是一个非常优雅的模式，用于实现：P(case1) ∨ P(case2) ∨ ... ∨ P(caseN) ⟹ Q的证明逻辑 *)
  proof -
    {
      assume "k mod 3 = 0"
      hence "3 dvd k" by presburger
      hence "3 dvd (k + 2) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 1"
      hence "3 dvd (k + 2)" by presburger
      hence "3 dvd (k + 2) * (k + 1) * k" by fastforce
    } moreover { 
      assume "k mod 3 = 2"
      hence "3 dvd (k + 1)" by presburger
      hence "3 dvd (k + 2) * (k + 1) * k" by fastforce
    } moreover {
        (* 如果这条不手动给出，那么在 ultimately 中使用 sledgehammer 出不了结果 *)
        (* 但是不给这条，直接在最后使用 by linarith 也能证出来 *)
        have "((k mod 3 = 0) ∨ (k mod 3 = 1) ∨ (k mod 3 = 2))"
            by fastforce
    }
    ultimately
    show "3 dvd (k + 2) * (k + 1) * k"
        by argo
  qed
  ultimately have **: "6 dvd (k + 2) * (k + 1) * k" by presburger

  (* the actual proof *)
  have "tet (Suc k) = triangle (Suc k) + tet k" 
    by simp
  also have "... = (k + 2) * (k + 1) div 2 + tet k" 
    using triangle_closed_form by simp
  also have "... = (k + 2) * (k + 1) div 2 + (k + 2) * (k + 1) * k div 6" 
    using IH by simp
  also have "... = ((k + 2) * (k + 1) * 3 + (k + 2) * (k + 1) * k) div 6" (* 这一步需要考虑整除性，否则变换不成立 *)
    using div_add[OF * **] (* 实例化 div_add 定理，* 和 ** 分别是两个前件，这样就能导出用于证明的结论 *)
    by linarith
  also have "... = (k + 2) * (k + 1) * (k + 3) div 6" 
    by (metis add.commute distrib_left)
  also have "... = (Suc k + 2) * (Suc k + 1) * Suc k div 6"
    by (metis calculation mult.commute mult.left_commute tet_closed_form)
  finally show ?case
    by blast
qed


end