theory InverseFun
  imports Main
begin

(* 定义一个满射但非单射的函数 *)
definition f_surj :: "int \<Rightarrow> nat"
  where "f_surj x \<equiv> nat(abs x)"

(* 定义反函数 *)
definition "f_surj_inv \<equiv> the_inv f_surj"

(* 关键证明：the_inv在满射函数上总是有定义 *)
lemma the_inv_defined_on_surjective:
  assumes "surj f"
  shows "\<exists>x. f x = y \<Longrightarrow> f ((the_inv f) y) = y"
proof -
  assume "\<exists>x. f x = y"
  then obtain x where "f x = y" by blast
  
  (* the_inv的定义使用了THE算子 *)
  have "(the_inv f) y = (THE x. f x = y)"
    unfolding the_inv_def by simp
  
  (* 由于存在x使得f x = y，THE算子会选择其中一个 *)
  have "f ((THE x. f x = y)) = y"
  proof -
    (* 这里需要使用THE算子的性质 *)
    from \<open>\<exists>x. f x = y\<close> obtain x where "f x = y" by blast
    hence "f ((THE x. f x = y)) = y"
      by (rule theI)
    thus ?thesis .
  qed
  
  with \<open>(the_inv f) y = (THE x. f x = y)\<close> 
  show "f ((the_inv f) y) = y" by simp
qed

(* 验证我们的具体例子 *)
lemma f_surj_inv_property:
  "f_surj ((f_surj_inv) 2) = 2"
proof -
  have "\<exists>x. f_surj x = 2"
  proof
    show "f_surj 2 = 2" unfolding f_surj_def by simp
  qed
  thus ?thesis
    using f_surj_surjective the_inv_defined_on_surjective
    unfolding f_surj_inv_def by blast
qed

(* 但是反函数不唯一 *)
lemma f_surj_inv_not_unique:
  "f_surj 2 = 2 \<and> f_surj (-2) = 2"
  unfolding f_surj_def by simp

(* 这说明the_inv选择了2或-2中的某一个 *)
lemma f_surj_inv_choice:
  "(f_surj_inv) 2 = 2 \<or> (f_surj_inv) 2 = -2"
proof -
  have "f_surj ((f_surj_inv) 2) = 2"
    by (rule f_surj_inv_property)
  
  have "\<forall>x. f_surj x = 2 \<longleftrightarrow> (x = 2 \<or> x = -2)"
  proof
    fix x
    show "f_surj x = 2 \<longleftrightarrow> (x = 2 \<or> x = -2)"
      unfolding f_surj_def
      by (cases "x \<ge> 0") auto
  qed
  
  with \<open>f_surj ((f_surj_inv) 2) = 2\<close>
  show ?thesis by blast
qed

end