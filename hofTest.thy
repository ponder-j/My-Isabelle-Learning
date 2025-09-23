theory hofTest
  imports Complex_Main
begin

definition limit :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
  where "limit f x0 A \<equiv>
          \<forall>(\<epsilon>::real) > 0. (\<exists>\<delta> > 0. (\<forall>x. 0 < \<bar>x - x0\<bar> \<and> \<bar>x - x0\<bar> < \<delta>
            \<longrightarrow> \<bar>f(x) - A\<bar> < \<epsilon>))"

end