theory MutuallyInductive
  imports Main
begin

inductive_set even :: "nat set" and
              odd  :: "nat set" where
    zero:  "0 \<in> even" |
    EvenI: "n \<in> odd  \<Longrightarrow> Suc n \<in> even" |
    OddI:  "n \<in> even \<Longrightarrow> Suc n \<in> odd"

end