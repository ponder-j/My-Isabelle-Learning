theory LocaleTest2
  imports Main
begin

locale database0 = 
  fixes update :: "'s \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 's" ("_ [_ := _]")
    and query  :: "'s \<Rightarrow> 'k \<Rightarrow> 'v option" ("_ \<triangleright> _")
  assumes updt_que: "s[k := v] \<triangleright> k = Some v"
begin
fun updates :: "'s \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 's"
  where "updates s [] = s" |
        "updates s ((k, v) # xs) = updates (update s k v) xs"
end

context database0
begin
definition queries :: "'s \<Rightarrow> 'k list \<Rightarrow> ('v option) list"
  where "queries s ks \<equiv> map (query s) ks"
end

definition (in database0) queries2 :: "'s \<Rightarrow> 'k list \<Rightarrow> ('v option) list"
  where "queries2 s ks \<equiv> map (query s) ks"

thm database0_def
print_locale database0
print_theorems
term "database0.updates"
thm database0.updates.simps

(* locale database = database0 update query
  for update :: "'s \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 's" ("_ [_ := _]")
    and query  :: "'s \<Rightarrow> 'k \<Rightarrow> 'v option" ("_ \<rhd> _")
  +
  fixes init :: 's
  assumes init_ : "\<forall>k. (init \<rhd> v) = None"

locale database1 =
  fixes update :: "'s1 \<Rightarrow> 'k1 \<Rightarrow> 'v1 \<Rightarrow> 's1" ("_ [_ := _]")
    and query  :: "'s1 \<Rightarrow> 'k1 \<Rightarrow> 'v1 option" ("_ \<rhd> _")
    and op2 :: "'k1 \<Rightarrow> 'v1"
  assumes updt_que: "s[k := v] \<rhd> k = Some v" *)

definition update_fun :: "('k \<Rightarrow> 'v option) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k \<Rightarrow> 'v option)"
  where "update_fun s k v = (\<lambda>x. if x = k then Some v else s x)"

definition query_fun :: "('k \<Rightarrow> 'v option) \<Rightarrow> 'k \<Rightarrow> 'v option"
  where "query_fun s k = s k"

interpretation database0 update query
  thm queries_def

end