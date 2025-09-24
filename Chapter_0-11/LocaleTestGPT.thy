theory LocaleTestGPT
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

(* --------------------------------------------------- *)
(* 这里是新增的具体实现                                *)
(* 用 ('k \<Rightarrow> 'v option) 作为数据库类型                  *)
(* --------------------------------------------------- *)

definition update_fun :: "('k \<Rightarrow> 'v option) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k \<Rightarrow> 'v option)"
  where "update_fun s k v = (\<lambda>x. if x = k then Some v else s x)"

definition query_fun :: "('k \<Rightarrow> 'v option) \<Rightarrow> 'k \<Rightarrow> 'v option"
  where "query_fun s k = s k"

(* --------------------------------------------------- *)
(* interpretation: 用上面的定义实例化 locale           *)
(* --------------------------------------------------- *)

interpretation db: database0 update_fun query_fun
  by (unfold_locales, simp add: update_fun_def query_fun_def)

(* 现在可以用 db.updates, db.queries 等带前缀的定理/定义 *)
thm db.updates.simps
thm db.queries_def
thm db.queries2_def

end
