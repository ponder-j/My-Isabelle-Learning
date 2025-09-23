theory CustmizedTest
  imports Main
begin

type_synonym mynat = nat
definition nat1 :: "mynat \<Rightarrow> mynat"
  where "nat1 n \<equiv> n + 1"
value "nat1 15"

datatype 'a array = Null | Conn 'a "'a array"("_,_")
type_synonym 'a array_alias = "'a array"
type_synonym 'a array_synonym = "'a array"

typedecl BOOL

axiomatization T :: BOOL and F :: BOOL 
  and AND :: "BOOL \<Rightarrow> BOOL \<Rightarrow> BOOL"
  and OR :: "BOOL \<Rightarrow> BOOL \<Rightarrow> BOOL"
  and NOT :: "BOOL \<Rightarrow> BOOL"
  where ANDs: "AND a b = (if (a = T \<and> b = T) 
then T else F)"
   and  ORs: "OR a b = (if (a = T \<or> b = T) then T else F)"
   and  NOTs: "NOT a \<equiv> (if a = T then F else T)"
   
definition xorBOOL :: "BOOL \<Rightarrow> BOOL \<Rightarrow> BOOL"
  where "xorBOOL a b \<equiv> OR (AND a (NOT b)) (AND (NOT a) b)"

typedef Even = "{x::nat. x mod 2 = 0}"
(*  此处忽略Even集合非空的证明 *)

term Rep_Even
(* 输出 "Rep_Even" :: "Even \<Rightarrow> nat" *)
term Abs_Even
(* 输出 "Abs_Even" :: "nat \<Rightarrow> Even" *)

instantiation Even :: zero
begin
definition Zero_even_def: "0 = Abs_Even 0"
instance ..
end
term "0::Even"
(* 输出 "0" :: "Even" *)

instantiation Even :: one
begin
definition One_even_def: "1 = Abs_Even 2"
instance ..
end
term "1::Even"
(* 输出 "1" :: "Even" *)

definition SUC :: "Even \<Rightarrow> Even"
  where "SUC n \<equiv> Abs_Even (Suc (Suc (Rep_Even n)))"

definition ADD :: "Even \<Rightarrow> Even \<Rightarrow> Even"
  where "ADD m n \<equiv> Abs_Even ((Rep_Even m) + (Rep_Even n))"

lemma "SUC 0 = 1"

lemma "ADD (SUC 0) (SUC 0) = SUC (SUC 0)"

end