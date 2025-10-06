theory AuxiliaryCommands
imports Main
begin
(* sorry 命令：令 Isabelle“姑且相信”欲证明的命题成立 *)
(* find_theorems 命令：查找包含给出的项（或匹配给出的模式）的定理 *)

find_theorems "?a+?b=?b+?a"
(* found 6 theorem(s):
  Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(24): ?a + ?c = ?c + ?a
  Groups.ab_semigroup_add_class.add.commute: ?a + ?b = ?b + ?a
  SMT.z3_rule(111): ?x + ?y = ?y + ?x
  Num.add_One_commute: num.One + ?n = ?n + num.One
  Num.numeral_class.one_plus_numeral_commute: 1 + numeral ?x = numeral ?x + 1
  Num.neg_numeral_class.is_num_add_commute: is_num ?x ⟹ is_num ?y ⟹ ?x + ?y = ?y + ?x *)

find_theorems "even"

end