theory HOLSetTest
  imports Main
begin

(* ================================================================= *)
(* HOL 中的集合论规则演示 *)
(* ================================================================= *)
(* 本文件演示 Isabelle/HOL 中集合论的所有基本规则 *)
(* 每个规则都包含中文注释解释其含义和用途 *)
(* 在 HOL 中，集合本质上是一个 'a ⇒ bool 类型的函数 *)

(* ================================================================= *)
(* 1. 集合的基本规则 *)
(* ================================================================= *)

(* mem_Collect_eq: 元素属于集合当且仅当满足谓词 *)
(* a ∈ {x. P x} 等价于 P a *)
(* {x. P x} 即 符合谓词 P 的所有元素的集合，a ∈ {x. P x} 是一个有真值的命题，其正确性和 P a 相同 *)
lemma mem_Collect_eq_example: "a ∈ {x. P x} = P a"
  by (rule mem_Collect_eq)

(* Collect_mem_eq: 集合等于其元素的集合 *)
(* {x. x ∈ A} = A *)
lemma Collect_mem_eq_example: "{x. x ∈ A} = A"
  by (rule Collect_mem_eq)

(* empty_def: 空集定义为空谓词 *)
(* {} = {x. False} *)
lemma empty_def_example: "{} = {x. False}"
  by (rule empty_def)

(* insert_def: 插入操作定义为单元素集合的并集 *)
(* insert a B = {x. x = a} ∪ B *)
lemma insert_def_example: "insert a B = {x. x = a} ∪ B"
  by (rule insert_def)

(* Ball_def: 全称有界量词定义为全称量词 *)
(* Ball A P = (∀x. x∈A ⟶ P x) *)
(* Ball 即 Bounded All, Ball A P 表示对集合 A 中的所有元素 x, 谓词 P 都成立，这条规则就是将有界全称量词改写为全称量词 *)
lemma Ball_def_example: "Ball A P = (∀x. x∈A ⟶ P x)"
  by (rule Ball_def)

(* Bex_def: 存在有界量词定义为存在量词 *)
(* Bex A P = (∃x. x ∈ A ∧ P x) *)
(* Bex 即 Bounded Exists, Bex A P 表示在集合 A 中存在元素 x 使得 P x 成立，这条规则就是将有界存在量词改写为存在量词 *)
lemma Bex_def_example: "Bex A P = (∃x. x ∈ A ∧ P x)"
  by (rule Bex_def)

(* subset_def: 子集定义为所有元素都在另一个集合中 *)
(* A ⊆ B = ∀x∈A. x∈B *)
lemma subset_def_example: "A ⊆ B = (∀x∈A. x∈B)"
  by blast

(* Un_def: 并集定义为元素属于任一集合 *)
(* A ∪ B = {x. x ∈ A ∨ x ∈ B} *)
(* Un 即 Union *)
lemma Un_def_example: "A ∪ B = {x. x ∈ A ∨ x ∈ B}"
  by (rule Un_def)

(* Int_def: 交集定义为元素属于两个集合 *)
(* A ∩ B = {x. x ∈ A ∧ x ∈ B} *)
(* Int 即 Intersection *)
lemma Int_def_example: "A ∩ B = {x. x ∈ A ∧ x ∈ B}"
  by (rule Int_def)

(* set_diff_eq: 差集定义为属于第一个集合但不属于第二个集合 *)
(* A - B = {x. x ∈ A ∧ x ∉ B} *)
(* Set Difference *)
lemma set_diff_eq_example: "A - B = {x. x ∈ A ∧ x ∉ B}"
  by (rule set_diff_eq)

(* Compl_eq: 补集定义为不属于原集合的元素 *)
(* - A = {x. ¬ x ∈ A} *)
(* Compl 即 Complement *)
lemma Compl_eq_example: "- A = {x. ¬ x ∈ A}"
  by (rule Compl_eq)

(* INTER_def: 索引交集定义为对所有索引都属于对应集合 *)
(* INTER A B = {y. ∀x∈A. y∈B x} *)
(* Index Intersection *)
lemma INTER_def_example: "INTER A B = {y. ∀x∈A. y∈B x}"
  by (rule INTER_def)

(* UNION_def: 索引并集定义为存在某个索引属于对应集合 *)
(* UNION A B = {y. ∃x∈A. y∈B x} *)
lemma UNION_def_example: "UNION A B = {y. ∃x∈A. y∈B x}"
  by (rule UNION_def)

(* INTER1_def: 一元索引交集 *)
(* INTER1 B = INTER {x. True} B *)
lemma INTER1_def_example: "INTER1 B = INTER {x. True} B"
  by (rule INTER1_def)

(* UNION1_def: 一元索引并集 *)
(* UNION1 B = UNION {x. True} B *)
lemma UNION1_def_example: "UNION1 B = UNION {x. True} B"
  by (rule UNION1_def)

(* Inter_def: 集合族的交集 *)
(* Inter S = (INT x∈S. x) *)
lemma Inter_def_example: "Inter S = (INT x∈S. x)"
  by (rule Inter_def)

(* Union_def: 集合族的并集 *)
(* Union S = (UN x∈S. x) *)
lemma Union_def_example: "Union S = (UN x∈S. x)"
  by (rule Union_def)

(* Pow_def: 幂集定义为所有子集的集合 *)
(* Pow A = {B. B ⊆ A} *)
lemma Pow_def_example: "Pow A = {B. B ⊆ A}"
  by (rule Pow_def)

(* image_def: 像集定义为函数应用到集合的结果 *)
(* f ` A = {y. ∃x∈A. y = f x} *)
lemma image_def_example: "f ` A = {y. ∃x∈A. y = f x}"
  by (rule image_def)

(* range_def: 值域定义为函数在全集上的像 *)
(* range f = f ` UNIV *)
lemma range_def_example: "range f = f ` UNIV"
  by (rule range_def)

(* ================================================================= *)
(* 2. 内涵(Comprehension)与有界量词规则 *)
(* ================================================================= *)

(* CollectI: 如果谓词成立，则元素属于内涵集合 *)
(* P a ⟹ a ∈ {x. P x} *)
lemma CollectI_example: "P a ⟹ a ∈ {x. P x}"
  by (rule CollectI)

(* CollectD: 如果元素属于内涵集合，则谓词成立 *)
(* a ∈ {x. P x} ⟹ P a *)
lemma CollectD_example: "a ∈ {x. P x} ⟹ P a"
  by (rule CollectD)

(* CollectE: 内涵集合的消除规则 *)
(* ⟦ a ∈ {x. P x}; P a ⟹ W ⟧ ⟹ W *)
lemma CollectE_example: "⟦a ∈ {x. P x}; P a ⟹ W⟧ ⟹ W"
  by (rule CollectE)

(* ballI: 有界全称量词引入 *)
(* (⋀x. x ∈ A ⟹ P x) ⟹ ∀x∈A. P x *)
lemma ballI_example: "(⋀x. x ∈ A ⟹ P x) ⟹ ∀x∈A. P x"
  by (rule ballI)

(* bspec: 有界全称量词消除 *)
(* ∀x∈A. P x ⟹ x ∈ A ⟹ P x *)
lemma bspec_example: "∀x∈A. P x ⟹ x ∈ A ⟹ P x"
  by (rule bspec)

(* ballE: 有界全称量词消除（扩展版） *)
(* ∀x∈A. P x ⟹ (P x ⟹ Q) ⟹ (x ∉ A ⟹ Q) ⟹ Q *)
lemma ballE_example: "∀x∈A. P x ⟹ (P x ⟹ Q) ⟹ (x ∉ A ⟹ Q) ⟹ Q"
  by (rule ballE)

(* bexI: 有界存在量词引入 *)
(* P x ⟹ x ∈ A ⟹ ∃x∈A. P x *)
lemma bexI_example: "P x ⟹ x ∈ A ⟹ ∃x∈A. P x"
  by (rule bexI)

(* bexCI: 有界存在量词经典引入 *)
(* (∀x∈A. ¬ P x ⟹ P a) ⟹ a ∈ A ⟹ ∃x∈A. P x *)
lemma bexCI_example: "(∀x∈A. ¬ P x ⟹ P a) ⟹ a ∈ A ⟹ ∃x∈A. P x"
  by (rule bexCI)

(* bexE: 有界存在量词消除 *)
(* ∃x∈A. P x ⟹ (⋀x. x ∈ A ⟹ P x ⟹ Q) ⟹ Q *)
lemma bexE_example: "∃x∈A. P x ⟹ (⋀x. x ∈ A ⟹ P x ⟹ Q) ⟹ Q"
  by (rule bexE)

(* ================================================================= *)
(* 3. 子集及等式规则 *)
(* ================================================================= *)

(* subsetI: 子集关系引入 *)
(* (⋀x. x ∈ A ⟹ x ∈ B) ⟹ A ⊆ B *)
lemma subsetI_example: "(⋀x. x ∈ A ⟹ x ∈ B) ⟹ A ⊆ B"
  by (rule subsetI)

(* subsetD: 子集关系消除 *)
(* A ⊆ B ⟹ c ∈ A ⟹ c ∈ B *)
lemma subsetD_example: "A ⊆ B ⟹ c ∈ A ⟹ c ∈ B"
  by (rule subsetD)

(* subsetCE: 子集关系的经典消除 *)
(* A ⊆ B ⟹ (c ∉ A ⟹ P) ⟹ (c ∈ B ⟹ P) ⟹ P *)
lemma subsetCE_example: "A ⊆ B ⟹ (c ∉ A ⟹ P) ⟹ (c ∈ B ⟹ P) ⟹ P"
  by (rule subsetCE)

(* subset_refl: 子集关系自反性 *)
(* A ⊆ A *)
lemma subset_refl_example: "A ⊆ A"
  by (rule subset_refl)

(* subset_trans: 子集关系传递性 *)
(* A ⊆ B ⟹ B ⊆ C ⟹ A ⊆ C *)
lemma subset_trans_example: "A ⊆ B ⟹ B ⊆ C ⟹ A ⊆ C"
  by (rule subset_trans)

(* equalityI: 集合等式从双向子集推出 *)
(* A ⊆ B ⟹ B ⊆ A ⟹ A = B *)
lemma equalityI_example: "A ⊆ B ⟹ B ⊆ A ⟹ A = B"
  by (rule equalityI)

(* equalityD1: 集合等式分解为子集关系1 *)
(* A = B ⟹ A ⊆ B *)
lemma equalityD1_example: "A = B ⟹ A ⊆ B"
  by (rule equalityD1)

(* equalityD2: 集合等式分解为子集关系2 *)
(* A = B ⟹ B ⊆ A *)
lemma equalityD2_example: "A = B ⟹ B ⊆ A"
  by (rule equalityD2)

(* equalityE: 集合等式的消除规则 *)
(* A = B ⟹ (A ⊆ B ⟹ B ⊆ A ⟹ P) ⟹ P *)
lemma equalityE_example: "A = B ⟹ (A ⊆ B ⟹ B ⊆ A ⟹ P) ⟹ P"
  by (rule equalityE)

(* equalityCE: 集合等式的经典消除 *)
(* A = B ⟹ (c ∈ A ⟹ c ∈ B ⟹ P) ⟹ (c ∉ A ⟹ c ∉ B ⟹ P) ⟹ P *)
lemma equalityCE_example: "A = B ⟹ (c ∈ A ⟹ c ∈ B ⟹ P) ⟹ (c ∉ A ⟹ c ∉ B ⟹ P) ⟹ P"
  by (rule equalityCE)

(* ========================================= *)
(* 集合的Lattice规则 *)
(* ========================================= *)

(* Un_upper1: 并集的上界1 *)
(* A ⊆ A ∪ B *)
lemma Un_upper1_example: "A ⊆ A ∪ B"
  by (rule Un_upper1)

(* Un_upper2: 并集的上界2 *)
(* B ⊆ A ∪ B *)
lemma Un_upper2_example: "B ⊆ A ∪ B"
  by (rule Un_upper2)

(* Un_least: 并集的最小上界 *)
(* A ⊆ C ⟹ B ⊆ C ⟹ A ∪ B ⊆ C *)
lemma Un_least_example: "A ⊆ C ⟹ B ⊆ C ⟹ A ∪ B ⊆ C"
  by (rule Un_least)

(* Int_lower1: 交集的下界1 *)
(* A ∩ B ⊆ A *)
lemma Int_lower1_example: "A ∩ B ⊆ A"
  by (rule Int_lower1)

(* Int_lower2: 交集的下界2 *)
(* A ∩ B ⊆ B *)
lemma Int_lower2_example: "A ∩ B ⊆ B"
  by (rule Int_lower2)

(* Int_greatest: 交集的最大下界 *)
(* C ⊆ A ⟹ C ⊆ B ⟹ C ⊆ A ∩ B *)
lemma Int_greatest_example: "C ⊆ A ⟹ C ⊆ B ⟹ C ⊆ A ∩ B"
  by (rule Int_greatest)

(* Union_upper: 大并集的上界 *)
(* B∈A ⟹ B ⊆ Union A *)
lemma Union_upper_example: "B∈A ⟹ B ⊆ Union A"
  by (rule Union_upper)

(* Union_least: 大并集的最小上界 *)
(* (⋀x. x ∈ A ⟹ x ⊆ B) ⟹ Union A ⊆ B *)
lemma Union_least_example: "(⋀x. x ∈ A ⟹ x ⊆ B) ⟹ Union A ⊆ B"
  by (rule Union_least)

(* Inter_lower: 大交集的下界 *)
(* B∈A ⟹ Inter A ⊆ B *)
lemma Inter_lower_example: "B∈A ⟹ Inter A ⊆ B"
  by (rule Inter_lower)

(* Inter_greatest: 大交集的最大下界 *)
(* (⋀X. X ∈ A ⟹ C ⊆ X) ⟹ C ⊆ Inter A *)
lemma Inter_greatest_example: "(⋀X. X ∈ A ⟹ C ⊆ X) ⟹ C ⊆ Inter A"
  by (rule Inter_greatest)

(* ========================================= *)
(* 集合的等式规则 *)
(* ========================================= *)

(* Int_absorb: 交集吸收律 *)
(* A ∩ A = A *)
lemma Int_absorb_example: "A ∩ A = A"
  by (rule Int_absorb)

(* Int_commute: 交集交换律 *)
(* A ∩ B = B ∩ A *)
lemma Int_commute_example: "A ∩ B = B ∩ A"
  by (rule Int_commute)

(* Int_assoc: 交集结合律 *)
(* (A ∩ B) ∩ C = A ∩ (B ∩ C) *)
lemma Int_assoc_example: "(A ∩ B) ∩ C = A ∩ (B ∩ C)"
  by (rule Int_assoc)

(* Int_Un_distrib: 交集对并集的分配律 *)
(* A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) *)
lemma Int_Un_distrib_example: "A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)"
  by (rule Int_Un_distrib)

(* Un_absorb: 并集吸收律 *)
(* A ∪ A = A *)
lemma Un_absorb_example: "A ∪ A = A"
  by (rule Un_absorb)

(* Un_commute: 并集交换律 *)
(* A ∪ B = B ∪ A *)
lemma Un_commute_example: "A ∪ B = B ∪ A"
  by (rule Un_commute)

(* Un_assoc: 并集结合律 *)
(* (A ∪ B) ∪ C = A ∪ (B ∪ C) *)
lemma Un_assoc_example: "(A ∪ B) ∪ C = A ∪ (B ∪ C)"
  by (rule Un_assoc)

(* Un_Int_distrib: 并集对交集的分配律 *)
(* A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) *)
lemma Un_Int_distrib_example: "A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)"
  by (rule Un_Int_distrib)

(* Compl_disjoint: 补集不相交 *)
(* A ∩ - A = {} *)
lemma Compl_disjoint_example: "A ∩ - A = {}"
  by (rule Compl_disjoint)

(* Compl_partition: 补集划分全集 *)
(* A ∪ - A = UNIV *)
lemma Compl_partition_example: "A ∪ - A = UNIV"
  by (rule Compl_partition)

(* double_complement: 双重补集 *)
(* - (-A) = A *)
lemma double_complement_example: "- (-A) = A"
  by (rule double_complement)

(* Compl_Un: 德摩根律1 *)
(* - (A ∪ B) = (- A) ∩ (- B) *)
lemma Compl_Un_example: "- (A ∪ B) = (- A) ∩ (- B)"
  by (rule Compl_Un)

(* Compl_Int: 德摩根律2 *)
(* - (A ∩ B) = (- A) ∪ (- B) *)
lemma Compl_Int_example: "- (A ∩ B) = (- A) ∪ (- B)"
  by (rule Compl_Int)

(* Union_Un_distrib: 大并集对并集的分配 *)
(* ⋃(A ∪ B) = ⋃A ∪ ⋃B *)
lemma Union_Un_distrib_example: "Union (A ∪ B) = Union A ∪ Union B"
  by (rule Union_Un_distrib)

(* Int_Union: 交集对大并集的分配 *)
(* A ∩ ⋃B = (⋃C∈B. A ∩ C) *)
lemma Int_Union_example: "A ∩ Union B = (⋃C∈B. A ∩ C)"
  by (rule Int_Union)

(* Inter_Un_distrib: 大交集对并集的分配 *)
(* ⋂(A ∪ B) = ⋂A ∩ ⋂B *)
lemma Inter_Un_distrib_example: "Inter (A ∪ B) = Inter A ∩ Inter B"
  by (rule Inter_Un_distrib)

(* Un_Inter: 并集对大交集的分配 *)
(* A ∪ ⋂B = (⋂C∈B. A ∪ C) *)
lemma Un_Inter_example: "A ∪ Inter B = (⋂C∈B. A ∪ C)"
  by (rule Un_Inter)

(* ========================================= *)
(* 其他规则 *)
(* ========================================= *)

(* emptyE: 空集消除 *)
(* a ∈ {} ⟹ P *)
lemma emptyE_example: "a ∈ {} ⟹ P"
  by (rule emptyE)

(* insertI1: 插入规则1 *)
(* a ∈ insert a B *)
lemma insertI1_example: "a ∈ insert a B"
  by (rule insertI1)

(* insertI2: 插入规则2 *)
(* a ∈ B ⟹ a ∈ insert b B *)
lemma insertI2_example: "a ∈ B ⟹ a ∈ insert b B"
  by (rule insertI2)

(* insertE: 插入消除 *)
(* a ∈ insert b A ⟹ (a = b ⟹ P) ⟹ (a ∈ A ⟹ P) ⟹ P *)
lemma insertE_example: "a ∈ insert b A ⟹ (a = b ⟹ P) ⟹ (a ∈ A ⟹ P) ⟹ P"
  by (rule insertE)

(* ComplI: 补集引入 *)
(* (c ∈ A ⟹ False) ⟹ c ∈ - A *)
lemma ComplI_example: "(c ∈ A ⟹ False) ⟹ c ∈ - A"
  by (rule ComplI)

(* ComplD: 补集消除 *)
(* c ∈ - A ⟹ c ∉ A *)
lemma ComplD_example: "c ∈ - A ⟹ c ∉ A"
  by (rule ComplD)

(* UnI1: 并集引入1 *)
(* c ∈ A ⟹ c ∈ A ∪ B *)
lemma UnI1_example: "c ∈ A ⟹ c ∈ A ∪ B"
  by (rule UnI1)

(* UnI2: 并集引入2 *)
(* c ∈ B ⟹ c ∈ A ∪ B *)
lemma UnI2_example: "c ∈ B ⟹ c ∈ A ∪ B"
  by (rule UnI2)

(* UnCI: 并集经典引入 *)
(* (c ∉ B ⟹ c ∈ A) ⟹ c ∈ A ∪ B *)
lemma UnCI_example: "(c ∉ B ⟹ c ∈ A) ⟹ c ∈ A ∪ B"
  by (rule UnCI)

(* UnE: 并集消除 *)
(* c ∈ A ∪ B ⟹ (c ∈ A ⟹ P) ⟹ (c ∈ B ⟹ P) ⟹ P *)
lemma UnE_example: "c ∈ A ∪ B ⟹ (c ∈ A ⟹ P) ⟹ (c ∈ B ⟹ P) ⟹ P"
  by (rule UnE)

(* IntI: 交集引入 *)
(* c ∈ A ⟹ c ∈ B ⟹ c ∈ A ∩ B *)
lemma IntI_example: "c ∈ A ⟹ c ∈ B ⟹ c ∈ A ∩ B"
  by (rule IntI)

(* IntD1: 交集消除1 *)
(* c ∈ A ∩ B ⟹ c ∈ A *)
lemma IntD1_example: "c ∈ A ∩ B ⟹ c ∈ A"
  by (rule IntD1)

(* IntD2: 交集消除2 *)
(* c ∈ A ∩ B ⟹ c ∈ B *)
lemma IntD2_example: "c ∈ A ∩ B ⟹ c ∈ B"
  by (rule IntD2)

(* IntE: 交集消除 *)
(* c ∈ A ∩ B ⟹ (c ∈ A ⟹ c ∈ B ⟹ P) ⟹ P *)
lemma IntE_example: "c ∈ A ∩ B ⟹ (c ∈ A ⟹ c ∈ B ⟹ P) ⟹ P"
  by (rule IntE)

(* UN_I: 集合并集引入 *)
(* a ∈ A ⟹ b ∈ B a ⟹ b ∈ (⋃x∈A. B x) *)
lemma UN_I_example: "a ∈ A ⟹ b ∈ B a ⟹ b ∈ (⋃x∈A. B x)"
  by (rule UN_I)

(* UN_E: 集合并集消除 *)
(* b ∈ (⋃x∈A. B x) ⟹ (⋀x. x∈A ⟹ b ∈ B x ⟹ R) ⟹ R *)
lemma UN_E_example: "b ∈ (⋃x∈A. B x) ⟹ (⋀x. x∈A ⟹ b ∈ B x ⟹ R) ⟹ R"
  by (rule UN_E)

(* INT_I: 集合交集引入 *)
(* (⋀x. x ∈ A ⟹ b ∈ B x) ⟹ b ∈ (⋂x∈A. B x) *)
lemma INT_I_example: "(⋀x. x ∈ A ⟹ b ∈ B x) ⟹ b ∈ (⋂x∈A. B x)"
  by (rule INT_I)

(* INT_D: 集合交集消除 *)
(* b ∈ (⋂x∈A. B x) ⟹ a ∈ A ⟹ b ∈ B a *)
lemma INT_D_example: "b ∈ (⋂x∈A. B x) ⟹ a ∈ A ⟹ b ∈ B a"
  by (rule INT_D)

(* INT_E: 集合交集消除 *)
(* b ∈ (⋂x∈A. B x) ⟹ (b ∈ B a ⟹ R) ⟹ (a ∉ A ⟹ R) ⟹ R *)
lemma INT_E_example: "b ∈ (⋂x∈A. B x) ⟹ (b ∈ B a ⟹ R) ⟹ (a ∉ A ⟹ R) ⟹ R"
  by (rule INT_E)

(* UnionI: 大并集引入 *)
(* X ∈ C ⟹ A ∈ X ⟹ A ∈ ⋃C *)
lemma UnionI_example: "X ∈ C ⟹ A ∈ X ⟹ A ∈ Union C"
  by (rule UnionI)

(* UnionE: 大并集消除 *)
(* A ∈ ⋃C ⟹ (⋀X. A ∈ X ⟹ X ∈ C ⟹ R) ⟹ R *)
lemma UnionE_example: "A ∈ Union C ⟹ (⋀X. A ∈ X ⟹ X ∈ C ⟹ R) ⟹ R"
  by (rule UnionE)

(* InterI: 大交集引入 *)
(* (⋀X. X ∈ C ⟹ A ∈ X) ⟹ A ∈ ⋂C *)
lemma InterI_example: "(⋀X. X ∈ C ⟹ A ∈ X) ⟹ A ∈ Inter C"
  by (rule InterI)

(* InterD: 大交集消除 *)
(* A ∈ ⋂C ⟹ X ∈ C ⟹ A ∈ X *)
lemma InterD_example: "A ∈ Inter C ⟹ X ∈ C ⟹ A ∈ X"
  by (rule InterD)

(* InterE: 大交集消除 *)
(* A ∈ ⋂C ⟹ (X ∉ C ⟹ R) ⟹ (A ∈ X ⟹ R) ⟹ R *)
lemma InterE_example: "A ∈ Inter C ⟹ (X ∉ C ⟹ R) ⟹ (A ∈ X ⟹ R) ⟹ R"
  by (rule InterE)

(* PowI: 幂集引入 *)
(* A ⊆ B ⟹ A ∈ Pow B *)
lemma PowI_example: "A ⊆ B ⟹ A ∈ Pow B"
  by (rule PowI)

(* PowD: 幂集消除 *)
(* A ∈ Pow B ⟹ A ⊆ B *)
lemma PowD_example: "A ∈ Pow B ⟹ A ⊆ B"
  by (rule PowD)

(* imageI: 像集引入 *)
(* x ∈ A ⟹ f x ∈ f ` A *)
lemma imageI_example: "x ∈ A ⟹ f x ∈ f ` A"
  by (rule imageI)

(* imageE: 像集消除 *)
(* ⟦ b ∈ (λx. f x) ` A; ⋀X. ⟦b = f x; x ∈ A ⟧⟹P ⟧ ⟹P *)
lemma imageE_example: "b ∈ f ` A ⟹ (⋀x. b = f x ⟹ x ∈ A ⟹ P) ⟹ P"
  by (rule imageE)

(* rangeI: 值域引入 *)
(* f x ∈ range f *)
lemma rangeI_example: "f x ∈ range f"
  by (rule rangeI)

(* rangeE: 值域消除 *)
(* b ∈ range (λx. f x) ⟹ (⋀x. b = f x ⟹ P) ⟹ P *)
lemma rangeE_example: "b ∈ range f ⟹ (⋀x. b = f x ⟹ P) ⟹ P"
  by (rule rangeE)

end
