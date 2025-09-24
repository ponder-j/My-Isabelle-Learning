theory TestSyntaxHighlighting
  imports Main Complex_Main
begin

(* This is a block comment *)
-- This is a line comment

section \<open>Basic Definitions\<close>

definition factorial :: "nat \<Rightarrow> nat"
  where "factorial n \<equiv> (if n = 0 then 1 else n * factorial (n - 1))"

fun fibonacci :: "nat \<Rightarrow> nat"
  where "fibonacci 0 = 0"
      | "fibonacci 1 = 1"
      | "fibonacci (Suc (Suc n)) = fibonacci (Suc n) + fibonacci n"

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

typedef Even = "{x::nat. x mod 2 = 0}"
proof
  show "0 \<in> {x::nat. x mod 2 = 0}" by simp
qed

record point =
  x_coord :: real
  y_coord :: real

subsection \<open>Locale Example\<close>

locale group =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
    and e :: 'a
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and left_neutral: "e \<cdot> x = x"
    and left_inverse: "\<exists>y. y \<cdot> x = e"

context group
begin

definition inv :: "'a \<Rightarrow> 'a"
  where "inv x = (THE y. y \<cdot> x = e)"

end

subsection \<open>Inductive Definitions\<close>

inductive_set Even_set :: "nat set"
  where zero: "0 \<in> Even_set"
      | step: "n \<in> Even_set \<Longrightarrow> n + 2 \<in> Even_set"

inductive rtc :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "('a \<times> 'a) set"
  where refl: "rtc r x x"
      | step: "rtc r x y \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> rtc r x z"

subsection \<open>Lemmas and Proofs\<close>

lemma factorial_positive: "factorial n > 0"
proof (induction n)
  case 0
  show ?case by (simp add: factorial_def)
next
  case (Suc n)
  show ?case
  proof -
    have "factorial (Suc n) = Suc n * factorial n"
      by (simp add: factorial_def)
    also have "... > 0"
      using Suc.IH by simp
    finally show ?thesis .
  qed
qed

theorem group_right_neutral:
  assumes "group f e"
  shows "\<exists>x. f x e = x"
proof -
  interpret group f e using assms .
  show ?thesis
  proof (cases "e = e")
    case True
    have "f e e = e"
      using left_neutral by simp
    thus ?thesis by blast
  qed
qed

subsection \<open>Class Instantiation\<close>

instantiation nat :: group_add
begin
  definition plus_nat_def: "plus_nat = (+)"
  definition zero_nat_def: "zero_nat = 0"
  instance by standard simp_all
end

subsection \<open>Symbols and Operators\<close>

lemma symbol_examples:
  "\<forall>x. \<exists>y. x \<le> y \<and> y \<in> {z. z \<ge> x}"
  "\<lambda>x. x + 1 \<in> {f. \<forall>n. f n > n}"
  "{x \<in> A. P x} \<union> {y \<in> B. Q y} = {z. (z \<in> A \<and> P z) \<or> (z \<in> B \<and> Q z)}"
  "A \<subseteq> B \<longleftrightarrow> A \<inter> B = A"
  "f \<circ> g = (\<lambda>x. f (g x))"
  by auto

text \<open>
  This theory demonstrates various Isabelle syntax elements:
  - Keywords: theory, imports, begin, end, definition, lemma, proof, qed
  - Symbols: \<forall>, \<exists>, \<Rightarrow>, \<le>, \<ge>, \<in>, \<subseteq>, \<union>, \<inter>
  - Comments: (* block *) and -- line
  - Type annotations: :: "nat \<Rightarrow> nat"
  - Proof commands: by, simp, auto, blast
\<close>

end