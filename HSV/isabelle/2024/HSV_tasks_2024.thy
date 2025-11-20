theory HSV_tasks_2024 imports Main begin

section ‹ Task 1: Extending our circuit synthesiser with NAND gates. ›

text ‹ Datatype for representing simple circuits, extended with NAND gates. ›
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| NAND "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text ‹ Simulates a circuit given a valuation for each input wire. ›
fun simulate where
  "simulate (AND c1 c2) ρ = ((simulate c1 ρ) ∧ (simulate c2 ρ))"
| "simulate (OR c1 c2) ρ = ((simulate c1 ρ) ∨ (simulate c2 ρ))"
| "simulate (NAND c1 c2) ρ = (¬ ((simulate c1 ρ) ∧ (simulate c2 ρ)))"
| "simulate (NOT c) ρ = (¬ (simulate c ρ))"
| "simulate TRUE ρ = True"
| "simulate FALSE ρ = False"
| "simulate (INPUT i) ρ = ρ i"

text ‹ Equivalence between circuits. ›
fun circuits_equiv (infix "∼" 50) where
  "c1 ∼ c2 = (∀ρ. simulate c1 ρ = simulate c2 ρ)"

text ‹ A transformation that replaces AND/OR/NOT gates with NAND gates. ›
definition nand_true :: circuit where
  "nand_true = NAND (INPUT 0) (NAND (INPUT 0) (INPUT 0))"

definition nand_false :: circuit where
  "nand_false = NAND nand_true nand_true"

lemma simulate_nand_true [simp]: "simulate nand_true ρ = True"
  by (simp add: nand_true_def)

lemma simulate_nand_false [simp]: "simulate nand_false ρ = False"
  by (simp add: nand_false_def)

fun intro_nand where
  "intro_nand (AND c1 c2) = 
         NAND (NAND (intro_nand c1) (intro_nand c2)) nand_true"
| "intro_nand (OR c1 c2) = 
         NAND (NAND (intro_nand c1) nand_true) (NAND (intro_nand c2) nand_true)"
| "intro_nand (NAND c1 c2) = (
         NAND (intro_nand c1) (intro_nand c2))"
| "intro_nand (NOT c) = NAND (intro_nand c) nand_true"
| "intro_nand TRUE = nand_true"
| "intro_nand FALSE = nand_false"
| "intro_nand (INPUT i) = INPUT i"


text ‹ The intro_nand transformation is sound. Note that there is a 
  (deliberate) bug in the definition above, which you will need to fix 
  before you can prove the theorem below.›
theorem intro_nand_is_sound: "intro_nand c ∼ c"
  by (induct c) auto

text ‹ The only_nands predicate holds if a circuit contains only NAND gates. ›
fun only_nands where
  "only_nands (NAND c1 c2) = (only_nands c1 ∧ only_nands c2)"
| "only_nands (INPUT _) = True"
| "only_nands _ = False"

lemma only_nands_nand_true [simp]: "only_nands nand_true"
  by (simp add: nand_true_def)

lemma only_nands_nand_false [simp]: "only_nands nand_false"
  by (simp add: nand_false_def)

text ‹ The output of the intro_nand transformation is a circuit that only
  contains NAND gates. Note that there is a (deliberate) bug in the
  definition above, which you will need to fix before you can prove the
  theorem below. ›
theorem intro_nand_only_produces_nands:
  "only_nands (intro_nand c)"
  by (induct c) auto

section ‹ Task 2: Converting numbers to lists of digits. ›

text ‹ Turns a natural number into a list of digits in reverse order. ›
fun digits10 :: "nat ⇒ nat list"
where
  "digits10 n = (if n < 10 then [n] else (n mod 10) # digits10 (n div 10))"

value "digits10 42"

text ‹ Every digit is less than 10 (helper lemma). ›
lemma digits10_all_below_10_helper: 
  "ds = digits10 n ⟹ ∀d ∈ set ds. d < 10"
  by (induct n rule: digits10.induct) auto

text ‹ Every digit is less than 10. ›
corollary 
  "∀d ∈ set (digits10 n). d < 10" 
  using digits10_all_below_10_helper by blast

text ‹ Task 3: Converting to and from digit lists. ›

text ‹ A function that converts a list of digits back into a natural number. ›
fun sum10 :: "nat list ⇒ nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [2,4]"

text ‹ Applying digits10 then sum10 gets you back to the same number. ›
theorem digits10_sum10_inverse: 
  "sum10 (digits10 n) = n"
  by (induct n rule: digits10.induct) auto

section ‹ Task 4: A divisibility theorem. ›

section ‹ Task 5: Verifying a naive SAT solver. ›

text ‹ This function can be used with List.fold to simulate a do-until loop. ›
definition until :: "('a ⇒ bool) ⇒ 'a ⇒ 'a option ⇒ 'a option" 
  where
  "until p x z == if z = None then if p x then Some x else None else z" 

text ‹ Once the loop condition holds, the return value is fixed. ›
lemma until_some: "fold (until p) xs (Some z) = Some z"
  by (induct xs, auto simp add: until_def)

text ‹ If the loop returns None, the condition holds for no element of the input list. ›
lemma until_none: "fold (until p) xs None = None ⟹ list_all (λx. ¬ p x) xs"
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  hence *: "fold (until p) xs (until p a None) = None" by simp
  {
    assume "p a"
    hence "until p a None = Some a" by (simp add: until_def)
    hence "fold (until p) xs (Some a) = None" using * by presburger
    hence False using until_some by (metis option.distinct(1))
  } 
  moreover {
    assume "¬ p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = None" using * by presburger
    hence "list_all (λx. ¬ p x) xs" by (rule Cons.hyps)
    hence ?case by (simp add: `¬ p a`)
  } 
  ultimately show ?case by blast
qed

text ‹ If the loop returns Some x, the condition holds for element x of the input list. ›
lemma until_none_some: "fold (until p) xs None = Some x ⟹ p x ∧ List.member xs x"
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  hence *: "fold (until p) xs (until p a None) = Some x" by simp
  {
    assume "p a"
    hence "until p a None = Some a" by (simp add: until_def) 
    hence "a = x" by (metis * option.inject until_some)
    hence "p x ∧ List.member (a # xs) x" using `p a` in_set_member by force
  } 
  moreover {
    assume "¬ p a"
    hence "until p a None = None" by (simp add: until_def)
    hence "fold (until p) xs None = Some x" using * by presburger
    hence "p x ∧ List.member (a # xs) x" using Cons.hyps by (simp add: member_rec(1))
  } 
  ultimately show ?case by blast
qed

text ‹ We shall use strings to represent symbols. ›
type_synonym symbol = "string"

text ‹ A literal is either a variable or a negated symbol. ›
type_synonym literal = "symbol * bool"

text ‹ A valuation is a list of symbols and their truth values. ›
type_synonym valuation = "(symbol * bool) list"

text ‹ A clause is a disjunction of literals. ›
type_synonym clause = "literal list"

text ‹ A SAT query is a conjunction of clauses. ›
type_synonym query = "clause list"

text ‹ Given a valuation, evaluate a clause to its truth value. ›
definition evaluate_clause :: "valuation ⇒ clause ⇒ bool"
where 
  "evaluate_clause ρ c = list_ex (List.member ρ) c"

text ‹ Given a valuation, evaluate a query to its truth value. ›
definition evaluate :: "query ⇒ valuation ⇒ bool"
where 
  "evaluate q ρ = list_all (evaluate_clause ρ) q"

text ‹ Some sample queries and valuations. ›
(* q1 is (a ∨ b) ∧ (¬b ∨ c) *)
definition "q1 == [[(''a'', True), (''b'', True)], [(''b'', False), (''c'', True)]]"
(* q2 is (a ∨ b) ∧ (¬a ∨ ¬b) *)
definition "q2 == [[(''a'', True), (''b'', True)], [(''a'', False)], [(''b'', False)]]"
(* q3 is (a ∨ ¬b) *)
definition "q3 == [[(''a'', True), (''b'', False)]]"
(* q4 is (¬b ∨ a) *)
definition "q4 == [[(''b'', False), (''a'', True)]]"
definition "ρ1 == [(''a'', True), (''b'', True), (''c'', False)]"
definition "ρ2 == [(''a'', False), (''b'', True), (''c'', True)]"

value "evaluate q1 ρ1" 
value "evaluate q1 ρ2"

text ‹ Construct the list of all possible valuations over the given symbols. ›
fun mk_valuation_list :: "symbol list ⇒ valuation list"
where 
  "mk_valuation_list [] = [[]]"
| "mk_valuation_list (x # xs) = (
     let ρs = mk_valuation_list xs in 
     map ((#) (x, True)) ρs @ map ((#) (x, False)) ρs)"

value "mk_valuation_list [''a'',''b'']"
value "mk_valuation_list [''a'',''b'',''c'']"

fun symbol_of_literal :: "literal ⇒ symbol"
where
  "symbol_of_literal (x, _) = x"

text ‹ Extract the list of symbols from the given clause. ›
definition symbol_list_clause :: "clause ⇒ symbol list"
where 
  "symbol_list_clause c == remdups (map symbol_of_literal c)"

text ‹ Extract the list of symbols from the given query. ›
definition symbol_list :: "query ⇒ symbol list"
where
  "symbol_list q == remdups (concat (map symbol_list_clause q))"

value "symbol_list q1"
value "symbol_list q2"

text ‹ A naive SAT solver. It works by constructing the list of all
  possible valuations over the symbols that appear in the query, and
  then iterating through that list until it finds the first valuation
  that makes the query true. If none of the valuations make the query
  true, it returns None. ›
definition naive_solve :: "query ⇒ valuation option"
where
  "naive_solve q == 
  let xs = symbol_list q in 
  let ρs = mk_valuation_list xs in
  List.fold (until (evaluate q)) ρs None"

value "naive_solve q1"
value "naive_solve q2"
value "naive_solve q3"
value "naive_solve q4"

text ‹ If the naive SAT solver returns a valuation, then that 
  valuation really does make the query true. ›
theorem naive_solve_correct_sat:
  assumes "naive_solve q = Some ρ"
  shows "evaluate q ρ"
  using assms naive_solve_def until_none_some by fastforce

text ‹ If the naive SAT solver returns no valuation, then none of the valuations 
  it tried make the query true. ›
theorem naive_solve_correct_unsat:
  assumes "naive_solve q = None"
  shows "∀ρ ∈ set (mk_valuation_list (symbol_list q)). ¬ evaluate q ρ" 
  using assms naive_solve_def until_none list_all_iff by fastforce

section ‹ Task 6: Verifying a simple SAT solver. ›

text ‹ Update the clause c by fixing the symbol x to have truth-value b. Recall that a clause is
  a disjunction of literals, so the clause is true if any one of its literals is true. So if
  the clause contains the literal (x,b), which is fixed to be true, then the whole clause 
  becomes true and can be completely removed (replaced with the empty list). And if the clause 
  contains the literal (x, ¬b), which is fixed to be false, then that literal should be removed 
  from the clause. ›
definition update_clause :: "symbol ⇒ bool ⇒ clause ⇒ clause list"
where
  "update_clause x b c = (if List.member c (x, b) then [] else [removeAll (x, ¬ b) c])"

value "update_clause ''a'' True [(''a'', True), (''b'', False), (''c'', True)]"
value "update_clause ''a'' False [(''a'', True), (''b'', False), (''c'', True)]"
value "update_clause ''a'' True [(''a'', True), (''a'', False)]"
value "update_clause ''a'' True [(''a'', False)]"

text ‹ Update a query by fixing the symbol x to have truth-value b. This is done by
  updating each clause independently (using the update_clause function). ›
fun update_query :: "symbol ⇒ bool ⇒ query ⇒ query"
where
  "update_query x b [] = []"
| "update_query x b (c # q) = update_clause x b c @ update_query x b q"

value "update_query ''a'' True q1"
value "update_query ''a'' False q1"
value "update_query ''b'' True q1"
value "update_query ''b'' False q1"

text ‹ Extract the set of symbols that appear in a given clause. ›
definition symbols_clause :: "clause ⇒ symbol set"
where 
  "symbols_clause c ≡ set (map symbol_of_literal c)"

text ‹ Extract the set of symbols that appear in a given query. ›
definition symbols :: "query ⇒ symbol set"
where
  "symbols q ≡ ⋃ (set (map symbols_clause q))"

value "symbols q1"
value "symbols q2"

text ‹ A simple SAT solver. Given a query, it does a three-way case split. If 
  the query has no clauses then it is trivially satisfiable (with the
   empty valuation). If the first clause in the query is empty, then the
   query is unsatisfiable. Otherwise, it considers the first symbol that 
   appears in the query, and makes two recursive solving attempts: one 
   with that symbol evaluated to true, and one with it evaluated to false.
   If neither recursive attempt succeeds, the query is deemed unsatisfiable. ›
function simp_solve :: "query ⇒ valuation option"
where
  "simp_solve q = (
   case q of
     [] ⇒ Some []
   | [] # _ ⇒ None
   | ((x,_) # _) # _ ⇒ (
     case simp_solve (update_query x True q) of
       Some ρ ⇒ Some ((x, True) # ρ)
     | None ⇒ (
       case simp_solve (update_query x False q) of 
         Some ρ ⇒ Some ((x, False) # ρ)
       | None ⇒ None)))"
by pat_completeness auto
termination 
  sorry

value "simp_solve q1"
value "simp_solve q2"
value "simp_solve q3"
value "simp_solve q4"


definition domain :: "('a * 'b) list ⇒ 'a set"
where
  "domain kvs = set (map fst kvs)"

lemma evaluate_update_clause_helper:
  assumes "x ∉ domain ρ"
  shows "(∀c' ∈ set (update_clause x b c). evaluate_clause ρ c') = evaluate_clause ((x, b) # ρ) c"
  using assms
  apply (auto simp: update_clause_def evaluate_clause_def domain_def)
  apply (metis fst_conv image_eqI)
  done

lemma evaluate_update_query: 
  assumes "x ∉ domain ρ"
  shows "evaluate (update_query x b q) ρ = evaluate q ((x, b) # ρ)"
  using assms evaluate_update_clause_helper
  by (induct q) (auto simp: evaluate_def)

lemma symbols_update_query:
  "symbols (update_query x b q) ⊆ symbols q - {x}"
  apply (induct q)
   apply (auto simp: symbols_def symbols_clause_def update_clause_def update_query.simps)
  done

lemma simp_solve_domain:
  "simp_solve q = Some ρ ⟹ domain ρ ⊆ symbols q"
  apply (induct q arbitrary: ρ rule: simp_solve.induct)
    apply (auto split: list.splits option.splits)
   apply (metis (mono_tags, lifting) Diff_subset Un_subset_iff insert_subset subset_trans symbols_update_query)
  apply (metis (mono_tags, lifting) Diff_subset Un_subset_iff insert_subset subset_trans symbols_update_query)
  done

text ‹ If the simple SAT solver returns a valuation, then that 
  valuation really does make the query true. ›
theorem simp_solve_sat_correct:
  "simp_solve q = Some ρ ⟹ evaluate q ρ"
proof (induct q arbitrary: ρ rule: simp_solve.induct)
  case (1 q)
  then show ?case
    apply (cases q)
     apply (auto simp: evaluate_def)
    apply (metis evaluate_update_query simp_solve_domain subsetD)
    done
qed

lemma evaluate_mono: "set ρ ⊆ set ρ' ⟹ evaluate q ρ ⟹ evaluate q ρ'"
  by (auto simp: evaluate_def evaluate_clause_def)

text ‹ A valuation is deemed well-formed (wf) as long as it does
  not assign a truth-value for the same symbol more than once. ›
definition wf_valuation where
  "wf_valuation ρ = distinct (map fst ρ)"

text ‹ If the simple SAT solver returns no valuation, then 
  there exists no well-formed valuation that can make the 
  query evaluate to true. ›
theorem simp_solve_unsat_correct:
  "simp_solve q = None ⟹ 
   (∀ρ. wf_valuation ρ ⟶ ¬ evaluate q ρ)"
proof (induct q rule: simp_solve.induct)
  case (1 q)
  show ?case
  proof (intro allI impI)
    fix ρ assume "wf_valuation ρ"
    show "¬ evaluate q ρ"
    proof (cases q)
      case Nil
      then show ?thesis using 1 by simp
    next
      case (Cons c q')
      then obtain x b where "c = (x, b) # tl c" by (cases c) auto
      have "simp_solve (update_query x True q) = None" 
        and "simp_solve (update_query x False q) = None"
        using 1 Cons `c = (x, b) # tl c` by (auto split: option.splits)
      
      show ?thesis
      proof (cases "x ∈ domain ρ")
        case True
        then obtain v where v_in: "(x, v) ∈ set ρ" by (auto simp: domain_def)
        let ?rho' = "filter (λl. fst l ≠ x) ρ"
        have wf_rho': "wf_valuation ?rho'" using `wf_valuation ρ` 
          by (simp add: wf_valuation_def)
        have "evaluate q ρ ⟷ evaluate q ((x, v) # ?rho')"
          using `wf_valuation ρ` v_in
          apply (auto simp: evaluate_def evaluate_clause_def)
           apply (metis (no_types, lifting) fst_conv image_eqI map_filter_ID member_filter set_filter)
          by (metis (no_types, lifting) fst_conv image_eqI map_filter_ID member_filter set_filter)
        also have "... ⟷ evaluate (update_query x v q) ?rho'"
          using evaluate_update_query[of x ?rho' v q]
          by (simp add: domain_def)
        finally have "evaluate q ρ ⟷ evaluate (update_query x v q) ?rho'" .
        
        moreover have "¬ evaluate (update_query x v q) ?rho'"
          using 1(1,2) `simp_solve (update_query x True q) = None` `simp_solve (update_query x False q) = None`
          using wf_rho' Cons `c = (x, b) # tl c`
          by (cases v) auto
        ultimately show ?thesis by simp
      next
        case False
        have "evaluate q ρ ⟹ evaluate q ((x, True) # ρ)"
          by (rule evaluate_mono) auto
        also have "... ⟷ evaluate (update_query x True q) ρ"
          using evaluate_update_query[of x ρ True q] False by simp
        finally have "evaluate q ρ ⟹ evaluate (update_query x True q) ρ" .
        moreover have "¬ evaluate (update_query x True q) ρ"
          using 1(1) `simp_solve (update_query x True q) = None` `wf_valuation ρ` Cons `c = (x, b) # tl c`
          by simp
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed

end