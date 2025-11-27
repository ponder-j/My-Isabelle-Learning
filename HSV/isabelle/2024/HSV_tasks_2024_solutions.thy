theory HSV_tasks_2024_solutions imports Main begin

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
fun intro_nand where
  "intro_nand (AND c1 c2) = 
         NAND (NAND (intro_nand c1) (intro_nand c2)) TRUE"
| "intro_nand (OR c1 c2) = 
         NAND (NAND (intro_nand c1) TRUE) (NAND (intro_nand c2) TRUE)"
| "intro_nand (NAND c1 c2) = (
         NAND (intro_nand c1) (intro_nand c2))"
| "intro_nand (NOT c) = NAND (intro_nand c) TRUE"
| "intro_nand TRUE = TRUE"
| "intro_nand FALSE = NAND TRUE FALSE"
| "intro_nand (INPUT i) = INPUT i"

fun intro_nand_fixed where
  "intro_nand_fixed (AND c1 c2) = 
         NAND (NAND (intro_nand_fixed c1) (intro_nand_fixed c2)) TRUE"
| "intro_nand_fixed (OR c1 c2) = 
         NAND (NAND (intro_nand_fixed c1) TRUE) (NAND (intro_nand_fixed c2) TRUE)"
| "intro_nand_fixed (NAND c1 c2) = (
         NAND (intro_nand_fixed c1) (intro_nand_fixed c2))"
| "intro_nand_fixed (NOT c) = NAND (intro_nand_fixed c) TRUE"
| "intro_nand_fixed TRUE = TRUE"
| "intro_nand_fixed FALSE = NAND TRUE TRUE"
| "intro_nand_fixed (INPUT i) = INPUT i"

text ‹ The intro_nand transformation is sound. Note that there is a 
  (deliberate) bug in the definition above, which you will need to fix 
  before you can prove the theorem below.›
theorem intro_nand_is_sound: "intro_nand_fixed c ∼ c"
  by (induct c, auto)

text ‹ The only_nands predicate holds if a circuit contains only NAND gates. ›
fun only_nands where
  "only_nands (NAND c1 c2) = (only_nands c1 ∧ only_nands c2)"
| "only_nands (INPUT _) = True"
| "only_nands _ = False"

text ‹ The only_nands predicate holds if a circuit contains only NAND gates. ›
fun only_nands_fixed where
  "only_nands_fixed (NAND c1 c2) = (only_nands_fixed c1 ∧ only_nands_fixed c2)"
| "only_nands_fixed TRUE = True"
| "only_nands_fixed (INPUT _) = True"
| "only_nands_fixed _ = False"

text ‹ The output of the intro_nand transformation is a circuit that only
  contains NAND gates. Note that there is a (deliberate) bug in the
  definition above, which you will need to fix before you can prove the
  theorem below. ›
theorem intro_nand_only_produces_nands:
  "only_nands_fixed (intro_nand_fixed c)"
  by (induct c, auto)

section ‹ Task 2: Converting numbers to lists of digits. ›

text ‹ Turns a natural number into a list of digits in reverse order. ›
fun digits10 :: "nat ⇒ nat list"
where
  "digits10 n = (if n < 10 then [n] else (n mod 10) # digits10 (n div 10))"

value "digits10 42"
value "digits10 12345"
value "digits10 0"
value "digits10 3"

text ‹ Every digit is less than 10 (helper lemma). ›
lemma digits10_all_below_10_helper: 
  "ds = digits10 n ⟹ ∀d ∈ set ds. d < 10"
proof (induct ds arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons d ds)
  {
    assume "n < 10"
    hence ?case by (simp add: Cons.prems)
  }
  moreover {
    assume "n ≥ 10"
    hence "digits10 n = (n mod 10) # digits10 (n div 10)" by simp
    hence "d = n mod 10" and "ds = digits10 (n div 10)" using Cons.prems by simp+
    hence ?case by (metis Cons.hyps mod_less_divisor set_ConsD zero_less_numeral)
  }
  ultimately show ?case by linarith
qed
  
text ‹ Every digit is less than 10. ›
corollary 
  "∀d ∈ set (digits10 n). d < 10" 
using digits10_all_below_10_helper by blast

text ‹ The list of digits is never empty. ›
theorem digits10_nonempty:
  "digits10 n ≠ []"
by simp

text ‹ Task 3: Converting to and from digit lists. ›

text ‹ A function that converts a list of digits back into a natural number. ›
fun sum10 :: "nat list ⇒ nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [2,4]"
value "sum10 [5,4,3,2,1]"
value "sum10 []"
value "sum10 [3]"

text ‹ Applying digits10 then sum10 gets you back to the same number (helper lemma). ›
lemma digits10_sum10_inverse_helper: 
  "ds = digits10 n ⟹ sum10 ds = n"
proof (induct ds arbitrary: n)
  case Nil
  thus ?case by (metis digits10_nonempty)
next
  case (Cons d ds)
  {
    assume "n < 10"
    hence ?case by (simp add: Cons.prems)
  } moreover {
    assume "n ≥ 10"
    hence "digits10 n = (n mod 10) # digits10 (n div 10)" by simp
    hence "d = n mod 10" and "ds = digits10 (n div 10)" using Cons.prems by simp+
    hence ?case using Cons.hyps by force
  } 
  ultimately show ?case by linarith
qed

text ‹ Applying digits10 then sum10 gets you back to the same number. ›
corollary digits10_sum10_inverse: 
  "sum10 (digits10 n) = n"
using digits10_sum10_inverse_helper by blast

text ‹ Applying sum10 then digits10 doesn't always gets you back to the same digit sequence. ›
lemma "ds ≠ [] ⟹ ds ≠ [0, 0] ⟹ ds ≠ [1, 0] ⟹ ds = digits10 (sum10 ds)" oops

section ‹ Task 4: A divisibility theorem. ›

text ‹ Any number whose digits are of the form ABABAB is divisible by 37. ›
theorem "digits10 n = [A, B, A, B, A, B] ⟹ 37 dvd n"
proof -
  assume "digits10 n = [A, B, A, B, A, B]"
  hence "sum10 (digits10 n) = A + B * 10 + A * 100 + B * 1000 + A * 10000 + B * 100000" by auto
  hence "n = (A + 10 * B) * 10101" using digits10_sum10_inverse by fastforce
  moreover have "(37::nat) dvd 10101" by eval
  ultimately show ?thesis by auto
qed

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
by (metis assms until_none_some naive_solve_def)

text ‹ If the naive SAT solver returns no valuation, then none of the valuations 
  it tried make the query true. ›
theorem naive_solve_correct_unsat:
  assumes "naive_solve q = None"
  shows "∀ρ ∈ set (mk_valuation_list (symbol_list q)). ¬ evaluate q ρ" 
by (metis assms until_none naive_solve_def in_set_conv_decomp list_all_append list_all_simps(1))

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

lemma symbols_append:
  "symbols (q @ q') = symbols q ∪ symbols q'"
  by (induct q, auto simp add: symbols_def)

lemma symbols_update_clause: 
  "symbols (update_clause x b c) ⊆ symbols_clause c - {x}"
proof (cases "List.member c (x, b)")
  case True
  thus ?thesis by (auto simp add: update_clause_def symbols_def) 
next
  case False
  thus ?thesis 
    apply (auto simp add: symbols_clause_def update_clause_def symbols_def member_def)
    apply (metis (full_types)) 
    done
qed

lemma symbols_update_query: 
  "symbols (update_query x b q) ⊆ symbols q - {x}"
proof (induct q)
  case Nil
  thus ?case using symbols_def by auto
next
  case (Cons c q)
  hence "symbols (update_query x b q) ⊆ symbols q - {x}" by blast
  have "symbols (update_query x b (c # q)) 
                 = symbols (update_clause x b c) ∪ symbols (update_query x b q)" 
    using symbols_append by simp
  also have "... ⊆ (symbols_clause c - {x}) ∪ (symbols q - {x})" 
    using Cons symbols_update_clause by blast
  also have "... = symbols_clause c ∪ symbols q - {x}" by blast
  also have "... = symbols (c # q) - {x}"
    using symbols_def by force
  finally show ?case by blast
qed

text ‹ The set of symbols in any query is finite. ›
lemma finite_symbols: 
  "finite (symbols q)"
by (induct q, auto simp add: symbols_def symbols_clause_def)

text ‹ If symbol x appears in query q, then update_query x b q will 
  strictly reduce the number of symbols in q. ›
lemma symbol_count_decreasing:
  assumes "x ∈ symbols q"
  shows "card (symbols (update_query x b q)) < card (symbols q)"
proof -
  have "card (symbols (update_query x b q)) ≤ card (symbols q - {x})" 
    using symbols_update_query finite_symbols by (simp add: card_mono)
  also have "... < card (symbols q)" using assms
    using finite_symbols by (meson card_Diff1_less)
  finally show ?thesis by blast
qed

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
  apply (relation "measure (λq. card (symbols q))")
  apply force
  apply (clarsimp simp del: update_query.simps, rule symbol_count_decreasing,
    simp add: symbols_def symbols_clause_def)+
  done

value "simp_solve q1"
value "simp_solve q2"
value "simp_solve q3"
value "simp_solve q4"

lemma list_ex_member:
  "list_ex (List.member xs) ys = (set xs ∩ set ys ≠ {})"
by (metis Bex_set disjoint_iff_not_equal in_set_member)

definition domain :: "('a * 'b) list ⇒ 'a set"
where
  "domain kvs = set (map fst kvs)"

lemma evaluate_update_clause: 
  assumes "x ∉ domain ρ"
  shows "evaluate (update_clause x b c) ρ = evaluate_clause c ((x, b) # ρ)"
proof (cases "List.member c (x, b)")
  case True
  thus ?thesis by (simp add: update_clause_def evaluate_clause_def evaluate_def)
next
  case False
  hence 1: "(x, b) ∉ set c" by (simp add: member_def)

  have 2: "(x, ¬b) ∉ set ρ" using assms domain_def by force

  have "evaluate (update_clause x b c) ρ 
                 = list_ex (List.member ρ) (removeAll (x, ¬ b) c)" 
    by (simp add: False update_clause_def evaluate_clause_def evaluate_def)
  also have "... = (set ρ ∩ (set c - {(x, ¬ b)}) ≠ {})" 
    by (metis list_ex_member set_removeAll)
  also have "... = (set ρ ∩ set c ≠ {})" using 2 by blast
  also have "... = (({(x, b)} ∪ set ρ) ∩ set c ≠ {})" using 1 by simp 
  also have "... = list_ex (List.member ((x, b) # ρ)) c" using list_ex_member by force
  also have "... = evaluate_clause c ((x, b) # ρ)"
    by (metis Bex_set evaluate_clause_def member_def)
  finally show ?thesis by blast
qed

lemma evaluate_update_query: 
  assumes "x ∉ domain ρ"
  shows "evaluate (update_query x b q) ρ = evaluate q ((x, b) # ρ)"
proof (induct q)
  case Nil
  show ?case by (simp add: evaluate_def)
next
  case (Cons c q)
  let ?q' = "update_query x b q"
  let ?c' = "update_clause x b c"

  have "evaluate (update_query x b (c # q)) ρ 
                 = evaluate (?c' @ ?q') ρ" by auto
  also have "... = (evaluate ?c' ρ ∧ evaluate ?q' ρ)" using evaluate_def by simp
  also have "... = (evaluate_clause c ((x, b) # ρ) ∧ evaluate ?q' ρ)" 
    using assms by (simp add: in_set_member evaluate_update_clause)
  also have "... = evaluate (c # q) ((x, b) # ρ)" using Cons.hyps evaluate_def 
    by (simp add: evaluate_clause_def list_ex_member Int_commute in_set_member) 
  finally show ?case by blast
qed


text ‹ If the simple SAT solver returns a valuation, then that 
  valuation really does make the query true (and the domain of
  that valuation doesn't mention any symbol not in the given 
  query). ›
lemma simp_solve_sat_correct:
  "simp_solve q = Some ρ ⟹ evaluate q ρ ∧ domain ρ ⊆ symbols q"
proof (induct arbitrary: ρ rule: simp_solve.induct)
  case (1 q)
  consider 
    (noclauses) "q = []" 
  | (emptyclause) cs where "q = [] # cs"
  | (normalcase) x b ls cs where "q = ((x,b) # ls) # cs"
    by (metis old.prod.exhaust transpose.cases)
  thus ?case
  proof (cases)
    case noclauses
    thus ?thesis using "1.prems" domain_def evaluate_def by force
  next
    case (emptyclause cs)
    thus ?thesis using "1.prems" by force
  next
    case (normalcase x b ls cs)

    let ?qT = "update_query x True q"
    let ?qF = "update_query x False q"

    {
      assume *: "simp_solve ?qT = None"
      hence "∃ρ'. simp_solve ?qF = Some ρ' ∧ ρ = (x, False) # ρ'" 
        using normalcase "1.prems" by (cases "simp_solve ?qF", auto)
      hence "∃ρ'. evaluate ?qF ρ' ∧ domain ρ' ⊆ symbols ?qF ∧ 
        ρ = (x, False) # ρ'" using "1.hyps"(2)[OF normalcase] * by blast
    } 
    moreover {
      assume "simp_solve ?qT ≠ None"
      hence "∃ρ'. simp_solve ?qT = Some ρ' ∧ ρ = (x, True) # ρ'" 
        using normalcase "1.prems" by auto
      hence "∃ρ'. evaluate ?qT ρ' ∧ domain ρ' ⊆ symbols ?qT ∧ 
        ρ = (x, True) # ρ'" using "1.hyps"(1)[OF normalcase] by blast
    }
    ultimately obtain ρ' b' where 
      "evaluate (update_query x b' q) ρ'" and
      "domain ρ' ⊆ symbols (update_query x b' q)" and
      rho_def: "ρ = (x, b') # ρ'" by blast

    hence "evaluate q ρ" and **: "domain ρ' ⊆ symbols q - {x}" 
      using symbols_update_query evaluate_update_query by blast+

    moreover have "domain ρ = {x} ∪ domain ρ'"
      by (metis rho_def domain_def fst_conv insert_is_Un list.simps(15) list.simps(9))

    moreover have "... ⊆ symbols q" 
      using symbols_def symbols_clause_def normalcase ** by auto

    ultimately show ?thesis by blast
  qed
qed

corollary 
  "simp_solve q = Some ρ ⟹ evaluate q ρ"
  using simp_solve_sat_correct by blast

text ‹ A valuation is deemed well-formed (wf) as long as it does
  not assign a truth-value for the same symbol more than once. ›
definition wf_valuation where
  "wf_valuation ρ = distinct (map fst ρ)"

lemma list_all_mono:
  assumes "p ≤ q"
  shows "list_all p xs ⟶ list_all q xs"
  using assms list.pred_mono by auto

lemma evaluate_on_larger_valuation:
  assumes "set ρ ⊆ set ρ'"
  shows "evaluate q ρ ⟶ evaluate q ρ'"
  using assms 
  apply (unfold evaluate_def evaluate_clause_def list_ex_member)
  apply (rule list_all_mono)
  apply blast
  done

lemma evaluate_on_permuted_valuation:
  assumes "set ρ = set ρ'"
  shows "evaluate q ρ = evaluate q ρ'"
using assms evaluate_on_larger_valuation by blast

text ‹ If the simple SAT solver returns no valuation, then 
  there exists no well-formed valuation that can make the 
  query evaluate to true. ›
theorem simp_solve_unsat_correct:
  "simp_solve q = None ⟹ 
   (∀ρ. wf_valuation ρ ⟶ ¬ evaluate q ρ)"
proof (induct rule: simp_solve.induct)
  case (1 q)
  consider 
    (noclauses) "q = []" 
  | (emptyclause) cs where "q = [] # cs"
  | (normalcase) x b ls cs where "q = ((x,b) # ls) # cs"
    by (metis old.prod.exhaust transpose.cases)
  thus ?case
  proof (cases)
    case noclauses
    thus ?thesis using "1.prems" domain_def evaluate_def by force
  next
    case (emptyclause cs)
    thus ?thesis using "1.prems" evaluate_clause_def evaluate_def by force
  next
    case (normalcase x b ls cs)

    let ?qT = "update_query x True q"
    let ?qF = "update_query x False q"

    {
      fix ρ :: valuation
      define ρ' where ρ'_def: "ρ' ≡ filter (λkv. fst kv ≠ x) ρ"

      assume "wf_valuation ρ"

      hence "wf_valuation ρ'" 
        using ρ'_def wf_valuation_def distinct_map_filter by blast

      have *: "simp_solve ?qT = None" 
        using "1.prems" normalcase option.discI by fastforce

      hence "¬ evaluate ?qT ρ'" 
        using "1.hyps"(1) normalcase `wf_valuation ρ'` by simp

      hence "¬ evaluate q ((x, True) # ρ')" 
        using evaluate_update_query ρ'_def domain_def by force

      moreover have "simp_solve ?qF = None" 
        using "1.prems" * normalcase option.discI by fastforce

      hence "¬ evaluate ?qF ρ'" 
         using "1.hyps"(2)[OF normalcase] * `wf_valuation ρ'` by simp

      hence "¬ evaluate q ((x, False) # ρ')" 
        using evaluate_update_query ρ'_def domain_def by force

      ultimately have **: "∀b. ¬ evaluate q ((x, b) # ρ')" 
        by (metis (full_types))

      {
        assume "x ∈ domain ρ"
        then obtain b' where "(x,b') ∈ set ρ" using domain_def by force
        hence "set ρ = set ((x,b') # filter (λkv. fst kv ≠ x) ρ)" 
          using eq_key_imp_eq_value `wf_valuation ρ` wf_valuation_def by fastforce
        hence "¬ evaluate q ρ" using evaluate_on_permuted_valuation ** ρ'_def by blast
      } 
      moreover {
        assume "x ∉ domain ρ"
        hence "ρ' = ρ" unfolding ρ'_def domain_def 
          by (metis (mono_tags, lifting) filter_True image_eqI list.set_map)
        hence "⋀b. ¬ evaluate q ((x, b) # ρ)" using ** by blast
        hence "¬ evaluate q ρ" using evaluate_on_larger_valuation 
          by (metis set_subset_Cons)
      }
      ultimately have "¬ evaluate q ρ" by blast
    }
    thus ?thesis by simp
  qed
qed


  

end