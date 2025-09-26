theory StateMonadInsertSort
  imports Main "HOL-Library.State_Monad" "HOL-Library.Monad_Syntax"
begin

definition return :: "'a ⇒ ('s, 'a) state"
  where "return x = State (λs. (x, s))"

definition swap :: "'a list ⇒ nat ⇒ nat ⇒ 'a list"
  where "swap l i j ≡ (let temp = l ! i in (l[i := l ! j])[j := temp])"

fun insert :: "('a::linorder) list ⇒ nat ⇒ (('a::linorder) list, ('a::linorder) list) state"
  where
    "insert l i =
      (if i ≠ 0 ∧ l!i < l!(i-1) then
        do {
          l1 ← return (swap l (i-1) i);
          insert l1 (i - 1)
        }
      else
        return l)"

function isort :: "('a :: linorder) list ⇒ nat ⇒ (('a :: linorder) list, ('a :: linorder) list) state"
  where "isort l i =
    (if i < length l then
      do {
        l' ← insert l i;
        isort l' (i + 1)
      }
    else
      return l)"
  by pat_completeness auto

termination isort
  by (relation "measure (λ(l, i). length l - i)") auto

value "(run_state (isort ([1::int, 0, 2, 8, 4, 3, 6, 2]) 1) [])"