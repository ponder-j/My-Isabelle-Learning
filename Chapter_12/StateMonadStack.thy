theory StateMonadStack
imports Main "HOL-Library.State_Monad" "HOL-Library.Monad_Syntax"
begin
    definition return :: "'a ⇒ ('s, 'a) state" where
        "return x = State (λs. (x, s))"

    type_synonym 'v stack = "'v list"

    definition pop :: "('v stack, 'v option) state"
        where "pop ≡ State (λs. case s of [] ⇒ (None, []) | 
                                        (x#xs) ⇒ (Some x, xs))"
    definition push :: "'v ⇒ ('v stack, 'v option) state"
        where "push v ≡ State (λs. case s of [] ⇒ (None, [v]) | 
                                        (x#xs) ⇒ (None, v#x#xs))"
    primrec pushn :: "'v list ⇒ ('v stack, 'v option) state"
        where
            "pushn [] = return None" |
            "pushn (x#xs) = do {
                push x;
                pushn xs
            }"

    value "run_state (pushn [1::int, 2, 3, 4, 5]) []"
    value "run_state (pushn [1::int, 2, 3, 4, 5]) [0, 1, 0]"

    primrec popn :: "nat ⇒ ('v stack, ('v option) list) state"
        where
            "popn 0 = State_Monad.return []" |
            "popn (Suc n) = do {
                a ← pop;
                as ← popn n;
                return (a#as)
            }"
    value "run_state (popn 5) [0, 1::int, 2, 3, 4, 5, 6]"
    value "run_state (do {
        pushn [1::int, 2, 3, 4, 5];
        popn 4
    }) []"
end