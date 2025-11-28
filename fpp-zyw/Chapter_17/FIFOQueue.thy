theory FIFOQueue
  imports Main
begin

type_synonym 'a queue = "'a list"

fun enqueue :: "'a queue ⇒ 'a ⇒ 'a queue" 
where "enqueue xs x = x # xs"

fun dequeue :: "'a queue ⇒ ('a × 'a queue)" 
where "dequeue xs = (last xs, butlast xs)"

definition isempty :: "'a queue ⇒ bool" 
where "isempty q ≡ (q = [])"

abbreviation "emptyq ≡ []"

end