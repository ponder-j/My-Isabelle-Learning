theory HOFList
  imports Main
begin

primrec map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
  where "map f [] = []" |
        "map f (x # xs) = f x # map f xs"

primrec filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "filter f [] = []" |
        "filter f (x # xs) = 
            (if f x then x # (filter f xs) 
             else filter f xs)"

primrec foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
  where "foldl f a [] = a" |
        "foldl f a (x # xs) = foldl f (f a x) xs"

(* primrec foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b"
  where "foldr f [] = id" |
        "foldr f (x # xs) = f x \<circ> foldr f xs" *)

value "foldl plus 0 [5::int, 2, 1]"
value "foldr plus [5::int, 2, 1] 0"
thm foldr.simps

end