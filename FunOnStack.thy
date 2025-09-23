theory FunOnStack
  imports Main
begin

type_synonym 'a stack = "'a list"

fun search0 :: "'a stack \<Rightarrow> 'a \<Rightarrow> (int \<times> int)"
  where "search0 [] a = (-1, -1)" |
         "search0 (x#xs) a = 
            (if x = a then (0,0) else 
                let idx = search0 xs a in
                  (1 + fst idx, snd idx))"

definition "search st a \<equiv> 
              (let idx = search0 st a in
                  if snd idx = -1 then -1 
                  else fst idx)"

value "search [1::int,2,3,4,5] 4"
(* 输出 "a" :: "'a" *)

end