theory test
  imports Main
begin

definition a :: nat where "a = 1"
definition alist where "alist = [1,2,3]"

value "(+) a a"

value "map (\<lambda>x::nat. 2 * x) alist"

fun add :: "nat => nat => nat" where
  "add 0 n = n"
|  "add (Suc m) n = Suc (add m n)"

lemma add_02: "add m 0 = m"
  apply (induction m)
  apply simp+
  done

thm add_02



end