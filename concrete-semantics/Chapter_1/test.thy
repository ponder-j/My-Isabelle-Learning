theory test
  imports Main
begin

definition aa :: nat where "aa = 1"
definition alist where "alist = [1,2,3]"

value "(+) aa aa"

value "map (\<lambda>x::nat. 2 * x) alist"

fun add :: "nat => nat => nat" where
  "add 0 n = n"
|  "add (Suc m) n = Suc (add m n)"

lemma add_02: "add m 0 = m"
  apply (induction m)
  apply simp+
  done

thm add_02

lemma add_03: "add m 0 = m"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  fix m
  assume IH: "add m 0 = m"
  hence "add (Suc m) 0 = Suc (add m 0)" by simp
  also have "… = Suc m" by (simp add: IH)
  then show "add (Suc m) 0 = Suc m" by simp
qed

end