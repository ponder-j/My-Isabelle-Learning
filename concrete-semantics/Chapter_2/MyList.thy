theory MyList
  imports Main
begin

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list ⇒ 'a list" where
  "rev Nil = Nil"
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"
value "rev (Cons a (Cons b Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
  by auto

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  apply (simp)
  sledgehammer



theorem rev_rev [simp]: "rev (rev xs) = xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  fix x1 xs
  assume IH: "rev (rev xs) = xs"
  (* rev (rev (Cons x1 xs)) = Cons x1 xs *)
  then show ?case sorry
qed

end