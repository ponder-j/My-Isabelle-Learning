theory Task1_2sqrt2nrat
  imports Complex_Main
begin

(* Task 1 : Prove that 2sqrt(2) is irrational *)
theorem task1: "2 * sqrt 2 ∉ ℚ"
(* 反证法可以使用 (rule ccontr) *)
hammerit

end