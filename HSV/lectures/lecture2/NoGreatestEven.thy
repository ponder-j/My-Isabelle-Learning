theory NoGreatestEven
    imports Complex_Main
begin

(* 命题表述：对于任意整数 n，如果 n 是偶数，则存在一个偶数 m，使得 m > n。 *)
theorem "∀n::int. even n ⟶ (∃m. even m ∧ m > n)"
(* by (metis even_add zless_add1_eq) 利用 sledgehammer 一句话证明 *)

(* 结构化证明 *)
(* 需要把原命题中的 ⟶ 转成 ⟹, 这个需要用到 clarify *)
proof clarify
    fix n::int
    assume "even n"
    hence "even (n + 2)" by simp
    hence "n < n + 2" by simp
    thus "∃m. even m ∧ m > n"
        using ‹even (n + 2)› by blast
qed

end

    