theory gcdEuclid
  imports Main
begin

function gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gcd x 0 = x" |
        "gcd 0 y = y" |
        "x < y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (Suc x) (y - x)" |
        "x \<ge> y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (x - y) (Suc y)"

  value "gcd 5 15"

end