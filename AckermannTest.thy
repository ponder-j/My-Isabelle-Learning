theory AckermannTest
  imports Main
begin

fun ack :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "ack 0 n = Suc n" |
        "ack (Suc m) 0 = ack m 1" |
        "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"

value "ack 3 3"
(* "61" :: "nat" *)

end