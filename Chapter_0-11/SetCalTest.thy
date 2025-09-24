theory SetCalTest
  imports Main
begin

abbreviation Set7 :: "nat set"
  where "Set7 \<equiv> {1,2,3,4,5}"

abbreviation Set8 :: "nat set"
  where "Set8 \<equiv> {4,5,6,7,8}"

value "Set7 \<inter> Set8"
(* 输出 "{4, 5}" :: "nat set" *)
value "Set7 \<union> Set8"
(* 输出 "{1, 2, 3, 4, 5, 6, 7, 8}" :: "nat set" *)
value "Set7 - Set8"
(* 输出 "{1, 2, 3}" :: "nat set" *)
value "- Set7"
(* 输出 "List.coset [1, 2, 3, 4, 5]":: "nat set" *)

abbreviation Set9 :: "nat set"
  where "Set9 \<equiv> {1,2,3}"

abbreviation Set10 :: "nat set"
  where "Set10 \<equiv> {4,5,6}"

value "Set9 \<times> Set10"
(* 输出 "{(1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6)}" :: "(nat \<times> nat) set" *)
value "card (Set9 \<times> Set10)"
(* 输出 "9" :: "nat" *)

abbreviation Set11 :: "char list set"
  where "Set11 \<equiv> {''a'', ''b''}"

value "Set9 \<times> Set10 \<times> Set11"
(* 输出 "{(1, 4, ''a''), (1, 4, ''b''), (1, 5, ''a''), (1, 5, ''b''), 
		  (1, 6, ''a''), (1, 6, ''b''), (2, 4, ''a''), (2, 4, ''b''), 
          (2, 5, ''a''), (2, 5, ''b''), (2, 6, ''a''), (2, 6, ''b''), 
          (3, 4, ''a''), (3, 4, ''b''), (3, 5, ''a''), (3, 5, ''b''), 
          (3, 6, ''a''), (3, 6, ''b'')}"  :: "(nat \<times> nat \<times> char list) set" *)

value "card (Set9 \<times> Set10 \<times> Set11)"
(* 输出 "18" :: "nat" *)

value "Pow Set9"
(* 输出 "{{}, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}}" :: "nat set set" *)

end