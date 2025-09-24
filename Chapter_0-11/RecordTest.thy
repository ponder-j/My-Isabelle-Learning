theory RecordTest
  imports Main
begin

record coord2d = Xpt :: int
                 Ypt :: int
term Xpt
(* "Xpt" :: "'a coord2d_scheme \<Rightarrow> int" *)

definition coord1 :: "coord2d"
  where "coord1 \<equiv> \<lparr>Xpt = 20, Ypt = 30\<rparr>"
(* consts coord1 :: "coord2d" *)

value "Xpt coord1"

definition coord1' :: "coord2d"
  where "coord1' \<equiv> coord1\<lparr>Ypt := 50\<rparr>"

value "coord1'"
(* "\<lparr>Xpt = 20, Ypt = 50\<rparr>" :: "coord2d" *)

definition incX :: "coord2d \<Rightarrow> coord2d"
  where "incX r \<equiv> r\<lparr>Xpt := Xpt r + 1\<rparr>"

value "incX coord1"
(* "\<lparr>Xpt = 21, Ypt = 30\<rparr>" :: "coord2d" *)

record coord3d = coord2d + Zpt :: int

definition coord3 :: "coord3d"
  where "coord3 \<equiv> \<lparr>Xpt = 20, Ypt = 30, Zpt = 40\<rparr>"

value "Zpt coord3"

definition coord3' :: "coord3d"
  where "coord3' \<equiv> coord3\<lparr>Zpt := 50\<rparr>"

value "coord3'"

record coord4d = coord3d + Time :: int
definition coord4 :: "coord4d"
  where "coord4 \<equiv> \<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000\<rparr>"

value "coord4"

value "\<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000 \<rparr>"
(* 输出 \<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000\<rparr> :: coord4d *)
value "coord4d.make 20 30 40 1000"
(* 输出 \<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000\<rparr> :: coord4d *)

term Time
(* 输出 Time :: 'a coord4d_scheme \<Rightarrow> int *)
definition "coord5 \<equiv> coord4d.extend coord4 (True)"
value "coord5"
(* 输出\<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000, \<dots> = True\<rparr> :: "bool coord4d_scheme” *)
value "more coord5"
(* 输出 True :: bool *)
value "coord2d.more coord4"
(* 输出 \<lparr>Zpt = 40, Time = 1000\<rparr>:: \<lparr>Zpt :: int, Time :: int\<rparr>*)
value "coord3d.more (coord3d.extend coord3 ''hello'')"
(* 输出 ''hello'' :: "char list" *)

value "coord2d.truncate coord3"
(* 输出 \<lparr>Xpt = 20, Ypt = 30\<rparr>:: coord2d *)
value "coord3d.fields 100"
(* 输出 \<lparr>Zpt = 100\<rparr>:: \<lparr>Zpt :: int\<rparr>*)
value "coord4d.fields 200"
(* 输出 \<lparr>Time = 200\<rparr>:: \<lparr>Time :: int\<rparr>*)
value "coord2d.extend coord1 (coord3d.fields 50)"
(* 输出 \<lparr>Xpt = 20, Ypt = 30, Zpt = 50\<rparr>:: coord3d *)

end