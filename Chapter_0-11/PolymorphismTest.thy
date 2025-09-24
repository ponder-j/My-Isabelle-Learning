theory PolymorphismTest
  imports Complex_Main
begin

record 'a Coord3d = xpos :: 'a
                    ypos :: 'a
                    zpos :: 'a

record 'a Coord4d = "'a Coord3d" + Time :: 'a

definition coord6 :: "int Coord3d"
  where "coord6 \<equiv> \<lparr>xpos = 10, ypos = 20, zpos = 30\<rparr>"

definition coord7 :: "real Coord3d"
  where "coord7 \<equiv> \<lparr>xpos = 10.0, ypos = 20.0, zpos = 30.0\<rparr>"

value "Coord3d.extend coord6 ''hello''"
value "Coord3d.extend coord7 ''good''"

datatype 'a array = Null | Conn 'a "'a array"("_,_")

primrec length :: "'a array \<Rightarrow> nat"
  where "length Null = 0" |
        "length (Conn a arr) = 1 + length arr"

primrec nth :: "'a array \<Rightarrow> nat \<Rightarrow> 'a"("_[_]")
  where "nth (Conn a arr) i = (case i of 0 \<Rightarrow> a | Suc k \<Rightarrow> nth arr k)"

primrec array_update :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array" ("_[_] := _")
  where "array_update (Conn a arr) i v = 
         (case i of 0 \<Rightarrow> Conn v arr |
                Suc j \<Rightarrow> Conn a (array_update arr j v))"

definition arr1 :: "int array"
  where "arr1 \<equiv> (1,2,3,Null)"

value "arr1[2]"
(* 输出 "3" :: "int"*)
value "length arr1"
(* 输出 "3" :: "nat"*)
value "arr1[2] := 10"
(* 输出 "1,2,10,Null" :: "int array"*)

definition arr2 :: "string array"
  where "arr2 \<equiv>(''hello'', ''world'', ''next'', ''word'', Null)"

value "arr2[1]"
value "arr2[0]"

value "arr2[0] := ''hi''"

end