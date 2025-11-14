theory Prog3
imports Main Prog1 Prog2
begin
    (* 默认使用后导入的定义 *)
    value "sub 1 2"
    (* 指定使用某个文件中的定义 *)
    value "Prog1.sub 1 2"
    value "Prog2.sub 1 2"
end