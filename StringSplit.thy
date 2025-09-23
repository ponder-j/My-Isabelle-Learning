theory StringSplit
  imports Main
begin

(* 定义空格字符 *)
definition space :: "char" 
  where "space = CHR '' ''"

(* 判断字符是否为空格 *)
definition is_space :: "char \<Rightarrow> bool" 
  where "is_space c \<equiv> (c = space)"

(* 跳过字符列表开头的所有空格 *)
fun skip_spaces :: "char list \<Rightarrow> char list" 
  where
    "skip_spaces [] = []" |
    "skip_spaces (c # cs) = (if is_space c then skip_spaces cs else c # cs)"

(* 从字符列表开头取出一个单词(直到遇到空格或结束) *)
fun take_word :: "char list \<Rightarrow> char list" 
  where
    "take_word [] = []" |
    "take_word (c # cs) = (if is_space c then [] else c # take_word cs)"

(* 跳过字符列表开头的一个单词 *)
fun drop_word :: "char list \<Rightarrow> char list" 
  where
    "drop_word [] = []" |
    "drop_word (c # cs) = (if is_space c then c # cs else drop_word cs)"

(* 将字符列表分割成字符串列表 *)
fun split_chars :: "char list \<Rightarrow> string list" 
  where
    "split_chars [] = []" |
    "split_chars cs = (
      let cs_no_leading_spaces = skip_spaces cs in
      if cs_no_leading_spaces = [] then []
      else
        let word = take_word cs_no_leading_spaces in
        let remaining = drop_word cs_no_leading_spaces in
        (String.implode word) # split_chars remaining
    )"

(* 主要的字符串分割函数 *)
definition split :: "string \<Rightarrow> string list" 
  where "split s \<equiv> split_chars (String.explode s)"

(* 一些基本的引理来帮助证明 *)
lemma split_empty: "split '''' = []"
  by (simp add: split_def)

lemma split_single_word: "split ''hello'' = [''hello'']"
  by (simp add: split_def space_def is_space_def)

(* 导出一些有用的引理 *)
lemma is_space_char: "is_space (CHR '' '') = True"
  by (simp add: is_space_def space_def)

lemma not_is_space_letter: "\<not>is_space (CHR ''a'')"
  by (simp add: is_space_def space_def)

(* 辅助函数：判断字符串是否只包含空格 *)
definition all_spaces :: "string \<Rightarrow> bool"
  where "all_spaces s \<equiv> \<forall>c \<in> set (String.explode s). is_space c"

(* 辅助函数：去除字符串两端的空格 *)
definition trim :: "string \<Rightarrow> string"
  where "trim s \<equiv> String.implode (skip_spaces (String.explode s))"

end