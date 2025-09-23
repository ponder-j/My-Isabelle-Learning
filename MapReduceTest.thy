theory MapReduceTest
  imports Main
begin

definition MapReduce :: 
  "'a list \<Rightarrow> 
    ('a \<Rightarrow> ('k1 \<times>'v1) list) \<Rightarrow> 
    (('k1 \<times>'v1) list list \<Rightarrow> ('k2 \<times> ('v2 list)) list) \<Rightarrow> 
    (('k2 \<times> ('v2 list)) \<Rightarrow> ('k2 \<times> 'v2)) \<Rightarrow> 
    ('k2 \<times> 'v2) list"
  where "MapReduce input m s r \<equiv> map r (s (map m input))"

type_synonym webpage= "string list"

primrec countword :: 
  "string \<Rightarrow> (string \<times> nat) list \<Rightarrow> (string \<times> nat) list"
  where "countword s [] = [(s,1)]" |
         "countword s (x # xs) = 
            (if fst x = s then (fst x, snd x + 1) # xs 
             else x # (countword s xs))"

primrec countwebpage :: 
  "webpage \<Rightarrow> (string \<times> nat) list \<Rightarrow> (string \<times> nat) list"
  where "countwebpage [] kvs = kvs" |
        "countwebpage (x # xs) kvs = 
            (let kvs1 = countword x kvs in countwebpage xs kvs1)"

definition mapper :: "webpage \<Rightarrow> (string \<times> nat) list"
  where "mapper a \<equiv> countwebpage a []"

primrec shuffword :: 
  "(string \<times> nat) \<Rightarrow> (string \<times> (nat list)) list 
                     \<Rightarrow> (string \<times> (nat list)) list"
  where "shuffword kv [] = [(fst kv, [snd kv])]" |
        "shuffword kv (x # xs) = 
            (if fst kv = fst x then (fst x, (snd kv) # (snd x))#xs 
             else x # (shuffword kv xs))"

primrec shuffwords :: 
  "(string \<times> nat) list \<Rightarrow> (string \<times> (nat list)) list 
                           \<Rightarrow> (string \<times> (nat list)) list"
  where "shuffwords [] kvs = kvs" |
        "shuffwords (x # xs) kvs = shuffwords xs (shuffword x kvs)"

primrec shuffall :: 
  "(string \<times> nat) list list \<Rightarrow> (string \<times> (nat list)) list 
                                 \<Rightarrow> (string \<times> (nat list)) list"
  where "shuffall [] kvs = kvs" |
         "shuffall (x # xs) kvs = shuffall xs (shuffwords x kvs)"

definition "shuff l \<equiv> shuffall l []"

fun reducer :: "string \<times> (nat list) \<Rightarrow> (string \<times> nat)"
  where "reducer (k,vlist) = (k, foldl plus 0 vlist)"

fun split_aux :: "char list \<Rightarrow> char list \<Rightarrow> char list list"
  where "split_aux [] acc = (if acc = [] then [] else [rev acc])" |
        "split_aux (c # cs) acc = 
          (if c = CHR 32
           then (if acc = [] then split_aux cs acc
                 else rev acc # split_aux cs [])
           else split_aux cs (c # acc))"

definition split :: "char list \<Rightarrow> char list list"
  where "split str = split_aux str []"

definition webpages :: "webpage list"
  where "webpages \<equiv> [split ''Dear Bear River'',
                         split ''Car Car River'',
                         split ''Dear Car Bear'']"

value "webpages"
value "map mapper webpages"
value "shuff (map mapper webpages)"
value "MapReduce webpages mapper shuff reducer"

end