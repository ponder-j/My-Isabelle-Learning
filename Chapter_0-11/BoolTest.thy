theory BoolTest
  imports Main
begin

value "True \<and> False"
value "True \<or> False"
value "True \<rightarrow> False"
definition "TRUE \<equiv> True "
definition "FALSE \<equiv> False"
definition "A \<equiv> TRUE \<and> FALSE"
value A

end