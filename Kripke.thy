theory Kripke 
  imports 
    "HOL-Library.Countable"
begin

datatype ('i, 's, 'a) kripke = Kripke (\<pi>: \<open>'s \<Rightarrow>'a \<Rightarrow> bool\<close>) (\<K>: \<open>'i \<Rightarrow> 's \<Rightarrow> 's set\<close>)
end