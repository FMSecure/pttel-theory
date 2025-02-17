theory Program_Expressions
  imports 
    Program_Model
    HOL.String
begin

datatype richexpr
  = RVal val                        ("#_"     [112] 112)      \<comment> \<open>value\<close>
  | RArray vname val          ("_.'[_']"      [111] 111)      \<comment> \<open>dereferencing\<close>
  | RVar vname                ("$_"     [110] 111)              \<comment> \<open>local variable\<close>
  | REq richexpr  richexpr    ("_ === _" [110,111] 110)  \<comment> \<open>binary operation\<close>
  | RBinOp richexpr bop richexpr    ("_ \<guillemotleft>_\<guillemotright> _" [110,110,110] 110)  \<comment> \<open>binary operation\<close>
  | TRUE (* "value representing true" *)
  | FALSE (* "value representing false" *)


end
