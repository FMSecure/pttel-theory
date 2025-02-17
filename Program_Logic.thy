(*
  File:     
  Author: 

*)

theory Program_Logic 
  imports 
    Program_Model
    Program_Expressions
    Temp_Logic
    HOL.String
begin



section \<open>Syntax\<close>

(* 'q is an atomic proposition
   'i is identity of an agent
 *)

datatype ('tid,'l) pfm  =
           At 'tid 'l ("_ at _" [100,100] 100)
        |  Active 'tid ("_ active" [100] 100)
        |  Said 'tid richexpr richexpr ("_ said _ = _" [100,100,100] 100) (* Note: why not says? *)
        |  LReadEvent \<open>'tid\<close> richexpr richexpr ("_ : _ \<lhd> _" [100,100,100] 100)
        |  LWriteEvent \<open>'tid\<close> richexpr richexpr ("_ : _ \<rhd> _"[100,100,100] 100)


section \<open>Semantics\<close>

type_synonym ('tid1,'tid2) id_interp = "'tid1 \<Rightarrow> 'tid2"

end
