theory Temp_Logic 
  imports 
    "HOL-Library.Countable"
    HOL.Transitive_Closure
    Kripke
begin

  (*  Epistemic_Logic *)


section \<open>Syntax\<close>

datatype 'a temporal_prop =
        Prev \<open>'a temporal_prop\<close>
      | Now \<open>'a\<close>
      | Since \<open>'a temporal_prop\<close> \<open>'a temporal_prop\<close>
        (*  (infixr "since" 20) (* less than implication *) *)

end
