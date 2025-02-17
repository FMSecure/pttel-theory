theory Program_Model
  imports Main
begin

(* Derived from  	
A Correctness Proof for the Volpano/Smith Security Typing System
Authors: 	Gregor Snelting and Daniel Wasserrab
https://www.isa-afp.org/entries/VolpanoSmith.html
Therefore, BSD Licenced
*)

section \<open>The Language\<close>

subsection \<open>Variables and Values\<close>

type_synonym vname = string \<comment> \<open>names for variables\<close>

type_synonym val = int (* TODO change to word. NOTE 0 is false, everything else is true *)

subsection \<open>Expressions and Commands\<close>

datatype bop = Eq | And |  Less | Add | Sub     \<comment> \<open>names of binary operations\<close>

datatype expr
  = Val val                   \<comment> \<open>value\<close>
  | Deref vname               \<comment> \<open>dereferencing\<close>
  | Var vname                 \<comment> \<open>local variable\<close>
  | BinOp vname bop vname     \<comment> \<open>binary operation\<close>


text \<open>Note: we assume that only type correct expressions are regarded
  as later proofs fail if expressions evaluate to None due to type errors.
  However there is [yet] no typing system\<close>

fun binop :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val"
where "binop Eq v\<^sub>1 v\<^sub>2               = (if v\<^sub>1 = v\<^sub>2 then 1 else 0)"
| "binop And v1 v2               =  (if v1 \<noteq> 0 \<and> v2 \<noteq> 0 then 1 else 0)" 
  | "binop Less i\<^sub>1 i\<^sub>2 = (if i\<^sub>1 < i\<^sub>2 then 1 else 0)"
  | "binop Add i\<^sub>1 i\<^sub>2  = (i\<^sub>1 + i\<^sub>2)"
  | "binop Sub i\<^sub>1 i\<^sub>2  = (i\<^sub>1 - i\<^sub>2)"


(* 'l is label, usually N *)
datatype ('l) auxcom
  = 
    Read vname expr \<open>'l * ('l auxcom)\<close> ("_ \<lhd> _;//_")
  | Write vname vname \<open>'l * ('l auxcom)\<close> ("_ \<rhd> _;//_") (* write value of lhs var to address that is value of rhs *)
  | Cond vname \<open>'l * ('l auxcom)\<close> \<open>'l * ('l auxcom)\<close>  ("if _ {(1//_//})//else{(1//_//})" [80,79,79] 70)
  | While vname \<open>'l * ('l auxcom)\<close> \<open>'l * ('l auxcom)\<close> ("while _ {(1//_//})//_" [80,79,70] 70)        
  | Skip

value "while vname 
       {(1, Read vname (Val 1) (2,Skip))}
       (1, Read vname (Val 1) (3,Skip))"

type_synonym ('l) com = \<open>'l * ('l auxcom)\<close>

fun fv :: "expr \<Rightarrow> vname set" \<comment> \<open>free variables in an expression\<close>
where
  FVc: "fv (Val V) = {}"
  | FVv: "fv (Var V) = {V}"
  | FVe: "fv (BinOp V1 bop V2) = {V1,V2}"
  | FVd: "fv (Deref V) = {V}"

subsection \<open>State\<close>

type_synonym vassign = "vname \<Rightarrow> val"

type_synonym ('tid,'l) lstate = "'tid * 'l com * vassign" 

type_synonym sharedres = "val \<Rightarrow> val"

datatype ('tid) event 
  = EmptyEvent ("\<epsilon>")
  | ReadEvent \<open>'tid\<close> val val 
  | WriteEvent \<open>'tid\<close> val val

(* No interpretation function, as memory access within an expression need to be reflected in 
   events. That's why conditions are registers, otherwise the small step function would be more tedious.*)


fun exp_interpret :: "expr \<Rightarrow> vassign \<Rightarrow> sharedres \<Rightarrow> val" ("\<lbrakk>_\<rbrakk>_ _")
where Val: "(\<lbrakk>Val v\<rbrakk> _ _) = v"
    | Var: "(\<lbrakk>Var V\<rbrakk> r _) = (r V)"
    | BinOp: "(\<lbrakk>BinOp V1 bop V2\<rbrakk> r s) = (binop bop (r V1) (r V2))" 
    | Deref: "(\<lbrakk>Deref V\<rbrakk> r s) = (s (r V))"


subsection \<open>Small Step Semantics\<close>

fun nxt :: "('tid,'l) lstate * sharedres \<Rightarrow> (('tid,'l) lstate * sharedres * 'tid event)"
  where 
  ReadVal: "nxt ((\<tau>, (l,(Rn \<lhd> Val w; c)), r), \<sigma>) = ((\<tau>, c, r(Rn := \<lbrakk>Val w\<rbrakk> r \<sigma>)), \<sigma>, \<epsilon>)"
| ReadVar: "nxt ((\<tau>, (l,(Rn \<lhd> Var V; c)), r), \<sigma>) = ((\<tau>, c, r(Rn := \<lbrakk>Var V\<rbrakk> r \<sigma>)), \<sigma>, \<epsilon>)"
| ReadOpL: "nxt ((\<tau>, (l,(Rn \<lhd> BinOp V1 bop V2; c)), r), \<sigma>) = ((\<tau>, c, r(Rn := \<lbrakk>BinOp V1 bop V2\<rbrakk> r \<sigma>)), \<sigma>, \<epsilon>)"
| ReadMem: "nxt ((\<tau>, (l,(Rn \<lhd> Deref V; c)), r), \<sigma>) = ((\<tau>, (l,Rn \<lhd> Val (\<lbrakk>Deref V\<rbrakk> r \<sigma>); c),r), \<sigma>, ReadEvent \<tau> (\<lbrakk>Deref V\<rbrakk> r \<sigma>) (\<lbrakk>Var V\<rbrakk> r \<sigma>))"
| WriteMem: "nxt ((\<tau>, (l,(Rn \<rhd> V; c)), r), \<sigma>) = ((\<tau>, c,r), \<sigma>(\<lbrakk>Var V\<rbrakk> r \<sigma> := r Rn), WriteEvent \<tau> (\<lbrakk>Var V\<rbrakk> r \<sigma>) (r Rn))"
| Cond: "nxt ((\<tau>, (l,(Cond Rn c1 c2)), r), \<sigma>) = ((\<tau>, if (r Rn = 0) then c2 else c1,r), \<sigma>, \<epsilon>)" (* NOTE: inner if is meta language *)
| While: "nxt ((\<tau>, (l,(While Rn c c')), r), \<sigma>) = ((\<tau>, 
       if (r Rn = 0) then c' else (l,while Rn { c } c')
      ,r), \<sigma>, \<epsilon>)"
| Skip: "nxt ((\<tau>, (l,Skip), r), \<sigma>) = ((\<tau>, (l,Skip), r), \<sigma>, \<epsilon>)"

type_synonym ('tid,'l) systemstate = "('tid \<Rightarrow> ('tid,'l) lstate) * sharedres * 'tid event"

inductive red :: "('tid \<Rightarrow> ('tid,'l) lstate) \<Rightarrow> sharedres \<Rightarrow> ('tid \<Rightarrow> ('tid,'l) lstate) \<Rightarrow> sharedres \<Rightarrow> 'tid event \<Rightarrow> bool"
   ("((1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_,/_\<rangle>))" [0,0,0,0,0] 81)
 (*  ("\<langle>_,_\<rangle> \<rightarrow> \<langle>_,_,_\<rangle>" [0,0,0,0,0] 81) *)
   where
  "\<exists> tid . 
      let \<delta>=\<Delta>(tid) in
       nxt(\<delta>,\<sigma>) = (\<delta>',\<sigma>',ev)
      \<Longrightarrow>
       \<langle>\<Delta>,\<sigma>\<rangle> \<rightarrow> \<langle>\<Delta>(tid:=\<delta>'),\<sigma>',ev\<rangle>"

lemmas red_induct = red.induct[split_format (complete)]

(*
type_synonym ('tid,'l) run = "nat \<Rightarrow> ('tid,'l) systemstate" (* NOTE could define as dependent type to make sure always connected by red *)
*)
type_synonym ('tid,'l) run = "(('tid,'l) systemstate) list" (* NOTE could define as dependent type to make sure always connected by red *)


fun cmd :: "('tid,'l) systemstate \<Rightarrow> 'tid \<Rightarrow> 'l com"
  where
    "cmd  (\<Delta>,_,_) tid = (let (_,c,_) = \<Delta>(tid) in c)"

fun getEvent :: \<open>('tid,'l) run \<Rightarrow> nat \<Rightarrow> 'tid event\<close> 
  where
 "getEvent \<pi> i = (let (_,_,e) = \<pi> ! i in e)"
(*  "getEvent \<pi> i = (let (_,_,e) = \<pi> i in e)"
*)

fun undefinedFunction 
  where
    "undefinedFunction x = (Eps (\<lambda>y. True))"

definition initSystem :: "('l com) list \<Rightarrow> (nat,'l) systemstate"
  where "initSystem list = (
      let localstate = \<lambda> i.
          (i, list ! i, undefinedFunction)
      in
         (localstate, undefinedFunction, \<epsilon>)
     )
 "

type_synonym label = nat
type_synonym natcom = \<open>nat com\<close>
type_synonym natsystemstate = "(nat,nat) systemstate"


fun hist:: "('tid,'l) run \<Rightarrow> 'tid \<Rightarrow> (('tid,'l) lstate)list" 
  where
  "hist \<Pi> \<tau> = map (\<lambda>(\<Delta>,_,_). \<Delta> \<tau>)  \<Pi>"

end
