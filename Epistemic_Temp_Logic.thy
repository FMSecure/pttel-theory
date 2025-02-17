(*
  File:      Epistemic_Logic.thy
  Author:    Andreas Halkjær From

  This work is a formalization of epistemic logic with countably many agents.
  It includes proofs of soundness and completeness for the axiom system K.
  The completeness proof is based on the textbook "Reasoning About Knowledge"
  by Fagin, Halpern, Moses and Vardi (MIT Press 1995).

  Modified by Hamed Nemati and Robert Künnemann and Yufei Liu:
*)

theory Epistemic_Temp_Logic
  imports 
    "HOL-Library.Countable"
    Program_Logic
begin

section \<open>Syntax\<close>

datatype ('i, 'a) fm
  = FF ("\<^bold>\<bottom>")
  | Pro 'a ("pro _" [90] 90)
  | Con \<open>('i,'a) fm\<close> \<open>('i,'a) fm\<close> (infixr "\<^bold>\<and>" 65)
  | Imp \<open>('i,'a) fm\<close> \<open>('i,'a) fm\<close> (infixr "\<^bold>\<longrightarrow>" 55)
  | K 'i \<open>('i,'a) fm\<close> (infixr "knows" 80)
  | Prev \<open>('i, 'a) fm\<close> ("prev _" [70] 70)
  | Since \<open>('i,'a) fm\<close> \<open>('i,'a) fm\<close> (infixr "since" 50)

abbreviation TT ("\<^bold>\<top>") where
  \<open>TT \<equiv> \<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Neg ("\<^bold>\<not> _" [75] 75) where
  \<open>Neg p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Dis (infixr "\<^bold>\<or>" 60) where
  \<open>(p \<^bold>\<or> q) \<equiv> \<^bold>\<not> (\<^bold>\<not> p \<^bold>\<and> \<^bold>\<not> q)\<close>

abbreviation Equiv (infixr "\<^bold>\<longleftrightarrow>"  55) where
  \<open>p \<^bold>\<longleftrightarrow> q \<equiv> (p \<^bold>\<longrightarrow> q) \<^bold>\<and> (q \<^bold>\<longrightarrow> p)\<close>

section \<open>Semantics\<close>
(* 's is world, so in our case a system state
 , 'a is the type of proposition, and
   'i is agent TODO change later
   
   \<pi> M s prop iff prop holds true in world/state s
   \<K> M i s gives all successor states of s for agent i
*)

datatype ('i, 's, 'a) kripke = Kripke (\<pi>: \<open>'s \<Rightarrow>'a \<Rightarrow> bool\<close>) (\<K>: \<open>'i \<Rightarrow> 's \<Rightarrow> 's set\<close>)

(* Define semantics using a combination of two kripke structures,
   see program_logic, to how we can generate them from program states
*)

primrec semantics :: \<open>('i, 's, 'a) kripke \<Rightarrow> 's \<Rightarrow> ('i, 'a) fm \<Rightarrow> bool\<close>
  ("_, _ \<Turnstile> _" [50,50] 50) where
  \<open>(_, _ \<Turnstile> \<^bold>\<bottom>) = False\<close>
| \<open>(M, s \<Turnstile> Pro prop) = \<pi> M s prop\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<and> q)) = ((M, s \<Turnstile> p) \<and> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<longrightarrow> q)) = ((M, s \<Turnstile> p) \<longrightarrow> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> K i p) = (\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p)\<close>
| \<open>(M, s \<Turnstile> Prev p) = (\<forall> t i. s \<in> \<K> M i t \<and>  M, t \<Turnstile> p )\<close>

section \<open>Utility\<close>

abbreviation reflexive :: \<open>('i, 's, 'a) kripke \<Rightarrow> bool\<close> where
  \<open>reflexive M \<equiv> \<forall>i s. s \<in> \<K> M i s\<close>

abbreviation symmetric :: \<open>('i, 's, 'a) kripke \<Rightarrow> bool\<close> where
  \<open>symmetric M \<equiv> \<forall>i s t. t \<in> \<K> M i s \<longleftrightarrow> s \<in> \<K> M i t\<close>

abbreviation transitive :: \<open>('i, 's, 'a) kripke \<Rightarrow> bool\<close> where
  \<open>transitive M \<equiv> \<forall>i s t u. t \<in> \<K> M i s \<and> u \<in> \<K> M i t \<longrightarrow> u \<in> \<K> M i s\<close>

(*
lemma Imp_intro: \<open>(M, s \<Turnstile> p \<Longrightarrow> M, s \<Turnstile> q) \<Longrightarrow> M, s \<Turnstile> Imp p q\<close>
  by simp
*)


section \<open>Axiom System K\<close>

(* Note: compared to eval in Epistemic_Logic, we removed g *)
primrec eval :: \<open>(('i,'a) fm \<Rightarrow> bool) \<Rightarrow> ('i,'a) fm \<Rightarrow> bool\<close> where
  \<open>eval _ \<^bold>\<bottom> = False\<close>
| \<open>eval h (Pro i) = h (Pro i)\<close>
| \<open>eval h (K i p) = h (K i p)\<close>
| \<open>eval h (Prev p) = h (Prev p)\<close>
| \<open>eval h (p since q) = h (p since q)\<close>
| \<open>eval h (p \<^bold>\<and> q) = (eval h p \<and> eval h q)\<close>
| \<open>eval h (p \<^bold>\<longrightarrow> q) = (eval h p \<longrightarrow> eval h q)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>h. eval h p\<close>

abbreviation LPrev ("lprev _ _" [70, 70] 70) where
  \<open>LPrev A p \<equiv> prev (\<^bold>\<not> pro A active since (p \<^bold>\<and> Pro (A active)))\<close>

abbreviation Always ("always _" [70] 70) where
  \<open>Always p \<equiv> Neg (\<^bold>\<top> since (\<^bold>\<not> p))\<close>

abbreviation Sometime ("sometime _" [70] 70) where
  \<open>Sometime p \<equiv> \<^bold>\<top> since p\<close>

abbreviation Weaksince ("_ sincew _" [50,50] 50) where
  \<open>Weaksince p q \<equiv> p since q \<^bold>\<or> (always p)\<close>

abbreviation Happensbefore ("_ \<^bold>\<rightarrow> _" [50,50] 50) where
  \<open>Happensbefore p q \<equiv> \<^bold>\<not> p since (q \<^bold>\<and> \<^bold>\<not> p) \<^bold>\<and> sometime p\<close>

abbreviation WroteTo (" _ wrote _ to _" [73,73,73] 73) where
  \<open>WroteTo A e1 e2 \<equiv> lprev A (Pro (A : e1 \<rhd> e2))\<close>

(* Mistake in draft \<rightarrow> we don't have existential in logic
abbreviation WroteSomethingTo (" _ wroteto _" [73,73] 73) where
  \<open>WroteSomethingTo A e2 \<equiv> \<exists> e1 . A wrote e1 to e2\<close>
*)

abbreviation RecentlyWrote ("_ recentlyWrote _ to _ ignore _" [70,70,70,70] 70) where
  \<open>RecentlyWrote A e x blankVar \<equiv>  \<^bold>\<not>(A wrote blankVar to x) since A wrote e to x\<close>

(* Once we do soundness proofs: split deduction systems into:
  1 epistemic part (to reuse proofs in Epistemic_Logic)
  2 temporal part (and put proofs in Temp_Logic? Or have proof for epistemic_temp logic 
  3 program-specific part (maybe in its own theory)

Here's the signature for 1+2, but not 3
inductive SystemK :: \<open>('i,'a) fm \<Rightarrow> bool\<close> ("\<turnstile> _" [50] 50) where
*)
inductive SystemET ::
  \<open> ('l com) list \<Rightarrow> ('tid,('tid,'l) pfm) fm \<Rightarrow> bool\<close> ("_ \<turnstile> _" [36,36] 36) where
(* purely epistemic stuff *)
  A1: \<open>tautology p \<Longrightarrow> S \<turnstile> p\<close>
| A2: \<open>S \<turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
| R1: \<open>S \<turnstile> p \<Longrightarrow> S \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> S \<turnstile> q\<close>
| R2: \<open>S \<turnstile> p \<Longrightarrow> S \<turnstile> K i p\<close>
| K: \<open>S \<turnstile> K i (p \<^bold>\<longrightarrow> q) \<Longrightarrow> S \<turnstile> K i p \<^bold>\<longrightarrow> K i q\<close>
| T: \<open>S \<turnstile> K i p \<^bold>\<longrightarrow> p\<close>
| 4: \<open>S \<turnstile> K i p \<^bold>\<longrightarrow> K i (K i p)\<close>
(* purely temporal stuff *)
| PrevDual: \<open>S \<turnstile> prev \<^bold>\<not> p \<^bold>\<longleftrightarrow> \<^bold>\<not> (prev q)\<close>
| Prev: \<open>S \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> S \<turnstile> prev p \<^bold>\<longrightarrow> prev q\<close>
| Since: \<open>S \<turnstile> (p since q) \<^bold>\<longleftrightarrow> q \<^bold>\<or> (p \<^bold>\<and> prev (p since q))\<close>
(* epistemic-temporal program stuff  *)
| KP1: \<open>S \<turnstile> prev Pro (A active) \<and> S \<turnstile> prev A knows p 
            \<Longrightarrow> S \<turnstile> A knows (prev (Pro (A active)  \<^bold>\<longrightarrow> p))\<close>
| KP2: \<open>S \<turnstile> prev (Neg(Pro (A active))) \<and> S \<turnstile> prev A knows p 
            \<Longrightarrow> S \<turnstile> A knows (prev (Neg (Pro (A active))  \<^bold>\<longrightarrow> p))\<close>
| KPA: \<open>S \<turnstile> lprev A (A knows p) \<Longrightarrow> S \<turnstile> A knows (lprev A p)\<close>
| KSRA:\<open>S \<turnstile> lprev A (A knows (p since q))
          \<and> S \<turnstile> A knows p  \<Longrightarrow> S \<turnstile> A knows (p since q)\<close>
(* program stuff *)

(*
| EqI: \<open> (\<forall> (\<Pi> :: ('tid,'l) run)
             i 
             (\<rho> :: ('tid,'tid) id_interp) 
             (A :: 'tid).
                \<Pi>,i,\<rho> \<Turnstile>p A said e1 = e2) \<Longrightarrow> S \<turnstile> pro A said e1 = e2\<close>

| InEqI: \<open> (\<forall> (\<Pi> :: ('tid,'l) run)
             i 
             (\<rho> :: ('tid,'tid) id_interp) 
             (A :: 'tid).
                not ( \<Pi>,i,\<rho> \<Turnstile>p A said e1 = e2))
             \<Longrightarrow> S \<turnstile> \<^bold>\<not> (pro A said e1 = e2)\<close>
*)


(*
section \<open>Soundness\<close>

lemma eval_semantics: \<open>eval (pi s) (\<lambda>q. Kripke pi r, s \<Turnstile> q) p = (Kripke pi r, s \<Turnstile> p)\<close>
  by (induct p) simp_all 

theorem tautology: \<open>tautology p \<Longrightarrow> M, s \<Turnstile> p\<close>
proof -
  assume \<open>tautology p\<close>
  then have \<open>eval (g s) (\<lambda>q. Kripke g r, s \<Turnstile> q) p\<close> for g r
    by simp
  then have \<open>Kripke g r, s \<Turnstile> p\<close> for g r
    using eval_semantics by metis
  then show \<open>M, s \<Turnstile> p\<close>
    by (metis kripke.collapse)
qed

theorem soundness: \<open>S \<turnstile> p \<Longrightarrow> M, s \<Turnstile> p\<close>
  by (induct p arbitrary: s rule: SystemK.induct) (simp_all add: tautology)
*)

section \<open>Derived rules\<close>

lemma K_FFI: \<open>S \<turnstile> (p \<^bold>\<longrightarrow> (\<^bold>\<not> p) \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
  by (simp add: A1)

primrec conjoin :: \<open>('i,'a) fm list \<Rightarrow> ('i,'a) fm \<Rightarrow> ('i,'a) fm\<close> where
  \<open>conjoin [] q = q\<close>
| \<open>conjoin (p # ps) q = (p \<^bold>\<and> conjoin ps q)\<close>

primrec imply :: \<open>('i,'a) fm list \<Rightarrow> ('i,'a) fm \<Rightarrow> ('i,'a) fm\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<^bold>\<longrightarrow> imply ps q)\<close>

lemma K_imply_head: \<open>S \<turnstile> imply (p # ps) p\<close>
proof -
  have \<open>tautology (imply (p # ps) p)\<close>
    by (induct ps) simp_all
  then show ?thesis
    using A1 by blast
qed

lemma K_imply_Cons:
  assumes \<open>S \<turnstile> imply ps q\<close>
  shows \<open>S \<turnstile> imply (p # ps) q\<close>
proof -
  have \<open>tautology (imply ps q \<^bold>\<longrightarrow> imply (p # ps) q)\<close>
    by simp
  then have \<open>S \<turnstile> (imply ps q \<^bold>\<longrightarrow> imply (p # ps) q)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_imply_member: \<open>p \<in> set ps \<Longrightarrow> S \<turnstile> imply ps p\<close>
proof (induct ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ps)
  then show ?case
  proof (cases \<open>a = p\<close>)
    case True
    then show ?thesis
      using Cons K_imply_head by blast
  next
    case False
    then show ?thesis
      using Cons K_imply_Cons by simp
  qed
qed

lemma K_right_mp:
  assumes \<open>S \<turnstile> imply ps p\<close> \<open>S \<turnstile> imply ps (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>S \<turnstile> imply ps q\<close>
proof -
  have \<open>tautology (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
    by (induct ps) simp_all
  then have \<open>S \<turnstile> (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma tautology_imply_superset:
  assumes \<open>set ps \<subseteq> set qs\<close>
  shows \<open>tautology (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
proof (rule ccontr)
  assume \<open>\<not> tautology (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
  then obtain h where \<open>\<not> eval h (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
    by blast
  then have \<open>eval h (imply ps r)\<close> \<open>\<not> eval h (imply qs r)\<close>
    by simp_all
  then consider (np) \<open>\<exists>p \<in> set ps. \<not> eval h p\<close> | (r) \<open>\<forall>p \<in> set ps. eval h p\<close> \<open>eval h r\<close>
    by (induct ps) auto
  then show False
  proof cases
    case np
    then have \<open>\<exists>p \<in> set qs. \<not> eval h p\<close>
      using \<open>set ps \<subseteq> set qs\<close> by blast
    then have \<open>eval h (imply qs r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval h (imply qs r)\<close> by blast
  next
    case r
    then have \<open>eval h (imply qs r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval h (imply qs r)\<close> by blast
  qed
qed

lemma tautology_imply: \<open>tautology q \<Longrightarrow> tautology (imply ps q)\<close>
  by (induct ps) simp_all

theorem K_imply_weaken:
  assumes \<open>S \<turnstile> imply ps q\<close> \<open>set ps \<subseteq> set ps'\<close>
  shows \<open>S \<turnstile> imply ps' q\<close>
proof -
  have \<open>tautology (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using \<open>set ps \<subseteq> set ps'\<close>
  proof (induct ps arbitrary: ps')
    case Nil
    then show ?case
      by (induct ps') simp_all
  next
    case (Cons a G)
    then show ?case
      using tautology_imply_superset by blast
  qed
  then have \<open>S \<turnstile> (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using A1 by blast
  then show ?thesis
    using \<open>S \<turnstile> imply ps q\<close> R1 by blast
qed

lemma imply_append: \<open>imply (ps @ ps') q = imply ps (imply ps' q)\<close>
  by (induct ps) simp_all

lemma K_ImpI:
  assumes \<open>S \<turnstile> imply (p # G) q\<close>
  shows \<open>S \<turnstile> imply G (p \<^bold>\<longrightarrow> q)\<close>
proof -
  have \<open>set (p # G) \<subseteq> set (G @ [p])\<close>
    by simp
  then have \<open>S \<turnstile> imply (G @ [p]) q\<close>
    using assms K_imply_weaken by blast
  then have \<open>S \<turnstile> imply G (imply [p] q)\<close>
    using imply_append by metis
  then show ?thesis
    by simp
qed

lemma cut: \<open>S \<turnstile> imply G p \<Longrightarrow> S \<turnstile> imply (p # G) q \<Longrightarrow> S \<turnstile> imply G q\<close>
  using K_ImpI K_right_mp by blast

lemma K_Boole: \<open>S \<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom> \<Longrightarrow> S \<turnstile> imply G p\<close>
proof -
  assume \<open>S \<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close>
  then have \<open>S \<turnstile> imply G (\<^bold>\<not> \<^bold>\<not> p)\<close>
    using K_ImpI by blast
  moreover have \<open>tautology (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    by (induct G) simp_all
  then have \<open>S \<turnstile> (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    using A1 by blast
  ultimately show ?thesis
    using R1 by blast
qed

lemma K_DisE:
  assumes \<open>S \<turnstile> imply (A # G) C\<close> \<open>S \<turnstile> imply (B # G) C\<close> \<open> S \<turnstile> imply G (A \<^bold>\<or> B)\<close>
  shows \<open>S \<turnstile> imply G C\<close>
proof -
  have \<open>tautology (imply (A # G) C \<^bold>\<longrightarrow> imply (B # G) C \<^bold>\<longrightarrow> imply G (A \<^bold>\<or> B) \<^bold>\<longrightarrow> imply G C)\<close>
    by (induct G) auto
  then have \<open>S \<turnstile> (imply (A # G) C \<^bold>\<longrightarrow> imply (B # G) C \<^bold>\<longrightarrow> imply G (A \<^bold>\<or> B) \<^bold>\<longrightarrow> imply G C)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_conjoin_imply:
  assumes \<open>S \<turnstile> (\<^bold>\<not> conjoin G (\<^bold>\<not> p))\<close>
  shows \<open>S \<turnstile> imply G p\<close>
proof -
  have \<open>tautology (\<^bold>\<not> conjoin G (\<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    by (induct G) simp_all
  then have \<open>S \<turnstile> (\<^bold>\<not> conjoin G (\<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_distrib_K_imp:
  assumes \<open>S \<turnstile> K i (imply G q)\<close>
  shows \<open>S \<turnstile> imply (map (K i) G) (K i q)\<close>
proof -
  have \<open>S \<turnstile> (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
  proof (induct G)
    case Nil
    then show ?case
      by (simp add: A1)
  next
    case (Cons a G)
    have \<open>S \<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q))\<close>
      by (simp add: A2)
    moreover have
      \<open>S \<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q)) \<^bold>\<longrightarrow>
        (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>S \<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using Cons R1 by blast
    moreover have
      \<open>S \<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>S \<turnstile> (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using R1 by blast
    then show ?case
      by simp
  qed
  then show ?thesis
    using assms R1 by blast
qed

(* derived rules *)

lemma conI: 
  assumes \<open>S \<turnstile> p\<close> \<open>S \<turnstile> q\<close> 
  shows \<open>S \<turnstile> p \<^bold>\<and> q\<close>
proof -
  have \<open>S \<turnstile> p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<and> q\<close> by (simp add: A1)
  with assms show ?thesis using R1 by blast
qed

lemma conE: 
  assumes  \<open>S \<turnstile> p \<^bold>\<and> q\<close>  
  shows \<open>S \<turnstile> p \<and> S \<turnstile> q\<close>
proof -
  have a1: \<open>S \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> p\<close> by (simp add: A1)
  have a2: \<open>S \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> q\<close> by (simp add: A1)
  show ?thesis using a1 a2 R1 assms by auto
qed

lemma disI: 
  assumes \<open>S \<turnstile> p \<or> S \<turnstile> q\<close>
  shows \<open>S \<turnstile> p \<^bold>\<or> q\<close>
proof -
  have \<open>S \<turnstile> p \<^bold>\<longrightarrow> p \<^bold>\<or> q\<close> by (simp add: A1)
  then have a1: \<open>S \<turnstile> p \<Longrightarrow> S \<turnstile> p \<^bold>\<or> q\<close> using R1 by blast
  have \<open>S \<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<or> q\<close> by (simp add: A1)
  then have a2: \<open>S \<turnstile> q \<Longrightarrow> S \<turnstile> p \<^bold>\<or> q\<close> using R1 by blast
  with assms a1 show ?thesis by blast 
qed

lemma PrevNeg:
  assumes \<open>S \<turnstile> prev \<^bold>\<not> p\<close>
  shows \<open>S \<turnstile> \<^bold>\<not> (prev p)\<close>
  using assms PrevDual R1 conE by blast

lemma SE: \<open>S \<turnstile> (q \<^bold>\<longrightarrow> r) \<^bold>\<and> (p since q) \<^bold>\<and> (prev (p since q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> r\<close>
proof -
  from Since have a: \<open>S \<turnstile> (p since q) \<^bold>\<longrightarrow> (q \<^bold>\<or> (p \<^bold>\<and> (prev (p since q))))\<close>
    using conE by blast
  have \<open>tautology (((p since q) \<^bold>\<longrightarrow> (q \<^bold>\<or> (p \<^bold>\<and> (prev (p since q))))) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<and> (p since q) \<^bold>\<and> (prev (p since q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> r)\<close> by auto
  with a R1 A1 show ?thesis by blast
qed

lemma alwaysI:  \<open>S \<turnstile> p \<and> S \<turnstile> (prev (always p)) \<Longrightarrow> S \<turnstile> always p\<close>
proof -
  assume assm: \<open>S \<turnstile> p \<and> S \<turnstile> (prev (always p))\<close>
  with PrevNeg conI have a1: \<open>S \<turnstile> p \<^bold>\<and> \<^bold>\<not> (prev (TT since \<^bold>\<not> p))\<close> by blast
  from SE have a2: \<open>S \<turnstile> \<^bold>\<not> ((\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<and> (TT since \<^bold>\<not> p) \<^bold>\<and> (\<^bold>\<not> (prev (TT since \<^bold>\<not> p))))\<close> by auto
  have \<open>tautology (\<^bold>\<not> (\<^bold>\<not> \<^bold>\<not> p \<^bold>\<and> (TT since \<^bold>\<not> p) \<^bold>\<and> (\<^bold>\<not> (prev (TT since \<^bold>\<not> p)))) \<^bold>\<longrightarrow> p \<^bold>\<and> (\<^bold>\<not> (prev (TT since \<^bold>\<not> p))) \<^bold>\<longrightarrow> \<^bold>\<not> (TT since \<^bold>\<not> p))\<close> by auto
  with a1 a2 A1 R1 show ?thesis by blast
qed

lemma taut1: \<open>tautology ((p \<^bold>\<longrightarrow> Neg q \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<^bold>\<longrightarrow>(p \<^bold>\<longrightarrow> q))\<close>
  by simp_all

lemma taut2: \<open>tautology ((p\<^bold>\<longrightarrow>q\<^bold>\<longrightarrow>\<^bold>\<bottom>)\<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> Neg q))\<close>
  by simp_all

lemma taut3: \<open>tautology ((p \<^bold>\<longrightarrow> q)\<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r)\<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> r) )\<close>
  by simp_all

lemma SI1: \<open>S \<turnstile> q \<^bold>\<longrightarrow> (p since q)\<close>
proof -
  have "tautology (((q \<^bold>\<or> p \<^bold>\<and> prev (p since q)) \<^bold>\<longrightarrow> (p since q)) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> (p since q))" by auto
  with A1 R1 Since conE show ?thesis by blast
qed

lemma SI2: \<open>S \<turnstile> p \<and> S \<turnstile> Prev (p since q) \<Longrightarrow> S \<turnstile> p since q\<close>
   by (metis R1 Since conE conI disI) 

lemma alwaysE1:  \<open>S \<turnstile> always p \<Longrightarrow> S \<turnstile> p\<close>
proof -
  assume assm: "S \<turnstile> always p"
  have "S \<turnstile> (\<^bold>\<not> p \<^bold>\<longrightarrow> (\<^bold>\<not> \<^bold>\<bottom> since \<^bold>\<not> p)) \<^bold>\<longrightarrow> always p \<^bold>\<longrightarrow> p" using A1 by force
  with R1 SI1 assm show ?thesis by blast
qed

lemma sometimeI1:  \<open>S \<turnstile> p \<Longrightarrow> S \<turnstile> sometime p\<close>
  using SI1 R1 by blast

lemma sometimeI2:  \<open>S \<turnstile> prev (sometime p) \<Longrightarrow> S \<turnstile> sometime p\<close>
  by (simp add: A1 SI2)

section \<open>Acknowledgements\<close>

text \<open>
The definition of a consistency property, subset closure, finite character and maximally consistent
sets is based on work by Berghofer, but has been adapted from first-order logic to epistemic logic.

  \<^item> Stefan Berghofer:
  First-Order Logic According to Fitting.
  \<^url>\<open>https://www.isa-afp.org/entries/FOL-Fitting.shtml\<close>
\<close>

end
