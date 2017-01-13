(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* This theory provides a very basic proof method for rewriting SIMPL (C) programs
  under ccorres/ccorres_underlying using semantic equivalence.
*)

theory CCorres_Rewrite
imports 
  "Corres_UL_C"
begin

(* C_simp rules may be applied repeatedly.
   The result of a C_simp_final simplification will not be simplified further.
   For example, use C_simp_final when the RHS matches the LHS. *)

named_theorems C_simp
named_theorems C_simp_final

context
  (* for less typing and local com_eq syntax *)
  fixes \<Gamma> :: "'b \<Rightarrow> ('a, 'b, 'c) com option"
begin

definition
  com_eq :: "('a, 'b, 'c) com \<Rightarrow> ('a, 'b, 'c) com \<Rightarrow> bool"
where
  "com_eq c c' \<equiv> \<forall>s s'. (\<Gamma> \<turnstile> \<langle>c,s\<rangle> \<Rightarrow> s') = (\<Gamma> \<turnstile> \<langle>c',s\<rangle> \<Rightarrow> s')"

(* local, in this context only *)
notation com_eq (infix "\<sim>" 10)

(* Slightly stronger than the existing semantic_equiv, which only talks about Normal s, not all s *)
lemma com_eq_semantic_equiv:
  "c \<sim> c' \<Longrightarrow> semantic_equiv \<Gamma> s s' c c'"
  by (simp add: com_eq_def semantic_equiv_def ceqv_def)

(* com_eq is an order *)
lemma com_eq_refl:
  "c \<sim> c"
  by (simp add: com_eq_def)

lemma com_eq_sym:
  "(c \<sim> c') = (c' \<sim> c)"
  by (auto simp: com_eq_def)

lemma com_eq_trans:
  "\<lbrakk> c \<sim> c'; c' \<sim> c'' \<rbrakk> \<Longrightarrow> c \<sim> c''"
  by (auto simp: com_eq_def)

(* com_eq permits rewriting under ccorres_underlying *)
lemma ccorres_com_eqI:
  "\<lbrakk> c \<sim> c'; ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H c' \<rbrakk> \<Longrightarrow> 
  ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H c"
  by (erule ccorres_semantic_equivD2, erule com_eq_semantic_equiv)

(* structural propagation rules *)
lemma com_eq_Seq:
  "\<lbrakk> c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk> \<Longrightarrow> c1;;c2 \<sim> c1';;c2'"
  unfolding com_eq_def
  by (auto intro: exec.Seq elim!: exec_elim_cases)

lemma com_eq_Cond:
  "\<lbrakk> c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk> \<Longrightarrow> Cond b c1 c2 \<sim> Cond b c1' c2'"
  unfolding com_eq_def
  by (auto intro: exec.CondTrue exec.CondFalse elim!: exec_elim_cases)

lemma com_eq_While':
  assumes eq: "c \<sim> c'"
  assumes W: "\<Gamma> \<turnstile> \<langle>While b c,s\<rangle> \<Rightarrow> s'"
  shows "\<Gamma> \<turnstile> \<langle>While b c',s\<rangle> \<Rightarrow> s'"
  using W
proof (induct "While b c" s s')
  case WhileTrue
  with eq show ?case unfolding com_eq_def by (auto elim: exec.WhileTrue)
next
  case WhileFalse
  then show ?case by (rule exec.WhileFalse)
qed auto

lemma com_eq_While:
  "c \<sim> c' \<Longrightarrow> While b c \<sim> While b c'"
  by (subst com_eq_def)
     (auto intro: com_eq_While' com_eq_While' [OF com_eq_sym [THEN iffD1]])

(* the actual form of WHILE b DO c OD *)
lemma com_eq_whileAnno:
  "c \<sim> c' \<Longrightarrow> (whileAnno b I V c) \<sim> (whileAnno b I V c')"
  by (clarsimp simp: whileAnno_def elim!: com_eq_While)

lemma com_eq_Guard:
  "c \<sim> c' \<Longrightarrow> Guard f b c \<sim> Guard f b c'"
  unfolding com_eq_def
  by (auto intro: exec.Guard exec.GuardFault elim!: exec_elim_cases)

lemma com_eq_Catch:
  "\<lbrakk> c \<sim> c'; h \<sim> h' \<rbrakk> \<Longrightarrow> Catch c h \<sim> Catch c' h'"
  unfolding com_eq_def
  by (auto intro: exec.CatchMiss exec.CatchMatch elim!: exec_elim_cases)

lemmas ccorres_rewrite_splits =
  com_eq_Seq com_eq_Cond com_eq_While com_eq_whileAnno com_eq_Guard com_eq_Catch

(* Actual simplification rules *)

lemma com_eq_Skip_Seq [C_simp]:
  "Skip;;c \<sim> c"
  apply (clarsimp simp: com_eq_def)
  apply (rule iffI)
   apply (fastforce elim!: exec_elim_cases)
  apply (case_tac s; (simp, (erule exec_elim_cases; simp)?))
  apply (rule exec.Seq, rule exec.Skip, simp)
  done

lemma com_eq_Seq_Skip [C_simp]:
  "c;;Skip \<sim> c"
  apply (clarsimp simp: com_eq_def)
  apply (rule iffI)
   apply (fastforce elim!: exec_elim_cases)  
  apply (case_tac s; (simp, (erule exec_elim_cases; simp)?))
  apply (rule exec.Seq, simp)
  apply (case_tac s'; (simp, (erule exec_elim_cases; simp)?))
  apply (rule exec.Skip)
  done

lemma com_eq_Cond_empty [C_simp]:
  "Cond {} c1 c \<sim> c"
  unfolding com_eq_def
  by (clarsimp, case_tac s, auto intro: exec.CondFalse elim!: exec_elim_cases)

lemma com_eq_Cond_UNIV [C_simp]:
  "Cond UNIV c c2 \<sim> c"
  unfolding com_eq_def
  by (clarsimp, case_tac s, auto intro: exec.CondTrue  elim!: exec_elim_cases)

lemma exec_Cond_cases:
  "\<lbrakk>s \<in> b \<Longrightarrow> \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> t; s \<notin> b \<Longrightarrow> \<Gamma>\<turnstile> \<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow> t\<rbrakk> \<Longrightarrow> 
  \<Gamma>\<turnstile> \<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow> t"
  by (cases "s \<in> b") (auto intro: exec.CondTrue exec.CondFalse)

lemma com_eq_Cond_both [C_simp]:
  "Cond b c c \<sim> c"
  unfolding com_eq_def
  by (clarsimp, case_tac s, auto intro: exec_Cond_cases elim!: exec_elim_cases)

lemma com_eq_If_False [C_simp]:
  "IF False THEN c1 ELSE c FI \<sim> c"
  by (simp add: com_eq_Cond_empty)

lemma com_eq_If_True [C_simp]:
  "IF True THEN c ELSE c2 FI \<sim> c"
  by (simp add: com_eq_Cond_UNIV)

lemma com_eq_While_empty [C_simp]:
  "While {} c \<sim> Skip"
  unfolding com_eq_def
  by (auto intro: exec.WhileFalse exec.Skip elim!: exec_elim_cases)

lemma com_eq_While_FALSE [C_simp]:
  "WHILE False INV P DO c OD \<sim> Skip"
  by (simp add: com_eq_While_empty whileAnno_def)

lemma com_eq_Guard_UNIV [C_simp]:
  "Guard f UNIV c \<sim> c"
  unfolding com_eq_def
  by (clarsimp, case_tac s, auto intro: exec.Guard elim!: exec_elim_cases)

lemma com_eq_Guard_True [C_simp]:
  "Guard f \<lbrace>True\<rbrace> c \<sim> c"
  by (clarsimp simp: com_eq_Guard_UNIV)

lemma com_eq_Guard_empty [C_simp_final]:
  "Guard f {} c \<sim> Guard f {} Skip"
  unfolding com_eq_def
  by (clarsimp, case_tac s, auto intro: exec.GuardFault elim!: exec_elim_cases)

lemma com_eq_Guard_False [C_simp_final]:
  "Guard f \<lbrace>False\<rbrace> c \<sim> Guard f {} Skip"
  by (clarsimp simp: com_eq_Guard_empty)

lemma com_eq_Catch_Skip [C_simp]:
  "Catch Skip c \<sim> Skip"
  unfolding com_eq_def
  by (auto intro: exec.CatchMiss exec.Skip elim!: exec_elim_cases)

lemma com_eq_Catch_Throw [C_simp]:
  "Catch Throw c \<sim> c"
  unfolding com_eq_def
  by (clarsimp, case_tac s, auto intro: exec.CatchMatch exec.Throw elim!: exec_elim_cases)

lemma com_eq_Throw [C_simp]:
  "Throw;; c \<sim> Throw"
  unfolding com_eq_def
  by (auto intro: exec.Throw exec.Seq elim!: exec_elim_cases)

end


(* First introduces com_eq goal (rule cccorres_com_eqI), then breaks the term into
   its component parts (ccorres_rewrite_decompose), and finally reassembles,
   applying simplification rules whenever possible, and otherwise applying reflexivity.

   At every decomposition or simplification step, we first apply a transitivity rule,
   to ensure we can continue simplifying each subterm until no more simplifications
   are possible, before applying reflexivity to reassemble the enclosing term.

   Limited to unconditional rewrite rules. Purpose is not to provide a real rewriting engine,
   just to get rid of annoying Skip and Cond {} bits that come from config options or macros.
*)

method ccorres_rewrite_decompose =
  (rule com_eq_trans, (rule ccorres_rewrite_splits; ccorres_rewrite_decompose)?)

method ccorres_rewrite_recombine declares C_simp C_simp_final =
  determ \<open>rule C_simp_final C_simp[THEN com_eq_trans] com_eq_refl\<close>

method ccorres_rewrite declares C_simp C_simp_final =
  changed \<open>rule ccorres_com_eqI, ccorres_rewrite_decompose, ccorres_rewrite_recombine+\<close>

(* Example *)
lemma
  assumes c3: "com_eq \<Gamma> c3 c"
  assumes c: "com_eq \<Gamma> (c;;c) c"
  shows "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H 
                            (c;; Guard f UNIV (IF X THEN c ELSE c FI);; Cond {} Skip (Skip;;c2);;
                             Skip;; 
                             (IF False THEN Skip ELSE SKIP;; TRY THROW CATCH c3 END FI;; SKIP))"
  apply ccorres_rewrite              (* c;; c;; c2;; c3 *)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c;;c2;;c3)" \<Rightarrow> \<open>-\<close>)
  apply (ccorres_rewrite C_simp: c3) (* c;; c;; c2;; c *)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (ccorres_rewrite C_simp: c)  (* c;; c2;; c *)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (fails \<open>ccorres_rewrite\<close>)    (* fails if nothing changes *)
  oops

(* Test for WHILE (whileAnno) case *)
lemma "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
        (WHILE b DO Guard f g c;; IF False THEN c2 FI OD;; SKIP)"
  apply ccorres_rewrite
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
                                (WHILE b DO Guard f g c OD)" \<Rightarrow> \<open>-\<close>)
  oops

(* Test that simplification works down all branches of the term. *)
lemma "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
           (IF b THEN
              (SKIP ;; c) ;; (SKIP ;; IF True THEN SKIP ELSE c FI)
            ELSE
              (SKIP ;; SKIP) ;; (Guard f UNIV c ;; SKIP)
            FI)"
  apply ccorres_rewrite
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H c" \<Rightarrow> \<open>-\<close>)
  oops

(* Test that complex simplification rules work. *)
context begin

private lemma com_eq_Cond_redundant:
  "com_eq \<Gamma> (IF b THEN c1 ELSE IF b THEN c2 ELSE c3 FI FI) (IF b THEN c1 ELSE c3 FI)"
  unfolding com_eq_def
  by (auto intro: exec.CondTrue exec.CondFalse elim!: exec_elim_cases)

private lemma "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
                (SKIP ;;
                 IF b THEN
                   (SKIP ;; c1) ;; (SKIP ;; SKIP)
                 ELSE
                   IF b THEN
                     IF b1 THEN c2 ELSE c2 FI
                   ELSE
                     WHILE False DO c4 OD ;; (c3 ;; SKIP)
                   FI
                 FI)"
  apply (ccorres_rewrite C_simp: com_eq_Cond_redundant)
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
                                (IF b THEN c1 ELSE c3 FI)" \<Rightarrow> \<open>-\<close>)
  oops

end

(* Test C_simp_final avoids looping. *)
lemma "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
        (SKIP ;; Guard f {} (IF b THEN c ELSE c FI) ;; SKIP)"
  apply ccorres_rewrite
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
                                (Guard f {} SKIP)" \<Rightarrow> \<open>-\<close>)
  oops

end
