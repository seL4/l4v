(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Automation framework for general C refinement *)

theory Ctac
imports
  AutoCorres_C
  "CLib.XPres"
begin

(* This file includes theorems associated with ctac and friends *)

context kernel
begin

(* tactic setup *)

lemma match_ccorres:
  "ccorres_underlying sr G r xf' arrel axf P P' hs a c
      \<Longrightarrow> ccorres_underlying sr G r xf' arrel axf P P' hs a c" .

(* xfru needs to appear in the lemma ... *)
lemma match_ccorres_record:
  fixes xfru :: "('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" and xf' :: "cstate \<Rightarrow> 'b" and xfr :: "'b \<Rightarrow> 'a"
  shows "ccorres_underlying sr G r (xfr \<circ> xf') arrel axf P P' hs a (c xfru)
          \<Longrightarrow> ccorres_underlying sr G r (xfr \<circ> xf') arrel axf P P' hs a (c xfru)" .

lemma match_ccorres_Seq:
  "ccorres_underlying sr G r xf arrel axf P P' hs a (c ;; d)
   \<Longrightarrow> ccorres_underlying sr G r xf arrel axf P P' hs a (c ;; d)" .

lemma match_ccorres_call_Seq:
  "ccorres_underlying sr G r xf arrel axf P P' hs a (call i f g c ;; d)
      \<Longrightarrow> ccorres_underlying sr G r xf arrel axf P P' hs a (call i f g c ;; d)" .

(* Most specific to least specific.  ctac uses <base> ^ "_novcg" so the suffic is important for the
 * ctac_splits lemmas *)
lemmas ctac_splits_non_call = ccorres_split_nothrowE [where F = UNIV] ccorres_split_nothrow  [where F = UNIV]
lemmas ctac_splits_non_call_novcg = ccorres_split_nothrow_novcgE ccorres_split_nothrow_novcg

lemmas ctac_splits_call = ccorres_split_nothrow_callE [where F = UNIV] ccorres_split_nothrow_call [where F = UNIV]
lemmas ctac_splits_call_novcg = ccorres_split_nothrow_call_novcgE ccorres_split_nothrow_call_novcg

lemmas ctac_splits_record =
  ccorres_split_nothrow_call_record  [where F = UNIV] ccorres_split_nothrow_record [where F = UNIV]
(* Probably useless as-is *)
lemmas ctac_splits_record_novcg =
  ccorres_split_nothrow_call_record_novcg ccorres_split_nothrow_record_novcg

(* None of these generate vcg obligations, so we don't need a _novcg alternative *)
lemmas ctac_nosplit_non_call = match_ccorres
lemmas ctac_nosplit_call = ccorres_callE ccorres_call
lemmas ctac_nosplit_record = ccorres_call_record match_ccorres_record

(* Used with the _spec and _modifies rules. WARNING: the order and
    position of these assumptions is relied on by the tactic csymbr.  The
    guard for cc is then simplified and gen_asm2 can be used. *)
lemma ccorres_lift_rhs_call:
  assumes cc: "\<And>rv'. ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' rv' \<inter> {s. P' rv' (i s)}) hs a (d' rv')"
  (* WARNING: the tactic csymbr relies on the outermost variable (v) being of the same type as the return type of xf' *)
  and  xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and f_spec: "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> P \<sigma> s} Call f {t. P' (xf'' t) s}"
  and f_modifies: "modifies_spec f"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     gg: "\<And>x f s. globals (xfu' f s) = globals s"
  and     gi: "\<And>s. globals (i s) = globals s"
  (* This is annoying, as simp doesn't always solve it *)
  and    Pig: "\<And>x (s :: cstate) v'. P' x (i s)
  \<Longrightarrow> P' x (i (xfu' (\<lambda>_. x) s))"
  (* The concrete guard here is stronger than required --- we really need xf'' t not v *)
  shows   "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G
  ({s. \<forall>v v'. P' v (i s) \<longrightarrow> xfu' (\<lambda>_. v) s \<in> {s. s \<in> G' v}}
  \<inter> {s. P (i s) (i s)}) hs a
            (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>_ t. Basic (xfu' (\<lambda>_. xf'' t))) ;; d)"
  (is "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G ?G' hs a (?c ;; d)")
proof (subst return_bind [where x = "()" and f = "\<lambda>_. a", symmetric],
    rule ccorres_guard_imp [OF ccorres_split_nothrow, OF ccorres_call ceqv, OF _ gg xfxfu gi cc])
  show "ccorres dc xf'' \<top> (Collect (\<lambda>s. P s s)) [] (return ()) (Call f)"
    apply (rule ccorres_guard_imp2)
    apply (rule ccorres_noop_spec [OF f_spec f_modifies])
    apply simp
    done
next
  show "\<lbrace>G\<rbrace> return () \<lbrace>\<lambda>_. G\<rbrace>" by wp
next
  show "\<Gamma>\<turnstile> ?G' ?c {s. \<forall>uu. dc uu (xf' s) \<longrightarrow> s \<in> G' (xf' s) \<inter> {sa. P' (xf' s) (i sa)}}"
    apply (rule HoarePartial.ProcModifyReturnNoAbr [where return' = "\<lambda>s t. s", OF _ _ f_modifies])
    apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ f_spec])
    defer
    apply vcg
    apply (clarsimp simp add: gi mex_def meq_def xfxfu)
    apply (clarsimp simp add: gi mex_def meq_def xfxfu Pig)
    done
qed simp_all

lemma ccorres_lift_rhs_Basic:
  assumes cc: "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' hs a (d' v)"
  and  xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     gg: "\<And>x f s. globals (xfu' f s) = globals s"
  (* WARNING: the tactic csymbr relies on the outermost variable being of the same type as the return type of xf' *)
  (*  and    Pig: "\<And>x (s :: cstate) v'. P' x (i s) \<Longrightarrow> P' x (i (xfu' (\<lambda>_. x) s))" *)
  (* The concrete guard here is stronger than required --- we really need xf'' t not v *)
  shows   "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G {s. xfu' (\<lambda>_. v) s \<in> G'}  hs a (Basic (xfu' (\<lambda>_. v)) ;; d)"
  (is "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G ?G' hs a (?c ;; d)")
proof (subst return_bind [where x = "()" and f = "\<lambda>_. a", symmetric],
    rule ccorres_guard_imp [OF ccorres_split_nothrow, OF _ ceqv])
  show "ccorres dc xf' \<top> UNIV hs (return ()) ?c"
    apply (rule ccorres_noop)
    apply (vcg spec=modifies)
    done
next
  fix rv'
  show "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' \<inter> {s. rv' = v}) hs a (d' rv')"
    apply (rule ccorres_gen_asm2)
    apply (erule ssubst)
    apply (rule cc)
    done
next
  show "\<lbrace>G\<rbrace> return () \<lbrace>\<lambda>_. G\<rbrace>" by wp
next
  show "\<Gamma>\<turnstile> ?G' ?c {s. \<forall>uu. dc uu (xf' s) \<longrightarrow> s \<in> G' \<inter> {_. xf' s = v}}"
    apply vcg
    apply (clarsimp simp add: xfxfu)
    done
qed simp_all


(* This needs to correspond in the first 4 assumptions to the above _call: *)
lemma ccorres_lift_rhs_call_record:
  fixes xf' :: "cstate \<Rightarrow> 'a" and xfu' :: "('a \<Rightarrow> 'a) \<Rightarrow> cstate \<Rightarrow> cstate"
  and  xf'' :: "cstate \<Rightarrow> 'b"  and xfr :: "'a \<Rightarrow> 'b" and xfru :: "('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes cc: "\<And>rv' :: 'b. ccorres_underlying rf_sr \<Gamma> r xf arrel axf
                     G (G' rv' \<inter> {s. P' rv' (i s)}) hs a (d' (xfru (\<lambda>_. rv') oldv))"
  (* WARNING: the tactic csymbr relies on the outermost variable being of the same type as the return type of xf' *)
  and  xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and f_spec: "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> P \<sigma> s} Call f {t. P' (xf'' t) s}"
  and f_modifies: "modifies_spec f"
  (* WARNING: the tactic csymbr relies on the outermost variable being of the same type as the return type of xfr *)
  and  xfrxfru: "\<And>v s. xfr (xfru (\<lambda>_. v) s) = v"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     gg: "\<And>x f s. globals (xfu' f s) = globals s"
  and     gi: "\<And>s. globals (i s) = globals s"
  and Pig: "\<And>x (s :: cstate) v'. P' x (i s) \<Longrightarrow>
                P' x (i (xfu' (\<lambda>_. xfru (\<lambda>_. x) oldv) s))"
  (* The concrete guard here is stronger than required --- we really need xf'' t not v *)
  shows   "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G
  ({s. \<forall>v v'. P' v (i s) \<longrightarrow> xfu' (\<lambda>_. xfru (\<lambda>_. v) oldv) s \<in> {s. s \<in> G' v}}
  \<inter> {s. P (i s) (i s)}) hs a
            (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>_ t. Basic (xfu' (\<lambda>_. xfru (\<lambda>_. xf'' t) oldv))) ;; d)"
  (is "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G ?G' hs a (?c ;; d)")
proof (subst return_bind [where x = "()" and f = "\<lambda>_. a", symmetric],
    rule ccorres_guard_imp [OF ccorres_split_nothrow_record [where xfru = "xfru"], OF ccorres_call ceqv, OF _ gg _ gi cc])
  show "ccorres dc xf'' \<top> (Collect (\<lambda>s. P s s)) [] (return ()) (Call f)"
    apply (rule ccorres_guard_imp2)
    apply (rule ccorres_noop_spec [OF f_spec f_modifies])
    apply simp
    done
next
  fix a s t
  show "(xfr \<circ> xf') (xfu' (\<lambda>_. xfru (\<lambda>_. xf'' t) oldv) (s\<lparr>globals := globals t\<rparr>)) = xf'' t"
    by (simp add: xfxfu xfrxfru)
next
  show "\<lbrace>G\<rbrace> return () \<lbrace>\<lambda>_. G\<rbrace>" by wp
next
  show "\<Gamma>\<turnstile> ?G' ?c {s. xf' s = xfru (\<lambda>_. (xfr \<circ> xf') s) oldv \<and>
    (\<forall>uu. dc uu ((xfr \<circ> xf') s) \<longrightarrow> s \<in> G' ((xfr \<circ> xf') s) \<inter> {sa. P' ((xfr \<circ> xf') s) (i sa)})}"
    apply (rule HoarePartial.ProcModifyReturnNoAbr [where return' = "\<lambda>s t. s", OF _ _ f_modifies])
    apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ f_spec])
    defer
    apply vcg
    apply (clarsimp simp add: gi mex_def meq_def xfxfu)
    apply (clarsimp simp add: gi mex_def meq_def xfxfu xfrxfru Pig)
    done
qed simp_all

lemma ccorres_lift_rhs_Basic_record:
  fixes xf' :: "cstate \<Rightarrow> 'a" and xfu' :: "('a \<Rightarrow> 'a) \<Rightarrow> cstate \<Rightarrow> cstate" and xfru :: "('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes cc: "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' hs a (d' (xfru (\<lambda>_. v) oldv))"
  and  xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     gg: "\<And>x f s. globals (xfu' f s) = globals s"
  (* The concrete guard here is stronger than required --- we really need xf'' t not v *)
  shows   "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G {s. xfu' (\<lambda>_. xfru (\<lambda>_. v) oldv) s \<in> G'} hs a (Basic (xfu' (\<lambda>_. xfru (\<lambda>_. v) oldv)) ;; d)"
  (is "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G ?G' hs a (?c ;; d)")
proof (subst return_bind [where x = "()" and f = "\<lambda>_. a", symmetric],
    rule ccorres_guard_imp [OF ccorres_split_nothrow_record [where xfru = "xfru"], OF _ ceqv])
  show "ccorres dc ((\<lambda>_. v) \<circ> xf') \<top> UNIV hs (return ()) ?c"
    apply (rule ccorres_noop)
    apply (vcg spec=modifies)
    done
next
  fix rv'
  show "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' \<inter> {s. rv' = v}) hs a (d' (xfru (\<lambda>_. rv') oldv))"
    apply (rule ccorres_gen_asm2)
    apply (erule ssubst)
    apply (rule cc)
    done
next
  show "\<lbrace>G\<rbrace> return () \<lbrace>\<lambda>_. G\<rbrace>" by wp
next
  show "\<Gamma>\<turnstile> ?G' ?c {s. xf' s = xfru (\<lambda>_. ((\<lambda>_. v) \<circ> xf') s) oldv \<and>
           (\<forall>uu. dc uu (((\<lambda>_. v) \<circ> xf') s) \<longrightarrow> s \<in> G' \<inter> \<lbrace>((\<lambda>_. v) \<circ> xf') s = v\<rbrace>)}"
    apply (rule conseqPre)
    apply vcg
    apply (clarsimp simp add: xfxfu)
    done
qed simp_all

lemmas ccorres_lift_rhs_no_guard = ccorres_lift_rhs_call [where P = "\<lambda>_ _. True", simplified]
lemmas ccorres_lift_rhss = ccorres_lift_rhs_no_guard ccorres_lift_rhs_call

lemmas ccorres_lift_rhs_record_no_guard = ccorres_lift_rhs_call_record [where P = "\<lambda>_ _. True", simplified]
lemmas ccorres_lift_rhss_record = ccorres_lift_rhs_record_no_guard ccorres_lift_rhs_call_record

lemma ccorres_lift_rhs_Basic_stateful:
  assumes cc: "\<And>v. ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' v) hs a (d' v)"
  and  xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     gg: "\<And>f s. globals (xfu' f s) = globals s"
  shows   "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G {s. xfu' (\<lambda>_. g s) s \<in> G' (g s)}  hs a (Basic (\<lambda>s. xfu' (\<lambda>_. g s) s) ;; d)"
  (is "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G ?G' hs a (?c ;; d)")
proof (subst return_bind [where x = "()" and f = "\<lambda>_. a", symmetric],
    rule ccorres_guard_imp [OF ccorres_split_nothrow, OF _ ceqv])
  show "ccorres dc xf' \<top> UNIV hs (return ()) ?c"
    apply (rule ccorres_noop)
    apply (vcg spec=modifies)
    done
next
  fix rv'
  show "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' rv') hs a (d' rv')"
    by (rule cc)
next
  show "\<lbrace>G\<rbrace> return () \<lbrace>\<lambda>_. G\<rbrace>" by wp
next
  show "\<Gamma>\<turnstile> ?G' ?c {s. \<forall>uu. dc uu (xf' s) \<longrightarrow> s \<in> G' (xf' s)}"
    apply (rule conseqPre)
    apply vcg
    apply (clarsimp simp add: xfxfu)
    done
qed simp_all

lemma ccorres_lift_rhs_Spec_stateful:
  assumes cc: "\<And>v. ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' v) hs a (d' v)"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  assumes gg: "\<And>v s. globals (upd (\<lambda>_. v) s) = globals s"
  assumes upd_acc: "\<And>s. upd (\<lambda>_. accessor s) s = s"
  shows   "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G {s. \<forall>v. upd (\<lambda>_. v) s \<in> G' (xf' (upd (\<lambda>_. v) s))}  hs a (Spec {(s,t). \<exists>v. t = upd (\<lambda>_. v) s};; d)"
  (is "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G ?G' hs a (?c ;; d)")
proof (subst return_bind [where x = "()" and f = "\<lambda>_. a", symmetric],
    rule ccorres_guard_imp [OF ccorres_split_nothrow, OF _ ceqv])
  show "ccorres dc xf' \<top> UNIV hs (return ()) ?c"
    apply (rule ccorres_noop)
    apply (vcg spec=modifies)
     apply clarsimp
     apply (drule arg_cong[where f=globals])
     apply (simp add: gg)
    apply (rule_tac x=s in exI)
    apply (rule_tac x="accessor s" in exI)
    apply (rule upd_acc [symmetric])
    done
next
  fix rv'
  show "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' rv') hs a (d' rv')"
    by (rule cc)
next
  show "\<lbrace>G\<rbrace> return () \<lbrace>\<lambda>_. G\<rbrace>" by wp
next
  show "\<Gamma>\<turnstile> ?G' ?c {s. \<forall>uu. dc uu (xf' s) \<longrightarrow> s \<in> G' (xf' s)}"
    apply (rule conseqPre)
    apply vcg
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
    apply (rule_tac x=x in exI)
    apply (rule_tac x="accessor x" in exI)
    apply (rule upd_acc [symmetric])
    done
qed simp_all

(* For something like

int foo(int x)
{
    int i;
    ...
}

the parser spits out

lvar_nondet_init i_' i_'_update;;
...

which we need to remove  --- lvar_nondet_init is a nondeterministic SPEC
statement that picks any value for i, but leaves the rest unchanged.
*)

lemma ccorres_lift_rhs_remove_lvar_init:
  assumes cc: "ccorres_underlying rf_sr \<Gamma> r xf ar arf G G' hs a d"
  assumes gg: "\<And>x f s. globals (i_upd f s) = globals s"
  assumes upd_acc: "\<And>s. i_upd (\<lambda>_. i_acc s) s = s"
  assumes arb: "\<And>s v. s \<in> G' \<Longrightarrow> i_upd (\<lambda>_. v) s \<in> G'"
  shows   "ccorres_underlying rf_sr \<Gamma> r xf ar arf G G' hs a (lvar_nondet_init i_acc i_upd ;; d)"
  apply (unfold lvar_nondet_init_def)
  apply (rule ccorres_guard_imp)
  apply (rule ccorres_lift_rhs_Spec_stateful [OF cc ceqv_refl gg])
    apply (rule upd_acc)
   apply assumption
  apply (simp add: arb)
  done

lemma ccorres_lift_rhs_remove_lvar_init_unknown_guard:
  assumes cc: "ccorres_underlying rf_sr \<Gamma> r xf ar arf G G' hs a d"
  assumes gg: "\<And>x f s. globals (i_upd f s) = globals s"
  assumes upd_acc: "\<And>s. i_upd (\<lambda>_. i_acc s) s = s"
  shows   "ccorres_underlying rf_sr \<Gamma> r xf ar arf G {s. \<forall>v. i_upd (\<lambda>_. v) s \<in> G'} hs a (lvar_nondet_init i_acc i_upd ;; d)"
  unfolding lvar_nondet_init_def
  by (rule ccorres_lift_rhs_Spec_stateful [OF cc ceqv_refl gg], rule upd_acc)

lemma ccorres_special_Int_cong:
  "(\<And>s. P s = P' s) \<Longrightarrow> ccorres r xf G (G' \<inter> {s. P s}) hs a c = ccorres r xf G (G' \<inter> {s. P' s}) hs a c" by simp

lemma ccorres_special_trim_Int:
  "ccorres r xf G G' hs a c \<Longrightarrow> ccorres r xf G (G' \<inter> P') hs a c"
  apply (erule ccorres_guard_imp)
  apply simp
  apply simp
  done

lemma semantic_equiv_def2:
  fixes s :: "'b" and s' :: "('b, 'c) xstate"
  shows "semantic_equiv G s s' a a' \<equiv> ((G \<turnstile> \<langle>a,Normal s\<rangle> \<Rightarrow> s') = (G \<turnstile> \<langle>a',Normal s\<rangle> \<Rightarrow> s'))"
  unfolding semantic_equiv_def ceqv_def
  by simp

(* MOVE *)
lemma semantic_equiv_While_cong:
  assumes se: "\<And>s s'. semantic_equiv Gamma s s' b b'"
  shows   "semantic_equiv Gamma s s' (While G b) (While G b')"
  using se
  apply -
  apply (rule semantic_equivI)
  apply (rule exec_While_cong)
  apply (simp add: semantic_equiv_def2)
  done

lemma semantic_equiv_Seq_cong:
  assumes sea: "\<And>s'. semantic_equiv Gamma s s' a a'"
  and     seb: "\<And>s. semantic_equiv Gamma s s' b b'"
  shows   "semantic_equiv Gamma s s' (a ;; b) (a' ;; b')"
  using sea seb
  apply (simp add: semantic_equiv_def2)
  apply (rule exec_Seq_cong)
   apply assumption
  apply assumption
  done

lemma semantic_equiv_Seq_Skip:
  assumes se: "semantic_equiv Gamma s s' a a'"
  shows   "semantic_equiv Gamma s s' (a ;; SKIP) a'"
  using se unfolding semantic_equiv_def2
  by (simp add: exec_Seq_Skip_simps)

lemma semantic_equiv_Guard_cong:
  assumes se: "semantic_equiv Gamma s s' a a'"
  shows   "semantic_equiv Gamma s s' (Guard F G a) (Guard F G a')"
  using se
  by (simp add: semantic_equiv_def2 exec_Guard)

lemma semantic_equiv_Guard_UNIV:
  assumes se: "semantic_equiv Gamma s s' a a'"
  shows   "semantic_equiv Gamma s s' (Guard F UNIV a) a'"
  using se
  by (simp add: semantic_equiv_def2 exec_Guard_UNIV_simp)

lemma semantic_equiv_Guard_True:
  assumes se: "semantic_equiv Gamma s s' a a'"
  shows   "semantic_equiv Gamma s s' (Guard F \<lbrace>True\<rbrace> a) a'"
  using se
  by (simp add: semantic_equiv_def2 exec_Guard_UNIV_simp)

lemma semantic_equiv_refl:
  shows   "semantic_equiv Gamma s s' a a"
  by (rule semantic_equivI, simp)

lemma semantic_equiv_trans:
  assumes  sea: "semantic_equiv Gamma s s' a b"
  and      seb: "semantic_equiv Gamma s s' b c"
  shows   "semantic_equiv Gamma s s' a c"
  using sea seb
  by (simp add: semantic_equiv_def2)

(* Ugh, a bit tricky to get this outcome without this sort of specialisation :( *)
lemma semantic_equiv_Guard_Skip_Seq:
  shows   "semantic_equiv Gamma s s' (a ;; Guard F \<lbrace>True\<rbrace> SKIP) a"
  apply (rule semantic_equiv_trans)
  apply (rule semantic_equiv_Seq_cong)
  apply (rule semantic_equiv_refl)
  apply (rule semantic_equiv_Guard_True)
  apply (rule semantic_equiv_refl)
  apply (rule semantic_equiv_Seq_Skip)
  apply (rule semantic_equiv_refl)
  done

lemma semantic_equiv_Seq_assoc:
  shows   "semantic_equiv Gamma s s' (a ;; (b ;; c)) (a ;; b ;; c)"
  apply (rule semantic_equivI)
  apply (rule exec_assoc)
  done

lemma semantic_equiv_seq_assoc_eq:
  "semantic_equiv Gamma s s' (a ;; (b ;; c)) d
     = semantic_equiv Gamma s s' (a ;; b ;; c) d"
  "semantic_equiv Gamma s s' d (a ;; (b ;; c))
     = semantic_equiv Gamma s s' d (a ;; b ;; c)"
  by (metis semantic_equiv_trans semantic_equiv_Seq_assoc
            semantic_equiv_Seq_assoc[THEN semantic_equiv_sym[THEN iffD1]])+

lemma semantic_equiv_Cond:
  assumes  sel: "semantic_equiv Gamma s s' l l'"
  and      ser: "semantic_equiv Gamma s s' r r'"
  shows   "semantic_equiv Gamma s s' (Cond P l r) (Cond P l' r')"
  using sel ser
  by (auto elim!: exec_Normal_elim_cases simp: semantic_equiv_def2 intro: exec.intros)

lemma semantic_equiv_Cond_True:
  "semantic_equiv G s s' (Cond UNIV c c') c"
  by (auto elim!: exec_Normal_elim_cases simp: semantic_equiv_def2 intro: exec.intros)

lemma semantic_equiv_Cond_False:
  "semantic_equiv G s s' (Cond {} c c') c'"
  by (auto elim!: exec_Normal_elim_cases simp: semantic_equiv_def2 intro: exec.intros)

lemma semantic_equiv_Cond_cases:
  "semantic_equiv G s s' a (Cond P c d)
    = semantic_equiv G s s' a (if s \<in> P then c else d)"
  "semantic_equiv G s s' (Cond P c d) e
    = semantic_equiv G s s' (if s \<in> P then c else d) e"
  by (auto simp: semantic_equiv_def2 elim!: exec_Normal_elim_cases intro: exec.intros)

lemma semantic_equiv_cond_seq2:
  "semantic_equiv G s s' (e;; Cond Q (c;;d) (c';;d)) (e;; Cond Q c c';; d)"
  apply (simp add: semantic_equiv_seq_assoc_eq[symmetric])
  apply (rule semantic_equiv_Seq_cong, rule semantic_equiv_refl)
  by (auto simp: semantic_equiv_def2 elim!: exec_Normal_elim_cases intro: exec.intros)

lemmas ccorres_cond_seq2 = ccorres_semantic_equiv[OF semantic_equiv_cond_seq2]

lemma semantic_equiv_cond_seq2_seq:
  "semantic_equiv G s s' (ci;; Cond Q (c;;ce) (c';;ce);; d) (ci;; Cond Q c c';; ce;; d)"
  apply (simp add: semantic_equiv_seq_assoc_eq[symmetric])
  apply (rule semantic_equiv_Seq_cong, rule semantic_equiv_refl)
  apply (simp add: semantic_equiv_seq_assoc_eq)
  by (auto simp: semantic_equiv_def2 elim!: exec_Normal_elim_cases intro: exec.intros)

lemmas ccorres_cond_seq2_seq = ccorres_semantic_equiv[OF semantic_equiv_cond_seq2_seq]

(* FIXME: move
   It appears that the semantic equiv. lemmas should go into their own file, then
   CCorresLemmas on top of that, and then finally Ctac on top of CCorresLemmas *)
lemma ccorres_rewrite_cond_sr:
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> s' \<in> Q' \<longrightarrow> (s' \<in> C) = (s' \<in> C') "
  and     c1: "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs m (Cond C' c d)"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (P and Q) (P' \<inter> Q') hs
                              m (Cond C c d)"
  apply (rule ccorres_name_pre)
  apply (rule_tac Q="(=) s" and Q'="P' \<inter> Q' \<inter> {s'. (s, s') \<in> sr}" in stronger_ccorres_guard_imp)
    apply (rule ccorres_semantic_equiv[THEN iffD1, rotated])
     apply (rule ccorres_guard_imp, rule c1, simp_all)
  apply (clarsimp simp add: semantic_equiv_Cond_cases abs semantic_equiv_refl)
  done

lemma ccorres_rewrite_cond_sr_Seq:
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> s' \<in> Q' \<longrightarrow> (s' \<in> C) = (s' \<in> C') "
  and     c1: "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs m (Cond C' c d ;; e)"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (P and Q) (P' \<inter> Q') hs
                              m (Cond C c d ;; e)"
  apply (rule ccorres_name_pre)
  apply (rule_tac Q="(=) s" and Q'="P' \<inter> Q' \<inter> {s'. (s, s') \<in> sr}" in stronger_ccorres_guard_imp)
    apply (rule ccorres_semantic_equiv[THEN iffD1, rotated])
     apply (rule ccorres_guard_imp, rule c1, simp_all)
  apply (rule semantic_equiv_Seq_cong)
   apply (clarsimp simp add: semantic_equiv_Cond_cases abs semantic_equiv_refl)+
  done

definition
  "push_in_stmt G stmt c c' \<equiv> (\<forall>s s'. semantic_equiv G s s' (c ;; stmt) c')"

lemma pis_base:
  "push_in_stmt G stmt c (c ;; stmt)"
  unfolding push_in_stmt_def by (clarsimp intro!: semantic_equivI)

lemma pis_throw:
  "push_in_stmt G stmt THROW THROW"
  unfolding push_in_stmt_def
  by (auto elim!: exec_Normal_elim_cases intro: semantic_equivI exec.intros)

lemma pis_Seq_right:
  "push_in_stmt G stmt d d' \<Longrightarrow> push_in_stmt G stmt (c ;; d) (c ;; d')"
  unfolding push_in_stmt_def
  apply (intro allI)
  apply (rule semantic_equiv_trans [rotated])
  apply (rule semantic_equiv_Seq_cong [OF semantic_equiv_refl])
  apply (drule spec, drule spec, assumption)
  apply (subst semantic_equiv_sym)
  apply (rule semantic_equiv_Seq_assoc)
  done

lemma pis_creturn:
  "push_in_stmt G stmt (return_C xfu xf) (return_C xfu xf)"
  unfolding creturn_def
  by (rule pis_Seq_right | rule pis_throw)+

lemma pis_Cond:
  "\<lbrakk> push_in_stmt G stmt l l'; push_in_stmt G stmt r r' \<rbrakk> \<Longrightarrow>
  push_in_stmt G stmt (Cond P l r) (Cond P l' r')"
  unfolding push_in_stmt_def
  apply (intro allI)
  apply (drule_tac x = s in spec, drule_tac x = s' in spec)+
  apply (case_tac "s \<in> P")
  apply (auto elim!: exec_Normal_elim_cases simp: semantic_equiv_def2 intro: exec.intros)
  done

(* We check this before simplifying everything, so we need to deal with switch *)
lemma pis_switch_Cons:
  "\<lbrakk> push_in_stmt G stmt c c';
     push_in_stmt G stmt (switch v (x # xs)) (switch v cs)   \<rbrakk>
   \<Longrightarrow> push_in_stmt G stmt (switch v ((g, c) # (x # xs))) (switch v ((g, c') # cs))"
  by (simp add: pis_Cond)

lemma pis_switch_Singleton:
  "\<lbrakk> push_in_stmt G stmt c c' \<rbrakk> \<Longrightarrow> push_in_stmt G stmt (switch v [(UNIV, c)]) (switch v [(UNIV, c')])"
  apply (clarsimp simp: push_in_stmt_def)
  apply (rule semantic_equiv_trans [OF _ iffD2 [OF semantic_equiv_sym, OF semantic_equiv_Cond_True]])
  apply (rule semantic_equiv_trans [rotated])
  apply (drule spec, drule spec, assumption)
  apply (rule semantic_equiv_Seq_cong [OF semantic_equiv_Cond_True semantic_equiv_refl])
  done

lemma pis_Guard:
  "push_in_stmt G stmt c c' \<Longrightarrow> push_in_stmt G stmt (Guard f G' c) (Guard f G' c')"
  unfolding push_in_stmt_def
  apply (intro allI)
  apply (rule semantic_equiv_trans [OF Guard_Seq_semantic_equiv])
  apply (rule semantic_equiv_Guard_cong)
  apply (drule spec, erule spec)
  done

lemmas push_in_stmt_rules =
  \<comment> \<open>No ordering apart from pis_base which must be last.\<close>
  pis_throw
  pis_creturn
  pis_Seq_right
  pis_Cond
  pis_switch_Singleton pis_switch_Cons
  pis_Guard
  \<comment> \<open>Last, just stick it where it is\<close>
  pis_base

lemma ccorres_special_trim_guard_DontReach_pis:
  assumes at: "push_in_stmt Gamma (Guard DontReach {} c) b b'"
  and      c: "ccorres_underlying sr Gamma r xf ar axf G G' hs a b'"
  shows   "ccorres_underlying sr Gamma r xf ar axf G G' hs a (b ;; Guard DontReach {} c)"
  using c at unfolding push_in_stmt_def
  apply -
  apply (erule ccorres_semantic_equivD2)
  apply (drule spec, erule spec)
  done

end

lemmas ccorres_boilerplace_simp_dels =
  Collect_const \<comment> \<open>Avoid getting an implication due to if_split.  Should probably just remove if_split\<close>

lemmas ccorres_introduce_UNIV_Int_when_needed
  = ccorres_add_UNIV_Int[where G'="{x. Q x}" for Q]

lemma Normal_Abrupt_resultE [consumes 2, case_names normal abrupt]:
  assumes ex: "\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> t"
  and      t: "t = Normal t' \<or> t = Abrupt t'"
  and     r1: "\<And>s'. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Normal s'\<rangle> \<Rightarrow> t; s = Normal s'\<rbrakk> \<Longrightarrow> R"
  and     r2: "\<And>s'. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Abrupt s'\<rangle> \<Rightarrow> t; s = Abrupt s'\<rbrakk> \<Longrightarrow> R"
  shows   R
  using ex t
  apply -
  apply (erule disjE; simp)
   apply (erule Normal_resultE)
   apply (rule r1; simp)
  apply (erule Abrupt_resultE)
   apply (rule r1; simp)
  apply (rule r2)
   apply simp
  apply simp
  done

(* Used so we can pattern match in ceqv (and hopefully speed things up *)
definition
  "rewrite_xf xf t v f f' \<equiv> xf t = v \<longrightarrow> f t = f' t"

lemma rewrite_xfI:
  "(xf t = v \<Longrightarrow> f t = f' t) \<Longrightarrow> rewrite_xf xf t v f f'"
  unfolding rewrite_xf_def by auto

lemma rewrite_xfD:
  "\<lbrakk> rewrite_xf xf t v f f'; xf t = v \<rbrakk> \<Longrightarrow> f t = f' t"
  unfolding rewrite_xf_def by auto

lemma Basic_ceqv:
  assumes rl: "rewrite_xf xf t v f f'"
  shows   "ceqv \<Gamma> xf v t t' (Basic f) (Basic f')"
  apply -
  apply (rule ceqvI)
  apply (drule rewrite_xfD [OF rl])
  apply rule
   apply (erule exec_Normal_elim_cases)
   apply simp
   apply rule
  apply (erule exec_Normal_elim_cases)
  apply simp
  apply (erule subst)
  apply (rule exec.Basic)
  done

(* the tactic uses THEN_ALL_NEW, which goes backwards *)
lemma Seq_ceqv:
  assumes ra: "\<And>t'. ceqv \<Gamma> xf v t t' a a'"
  and     rb: "\<And>t. ceqv \<Gamma> xf v t t' b b'"
  and     xp: "xpres_strong \<Gamma> xf v a True pres_abr abnormal" (* Check that a does preserve xf first *)
  shows   "ceqv \<Gamma> xf v t t' (a ;; b) (a' ;; b')"
  using xp
  apply -
  apply (rule ceqvI)
  apply rule
   apply (erule exec_Normal_elim_cases)
   apply rule
    apply (erule (1) ceqvD1 [OF _ _ ra])
   apply (case_tac s')
      apply simp
      apply (erule ceqvD1)
       prefer 2
       apply (rule assms)
      apply (erule (2) xpres_execs[OF _ TrueI])
     apply (fastforce dest: Abrupt_end Fault_end Stuck_end)+
  (* clag *)
   apply (erule exec_Normal_elim_cases)
   apply rule
   apply (erule (1) ceqvD2 [OF _ _ ra])
    apply (case_tac s')
      apply simp
      apply (erule ceqvD2)
       prefer 2
       apply (rule assms)
      apply (rule xpres_execs[OF _ TrueI], assumption)
      apply (erule (1) ceqvD2 [OF _ _ ra])
     apply (fastforce dest: Abrupt_end Fault_end Stuck_end)+
     done

lemma Seq_weak_ceqv: (* A weaker form where xpres doesn't hold for a *)
  assumes ra: "\<And>t'. ceqv \<Gamma> xf v t t' a a'"
  shows   "ceqv \<Gamma> xf v t t' (a ;; b) (a' ;; b)"
  apply -
  apply (rule ceqvI)
  apply rule
   apply (erule exec_Normal_elim_cases)
   apply rule
   apply (erule (2) ceqvD1 [OF _ _ ra])
  (* clag *)
   apply (erule exec_Normal_elim_cases)
   apply rule
   apply (erule (2) ceqvD2 [OF _ _ ra])
   done

lemma xpres_ceqv:
  assumes xp: "xpres_strong \<Gamma> xf v a pres_norm pres_abr abnormal"
  and    ceq: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  shows  "xpres_strong \<Gamma> xf v a' pres_norm pres_abr False"
  apply (rule xpres_strongI)
  apply (drule (1) ceqvD2[OF _ _ ceq], erule (2) xpres_execs[OF xp])+
  by auto

lemma While_ceqv_na0:
  assumes ra: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  and     xp: "xpres_strong \<Gamma> xf v a True pabr abnormal"
  and     ex: "\<Gamma>\<turnstile> \<langle>d,s\<rangle> \<Rightarrow> t'"
  and    beq0: "\<And>t. xf t = v \<longrightarrow> (t \<in> b) = (t \<in> b')"
  and     d: "d = While b a"
  and     s: "s \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. pabr \<longrightarrow> xf s = v}"
  and     d': "d' = While b' a'"
  and     t: "\<not> isFault t'" "t' \<noteq> Stuck"
  shows   "\<Gamma>\<turnstile> \<langle>d',s\<rangle> \<Rightarrow> t'"
  using ex d s d' t
proof (induct)
  case (WhileTrue s' b'' c' t u)
  hence bv: "b'' = b" and cv: "c' = a" and xfs: "xf s' = v" by auto

  note xp = xpres_ceqv [OF xp ra]

  note beq = beq0 [rule_format]

  have "\<Gamma> \<turnstile> \<langle>While b' a', Normal s'\<rangle> \<Rightarrow> u"
  proof (rule exec.WhileTrue)
    show "s' \<in> b'" using beq xfs bv[symmetric] WhileTrue
      by auto

    show ae: "\<Gamma>\<turnstile> \<langle>a',Normal s'\<rangle> \<Rightarrow> t" using WhileTrue ceqvD1[OF _ _ ra]
      by auto
    show "\<Gamma>\<turnstile> \<langle>While b' a',t\<rangle> \<Rightarrow> u"
    proof (subst d' [symmetric], rule WhileTrue.hyps(5))
      obtain z where "u = Normal z \<or> u = Abrupt z"
        using WhileTrue.prems by (cases u, auto)
      then obtain z' where "t = Normal z' \<or> t = Abrupt z'"
        using WhileTrue.prems WhileTrue.hyps(2) WhileTrue.hyps(4)
        by (auto elim: Normal_resultE Abrupt_resultE)

      thus "t \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. pabr \<longrightarrow> xf s = v}" using xp ae xfs
        by (auto dest: xpres_execs)
    qed fact+
  qed
  thus ?case using WhileTrue.prems by simp
next
  note beq = beq0 [rule_format]

  case WhileFalse
  thus ?case
    apply simp
    apply rule
    apply (erule disjE)
     apply (erule imageE, simp)
     apply (auto simp: beq)
    done
qed simp_all

lemmas While_ceqv_na = While_ceqv_na0 [OF _ _ _ _ refl _ refl]

lemma While_ceqv_fs0:
  assumes ra: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  and     xp: "xpres_strong \<Gamma> xf v a True pabr abnormal"
  and     ex: "\<Gamma>\<turnstile> \<langle>d,x\<rangle> \<Rightarrow> t'"
  and     d: "d = While b a"
  and     d': "d' = While b' a'"
  and     beq0: "\<And>t. xf t = v \<longrightarrow> (t \<in> b) = (t \<in> b')"
  and     t: "isFault t' \<or> t' = Stuck"
  and     s: "x \<in> Normal ` {s. xf s = v}"
  shows   "\<Gamma>\<turnstile> \<langle>d',x\<rangle> \<Rightarrow> t'"
  using ex d d' t s
proof (induct)
  case (WhileTrue s' b'' c' t u)
  hence bv: "b'' = b" and cv: "c' = a" and xfs: "xf s' = v" by auto

  note xp = xpres_ceqv [OF xp ra]

  note beq = beq0 [rule_format]

  have "\<Gamma> \<turnstile> \<langle>While b' a', Normal s'\<rangle> \<Rightarrow> u"
  proof (rule exec.WhileTrue)
    show sb: "s' \<in> b'" using WhileTrue beq by auto

    show ae: "\<Gamma>\<turnstile> \<langle>a',Normal s'\<rangle> \<Rightarrow> t"
      using xfs WhileTrue ceqvD1[OF _ _ ra] by auto

    {
      fix f
      assume "u = Fault f" and "t = Fault f"
      hence "\<Gamma>\<turnstile> \<langle>While b' a',t\<rangle> \<Rightarrow> u" by simp
    } moreover
    {
      fix f z
      assume uv: "u = Fault f" and tv: "t = Normal z"

      have "\<Gamma>\<turnstile> \<langle>d',t\<rangle> \<Rightarrow> u"
      proof (rule WhileTrue.hyps(5))
        show "isFault u \<or> u = Stuck" using uv by simp
        have "xf z = v" using ae unfolding tv
          by (rule xpres_exec_Normal[OF xp TrueI _ xfs])

        thus "t \<in> Normal ` {s. xf s = v}" by (simp add: tv)
      qed fact+
      hence "\<Gamma>\<turnstile> \<langle>While b' a',t\<rangle> \<Rightarrow> u" using d' by simp
    } moreover
    {
      assume "u = Stuck" and "t = Stuck"
      hence "\<Gamma>\<turnstile> \<langle>While b' a',t\<rangle> \<Rightarrow> u" by simp
    } moreover
    {
      fix z
      assume uv: "u = Stuck" and tv: "t = Normal z"
      (* clag *)
      have "\<Gamma>\<turnstile> \<langle>d',t\<rangle> \<Rightarrow> u"
      proof (rule WhileTrue.hyps(5))
        show "isFault u \<or> u = Stuck" using uv by simp
        have "xf z = v" using ae unfolding tv
          by (rule xpres_exec_Normal[OF xp TrueI _ xfs])

        thus "t \<in> Normal ` {s. xf s = v}" by (simp add: tv)
      qed fact+
      hence "\<Gamma>\<turnstile> \<langle>While b' a',t\<rangle> \<Rightarrow> u" using d' by simp
    }
    ultimately show "\<Gamma>\<turnstile> \<langle>While b' a',t\<rangle> \<Rightarrow> u" using WhileTrue.prems WhileTrue.hyps(4)
      by (auto elim: Fault_resultE Stuck_resultE elim!: isFaultE)
  qed
  thus ?case by (simp add: d')
qed simp_all

lemmas While_ceqv_fs = While_ceqv_fs0 [OF _ _ _ refl refl]

lemma While_ceqv:
  assumes beq: "\<And>t. xf t = v \<longrightarrow> (t \<in> b) = (t \<in> b')"
  and      ra: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  and      xp: "xpres_strong \<Gamma> xf v a True pabr abnormal"   (* So we fail as early as possible *)
  shows   "ceqv \<Gamma> xf v t t' (While b a) (While b' a')" (* b is a set, doesn't rewrite nicely *)
  using xp
  apply -
  apply (rule ceqvI)
  apply (cases t')
     apply rule
      apply (erule (1) While_ceqv_na [OF ra])
         apply (rule beq)
        apply simp
       apply simp
      apply simp
     apply (rule While_ceqv_na [OF ceqv_sym [OF ra]])
          apply (erule (1) xpres_ceqv [OF _ ra])
        apply (rule impI)
        apply (erule beq [rule_format, symmetric])
       apply simp
      apply simp
     apply simp
    (* clag *)
    apply rule
     apply (erule (1) While_ceqv_na [OF ra])
        apply (rule beq)
       apply simp
      apply simp
     apply simp
    apply simp
    apply (rule While_ceqv_na [OF ceqv_sym [OF ra]])
         apply (erule (1) xpres_ceqv [OF _ ra])
       apply (rule impI)
       apply (erule beq [rule_format, symmetric])
      apply simp
     apply simp
    apply simp
   apply rule
    apply (erule While_ceqv_fs [OF ra xp])
      apply (rule beq)
     apply simp
    apply simp
   apply (rule While_ceqv_fs [OF ceqv_sym [OF ra]])
       apply (erule (1) xpres_ceqv [OF _ ra])
     apply (rule impI)
     apply (erule beq [rule_format, symmetric])
    apply simp
   apply simp
(* clag *)
  apply rule
   apply (erule While_ceqv_fs [OF ra xp])
     apply (rule beq)
    apply simp
   apply simp
  apply (rule While_ceqv_fs [OF ceqv_sym [OF ra]])
      apply (erule (1) xpres_ceqv [OF _ ra])
    apply (rule impI)
    apply (rule beq [rule_format, symmetric])
    apply simp
   apply simp
  apply simp
  done

lemma call_ceqv_hoarep_gen:
  assumes mod: "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/F s\<^esub> (P s) Call f (Q s),(A s)"
  assumes ieq: "\<And>s. rewrite_xf xf s v i i'"
  and    ceqv: "\<And>t t' s'. ceqv \<Gamma> xf v (r t s') t' (c t s') (c' t s')"
  and     xf:  "\<And>s t. xf s = v \<Longrightarrow> i' s \<in> P (x s) \<longrightarrow> t \<in> Q (x s) \<or> t \<in> A (x s) \<Longrightarrow> xf (r s t) = v"
  shows   "ceqv \<Gamma> xf v t t' (call i f r c) (call i' f r c')"
  apply (rule ceqvI)
  apply (rule iffI)
   apply (erule exec_call_Normal_elim)
       apply (drule ceqvD1[OF _ _ ceqv])
        apply (simp add: rewrite_xfD[OF ieq])
        apply (erule xf)
        apply (frule (1) hoarep_exec_call_body[OF mod], fastforce)
       apply (erule exec_call)
        apply (simp add: rewrite_xfD[OF ieq])
       apply assumption
      apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callAbrupt)
     apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callFault)
    apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callStuck)
   apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callUndefined)
  apply (erule exec_call_Normal_elim)
      apply (drule ceqvD2 [OF _ _ ceqv])
       apply (erule xf)
       apply (frule (1) hoarep_exec_call_body[OF mod], fastforce)
      apply (erule exec_call)
       apply (simp add: rewrite_xfD[OF ieq])
      apply assumption
     apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callAbrupt)
    apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callFault)
   apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callStuck)
  apply (clarsimp simp: rewrite_xfD[OF ieq] elim!: exec_callUndefined)
  done

lemmas call_ceqv = call_ceqv_hoarep_gen[OF hoarep_false_pre_gen, simplified]
lemmas call_ceqv_hoarep = call_ceqv_hoarep_gen[where P="\<lambda>s. {s}" and x=i and i=i for i, simplified]

lemma call_ceqv':
  assumes ieq: "\<And>t. rewrite_xf xf t v i i'"
  and    ceqv: "\<And>t t' s'. ceqv \<Gamma> xf v (r t s') t' (c t s') (c' t s')" (* For record field updates *)
  and     xf:  "\<And>t t'. xf (r t t') = xf t"
  shows   "ceqv \<Gamma> xf v t t' (call i f r c) (call i' f r c')"
  by (rule call_ceqv [OF ieq ceqv], simp add: xf)

lemmas Skip_ceqv = ceqv_refl [where c = Skip]

lemma Catch_ceqv:
  assumes ca: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  and     cb: "\<And>t t'. ceqv \<Gamma> xf v t t' b b'"
  and     xp: "xpres_strong \<Gamma> xf v a pnorm True abnormal"
  shows   "ceqv \<Gamma> xf v t t' (Catch a b) (Catch a' b')"
  apply (rule ceqvI)
  apply rule
   apply (erule exec_Normal_elim_cases)
    apply (drule (1) ceqvD1 [OF _ _ ca])
    apply (rule exec.CatchMatch, assumption)
    apply (erule ceqvD1 [OF _ _ cb])
    apply (erule (1) xpres_exec_Abrupt[OF xpres_ceqv[OF xp ca] TrueI])
   apply (rule exec.CatchMiss)
    apply (erule (1) ceqvD1 [OF _ _ ca])
   apply assumption
   apply (erule exec_Normal_elim_cases)
    apply (drule (1) ceqvD2 [OF _ _ ca])
    apply (rule exec.CatchMatch, assumption)
    apply (erule ceqvD2 [OF _ _ cb])
   apply (rule xpres_exec_Abrupt[OF xpres_ceqv[OF xp ca] TrueI, rotated], assumption)
   apply (erule (1) ceqvD1 [OF _ _ ca])
   apply (rule exec.CatchMiss)
    apply (erule (1) ceqvD2 [OF _ _ ca])
   apply assumption
   done

lemma Catch_ceqv_weak_imp:
  assumes "\<And>s t. ceqv \<Gamma> xf v s t c c'"
  assumes "xf s = v"
  assumes "\<Gamma> \<turnstile> \<langle>Catch c d, Normal s\<rangle> \<Rightarrow> t"
  shows "\<Gamma> \<turnstile> \<langle>Catch c' d, Normal s\<rangle> \<Rightarrow> t"
  using assms
  apply (clarsimp simp: ceqv_def)
  apply (erule exec_Normal_elim_cases; simp; erule (1) exec.intros)
  done

lemma Catch_ceqv_weak:
  assumes c: "\<And>s t. ceqv \<Gamma> xf v s t c c'"
  notes s = ceqv_sym[OF c]
  notes cs = c s
  shows "ceqv \<Gamma> xf v t t' (Catch c d) (Catch c' d)"
  by (intro ceqvI iffI; erule (1) cs[THEN Catch_ceqv_weak_imp])+

lemma Cond_ceqv:
  assumes be: "\<And>t. xf t = v \<longrightarrow> (t \<in> x) = (t \<in> x')"
  and     ca: "ceqv \<Gamma> xf v t t' a a'"
  and     cb: "ceqv \<Gamma> xf v t t' b b'"
  shows   "ceqv \<Gamma> xf v t t' (Cond x a b) (Cond x' a' b')"
  apply (rule ceqvI)
  apply rule
   apply (erule exec_Normal_elim_cases)
    apply (frule (1) iffD1 [OF be [rule_format]])
    apply (erule exec.CondTrue)
    apply (erule (1) ceqvD1 [OF _ _ ca])
   apply (subst (asm) be)
    apply assumption
   apply (erule exec.CondFalse)
   apply (erule (1) ceqvD1 [OF _ _ cb])
  (* clag *)
   apply (erule exec_Normal_elim_cases)
    apply (frule (1) iffD2 [OF be [ rule_format]])
    apply (erule exec.CondTrue)
    apply (erule (1) ceqvD2 [OF _ _ ca])
   apply (subst (asm) be [rule_format, symmetric])
    apply assumption
   apply (erule exec.CondFalse)
   apply (erule (1) ceqvD2 [OF _ _ cb])
   done

lemmas Throw_ceqv = ceqv_refl [where c = Throw]

lemma Collect_mem_eqv:
  "rewrite_xf xf t v Q Q' \<Longrightarrow> xf t = v \<longrightarrow> (t \<in> Collect Q) = (t \<in> Collect Q')"
  apply (rule impI)
  apply (drule (1) rewrite_xfD)
  apply simp
  done

(* We could just use ceqv_refl at the end, but I want to catch missed cases.
   I also assume that While and Cond have {s. P s} as conditionals.
   The WhileAnnot case is a consequence of While.
  *)

lemma UNIV_mem_eqv:
  "xf t = v \<longrightarrow> (t \<in> UNIV) = (t \<in> UNIV)"
  by simp

lemma empty_mem_eqv:
  "xf t = v \<longrightarrow> (t \<in> {}) = (t \<in> {})"
  by simp

lemma creturn_ceqv_xf:
  fixes \<Gamma> :: "(('a globals_scheme, 'b) myvars_scheme) c_body"
  assumes xfg: "\<And>s f. xf (global_exn_var_'_update f s) = xf s"
  and   xfxfu: "\<And>v s. xf (xfu (\<lambda>_. v) s) = v"
  shows   "ceqv \<Gamma> xf v t t' (return_C xfu xf) (return_C xfu (\<lambda>_. v))"
  unfolding creturn_def
  apply (rule Seq_ceqv)+
    apply (rule Basic_ceqv)
    apply (rule rewrite_xfI)
    apply simp
   apply (rule Seq_ceqv)
     apply (rule Basic_ceqv)
     apply (simp add: rewrite_xf_def)
    apply (rule Throw_ceqv)
   apply (rule xpres_basic)
   apply simp
   apply (simp add: xfg)
  apply (rule xpres_basic)
  apply (simp add: xfxfu)
  done

lemma creturn_ceqv_not_xf:
  fixes \<Gamma> :: "(('a globals_scheme, 'b) myvars_scheme) c_body"
  assumes rl: "\<And>t. rewrite_xf xf t v rv rv'"
  and    xfu: "\<And>s f. xf (xfu' f s) = xf s" \<comment> \<open>i.e., xf is independent of xfu\<close>
  and    xfg: "\<And>s f. xf (global_exn_var_'_update f s) = xf s"
  shows   "ceqv \<Gamma> xf v t t' (return_C xfu' rv) (return_C xfu' rv')"
  unfolding creturn_def
  apply (rule Seq_ceqv)+
    apply (rule Basic_ceqv)
    apply (rule rewrite_xfI)
    apply (simp add: rewrite_xfD [OF rl] xfu)
   apply (rule Seq_ceqv)
     apply (rule Basic_ceqv)
     apply (simp add: rewrite_xf_def)
    apply (rule Throw_ceqv)
   apply (rule xpres_basic)
   apply (simp add: xfg)
  apply (rule xpres_basic)
  apply (simp add: xfu)
  done

lemma Guard_ceqv:
  assumes be: "\<And>t. xf t = v \<longrightarrow> (t \<in> x) = (t \<in> x')"
  and     ca: "ceqv \<Gamma> xf v t t' a a'"
  shows   "ceqv \<Gamma> xf v t t' (Guard f x a) (Guard f x' a')"
  apply (rule ceqvI)
  apply rule
   apply (erule exec_Normal_elim_cases)
    apply (frule (1) iffD1 [OF be [rule_format]])
    apply (erule exec.Guard)
    apply (erule (1) ceqvD1 [OF _ _ ca])
   apply (subst (asm) be)
    apply assumption
   apply simp
   apply (erule exec.GuardFault)
  apply (erule exec_Normal_elim_cases)
   apply (frule (1) iffD2 [OF be [rule_format]])
   apply (erule exec.Guard)
   apply (erule (1) ceqvD2 [OF _ _ ca])
  apply (subst (asm) be [rule_format, symmetric])
   apply assumption
  apply simp
  apply (erule exec.GuardFault)
  done

lemma Cond_UNIV_ceqv: (* Crops up occasionally *)
  assumes ca: "ceqv \<Gamma> xf v t t' a a'"
  shows   "ceqv \<Gamma> xf v t t' (Cond UNIV a b) a'"
  using ca
  apply -
  apply (rule ceqvI)
  apply (auto elim!: exec_Normal_elim_cases dest: ceqvD1 ceqvD2 intro: exec.intros)
  done

lemma Cond_empty_ceqv: (* Crops up occasionally *)
  assumes ca: "ceqv \<Gamma> xf v t t' b b'"
  shows   "ceqv \<Gamma> xf v t t' (Cond {} a b) b'"
  using ca
  apply -
  apply (rule ceqvI)
  apply (auto elim!: exec_Normal_elim_cases dest: ceqvD1 ceqvD2 intro: exec.intros)
  done

lemmas Guard_UNIV_ceqv = Guard_ceqv [where x = UNIV and x' = UNIV, simplified]

lemmas ceqv_rules = ceqv_refl [where xf' = xfdc] \<comment> \<open>Any ceqv with xfdc should be ignored\<close>
  While_ceqv [OF Collect_mem_eqv] While_ceqv [OF UNIV_mem_eqv]
  Cond_ceqv [OF Collect_mem_eqv] Cond_UNIV_ceqv Cond_empty_ceqv
  Guard_ceqv [OF Collect_mem_eqv] Guard_UNIV_ceqv
  Seq_ceqv Seq_weak_ceqv
  Basic_ceqv call_ceqv' Skip_ceqv
  Catch_ceqv Throw_ceqv
  creturn_ceqv_xf creturn_ceqv_not_xf \<comment> \<open>order is important with these two, the second is more general\<close>
  ceqv_refl [where c = return_void_C] ceqv_refl [where c = break_C]
  ceqv_refl [where c = catchbrk_C]

\<comment> \<open>
Equivalence of SIMPL commands under the assumption that a variable contains a specified value.
Intended to be used to calculate output parameters from input parameters.
Stronger than `ceqv`, since it can also calculate the conditions under which the variable's
value is preserved.

Input parameters:
- c: The SIMPL command under consideration.
- pres_cont: false if execution of a previous command terminates normally
  without preserving the value of the variable.
- xf: a function that extracts the value of a particular variable from the state.
- v: if `pres_cont` is true, the presumed value of the variable prior to executing `c`.

Output parameters:
- pres_norm: true if syntactic analysis shows that the variable still has
  the value `v` whenever `c` terminates normally.
- pres_abr: true if syntactic analysis shows that the variable still has
  the value `v` whenever `c` terminates abruptly.
- abnormal: true if syntactic analysis shows that `c` never terminates normally.
- c': a command that is equivalent to `c`, with the intention that occurrences of the
  variable have been replaced with the value `v` in any context where that value is
  known to have been preserved.
\<close>
definition
  ceqv_xpres :: "(('s,'p,'f) body) \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> bool \<Rightarrow> ('s,'p,'f) com
                 \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('s,'p,'f) com \<Rightarrow> bool"
where
  "ceqv_xpres \<Gamma> xf v pres_cont c pres_norm pres_abr abnormal c'
   \<equiv> (\<not> pres_cont \<longrightarrow> (pres_norm \<longleftrightarrow> abnormal) \<and> \<not> pres_abr \<and> c' = c)
     \<and> (\<forall>s t. ceqv \<Gamma> xf v s t c c')
     \<and> xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"

lemmas ceqv_xpres_defs = ceqv_xpres_def ceqv_def xpres_strong_def

lemma ceqv_xpresI:
  assumes "\<And>s t. ceqv \<Gamma> xf v s t c c'"
  assumes "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  shows "ceqv_xpres \<Gamma> xf v True c pres_norm pres_abr abnormal c'"
  using assms by (simp add: ceqv_xpres_def)

lemma ceqv_xpres_ceqvD:
  assumes "ceqv_xpres \<Gamma> xf v True c pres_norm pres_abr abnormal c'"
  shows "ceqv \<Gamma> xf v s t c c'"
  using assms by (simp add: ceqv_xpres_def)

lemma ceqv_xpres_xpresD:
  assumes "ceqv_xpres \<Gamma> xf v True c pres_norm pres_abr abnormal c'"
  shows "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  using assms by (simp add: ceqv_xpres_def)

lemma ceqv_xpres_abnormalD:
  assumes "ceqv_xpres \<Gamma> xf v pres_cont c pres_norm pres_abr abnormal c'"
  shows "xpres_abnormal \<Gamma> c abnormal"
  using assms by (auto simp: ceqv_xpres_def xpres_strong_def xpres_abnormal_def)

lemma ceqv_xpres_abnormal_iff:
  "ceqv_xpres \<Gamma> xf v False c abnormal False abnormal c \<longleftrightarrow> xpres_abnormal \<Gamma> c abnormal"
  by (auto simp: ceqv_xpres_def xpres_strong_def xpres_abnormal_def ceqv_refl)

lemmas ceqv_xpres_abnormalI = ceqv_xpres_abnormal_iff[THEN iffD2]

definition
  ceqv_xpres_rewrite_set :: "('s \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> bool" where
 "ceqv_xpres_rewrite_set xf v S S'
    \<equiv> \<forall>s. xf s = v \<longrightarrow> (s \<in> S) = (s \<in> S')"

definition
  ceqv_xpres_rewrite_basic :: "('s \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> bool" where
 "ceqv_xpres_rewrite_basic xf v f f'
    \<equiv> \<forall>s. xf s = v \<longrightarrow> f s = f' s"

(* The trace argument can be any term. It will be included in a message emitted by the tactic
   which solves ceqv_xpres_basic_preserves subgoals, in cases where the tactic fails to prove
   that xf was preserved by the Basic block. *)
definition ceqv_xpres_basic_preserves ::
  "'trace \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> bool \<Rightarrow> bool"
  where
  "ceqv_xpres_basic_preserves trace xf v P f b \<equiv> b \<longrightarrow> (\<forall>s. xf s = v \<longrightarrow> P s \<longrightarrow> xf (f s) = v)"

definition
  ceqv_xpres_call_restore_args :: "'a \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> bool"
where
 "ceqv_xpres_call_restore_args x f g = (f = g)"

lemma ceqv_xpres_xfdc:
  "ceqv_xpres \<Gamma> xfdc v pres c pres pres False c"
  by (auto simp: ceqv_xpres_defs)

lemma ceqv_xpres_call_restore_argsI:
  "\<forall> s. f s = g s \<Longrightarrow> ceqv_xpres_call_restore_args i f g"
  by (simp add: ceqv_xpres_call_restore_args_def fun_eq_iff)

lemma ceqv_xpres_whileAnno:
  "\<lbrakk> ceqv_xpres \<Gamma> xf v True c pres_norm pres_abr abnormal c'; ceqv_xpres_rewrite_set xf v S S';
         xpres_eq_If pres_norm c' c c''; xpres_eq_If pres_norm S' S S'';
         xpres_eq_If pres_norm pres_abr False pres_abr' \<rbrakk>
     \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (whileAnno S I V c) pres_norm pres_abr' False (whileAnno S'' I V c'')"
  unfolding whileAnno_def
  apply (cases pres_norm)
   apply (clarsimp simp add: ceqv_xpres_def xpres_eq_If_def)
   apply (intro conjI allI)
    apply (rule While_ceqv)
      apply (simp add: ceqv_xpres_rewrite_set_def)
     apply simp
    apply (erule xpres_ceqv)
    apply (rule ceqv_refl)
   apply (erule xpres_strong_while, rule xpres_eq_If_rules)
  apply (clarsimp simp: ceqv_xpres_def ceqv_def xpres_strong_def xpres_eq_If_def)
  done

lemmas ceqv_xpres_While = ceqv_xpres_whileAnno[unfolded whileAnno_def]

lemma ceqv_xpres_Cond:
  assumes rws: "ceqv_xpres_rewrite_set xf v S S'"
  assumes cxs: "ceqv_xpres \<Gamma> xf v True c c_pres_norm c_pres_abr c_abnormal c'"
               "ceqv_xpres \<Gamma> xf v True d d_pres_norm d_pres_abr d_abnormal d'"
  \<comment> \<open>pres_norm \<longleftrightarrow> abnormal \<or> c_pres_norm \<and> d_pres_norm \<or> c_abnormal \<and> d_pres_norm \<or> c_pres_norm \<and> d_abnormal\<close>
  \<comment> \<open>pres_abr \<longleftrightarrow> c_pres_abr \<and> d_pres_abr\<close>
  \<comment> \<open>abnormal \<longleftrightarrow> c_abnormal \<and> d_abnormal\<close>
  assumes ifs: "xpres_eq_If c_abnormal d_abnormal False abnormal"
               "xpres_eq_If c_pres_norm d_pres_norm False cd_pres_norm"
               "xpres_eq_If c_abnormal d_pres_norm False ca_pres_norm"
               "xpres_eq_If c_pres_norm d_abnormal False da_pres_norm"
               "xpres_eq_If ca_pres_norm True da_pres_norm cda_pres_norm"
               "xpres_eq_If cd_pres_norm True cda_pres_norm pres_norm'"
               "xpres_eq_If abnormal True pres_norm' pres_norm"
               "xpres_eq_If c_pres_abr d_pres_abr False pres_abr"
  shows "ceqv_xpres \<Gamma> xf v True (Cond S c d) pres_norm pres_abr abnormal (Cond S' c' d')"
  apply (rule ceqv_xpresI[OF Cond_ceqv[OF _ cxs[THEN ceqv_xpres_ceqvD]]
                                  xpres_strong_cond[OF cxs[THEN ceqv_xpres_xpresD] ifs]])
  using rws by (simp add: ceqv_xpres_rewrite_set_def)

lemma ceqv_xpres_Guard:
  assumes "ceqv_xpres_rewrite_set xf v S S'"
  assumes "ceqv_xpres \<Gamma> xf v True c pres_norm pres_abr abnormal c'"
  shows "ceqv_xpres \<Gamma> xf v True (Guard g S c) pres_norm pres_abr abnormal (Guard g S' c')"
  using assms
  apply (clarsimp simp: ceqv_xpres_def xpres_strong_guard)
  apply (rule Guard_ceqv)
   apply (simp add: ceqv_xpres_rewrite_set_def)
  apply simp
  done

lemma ceqv_xpres_Seq:
  assumes cxc: "ceqv_xpres \<Gamma> xf v True c c_pres_norm c_pres_abr c_abnormal c'"
  assumes cxd: "ceqv_xpres \<Gamma> xf v c_pres_norm d d_pres_norm d_pres_abr d_abnormal d'"
  notes cxs = cxc cxd
  \<comment> \<open>abnormal \<longleftrightarrow> c_abnormal \<or> d_abnormal\<close>
  \<comment> \<open>pres_norm \<longleftrightarrow> c_pres_norm \<and> d_pres_norm \<or> abnormal\<close>
  \<comment> \<open>pres_abr \<longleftrightarrow> c_pres_abr \<and> c_pres_norm \<and> d_pres_abr \<or> c_abnormal \<and> c_pres_abr\<close>
  assumes ifs: "xpres_eq_If c_abnormal True d_abnormal abnormal"
               "xpres_eq_If c_pres_norm d_pres_norm False cd_pres_norm"
               "xpres_eq_If cd_pres_norm True abnormal pres_norm"
               "xpres_eq_If c_pres_norm d_pres_abr False c_norm_d_pres_abr"
               "xpres_eq_If c_pres_abr c_norm_d_pres_abr False cd_pres_abr"
               "xpres_eq_If c_abnormal c_pres_abr False c_abnormal_pres_abr"
               "xpres_eq_If cd_pres_abr True c_abnormal_pres_abr pres_abr"
  shows "ceqv_xpres \<Gamma> xf v True (c ;; d) pres_norm pres_abr abnormal (c' ;; d')"
proof (cases c_pres_norm)
  case True
  note cxs' = cxs[simplified True]
  note ceqvs = cxs'[THEN ceqv_xpres_ceqvD]
  note xpres = cxs'[THEN ceqv_xpres_xpresD]
  note ifs' = ifs[simplified True]
  show ?thesis
  apply (rule ceqv_xpresI[OF Seq_ceqv[OF ceqvs xpres(1)]])
  apply (rule xpres_strong_seq[OF xpres ifs'])
  done
next
  case False
  have 1: "d_pres_norm = d_abnormal \<and> \<not> d_pres_abr \<and> d' = d"
    using cxd by (simp add: False ceqv_xpres_def)
  have 2: "\<not> c_abnormal"
    using cxc by (simp add: False ceqv_xpres_def xpres_strong_def)
  have 3: "abnormal = d_abnormal \<and> pres_norm = d_abnormal \<and> \<not> pres_abr"
    using 1 2 ifs by (auto simp add: xpres_eq_If_def if_bool_simps)
  show ?thesis
  apply (simp add: 1 3)
  apply (rule ceqv_xpresI[OF Seq_weak_ceqv[OF ceqv_xpres_ceqvD, OF cxc]])
  apply (clarsimp simp: xpres_strong_def cong: conj_cong elim!: exec_Normal_elim_cases)
  apply (erule Normal_resultE, erule (1) xpres_abnormalD[OF cxd[THEN ceqv_xpres_abnormalD]])
  done
qed

lemma ceqv_xpres_Basic:
  assumes "ceqv_xpres_rewrite_basic xf v f f'"
  assumes "ceqv_xpres_basic_preserves (Basic f) xf v \<top> f' pres"
  shows "ceqv_xpres \<Gamma> xf v True (Basic f) pres pres_abr False (Basic f')"
  using assms
  apply (simp add: ceqv_xpres_def ceqv_xpres_rewrite_basic_def ceqv_xpres_basic_preserves_def)
  apply (intro allI impI conjI)
   apply (rule Basic_ceqv)
   apply (simp add: rewrite_xf_def)
  apply (rule xpres_strong_basic', simp)
  done

(* `call` needs special handling for `ceqv_xpres`, so it has its own predicate.
   If `xf` is a global variable, then the tactic needs to find the `modifies` lemma
   for the function `f`. Although the Simpl framework allows the fourth parameter
   of a `call` node to be an arbitrary command, the C parser only produces `call`
   nodes in which the fourth parameter is a `Basic` node. We only support that form. *)
definition ceqv_xpres_call where
  "ceqv_xpres_call \<Gamma> xf v f glob i ret pres_norm pres_abr abnormal i' ret'
   \<equiv> ceqv_xpres \<Gamma> xf v True (call i f glob ret) pres_norm pres_abr abnormal (call i' f glob ret')"

lemma ceqv_xpres_call_ceqv_xpres:
  assumes "ceqv_xpres_call \<Gamma> xf v f glob i ret pres_norm pres_abr abnormal i' ret'"
  shows "ceqv_xpres \<Gamma> xf v True (call i f glob ret) pres_norm pres_abr abnormal (call i' f glob ret')"
  using assms by (simp add: ceqv_xpres_call_def)

lemma ceqv_xpres_call_hoarep_gen:
  assumes mod: "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/F s\<^esub> (P s) Call f (Q s),(A s)"
  assumes args: "ceqv_xpres_call_restore_args f i i''"
  assumes init: "ceqv_xpres_rewrite_basic xf v i'' i'"
  assumes reset: "\<And>t. ceqv_xpres_basic_preserves (call i f reset ret) xf v
                        (\<lambda>s. i' s \<in> P (x s) \<longrightarrow> t \<in> Q (x s) \<or> t \<in> A (x s))
                        (\<lambda>s. reset s t) pres_reset"
  assumes xpr: "\<And>s t. ceqv_xpres \<Gamma> xf v pres_reset (ret s t) pres_norm pres_abr abnormal (ret' s t)"
  shows "ceqv_xpres_call \<Gamma> xf v f reset i ret pres_norm pres_abr abnormal i' ret'"
proof (cases pres_reset)
  case True
  note xpr' = xpr[simplified True]
  show ?thesis
  unfolding ceqv_xpres_call_def args[unfolded ceqv_xpres_call_restore_args_def]
  apply (rule ceqv_xpresI)
   apply (rule call_ceqv_hoarep_gen[OF mod _ xpr'[THEN ceqv_xpres_ceqvD]])
    apply (simp add: rewrite_xf_def init[unfolded ceqv_xpres_rewrite_basic_def])
   using reset apply (fastforce simp: True ceqv_xpres_basic_preserves_def)
  apply (rule xpres_strong_call_hoarep_gen[OF mod _ ceqv_xpres_xpresD[OF xpr']])
  using reset by (fastforce simp: True ceqv_xpres_basic_preserves_def
                                  init[unfolded ceqv_xpres_rewrite_basic_def])
next
  case False
  have 1: "pres_norm = abnormal \<and> \<not> pres_abr \<and> ret' = ret"
    using xpr by (auto simp: False ceqv_xpres_def)
  then show ?thesis
  unfolding ceqv_xpres_call_def args[unfolded ceqv_xpres_call_restore_args_def]
  using init xpr[simplified False, THEN ceqv_xpres_abnormalD]
  apply (clarsimp simp add: 1 ceqv_xpres_def ceqv_def ceqv_xpres_rewrite_basic_def
                            xpres_strong_abnormal_iff xpres_abnormal_call)
  by (auto elim!: exec_call_Normal_elim exec_call
                  exec_callAbrupt exec_callFault exec_callStuck exec_callUndefined)
qed

lemmas ceqv_xpres_call
  = ceqv_xpres_call_hoarep_gen[OF hoarep_false_pre_gen, simplified]
lemmas ceq_xpres_call_hoarep
  = ceqv_xpres_call_hoarep_gen[where P="\<lambda>s. {s}" and x=i' and i'=i' for i', simplified]

lemma ceqv_xpres_Skip:
  "ceqv_xpres \<Gamma> xf v True Skip True True False Skip"
  by (simp add: ceqv_xpres_def Skip_ceqv xpres_skip)

lemma ceqv_xpres_Catch:
  assumes cxc: "ceqv_xpres \<Gamma> xf v True c c_pres_norm c_pres_abr c_abnormal c'"
  assumes cxd: "ceqv_xpres \<Gamma> xf v c_pres_abr d d_pres_norm d_pres_abr d_abnormal d'"
  notes cxs = cxc cxd
  \<comment> \<open>abnormal \<longleftrightarrow> c_abnormal \<and> d_abnormal\<close>
  \<comment> \<open>pres_norm \<longleftrightarrow> abnormal \<or> c_pres_norm \<and> c_pres_abr \<and> d_pres_norm\<close>
  \<comment> \<open>pres_abr \<longleftrightarrow> c_pres_abr \<and> c_pres_abr\<close>
  assumes rew: "xpres_eq_If c_abnormal d_abnormal False abnormal"
               "xpres_eq_If c_pres_norm c_pres_abr False c_pres_norm_abr"
               "xpres_eq_If c_pres_norm_abr d_pres_norm False cd_pres_norm"
               "xpres_eq_If abnormal True cd_pres_norm pres_norm"
               "xpres_eq_If c_pres_abr d_pres_abr False pres_abr"
  shows "ceqv_xpres \<Gamma> xf v True (Catch c d) pres_norm pres_abr abnormal (Catch c' d')"
proof (cases c_pres_abr)
  case True
  note cxs' = cxs[simplified True]
  note ceqvs = cxs'[THEN ceqv_xpres_ceqvD]
  note xpres = cxs'[THEN ceqv_xpres_xpresD]
  note rew' = rew[simplified True]
  show ?thesis
  apply (rule ceqv_xpresI[OF Catch_ceqv[OF ceqvs xpres(1)]])
  apply (rule xpres_strong_catch[OF xpres rew'])
  done
next
  case False
  have 1: "d_pres_norm = d_abnormal \<and> \<not> d_pres_abr \<and> d' = d"
    using cxd by (simp add: False ceqv_xpres_def)
  have 3: "abnormal = (d_abnormal \<and> c_abnormal) \<and> pres_norm = abnormal \<and> \<not> pres_abr"
    using 1 rew by (auto simp add: False xpres_eq_If_def if_bool_simps)
  show ?thesis
  apply (simp add: 1 3)
  apply (rule ceqv_xpresI[OF Catch_ceqv_weak[OF cxc[THEN ceqv_xpres_ceqvD]]])
  apply (clarsimp simp: xpres_strong_def cong: conj_cong)
  apply (erule exec_Normal_elim_cases
         ; erule Normal_resultE
         ; erule (1) cxs[THEN ceqv_xpres_abnormalD, THEN xpres_abnormalD])+
  done
qed

lemma exec_Basic_Seq:
  "\<Gamma> \<turnstile> \<langle>Basic f ;; c, Normal s\<rangle> \<Rightarrow> s'
     = \<Gamma> \<turnstile> \<langle>c, Normal (f s)\<rangle> \<Rightarrow> s'"
  by (auto elim: exec_elim_cases intro: exec.Basic exec.Seq)

lemma exec_Basic_Seq_Basic:
  "\<Gamma>\<turnstile> \<langle>Basic f;; Basic g, x\<rangle> \<Rightarrow> y = \<Gamma>\<turnstile> \<langle>Basic (g \<circ> f), x\<rangle> \<Rightarrow> y"
  by (auto simp: o_def elim: exec_elim_cases intro: exec.Basic exec.Seq)

lemma ceqv_xpres_creturn:
  assumes "abnormal \<longrightarrow> pres_norm"
  assumes "ceqv_xpres_rewrite_basic xf v qf qf'"
  assumes "\<And>f. ceqv_xpres_basic_preserves (creturn exu xfu qf, 1) xf v \<top> (xfu f) pres'"
  assumes "\<And>f. ceqv_xpres_basic_preserves (creturn exu xfu qf, 2) xf v \<top> (exu f) pres''"
  assumes "xpres_eq_If pres' pres'' False pres"
  shows "ceqv_xpres \<Gamma> xf v True (creturn exu xfu qf) pres_norm pres abnormal (creturn exu xfu qf')"
  using assms
  apply (simp add: ceqv_xpres_defs ceqv_xpres_rewrite_basic_def
                   ceqv_xpres_basic_preserves_def creturn_def
                   xpres_eq_If_def if_bool_simps)
  apply (auto elim!: exec_elim_cases simp: exec_Basic_Seq)
  done

lemma ceqv_xpres_Throw:
  "ceqv_xpres \<Gamma> xf v True Throw True True abnormal Throw"
  by (simp add: ceqv_xpres_def Throw_ceqv xpres_strong_throw')

lemma ceqv_xpres_creturn_void:
  assumes "abnormal \<longrightarrow> pres_norm"
  assumes "\<And>f. ceqv_xpres_basic_preserves (creturn_void exu) xf v \<top> (exu f) pres"
  shows "ceqv_xpres \<Gamma> xf v True (creturn_void exu) pres_norm pres abnormal (creturn_void exu)"
  using assms by (auto simp: ceqv_xpres_defs creturn_void_def ceqv_xpres_basic_preserves_def
                      elim!: exec_elim_cases)

lemma ceqv_xpres_cbreak:
  assumes "abnormal \<longrightarrow> pres_norm"
  assumes "\<And>f. ceqv_xpres_basic_preserves (cbreak exu) xf v \<top> (exu f) pres"
  shows "ceqv_xpres \<Gamma> xf v True (cbreak exu) pres_norm pres abnormal (cbreak exu)"
  using assms by (auto simp: ceqv_xpres_defs cbreak_def ceqv_xpres_basic_preserves_def
                      elim!: exec_elim_cases)

lemma ceqv_xpres_ccatchbrk:
  "ceqv_xpres \<Gamma> xf v True (ccatchbrk exv) True True False (ccatchbrk exv)"
  by (auto simp: ceqv_xpres_defs ccatchbrk_def ceqv_xpres_basic_preserves_def
          elim!: exec_elim_cases)

definition
  "ceqv_xpres_lvar_nondet_init xf v_upd pres \<equiv> pres \<longrightarrow> (\<forall>s v. xf (v_upd (\<lambda>_. v) s) = xf s)"

lemma ceqv_xpres_lvar_nondet_init:
  "ceqv_xpres_lvar_nondet_init xf v_upd pres \<Longrightarrow>
   ceqv_xpres \<Gamma> xf v True (lvar_nondet_init v_acc v_upd) pres pres_abr False (lvar_nondet_init v_acc v_upd)"
  apply (clarsimp simp: ceqv_xpres_defs lvar_nondet_init_def ceqv_xpres_lvar_nondet_init_def)
  apply (intro conjI impI; erule exec.cases; clarsimp)
  done

\<comment> \<open>
Some ceqv_xpres rules as stated above are too general for the automation, and need to
be instantiated to ensure that output parameters are fully determined by input parameters.
The instantiations we use in `ceqv_xpres_rules` allow us to take advantage of exceptional
control flow.
\<close>

lemmas ceqv_xpres_returns
  = ceqv_xpres_creturn ceqv_xpres_creturn_void ceqv_xpres_cbreak

lemmas ceqv_xpres_basics
  = ceqv_xpres_Basic ceqv_xpres_lvar_nondet_init

lemmas ceqv_xpres_rules =
  ceqv_xpres_xfdc ceqv_xpres_whileAnno ceqv_xpres_While ceqv_xpres_Cond ceqv_xpres_Guard
  ceqv_xpres_Seq ceqv_xpres_call_ceqv_xpres ceqv_xpres_Skip ceqv_xpres_Catch ceqv_xpres_ccatchbrk
  ceqv_xpres_abnormalI
  ceqv_xpres_Throw[where abnormal=True]
  ceqv_xpres_returns[where pres_norm=True and abnormal=True, simplified]
  ceqv_xpres_basics[where pres_abr=True]

lemma ceqv_xpres_FalseI:
  "ceqv_xpres \<Gamma> xf v pres c False False False c"
  by (simp add: ceqv_xpres_defs)

lemma ceqv_xpres_rewrite_basic_left_cong:
  "\<lbrakk> \<And>s. xf s = v \<Longrightarrow> f s = f'' s \<rbrakk>
     \<Longrightarrow> ceqv_xpres_rewrite_basic xf v f f'
           = ceqv_xpres_rewrite_basic xf v f'' f'"
  by (simp add: ceqv_xpres_rewrite_basic_def)

lemma ceqv_xpres_rewrite_basic_refl:
  "ceqv_xpres_rewrite_basic xf v f f"
  by (simp add: ceqv_xpres_rewrite_basic_def)

lemma ceqv_xpres_basic_preserves_TrueI:
  "\<lbrakk> \<And>s. xf s = v \<longrightarrow> P s \<longrightarrow> xf (f s) = v \<rbrakk> \<Longrightarrow> ceqv_xpres_basic_preserves trace xf v P f True"
  by (simp add: ceqv_xpres_basic_preserves_def)

lemma ceqv_xpres_basic_preserves_FalseI:
  "ceqv_xpres_basic_preserves trace xf v P f False"
  by (simp add: ceqv_xpres_basic_preserves_def)

lemma ceqv_xpres_lvar_nondet_init_TrueI:
  "(\<And>s v. xf (v_upd (\<lambda>_. v) s) = xf s) \<Longrightarrow> ceqv_xpres_lvar_nondet_init xf v_upd True"
  by (simp add: ceqv_xpres_lvar_nondet_init_def)

lemma ceqv_xpres_lvar_nondet_init_FalseI:
  "ceqv_xpres_lvar_nondet_init xf v_upd False"
  by (simp add: ceqv_xpres_lvar_nondet_init_def)

lemma ceqv_xpres_rewrite_set_rules:
  "ceqv_xpres_rewrite_basic xf v P P'
     \<Longrightarrow> ceqv_xpres_rewrite_set xf v {s. P s} {s. P' s}"
  "ceqv_xpres_rewrite_set xf v UNIV UNIV"
  "ceqv_xpres_rewrite_set xf v {} {}"
  "\<lbrakk> ceqv_xpres_rewrite_set xf v S S''; ceqv_xpres_rewrite_set xf v S' S''' \<rbrakk>
     \<Longrightarrow> ceqv_xpres_rewrite_set xf v (if G then S else S') (if G then S'' else S''')"
  by (simp_all add: ceqv_xpres_rewrite_set_def ceqv_xpres_rewrite_basic_def
             split: if_split)

\<comment> \<open>\<close>

definition ccorres_save_pre where
  "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S G' hs a c
   \<equiv> ccorres_underlying srel \<Gamma> rrel xf arrel axf G (G' \<inter> S) hs a c"

lemma ccorres_save_pre_iff:
  assumes "G'' \<inter> S' = G' \<inter> S"
  shows "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S G' hs a c
         \<longleftrightarrow> ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S' G'' hs a c"
  by (simp add: ccorres_save_pre_def assms)

lemma ccorres_save_pre_move:
  "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G (S \<inter> E) G' hs a c
   \<longleftrightarrow> ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S (G' \<inter> E) hs a c"
  by (rule ccorres_save_pre_iff; blast)

lemmas ccorres_save_pre_push = ccorres_save_pre_move[THEN iffD1]
lemmas ccorres_save_pre_pop = ccorres_save_pre_move[THEN iffD2]

lemma ccorres_save_pre_trivial:
  "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G UNIV G' hs a c
   \<longleftrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs a c"
  unfolding ccorres_save_pre_def by simp

lemmas ccorres_save_pre_start = ccorres_save_pre_trivial[THEN iffD1]

lemmas ccorres_save_pre_finish
  = ccorres_save_pre_trivial[THEN iffD2]
    ccorres_save_pre_pop

lemma ccorres_save_pre_dup_iff:
  "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G (S \<inter> E) (G' \<inter> E) hs a c
   \<longleftrightarrow> ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S (G' \<inter> E) hs a c"
  by (rule ccorres_save_pre_iff; blast)

lemma ccorres_save_pre_Int_def:
  "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S (G' \<inter> E) hs m c
   \<longleftrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf G (G' \<inter> S \<inter> E) hs m c"
  by (prop_tac "G' \<inter> E \<inter> S = G' \<inter> S \<inter> E", blast, simp add: ccorres_save_pre_def)

\<comment> \<open>If we use this rule for the first lift in `cinit`, then the precondition will be consumed
    in the second lift, by `ccorres_save_pre_init_lift2`. This reflects the older behaviour
    of `cinit`, which always dropped preconditions used for lifting. It is still used for all
    local variable lifting.\<close>
lemma ccorres_save_pre_lift1:
  assumes "\<And>rv'. P rv' \<Longrightarrow> ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S (G' \<inter> {s. xf' s = rv'}) hs m c"
  shows "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S (G' \<inter> {s. P (xf' s)}) hs m c"
  using assms by (clarsimp simp: ccorres_save_pre_Int_def ccorres_tmp_lift1)

\<comment> \<open>On the other hand, if we use this rule for the first lift in `cinit`, the precondition is
    copied. One copy will be consumed by `ccorres_save_pre_init_lift2`, but the second copy will be
    used to restore the precondition at the end of `cinit`. The end result is that `cinit` performs
    lifting without dropping the precondition. Ideally, we would use this for all variable lifting,
    but using this for local variables breaks some existing proofs. Currently, we use it for
    lifting global variables only; see `ccorres_save_pre_lift1_save_global` below.\<close>
lemmas ccorres_save_pre_lift1_save
  = ccorres_save_pre_lift1[OF ccorres_save_pre_dup_iff[THEN iffD1]]

lemmas ccorres_save_pre_lift1_save_global
  = ccorres_save_pre_lift1_save[where xf'="xf' \<circ> globals" for xf', simplified]

lemma ccorres_save_pre_init_lift2:
  assumes ceqv: "\<And>t t'. ceqv \<Gamma> xf' rv' t t' c c'"
  assumes ccorres: "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S G' hs m c'"
  shows "ccorres_save_pre srel \<Gamma> rrel xf arrel axf G S (G' \<inter> {s. xf' s = rv'}) hs m c"
  using  ccorres_init_tmp_lift2[OF ceqv ccorres[unfolded ccorres_save_pre_def]]
  by (clarsimp simp: ccorres_save_pre_Int_def)

lemma ccorres_save_pre_UNIV_Int:
  assumes "ccorres_save_pre rf_sr \<Gamma> r xf arrel axf G S (UNIV \<inter> {x. P x}) hs a c"
  shows "ccorres_save_pre rf_sr \<Gamma> r xf arrel axf G S {x. P x} hs a c"
  using assms by simp

lemmas ccorres_tmp_lift1_global = ccorres_tmp_lift1[where xf'="xf' \<circ> globals" for xf', simplified]

\<comment> \<open>\<close>

definition
  "simpl_sequence f xs
    = foldr (Seq) (map f xs) Skip"

lemma simpl_sequence_Cons:
  "simpl_sequence f (x # xs) = Seq (f x) (simpl_sequence f xs)"
  by (simp add: simpl_sequence_def)

fun(sequential)
  simpl_final_basic_opts :: "('s, 'p, 'x) com \<Rightarrow> ('s \<Rightarrow> 's) option"
where
    "simpl_final_basic_opts (x ;; y)
        = (case (simpl_final_basic_opts y) of None \<Rightarrow> simpl_final_basic_opts x
            | Some v \<Rightarrow> Some v)"
  | "simpl_final_basic_opts (Basic f) = Some f"
  | "simpl_final_basic_opts (Guard E F c) = simpl_final_basic_opts c"
  | "simpl_final_basic_opts Skip = None"
  | "simpl_final_basic_opts Throw = None"
  | "simpl_final_basic_opts c = Some id"

definition
  "simpl_final_basic c = (case simpl_final_basic_opts c
      of Some v \<Rightarrow> v | None \<Rightarrow> id)"

lemmas simpl_final_basic_simps[simp]
    = simpl_final_basic_def[where c="Seq c c'" for c c']
      simpl_final_basic_def[where c="Basic f" for f]
      simpl_final_basic_def[where c="Guard E F c" for E F c]

lemma simpl_final_basic_opts_exec[OF _ refl refl]:
  "\<Gamma> \<turnstile> \<langle>c, xs\<rangle> \<Rightarrow> xs' \<Longrightarrow> xs = Normal t \<Longrightarrow> xs' = Normal t'
    \<Longrightarrow> (case simpl_final_basic_opts c of None \<Rightarrow> t' = t
            | Some f \<Rightarrow> \<exists>s. t' = f s)"
  apply (induct arbitrary: t t' rule: exec.induct, simp_all)
   apply metis
  apply atomize
  apply clarsimp
  apply (case_tac s')
     apply (auto split: option.split_asm)[1]
    apply (auto elim!: exec_elim_cases)
  done

lemma simpl_final_basic_exec:
  "\<Gamma> \<turnstile> \<langle>c, Normal t\<rangle> \<Rightarrow> Normal t'
    \<Longrightarrow> \<exists>s. t' = simpl_final_basic c s"
  apply (frule simpl_final_basic_opts_exec)
  apply (simp add: simpl_final_basic_def split: option.split_asm)
  done

lemma xpres_strong_False_trivial:
  "xpres_strong \<Gamma> xf v c False False False"
  by (simp add: xpres_strong_def)

lemma ceqv_xpres_eq_ceqv:
  "ceqv_xpres \<Gamma> xf v True c False False False c' = (\<forall>s t. ceqv \<Gamma> xf v s t c c')"
  by (simp add: ceqv_xpres_def xpres_strong_False_trivial)

lemma ceqv_xpres_to_simpl_sequence:
  fixes v :: "'a :: ring_1"
  assumes c: "\<And>v. ceqv_xpres \<Gamma> xf' v True c pres_norm pres_abr abnormal (c' v)"
      and v: "\<And>v s. xf' (simpl_final_basic (c' v) s) - v = offs"
  shows "\<not> CP (v + of_nat n * offs)
    \<Longrightarrow> ceqv_xpres \<Gamma> xf' v True (While {s. CP (xf' s)} c) False False False
        (simpl_sequence c' (takeWhile CP (map (\<lambda>x. v + of_nat x * offs) [0 ..< n])))"
  (is "_ \<Longrightarrow> ceqv_xpres _ _ _ _ (While ?S _) _ _ _ _")
proof (induct n arbitrary: v)
  case 0
  show ?case using c[where v=v] 0
    apply (simp add: simpl_sequence_def)
    apply (simp add: ceqv_xpres_def ceqv_def xpres_strong_False_trivial)
    apply (auto elim!: exec_Normal_elim_cases intro: exec.Skip exec.WhileFalse)
    done
next
  case (Suc n)
  have foo: "\<And>t t'. (\<Gamma> \<turnstile> \<langle>c' v, Normal t\<rangle> \<Rightarrow> Normal t') \<longrightarrow> xf' t' = v + offs"
    using v
    by (clarsimp simp: field_simps dest!: simpl_final_basic_exec)

  show ?case using c[where v=v] Suc.hyps[where v="v + offs"] Suc.prems
    apply (subst upt_conv_Cons, simp)
    apply (simp only: map_Suc_upt[symmetric] list.simps)
    apply (cases "CP v")
     apply (simp add: o_def field_simps simpl_sequence_Cons
                      ceqv_xpres_def xpres_strong_False_trivial)
     apply (clarsimp, rule ceqv_trans[where c'="c ;; While ?S c"])
      apply (simp add: ceqv_def)
      apply (auto elim!: exec_Normal_elim_cases intro: exec.Seq exec.WhileTrue)[1]
     apply (rule ceqv_trans[where c'="c' v ;; While ?S c"])
      apply (simp add: ceqv_def)
      apply (auto elim!: exec_Normal_elim_cases intro: exec.Seq)[1]
     apply (simp add: ceqv_def)
     apply (intro impI exec_Seq_cong refl)
     apply (simp add: foo)
    apply (simp add: simpl_sequence_def field_simps)
    apply (simp add: ceqv_xpres_def xpres_strong_False_trivial ceqv_def)
    apply (auto intro: exec.WhileFalse exec.Skip elim!: exec_Normal_elim_cases)[1]
    done
qed

lemma ceqv_xpres_While_simpl_sequence:
  fixes v :: "'a :: ring_1"
  assumes c: "\<And>v. ceqv_xpres \<Gamma> xf' v True c pres_norm pres_abr abnormal (c' v)"
  shows "ceqv_xpres \<Gamma> xf' v True (While {s. CP (xf' s)} c) False False False
        (if \<exists>n offs. (\<forall>s v. (xf' (simpl_final_basic (c' v) s) - v = offs)) \<and> \<not> CP (v + of_nat n * offs)
          then simpl_sequence c' (map (\<lambda>x. v + of_nat x
                  * (THE offs. \<forall>s v. (xf' (simpl_final_basic (c' v) s) - v = offs)))
              [0 ..< (LEAST n. \<not> CP (v + of_nat n
                  * (THE offs. \<forall>s v. (xf' (simpl_final_basic (c' v) s) - v = offs))))])
          else While {s. CP (xf' s)} c)"
  apply (split if_split, clarsimp simp: ceqv_xpres_def xpres_strong_def ceqv_refl)
  apply (rule ceqv_trans)
   apply (rule_tac n="LEAST n. \<not> CP (v + of_nat n * offs)"
     in ceqv_xpres_to_simpl_sequence[simplified ceqv_xpres_eq_ceqv, rule_format])
     apply (rule c)
    apply simp
   apply simp
   apply (rule LeastI_ex)
   apply blast
  apply (subst takeWhile_eq_all_conv[THEN iffD2])
   apply (clarsimp dest!: not_less_Least)
  apply (simp add: ceqv_def)
  done

lemma ccorres_underlying_name_seq_bound:
  "(\<not> CP n \<and> (\<forall>n' < n. CP n'))
    \<Longrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m
        (simpl_sequence c' (map f [0 ..< n]))
    \<Longrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf
          G G' hs m (if \<exists>n. \<not> CP n
            then simpl_sequence c' (map f [0 ..< (LEAST n. \<not> CP n)])
            else c)"
  apply (subst if_P, blast)
  apply (subst Least_equality[where x=n], simp_all)
  apply (rule ccontr, simp add: linorder_not_le)
  done

lemma sequenceE_simpl_sequence_nth_corres':
  "\<lbrakk> length xs = length ys;
    \<And>zs. length zs < length xs \<Longrightarrow>
        ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv rv'. r' (prev_xs @ zs @ [rv]) rv')) xf'
                            (inl_rrel arrel) axf
                            (P and F (length prev_xs + length zs)) (Q \<inter> {s. r' (prev_xs @ zs) (xf' s)}) hs
                            (xs ! length zs) (f (ys ! length zs));
    \<And>s \<sigma>. s \<in> Q \<Longrightarrow> P \<sigma> \<Longrightarrow>
        (\<sigma>, s) \<in> sr \<Longrightarrow> \<forall>y \<in> set ys. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} (f y) Q,UNIV;
    \<And>n. Suc n < length xs \<Longrightarrow> \<lbrace>P and F (length prev_xs + n)\<rbrace> xs ! n \<lbrace>\<lambda>_. P and F (length prev_xs + Suc n)\<rbrace>, -
    \<rbrakk>
    \<Longrightarrow> ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv rv'. r' (prev_xs @ rv) rv')) xf'
                  (inl_rrel arrel) axf
                  (\<lambda>s. xs \<noteq> [] \<longrightarrow> P s \<and> F (length prev_xs) s) (Q \<inter> {s. r' prev_xs (xf' s)}) hs
          (sequenceE xs)
          (simpl_sequence f ys)"
proof (induct xs ys arbitrary: prev_xs rule: list_induct2)
  case Nil
  show ?case
    apply (simp add: sequenceE_def simpl_sequence_def)
    apply (rule ccorres_guard_imp2, rule ccorres_returnOk_skip)
    apply simp
    done
next
  case (Cons x xs y ys)
  show ?case
    apply (simp add: simpl_sequence_Cons sequenceE_Cons)
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_splitE)
         apply simp
         apply (rule Cons.prems(1)[where zs=Nil, simplified])
        apply (rule ceqv_refl)
       apply (simp add: liftME_def[symmetric] liftME_liftM)
       apply (rule ccorres_rel_imp2, rule Cons.hyps(2)[where prev_xs="prev_xs @ [rv]" for rv])
           apply (rule ccorres_guard_imp2, rule ccorres_rel_imp2,
             rule Cons.prems(1)[where zs="z # zs" for z zs, simplified])
              apply simp+
          apply (blast dest: Cons.prems[simplified])
         apply simp
         apply (cut_tac n="Suc n" in Cons.prems(3), simp, simp)
        apply (clarsimp elim!: inl_inrE)
        apply assumption
       apply (clarsimp elim!: inl_inrE)
      apply simp
      apply (rule hoare_vcg_const_imp_lift_R)
      apply (rule hoare_gen_asmE)
      apply (erule Cons.prems(3)[where n=0, simplified])
     apply (rule_tac P="Q \<inter> {s. \<exists>\<sigma>. P \<sigma> \<and> (\<sigma>, s) \<in> sr}"
         in HoarePartial.conseq_exploit_pre)
     apply (clarsimp, rule conseqPost, rule Cons.prems(2)[simplified, THEN conjunct1],
       simp+)
      apply (clarsimp simp: ccHoarePost_def elim!: inl_inrE)
     apply simp
    apply auto
    done
qed

lemmas sequenceE_simpl_sequence_nth_corres
    = sequenceE_simpl_sequence_nth_corres'[where prev_xs=Nil, simplified]

lemma mapME_x_simpl_sequence_fun_related:
  "\<lbrakk> ys = map yf xs;
    \<And>n x. x \<in> set xs \<Longrightarrow>
        ccorres_underlying sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel arrel) axf
            (P and F n (n < length xs) x) Q hs
                            (f x) (f' (yf x));
    \<And>s \<sigma>. s \<in> Q \<Longrightarrow> P \<sigma> \<Longrightarrow>
        (\<sigma>, s) \<in> sr \<Longrightarrow> \<forall>x \<in> set xs. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} (f' (yf x)) Q,UNIV;
    \<And>n. Suc n < length xs \<Longrightarrow> \<lbrace>P and F n True (xs ! n)\<rbrace> f (xs ! n) \<lbrace>\<lambda>_. P and F (Suc n) (Suc n < length xs) (xs ! Suc n)\<rbrace>, -
    \<rbrakk>
    \<Longrightarrow> ccorres_underlying sr \<Gamma> (inr_rrel dc) xfdc
                  (inl_rrel arrel) axf
                  (P and F 0 (xs \<noteq> []) (xs ! 0)) Q hs
          (mapME_x f xs)
          (simpl_sequence f' ys)"
  apply (simp add: mapME_x_sequenceE liftME_def[symmetric]
    liftME_liftM)
  apply (rule ccorres_rel_imp2, rule ccorres_guard_imp2,
    rule sequenceE_simpl_sequence_nth_corres[where r'=dc and xf'=xfdc
      and P=P and F="\<lambda>i. F i (i < length xs) (xs ! i)" and Q=Q and arrel=arrel and axf=axf];
        clarsimp elim!: inl_inrE)
  apply (erule_tac x="length zs" in meta_allE
       | erule_tac x="xs ! length zs" in meta_allE)+
  apply (simp add: dc_def cong: ccorres_all_cong)
  done

lemmas mapME_x_simpl_sequence_same
    = mapME_x_simpl_sequence_fun_related[where yf=id, simplified]

lemmas call_ignore_cong = refl[of "call i f g r" for i f g r]

(* These could be done with ML patterns, but this fits in better with tactics *)
lemmas match_valid = trivial[of "NonDetMonadVCG.valid P a P'" for P a P']
lemmas match_validE = trivial[of "NonDetMonadVCG.validE P a P' P''" for P a P' P'']
lemmas match_hoare = trivial[of "HoarePartialDef.hoarep G T F P C P' A" for G T F P C P' A]
lemmas match_all_hoare = trivial[of "\<forall>x. HoarePartialDef.hoarep G T F (P x) C (P' x) (A x)" for G T F P C P' A]
lemmas match_xpres = trivial[of "xpres xf v \<Gamma> c" for xf v \<Gamma> c]
lemmas match_ceqv = trivial[of "ceqv \<Gamma> xf v t t' c c'" for \<Gamma> xf v t t' c c']

lemmas ctac_skips = match_valid match_validE match_all_hoare match_hoare

ML_file "ctac-method.ML"

setup CtacImpl.setup

method_setup ctac = \<open>CtacImpl.corres_ctac_tactic\<close>
  "Split and rewrite corres rules.  Arguments simp (add|del|only), pre (add|del|only), (ccorres) (add|del|only)"

method_setup clift = \<open>CtacImpl.corres_abstract_args\<close>
  "Abstract a local variable into a HOL variable"

method_setup cinitlift = \<open>CtacImpl.corres_abstract_init_args\<close>
  "Abstract a list of local variables into HOL variable without touching the remaining guards"

method_setup csymbr = \<open>CtacImpl.corres_symb_rhs\<close>
  "Symbolically execute the call on the right hand side of corres (see ccorres_lift_rhss). Arguments simp (add|del|only)."

method_setup ceqv = \<open>CtacImpl.corres_ceqv\<close>
  "Solve ceqv goals."

(* The true here says to unfold the Haskell side *)
method_setup cinit = \<open>CtacImpl.corres_boilerplate true\<close>
  "Boilerplate tactic for the start of a Call ccorres proof. Arguments 'lift' then 'simp (add|del|only)', e.g. apply (cinit lift: var1_' var2_' simp add: return_bind)"

method_setup cinit' = \<open>CtacImpl.corres_boilerplate false\<close>
  "As for cinit without unfolding the abstract side"

(* Debugging *)
method_setup ctac_print_xf = \<open>CtacImpl.corres_print_xf\<close>
  "Print out what ctac thinks is the current xf"

(* Set up wpc *)
lemma wpc_helper_ccorres_final:
  "ccorres_underlying sr G rv xf arrel axf Q Q'' hs f f'
   \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'')
                  (ccorres_underlying sr G rv xf arrel axf P P'' hs f f')"
  apply (clarsimp simp: wpc_helper_def)
  apply (erule ccorres_guard_imp)
   apply auto
  done

wpc_setup "\<lambda>m. ccorres_underlying sr G rv xf arrel axf P P' hs m conc" wpc_helper_ccorres_final
wpc_setup "\<lambda>m. ccorres_underlying sr G rv xf arrel axf P P' hs (m >>= a) conc" wpc_helper_ccorres_final
wpc_setup "\<lambda>m. ccorres_underlying sr G rv xf arrel axf P P' hs (m >>=E a) conc" wpc_helper_ccorres_final

context kernel
begin

(* Set up ctac proof sets.  These are tried in reverse order (further down is tried first) *)

declare ccorres_Guard [ccorres_pre]
declare ccorres_Guard_Seq [ccorres_pre]

lemma c_guard_field_abs:
  fixes p :: "'a :: mem_type ptr"
  assumes abs: "\<forall>s s'. (s, s') \<in> rf_sr \<and> P s \<and> P' s' \<longrightarrow> c_guard p"
  shows "\<forall>s s'. (s, s') \<in> rf_sr \<and> P s
  \<and> (P' s' \<and> (\<exists>t. field_ti TYPE('a) f = Some t \<and> export_uinfo t = export_uinfo (typ_info_t TYPE('b :: mem_type))))
  \<longrightarrow> c_guard (Ptr &(p\<rightarrow>f) :: 'b :: mem_type ptr)"
  using c_guard_field abs by blast

lemma h_t_valid_field_abs:
  fixes p :: "'a :: mem_type ptr"
  assumes abs: "\<forall>s s'. (s, s') \<in> rf_sr \<and> P s \<and> P' s' \<longrightarrow> s' \<Turnstile>\<^sub>c p"
  shows "\<forall>s s'. (s, s') \<in> rf_sr \<and> P s
  \<and> (P' s' \<and> (\<exists>t. field_ti TYPE('a) f = Some t \<and> export_uinfo t = export_uinfo (typ_info_t TYPE('b :: mem_type))))
  \<longrightarrow> s' \<Turnstile>\<^sub>c (Ptr &(p\<rightarrow>f) :: 'b :: mem_type ptr)"
  using h_t_valid_field abs by blast

lemmas ccorres_move_c_guard_Seq_field = ccorres_move_Guard_Seq [OF c_guard_field_abs]
lemmas ccorres_move_c_guard_field = ccorres_move_Guard [OF c_guard_field_abs]

lemma abs_c_guard_from_abs_h_t_valid:
  "(\<forall>s s'. (s, s') \<in> rf_sr \<and> P s \<and> P' s' \<longrightarrow> s' \<Turnstile>\<^sub>c p)
    \<Longrightarrow> (\<forall>s s'. (s, s') \<in> rf_sr \<and> P s \<and> P' s' \<longrightarrow> c_guard p)"
  by (auto intro: h_t_valid_c_guard)

lemmas ccorres_move_c_guards =
  ccorres_move_c_guard_Seq_field[OF abs_c_guard_from_abs_h_t_valid]
  ccorres_move_Guard_Seq[OF h_t_valid_field_abs]
  ccorres_move_Guard_Seq[OF abs_c_guard_from_abs_h_t_valid]
  ccorres_move_Guard_Seq
  ccorres_move_c_guard_field[OF abs_c_guard_from_abs_h_t_valid]
  ccorres_move_Guard[OF h_t_valid_field_abs]
  ccorres_move_Guard[OF abs_c_guard_from_abs_h_t_valid]
  ccorres_move_Guard

lemma array_assertion_abs_to_const:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> P s \<and> P' s'
    \<longrightarrow> (Suc 0 = 0 \<or> array_assertion (ptr s s') (n s s') (htd s s'))
    \<Longrightarrow> \<forall>s s'. (s, s') \<in> rf_sr \<and> P s \<and> P' s'
        \<longrightarrow> array_assertion (ptr s s') (n s s') (htd s s')"
  by simp

lemmas ccorres_move_array_assertions
    = ccorres_move_Guard_Seq ccorres_move_Guard
      ccorres_move_Guard_Seq[OF array_assertion_abs_to_const]
      ccorres_move_Guard[OF array_assertion_abs_to_const]

lemma ptr_add_assertion_positive_helper:
  "n == m \<Longrightarrow> 0 \<le> sint m \<Longrightarrow> 0 \<le> sint n"
  by simp

lemma cvariable_array_map_const_add_map_option:
  "cvariable_array_map_relation m (\<lambda>_. n)
        = cvariable_array_map_relation (map_option f o m) (\<lambda>_. n)"
  by (simp add: cvariable_array_map_relation_def fun_eq_iff)

lemma ccorres_move_const_guard:
  "ccorres_underlying rf_sr Gamm rrel xf arrel axf P P' hs m c
    \<Longrightarrow> ccorres_underlying rf_sr Gamm rrel xf arrel axf
         (P and K G) P' hs m (Guard F {s. G} c)"
  "ccorres_underlying rf_sr Gamm rrel xf arrel axf P P' hs m (c ;; d)
    \<Longrightarrow> ccorres_underlying rf_sr Gamm rrel xf arrel axf
         (P and K G) P' hs m (Guard F {s. G} c ;; d)"
  apply (rule ccorres_guard_imp2, erule ccorres_Guard, simp)
  apply (rule ccorres_guard_imp2, erule ccorres_Guard_Seq, simp)
  done

lemmas ccorres_move_const_guards
    = ccorres_move_const_guard
      ccorres_move_const_guard[unfolded Collect_const]

lemma liftM_exs_valid:
  "\<lbrace>P\<rbrace> m \<exists>\<lbrace>\<lambda>rv. Q (f rv)\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftM f m \<exists>\<lbrace>Q\<rbrace>"
  unfolding liftM_def exs_valid_def
  apply (clarsimp)
  apply (drule spec, drule (1) mp)
  apply (clarsimp simp: bind_def return_def)
  apply (erule bexI [rotated])
  apply simp
  done

lemma ceqv_remove_eqv_skip:
  "\<lbrakk> \<And>s. ceqv \<Gamma> xf () s s' b Skip \<rbrakk> \<Longrightarrow>
     ceqv \<Gamma> xf () s s' (a ;; b) a"
  apply (rule ceqv_trans)
   apply (erule Seq_ceqv[where abnormal=False, OF ceqv_refl])
   apply (simp add: xpres_strong_def)
  apply (clarsimp simp add: ceqv_def)
  apply (rule iffI)
   apply (auto elim!: exec_elim_cases)[1]
  apply (erule exec.intros)
  apply (cases s', simp_all)
  apply (rule exec.intros)
  done

lemma ceqv_remove_eqv_skip':
  "\<lbrakk> \<And>s. ceqv \<Gamma> xf v s s' b Skip; \<And>s'. ceqv \<Gamma> xf v s s' a a'; xpres \<Gamma> xf v a \<rbrakk> \<Longrightarrow>
     ceqv \<Gamma> xf v s s' (a ;; b) a'"
  apply (rule ceqv_trans)
   apply (erule Seq_ceqv [OF ceqv_refl])
   apply (simp add: xpres_ceqv)
  apply (clarsimp simp add: ceqv_def)
  apply (rule iffI)
   apply (erule exec_elim_cases, simp_all)
   apply (auto elim!: exec_elim_cases)[1]
  apply (rule exec.intros, simp)
  apply (cases s', simp_all)
  apply (rule exec.intros)
  done

lemma xpres_triv:
  "xpres G xf () c"
  by (simp add: xpres_def)


lemma ceqv_Guard_UNIV:
  "ceqv G xf v s s' (Guard Err UNIV c) c'
       = ceqv G xf v s s' c c'"
  by (simp add: ceqv_def exec_Guard)

lemma ceqv_guard_into_seq:
  "ceqv \<Gamma> xf v s s' (Guard Err S (a ;; b)) (Guard Err S a ;; b)"
  by (auto simp: ceqv_def elim!: exec_elim_cases intro: exec.intros)

lemma ceqv_Seq_Skip_cases:
  "\<lbrakk> \<And>s'. ceqv \<Gamma> xf v s s' a a'; \<And>s. ceqv \<Gamma> xf v s s' b c; xpres \<Gamma> xf v a;
        (c = Skip \<and> c' = a' \<or> c' = (a' ;; c)) \<rbrakk> \<Longrightarrow>
     ceqv \<Gamma> xf v s s' (a ;; b) c'"
  by (metis Seq_ceqv ceqv_remove_eqv_skip')

lemma finish_ceqv_Seq_Skip_cases:
  "(Skip = Skip \<and> x = x \<or> x = y)"
  "(y = Skip \<and> (x ;; y) = z \<or> (x ;; y) = (x ;; y))"
  by simp_all

lemma semantic_equiv_IF_True:
  "semantic_equiv G s s'  (IF True THEN c ELSE c' FI) c"
  apply (simp add: semantic_equiv_seq_assoc_eq[symmetric])
  by (auto simp: semantic_equiv_def2 elim!: exec_Normal_elim_cases intro: exec.intros)

lemmas ccorres_IF_True = ccorres_semantic_equiv[OF semantic_equiv_IF_True]

ML \<open>
fun tac ctxt =
  resolve_tac ctxt [@{thm ccorres_abstract[where xf'="\<lambda>s. ()"]}] 1
  THEN (REPEAT_DETERM
    (resolve_tac ctxt @{thms While_ceqv[OF impI, OF refl] Cond_ceqv[OF impI, OF refl]
            ceqv_Seq_Skip_cases ceqv_Guard_UNIV[THEN iffD2]
            Guard_ceqv[OF impI, OF refl] ceqv_refl
            finish_ceqv_Seq_Skip_cases} 1
        ORELSE (resolve_tac ctxt [@{thm xpresI}] THEN' simp_tac (ctxt |> Splitter.del_split @{thm "if_split"})) 1
    ))
  THEN simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms com.case}) 1
  THEN no_name_eta_tac ctxt
\<close>

end

method_setup ccorres_remove_UNIV_guard = \<open>Args.context >> (fn ctxt => (K (Method.SIMPLE_METHOD (tac ctxt))))\<close>
  "removes UNIV guards"

end
