(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(* Automation framework for general C refinement *)

theory Ctac
imports
  Corres_C
  "../XPres"
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
    apply (rule HoarePartial.ProcModifyReturnNoAbr
      [where return' = "\<lambda>s t. s",
	OF _ _ f_modifies])
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
    apply (rule HoarePartial.ProcModifyReturnNoAbr 
      [where return' = "\<lambda>s t. s",
	OF _ _ f_modifies])
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


thm ccorres_lift_rhs_call [where P = "\<lambda>_ s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t (xfa s)"]

lemmas ccorres_lift_rhs_no_guard = ccorres_lift_rhs_call [where P = "\<lambda>_ _. True", simplified]
lemmas ccorres_lift_rhss = ccorres_lift_rhs_no_guard ccorres_lift_rhs_call 

lemmas ccorres_lift_rhs_record_no_guard = ccorres_lift_rhs_call_record [where P = "\<lambda>_ _. True", simplified]
lemmas ccorres_lift_rhss_record = ccorres_lift_rhs_record_no_guard ccorres_lift_rhs_call_record
   
lemma ccorres_lift_rhs_Basic_stateful:
  assumes cc: "\<And>v. ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (G' v) hs a (d' v)"
  and  xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"  
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     gg: "\<And>x f s. globals (xfu' f s) = globals s"
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
    apply (rule_tac x=x in exI)
    apply (rule_tac x="accessor x" in exI)
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
  apply (rule_tac Q="op = s" and Q'="P' \<inter> Q' \<inter> {s'. (s, s') \<in> sr}" in stronger_ccorres_guard_imp)
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
  apply (rule_tac Q="op = s" and Q'="P' \<inter> Q' \<inter> {s'. (s, s') \<in> sr}" in stronger_ccorres_guard_imp)
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
  -- "No ordering apart from pis_base which must be last."
  pis_throw
  pis_creturn
  pis_Seq_right 
  pis_Cond
  pis_switch_Singleton pis_switch_Cons 
  pis_Guard
  -- "Last, just stick it where it is"
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
  Collect_const -- "Avoid getting an implication due to if_split.  Should probably just remove if_split"

lemma ccorres_introduce_UNIV_Int_when_needed:
  "ccorres_underlying sr Gamm r xf ar axf P (UNIV \<inter> {x. Q x}) hs a c
     \<Longrightarrow> ccorres_underlying sr Gamm r xf ar axf P {x. Q x} hs a c"
  by simp

lemma Normal_Abrupt_resultE [consumes 2, case_names normal abrupt]:
  assumes ex: "\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> t"
  and      t: "t = Normal t' \<or> t = Abrupt t'"
  and     r1: "\<And>s'. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Normal s'\<rangle> \<Rightarrow> t; s = Normal s'\<rbrakk> \<Longrightarrow> R"
  and     r2: "\<And>s'. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Abrupt s'\<rangle> \<Rightarrow> t; s = Abrupt s'\<rbrakk> \<Longrightarrow> R"
  shows   R
  using ex t
  apply -
  apply (erule disjE)
   apply simp
   apply (erule Normal_resultE)
   apply (rule r1)
    apply simp
   apply simp
  apply simp
  apply (erule Abrupt_resultE)
   apply (rule r1)
    apply simp
   apply simp
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
  and     xp: "xpres xf v \<Gamma> a" (* Check that a does preserve xf first *)
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
      apply (rule xpresD [where xf = xf], assumption+)
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
      apply (rule xpresD [where xf = xf], assumption+)
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
  assumes xp: "xpres xf v \<Gamma> a"
  and    ceq: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  shows  "xpres xf v \<Gamma> a'"
  apply (rule xpresI)
  apply (drule (1) ceqvD2 [OF _ _ ceq])
  apply (erule (2) xpres_exec0 [OF xp])
  done
 
lemma While_ceqv_na0:
  assumes ra: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  and     xp: "xpres xf v \<Gamma> a"
  and     ex: "\<Gamma>\<turnstile> \<langle>d,s\<rangle> \<Rightarrow> t'"
  and    beq0: "\<And>t. xf t = v \<longrightarrow> (t \<in> b) = (t \<in> b')" 
  and     d: "d = While b a"
  and     s: "s \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}"
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
      
      thus "t \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}" using xp ae xfs
	by (auto dest: xpres_exec0)
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
  and     xp: "xpres xf v \<Gamma> a"
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
	have "xf z = v" using xfs ae
	  apply -
	  apply (erule xpresD [OF _ xp])
	  apply (simp add: tv)
	  done

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
	have "xf z = v" using xfs ae
	  apply -
	  apply (erule xpresD [OF _ xp])
	  apply (simp add: tv)
	  done

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
  and      xp: "xpres xf v \<Gamma> a"   (* So we fail as early as possible *)
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

lemma call_ceqv':
  assumes ieq: "\<And>t. rewrite_xf xf t v i i'"
  and    ceqv: "\<And>t t' s'. ceqv \<Gamma> xf v (r t s') t' (c t s') (c' t s')" (* For record field updates *)
  and     xf:  "\<And>t t'. xf t = v \<Longrightarrow> xf (r t t') = v"  
  shows   "ceqv \<Gamma> xf v t t' (call i f r c) (call i' f r c')"
  apply (rule ceqvI)
  apply (rule iffI)
   apply (erule exec_call_Normal_elim)       
       apply (drule ceqvD1 [OF _ _ ceqv]) 
	apply (simp add: xf)
       apply (erule exec_call)
	apply (simp add: rewrite_xfD [OF ieq])
       apply assumption
      apply (clarsimp simp: rewrite_xfD [OF ieq] elim!: exec_callAbrupt exec_callFault exec_callStuck exec_callUndefined)
     apply (clarsimp simp: rewrite_xfD [OF ieq] elim!: exec_callAbrupt exec_callFault exec_callStuck exec_callUndefined)
    apply (clarsimp simp: rewrite_xfD [OF ieq] elim!: exec_callAbrupt exec_callFault exec_callStuck exec_callUndefined)
   apply (clarsimp simp: rewrite_xfD [OF ieq] elim!: exec_callAbrupt exec_callFault exec_callStuck exec_callUndefined)
  (* clag *)
   apply (erule exec_call_Normal_elim)       
       apply (drule ceqvD2 [OF _ _ ceqv])
	apply (simp add: xf)
       apply (erule exec_call)
	apply (simp add: rewrite_xfD [OF ieq])
       apply assumption
      apply (clarsimp simp: rewrite_xfD [OF ieq, symmetric] 
	elim!: exec_callAbrupt exec_callFault exec_callStuck exec_callUndefined)+
  done

lemma call_ceqv:
  assumes ieq: "\<And>t. rewrite_xf xf t v i i'"
  and    ceqv: "\<And>t t' s'. ceqv \<Gamma> xf v (r t s') t' (c t s') (c' t s')" (* For record field updates *)
  and     xf:  "\<And>t t'. xf (r t t') = xf t"  
  shows   "ceqv \<Gamma> xf v t t' (call i f r c) (call i' f r c')"
  by (rule call_ceqv' [OF ieq ceqv], simp add: xf)

lemmas Skip_ceqv = ceqv_refl [where c = Skip]

lemma Catch_ceqv:
  assumes ca: "\<And>t t'. ceqv \<Gamma> xf v t t' a a'"
  and     cb: "\<And>t t'. ceqv \<Gamma> xf v t t' b b'"
  and     xp: "xpres xf v \<Gamma> a"
  shows   "ceqv \<Gamma> xf v t t' (Catch a b) (Catch a' b')"
  apply (rule ceqvI)
  apply rule
   apply (erule exec_Normal_elim_cases)
    apply (drule (1) ceqvD1 [OF _ _ ca])
    apply (rule exec.CatchMatch, assumption)
    apply (erule ceqvD1 [OF _ _ cb])
    apply (erule (1) xpres_abruptD [OF _ xpres_ceqv [OF xp ca]])
   apply (rule exec.CatchMiss)
    apply (erule (1) ceqvD1 [OF _ _ ca])
   apply assumption
  (* clag *)  
   apply (erule exec_Normal_elim_cases)
    apply (drule (1) ceqvD2 [OF _ _ ca])
    apply (rule exec.CatchMatch, assumption)
    apply (erule ceqvD2 [OF _ _ cb])
   apply (erule xpres_abruptD [where xf = xf])
   apply (rule xp)
   apply assumption
   apply (rule exec.CatchMiss)
    apply (erule (1) ceqvD2 [OF _ _ ca])
   apply assumption
   done
 
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
  and    xfu: "\<And>s f. xf (xfu' f s) = xf s" -- "i.e., xf is independent of xfu"
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

lemmas ceqv_rules = ceqv_refl [where xf' = xfdc] -- "Any ceqv with xfdc should be ignored"
  While_ceqv [OF Collect_mem_eqv] While_ceqv [OF UNIV_mem_eqv] 
  Cond_ceqv [OF Collect_mem_eqv] Cond_UNIV_ceqv Cond_empty_ceqv
  Guard_ceqv [OF Collect_mem_eqv] Guard_UNIV_ceqv
  Seq_ceqv Seq_weak_ceqv
  Basic_ceqv call_ceqv Skip_ceqv 
  Catch_ceqv Throw_ceqv 
  creturn_ceqv_xf creturn_ceqv_not_xf -- "order is important with these two, the second is more general"
  ceqv_refl [where c = return_void_C] ceqv_refl [where c = break_C] 
  ceqv_refl [where c = catchbrk_C]

definition
  ceqv_xpres :: "('p \<rightharpoonup> ('s, 'p, 'x) com) \<Rightarrow> ('s \<Rightarrow> 'a) \<Rightarrow> 'a
                    \<Rightarrow> bool \<Rightarrow> ('s, 'p, 'x) com \<Rightarrow> bool \<Rightarrow> ('s, 'p, 'x) com \<Rightarrow> bool"
where
 "ceqv_xpres \<Gamma> xf v pres c pres' c'
    \<equiv> \<forall>s s' s''. (pres \<longrightarrow> xf s = v)
        \<longrightarrow> (\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>c', Normal s\<rangle> \<Rightarrow> s')
         \<and> (\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s' \<and> (s' = Normal s'' \<or> s' = Abrupt s'') \<and> pres'
                 \<longrightarrow> xf s'' = v)
         \<and> (\<not> pres \<longrightarrow> \<not> pres' \<and> c = c')"

definition
  ceqv_xpres_rewrite_set :: "('s \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> bool" where
 "ceqv_xpres_rewrite_set xf v S S'
    \<equiv> \<forall>s. xf s = v \<longrightarrow> (s \<in> S) = (s \<in> S')"

definition
  ceqv_xpres_rewrite_basic :: "('s \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> bool" where
 "ceqv_xpres_rewrite_basic xf v f f'
    \<equiv> \<forall>s. xf s = v \<longrightarrow> f s = f' s"

definition
  ceqv_xpres_basic_preserves :: "('s \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> bool \<Rightarrow> bool" where
 "ceqv_xpres_basic_preserves xf v f b
    \<equiv> b \<longrightarrow> (\<forall>s. xf s = v \<longrightarrow> xf (f s) = v)"

definition
  ceqv_xpres_eq_If :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
 "ceqv_xpres_eq_If b x y z \<equiv> z = (if b then x else y)"

definition
  ceqv_xpres_call_restore_args :: "'a \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> bool"
where
 "ceqv_xpres_call_restore_args x f g = (f = g)"

lemma ceqv_xpres_eq_both:
  "ceqv_xpres \<Gamma> xf v True c True c'
       = ((\<forall>t t'. ceqv \<Gamma> xf v t t' c c') \<and> xpres xf v \<Gamma> c')"
  apply (simp add: ceqv_xpres_def ceqv_def xpres_def)
  apply blast
  done

lemma ceqv_xpres_eq_ceqv:
  "ceqv_xpres \<Gamma> xf v True c False c'
      = (\<forall> t t'. ceqv \<Gamma> xf v t t' c c')"
  by (simp add: ceqv_xpres_def ceqv_def)

lemma ceqv_xpres_eq_imp:
  "ceqv_xpres \<Gamma> xf v True c pres c'
      = ((\<forall>t t'. ceqv \<Gamma> xf v t t' c c') \<and> (pres \<longrightarrow> xpres xf v \<Gamma> c'))"
  by (cases pres, simp_all add: ceqv_xpres_eq_ceqv ceqv_xpres_eq_both)

lemma ceqv_xpres_False:
  "ceqv_xpres \<Gamma> xf v False c pres c' = (\<not> pres \<and> c = c')"
  by (auto simp add: ceqv_xpres_def)

lemma ceqv_xpres_eq_If_False:
  "ceqv_xpres_eq_If P Q False R = (R = (P \<and> Q))"
  by (simp add: ceqv_xpres_eq_If_def)

lemma ceqv_xpres_False_pres:
  "ceqv_xpres \<Gamma> xf v False c False c"
  by (simp add: ceqv_xpres_def)

lemma ceqv_xpres_xfdc:
  "ceqv_xpres \<Gamma> xfdc v pres c pres c"
  by (simp add: ceqv_xpres_def xfdc_def)

lemma ceqv_xpres_call_restore_argsI:
  "\<forall> s. f s = g s \<Longrightarrow> ceqv_xpres_call_restore_args i f g"
  by (simp add: ceqv_xpres_call_restore_args_def fun_eq_iff)

lemma ceqv_xpres_whileAnno:
  "\<lbrakk> ceqv_xpres \<Gamma> xf v True c pres c'; ceqv_xpres_rewrite_set xf v S S';
        ceqv_xpres_eq_If pres c' c c''; ceqv_xpres_eq_If pres S' S S'' \<rbrakk>
     \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (whileAnno S I V c) pres (whileAnno S'' I V c'')"
  apply (cases pres)
   apply (clarsimp simp add: ceqv_xpres_eq_both ceqv_xpres_eq_If_def
                             whileAnno_def)
   apply (intro conjI allI)
    apply (rule While_ceqv)
      apply (simp add: ceqv_xpres_rewrite_set_def)
     apply simp
    apply (erule xpres_ceqv)
    apply (rule ceqv_sym, simp)
   apply (erule xpres_while)
  apply (simp add: ceqv_xpres_def ceqv_xpres_eq_If_def)
  done

lemmas ceqv_xpres_While = ceqv_xpres_whileAnno[unfolded whileAnno_def]

lemma ceqv_xpres_Cond:
  "\<lbrakk> ceqv_xpres_rewrite_set xf v S S'; ceqv_xpres \<Gamma> xf v True c cpres c';
     ceqv_xpres \<Gamma> xf v True d dpres d'; ceqv_xpres_eq_If dpres cpres False pres \<rbrakk>
    \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (Cond S c d) pres (Cond S' c' d')"
  apply (clarsimp simp add: ceqv_xpres_eq_imp ceqv_xpres_eq_If_False)
  apply (intro allI conjI impI)
   apply (rule Cond_ceqv)
     apply (simp add: ceqv_xpres_rewrite_set_def)
    apply simp
   apply simp
  apply simp
  apply (erule(1) xpres_cond)
  done

lemma ceqv_xpres_Guard:
  "\<lbrakk> ceqv_xpres_rewrite_set xf v S S'; ceqv_xpres \<Gamma> xf v True c pres c' \<rbrakk>
     \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (Guard g S c) pres (Guard g S' c')"
  apply (clarsimp simp: ceqv_xpres_eq_imp xpres_guard)
  apply (rule Guard_ceqv)
   apply (simp add: ceqv_xpres_rewrite_set_def)
  apply simp
  done

lemma ceqv_xpres_Seq:
  "\<lbrakk> ceqv_xpres \<Gamma> xf v True c cpres c'; ceqv_xpres \<Gamma> xf v cpres d pres d' \<rbrakk>
     \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (c ;; d) pres (c' ;; d')"
  apply (cases cpres)
   apply (clarsimp simp add: ceqv_xpres_eq_imp xpres_seq)
   apply (rule Seq_ceqv, simp+)
   apply (erule xpres_ceqv)
   apply (rule ceqv_sym, simp)
  apply (clarsimp simp add: ceqv_xpres_eq_imp ceqv_xpres_False)
  apply (rule Seq_weak_ceqv, simp)
  done

lemma ceqv_xpres_Basic:
  "\<lbrakk> ceqv_xpres_rewrite_basic xf v f f';
          ceqv_xpres_basic_preserves xf v f' pres \<rbrakk>
    \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (Basic f) pres (Basic f')"
  apply (simp add: ceqv_xpres_eq_imp)
  apply (intro allI impI conjI)
   apply (rule Basic_ceqv)
   apply (simp add: rewrite_xf_def ceqv_xpres_rewrite_basic_def)
  apply (rule xpres_basic)
  apply (simp add: ceqv_xpres_basic_preserves_def)
  done

lemma ceqv_xpres_call:
  "\<lbrakk> ceqv_xpres_call_restore_args f i i';
     ceqv_xpres_rewrite_basic xf v i' i'';
           \<And>s'. ceqv_xpres_basic_preserves xf v (\<lambda>s. r s s') pres';
           \<And>s' s''. ceqv_xpres \<Gamma> xf v pres' (c s' s'')  pres (c' s' s'') \<rbrakk>
      \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (call i f r c) pres (call i'' f r c')"
  apply (simp add: ceqv_xpres_eq_imp ceqv_xpres_call_restore_args_def)
  apply (intro allI conjI impI)
   defer
   apply (cases pres')
    apply (rule xpres_call)
     apply (simp add: ceqv_xpres_basic_preserves_def)
    apply (simp add: ceqv_xpres_eq_imp)
   apply (simp add: ceqv_xpres_False)
  apply (cases pres')
   apply (clarsimp simp add: ceqv_xpres_eq_imp)
   apply (rule call_ceqv')
     apply (simp add: rewrite_xf_def ceqv_xpres_rewrite_basic_def)
    apply simp
   apply (simp add: ceqv_xpres_basic_preserves_def)
  apply (simp add: ceqv_xpres_False)
  apply (clarsimp simp add: ceqv_def ceqv_xpres_rewrite_basic_def)
  apply (auto elim!: exec_call_Normal_elim exec_call
                     exec_callAbrupt exec_callFault exec_callStuck exec_callUndefined)
  done

lemma ceqv_xpres_Skip:
  "ceqv_xpres \<Gamma> xf v True Skip True Skip"
  by (simp add: ceqv_xpres_eq_imp Skip_ceqv xpres_skip)

lemma ceqv_xpres_Catch:
  "\<lbrakk> ceqv_xpres \<Gamma> xf v True c pres c'; ceqv_xpres \<Gamma> xf v pres h pres' h' \<rbrakk>
        \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (Catch c h) pres' (Catch c' h')"
  apply (cases pres)
   apply (clarsimp simp add: ceqv_xpres_eq_imp xpres_catch)
   apply (rule Catch_ceqv)
     apply simp
    apply simp
   apply (erule xpres_ceqv)
   apply (rule ceqv_sym, simp)
  apply (clarsimp simp add: ceqv_xpres_False ceqv_xpres_eq_imp)
  apply (clarsimp simp: ceqv_def)
  apply (auto elim!: exec_Normal_elim_cases
              intro: exec.intros)
  done

lemma ceqv_xpres_Throw:
  "ceqv_xpres \<Gamma> xf v True Throw True Throw"
  by (simp add: ceqv_xpres_eq_imp Throw_ceqv xpres_throw)

lemma exec_Basic_Seq:
  "\<Gamma> \<turnstile> \<langle>Basic f ;; c, Normal s\<rangle> \<Rightarrow> s'
     = \<Gamma> \<turnstile> \<langle>c, Normal (f s)\<rangle> \<Rightarrow> s'"
  by (auto elim: exec_elim_cases intro: exec.Basic exec.Seq)

lemma exec_Basic_Seq_Basic:
  "\<Gamma>\<turnstile> \<langle>Basic f;; Basic g, x\<rangle> \<Rightarrow> y = \<Gamma>\<turnstile> \<langle>Basic (g \<circ> f), x\<rangle> \<Rightarrow> y"
  by (auto simp: o_def elim: exec_elim_cases intro: exec.Basic exec.Seq)

lemma ceqv_xpres_return_C:
  "\<lbrakk> ceqv_xpres_rewrite_basic xf v qf qf';
          \<And>f. ceqv_xpres_basic_preserves xf v (xfu f) pres';
          \<And>f. ceqv_xpres_basic_preserves xf v
                  (global_exn_var_'_update f) pres'';
          ceqv_xpres_eq_If pres' pres'' False pres \<rbrakk>
     \<Longrightarrow> ceqv_xpres \<Gamma> xf v True (return_C xfu qf) pres (return_C xfu qf')"
  apply (simp add: ceqv_xpres_def ceqv_xpres_rewrite_basic_def
                   ceqv_xpres_basic_preserves_def creturn_def
                   ceqv_xpres_eq_If_False)
  apply (auto elim!: exec_elim_cases simp: exec_Basic_Seq)
  done

lemma ceqv_xpres_C_bits:
  "\<lbrakk> \<And>f. ceqv_xpres_basic_preserves xf v
                  (global_exn_var_'_update f) pres \<rbrakk>
     \<Longrightarrow> ceqv_xpres \<Gamma> xf v True return_void_C pres return_void_C"
  "\<lbrakk> \<And>f. ceqv_xpres_basic_preserves xf v
                  (global_exn_var_'_update f) pres \<rbrakk>
     \<Longrightarrow> ceqv_xpres \<Gamma> xf v True break_C pres break_C"
  "ceqv_xpres \<Gamma> xf v True catchbrk_C True catchbrk_C"
  by (auto simp: ceqv_xpres_def
                 return_void_C_def cbreak_def
                 catchbrk_C_def
                 ceqv_xpres_basic_preserves_def
          elim!: exec_elim_cases)

definition
  "ceqv_xpres_lvar_nondet_init xf v_upd pres \<equiv> pres \<longrightarrow> (\<forall>s v. xf (v_upd (\<lambda>_. v) s) = xf s)"

lemma ceqv_xpres_lvar_nondet_init:
  "ceqv_xpres_lvar_nondet_init xf v_upd pres \<Longrightarrow>
   ceqv_xpres \<Gamma> xf v True (lvar_nondet_init v_acc v_upd) pres (lvar_nondet_init v_acc v_upd)"
  apply (clarsimp simp: ceqv_xpres_def lvar_nondet_init_def)
  apply (erule exec.cases, simp_all)
  apply (clarsimp simp: ceqv_xpres_lvar_nondet_init_def)
  done

lemmas ceqv_xpres_rules =
  ceqv_xpres_False_pres ceqv_xpres_xfdc ceqv_xpres_whileAnno
  ceqv_xpres_While ceqv_xpres_Cond ceqv_xpres_Guard ceqv_xpres_Seq
  ceqv_xpres_lvar_nondet_init ceqv_xpres_Basic ceqv_xpres_call 
  ceqv_xpres_Skip ceqv_xpres_Catch ceqv_xpres_Throw ceqv_xpres_return_C
  ceqv_xpres_C_bits

lemma ceqv_xpres_FalseI:
  "ceqv_xpres \<Gamma> xf v pres c False c"
  by (simp add: ceqv_xpres_def)

lemma ceqv_xpres_ceqvI:
  "ceqv_xpres \<Gamma> xf v True c pres c' \<Longrightarrow> ceqv \<Gamma> xf v t t' c c'"
  by (simp add: ceqv_xpres_eq_imp)

lemma ceqv_xpres_rewrite_basic_left_cong:
  "\<lbrakk> \<And>s. xf s = v \<Longrightarrow> f s = f'' s \<rbrakk>
     \<Longrightarrow> ceqv_xpres_rewrite_basic xf v f f'
           = ceqv_xpres_rewrite_basic xf v f'' f'"
  by (simp add: ceqv_xpres_rewrite_basic_def)

lemma ceqv_xpres_rewrite_basic_refl:
  "ceqv_xpres_rewrite_basic xf v f f"
  by (simp add: ceqv_xpres_rewrite_basic_def)

lemma ceqv_xpres_basic_preserves_TrueI:
  "\<lbrakk> \<And>s. xf s = v \<longrightarrow> xf (f s) = v \<rbrakk> \<Longrightarrow> ceqv_xpres_basic_preserves xf v f True"
  by (simp add: ceqv_xpres_basic_preserves_def)

lemma ceqv_xpres_basic_preserves_FalseI:
  "ceqv_xpres_basic_preserves xf v f False"
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

lemma ceqv_xpres_eq_If_rules:
  "ceqv_xpres_eq_If False x y y"
  "ceqv_xpres_eq_If True x y x"
  by (simp add: ceqv_xpres_eq_If_def)+

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

lemma ceqv_xpres_to_simpl_sequence:
  fixes v :: "'a :: ring_1"
  assumes c: "\<And>v. ceqv_xpres \<Gamma> xf' v True c pres (c' v)"
      and v: "\<And>v s. xf' (simpl_final_basic (c' v) s) - v = offs"
  shows "\<not> CP (v + of_nat n * offs)
    \<Longrightarrow> ceqv_xpres \<Gamma> xf' v True (While {s. CP (xf' s)} c) False
        (simpl_sequence c' (takeWhile CP (map (\<lambda>x. v + of_nat x * offs) [0 ..< n])))"
  (is "_ \<Longrightarrow> ceqv_xpres _ _ _ _ (While ?S _) _ _")
proof (induct n arbitrary: v)
  case 0
  show ?case using c[where v=v] 0
    apply (simp add: simpl_sequence_def)
    apply (simp add: ceqv_xpres_eq_imp ceqv_def)
    apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)[1]
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
                      ceqv_xpres_eq_imp)
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
    apply (simp add: ceqv_xpres_eq_imp ceqv_def)
    apply (auto intro: exec.WhileFalse exec.Skip elim!: exec_Normal_elim_cases)[1]
    done
qed

lemma ceqv_xpres_While_simpl_sequence:
  fixes v :: "'a :: ring_1"
  assumes c: "\<And>v. ceqv_xpres \<Gamma> xf' v True c pres (c' v)"
  shows "ceqv_xpres \<Gamma> xf' v True (While {s. CP (xf' s)} c) False
        (if \<exists>n offs. (\<forall>s v. (xf' (simpl_final_basic (c' v) s) - v = offs)) \<and> \<not> CP (v + of_nat n * offs)
          then simpl_sequence c' (map (\<lambda>x. v + of_nat x
                  * (THE offs. \<forall>s v. (xf' (simpl_final_basic (c' v) s) - v = offs)))
              [0 ..< (LEAST n. \<not> CP (v + of_nat n
                  * (THE offs. \<forall>s v. (xf' (simpl_final_basic (c' v) s) - v = offs))))])
          else While {s. CP (xf' s)} c)"
  apply (split if_split, simp add: ceqv_xpres_def[where c=c and c'=c for c])
  apply (clarsimp simp: ceqv_xpres_eq_ceqv)
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
         apply (simp add: inl_rrel_inl_rrel)
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
  apply (simp add: dc_def)
  done

lemmas mapME_x_simpl_sequence_same
    = mapME_x_simpl_sequence_fun_related[where yf=id, simplified]

lemma call_ignore_cong:
  "call i f g r = call i f g r" by (rule refl)

(* These could be done with ML patterns, but this fits in better with tactics *)
lemma match_valid:
  "NonDetMonad.valid P a P' \<Longrightarrow> NonDetMonad.valid P a P'" .

lemma match_validE:
  "NonDetMonad.validE P a P' P'' \<Longrightarrow> NonDetMonad.validE P a P' P''" .

lemma match_hoare:
  "HoarePartialDef.hoarep G T F P C P' A \<Longrightarrow> HoarePartialDef.hoarep G T F P C P' A" . 

lemma match_all_hoare:
  "\<forall>x. HoarePartialDef.hoarep G T F (P x) C (P' x) (A x) \<Longrightarrow> 
  \<forall>x. HoarePartialDef.hoarep G T F (P x) C (P' x) (A x)" . 

lemmas ctac_skips = match_valid match_validE match_all_hoare match_hoare

lemma match_xpres:
  "xpres xf v \<Gamma> c \<Longrightarrow> xpres xf v \<Gamma> c" .

lemma match_ceqv:
  "ceqv \<Gamma> xf v t t' c c' \<Longrightarrow> ceqv \<Gamma> xf v t t' c c'" .

ML_file "ctac-method.ML"

setup CtacImpl.setup

method_setup ctac = {* CtacImpl.corres_ctac_tactic *}
  "Split and rewrite corres rules.  Arguments simp (add|del|only), pre (add|del|only), (ccorres) (add|del|only)"

method_setup clift = {* CtacImpl.corres_abstract_args *}
  "Abstract a local variable into a HOL variable"

method_setup cinitlift = {* CtacImpl.corres_abstract_init_args *}
  "Abstract a list of local variables into HOL variable without touching the remaining guards"

method_setup csymbr = {* CtacImpl.corres_symb_rhs *}
  "Symbolically execute the call on the right hand side of corres (see ccorres_lift_rhss). Arguments simp (add|del|only)."

method_setup ceqv = {* CtacImpl.corres_ceqv *}
  "Solve ceqv goals."

(* The true here says to unfold the Haskell side *)
method_setup cinit = {* CtacImpl.corres_boilerplate true *}
  "Boilerplate tactic for the start of a Call ccorres proof. Arguments 'lift' then 'simp (add|del|only)', e.g. apply (cinit lift: var1_' var2_' simp add: return_bind)"

method_setup cinit' = {* CtacImpl.corres_boilerplate false *}
  "As for cinit without unfolding the abstract side"

(* Debugging *)
method_setup ctac_print_xf = {* CtacImpl.corres_print_xf *}
  "Print out what ctac thinks is the current xf"

(* Set up wpc *)
lemma
  wpc_helper_ccorres_final:
  "ccorres_underlying sr G rv xf arrel axf Q Q' hs f f'
   \<Longrightarrow> wpc_helper (P, P') (Q, Q')
                  (ccorres_underlying sr G rv xf arrel axf P P' hs f f')"
  apply (clarsimp simp: wpc_helper_def)
  apply (erule ccorres_guard_imp)
   apply auto
  done

wpc_setup "\<lambda>m. ccorres_underlying sr G rv xf arrel axf P P' hs m conc" wpc_helper_ccorres_final
wpc_setup "\<lambda>m. ccorres_underlying sr G rv xf arrel axf P P' hs (m >>= a) conc" wpc_helper_ccorres_final

context kernel
begin

(* Set up ctac proof sets.  These are tried in reverse order (further down is tried first) *)

declare ccorres_Guard [corres_pre]
declare ccorres_Guard_Seq [corres_pre]

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

lemma h_t_array_valid_array_assertion:
  "h_t_array_valid htd ptr n \<Longrightarrow> 0 < n
    \<Longrightarrow> array_assertion ptr n htd"
  apply (simp add: array_assertion_def)
  apply (fastforce intro: exI[where x=0])
  done

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
   apply (erule Seq_ceqv [OF ceqv_refl])
   apply (simp add: xpres_def)
  apply (clarsimp simp add: ceqv_def)
  apply (rule iffI)
   apply (auto elim!: exec_elim_cases)[1]
  apply (erule exec.intros)
  apply (cases s', simp_all)
  apply (rule exec.intros)
  done

lemma ceqv_remove_eqv_skip':
  "\<lbrakk> \<And>s. ceqv \<Gamma> xf v s s' b Skip; \<And>s'. ceqv \<Gamma> xf v s s' a a'; xpres xf v \<Gamma> a \<rbrakk> \<Longrightarrow>
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
  "xpres xf () G c"
  by (simp add: xpres_def)


lemma ceqv_Guard_UNIV:
  "ceqv G xf v s s' (Guard Err UNIV c) c'
       = ceqv G xf v s s' c c'"
  by (simp add: ceqv_def exec_Guard)

lemma ceqv_guard_into_seq:
  "ceqv \<Gamma> xf v s s' (Guard Err S (a ;; b)) (Guard Err S a ;; b)"
  by (auto simp: ceqv_def elim!: exec_elim_cases intro: exec.intros)

lemma ceqv_Seq_Skip_cases:
  "\<lbrakk> \<And>s'. ceqv \<Gamma> xf v s s' a a'; \<And>s. ceqv \<Gamma> xf v s s' b c; xpres xf v \<Gamma> a;
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

ML {*
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
*}

end

method_setup ccorres_remove_UNIV_guard = {* Args.context >> (fn ctxt => (K (Method.SIMPLE_METHOD (tac ctxt)))) *}
  "removes UNIV guards"

end
