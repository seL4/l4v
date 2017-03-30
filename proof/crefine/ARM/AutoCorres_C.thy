(*
 * Copyright 2016, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

text \<open>
  Framework for performing C refinement proofs on AutoCorres-generated specs.

  See AutoCorresTest for example usage.
\<close>
theory AutoCorres_C imports
  "../../../tools/autocorres/AutoCorres"
  "../../../tools/autocorres/L4VerifiedLinks"
  "../../../lib/clib/AutoCorresModifiesProofs"
  "../../../lib/clib/Corres_C"
begin

context kernel begin

section \<open>Proof frameworks\<close>

subsection \<open>Proving @{term ccorres}\<close>
text \<open>
  From AutoCorres @{term ac_corres}, obtain @{term ccorres}.
  This requires a separate @{term corres_underlying} proof between the
  AutoCorres spec and design spec, in order to establish @{term cstate_relation}.
\<close>
lemma ac_corres_to_ccorres:
  "\<lbrakk> ac_corres globals check_termination \<Gamma> ret_xf arg_rel (liftE ac_f) (Call f_'proc);
     arg_relS = Collect arg_rel;
     corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc P arg_relS [] dspec_f (Call f_'proc)"
  by (fastforce simp: ccorres_underlying_def corres_underlying_def rf_sr_def Ball_def
                      liftE_def in_liftE[simplified liftE_def] unif_rrel_def
                dest: ac_corres_ccorres_underlying split: xstate.splits)

subsection \<open>Importing @{term ccorres}\<close>

lemma in_AC_call_simpl:
  fixes r s s' arg_pred globals ret_xf \<Gamma> f_'proc
  shows "(r, s') \<in> fst (AC_call_L1 arg_pred globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc) s) \<Longrightarrow>
         \<exists>cs cs'. s = globals cs \<and> arg_pred cs \<and>
                  (check_termination \<longrightarrow> \<Gamma> \<turnstile> Call f_'proc \<down> Normal cs) \<and>
                  \<Gamma> \<turnstile> \<langle>Call f_'proc, Normal cs\<rangle> \<Rightarrow> Normal cs' \<and>
                  s' = globals cs' \<and> r = ret_xf cs'"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (monad_eq simp: liftM_def select_def select_f_def liftE_def split: xstate.splits sum.splits)
  apply (rename_tac cs cs' status)
  apply (case_tac status)
  apply auto
  done

lemma ccorres_rrel_nat_unit:
  "ccorres op = (\<lambda>s. ()) st_P arg_P hs m c = ccorres dc xfdc st_P arg_P hs m c"
  by (simp add: ccorres_underlying_def dc_def xfdc_def unif_rrel_def cong del: xstate.case_cong)

text \<open>
  From @{term ccorres} obtain @{term corres}.
  This is for exporting existing ccorres theorems to be used
  in AutoCorres-based corres proofs.
\<close>

text \<open>Partial correspondence is simple to prove, but not good enough.\<close>
lemma
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True False (* \<leftarrow> partial *) R P \<top> dspec_f ac_f"
  by (fastforce simp: unif_rrel_def ac_def corres_underlying_def ccorres_underlying_def rf_sr_def
                intro: EHOther dest: in_AC_call_simpl)

text \<open>Requires termination proof for f_'proc. Used when no_c_termination is off.\<close>
lemma ccorres_to_corres_with_termination:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl True \<Gamma> f_'proc)"
  assumes terminates:
    "\<And>s s'. \<lbrakk> cstate_relation s (globals s'); P s; \<not> snd (dspec_f s); arg_rel s' \<rbrakk> \<Longrightarrow>
            \<Gamma> \<turnstile> Call f_'proc \<down> Normal s'"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f"
  apply (clarsimp simp: ac_def corres_underlying_def ccorres_underlying_def rf_sr_def Ball_def Bex_def)
  apply (rule conjI)
   -- "proof for return values"
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)

  -- "proof for fail bit is trickier"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (clarsimp simp: select_f_def select_def snd_bind snd_assert get_def split: sum.splits prod.splits)
  apply (erule impE)
   apply (blast intro: terminates)
  apply (erule disjE)
   apply (monad_eq split: xstate.splits sum.splits)
    apply (drule EHOther, fastforce)
    apply blast
   apply (drule EHOther, fastforce)
   apply blast
  apply (monad_eq split: xstate.splits)
  apply (fastforce dest: EHAbrupt[OF _ EHEmpty])
  done

text \<open>Does not require termination proof for f_'proc. Used with no_c_termination.\<close>
lemma ccorres_to_corres_no_termination:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl False \<Gamma> f_'proc)"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f"
  apply (clarsimp simp: ac_def corres_underlying_def ccorres_underlying_def rf_sr_def Ball_def Bex_def)
  apply (rule conjI)
   -- "proof for return values"
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)

  -- "proof for fail bit is trickier"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (clarsimp simp: select_f_def select_def snd_bind snd_assert get_def split: sum.splits prod.splits)
  apply (erule disjE)
   apply (monad_eq split: xstate.splits sum.splits)
    apply (drule EHOther, fastforce)
    apply blast
   apply (drule EHOther, fastforce)
   apply blast
  apply (monad_eq split: xstate.splits)
  apply (fastforce dest: EHAbrupt[OF _ EHEmpty])
  done

end



section \<open>Experiments with transferring bitfield proofs\<close>

text \<open>Generic transfer rules\<close>
lemma autocorres_transfer_spec:
  assumes ac_def:
    "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  assumes c_spec:
    "\<forall>s0. \<Gamma>\<turnstile> (Collect (\<lambda>s. s0 = s \<and> P s)) Call f_'proc (Collect (Q s0))"
  assumes precond_deps:
    "\<And>s t. \<lbrakk> arg_rel s; arg_rel t; globals s = globals t \<rbrakk> \<Longrightarrow> P s = P t"
  assumes postcond_deps:
    "\<And>s0 s0' s t. \<lbrakk> arg_rel s0; arg_rel s0'; globals s0 = globals s0';
                    ret_xf s = ret_xf t; globals s = globals t \<rbrakk> \<Longrightarrow> Q s0 s = Q s0' t"
  shows "\<lbrace>\<lambda>s. P cs \<and> s = globals cs \<and> arg_rel cs \<rbrace>
           ac_f
         \<lbrace>\<lambda>r s'. \<exists>cs'. s' = globals cs' \<and> r = ret_xf cs' \<and> Q cs cs' \<rbrace>"
  apply (clarsimp simp: valid_def ac_def AC_call_L1_def L2_call_L1_def L1_call_simpl_def
                        in_monad' in_liftM select_f_def in_select in_fail
                  split: sum.splits xstate.splits)
  apply (rename_tac r', case_tac r'; clarsimp)
  apply (rename_tac xst, case_tac xst; clarsimp)
  apply (drule_tac ?s0.1=s in exec_normal[OF _ _ c_spec[rule_format], rotated])
   apply (blast dest: precond_deps)
  apply (blast dest: postcond_deps)
  done

text \<open>This one is probably more useful\<close>
lemma autocorres_transfer_spec_no_modifies:
  assumes ac_def:
    "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  assumes c_spec:
    "\<forall>s0. hoarep \<Gamma> {} {} (P' s0) (Call f_'proc) (Collect (Q s0)) A" -- \<open>syntax parser barfs...\<close>
  assumes c_modifies:
    "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call f_'proc {t. t may_not_modify_globals \<sigma>}"
  assumes c_spec_unify:
    "\<And>s0. P' s0 = {s. s0 = s \<and> P s}"
  assumes precond_deps:
    "\<And>s0 s t. \<lbrakk> arg_rel s; arg_rel t; globals s = globals t \<rbrakk> \<Longrightarrow> P s = P t"
  assumes postcond_deps:
    "\<And>s0 s0' s t. \<lbrakk> arg_rel s0; arg_rel s0'; globals s0 = globals s0';
                    ret_xf s = ret_xf t; globals s = globals t \<rbrakk> \<Longrightarrow> Q s0 s = Q s0' t"
  shows "\<lbrace>\<lambda>s. s = globals cs \<and> P cs \<and> arg_rel cs \<rbrace>
           ac_f
         \<lbrace>\<lambda>r s'. s' = globals cs \<and> (\<exists>cs'. r = ret_xf cs' \<and> Q cs cs') \<rbrace>"
  apply (clarsimp simp: valid_def ac_def AC_call_L1_def L2_call_L1_def L1_call_simpl_def
                        in_monad' in_liftM select_f_def in_select in_fail
                  split: sum.splits xstate.splits)
  apply (rename_tac r', case_tac r'; clarsimp)
  apply (rename_tac xst, case_tac xst; clarsimp)
  apply (frule_tac ?s0.1=s in exec_normal[OF _ _ c_spec[rule_format], rotated])
   apply (clarsimp simp: c_spec_unify)
   apply (blast dest: precond_deps)
  apply (frule exec_normal[OF singletonI _ c_modifies[rule_format]])
  apply (clarsimp simp: meq_def)
  apply (blast dest: postcond_deps)
  done

subsection \<open>Helpers\<close>

lemma All_to_all':
  "(\<forall>x. P x) \<Longrightarrow> (\<And>x. P x)"
  by simp

text \<open>
  Convert references to global or local state variables, to the opposite one.
  FIXME: surely this has been proven already.
\<close>
lemma collect_lift:
  "Collect (\<lambda>s. s0 = s \<and> f s) = Collect (\<lambda>s. s0 = s \<and> f s0)"
  by blast
lemma collect_unlift:
  "Collect (\<lambda>s. s0 = s \<and> f s0 s) = Collect (\<lambda>s. s0 = s \<and> f s s)"
  by blast


subsection \<open>Experiment with wrapping specs\<close>
lemma exec_no_fault:
  assumes asms: "s \<in> P"
  and     ce: "Gamma \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Fault f"
  and  valid: "Gamma \<turnstile> P c Q, A"
  shows   "False"
  using valid ce asms
  apply -
  apply (frule hoare_sound)
  apply (clarsimp simp: NonDetMonad.bind_def cvalid_def split_def HoarePartialDef.valid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply auto
  done

lemma exec_no_stuck:
  assumes asms: "s \<in> P"
  and     ce: "Gamma \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Stuck"
  and  valid: "Gamma \<turnstile> P c Q, A"
  shows   "False"
  using valid ce asms
  apply -
  apply (frule hoare_sound)
  apply (clarsimp simp: NonDetMonad.bind_def cvalid_def split_def HoarePartialDef.valid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply auto
  done

definition L1_call_simpl_spec where
  "L1_call_simpl_spec check_term Gamma proc precond postcond =
     L1_spec (Collect (\<lambda>(s, t). precond s s \<and> postcond s t))"

lemma L1corres_call_simpl_spec:
  "\<lbrakk> \<forall>s0. Gamma\<turnstile> (Collect (precond s0)) (Call proc) (Collect (postcond s0));
     \<And>s. ct \<Longrightarrow> Gamma\<turnstile>Call proc \<down> Normal s \<rbrakk> \<Longrightarrow>
   L1corres ct Gamma (L1_call_simpl_spec ct Gamma proc precond postcond) (Call proc)"
  apply (clarsimp simp: L1corres_def L1_call_simpl_spec_def L1_defs
                        assert_def snd_select snd_liftE snd_spec
                        in_monad' in_spec
                  split: xstate.splits)
  apply (case_tac t)
     apply (blast dest: exec_normal[rotated])
    apply (blast dest: exec_abrupt[rotated])
   apply (blast intro: exec_no_fault[rotated])
  apply (blast intro: exec_no_stuck[rotated])
  done



section \<open>Termination proofs\<close>
text \<open>
  Proving termination side conditions for @{thm kernel.ccorres_to_corres_with_termination}.

  To begin with, we can automatically prove terminates for most
  helper functions as they do not have recursion or loops.
\<close>

named_theorems terminates_trivial

ML \<open>
local
  fun terminates_intros ctxt =
    REPEAT_ALL_NEW (resolve_tac ctxt (Proof_Context.get_thms ctxt "terminates_trivial"));
in
fun terminates_trivial_tac ctxt n st =
  case Logic.concl_of_goal (Thm.prop_of st) n of
      @{term_pat "Trueprop (_ \<turnstile> Call ?f_'proc \<down> _)"} => let
        val f = dest_Const f_'proc |> fst |> Long_Name.base_name |> unsuffix "_'proc";
        val impl = Proof_Context.get_thm ctxt (f ^ "_impl");
        val body = Proof_Context.get_thm ctxt (f ^ "_body_def");
        in st |>
           (resolve_tac ctxt @{thms terminates.Call} n
             THEN resolve_tac ctxt [impl] n
            THEN simp_tac (put_simpset HOL_ss ctxt addsimps
                             (body :: @{thms return_C_def lvar_nondet_init_def})) n
            THEN terminates_intros ctxt n) end
    | _ => terminates_intros ctxt n st
end
\<close>

lemma [terminates_trivial]:
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> c \<down> Normal s \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Guard F G c \<down> Normal s"
  apply (blast intro: terminates.Guard terminates.GuardFault)
  done
lemma [terminates_trivial]:
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> c1 \<down> Normal s; \<And>s. \<Gamma> \<turnstile> c2 \<down> Normal s \<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> Cond C c1 c2 \<down> Normal s"
  apply (blast intro: terminates.CondTrue terminates.CondFalse)
  done
lemma [terminates_trivial]:
  "\<lbrakk> \<Gamma> \<turnstile> c1 \<down> Normal s; \<And>s. \<Gamma> \<turnstile> c2 \<down> Normal s \<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> c1;;c2 \<down> Normal s"
  apply (erule terminates.Seq)
  apply clarsimp
  apply (case_tac s'; auto)
  done

lemma [terminates_trivial]:
  fixes \<Gamma> return init shows
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> Call p \<down> Normal s; \<And>s t u. \<Gamma> \<turnstile> c s t \<down> Normal u \<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> call init p return c \<down> Normal s"
  apply (case_tac "\<Gamma> p")
   apply (erule terminates_callUndefined)
  apply (fastforce simp: terminates_Call_body intro: terminates_call)
  done

lemmas [terminates_trivial] =
  terminates.Basic
  terminates.Catch[rule_format]
  terminates.Throw
  terminates.Skip
  terminates.Spec

end
