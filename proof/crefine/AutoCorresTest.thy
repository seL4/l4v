(*
 * @LICENSE(NICTA) (FIXME?)
 *)

(* Experimental AutoCorres proofs over CRefine: work in progress *)

theory AutoCorresTest
imports "../../tools/autocorres/AutoCorres"
        "../../tools/autocorres/L4VerifiedLinks"
        "../../../../isabelle-hacks/insulin/Insulin"
        "../../../../isabelle-hacks/ShowTypes"
        (* import Refine_C last to minimise change to global context *)
        Refine_C
begin


autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleYield,
   scope_depth = 0
  ] "c/kernel_all.c_pp"

find_theorems
  handleSyscall_'proc
  Substitute.kernel_all_substitute.\<Gamma>


subsection \<open>Proof frameworks\<close>

context kernel_m begin

text \<open>
  Strengthening of ccorres_underlying. Sorried; for testing purposes only.
\<close>
lemma ccorres_underlying_idealised_def:
  "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs \<equiv>
  \<lambda>m c. \<forall>(s, s')\<in>srel.
            G s \<and> s' \<in> G' \<and> \<not> snd (m s) \<longrightarrow>
            \<Gamma> \<turnstile> c \<down> Normal s' \<and>
            (\<forall>n t. \<Gamma>\<turnstile>\<^sub>h \<langle>c # hs,s'\<rangle> \<Rightarrow> (n, t) \<longrightarrow>
                   (case t of Normal s'' \<Rightarrow> \<exists>(r, t)\<in>fst (m s). (t, s'') \<in> srel \<and> unif_rrel (n = length hs) rrel xf arrel axf r s'' | _ \<Rightarrow> False))"
  sorry

text \<open>
  From AutoCorres @{term ac_corres}, obtain @{term ccorres}.
  This requires a separate corres_underlying proof between the
  AutoCorres spec and DSpec, in order to establish @{term cstate_relation}.
\<close>
lemma autocorres_to_ccorres:
  "\<lbrakk> ac_corres globals \<Gamma> ret_xf arg_rel (liftE ac_f) (Call f_'proc);
     corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc P (Collect arg_rel) [] dspec_f (Call f_'proc)"
  by (fastforce simp: ccorres_underlying_def corres_underlying_def rf_sr_def Ball_def
                      liftE_def in_liftE[simplified liftE_def] unif_rrel_def
                dest: ac_corres_ccorres_underlying split: xstate.splits)


text \<open>
  From @{term ccorres} obtain @{term corres}.
  This is for exporting existing ccorres theorems to be used
  in AutoCorres-based corres proofs.
\<close>
thm AC_call_L1_def L2_call_L1_def L1_call_simpl_def
lemma in_AC_call_simpl:
  fixes r s s' arg_pred globals ret_xf \<Gamma> f_'proc
  shows "(r, s') \<in> fst (AC_call_L1 arg_pred globals ret_xf (L1_call_simpl \<Gamma> f_'proc) s) \<Longrightarrow>
         \<exists>cs cs'. s = globals cs \<and> arg_pred cs \<and>
                  \<Gamma> \<turnstile> Call f_'proc \<down> Normal cs \<and>
                  \<Gamma> \<turnstile> \<langle>Call f_'proc, Normal cs\<rangle> \<Rightarrow> Normal cs' \<and>
                  s' = globals cs' \<and> r = ret_xf cs'"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (monad_eq simp: liftM_def select_def select_f_def liftE_def split: xstate.splits sum.splits)
  apply (rename_tac cs cs' status)
  apply (case_tac status)
  apply auto
  done

lemma ccorres_to_corres_partial:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl \<Gamma> f_'proc)"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True False R P \<top> dspec_f ac_f"
  by (fastforce simp: unif_rrel_def ac_def corres_underlying_def ccorres_underlying_def rf_sr_def
                intro: EHOther dest: in_AC_call_simpl)

lemma ccorres_to_corres:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl \<Gamma> f_'proc)"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f"
  apply (clarsimp simp: ac_def corres_underlying_def ccorres_underlying_def rf_sr_def Ball_def Bex_def)
  apply (rule conjI)
   -- "proof for return values"
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)

  -- "proof for fail bit is trickier"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (clarsimp simp: select_f_def select_def snd_bind split: sum.splits prod.splits)
  apply (clarsimp simp: Bex_def get_def)
  apply (erule impE)
   -- "oops... @{term ccorres} doesn't give us @{term terminates}"
   subgoal sorry
  apply (erule disjE)
   apply (monad_eq split: xstate.splits sum.splits)
    apply (drule EHOther, fastforce)
    apply blast
   apply (drule EHOther, fastforce)
   apply blast
  apply (monad_eq split: xstate.splits)
  apply (fastforce dest: EHAbrupt[OF _ EHEmpty])
  done

text \<open>With proposed alternative ccorres...\<close>
lemma
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl \<Gamma> f_'proc)"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f"
  apply (clarsimp simp: ac_def corres_underlying_def ccorres_underlying_idealised_def rf_sr_def Ball_def Bex_def)
  apply (rule conjI)
   -- "proof for return values"
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)

  -- "proof for fail bit is trickier"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (clarsimp simp: select_f_def select_def snd_bind split: sum.splits prod.splits)
  apply (clarsimp simp: Bex_def get_def)
  apply (erule disjE)
   apply (monad_eq split: xstate.splits sum.splits)
    apply (drule EHOther, fastforce)
    apply blast
   apply (drule EHOther, fastforce)
   apply blast
  apply (monad_eq split: xstate.splits)
  apply (fastforce dest: EHAbrupt[OF _ EHEmpty])
  done


lemma ccorres_rrel_nat_unit:
  "ccorres op = (\<lambda>s. ()) st_P arg_P hs m c = ccorres dc xfdc st_P arg_P hs m c"
  by (simp add: ccorres_underlying_def dc_def xfdc_def unif_rrel_def cong del: xstate.case_cong)

(* FIXME: this is a lie *)
lemma \<Gamma>_eq: "kernel_all_global_addresses.\<Gamma> symbol_table = kernel_all_substitute.\<Gamma> symbol_table domain"
  sorry



subsection \<open>Case study: handleYield\<close>

(* AutoCorres translation of handleYield *)
thm kernel_all.handleYield'_def

(* handleYield calls un-translated functions, such as tcbSchedDequeue *)
thm tcbSchedDequeue_body_def
(* AutoCorres produces a monadic wrapper of the SIMPL code *)
thm kernel_all.tcbSchedDequeue'_def
    kernel_all.tcbSchedDequeue'_def[unfolded AC_call_L1_def L2_call_L1_def L1_call_simpl_def]


text \<open>
  First, create some corres versions of ccorres rules.
\<close>
thm getCurThread_ccorres
lemma getCurThread_corres:
  "corres_underlying {(x, y). cstate_relation x y} True True (\<lambda>ct ct'. tcb_ptr_to_ctcb_ptr ct = ct') invs' (\<lambda>_. True) getCurThread (gets ksCurThread_')"
  apply (simp add: getCurThread_def cstate_relation_def)
  by metis

thm ccorres_pre_getCurThread
lemma corres_pre_getCurThread:
  assumes cc: "\<And>rv rv'. rv' = tcb_ptr_to_ctcb_ptr rv \<Longrightarrow>
                  corres_underlying {(x, y). cstate_relation x y} True True R (P rv) (P' rv) (f rv) (f' rv')"
  shows   "corres_underlying {(x, y). cstate_relation x y} True True R
                  (\<lambda>s. \<forall>rv. ksCurThread s = rv \<longrightarrow> P rv s)
                  (\<lambda>s. \<forall>rv. ksCurThread_' s = tcb_ptr_to_ctcb_ptr rv \<longrightarrow> P' rv s)
                  (getCurThread >>= f) (gets ksCurThread_' >>= f')"
  (* ugly but works -- corres_symb_exec_l doesn't *)
  using cc
  apply (clarsimp simp: corres_underlying_def getCurThread_def)
  apply monad_eq
  apply (clarsimp simp: cstate_relation_def Let_def)
  done

thm tcbSchedDequeue_ccorres
lemma tcbSchedDequeue_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and valid_queues' and tcb_at' ct and valid_objs') \<top>
     (tcbSchedDequeue ct) (kernel_all.tcbSchedDequeue' symbol_table ct')"
  apply (rule ccorres_to_corres)
   apply (simp add: kernel_all.tcbSchedDequeue'_def \<Gamma>_eq)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedDequeue_ccorres[simplified])
  done

thm tcbSchedAppend_ccorres
lemma tcbSchedAppend_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and tcb_at' ct and valid_objs') \<top>
     (tcbSchedAppend ct) (kernel_all.tcbSchedAppend' symbol_table ct')"
  apply (rule ccorres_to_corres)
   apply (simp add: kernel_all.tcbSchedAppend'_def \<Gamma>_eq)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedAppend_ccorres[simplified])
  done

thm rescheduleRequired_ccorres
lemma rescheduleRequired_corres:
  "corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs') \<top>
     rescheduleRequired (kernel_all.rescheduleRequired' symbol_table)"
  apply (rule ccorres_to_corres)
   apply (simp add: kernel_all.rescheduleRequired'_def \<Gamma>_eq)
  apply (clarsimp simp: ccorres_rrel_nat_unit rescheduleRequired_ccorres[simplified])
  done

text \<open>
  This spec (one extra getCurThread) is easier to prove.
  Doing the corres proof on handleYield_def requires reasoning about modifies
  for tcbSchedDequeue.
\<close>
lemma handleYield_alt_def:
  "handleYield \<equiv> do thread \<leftarrow> getCurThread;
                     tcbSchedDequeue thread;
                     thread \<leftarrow> getCurThread;
                     tcbSchedAppend thread;
                     rescheduleRequired
                  od"
  sorry
(* ... matches this \<longrightarrow> *) thm kernel_all.handleYield'_def


(* ugly modifies rules *)
thm tcbSchedDequeue_modifies
desugar_thm tcbSchedDequeue_modifies "["


text \<open>Existing ccorres proof, for reference\<close>
lemma
  "ccorres dc xfdc
       (invs' and ct_active')
       UNIV
       []
       (handleYield)
       (Call handleYield_'proc)"
  apply cinit
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: tcbSchedDequeue_ccorres)
     apply (ctac  add: tcbSchedAppend_ccorres)
       apply (ctac add: rescheduleRequired_ccorres)
      apply (wp weak_sch_act_wf_lift_linear tcbSchedAppend_valid_objs')
     apply (vcg exspec= tcbSchedAppend_modifies)
    apply (wp weak_sch_act_wf_lift_linear tcbSchedDequeue_valid_queues)
   apply (vcg exspec= tcbSchedDequeue_modifies)
  apply (clarsimp simp: tcb_at_invs' invs_valid_objs'
                        valid_objs'_maxPriority valid_objs'_maxDomain)
  apply (auto simp: obj_at'_def st_tcb_at'_def ct_in_state'_def valid_objs'_maxDomain)
  done


text \<open>ccorres proof using AutoCorres\<close>
lemma (* handleYield_ccorres: *)
  "ccorres dc xfdc (invs' and ct_active') UNIV [] handleYield (Call handleYield_'proc)"
  apply (rule autocorres_to_ccorres[where arg_rel = \<top>, simplified Collect_True])
   apply (subst \<Gamma>_eq[symmetric])
   apply (rule kernel_all.handleYield'_ac_corres)
  apply (simp add: handleYield_alt_def kernel_all.handleYield'_def)

  apply (rule corres_guard_imp)
    apply (rule corres_pre_getCurThread)
    apply (rule corres_split[OF _ tcbSchedDequeue_corres])
       apply (rule corres_split[OF _ getCurThread_corres])
         apply (rule corres_split[OF _ tcbSchedAppend_corres])
            apply (rule rescheduleRequired_corres)
           apply simp
          apply ((wp weak_sch_act_wf_lift_linear tcbSchedAppend_valid_objs' | simp)+)[5]
     apply (clarsimp simp: pred_conj_def)
     apply wps
     apply (wp tcbSchedDequeue_invs' tcbSchedDequeue_typ_at' tcbSchedDequeue_valid_queues tcbSchedDequeue_valid_objs' weak_sch_act_wf_lift_linear)[1]
    apply wp[1]
   apply (clarsimp simp: invs_valid_objs' invs_queues invs_valid_queues' tcb_at_invs'
                         valid_objs'_maxPriority valid_objs'_maxDomain)
   apply (drule ct_active_runnable')
   apply (clarsimp simp: obj_at'_def st_tcb_at'_def ct_in_state'_def)
  apply clarsimp
  done

end


end
