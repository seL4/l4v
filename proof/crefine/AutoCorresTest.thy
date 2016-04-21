(*
 * @LICENSE(NICTA) (FIXME?)
 *)

(* Experimental AutoCorres proofs over CRefine: work in progress *)

theory AutoCorresTest
imports "../../tools/autocorres/AutoCorres"
        "../../tools/autocorres/L4VerifiedLinks"
        AutoCorresModifiesProofs
        "../../../../isabelle-hacks/insulin/Insulin"
        "../../../../isabelle-hacks/ShowTypes"
        (* import Refine_C last to minimise change to global context *)
        Refine_C
begin


autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleYield,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "c/kernel_all.c_pp"


(* Prove and store modifies rules. *)
context kernel_all_substitute begin
local_setup \<open>fn ctxt =>
let val fn_info = Symtab.lookup (AutoCorresFunctionInfo.get (Proof_Context.theory_of ctxt)) "c/kernel_all.c_pp" |> the;
    val prog_info = ProgramInfo.get_prog_info ctxt "c/kernel_all.c_pp";
    val all_function_groups = FunctionInfo.get_topo_sorted_functions fn_info;
    val (callee_modifies, results, ctxt') =
          fold (AutoCorresModifiesProofs.define_modifies_group fn_info prog_info)
               all_function_groups (AutoCorresModifiesProofs.build_incr_net [], Symtab.empty, ctxt)
in ctxt' end
\<close>

end


subsection \<open>Proof frameworks\<close>

context kernel_m begin

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

text \<open>
  A fantasy world where ccorres_underlying is as strong as we need.
\<close>
context begin

private lemma ccorres_underlying_idealised_def:
  "\<And>srel rrel xf arrel axf G G' hs.
   ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs \<equiv>
   \<lambda>m c. \<forall>(s, s')\<in>srel.
            G s \<and> s' \<in> G' \<and> \<not> snd (m s) \<longrightarrow>
            \<Gamma> \<turnstile> c \<down> Normal s' \<and>
            (\<forall>n t. \<Gamma>\<turnstile>\<^sub>h \<langle>c # hs,s'\<rangle> \<Rightarrow> (n, t) \<longrightarrow>
                   (case t of Normal s'' \<Rightarrow> \<exists>(r, t)\<in>fst (m s). (t, s'') \<in> srel \<and> unif_rrel (n = length hs) rrel xf arrel axf r s'' | _ \<Rightarrow> False))"
  sorry

private lemma ccorres_to_corres_idealised:
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
private lemma
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



subsection \<open>Case study: handleYield\<close>

(* AutoCorres translation of handleYield *)
thm handleYield'_def

(* handleYield calls un-translated functions, such as tcbSchedDequeue *)
thm tcbSchedDequeue_body_def
(* AutoCorres produces a monadic wrapper of the SIMPL code *)
thm tcbSchedDequeue'_def
    tcbSchedDequeue'_def[unfolded AC_call_L1_def L2_call_L1_def L1_call_simpl_def]


text \<open>
  First, create some corres versions of ccorres rules.
\<close>
thm getCurThread_ccorres
lemma getCurThread_corres:
  "corres_underlying {(x, y). cstate_relation x y} True True (\<lambda>ct ct'. tcb_ptr_to_ctcb_ptr ct = ct') invs' (\<lambda>_. True) getCurThread (gets ksCurThread_')"
  by (simp add: getCurThread_def cstate_relation_def Let_def)

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
private lemma tcbSchedDequeue_corres_cheat:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and valid_queues' and tcb_at' ct and valid_objs') \<top>
     (tcbSchedDequeue ct) (tcbSchedDequeue' ct')"
  apply (rule ccorres_to_corres_idealised)
   apply (simp add: tcbSchedDequeue'_def)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedDequeue_ccorres[simplified])
  done

thm tcbSchedAppend_ccorres
private lemma tcbSchedAppend_corres_cheat:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and tcb_at' ct and valid_objs') \<top>
     (tcbSchedAppend ct) (tcbSchedAppend' ct')"
  apply (rule ccorres_to_corres_idealised)
   apply (simp add: tcbSchedAppend'_def)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedAppend_ccorres[simplified])
  done

thm rescheduleRequired_ccorres
private lemma rescheduleRequired_corres_cheat:
  "corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs') \<top>
     rescheduleRequired rescheduleRequired'"
  apply (rule ccorres_to_corres_idealised)
   apply (simp add: rescheduleRequired'_def)
  apply (clarsimp simp: ccorres_rrel_nat_unit rescheduleRequired_ccorres[simplified])
  done

text \<open>Returning to the real world...\<close>
end



text \<open>
  Instead of adding termination to ccorres in one go,
  we can also prove terminates as incremental side conditions.

  To begin with, we can automatically prove terminates for most
  helper functions as they do not have recursion or loops.
\<close>

named_theorems terminates_trivial

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

lemma cap_get_capType_terminates:
  "\<Gamma> \<turnstile> Call cap_get_capType_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule cap_get_capType_impl)
  apply (unfold cap_get_capType_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial)
  done

lemma thread_state_get_tcbQueued_terminates:
  "\<Gamma> \<turnstile> Call thread_state_get_tcbQueued_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule thread_state_get_tcbQueued_impl)
  apply (unfold thread_state_get_tcbQueued_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial)
  done

lemma thread_state_ptr_set_tcbQueued_terminates:
  "\<Gamma> \<turnstile> Call thread_state_ptr_set_tcbQueued_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule thread_state_ptr_set_tcbQueued_impl)
  apply (unfold thread_state_ptr_set_tcbQueued_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial)
  done

lemma ready_queues_index_terminates:
  "\<Gamma> \<turnstile> Call ready_queues_index_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule ready_queues_index_impl)
  apply (unfold ready_queues_index_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial)
  done

lemma prio_to_l1index_terminates:
  "\<Gamma> \<turnstile> Call prio_to_l1index_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule prio_to_l1index_impl)
  apply (unfold prio_to_l1index_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial)
  done

lemma removeFromBitmap_terminates:
  "\<Gamma> \<turnstile> Call removeFromBitmap_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule removeFromBitmap_impl)
  apply (unfold removeFromBitmap_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial prio_to_l1index_terminates)
  done

lemma addToBitmap_terminates:
  "\<Gamma> \<turnstile> Call addToBitmap_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule addToBitmap_impl)
  apply (unfold addToBitmap_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial prio_to_l1index_terminates)
  done

lemma tcbSchedDequeue_terminates:
   "\<Gamma> \<turnstile> Call tcbSchedDequeue_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule tcbSchedDequeue_impl)
  apply (unfold tcbSchedDequeue_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial
          thread_state_get_tcbQueued_terminates
          thread_state_ptr_set_tcbQueued_terminates
          ready_queues_index_terminates
          removeFromBitmap_terminates)
  done

lemma tcbSchedAppend_terminates:
   "\<Gamma> \<turnstile> Call tcbSchedAppend_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule tcbSchedAppend_impl)
  apply (unfold tcbSchedAppend_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial
          thread_state_get_tcbQueued_terminates
          thread_state_ptr_set_tcbQueued_terminates
          ready_queues_index_terminates
          addToBitmap_terminates)
  done

lemma tcbSchedEnqueue_terminates:
   "\<Gamma> \<turnstile> Call tcbSchedEnqueue_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule tcbSchedEnqueue_impl)
  apply (unfold tcbSchedEnqueue_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial
          thread_state_get_tcbQueued_terminates
          thread_state_ptr_set_tcbQueued_terminates
          ready_queues_index_terminates
          addToBitmap_terminates)
  done

lemma rescheduleRequired_terminates:
   "\<Gamma> \<turnstile> Call rescheduleRequired_'proc \<down> Normal s"
  apply (rule terminates.Call)
   apply (rule rescheduleRequired_impl)
  apply (unfold rescheduleRequired_body_def return_C_def lvar_nondet_init_def)
  apply (intro terminates_trivial
          tcbSchedEnqueue_terminates)
  done


text \<open>Verify handleYield without cheating\<close>

lemma ccorres_to_corres:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl \<Gamma> f_'proc)"
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
  apply (clarsimp simp: select_f_def select_def snd_bind split: sum.splits prod.splits)
  apply (clarsimp simp: Bex_def get_def)
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


thm tcbSchedDequeue_ccorres
lemma tcbSchedDequeue_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and valid_queues' and tcb_at' ct and valid_objs') \<top>
     (tcbSchedDequeue ct) (tcbSchedDequeue' ct')"
  apply (rule ccorres_to_corres)
    apply (simp add: tcbSchedDequeue'_def)
   apply (rule tcbSchedDequeue_terminates)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedDequeue_ccorres[simplified])
  done

thm tcbSchedAppend_ccorres
lemma tcbSchedAppend_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and tcb_at' ct and valid_objs') \<top>
     (tcbSchedAppend ct) (tcbSchedAppend' ct')"
  apply (rule ccorres_to_corres)
    apply (simp add: tcbSchedAppend'_def)
   apply (rule tcbSchedAppend_terminates)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedAppend_ccorres[simplified])
  done

thm rescheduleRequired_ccorres
lemma rescheduleRequired_corres:
  "corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs') \<top>
     rescheduleRequired rescheduleRequired'"
  apply (rule ccorres_to_corres)
    apply (simp add: rescheduleRequired'_def)
   apply (rule rescheduleRequired_terminates)
  apply (clarsimp simp: ccorres_rrel_nat_unit rescheduleRequired_ccorres[simplified])
  done

text \<open>
  Proving handleYield_ccorres via handleYield'.
  The handleYield spec has one less getCurThread, so we need to use the fact
  that tcbSchedDequeue does not modify ksCurThread.
\<close>
thm tcbSchedDequeue'_modifies

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

lemma reorder_gets:
  "(\<And>x. \<lbrace> \<lambda>s. x = f s \<rbrace> g \<lbrace> \<lambda>_ s. x = f s \<rbrace>) \<Longrightarrow>
   (do x \<leftarrow> gets f;
       g;
       h x od) =
   (do g;
       x \<leftarrow> gets f;
       h x od)"
  by (fastforce simp: bind_def' valid_def gets_def get_def return_def)

text \<open>Now the proof.\<close>
lemma (* handleYield_ccorres: *)
  "ccorres dc xfdc (invs' and ct_active') UNIV [] handleYield (Call handleYield_'proc)"
  apply (rule autocorres_to_ccorres[where arg_rel = \<top>, simplified Collect_True])
   apply (rule kernel_all_substitute.handleYield'_ac_corres)
  apply (simp add: handleYield_def handleYield'_def)

  apply (rule corres_guard_imp)
    (* Emulate vcg exspec=tcbSchedDequeue_modifies
     * FIXME: proper way to do this? *)
    apply (subst reorder_gets[symmetric, unfolded K_bind_def])
     using tcbSchedDequeue'_modifies apply (fastforce simp: valid_def)
    apply (subst gets_gets)

    apply (rule corres_pre_getCurThread)
    apply (rule corres_split[OF _ tcbSchedDequeue_corres])
       apply (rule corres_split[OF _ tcbSchedAppend_corres])
          apply (rule rescheduleRequired_corres)
         apply (solves simp)
        apply (solves \<open>wp tcbSchedAppend_valid_objs' weak_sch_act_wf_lift_linear | simp\<close>)+
     apply wps
     apply (solves \<open>wp tcbSchedDequeue_invs' tcbSchedDequeue_typ_at'
                       tcbSchedDequeue_valid_queues tcbSchedDequeue_valid_objs'
                       weak_sch_act_wf_lift_linear\<close>)
    apply (solves wp)
   apply (clarsimp simp: invs_valid_objs' invs_queues invs_valid_queues' tcb_at_invs'
                         valid_objs'_maxPriority valid_objs'_maxDomain)
   apply (fastforce simp: obj_at'_def st_tcb_at'_def ct_in_state'_def dest: ct_active_runnable')
  apply fastforce
  done

end

end
