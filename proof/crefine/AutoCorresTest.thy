(*
 * @LICENSE(NICTA) (FIXME?)
 *)

(* Experimental AutoCorres proofs over CRefine: work in progress *)

theory AutoCorresTest
imports "../../tools/autocorres/AutoCorres"
        "../../tools/autocorres/L4VerifiedLinks"
        AutoCorresModifiesProofs
        (* import Refine_C last to minimise change to global context *)
        Refine_C
begin

ML \<open>
fun do_ac_modifies_rules filename ctxt = let
    val fn_info = Symtab.lookup (AutoCorresFunctionInfo.get (Proof_Context.theory_of ctxt)) filename |> the;
    val prog_info = ProgramInfo.get_prog_info ctxt filename;
    val existing_modifies =
          Symtab.dest (FunctionInfo.get_functions fn_info)
          |> List.mapPartial (fn (fn_name, fn_def) =>
               if not (#finished fn_def) then NONE else
                 SOME (fn_name, Proof_Context.get_thm ctxt (fn_name ^ "'_modifies")))
    val all_function_groups = FunctionInfo.get_topo_sorted_functions fn_info;
    val (callee_modifies, results, ctxt') =
          fold (AutoCorresModifiesProofs.define_modifies_group fn_info prog_info)
               all_function_groups (AutoCorresModifiesProofs.build_incr_net (map snd existing_modifies),
                                    Symtab.make existing_modifies, ctxt)
in ctxt' end
\<close>

autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleYield,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "c/kernel_all.c_pp"

(* Prove and store modifies rules. *)
context kernel_all_substitute begin
local_setup \<open>do_ac_modifies_rules "c/kernel_all.c_pp"\<close>
end


subsection \<open>Proof frameworks\<close>


context kernel_m begin

thm handleYield_body_def
    handleYield'_def
    handleYield_def
    tcbSchedDequeue'_def
    tcbSchedDequeue'_def[unfolded AC_call_L1_def L2_call_L1_def L1_call_simpl_def]
thm handleYield'_ac_corres
thm handleYield'_modifies
desugar_thm handleYield_modifies[unfolded mex_def meq_def] "may_only"

text \<open>
  From AutoCorres @{term ac_corres}, obtain @{term ccorres}.
  This requires a separate corres_underlying proof between the
  AutoCorres spec and design Spec, in order to establish @{term cstate_relation}.
\<close>
lemma autocorres_to_ccorres:
  "\<lbrakk> ac_corres globals check_termination \<Gamma> ret_xf arg_rel (liftE ac_f) (Call f_'proc);
     arg_relS = Collect arg_rel;
     corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc P arg_relS [] dspec_f (Call f_'proc)"
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

lemma ccorres_to_corres_partial:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True False R P \<top> dspec_f ac_f"
  by (fastforce simp: unif_rrel_def ac_def corres_underlying_def ccorres_underlying_def rf_sr_def
                intro: EHOther dest: in_AC_call_simpl)

text \<open>
  A fantasy world where ccorres_underlying proves termination.
\<close>
context begin

private lemma ccorres_underlying_idealised_def:
  "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs \<equiv>
   \<lambda>m c. \<forall>(s, s')\<in>srel.
            G s \<and> s' \<in> G' \<and> \<not> snd (m s) \<longrightarrow>
            \<Gamma> \<turnstile> c \<down> Normal s' \<and>
            (\<forall>n t. \<Gamma>\<turnstile>\<^sub>h \<langle>c # hs,s'\<rangle> \<Rightarrow> (n, t) \<longrightarrow>
                   (case t of Normal s'' \<Rightarrow> \<exists>(r, t)\<in>fst (m s). (t, s'') \<in> srel \<and> unif_rrel (n = length hs) rrel xf arrel axf r s'' | _ \<Rightarrow> False))"
  sorry

private lemma ccorres_to_corres_idealised:
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  shows "\<lbrakk> ccorres R ret_xf P (Collect arg_rel) [] dspec_f (Call f_'proc) \<rbrakk> \<Longrightarrow>
         corres_underlying {(s, s'). cstate_relation s s'} True True R P \<top> dspec_f ac_f"
  apply (clarsimp simp: ac_def corres_underlying_def ccorres_underlying_def rf_sr_def Ball_def Bex_def)
  apply (rule conjI)
   -- "proof for return values"
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)

  -- "proof for fail bit is trickier"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (case_tac check_termination)
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

  (* FIXME: duplication *)
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

text \<open>With proposed alternative ccorres...\<close>
private lemma
  assumes ac_def: "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
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



subsection \<open>Termination on demand\<close>
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


text \<open>Process handleYield's callees without cheating\<close>

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


thm tcbSchedDequeue_ccorres
lemma tcbSchedDequeue_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and valid_queues' and tcb_at' ct and valid_objs') \<top>
     (tcbSchedDequeue ct) (tcbSchedDequeue' ct')"
  apply (rule ccorres_to_corres_no_termination)
   apply (simp add: tcbSchedDequeue'_def)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedDequeue_ccorres[simplified])
  done

thm tcbSchedAppend_ccorres
lemma tcbSchedAppend_corres:
  "tcb_ptr_to_ctcb_ptr ct = ct' \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and tcb_at' ct and valid_objs') \<top>
     (tcbSchedAppend ct) (tcbSchedAppend' ct')"
  apply (rule ccorres_to_corres_no_termination)
   apply (simp add: tcbSchedAppend'_def)
  apply (clarsimp simp: ccorres_rrel_nat_unit tcbSchedAppend_ccorres[simplified])
  done

thm rescheduleRequired_ccorres
lemma rescheduleRequired_corres:
  "corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (Invariants_H.valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs') \<top>
     rescheduleRequired rescheduleRequired'"
  apply (rule ccorres_to_corres_no_termination)
   apply (simp add: rescheduleRequired'_def)
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
  apply (rule autocorres_to_ccorres[OF _ refl, where arg_rel = \<top>, simplified Collect_True])
   apply (rule kernel_all_substitute.handleYield'_ac_corres)
  apply (simp add: handleYield_def handleYield'_def)

  apply (rule corres_guard_imp)
    (* Show that current thread is unmodified.
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

context kernel_m begin
ML \<open>
(* Search for function call testcase:
 *   function calls with the smallest caller + callee *)
let val ctxt = @{context};
    val fn_info = FunctionInfo.init_fn_info ctxt "c/kernel_all.c_pp";
    val real_funcs =
          Symtab.dest (FunctionInfo.get_functions fn_info)
          |> filter (fn (f, info) => case Thm.prop_of (#definition info) of
                        @{term_pat "_ \<equiv> Spec _"} => false
                      | @{term_pat "_ \<equiv> TRY SKIP CATCH SKIP END"} => false
                      | _ => true)
          |> map fst
          |> filter (fn f => isSome (try (Proof_Context.get_thm ctxt) (f ^ "_ccorres")))
          |> Symset.make;
    val call2s = Symtab.dest (FunctionInfo.get_functions fn_info)
          |> maps (fn (fn_name, fn_def) =>
                if not (Symset.contains real_funcs fn_name) then [] else
                FunctionInfo.get_function_callees fn_info fn_name
                |> filter (Symset.contains real_funcs)
                |> map (fn callee =>
                    (size_of_thm (#definition fn_def) +
                       size_of_thm (#definition (FunctionInfo.get_function_def fn_info callee)),
                     (fn_name, callee))));
in sort (prod_ord int_ord (K EQUAL)) call2s end
\<close>
thm handleFault_body_def handleDoubleFault_body_def
thm handleFault_ccorres handleDoubleFault_ccorres
end


autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleDoubleFault,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "c/kernel_all.c_pp"

(* Prove and store modifies rules. *)
context kernel_all_substitute begin
local_setup \<open>do_ac_modifies_rules "c/kernel_all.c_pp"\<close>
end

context kernel_m begin
lemma (*handleDoubleFault_ccorres:*)
  "ccorres dc xfdc (invs' and  tcb_at' tptr and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and
        sch_act_not tptr and (\<lambda>s. \<forall>p. tptr \<notin> set (ksReadyQueues s p)))
      (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr tptr})
      [] (handleDoubleFault tptr ex1 ex2)
         (Call handleDoubleFault_'proc)"
  apply (cinit lift: tptr_')
   apply (subst ccorres_seq_skip'[symmetric])
   apply (ctac (no_vcg))
    apply (rule ccorres_symb_exec_l)
       apply (rule ccorres_return_Skip)
      apply (wp asUser_inv getRestartPC_inv)
    apply (rule empty_fail_asUser)
    apply (simp add: getRestartPC_def)
   apply wp
  apply clarsimp
  apply (simp add: ThreadState_Inactive_def)
  apply (fastforce simp: valid_tcb_state'_def)
  done

thm setThreadState_ccorres[no_vars]
lemma setThreadState_corres:
  "(\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := ts && mask 4\<rparr>, fl)) \<and>
   tptr = tcb_ptr_to_ctcb_ptr thread \<Longrightarrow>
   corres_underlying {(x, y). cstate_relation x y} True True (op=)
     (\<lambda>s. tcb_at' thread s \<and>
       Invariants_H.valid_queues s \<and>
       valid_objs' s \<and>
       valid_tcb_state' st s \<and>
       (ksSchedulerAction s = SwitchToThread thread \<longrightarrow> runnable' st) \<and> (\<forall>p. thread \<in> set (ksReadyQueues s p) \<longrightarrow> runnable' st) \<and> sch_act_wf (ksSchedulerAction s) s) \<top>
     (setThreadState st thread) (setThreadState' tptr ts)"
  apply (rule ccorres_to_corres_no_termination)
   apply (simp add: setThreadState'_def)
  apply (clarsimp simp: ccorres_rrel_nat_unit)
  using setThreadState_ccorres
  apply (fastforce simp: ccorres_underlying_def Ball_def)
  done

lemma corres_gen_asm':
  "\<lbrakk> corres_underlying sr nf nf' r Q P' f g; \<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; P' s' \<rbrakk> \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' r P P' f g"
  by (fastforce simp: corres_underlying_def)

lemma corres_add_noop_rhs2:
  "corres_underlying sr nf nf' r P P' f (do _ \<leftarrow> g; return () od)
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

(* use termination (nf=True) to avoid exs_valid *)
lemma corres_noop2_no_exs:
  assumes x: "\<And>s. P s  \<Longrightarrow> \<lbrace>op = s\<rbrace> f \<lbrace>\<lambda>r. op = s\<rbrace> \<and> empty_fail f"
  assumes y: "\<And>s. P' s \<Longrightarrow> \<lbrace>op = s\<rbrace> g \<lbrace>\<lambda>r. op = s\<rbrace>"
  assumes z: "nf' \<Longrightarrow> no_fail P f" "no_fail P' g"
  shows      "corres_underlying sr True nf' dc P P' f g"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   apply (drule x, drule y)
   apply (clarsimp simp: valid_def empty_fail_def Ball_def Bex_def)
   apply fast
  apply (insert z)
  apply (clarsimp simp: no_fail_def)
  done

lemma corres_symb_exec_l_no_exs:
  assumes z: "\<And>rv. corres_underlying sr True nf' r (Q rv) P' (x rv) y"
  assumes x: "\<And>s. P s \<Longrightarrow> \<lbrace>op = s\<rbrace> m \<lbrace>\<lambda>r. op = s\<rbrace> \<and> empty_fail m"
  assumes y: "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail P m"
  shows      "corres_underlying sr True nf' r P P' (m >>= (\<lambda>rv. x rv)) y"
  apply (rule corres_guard_imp)
    apply (subst gets_bind_ign[symmetric], rule corres_split)
       apply (rule z)
      apply (rule corres_noop2_no_exs)
         apply (erule x)
        apply (rule gets_wp)
       apply (erule nf)
      apply (rule non_fail_gets)
     apply (rule y)
    apply (rule gets_wp)
   apply simp+
  done

lemma (*handleDoubleFault_ccorres:*)
  "ccorres dc xfdc (invs' and tcb_at' tptr and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and
        sch_act_not tptr and (\<lambda>s. \<forall>p. tptr \<notin> set (ksReadyQueues s p)))
      (UNIV \<inter> {s. ex1_' s = ex1' \<and> tptr_' s = tcb_ptr_to_ctcb_ptr tptr})
      [] (handleDoubleFault tptr ex1 ex2)
         (Call handleDoubleFault_'proc)"
  apply (rule autocorres_to_ccorres[where R="op="])
    apply (rule handleDoubleFault'_ac_corres)
   apply (simp add: pred_conj_def)
  apply (unfold handleDoubleFault_def handleDoubleFault'_def)
  apply (simp only: K_bind_def) -- "normalise"
  apply (rule corres_add_noop_rhs2) -- "split out extra haskell code"
  apply (rule corres_split')
     (* call setThreadState *)
     apply (rule corres_gen_asm')
      apply (rule setThreadState_corres)
      apply (simp add: ThreadState_Inactive_def)
     apply (fastforce simp: valid_tcb_state'_def ThreadState_Inactive_def)
    (* extra haskell code *)
    apply simp
    apply (rule corres_symb_exec_l_no_exs)
       apply simp
      apply (rule conjI)
       apply (wp asUser_inv getRestartPC_inv)
      apply (wp empty_fail_asUser)[1]
     apply (rule hoare_TrueI)
    apply (simp add: getRestartPC_def)
    apply wp
   apply simp
  apply (rule hoare_TrueI)
  done

end

autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleFault,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "c/kernel_all.c_pp"

(* Prove and store modifies rules. *)
context kernel_all_substitute begin
local_setup \<open>do_ac_modifies_rules "c/kernel_all.c_pp"\<close>
end

context kernel_m begin

thm handleFault_ccorres

end





text \<open>
  __builtin_clzl is defined using guarded_spec_body,
  which is a bit hard to translate generically.
  This is an experiment to translate clzl manually.
\<close>
context kernel_all_substitute begin

thm kernel_m.clzl_spec clzl_body_def

definition l1_clzl' :: "nat \<Rightarrow> (globals myvars, unit + unit) nondet_monad" where
  "l1_clzl' rec_measure' \<equiv>
     L1_spec ({(s', t). (\<forall>s. s' \<in> \<lbrace>s. \<^bsup>s\<^esup>x \<noteq> 0\<rbrace> \<longrightarrow> t \<in> \<lbrace>\<acute>ret__long = of_nat (word_clz \<^bsup>s\<^esup>x)\<rbrace>) \<and>
                          (\<exists>s. s' \<in> \<lbrace>s. \<^bsup>s\<^esup>x \<noteq> 0\<rbrace>)} \<inter> {(s, t). t may_not_modify_globals s})"

lemma l1_clzl'_corres:
  "L1corres ct \<Gamma> (l1_clzl' rec_measure') (Call clzl_'proc)"
  apply (unfold l1_clzl'_def)
  apply (rule L1corres_Call)
   apply (rule clzl_impl)
  apply (unfold clzl_body_def)
  apply (rule L1corres_guarded_spec)
  done

definition l2_clzl' :: "nat \<Rightarrow> 32 word \<Rightarrow> (globals, unit + 32 signed word) nondet_monad" where
  "l2_clzl' rec_measure' x \<equiv>
     L2_seq (L2_guard (\<lambda>_. x \<noteq> 0))
       (\<lambda>_. L2_gets (\<lambda>_. of_nat (word_clz x)) [''ret''])"

lemma l2_clzl'_corres:
  "L2corres globals ret__long_' (\<lambda>_. ()) (\<lambda>s. x_' s = x) (l2_clzl' rec_measure' x) (l1_clzl' rec_measure')"
  apply (unfold l2_clzl'_def l1_clzl'_def)
  apply (monad_eq simp: L1_defs L2_defs L2corres_def corresXF_def meq_def)
  apply (subst myvars.splits)
  apply simp
  done

definition clzl' :: "32 word \<Rightarrow> (globals, 32 signed word) nondet_monad" where
  "clzl' x \<equiv> do guard (\<lambda>_. x \<noteq> 0);
                return (of_nat (word_clz x)) od"

lemma clzl'_TScorres:
  "L2_call (l2_clzl' rec_measure' x) = liftE (clzl' x)"
  apply (unfold l2_clzl'_def clzl'_def)
  apply (tactic {* simp_tac (@{context} addsimps
      (#lift_rules (the (Monad_Types.get_monad_type "nondet" (Context.Proof @{context})))
       |> Thmtab.dest |> map fst)) 1 *})
  done

lemma "ac_corres globals ct \<Gamma> ret__long_' (\<lambda>s. x_' s = x) (liftE (clzl' x)) (Call clzl_'proc)"
  apply (rule ac_corres_chain[OF _ _ L2Tcorres_id corresTA_trivial, simplified o_def, simplified])
    apply (rule l1_clzl'_corres)
   apply (rule l2_clzl'_corres)
  apply (rule clzl'_TScorres)
  done
end

text \<open>Add our manual translation of clzl into the AutoCorres function info.\<close>
setup {*
let val clzl_raw_const = @{term "kernel_all_substitute.clzl'"};
    val clzl_const = @{term "kernel_all_substitute.clzl'"};
    val clzl_info = {
      name = "clzl",
      args = [("x", @{typ "32 word"})],
      return_type = @{typ "32 signed word"},
      const = clzl_const,
      raw_const = clzl_raw_const,
      definition = @{thm kernel_all_substitute.clzl'_def},
      finished = false,
      invented_body = false,
      is_simpl_wrapper = false,
      mono_thm = @{thm TrueI}
    }: FunctionInfo.function_def;
    val file = "c/kernel_all.c_pp";
    val fn_info = the (Symtab.lookup (AutoCorresFunctionInfo.get @{theory}) file);
    val fn_info' = case fn_info of FunctionInfo.FunctionInfo x =>
      FunctionInfo.FunctionInfo
        {const_to_function = Termtab.update_new (clzl_raw_const, "clzl") (#const_to_function x),
         function_callees = Symtab.update_new ("clzl", []) (#function_callees x),
         topo_sorted_functions = ["clzl"] :: #topo_sorted_functions x,
         recursive_functions = Symtab.update_new ("clzl", []) (#recursive_functions x),
         function_info = Symtab.update_new ("clzl", clzl_info) (#function_info x)
        };
in
  AutoCorresFunctionInfo.map (Symtab.update (file, fn_info'))
  #> AutoCorresData.add_def file "L1def" "clzl" @{thm kernel_all_substitute.l1_clzl'_def}
  #> AutoCorresData.add_def file "L2def" "clzl" @{thm kernel_all_substitute.l2_clzl'_def}
  #> AutoCorresData.add_def file "TSdef" "clzl" @{thm kernel_all_substitute.clzl'_def}
  #> AutoCorresData.add_thm file "L1corres" "clzl" @{thm kernel_all_substitute.l1_clzl'_corres}
  #> AutoCorresData.add_thm file "L2corres" "clzl" @{thm kernel_all_substitute.l2_clzl'_corres}
  #> AutoCorresData.add_thm file "TScorres" "clzl" @{thm kernel_all_substitute.clzl'_TScorres}
end
*}

text \<open>Now AutoCorres will use our manual specification in clzl calls.\<close>
autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = chooseThread,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "c/kernel_all.c_pp"

context kernel_m begin
thm clzl'_def chooseThread'_def
end



subsection \<open>Test recursion + call to previously translated (cap_get_capType)\<close>
autocorres
  [
   skip_heap_abs, skip_word_abs, ts_rules = nondet, (* for compatibility *)
   scope = cap_get_capType,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "c/kernel_all.c_pp"

thm kernel_all_substitute.cap_get_capType'_def
    kernel_all_substitute.cap_get_capType_body_def

autocorres
  [
   skip_heap_abs, skip_word_abs, ts_rules = nondet, (* for compatibility *)
   scope = cteDelete finaliseSlot reduceZombie,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "c/kernel_all.c_pp"

context kernel_m begin
thm cteDelete'.simps finaliseSlot'.simps reduceZombie'.simps
end




subsection \<open>Experiment with proving bitfield specs\<close>
autocorres
  [
   skip_heap_abs, skip_word_abs, ts_rules = nondet, (* for compatibility *)
   scope = cap_capType_equals
     cap_cnode_cap_get_capCNodePtr
     cap_cnode_cap_get_capCNodeGuard
     cap_cnode_cap_get_capCNodeRadix,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "c/kernel_all.c_pp"

thm kernel_all_substitute.cap_capType_equals_spec
thm kernel_all_substitute.cap_capType_equals'_def
    kernel_all_substitute.cap_capType_equals_body_def

lemma of_bl_from_cond:
  "(if C then 1 else 0) = of_bl [C]"
  by (simp add: word_1_bl)
lemma of_bl_cond:
  "(if C then of_bl [A] else of_bl [B]) = of_bl [if C then A else B]"
  by (rule if_f)

thm kernel_all_substitute.cap_get_capType'_def[
      simplified of_bl_from_cond of_bl_cond,
      folded cap_get_tag_def[simplified mask_def, simplified]]
thm kernel_all_substitute.cap_cnode_cap_get_capCNodePtr'_def
thm kernel_all_substitute.cap_cnode_cap_get_capCNodePtr_spec
thm cap_cnode_cap_lift_def cap_lift_def

context kernel_m begin
lemma "\<lbrace>\<lambda>_. cap_get_tag cap = scast cap_cnode_cap\<rbrace> cap_cnode_cap_get_capCNodePtr' cap \<lbrace>\<lambda>r _. r = capCNodePtr_CL (cap_cnode_cap_lift cap)\<rbrace>"
  apply (unfold cap_cnode_cap_get_capCNodePtr'_def)
  apply wp
  apply (simp add: cap_get_tag_def cap_cnode_cap_lift_def cap_lift_def cap_tag_values shiftr_over_and_dist)
  done

lemma "\<lbrace>\<lambda>_. cap_get_tag cap = scast cap_cnode_cap\<rbrace> cap_cnode_cap_get_capCNodeGuard' cap \<lbrace>\<lambda>r _. r = capCNodeGuard_CL (cap_cnode_cap_lift cap)\<rbrace>"
  apply (unfold cap_cnode_cap_get_capCNodeGuard'_def)
  apply wp
  apply (simp add: cap_get_tag_def cap_cnode_cap_lift_def cap_lift_def cap_tag_values shiftr_over_and_dist)
  done

lemma "\<lbrace>\<lambda>_. cap_get_tag cap = scast cap_cnode_cap\<rbrace> cap_cnode_cap_get_capCNodeRadix' cap \<lbrace>\<lambda>r _. r = capCNodeRadix_CL (cap_cnode_cap_lift cap)\<rbrace>"
  apply (unfold cap_cnode_cap_get_capCNodeRadix'_def)
  apply wp
  apply (simp add: cap_get_tag_def cap_cnode_cap_lift_def cap_lift_def cap_tag_values shiftr_over_and_dist)
  done

thm cap_cnode_cap_get_capCNodeRadix'_ac_corres
thm cap_cnode_cap_get_capCNodeRadix_spec
thm cap_cnode_cap_get_capCNodeRadix_modifies

end


subsection \<open>Experiment with transferring bitfield specs\<close>

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

context kernel_m begin

thm cap_zombie_cap_get_capZombiePtr_spec
lemma cap_zombie_cap_get_capZombiePtr'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<and> cap_get_tag cap = scast cap_zombie_cap \<and> get_capZombieBits_CL (cap_zombie_cap_lift cap) < 0x1F\<rbrace>
     cap_zombie_cap_get_capZombiePtr' cap
   \<lbrace>\<lambda>r s. s = s0 \<and> r = get_capZombiePtr_CL (cap_zombie_cap_lift cap)\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    thm autocorres_transfer_spec_no_modifies[OF
          cap_zombie_cap_get_capZombiePtr'_def cap_zombie_cap_get_capZombiePtr_spec]
    apply (rule autocorres_transfer_spec_no_modifies[OF
                  cap_zombie_cap_get_capZombiePtr'_def cap_zombie_cap_get_capZombiePtr_spec _ refl,
                  where cs="undefined\<lparr>globals := s0, cap_' := cap\<rparr>"])
      apply (rule cap_zombie_cap_get_capZombiePtr_modifies)
     apply auto
  done

thm cap_zombie_cap_get_capZombieType_spec
lemma cap_zombie_cap_get_capZombieType'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<and> cap_get_tag cap = scast cap_zombie_cap \<rbrace>
     cap_zombie_cap_get_capZombieType' cap
   \<lbrace>\<lambda>r s. s = s0 \<and> r = capZombieType_CL (cap_zombie_cap_lift cap)\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    thm autocorres_transfer_spec_no_modifies[OF
          cap_zombie_cap_get_capZombieType'_def cap_zombie_cap_get_capZombieType_spec]
    apply (rule autocorres_transfer_spec_no_modifies[OF
                  cap_zombie_cap_get_capZombieType'_def cap_zombie_cap_get_capZombieType_spec _ refl,
                  where cs="undefined\<lparr>globals := s0, cap_' := cap\<rparr>"])
      apply (rule cap_zombie_cap_get_capZombieType_modifies)
     apply auto
  done

text \<open>Helpers\<close>
lemma All_to_all':
  "(\<forall>x. P x) \<Longrightarrow> (\<And>x. P x)"
  by simp
text \<open>Convert references to global or local state variables, to the opposite one.
  FIXME: surely this has been proven already.\<close>
lemma collect_lift:
  "Collect (\<lambda>s. s0 = s \<and> f s) = Collect (\<lambda>s. s0 = s \<and> f s0)"
  by blast
lemma collect_unlift:
  "Collect (\<lambda>s. s0 = s \<and> f s0 s) = Collect (\<lambda>s. s0 = s \<and> f s s)"
  by blast

thm cap_zombie_cap_set_capZombieNumber_spec[THEN All_to_all']
lemma cap_zombie_cap_set_capZombieNumber'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<and> ccap_relation cap' cap \<and> isZombie cap' \<and> capAligned cap' \<and> unat n \<le> zombieCTEs (capZombieType cap')\<rbrace>
     cap_zombie_cap_set_capZombieNumber' cap n
   \<lbrace>\<lambda>r s. s = s0 \<and> ccap_relation (capZombieNumber_update (\<lambda>_. unat n) cap') r\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    thm autocorres_transfer_spec_no_modifies[OF
          cap_zombie_cap_set_capZombieNumber'_def cap_zombie_cap_set_capZombieNumber_spec[THEN All_to_all']]
    apply (rule autocorres_transfer_spec_no_modifies[OF
                  cap_zombie_cap_set_capZombieNumber'_def cap_zombie_cap_set_capZombieNumber_spec[THEN All_to_all'],
                  where cs="undefined\<lparr>globals := s0, cap_' := cap, n_' := n\<rparr>"])
      apply (rule cap_zombie_cap_set_capZombieNumber_modifies)
     apply (rule collect_unlift)
    apply auto
  done

thm cap_capType_equals_spec
lemma cap_capType_equals'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<rbrace>
     AC_call_L1 (\<lambda>s. cap_' s = cap \<and> cap_type_tag_' s = cap_type_tag) globals ret__int_'
       (L1_call_simpl check_termination \<Gamma> cap_capType_equals_'proc)
   \<lbrace>\<lambda>r s. s = s0 \<and> r = of_bl [cap_get_tag cap = cap_type_tag]\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    thm autocorres_transfer_spec_no_modifies[OF reflexive cap_capType_equals_spec]
    apply (rule autocorres_transfer_spec_no_modifies[
                  OF reflexive cap_capType_equals_spec,
                  where cs="undefined\<lparr>globals := s0, cap_' := cap, cap_type_tag_' := cap_type_tag\<rparr>"])
      apply (rule cap_capType_equals_modifies)
     apply auto
  done


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

thm clzl_body_def clzl_spec

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


end
