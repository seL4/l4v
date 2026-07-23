(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* The main abstract-to-design refinement theorem *)

theory Refine
imports
  KernelInit_R
  ArchADT_H
begin

arch_requalify_facts no_irq_getActiveIRQ (* FIXME arch-split: Machine_AI *)
arch_requalify_facts no_irq_modify (* FIXME arch-split: Machine_AI *)

lemmas [simp] =
  headM_tailM_Cons
  cart_singletons
  less_1_simp
  is_aligned_no_overflow
  maybe_fail_bind_fail

crunch setPriority
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (simp: crunch_simps)

locale Refine =
  assumes user_mem_relation:
    "\<And>s s'.
     \<lbrakk>(s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
     \<Longrightarrow> user_mem' s' = user_mem s"
  assumes device_mem_relation:
    "\<And>s s'.
     \<lbrakk>(s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
     \<Longrightarrow> device_mem' s' = device_mem s"
  assumes arch_activate_thread_sched_act:
    "\<And>t P.
     \<lbrace>ct_in_state activatable and (\<lambda>s. P (scheduler_action s))\<rbrace>
     arch_activate_idle_thread t
     \<lbrace>\<lambda>rs s. P (scheduler_action (s::det_state))\<rbrace>"
  assumes valid_list_init[simp]:
    "valid_list (init_A_st :: det_state)"
  assumes sched_act_init[simp]:
    "scheduler_action (init_A_st :: det_state) = resume_cur_thread"
  (* sched_act_init being in the simpset automatically expands this to a no-longer-abbreviated
     valid_sched_2 term we don't want to type out, but it's still used to simplify the proofs *)
  assumes valid_sched_init[simplified, simp]:
    "valid_sched (init_A_st :: det_state)"
  assumes valid_domain_list_init[simp]:
    "valid_domain_list (init_A_st :: det_state)"
  assumes valid_domain_time_init[simp]:
    "0 < domain_time (init_A_st :: det_state)"
  assumes fastpathKernelAssertions_cross:
    "\<And>s s'. \<lbrakk>(s,s') \<in> state_relation; invs s; valid_arch_state' s'\<rbrakk> \<Longrightarrow> fastpathKernelAssertions s'"
  assumes callKernel_valid_duplicates':
    "\<And>e.
     \<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
      (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)\<rbrace>
     callKernel e
     \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  assumes doUserOp_valid_duplicates':
    "\<And>f tc. doUserOp f tc \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  assumes checkActiveIRQ_valid_duplicates':
    "checkActiveIRQ \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  assumes tcb_hyp_refs'_atcbContextSet[simp]:
    "\<And>tc atcb. tcb_hyp_refs' (atcbContextSet tc atcb) = tcb_hyp_refs' atcb"
  assumes ptable_lift_abs_state[simp]:
    "\<And>t (s::det_state). ptable_lift t (abs_state s) = ptable_lift t s"
  assumes ptable_rights_abs_state[simp]:
    "\<And>t (s::det_state). ptable_rights t (abs_state s) = ptable_rights t s"
  assumes pointerInUserData_relation:
    "\<And>s s' p.
     \<lbrakk> (s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
     \<Longrightarrow> pointerInUserData p s' = in_user_frame p s"
  assumes pointerInDeviceData_relation:
    "\<And>s s' p.
     \<lbrakk> (s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
     \<Longrightarrow> pointerInDeviceData p s' = in_device_frame p s"
  assumes arch_tcb_relation_arch_context_set:
    "\<And>atcb atcb' tc.
     arch_tcb_relation atcb atcb'
     \<Longrightarrow> arch_tcb_relation (arch_tcb_context_set tc atcb) (atcbContextSet tc atcb')"
  assumes arch_tcb_relation_arch_context_get:
    "\<And>atcb atcb'.
     arch_tcb_relation atcb atcb' \<Longrightarrow> arch_tcb_context_get atcb = atcbContextGet atcb'"
begin

lemma absKState_correct:
  assumes invs: "einvs (s :: det_ext state)" and invs': "invs' s'"
  assumes rel: "(s,s') \<in> state_relation"
  shows "absKState s' = abs_state s"
  using assms
  apply (intro state.equality, simp_all add: absKState_def abs_state_def)
                  apply (rule absHeap_correct; clarsimp elim!: state_relationE)
                 apply (rule absCDT_correct; clarsimp)
                apply (rule absIsOriginalCap_correct; clarsimp)
               apply (simp add: state_relation_def)
              apply (simp add: state_relation_def)
             apply (clarsimp simp: state_relation_def)
             apply (rule absSchedulerAction_correct, simp add: state_relation_def)
            apply (simp add: domSchedule_map_relation)
           apply (simp add: state_relation_def)
          apply (simp add: state_relation_def)
         apply (simp add: state_relation_def)
        apply (simp add: state_relation_def)
       apply (simp add: state_relation_def ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
       apply (fastforce dest: heap_ls_is_walk)
      apply (clarsimp simp:  user_mem_relation invs_def invs'_def)
      apply (simp add: state_relation_def)
     apply (rule absInterruptIRQNode_correct, simp add: state_relation_def)
    apply (rule absInterruptStates_correct, simp add: state_relation_def)
   apply (rule absArchState_correct, simp)
  apply (rule absExst_correct; simp)
  done

end (* Refine *)

text \<open>The top-level invariance\<close>

lemma set_thread_state_sched_act:
  "\<lbrace>(\<lambda>s. runnable state) and (\<lambda>s. P (scheduler_action s))\<rbrace>
   set_thread_state thread state
   \<lbrace>\<lambda>rs s. P (scheduler_action (s::det_state))\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply wp
     apply (simp add: set_thread_state_act_def)
     apply wp
        apply (rule hoare_pre_cont)
       apply (rule_tac Q'="\<lambda>rv. (\<lambda>s. runnable ts) and (\<lambda>s. P (scheduler_action s))"
               in hoare_strengthen_post)
        apply wp
       apply force
      apply (wp gts_st_tcb_at)+
    apply (rule_tac Q'="\<lambda>rv. st_tcb_at ((=) state) thread
                             and (\<lambda>s. runnable state)
                             and (\<lambda>s. P (scheduler_action s))"
                 in hoare_strengthen_post)
     apply (simp add: st_tcb_at_def)
     apply (wp obj_set_prop_at)+
    apply (force simp: st_tcb_at_def obj_at_def)
   apply wp
  apply clarsimp
  done

lemma schedule_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> Schedule_A.schedule
  \<lbrace>\<lambda>rs (s::det_state). scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding Schedule_A.schedule_def
  by (wpsimp)

context Refine begin

lemma activate_thread_sched_act:
  "\<lbrace>ct_in_state activatable and (\<lambda>s. P (scheduler_action s))\<rbrace>
   activate_thread
   \<lbrace>\<lambda>rs s. P (scheduler_action (s::det_state))\<rbrace>"
  by (wpsimp simp: activate_thread_def set_thread_state_def
             wp: set_thread_state_sched_act gts_wp arch_activate_thread_sched_act)

lemma call_kernel_sched_act_rct[wp]:
  "\<lbrace>einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>rs (s::det_state). scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding call_kernel_def
  by (wpsimp wp: activate_thread_sched_act handle_spurious_irq_invs simp: active_from_running)

lemma kernel_entry_invs:
  "\<lbrace>einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
    and (\<lambda>s. 0 < domain_time s) and valid_domain_list and (ct_running or ct_idle)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
  kernel_entry e us
  \<lbrace>\<lambda>rv. einvs and (\<lambda>s. ct_running s \<or> ct_idle s)
    and (\<lambda>s. 0 < domain_time s) and valid_domain_list
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>"
  apply (rule_tac Q'="\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s) and valid_sched and
                           (\<lambda>s. 0 < domain_time s) and valid_domain_list and
                           valid_list and (\<lambda>s. scheduler_action s = resume_cur_thread)"
            in hoare_post_imp)
   apply clarsimp
  apply (simp add: kernel_entry_def)
  apply (wp akernel_invs_det_ext call_kernel_valid_sched thread_set_invs_trivial
            thread_set_not_state_valid_sched
            hoare_vcg_disj_lift ct_in_state_thread_state_lift thread_set_no_change_tcb_state
            call_kernel_domain_time_inv_det_ext call_kernel_domain_list_inv_det_ext
            hoare_weak_lift_imp valid_domain_list_lift
      | clarsimp simp add: tcb_cap_cases_def active_from_running)+
  done

end (* Refine *)

definition full_invs :: "(('user_context \<times> det_ext state) \<times> mode \<times> event option) set" where
  "full_invs \<equiv> {((tc, s :: det_ext state), m, e).
                 einvs s \<and>
                 (ct_running s \<or> ct_idle s) \<and>
                 (m = KernelMode \<longrightarrow> e \<noteq> None) \<and>
                 (m = UserMode \<longrightarrow> ct_running s) \<and>
                 (m = IdleMode \<longrightarrow> ct_idle s) \<and>
                 (e \<noteq> None \<and> e \<noteq> Some Interrupt \<longrightarrow> ct_running s) \<and>
                 0 < domain_time s \<and> valid_domain_list s \<and>
                 (scheduler_action s = resume_cur_thread)}"

crunch do_user_op
  for valid_list: valid_list
  and valid_sched: valid_sched
  and sched_act: "\<lambda>s. P (scheduler_action s)"
  and domain_fields_inv[wp]: "domain_fields P"

lemma do_user_op_invs2:
  "\<lbrace>einvs  and ct_running and (\<lambda>s. scheduler_action s = resume_cur_thread)
    and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>
   do_user_op f tc
   \<lbrace>\<lambda>_. (einvs  and ct_running and (\<lambda>s. scheduler_action s = resume_cur_thread))
        and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>"
  apply (rule_tac Q'="\<lambda>_. valid_list and valid_sched and
                          (\<lambda>s. scheduler_action s = resume_cur_thread) and (invs and ct_running) and
                          (\<lambda>s. 0 < domain_time s) and valid_domain_list"
                  in hoare_strengthen_post)
   apply (wpsimp wp: do_user_op_valid_list do_user_op_valid_sched do_user_op_sched_act
                     valid_domain_list_lift do_user_op_invs)
  apply force
  done

lemmas ext_init_def = ext_init_det_ext_ext_def ext_init_unit_def

lemma (in Refine) akernel_invariant:
  "ADT_A uop \<Turnstile> full_invs"
  unfolding full_invs_def
  apply (rule invariantI)
   apply (clarsimp simp: ADT_A_def subset_iff)
   apply (frule bspec[OF akernel_init_invs])
   apply (simp add: Let_def Init_A_def ext_init_def)
  apply (clarsimp simp: ADT_A_def global_automaton_def)
  apply (rename_tac tc' s' mode' e' tc s mode e)
  apply (elim disjE)
             apply ((clarsimp simp: kernel_call_A_def
                   | drule use_valid[OF _ kernel_entry_invs])+)[2]
           apply ((clarsimp simp: do_user_op_A_def monad_to_transition_def
                                  check_active_irq_A_def
                 | drule use_valid[OF _ do_user_op_invs2]
                 | drule use_valid[OF _ check_active_irq_invs_just_running])+)[2]
         apply ((clarsimp simp add: check_active_irq_A_def
               | drule use_valid[OF _ check_active_irq_invs])+)[1]
        apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
       apply ((clarsimp simp add: do_user_op_A_def check_active_irq_A_def
             | drule use_valid[OF _ do_user_op_invs2]
             | drule use_valid[OF _ check_active_irq_invs_just_running])+)[1]
      apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
     apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
    apply ((clarsimp simp add: check_active_irq_A_def
         | drule use_valid[OF _ check_active_irq_invs])+)[1]
   apply ((clarsimp simp add: check_active_irq_A_def
        | drule use_valid[OF _ check_active_irq_invs_just_idle])+)[1]
  apply ((clarsimp simp add: check_active_irq_A_def
        | drule use_valid[OF _ check_active_irq_invs])+)[1]
  done

lemma dmo_getActiveIRQ_notin_non_kernel_IRQs[wp]:
  "\<lbrace>\<top>\<rbrace> doMachineOp (getActiveIRQ True) \<lbrace>\<lambda>irq _. irq \<notin> Some ` non_kernel_IRQs\<rbrace>"
  by (wp dmo_lift' getActiveIRQ_neq_non_kernel)

lemma ckernel_invs:
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   callKernel e
   \<lbrace>\<lambda>rs. (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
    and (invs' and (ct_running' or ct_idle'))\<rbrace>"
  unfolding callKernel_def
  by (wpsimp wp: activate_invs' activate_sch_act schedule_sch
                 schedule_sch_act_simple he_invs' schedule_invs' hoare_vcg_if_lift3
                 hoare_drop_imp[where Q'="\<lambda>_. kernelExitAssertions"]
                 hoare_drop_imp[where Q'="\<lambda>rv _. rv = None"]
             simp: no_irq_getActiveIRQ
      | strengthen non_kernel_IRQs_strg)+

(* this is only needed for callKernel, where we have invs' on concrete side *)
lemma (in Refine) corres_cross_over_fastpathKernelAssertions:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> invs s; \<And>s'. Q s' \<Longrightarrow> invs' s';
     corres r P (Q and fastpathKernelAssertions) f g \<rbrakk> \<Longrightarrow>
   corres r P Q f g"
  by (rule corres_cross_over_guard[where Q="Q and fastpathKernelAssertions"])
     (fastforce elim: fastpathKernelAssertions_cross)+

defs kernelExitAssertions_def:
  "kernelExitAssertions s \<equiv> 0 < ksDomainTime s"

lemma callKernel_domain_time_left:
  "\<lbrace>\<top>\<rbrace> callKernel e \<lbrace>\<lambda>_ s. 0 < ksDomainTime s\<rbrace>"
  unfolding callKernel_def kernelExitAssertions_def by wpsimp

lemma doMachineOp_sch_act_simple[wp]:
  "doMachineOp f \<lbrace>sch_act_simple\<rbrace>"
  by (wp sch_act_simple_lift)

lemma device_update_invs':
  "doMachineOp (device_memory_update ds) \<lbrace>invs'\<rbrace>"
  apply (simp add: doMachineOp_def device_memory_update_def simpler_modify_def select_f_def
                   gets_def get_def bind_def valid_def return_def)
  by (clarsimp simp: invs'_def valid_state'_def valid_irq_states'_def valid_machine_state'_def)

crunch doMachineOp
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"

context Refine begin

lemma kernelEntry_invs':
  "\<lbrace> invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and
           (ct_running' or ct_idle') and
           (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
           (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
           (\<lambda>s. 0 < ksDomainTime s) \<rbrace>
  kernelEntry e tc
  \<lbrace>\<lambda>rs. (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
         (invs' and (ct_running' or ct_idle')) and
         (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
         (\<lambda>s. 0 < ksDomainTime s) \<rbrace>"
  apply (simp add: kernelEntry_def)
  apply (wp ckernel_invs callKernel_domain_time_left callKernel_valid_duplicates'
            threadSet_invs_trivial threadSet_ct_running'
            TcbAcc_R.dmo_invs' hoare_weak_lift_imp
            doMachineOp_ct_in_state' doMachineOp_sch_act_simple
            callKernel_domain_time_left
         | clarsimp simp: user_memory_update_def no_irq_def tcb_at_invs')+
  done

lemma ptable_rights_imp_UserData:
  assumes invs: "einvs s" and invs': "invs' s'"
  assumes rel: "(s,s') : state_relation"
  assumes rights: "ptable_rights t (absKState s') x \<noteq> {}"
  assumes trans:
    "ptable_lift t (absKState s') x = Some (addrFromPPtr y)"
  shows "pointerInUserData y s' \<or> pointerInDeviceData y s'"
proof -
  from invs invs' rel have [simp]: "absKState s' = abs_state s"
    by - (rule absKState_correct, simp_all)
  from invs have valid: "valid_state s" by auto
  from invs' have valid': "valid_state' s'" by auto
  have "in_user_frame y s \<or> in_device_frame y s "
    by (rule ptable_rights_imp_frame[OF valid rights[simplified] trans[simplified]])
  thus ?thesis
   by (auto simp add: pointerInUserData_relation[OF rel valid' valid]
     pointerInDeviceData_relation[OF rel valid' valid])
qed

lemma doUserOp_invs':
  "\<lbrace>invs' and ex_abs einvs and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running' and
    (\<lambda>s. 0 < ksDomainTime s)\<rbrace>
   doUserOp f tc
   \<lbrace>\<lambda>_. invs' and
        (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running' and
        (\<lambda>s. 0 < ksDomainTime s)\<rbrace>"
  apply (simp add: doUserOp_def split_def ex_abs_def)
  apply (wp device_update_invs' doMachineOp_ct_in_state'
    | (wp (once) dmo_invs', wpsimp simp: no_irq_modify device_memory_update_def
                                         user_memory_update_def))+
  apply (clarsimp simp: user_memory_update_def simpler_modify_def
                        restrict_map_def
                 split: option.splits)
  apply (frule ptable_rights_imp_UserData[rotated 2], auto)
  done

end (* Refine *)

text \<open>The top-level correspondence\<close>

lemma None_drop:
  "P \<Longrightarrow> x = None \<longrightarrow> P"
  by simp

lemma contract_all_imp_strg':
  "P \<and> P' \<and> P'' \<and> (\<forall>x. R x \<longrightarrow> Q x) \<Longrightarrow> \<forall>x. R x \<longrightarrow> P \<and> Q x \<and> P' \<and> P''"
  by blast

lemma kernel_corres':
  "corres dc (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
               and (\<lambda>s. scheduler_action s = resume_cur_thread) and valid_domain_list)
             (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle') and
              (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
              (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
             (call_kernel event)
             (do _ \<leftarrow> runExceptT $
                      handleEvent event `~catchError~`
                        (\<lambda>_. withoutPreemption $ maybeHandleInterrupt True);
                 _ \<leftarrow> ThreadDecls_H.schedule;
                 activateThread
              od)"
  unfolding call_kernel_def
  apply (corres corres: handleEvent_corres corres_machine_op maybeHandleInterrupt_corres
         | corres_cases_both)+
        apply (wpsimp wp: handle_event_valid_sched)+
      apply (corres corres: schedule_corres activateThread_corres)
      apply (wpsimp wp: schedule_invs' hoare_vcg_if_lift2 dmo_getActiveIRQ_non_kernel
                        handle_spurious_irq_invs
                        valid_domain_list_lift[of handle_spurious_irq]
                        valid_domain_list_lift[of "handle_interrupt irq" for irq]
                        valid_domain_list_lift[of "do_machine_op mop" for mop]
             | simp add: maybe_handle_interrupt_def cong: rev_conj_cong
             | strengthen None_drop contract_all_imp_strg')+
     apply (rule_tac Q'="\<lambda>_. valid_domain_list and valid_sched and invs and valid_list" and
                     E'="\<lambda>_. valid_domain_list and valid_sched and invs and valid_list"
                     in hoare_strengthen_postE)
       apply (wpsimp wp: handle_event_valid_sched handle_event_domain_list_inv)
      apply simp
     apply simp
    apply (wpsimp | strengthen non_kernel_IRQs_strg None_drop)+
   apply (clarsimp simp: active_from_running schact_is_rct_def)
  apply (clarsimp simp: active_from_running')
  done

lemma corres_gets_machine_state:
  "corres (=) \<top> \<top> (gets (f \<circ> machine_state)) (gets (f \<circ> ksMachineState))"
  by (clarsimp simp: gets_def corres_underlying_def
                     in_monad bind_def get_def return_def state_relation_def)

context Refine begin

lemma kernel_corres:
  "corres dc (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle) and
              (\<lambda>s. scheduler_action s = resume_cur_thread) and
              (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s))
             (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle') and
              (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
              (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
             (call_kernel event) (callKernel event)"
  unfolding callKernel_def K_bind_def
  apply (rule corres_cross_over_fastpathKernelAssertions, blast+)
  apply (rule corres_stateAssert_r)
  apply (rule corres_guard_imp)
    apply (rule corres_add_noop_lhs2)
    apply (simp only: bind_assoc[symmetric])
    apply (rule corres_split[where r'=dc and
                                   R="\<lambda>_ s. 0 < domain_time s \<and> valid_domain_list s" and
                                   R'="\<lambda>_. \<top>"])
       apply (simp only: bind_assoc)
       apply (rule kernel_corres')
      apply (rule corres_bind_return2, rule corres_stateAssert_assume_stronger)
       apply simp
      apply (simp add: kernelExitAssertions_def state_relation_def)
     apply (wp call_kernel_domain_time_inv_det_ext call_kernel_domain_list_inv_det_ext)
    apply wp
   apply clarsimp
  apply clarsimp
  done

lemma user_mem_corres:
  "corres (=) invs invs' (gets (\<lambda>x. g (user_mem x))) (gets (\<lambda>x. g (user_mem' x)))"
  by (clarsimp simp add: gets_def get_def return_def bind_def
                         invs_def invs'_def
                         corres_underlying_def user_mem_relation)

lemma device_mem_corres:
  "corres (=) invs invs' (gets (\<lambda>x. g (device_mem x))) (gets (\<lambda>x. g (device_mem' x)))"
  by (clarsimp simp add: gets_def get_def return_def bind_def
                         invs_def invs'_def
                         corres_underlying_def device_mem_relation)

lemma entry_corres:
  "corres (=) (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and
                  (\<lambda>s. 0 < domain_time s) and valid_domain_list and (ct_running or ct_idle) and
                  (\<lambda>s. scheduler_action s = resume_cur_thread))
                 (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and
                  (\<lambda>s. 0 < ksDomainTime s) and (ct_running' or ct_idle') and
                  (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
                  (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
          (kernel_entry event tc) (kernelEntry event tc)"
  apply (simp add: kernel_entry_def kernelEntry_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split)
         apply simp
         apply (rule threadset_corresT; simp?)
           apply (clarsimp simp: tcb_relation_def arch_tcb_relation_arch_context_set)
          apply (clarsimp simp: tcb_cap_cases_def tcb_cte_cases_neqs)
         apply (clarsimp simp: tcb_cap_cases_def tcb_cte_cases_def tcb_cte_cases_neqs)
        apply (rule corres_split[OF kernel_corres])
          apply (rule corres_split_eqr[OF getCurThread_corres])
            apply (rule threadGet_corres)
            apply (clarsimp simp add: tcb_relation_def arch_tcb_relation_arch_context_get)
           apply wp+
         apply (rule hoare_strengthen_post, rule akernel_invs_det_ext,
                simp add: invs_def valid_state_def valid_pspace_def cur_tcb_def)
        apply (rule hoare_strengthen_post, rule ckernel_invs, simp add: invs'_def cur_tcb'_def)
       apply (wp thread_set_invs_trivial
                 threadSet_invs_trivial threadSet_ct_running'
                 thread_set_not_state_valid_sched hoare_weak_lift_imp
                 hoare_vcg_disj_lift ct_in_state_thread_state_lift
                 thread_set_no_change_tcb_state
              | simp add: tcb_cap_cases_def ct_in_state'_def schact_is_rct_def
              | (wps, wp threadSet_st_tcb_at2) )+
   apply (clarsimp simp: invs_def cur_tcb_def valid_state_def valid_pspace_def)
  apply (clarsimp simp: ct_in_state'_def)
  done

lemma do_user_op_corres:
  "corres (=) (einvs and ct_running)
                 (invs' and (%s. ksSchedulerAction s = ResumeCurrentThread) and
                  ct_running')
          (do_user_op f tc) (doUserOp f tc)"
  apply (simp add: do_user_op_def doUserOp_def split_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule_tac r'="(=)" and P=einvs and P'=invs' in corres_split)
         apply (fastforce dest: absKState_correct [rotated])
        apply (rule_tac r'="(=)" and P=einvs and P'=invs' in corres_split)
           apply (fastforce dest: absKState_correct [rotated])
          apply (rule_tac r'="(=)" and P=invs and P'=invs' in corres_split)
             apply (rule user_mem_corres)
            apply (rule_tac r'="(=)" and P=invs and P'=invs' in corres_split)
               apply (rule device_mem_corres)
              apply (rule_tac r'="(=)" in corres_split)
                 apply (rule corres_gets_machine_state)
                apply (rule_tac F = "dom (rvb \<circ> addrFromPPtr)  \<subseteq> - dom rvd" in corres_gen_asm)
                apply (rule_tac F = "dom (rvc \<circ> addrFromPPtr)  \<subseteq> dom rvd" in corres_gen_asm)
                apply simp
                apply (rule_tac r'="(=)" in corres_split[OF corres_select])
                   apply simp
                  apply (rule corres_underlying_split[OF corres_machine_op])
                     apply simp
                     apply (rule corres_underlying_trivial)
                     apply (simp add: user_memory_update_def)
                     apply (wp | simp)+
                    apply (rule corres_underlying_split[OF corres_machine_op,where Q = dc and Q'=dc])
                       apply (rule corres_underlying_trivial)
                       apply (wp | simp add: dc_def device_memory_update_def)+
   apply (clarsimp simp: invs_def valid_state_def pspace_respects_device_region_def
                         ptrFormPAddr_addFromPPtr)
  apply fastforce
  done

end (* Refine *)

lemma ct_running_related:
  "\<lbrakk> (a, c) \<in> state_relation; ct_running' c \<rbrakk>
     \<Longrightarrow> ct_running a"
  apply (clarsimp simp: ct_in_state_def ct_in_state'_def
                        curthread_relation)
  apply (frule(1) st_tcb_at_coerce_abstract)
  apply (erule st_tcb_weakenE)
  apply (case_tac st, simp_all)[1]
  done

lemma ct_idle_related:
  "\<lbrakk> (a, c) \<in> state_relation; ct_idle' c \<rbrakk>
     \<Longrightarrow> ct_idle a"
  apply (clarsimp simp: ct_in_state_def ct_in_state'_def
                        curthread_relation)
  apply (frule(1) st_tcb_at_coerce_abstract)
  apply (erule st_tcb_weakenE)
  apply (case_tac st, simp_all)[1]
  done

definition full_invs' :: "(('user_context \<times> global.kernel_state) \<times> mode \<times> event option) set" where
  "full_invs' \<equiv> {((tc,s),m,e).
                  invs' s \<and> vs_valid_duplicates' (ksPSpace s) \<and>
                  ex_abs (einvs::det_ext state \<Rightarrow> bool) s \<and>
                  ksSchedulerAction s = ResumeCurrentThread \<and>
                  (ct_running' s \<or> ct_idle' s) \<and>
                  (m = KernelMode \<longrightarrow> e \<noteq> None) \<and>
                  (m = UserMode \<longrightarrow> ct_running' s) \<and>
                  (m = IdleMode \<longrightarrow> ct_idle' s) \<and>
                  (e \<noteq> None \<and> e \<noteq> Some Interrupt \<longrightarrow> ct_running' s) \<and>
                  0 < ksDomainTime s}"

lemma check_active_irq_corres':
  "corres (=) \<top> \<top> (check_active_irq) (checkActiveIRQ)"
  by (simp add: check_active_irq_def checkActiveIRQ_def)
     corres

lemma check_active_irq_corres:
  "corres (=)
    (invs and (ct_running or ct_idle) and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
     and (\<lambda>s. 0 < domain_time s) and valid_domain_list)
    (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
      and (\<lambda>s. 0 < ksDomainTime s) and (ct_running' or ct_idle'))
    (check_active_irq) (checkActiveIRQ)"
  by (corres corres: check_active_irq_corres')

lemma checkActiveIRQ_just_running_corres:
  "corres (=)
    (invs and ct_running and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and (\<lambda>s. 0 < domain_time s) and valid_domain_list)
    (invs' and ct_running'
      and (\<lambda>s. 0 < ksDomainTime s)
      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
    (check_active_irq) (checkActiveIRQ)"
  by (corres corres: check_active_irq_corres')

lemma checkActiveIRQ_just_idle_corres:
  "corres (=)
    (invs and ct_idle and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and (\<lambda>s. 0 < domain_time s)  and valid_domain_list)
    (invs' and ct_idle'
      and (\<lambda>s. 0 < ksDomainTime s)
      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
    (check_active_irq) (checkActiveIRQ)"
  by (corres corres: check_active_irq_corres')

lemma checkActiveIRQ_invs':
  "\<lbrace>invs' and ex_abs invs and (ct_running' or ct_idle')
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   checkActiveIRQ
   \<lbrace>\<lambda>_. invs' and (ct_running' or ct_idle') and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>"
  by (simp add: checkActiveIRQ_def ex_abs_def)
     (wpsimp wp: dmo_invs')

lemma checkActiveIRQ_invs'_just_running:
  "\<lbrace>invs' and ex_abs invs and ct_running' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   checkActiveIRQ
   \<lbrace>\<lambda>_. invs' and ct_running' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>"
  by (wpsimp simp: checkActiveIRQ_def)

lemma checkActiveIRQ_invs'_just_idle:
  "\<lbrace>invs' and ex_abs invs and ct_idle' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   checkActiveIRQ
   \<lbrace>\<lambda>_. invs' and ct_idle' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>"
  by (wpsimp simp: checkActiveIRQ_def)

lemma sched_act_rct_related:
  "\<lbrakk> (a, c) \<in> state_relation; ksSchedulerAction c = ResumeCurrentThread\<rbrakk>
   \<Longrightarrow> scheduler_action a = resume_cur_thread"
  by (case_tac "scheduler_action a", simp_all add: state_relation_def)

lemma domain_time_rel_eq:
  "(a, c) \<in> state_relation \<Longrightarrow> P (ksDomainTime c) = P (domain_time a)"
  by (clarsimp simp: state_relation_def)

crunch doUserOp, checkActiveIRQ
  for valid_objs': valid_objs'
  (wp: crunch_wps
   rule: doUserOp_def) (* FIXME: crunch can't find the rule of locale-defined constant *)

lemma valid_domain_list_2_cross:
  "\<lbrakk>valid_dom_schedule'_2 sched idx start; domain_list_map dom_list = sched \<rbrakk>
   \<Longrightarrow> valid_domain_list_2 start idx dom_list"
  by (fastforce simp: valid_domain_list_2_def valid_dom_schedule'_2_def ucast_eq_0 is_up
                split: prod.splits)

lemma valid_domain_list_from_invs':
  "\<lbrakk> (s, s') \<in> state_relation; invs' s' \<rbrakk> \<Longrightarrow> valid_domain_list s"
  by (clarsimp simp: valid_domain_list_2_cross invs'_def valid_state'_def elim!: state_relationE)

context Refine begin

lemma ckernel_invariant:
  "ADT_H uop \<Turnstile> full_invs'"
  unfolding full_invs'_def
  supply word_neq_0_conv[simp]
  supply domain_time_rel_eq[simp]
  apply (rule invariantI)
   apply (clarsimp simp add: ADT_H_def)
   apply (subst conj_commute, simp)
   apply (rule conjI)
    apply (drule ckernel_init_valid_duplicates'[rule_format], simp)
   apply (rule conjI)
    apply (frule init_refinement[simplified subset_eq, THEN bspec])
    apply (clarsimp simp: ex_abs_def lift_state_relation_def)
    apply (frule akernel_init_invs[THEN bspec])
    apply (rule_tac x=s in exI)
    apply (clarsimp simp: Init_A_def)
   apply (insert ckernel_init_invs)[1]
   apply clarsimp
   apply (frule ckernel_init_sch_norm)
   apply (frule ckernel_init_ctr)
   apply (frule ckernel_init_domain_time)
   apply (frule ckernel_init_domain_list)
   apply (fastforce simp: Init_H_def)
  apply (clarsimp simp: ADT_A_def ADT_H_def global_automaton_def)
  apply (erule_tac P="a \<and> (\<exists>x. b x)" for a b in disjE)
  apply (clarsimp simp: kernel_call_H_def)
   apply (drule use_valid[OF _ valid_corres_combined
                            [OF kernel_entry_invs entry_corres],
                            OF _ kernelEntry_invs'[THEN hoare_weaken_pre]])
     apply fastforce
    apply (clarsimp simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                           sched_act_rct_related)
    apply (rule exI, rule conjI, assumption)
    apply simp
    apply (fastforce simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                           sched_act_rct_related valid_domain_list_from_invs')
   apply (clarsimp simp: kernel_call_H_def)
   apply (fastforce simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                          sched_act_rct_related)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp add: do_user_op_H_def monad_to_transition_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_duplicates')
     apply (rule valid_corres_combined[OF do_user_op_invs2 corres_guard_imp2[OF do_user_op_corres]])
      apply clarsimp
     apply (rule doUserOp_invs'[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (clarsimp simp: invs_valid_objs' ex_abs_def, rule_tac x=s in exI,
            clarsimp simp: ct_running_related sched_act_rct_related valid_domain_list_from_invs')
   apply (clarsimp simp: ex_abs_def)
   apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related)

  apply (erule_tac P="a \<and> b \<and> c \<and> (\<exists>x. d x)" for a b c d in disjE)
   apply (clarsimp simp add: do_user_op_H_def monad_to_transition_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_duplicates')
     apply (rule valid_corres_combined[OF do_user_op_invs2 corres_guard_imp2[OF do_user_op_corres]])
      apply clarsimp
     apply (rule doUserOp_invs'[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related
                           valid_domain_list_from_invs')
   apply (fastforce simp: ex_abs_def)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp: check_active_irq_H_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_duplicates')
     apply (rule valid_corres_combined[OF check_active_irq_invs_just_running checkActiveIRQ_just_running_corres])
     apply (rule checkActiveIRQ_invs'_just_running[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related
                           valid_domain_list_from_invs')
   apply (fastforce simp: ex_abs_def)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp: check_active_irq_H_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_objs')
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_duplicates')
     apply (rule valid_corres_combined[OF check_active_irq_invs_just_idle checkActiveIRQ_just_idle_corres])
     apply (rule checkActiveIRQ_invs'_just_idle[THEN hoare_weaken_pre])
     apply clarsimp
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_idle_related sched_act_rct_related
                           valid_domain_list_from_invs')
   apply (fastforce simp: ex_abs_def)

  apply (clarsimp simp: check_active_irq_H_def)
  apply (drule use_valid)
    apply (rule hoare_vcg_conj_lift)
     apply (rule checkActiveIRQ_valid_objs')
    apply (rule hoare_vcg_conj_lift)
     apply (rule checkActiveIRQ_valid_duplicates')
    apply (rule valid_corres_combined[OF check_active_irq_invs check_active_irq_corres])
    apply (rule checkActiveIRQ_invs'[THEN hoare_weaken_pre])
    apply clarsimp
    apply (fastforce simp: ex_abs_def)
   apply (fastforce simp: ex_abs_def ct_running_related ct_idle_related sched_act_rct_related
                          valid_domain_list_from_invs')
  apply (fastforce simp: ex_abs_def)
  done

text \<open>The top-level theorem\<close>

lemma fw_sim_A_H:
  "LI (ADT_A uop)
      (ADT_H uop)
      (lift_state_relation state_relation)
      (full_invs \<times> full_invs')"
  apply (unfold LI_def full_invs_def full_invs'_def)
  apply (simp add: ADT_H_def ADT_A_def)
  apply (intro conjI)
    apply (rule init_refinement)
   apply (clarsimp simp: rel_semi_def relcomp_unfold in_lift_state_relation_eq)
   apply (rename_tac tc ak m ev tc' ck' m' ev' ck)
   apply (simp add: global_automaton_def)

   apply (erule_tac P="a \<and> (\<exists>x. b x)" for a b in disjE)
    apply (clarsimp simp add: kernel_call_H_def kernel_call_A_def)
    apply (rule rev_mp, rule_tac tc=tc and event=x in entry_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: sch_act_simple_def)
    apply (drule (1) bspec)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (rule_tac x=b in exI)
     apply (rule conjI)
      apply (rule impI, simp)
     apply (frule (2) ct_running_related)
    apply clarsimp
    apply (rule_tac x=b in exI)
    apply (drule use_valid, rule kernelEntry_invs')
     apply (simp add: sch_act_simple_def)
    apply clarsimp
    apply (frule (1) ct_idle_related)
    apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: do_user_op_H_def do_user_op_A_def monad_to_transition_def)
    apply (rule rev_mp, rule_tac tc1=tc and f1=uop and P="ct_running and einvs" in corres_guard_imp2[OF do_user_op_corres])
     apply simp
    apply (clarsimp simp add: corres_underlying_def)
    apply (drule (1) bspec, clarsimp)
    apply (drule (1) bspec, clarsimp)
    apply fastforce

   apply (erule_tac P="a \<and> b \<and> c \<and> (\<exists>x. d x)" for a b c d in disjE)
    apply (clarsimp simp: do_user_op_H_def do_user_op_A_def monad_to_transition_def)
    apply (rule rev_mp, rule_tac tc1=tc and f1=uop and P="ct_running and einvs" in corres_guard_imp2[OF do_user_op_corres])
     apply simp
    apply (clarsimp simp add: corres_underlying_def)
    apply (drule (1) bspec, clarsimp)
    apply (drule (1) bspec, clarsimp)
    apply fastforce

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
    apply (rule rev_mp, rule check_active_irq_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply fastforce

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
    apply (rule rev_mp, rule check_active_irq_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply fastforce

   apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
   apply (rule rev_mp, rule check_active_irq_corres)
   apply (clarsimp simp: corres_underlying_def)
    apply fastforce

  apply (clarsimp simp: absKState_correct dest!: lift_state_relationD)
  done

theorem refinement:
  "ADT_H uop \<sqsubseteq> ADT_A uop"
  apply (rule sim_imp_refines)
  apply (rule L_invariantI)
    apply (rule akernel_invariant)
   apply (rule ckernel_invariant)
  apply (rule fw_sim_A_H)
  done

end (* Refine *)

end
