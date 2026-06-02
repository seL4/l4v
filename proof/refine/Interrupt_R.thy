(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Refinement for interrupt controller operations *)

theory Interrupt_R
imports ArchIpc_R Invocations_R
begin

arch_requalify_consts (H) handleReservedIRQ checkIRQ

arch_requalify_facts no_fail_ackInterrupt no_fail_resetTimer (* FIXME arch-split: Machine_AI *)
lemmas [wp,simp] = no_fail_resetTimer no_fail_ackInterrupt

arch_requalify_facts (* FIXME arch-split: Machine_AI *)
  no_irq_resetTimer no_irq_ackInterrupt
  resetTimer_underlying_memory_inv ackInterrupt_underlying_memory_inv

arch_requalify_facts dmo_maskInterrupt_True (* FIXME arch-split: ArchMachine_R *)

arch_requalify_facts is_simple_cap_arch (* FIXME arch-split: CSpaceInv_AI *)

(* FIXME: move to Lib *)
lemma imp_not_concl_imp:
  "((P \<longrightarrow> Q) \<longrightarrow> \<not> Q \<longrightarrow> R) = (\<not>P \<and> \<not>Q \<longrightarrow> R)"
  by blast

(* FIXME: move *)
method do_machine_op_corres
  = (rule corres_machine_op, rule corres_Id, rule refl, simp, wp)

(* FIXME arch-split: move *)
lemmas corres_eq_trivial = corres_Id[where f = h and g = h for h, simplified]

crunch setIRQState
  for valid_cap'[wp]: "valid_cap' cap"
  and valid_mdb'[wp]: "valid_mdb'"

crunch set_irq_state
  for valid_arch_state[wp]: valid_arch_state

(* disambiguate name clash between Arch and non-arch definitions with same names *)
(* FIXME arch-split: consider moving closer to invariant lemmas? *)
context Arch begin

lemmas [crunch_def] = decodeIRQControlInvocation_def performIRQControl_def

context begin global_naming global

requalify_types (aliasing)
  Invocations_H.irqcontrol_invocation

requalify_facts (aliasing)
  Interrupt_H.decodeIRQControlInvocation_def
  Interrupt_H.performIRQControl_def

end
end (* Arch *)

primrec irq_handler_inv_relation ::
  "irq_handler_invocation \<Rightarrow> irqhandler_invocation \<Rightarrow> bool"
  where
  "irq_handler_inv_relation (Invocations_A.ACKIrq irq) x = (x = AckIRQ irq)"
| "irq_handler_inv_relation (Invocations_A.ClearIRQHandler irq) x = (x = ClearIRQHandler irq)"
| "irq_handler_inv_relation (Invocations_A.SetIRQHandler irq cap ptr) x =
       (\<exists>cap'. x = SetIRQHandler irq cap' (cte_map ptr) \<and> cap_relation cap cap')"

lemma decodeIRQHandlerInvocation_corres:
  "\<lbrakk> list_all2 cap_relation (map fst caps) (map fst caps');
    list_all2 (\<lambda>p pa. snd pa = cte_map (snd p)) caps caps' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> irq_handler_inv_relation) invs invs'
     (decode_irq_handler_invocation label irq caps)
     (decodeIRQHandlerInvocation label irq caps')"
  apply (simp add: decode_irq_handler_invocation_def decodeIRQHandlerInvocation_def)
  apply (cases caps)
   apply (simp add: returnOk_def
               split: invocation_label.split gen_invocation_labels.split list.splits)
  apply (clarsimp simp: list_all2_Cons1)
  apply (simp add: returnOk_def split: invocation_label.split gen_invocation_labels.split list.splits)
  apply (frule is_ntfn_cap_relation)
  apply (auto simp: returnOk_def is_cap_simps gen_isCap_simps split: capability.splits split: bool.splits)
  done

lemma is_irq_active_corres:
  "corres (=) \<top> \<top> (is_irq_active irq) (isIRQActive irq)"
  apply (simp add: is_irq_active_def isIRQActive_def get_irq_state_def
                   getIRQState_def getInterruptState_def)
  apply (clarsimp simp: state_relation_def interrupt_state_relation_def)
  apply (drule_tac x=irq in spec)+
  apply (simp add: irq_state_relation_def
            split: irqstate.split_asm irq_state.split_asm)
  done

crunch isIRQActive
  for inv: "P"

lemma isIRQActive_wp:
  "\<lbrace>\<lambda>s. \<forall>rv. (irq_issued' irq s \<longrightarrow> rv) \<longrightarrow> Q rv s\<rbrace> isIRQActive irq \<lbrace>Q\<rbrace>"
  apply (simp add: isIRQActive_def getIRQState_def
                   getInterruptState_def)
  apply wp
  apply (clarsimp simp: irq_issued'_def)
  done

lemma whenE_rangeCheck_eq:
  "(rangeCheck (x :: 'a :: {linorder, integral}) y z) =
    (whenE (x < fromIntegral y \<or> fromIntegral z < x)
      (throwError (RangeError (fromIntegral y) (fromIntegral z))))"
  by (simp add: rangeCheck_def unlessE_whenE linorder_not_le[symmetric])

crunch decodeIRQHandlerInvocation
  for inv[wp]: "P"
  (simp: crunch_simps)

lemma irqhandler_simp[simp]:
  "gen_invocation_type label \<noteq> IRQIssueIRQHandler \<Longrightarrow>
   (case gen_invocation_type label of IRQIssueIRQHandler \<Rightarrow> b | _ \<Rightarrow> c) = c"
  by (clarsimp split: gen_invocation_labels.splits)

lemma cteDeleteOne_ex_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_wp_to' P p\<rbrace> cteDeleteOne ptr \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF cteDeleteOne_irq_node'])
   apply (wp hoare_vcg_ex_lift cteDeleteOne_cte_wp_at_preserved)
   apply (case_tac cap, simp_all add: finaliseCap_def gen_isCap_simps)
  done

lemma cteDeleteOne_other_cap:
  "\<lbrace>(\<lambda>s. cte_wp_at' (P o cteCap) p s) and K (p \<noteq> p')\<rbrace>
     cteDeleteOne p'
   \<lbrace>\<lambda>rv s. cte_wp_at' (P o cteCap) p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: tree_cte_cteCap_eq)
  apply (wp cteDeleteOne_cteCaps_of)
  apply simp
  done

lemma isnt_irq_handler_strg:
  "(\<not> isIRQHandlerCap cap) \<longrightarrow> (\<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> P irq)"
  by (clarsimp simp: gen_isCap_simps)

lemma doMachineOp_maskInterrupt_False[wp]:
  "\<lbrace> \<lambda>s. invs' s \<and> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive \<rbrace>
   doMachineOp (maskInterrupt False irq)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (simp add: valid_irq_masks'_def valid_machine_state'_def
                   ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma setIRQState_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setIRQState st irq \<lbrace>\<lambda>_. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: setIRQState_def doMachineOp_def
                   split_def setInterruptState_def getInterruptState_def)
  apply wp
  apply (clarsimp simp: ex_cte_cap_to'_def)
  done

lemma setIRQState_issued[wp]:
  "\<lbrace>K (st = IRQSignal)\<rbrace> setIRQState st irq \<lbrace>\<lambda>rv. irq_issued' irq\<rbrace>"
  apply (simp add: setIRQState_def irq_issued'_def setInterruptState_def
                   getInterruptState_def)
  apply wp
  apply clarsimp
  done

lemma getIRQState_corres:
  "corres irq_state_relation \<top> \<top>
       (get_irq_state irq) (getIRQState irq)"
  apply (simp add: get_irq_state_def getIRQState_def getInterruptState_def)
  apply (clarsimp simp: state_relation_def interrupt_state_relation_def)
  done

lemma decDomainTime_corres:
  "corres dc \<top> \<top> dec_domain_time decDomainTime"
  by (simp add:dec_domain_time_def corres_underlying_def decDomainTime_def simpler_modify_def)
     (clarsimp simp: state_relation_def cdt_relation_def)

lemma thread_state_case_if:
 "(case state of Structures_A.thread_state.Running \<Rightarrow> f | _ \<Rightarrow> g) =
  (if state = Structures_A.thread_state.Running then f else g)"
  by (case_tac state, auto)

lemma threadState_case_if:
 "(case state of Structures_H.thread_state.Running \<Rightarrow> f | _ \<Rightarrow> g) =
  (if state = Structures_H.thread_state.Running then f else g)"
  by (case_tac state, auto)

lemma ready_qs_distinct_domain_time_update[simp]:
  "ready_qs_distinct (domain_time_update f s) = ready_qs_distinct s"
  by (clarsimp simp: ready_qs_distinct_def)

lemma timerTick_corres:
  "corres dc
     (cur_tcb and valid_sched and pspace_aligned and pspace_distinct) invs'
     timer_tick timerTick"
  supply if_cong[cong]
  apply (simp add: timerTick_def timer_tick_def)
  apply (simp add: thread_state_case_if threadState_case_if)
  apply (rule_tac Q="cur_tcb and valid_sched and pspace_aligned and pspace_distinct"
              and Q'=invs'
               in corres_guard_imp)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF getCurThread_corres])
        apply simp
        apply (rule corres_split[OF getThreadState_corres])
          apply (rename_tac state state')
          apply (rule corres_split[where r' = dc])
             apply (rule corres_if[where Q = \<top> and Q' = \<top>])
               apply (case_tac state,simp_all)[1]
              apply (rule_tac r'="(=)" in corres_split[OF threadGet_corres])
                 apply (simp add: tcb_relation_def)
                apply (rename_tac ts ts')
                apply (rule_tac R="1 < ts" in corres_cases)
                 apply (simp)
                 apply (unfold thread_set_time_slice_def)
                 apply (rule threadset_corres; simp add: tcb_relation_def inQ_def)
                apply simp
                apply (rule corres_split[OF threadset_corres])
                                apply (simp add: sch_act_wf_weak tcb_relation_def pred_conj_def inQ_def)+
                  apply (rule corres_split[OF tcbSchedAppend_corres], simp)
                    apply (rule rescheduleRequired_corres)
                   apply wp
                  apply ((wpsimp wp: tcbSchedAppend_sym_heap_sched_pointers
                                     tcbSchedAppend_valid_objs'
                          | strengthen valid_objs'_valid_tcbs')+)[1]
                 apply ((wpsimp wp: thread_set_valid_queues thread_set_no_change_tcb_state
                                    thread_set_weak_valid_sched_action
                         | strengthen valid_queues_in_correct_ready_q
                                      valid_queues_ready_qs_distinct)+)[1]
                apply ((wpsimp wp: threadSet_sched_pointers threadSet_valid_sched_pointers
                                   threadSet_valid_objs'
                        | strengthen valid_objs'_valid_tcbs')+)[1]
               apply wpsimp+
            apply (rule corres_when, simp)
            apply (rule corres_split[OF decDomainTime_corres])
              apply (rule corres_split[OF getDomainTime_corres])
                apply (rule corres_when,simp)
                apply (rule rescheduleRequired_corres)
               apply (wp hoare_drop_imp)+
             apply (wpsimp simp: dec_domain_time_def)
            apply (wpsimp simp: decDomainTime_def)
           apply (wpsimp wp: hoare_weak_lift_imp threadSet_timeslice_invs
                             tcbSchedAppend_valid_objs'
                             threadSet_pred_tcb_at_state threadSet_weak_sch_act_wf
                             rescheduleRequired_weak_sch_act_wf)+
              apply (strengthen valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct)
              apply (wpsimp wp: thread_set_valid_queues thread_set_weak_valid_sched_action)
             apply ((wpsimp wp: thread_set_valid_queues
                     | strengthen valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct)+)[1]
            apply (wpsimp wp: thread_get_wp)
           apply wpsimp
          apply ((wpsimp wp: threadSet_sched_pointers threadSet_valid_sched_pointers
                             threadSet_valid_objs'
                  | strengthen valid_objs'_valid_tcbs'
                  | wp (once) hoare_drop_imp)+)[1]
         apply (wpsimp wp: gts_wp gts_wp')+
     apply (clarsimp simp: cur_tcb_def)
     apply (frule valid_sched_valid_queues)
     apply (fastforce simp: pred_tcb_at_def obj_at_def valid_sched_weak_strg)
    apply fastforce
   apply (fastforce simp: valid_state'_def ct_not_inQ_def)
  apply fastforce
  done

lemma countTrailingZeros_simp[simp]:
  "countTrailingZeros = word_ctz"
  unfolding countTrailingZeros_def word_ctz_def
  by (simp add: to_bl_upt)

crunch doMachineOp
   for sch_act_ct_rq[wp]: "\<lambda>s. P (ksSchedulerAction s) (ksCurThread s) (ksReadyQueues s)"
   and pred_tcb_at'_ct[wp]: "\<lambda>s. pred_tcb_at' proj test (ksCurThread s) s"
   and ex_nonz_cap_to'[wp]: "\<lambda>s. P (ex_nonz_cap_to' (ksCurThread s) s)"

lemma dmo_wp_no_rest:
  "\<lbrace>K((\<forall>s f. P s = (P (machine_state_update (machine_state_rest_update f) s)))) and P\<rbrace>
   do_machine_op (machine_op_lift f)
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: do_machine_op_def machine_op_lift_def bind_assoc)
  apply wpsimp
  apply (clarsimp simp add: machine_rest_lift_def in_monad select_f_def ignore_failure_def)
  apply (clarsimp split: if_splits)
  apply (drule_tac x=s in spec)
  apply (drule_tac x="\<lambda>_. b" in spec)
  apply simp
  apply (erule rsubst[OF _ arg_cong[where f=P]])
  apply clarsimp
  done

lemma dmo_gets_wp:
  "\<lbrace>\<lambda>s. P (f (machine_state s)) s\<rbrace> do_machine_op (gets f) \<lbrace>P\<rbrace>"
  by (wpsimp simp: submonad_do_machine_op.gets)

lemma not_pred_tcb':
  "(\<not>pred_tcb_at' proj P t s) = (\<not>tcb_at' t s \<or> pred_tcb_at' proj (\<lambda>a. \<not>P a) t s)"
  by (auto simp: pred_tcb_at'_def obj_at'_def)


crunch rescheduleRequired
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
(simp:tcbSchedEnqueue_def wp:unless_wp)

crunch tcbSchedAppend
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
(simp:tcbSchedEnqueue_def wp:unless_wp)

lemma updateTimeSlice_valid_pspace[wp]:
  "\<lbrace>valid_pspace'\<rbrace>
   threadSet (tcbTimeSlice_update (\<lambda>_. ts')) thread
   \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  by (wp threadSet_valid_pspace'T)
     (auto simp: tcb_cte_cases_def tcb_cte_cases_neqs)

lemma dom_upd_eq:
  "f t = Some y \<Longrightarrow> dom (\<lambda>a. if a = t then Some x else f a) = dom f"
  by (auto split: if_split_asm)

lemma updateTimeSlice_hyp_refs[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
   threadSet (tcbTimeSlice_update f) thread
  \<lbrace>\<lambda>r s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding threadSet_def
  apply (clarsimp simp: setObject_def split_def)
  apply (wp getObject_tcb_wp | simp add: updateObject_default_def)+
  apply (clarsimp simp: state_hyp_refs_of'_def obj_at'_def)
  apply (erule subst[where P=P, rotated])
  apply (rule ext)
  apply (clarsimp simp: objBitsKO_def ps_clear_def dom_upd_eq split: option.splits)
  done

crunch tcbSchedAppend
  for irq_handlers'[wp]: valid_irq_handlers'
  and irqs_masked'[wp]: irqs_masked'
  and ct[wp]: cur_tcb'
  (simp: unless_def tcb_cte_cases_def tcb_cte_cases_neqs wp: crunch_wps cur_tcb_lift)

lemma timerTick_invs'[wp]:
  "timerTick \<lbrace>invs'\<rbrace>"
  apply (simp add: timerTick_def)
  apply (wpsimp wp: threadSet_invs_trivial threadSet_pred_tcb_no_state
                    rescheduleRequired_all_invs_but_ct_not_inQ
              simp: tcb_cte_cases_def)
      apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp)
       apply (clarsimp simp: invs'_def valid_state'_def)
      apply (simp add: decDomainTime_def)
      apply wp
     apply simp
     apply wpc
            apply (wp add: threadGet_wp threadSet_cur threadSet_timeslice_invs
                           rescheduleRequired_all_invs_but_ct_not_inQ
                           hoare_vcg_imp_lift threadSet_ct_idle_or_in_cur_domain')+
            apply (rule hoare_strengthen_post[OF tcbSchedAppend_all_invs_but_ct_not_inQ'])
            apply (wpsimp simp: invs'_def valid_state'_def valid_pspace'_def sch_act_wf_weak)+
           apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post)
            apply (wpsimp wp: threadSet_pred_tcb_no_state threadSet_tcbDomain_triv
                              threadSet_valid_objs' threadSet_timeslice_invs)+
           apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
          apply (wpsimp simp: invs'_def valid_state'_def valid_pspace'_def sch_act_wf_weak)+
      apply (wp gts_wp')+
  apply (frule invs_pspace_in_kernel_mappings')
  apply (auto simp: invs'_def st_tcb_at'_def obj_at'_def valid_state'_def cong: conj_cong)
  done

lemma resetTimer_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp resetTimer \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq no_irq_resetTimer)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ b. underlying_memory b p = underlying_memory m p" in use_valid)
    apply (wpsimp wp: resetTimer_underlying_memory_inv)+
  done

lemma dmo_ackInterrupt[wp]:
"\<lbrace>invs'\<rbrace> doMachineOp (ackInterrupt irq) \<lbrace>\<lambda>y. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq no_irq_ackInterrupt)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid)
    apply (wpsimp wp: ackInterrupt_underlying_memory_inv)+
  done

lemma runnable'_eq:
  "runnable' st = (st = Running \<or> st = Restart)"
  by (cases st; simp)

crunch timerTick
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (wp: threadSet_pred_tcb_no_state)

locale Interrupt_R =
  fixes arch_irq_control_inv_valid' :: "Arch.irqcontrol_invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
  fixes arch_irq_control_inv_relation :: "arch_irq_control_invocation \<Rightarrow> Arch.irqcontrol_invocation \<Rightarrow> bool"
  assumes arch_check_irq_inv:
    "\<And>data P. arch_check_irq data \<lbrace>P :: det_state \<Rightarrow> bool\<rbrace>"
  assumes arch_check_irq_valid':
    "\<And>irq. \<lbrace>\<top>\<rbrace> arch_check_irq irq \<lbrace>\<lambda>_ (_::det_state). irq \<le> ucast maxIRQ\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  (* not in [wp] to avoid clobbering checkIRQ_irq_valid *)
  assumes checkIRQ_inv:
    "\<And>irq P. checkIRQ irq \<lbrace>P\<rbrace>"
  assumes checkIRQ_irq_valid:
    "\<And>irq. \<lbrace>\<top>\<rbrace> checkIRQ irq \<lbrace>\<lambda>_ _. arch_valid_irq (toEnum (unat irq))\<rbrace>, -"
  assumes Arch_decodeIRQControlInvocation_inv[wp]:
    "\<And>label args srcSlot extraCaps P.
     Arch.decodeIRQControlInvocation label args srcSlot extraCaps \<lbrace>P\<rbrace>"
  assumes arch_decodeIRQControlInvocation_corres:
    "\<And>caps caps' label args slot.
     list_all2 cap_relation caps caps' \<Longrightarrow>
     corres (ser \<oplus> arch_irq_control_inv_relation)
       (invs and (\<lambda>s. \<forall>cp \<in> set caps. s \<turnstile> cp))
       (invs' and (\<lambda>s. \<forall>cp \<in> set caps'. s \<turnstile>' cp))
       (arch_decode_irq_control_invocation label args slot caps)
       (Arch.decodeIRQControlInvocation label args (cte_map slot) caps')"
  assumes checkIRQ_corres:
    "\<And>irq. corres (ser \<oplus> dc) \<top> \<top> (arch_check_irq irq) (Arch.checkIRQ irq)"
  assumes maxIRQ_H_ucast_toEnum_eq_irq:
    "\<And>x::machine_word. x \<le> ucast maxIRQ \<Longrightarrow> toEnum (unat x) = (ucast x :: irq)"
  assumes arch_decode_irq_control_valid'[wp]:
    "\<And>label args slot caps.
     \<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' cap)
          \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
          \<and> cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot s\<rbrace>
     Arch.decodeIRQControlInvocation label args slot caps
     \<lbrace>arch_irq_control_inv_valid'\<rbrace>,-"
  assumes irq_node_in_global_refs':
    "\<And>(irq::irq) s. Invariants_H.irq_node' s + (ucast irq << cteSizeBits) \<in> global_refs' s"
  assumes arch_invokeIRQHandler_corres:
    "\<And>i i'.
     irq_handler_inv_relation i i' \<Longrightarrow>
     corres dc \<top> \<top> (arch_invoke_irq_handler i) (Arch.invokeIRQHandler i')"
  assumes arch_invoke_irq_control_invs'[wp]:
    "\<And>i. \<lbrace>invs' and arch_irq_control_inv_valid' i\<rbrace> Arch.performIRQControl i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  assumes is_derived'_NotificationCap:
    "\<And>ctes src cap cap'.
     \<lbrakk>isNotificationCap cap; isNotificationCap cap'\<rbrakk>
     \<Longrightarrow> is_derived' ctes src cap' cap = badge_derived' cap' cap"
  assumes arch_performIRQControl_corres:
    "\<And>ivk ivk'.
     arch_irq_control_inv_relation ivk ivk' \<Longrightarrow> corres (dc \<oplus> dc)
            (einvs and arch_irq_control_inv_valid ivk)
            (invs' and arch_irq_control_inv_valid' ivk')
            (arch_invoke_irq_control ivk)
            (Arch.performIRQControl ivk')"
  assumes is_simple_cap'_IRQHandlerCap:
    "\<And>cap. isIRQHandlerCap cap \<Longrightarrow> is_simple_cap' cap"
  assumes sameRegionAs_IRQControl_handler[simp]:
    "\<And>irq. global.sameRegionAs capability.IRQControlCap (capability.IRQHandlerCap irq)"
  assumes handle_reserved_irq_corres[corres]:
    "\<And>irq.
     corres dc einvs
       (\<lambda>s. invs' s \<and> (irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s))
       (handle_reserved_irq irq) (handleReservedIRQ irq)"
  assumes maskIrqSignal_corres[corres]:
    "\<And>irq. corres dc \<top> \<top> (arch_mask_irq_signal irq) (Arch.maskIrqSignal irq)"
  assumes dmo_ackInterrupt_corres[corres]:
    "\<And>irq. corres dc \<top> \<top> (do_machine_op (ackInterrupt irq)) (doMachineOp (ackInterrupt irq))"
  assumes maskIrqSignal_invs'[wp]:
    "\<And>irq. Arch.maskIrqSignal irq \<lbrace>invs'\<rbrace>"
  assumes handleReservedIRQ_invs':
    "\<And>irq.
     \<lbrace>invs' and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s)\<rbrace>
     handleReservedIRQ irq
     \<lbrace>\<lambda>_. invs'\<rbrace>"
  assumes arch_valid_irq_le_maxIRQ:
    "\<And>irq. arch_valid_irq irq \<Longrightarrow> irq \<le> maxIRQ"
  assumes arch_valid_irq_valid_IRQHandlerCap:
    "\<And>irq s. arch_valid_irq irq \<Longrightarrow> valid_cap' (capability.IRQHandlerCap irq) s"
begin

primrec irq_control_inv_relation ::
  "irq_control_invocation \<Rightarrow> irqcontrol_invocation \<Rightarrow> bool"
  where
  "irq_control_inv_relation (Invocations_A.IRQControl irq slot slot') x
       = (x = IssueIRQHandler irq (cte_map slot) (cte_map slot'))"
| "irq_control_inv_relation (Invocations_A.ArchIRQControl ivk) x
       = (\<exists>ivk'. x = ArchIRQControl ivk' \<and> arch_irq_control_inv_relation ivk ivk')"

primrec irq_handler_inv_valid' :: "irqhandler_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "irq_handler_inv_valid' (AckIRQ irq) = (\<lambda>s. intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive)"
| "irq_handler_inv_valid' (ClearIRQHandler irq) = \<top>"
| "irq_handler_inv_valid' (SetIRQHandler irq cap cte_ptr)
     = (valid_cap' cap and valid_cap' (IRQHandlerCap irq)
           and K (isNotificationCap cap)
           and cte_wp_at' (badge_derived' cap \<circ> cteCap) cte_ptr
           and (\<lambda>s. \<exists>ptr'. cte_wp_at' (\<lambda>cte. cteCap cte = IRQHandlerCap irq) ptr' s)
           and ex_cte_cap_wp_to' isCNodeCap cte_ptr)"

primrec irq_control_inv_valid' :: "irqcontrol_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "irq_control_inv_valid' (ArchIRQControl ivk) = arch_irq_control_inv_valid' ivk"
| "irq_control_inv_valid' (IssueIRQHandler irq ptr ptr') =
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) ptr and
      cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) ptr' and
      ex_cte_cap_to' ptr and real_cte_at' ptr and
      (Not o irq_issued' irq) and K (arch_valid_irq irq))"

lemma decode_irq_handler_valid'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' fst cap)
        \<and> (\<exists>ptr'. cte_wp_at' (\<lambda>cte. cteCap cte = IRQHandlerCap irq) ptr' s)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' (fst cap) (irq_node' s). ex_cte_cap_to' r s)
        \<and> (\<forall>cap \<in> set caps. ex_cte_cap_wp_to' isCNodeCap (snd cap) s)
        \<and> (\<forall>cap \<in> set caps. cte_wp_at' (badge_derived' (fst cap) \<circ> cteCap) (snd cap) s)
        \<and> s \<turnstile>' IRQHandlerCap irq\<rbrace>
   decodeIRQHandlerInvocation label irq caps
   \<lbrace>irq_handler_inv_valid'\<rbrace>,-"
  apply (simp add: decodeIRQHandlerInvocation_def Let_def split_def
               split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  apply (clarsimp simp: neq_Nil_conv gen_isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule (1) valid_irq_handlers_ctes_ofD)
    apply (simp add: invs'_def valid_state'_def)
   apply (simp add: irq_issued'_def)
  apply clarsimp
  done

crunch InterruptDecls_H.decodeIRQControlInvocation
  for inv[wp]: "P"
  (simp: crunch_simps wp: crunch_wps checkIRQ_inv)

lemma decodeIRQControlInvocation_corres:
  "list_all2 cap_relation caps caps' \<Longrightarrow>
   corres (ser \<oplus> irq_control_inv_relation)
     (invs and (\<lambda>s. \<forall>cp \<in> set caps. s \<turnstile> cp)) (invs' and (\<lambda>s. \<forall>cp \<in> set caps'. s \<turnstile>' cp))
     (decode_irq_control_invocation label args slot caps)
     (decodeIRQControlInvocation label args (cte_map slot) caps')"
  apply (clarsimp simp: decode_irq_control_invocation_def decodeIRQControlInvocation_def
             split del: if_split cong: if_cong)
  (* decode_irq_control_invocation features a machine_word to irq ucast, so 64/32 shows up here
     until we can wrap it up below *)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp)
    apply (cases caps, simp split: list.split)
    apply (case_tac "\<exists>n. length args = Suc (Suc (Suc n))")
     apply (clarsimp simp: list_all2_Cons1 Let_def split_def liftE_bindE length_Suc_conv)
     defer
     apply (prop_tac "length args \<le> 2", arith)
     apply (clarsimp split: list.split)
    apply (corres simp: o_def corres: arch_decodeIRQControlInvocation_corres)
   apply (auto intro!: corres_guard_imp[OF arch_decodeIRQControlInvocation_corres]
               dest!: not_le_imp_less
               simp: o_def length_Suc_conv whenE_rangeCheck_eq ucast_nat_def
               split: list.splits)[1]
  apply (corres corres: checkIRQ_corres)
      (* we now know the irq is in safe range; assume that *)
      apply (rule_tac F="y \<le> ucast maxIRQ" in corres_gen_asm)
      (* use it to rewrite the ucast back to a less revealing form *)
      apply (simp only: maxIRQ_H_ucast_toEnum_eq_irq)
      apply (corres corres: is_irq_active_corres)
        apply (rule corres_splitEE)
           apply (rule lookupSlotForCNodeOp_corres; clarsimp)
          apply (rule corres_splitEE[OF ensureEmptySlot_corres], simp)
            apply (rule corres_returnOkTT)
            apply clarsimp
           apply (wpsimp wp: isIRQActive_inv arch_check_irq_valid' checkIRQ_inv
                       simp: invs_valid_objs invs_psp_aligned invs_valid_objs'
                             invs_pspace_aligned' invs_pspace_distinct'
                  | strengthen invs_valid_objs invs_psp_aligned
                  | wp (once) hoare_drop_imps arch_check_irq_inv)+
  done

lemma decode_irq_control_valid'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' cap)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
        \<and> cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot s\<rbrace>
   decodeIRQControlInvocation label args slot caps
   \<lbrace>irq_control_inv_valid'\<rbrace>,-"
  apply (simp add: decodeIRQControlInvocation_def Let_def split_def
                   rangeCheck_def unlessE_whenE
              split del: if_split
              cong: if_cong list.case_cong gen_invocation_labels.case_cong)
  (* very sensitive; validE_valid makes unprovable goal out of checkIRQ's valid IRQ postcondition;
     since checkIRQ ensures the IRQ is valid, that postcondition can't be true on throw side *)
  apply (wpsimp wp: ensureEmptySlot_stronger isIRQActive_wp whenE_throwError_wp checkIRQ_irq_valid
                simp: o_def imp_not_concl_imp
         | wp (once) hoare_drop_impE hoare_drop_imp checkIRQ_inv)+
  done

lemma valid_globals_ex_cte_cap_irq:
  "\<lbrakk> ex_cte_cap_wp_to' isCNodeCap ptr s; valid_global_refs' s; valid_objs' s \<rbrakk>
   \<Longrightarrow> ptr \<noteq> intStateIRQNode (ksInterruptState s) + 2 ^ cte_level_bits * ucast (irq :: irq)"
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_wp_to'_def)
  apply (drule(1) ctes_of_valid'[rotated])
  apply (drule(1) valid_global_refsD')
  apply (drule subsetD[rotated], erule cte_refs_capRange)
   apply (clarsimp simp: gen_isCap_simps)
  apply (subgoal_tac "irq_node' s + 2 ^ cte_level_bits * ucast irq \<in> global_refs' s")
   apply blast
  using irq_node_in_global_refs'
  apply (clarsimp simp: cteSizeBits_cte_level_bits[symmetric] shiftl_t2n)
  done

lemma invokeIRQHandler_corres:
  "irq_handler_inv_relation i i' \<Longrightarrow>
   corres dc (einvs and irq_handler_inv_valid i)
             (invs' and irq_handler_inv_valid' i')
     (invoke_irq_handler i)
     (InterruptDecls_H.invokeIRQHandler i')"
  apply (cases i; simp add: Interrupt_H.invokeIRQHandler_def)
    apply (rule corres_guard_imp, rule arch_invokeIRQHandler_corres; simp)
   apply (rename_tac word cap prod)
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getIRQSlot_corres])
       apply simp
       apply (rule corres_split_nor[OF cap_delete_one_corres])
         apply (rule cteInsert_corres, simp+)
        apply (rule_tac Q'="\<lambda>rv s. einvs s \<and> cte_wp_at (\<lambda>c. c = cap.NullCap) irq_slot s
                                  \<and> (a, b) \<noteq> irq_slot
                                  \<and> cte_wp_at (is_derived (cdt s) (a, b) cap) (a, b) s"
                      in hoare_post_imp)
         apply fastforce
        apply (wp cap_delete_one_still_derived)+
       apply (strengthen invs_mdb_strengthen')
       apply wp+
      apply (simp add: conj_comms eq_commute)
      apply (wp get_irq_slot_different hoare_drop_imps)+
    apply (clarsimp simp: valid_state_def invs_def)
    apply (erule cte_wp_at_weakenE, simp add: is_derived_use_interrupt)
   apply fastforce
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getIRQSlot_corres])
      apply simp
      apply (rule cap_delete_one_corres)
     apply wp+
   apply simp+
  done

lemma ntfn_badge_derived_enough_strg:
  "cte_wp_at' (\<lambda>cte. isNotificationCap cap \<and> badge_derived' cap (cteCap cte)) ptr s
        \<longrightarrow> cte_wp_at' (is_derived' ctes ptr cap \<circ> cteCap) ptr s"
  by (clarsimp simp: cte_wp_at_ctes_of gen_isCap_simps is_derived'_NotificationCap badge_derived'_def)

lemma performIRQControl_corres:
  "irq_control_inv_relation i i' \<Longrightarrow>
   corres (dc \<oplus> dc)
     (einvs and irq_control_inv_valid i)
     (invs' and irq_control_inv_valid' i')
     (invoke_irq_control i) (performIRQControl i')"
  apply (cases i, simp_all add: performIRQControl_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor[OF setIRQState_corres])
        apply (simp add: irq_state_relation_def)
       apply (rule cteInsert_simple_corres)
         apply wpsimp+
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                          cte_wp_at_caps_of_state is_simple_cap_arch
                          is_simple_cap_def is_cap_simps safe_parent_for_def)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                         is_simple_cap'_IRQHandlerCap
                         gen_isCap_simps arch_valid_irq_valid_IRQHandlerCap)
   apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
   apply (case_tac ctea)
   apply (auto simp: gen_isCap_simps dest: valid_irq_handlers_ctes_ofD)[1]
  apply (clarsimp simp: arch_performIRQControl_corres)
  done

lemma invoke_irq_control_invs'[wp]:
  "\<lbrace>invs' and irq_control_inv_valid' i\<rbrace> performIRQControl i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (cases i, simp_all add: performIRQControl_def)
  apply (rule hoare_pre)
   apply_trace (wp cteInsert_simple_invs | simp add: cte_wp_at_ctes_of)+
  apply (clarsimp simp: cte_wp_at_ctes_of arch_valid_irq_le_maxIRQ
                        gen_isCap_simps is_simple_cap'_IRQHandlerCap
                        safe_parent_for'_def arch_valid_irq_valid_IRQHandlerCap)
  apply (case_tac ctea)
  apply (auto dest: valid_irq_handlers_ctes_ofD
              simp: invs'_def valid_state'_def)
  done

lemma handleInterrupt_corres:
  "corres dc
     einvs (invs' and (\<lambda>s. intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive)
                  and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s))
     (handle_interrupt irq) (handleInterrupt irq)"
  (is "corres dc _ (invs' and _ and ?P') _ _")
  supply debugPrint_def[simp]
  apply (simp add: handle_interrupt_def handleInterrupt_def)
  apply (rule conjI[rotated]; rule impI)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getIRQState_corres,
                               where R="\<lambda>rv. einvs"
                                 and R'="\<lambda>rv. invs' and ?P' and (\<lambda>s. rv \<noteq> IRQInactive)"])
       defer
       apply (wp getIRQState_wp getIRQState_inv do_machine_op_bind doMachineOp_bind
              | simp add: do_machine_op_bind doMachineOp_bind)+
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule corres_machine_op, rule corres_eq_trivial;
               simp add: no_fail_maskInterrupt)+
      apply ((wp | simp)+)[4]
  apply (rule corres_gen_asm2)
  apply (case_tac st, simp_all add: irq_state_relation_def bind_assoc split: irqstate.split_asm)
    apply (simp add: getSlotCap_def bind_assoc)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF getIRQSlot_corres])
        apply simp
        apply (rule corres_split[OF get_cap_corres,
                                  where R="\<lambda>rv. einvs and valid_cap rv"
                                   and R'="\<lambda>rv. invs' and valid_cap' (cteCap rv)"])
          apply (rule corres_underlying_split[where r'=dc])
             apply (case_tac xb, simp_all add: doMachineOp_return)[1]
              apply (clarsimp simp add: when_def doMachineOp_return)
              apply (rule corres_guard_imp, rule sendSignal_corres)
               apply (clarsimp simp: valid_cap_def valid_cap'_def dc_def[symmetric]
                                     do_machine_op_bind doMachineOp_bind)+
            apply corres
             apply wpsimp+
    apply fastforce
   apply (corres corres: timerTick_corres corres_machine_op simp: invs_distinct invs_psp_aligned)
  apply (corres corres: corres_machine_op corres_eq_trivial)
  done

lemma hint_invs[wp]:
  "\<lbrace>invs' and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s)\<rbrace>
    handleInterrupt irq \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply debugPrint_def[simp]
  apply (simp add: handleInterrupt_def getSlotCap_def cong: irqstate.case_cong)
  apply (rule conjI; rule impI)
   apply (wp dmo_maskInterrupt_True getCTE_wp' | wpc | simp add: doMachineOp_bind)+
    apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp)
     apply (clarsimp simp: cte_wp_at_ctes_of ex_nonz_cap_to'_def)
     apply fastforce
    apply (wpsimp wp: threadSet_invs_trivial getIRQState_wp handleReservedIRQ_invs'
                  split_del: if_split)+
  done

end (* Interrupt_R *)

locale Interrupt_R_2 = Interrupt_R +
  assumes invoke_arch_irq_handler_invs'[wp]:
    "\<And>i. \<lbrace>invs' and irq_handler_inv_valid' i\<rbrace> Arch.invokeIRQHandler i \<lbrace>\<lambda>rv. invs'\<rbrace>"
begin

lemma invoke_irq_handler_invs'[wp]:
  "\<lbrace>invs' and irq_handler_inv_valid' i\<rbrace>
   InterruptDecls_H.invokeIRQHandler i
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (cases i; simp add: Interrupt_H.invokeIRQHandler_def)
    apply wpsimp
   apply (wp cteInsert_invs)+
    apply (strengthen ntfn_badge_derived_enough_strg isnt_irq_handler_strg)
    apply (wp cteDeleteOne_other_cap cteDeleteOne_other_cap[unfolded o_def])
   apply (rename_tac word1 cap word2)
   apply (simp add: getInterruptState_def getIRQSlot_def locateSlot_conv)
   apply wp
  apply (rename_tac word1 cap word2 s)
  apply (clarsimp simp: ucast_nat_def)
  apply (drule_tac irq=word1 in valid_globals_ex_cte_cap_irq)
    apply clarsimp+
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_to'_def
                        gen_isCap_simps untyped_derived_eq_def)
  apply (fastforce simp: cteSizeBits_cte_level_bits shiftl_t2n)+
  done

end (* Interrupt_R_2 *)

end
