(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchEmptyFail_AI
imports EmptyFail_AI
begin

context Arch begin arch_global_naming

named_theorems EmptyFail_AI_assms

crunch_ignore (empty_fail)
  (add: invalidateLocalTLB_ASID_impl invalidateLocalTLB_VAASID_impl cleanByVA_impl
        cleanByVA_PoU_impl invalidateByVA_impl invalidateByVA_I_impl
        invalidate_I_PoU_impl cleanInvalByVA_impl branchFlush_impl
        clean_D_PoU_impl cleanInvalidate_D_PoC_impl cleanInvalidateL2Range_impl
        invalidateL2Range_impl cleanL2Range_impl flushBTAC_impl
        writeContextID_impl isb_impl dsb_impl dmb_impl setHardwareASID_impl
        writeTTBR0_impl cacheRangeOp setIRQTrigger_impl)

crunch
  loadWord, load_word_offs, store_word_offs, storeWord, getRestartPC, get_mrs, setRegister
 for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]

end

global_interpretation EmptyFail_AI_load_word?: EmptyFail_AI_load_word
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch possible_switch_to,set_thread_state_act
 for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: kernel_object.splits option.splits arch_cap.splits cap.splits endpoint.splits
         bool.splits list.splits thread_state.splits split_def catch_def sum.splits
         Let_def wp: empty_fail_zipWithM_x)

crunch handle_fault
 for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: kernel_object.splits option.splits arch_cap.splits cap.splits endpoint.splits
         bool.splits list.splits thread_state.splits split_def catch_def sum.splits
         Let_def)

crunch decode_tcb_configure, decode_bind_notification, decode_unbind_notification,
  decode_set_priority, decode_set_mcpriority, decode_set_sched_params, decode_set_timeout_ep,
  decode_set_tls_base, decode_set_space
 for (empty_fail) empty_fail[wp]
  (simp: cap.splits arch_cap.splits split_def)

lemma decode_tcb_invocation_empty_fail[wp]:
  "empty_fail (decode_tcb_invocation a b (ThreadCap p) d e)"
  by (simp add: decode_tcb_invocation_def split: invocation_label.splits | wp | wpc | intro conjI impI)+

crunch find_pd_for_asid, get_master_pde, check_vp_alignment,
                   create_mapping_entries, ensure_safe_mapping, get_asid_pool, resolve_vaddr
  for (empty_fail) empty_fail[wp]
  (simp: kernel_object.splits arch_kernel_obj.splits option.splits pde.splits pte.splits)

lemma arch_decode_ARMASIDControlMakePool_empty_fail:
  "invocation_type label = ArchInvocationLabel ARMASIDControlMakePool
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (simp add: arch_decode_invocation_def Let_def)
  apply (intro impI conjI allI)
   apply (simp add: isPageFlushLabel_def isPDFlushLabel_def split: arch_cap.splits)+
   apply (rule impI)
   apply (simp add: split_def)
   apply (wp (once), simp)
   apply (subst bindE_assoc[symmetric])
   apply (rule empty_fail_bindE)
    subgoal by (force simp: empty_fail_def whenE_def throwError_def select_ext_def bindE_def
                            bind_def return_def returnOk_def lift_def liftE_def fail_def gets_def
                            get_def assert_def select_def
                      split: if_split_asm)
   by (simp add: Let_def split: cap.splits arch_cap.splits option.splits bool.splits | wp | intro conjI impI allI)+

lemma arch_decode_ARMASIDPoolAssign_empty_fail:
  "invocation_type label = ArchInvocationLabel ARMASIDPoolAssign
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (simp add: arch_decode_invocation_def split_def Let_def isPageFlushLabel_def isPDFlushLabel_def
            split: arch_cap.splits cap.splits option.splits | intro impI allI)+
  apply (rule empty_fail_bindE)
   apply simp
  apply (rule empty_fail_bindE)
   apply ((simp | wp)+)[1]
  apply (rule empty_fail_bindE)
   apply ((simp | wp)+)[1]
  apply (rule empty_fail_bindE)
   apply ((simp | wp)+)[1]
  apply (subst bindE_assoc[symmetric])
  apply (rule empty_fail_bindE)
   subgoal by (force simp: empty_fail_def whenE_def throwError_def select_def bindE_def
                           bind_def return_def returnOk_def lift_def liftE_def select_ext_def
                           gets_def get_def assert_def fail_def)
  apply wp
  done

lemma arch_decode_invocation_empty_fail[wp]:
  "empty_fail (arch_decode_invocation label b c d e f)"
  apply (case_tac "invocation_type label")
  apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> \<open>-\<close>\<close>)
  apply (rename_tac alabel)
  apply (case_tac alabel; simp)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_ARMASIDControlMakePool_empty_fail\<close>\<close>)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_ARMASIDPoolAssign_empty_fail\<close>\<close>)
  apply ((simp add: arch_decode_ARMASIDControlMakePool_empty_fail arch_decode_ARMASIDPoolAssign_empty_fail)+)[2]
  including no_pre
  by ((simp add: arch_decode_invocation_def Let_def split: arch_cap.splits cap.splits option.splits
     | (wp+) | intro conjI impI allI)+)

end

global_interpretation EmptyFail_AI_derive_cap?: EmptyFail_AI_derive_cap
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma preemption_point_empty_fail[wp, EmptyFail_AI_assms]:
  "empty_fail preemption_point"
  apply (wpsimp simp: mk_ef_def getActiveIRQ_def  preemption_point_def OR_choiceE_def andM_def
                      ifM_def update_time_stamp_def getCurrentTime_def get_sc_active_def)
  done

crunch maskInterrupt, empty_slot,
    setHardwareASID, set_current_pd, finalise_cap, preemption_point, reset_work_units,
    update_work_units, cap_swap_for_delete, decode_invocation
 for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: Let_def catch_def split_def OR_choiceE_def mk_ef_def andM_def ifM_def
         option.splits endpoint.splits
         notification.splits thread_state.splits sum.splits cap.splits arch_cap.splits
         kernel_object.splits vmpage_size.splits pde.splits bool.splits list.splits)

crunch setRegister, setNextPC
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]

end

global_interpretation EmptyFail_AI_rec_del?: EmptyFail_AI_rec_del
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming
crunch
  cap_delete, choose_thread
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
end

global_interpretation EmptyFail_AI_schedule?: EmptyFail_AI_schedule
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma deactivateInterrupt_empty_fail[wp]:
  "config_ARM_GIC_V3 \<Longrightarrow> empty_fail (deactivateInterrupt irq)"
  unfolding deactivateInterrupt_def
  by wpsimp

crunch handle_event, activate_thread, check_budget
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: cap.splits arch_cap.splits split_def invocation_label.splits Let_def
         kernel_object.splits arch_kernel_obj.splits option.splits pde.splits pte.splits
         bool.splits apiobject_type.splits aobject_type.splits notification.splits
         thread_state.splits endpoint.splits catch_def sum.splits cnode_invocation.splits
         page_table_invocation.splits page_invocation.splits asid_control_invocation.splits
         asid_pool_invocation.splits arch_invocation.splits irq_state.splits syscall.splits
         flush_type.splits page_directory_invocation.splits
   ignore: resetTimer_impl ackInterrupt_impl)
end

global_interpretation EmptyFail_AI_call_kernel?: EmptyFail_AI_call_kernel
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

end
