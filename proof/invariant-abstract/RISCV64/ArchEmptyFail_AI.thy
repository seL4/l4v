(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchEmptyFail_AI
imports EmptyFail_AI
begin

context Arch begin global_naming RISCV64

named_theorems EmptyFail_AI_assms

crunch_ignore (empty_fail)
  (add: setVSpaceRoot_impl sfence_impl hwASIDFlush_impl read_stval resetTimer_impl stval_val
        pt_lookup_from_level setIRQTrigger_impl plic_complete_claim_impl)

crunches
  loadWord, load_word_offs, storeWord, getRestartPC, get_mrs
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]

end

global_interpretation EmptyFail_AI_load_word?: EmptyFail_AI_load_word
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin global_naming RISCV64

crunches handle_fault
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: kernel_object.splits option.splits arch_cap.splits cap.splits endpoint.splits
         bool.splits list.splits thread_state.splits split_def catch_def sum.splits
         Let_def)

crunches
  decode_tcb_configure, decode_bind_notification, decode_unbind_notification,
  decode_set_priority, decode_set_mcpriority, decode_set_sched_params,
  decode_set_tls_base
  for (empty_fail) empty_fail[wp]
  (simp: cap.splits arch_cap.splits split_def)

lemma decode_tcb_invocation_empty_fail[wp]:
  "empty_fail (decode_tcb_invocation a b (ThreadCap p) d e)"
  by (simp add: decode_tcb_invocation_def split: gen_invocation_labels.splits invocation_label.splits
      | wp | intro conjI impI)+

crunches find_vspace_for_asid, check_vp_alignment, check_slot
  for (empty_fail) empty_fail[wp]

lemma arch_decode_RISCVASIDControlMakePool_empty_fail:
  "invocation_type label = ArchInvocationLabel RISCVASIDControlMakePool
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (wpsimp simp: arch_decode_invocation_def decode_asid_pool_invocation_def)
    apply (simp add: decode_asid_control_invocation_def)
    apply (intro impI conjI allI)
    apply (simp add: split_def)
    apply (wp (once), simp)
    apply (subst bindE_assoc[symmetric])
    apply (rule empty_fail_bindE)
     subgoal by (force simp: empty_fail_def whenE_def throwError_def select_ext_def bindE_def
                             bind_def return_def returnOk_def lift_def liftE_def fail_def
                             gets_def get_def assert_def select_def
                       split: if_split_asm)
    apply wpsimp
   apply (wpsimp simp: decode_frame_invocation_def)
  apply (wpsimp simp: decode_page_table_invocation_def)
  done

lemma arch_decode_RISCVASIDPoolAssign_empty_fail:
  "invocation_type label = ArchInvocationLabel RISCVASIDPoolAssign
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  unfolding arch_decode_invocation_def decode_page_table_invocation_def decode_frame_invocation_def
            decode_asid_control_invocation_def
  apply (wpsimp; wpsimp?)
  apply (simp add: decode_asid_pool_invocation_def)
  apply (intro impI allI conjI)
  apply (simp add: arch_decode_invocation_def split_def Let_def
            split: arch_cap.splits cap.splits option.splits | intro impI allI)+
  apply clarsimp
  apply (rule empty_fail_bindE, simp)
  apply (rule empty_fail_bindE, wpsimp)
  apply (rule empty_fail_bindE, wpsimp)
  apply (rule empty_fail_bindE, wpsimp)
  apply (subst bindE_assoc[symmetric])
  apply (rule empty_fail_bindE)
   subgoal by (force simp: empty_fail_def whenE_def throwError_def select_def bindE_def
                           bind_def return_def returnOk_def lift_def liftE_def select_ext_def
                           gets_def get_def assert_def fail_def)
  apply wpsimp
  done

lemma arch_decode_invocation_empty_fail[wp]:
  "empty_fail (arch_decode_invocation label b c d e f)"
  apply (case_tac "invocation_type label")
  apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> \<open>-\<close>\<close>)
  apply (rename_tac alabel)
  apply (case_tac alabel; simp)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_RISCVASIDControlMakePool_empty_fail\<close>\<close>)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_RISCVASIDPoolAssign_empty_fail\<close>\<close>)
  apply ((simp add: arch_decode_RISCVASIDControlMakePool_empty_fail
                    arch_decode_RISCVASIDPoolAssign_empty_fail)+)[2]
  by (all \<open>(wpsimp simp: arch_decode_invocation_def decode_asid_pool_invocation_def
                         decode_asid_control_invocation_def decode_frame_invocation_def
                         decode_page_table_invocation_def decode_pt_inv_map_def
                         decode_fr_inv_map_def Let_def)\<close>) (* 15s *)

end

global_interpretation EmptyFail_AI_derive_cap?: EmptyFail_AI_derive_cap
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin global_naming RISCV64

lemma empty_fail_pt_lookup_from_level[wp]:
  "empty_fail (pt_lookup_from_level level pt_ptr vptr target_pt_ptr)"
  apply (induct level arbitrary: pt_ptr)
   apply (subst pt_lookup_from_level_simps, simp)
  apply (subst pt_lookup_from_level_simps)
  apply wpsimp
  done

crunches maskInterrupt, empty_slot,
    finalise_cap, preemption_point,
    cap_swap_for_delete, decode_invocation
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: Let_def catch_def split_def OR_choiceE_def mk_ef_def option.splits endpoint.splits
         notification.splits thread_state.splits sum.splits cap.splits arch_cap.splits
         kernel_object.splits vmpage_size.splits pte.splits bool.splits list.splits)

crunches setRegister, setNextPC
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]

end

global_interpretation EmptyFail_AI_rec_del?: EmptyFail_AI_rec_del
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin global_naming RISCV64
crunches
  cap_delete, choose_thread
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
end

global_interpretation EmptyFail_AI_schedule_unit?: EmptyFail_AI_schedule_unit
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

global_interpretation EmptyFail_AI_schedule_det?: EmptyFail_AI_schedule_det
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

global_interpretation EmptyFail_AI_schedule?: EmptyFail_AI_schedule
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin global_naming RISCV64

crunches read_stval
  for (empty_fail) empty_fail[wp]
  (ignore_del: read_stval)

lemma plic_complete_claim_empty_fail[wp, EmptyFail_AI_assms]:
  "empty_fail (plic_complete_claim irq)"
  by (clarsimp simp: plic_complete_claim_def)

crunches possible_switch_to, handle_event, activate_thread
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: cap.splits arch_cap.splits split_def invocation_label.splits Let_def
         kernel_object.splits arch_kernel_obj.splits option.splits pte.splits
         bool.splits apiobject_type.splits aobject_type.splits notification.splits
         thread_state.splits endpoint.splits catch_def sum.splits cnode_invocation.splits
         page_table_invocation.splits page_invocation.splits asid_control_invocation.splits
         asid_pool_invocation.splits arch_invocation.splits irq_state.splits syscall.splits
   ignore_del: possible_switch_to)

end

global_interpretation EmptyFail_AI_call_kernel_unit?: EmptyFail_AI_call_kernel_unit
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

global_interpretation EmptyFail_AI_call_kernel_det?: EmptyFail_AI_call_kernel_det
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

global_interpretation EmptyFail_AI_call_kernel?: EmptyFail_AI_call_kernel
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

end
