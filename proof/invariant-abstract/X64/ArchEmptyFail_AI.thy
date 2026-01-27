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

crunch
  load_word_offs, get_mrs, invalidate_page_structure_cache_asid
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]

(* FIXME: remove from locale *)
declare loadWord_empty_fail[EmptyFail_AI_assms]

end

global_interpretation EmptyFail_AI_load_word?: EmptyFail_AI_load_word
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch handle_fault
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: kernel_object.splits option.splits arch_cap.splits cap.splits endpoint.splits
         bool.splits list.splits thread_state.splits split_def catch_def sum.splits
         Let_def)

lemma port_out_empty_fail[simp, intro!]:
  assumes ef: "\<And>a. empty_fail (oper a)"
  shows "empty_fail (port_out oper w)"
  apply (simp add: port_out_def)
  by (wp | simp add: ef)+

lemma port_in_empty_fail[simp, intro!]:
  assumes ef: "empty_fail oper"
  shows "empty_fail (port_in oper)"
  apply (simp add: port_in_def)
  by (wp | simp add: ef)+

crunch
  decode_tcb_configure, decode_bind_notification, decode_unbind_notification,
  decode_set_priority, decode_set_mcpriority, decode_set_sched_params,
  decode_set_tls_base, decode_set_flags
  for (empty_fail) empty_fail[wp]
  (simp: cap.splits arch_cap.splits split_def)

lemma decode_tcb_invocation_empty_fail[wp]:
  "empty_fail (decode_tcb_invocation a b (ThreadCap p) d e)"
  by (simp add: decode_tcb_invocation_def split: gen_invocation_labels.splits invocation_label.splits
      | wp | intro conjI impI)+

crunch find_vspace_for_asid, check_vp_alignment,
                   ensure_safe_mapping, get_asid_pool, lookup_pt_slot, get_pt,
                   decode_port_invocation, decode_ioport_control_invocation
  for (empty_fail) empty_fail[wp]
  (simp: kernel_object.splits arch_kernel_obj.splits option.splits pde.splits pte.splits
         pdpte.splits pml4e.splits vmpage_size.splits Let_def)

lemma create_mapping_entries_empty_fail[wp]:
  "empty_fail (create_mapping_entries a b c d e f)"
  by (case_tac c; simp add: create_mapping_entries_def; wp)

lemma arch_decode_X64ASIDControlMakePool_empty_fail:
  "invocation_type label = ArchInvocationLabel X64ASIDControlMakePool
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (simp add: arch_decode_invocation_def Let_def)
  apply (intro impI conjI allI)
   apply (simp split: arch_cap.splits)
   apply (intro conjI impI)
   apply (simp add: split_def)
   apply (wp (once), simp)
   apply (subst bindE_assoc[symmetric])
   apply (rule empty_fail_bindE)
    subgoal by (force simp: empty_fail_def whenE_def throwError_def select_ext_def bindE_def bind_def return_def
                            returnOk_def lift_def liftE_def fail_def gets_def get_def assert_def select_def split: if_split_asm)
  apply (simp add: Let_def split: cap.splits arch_cap.splits option.splits bool.splits | wp | intro conjI impI allI)+
  by (clarsimp simp add: decode_page_invocation_def decode_page_table_invocation_def
                         decode_page_directory_invocation_def decode_pdpt_invocation_def
                  split: arch_cap.splits | wp | intro conjI)+


lemma arch_decode_X64ASIDPoolAssign_empty_fail:
  "invocation_type label = ArchInvocationLabel X64ASIDPoolAssign
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (simp add: arch_decode_invocation_def Let_def split: arch_cap.splits)
  apply (intro impI allI conjI)
  apply (simp add: arch_decode_invocation_def split_def Let_def
            split: arch_cap.splits cap.splits option.splits | intro impI allI)+
  apply clarsimp
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
  apply (clarsimp simp: decode_page_invocation_def decode_page_table_invocation_def
                         decode_page_directory_invocation_def decode_pdpt_invocation_def | wp | intro conjI)+
  done

lemma arch_decode_invocation_empty_fail[wp]:
  "empty_fail (arch_decode_invocation label b c d e f)"
  apply (case_tac "invocation_type label")
  apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> \<open>-\<close>\<close>)
  apply (rename_tac alabel)
  apply (case_tac alabel; simp)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_X64ASIDControlMakePool_empty_fail\<close>\<close>)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_X64ASIDPoolAssign_empty_fail\<close>\<close>)
  apply ((simp add: arch_decode_X64ASIDControlMakePool_empty_fail arch_decode_X64ASIDPoolAssign_empty_fail)+)[2]
  by ((simp add: arch_decode_invocation_def decode_page_invocation_def Let_def decode_page_table_invocation_def
                         decode_page_directory_invocation_def decode_pdpt_invocation_def
             split: arch_cap.splits cap.splits option.splits | wp | intro conjI impI allI)+)

end

global_interpretation EmptyFail_AI_derive_cap?: EmptyFail_AI_derive_cap
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma flush_table_empty_fail[simp, wp]: "empty_fail (flush_table a b c d)"
  unfolding flush_table_def
  by wpsimp

crunch maskInterrupt, empty_slot,
    finalise_cap, preemption_point,
    cap_swap_for_delete, decode_invocation
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: Let_def catch_def split_def OR_choiceE_def mk_ef_def option.splits endpoint.splits
         notification.splits thread_state.splits sum.splits cap.splits arch_cap.splits
         kernel_object.splits vmpage_size.splits pde.splits bool.splits list.splits
         set_object_def)

end

global_interpretation EmptyFail_AI_rec_del?: EmptyFail_AI_rec_del
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming
crunch
  cap_delete, choose_thread, arch_prepare_next_domain
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
end

global_interpretation EmptyFail_AI_schedule?: EmptyFail_AI_schedule
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch possible_switch_to, handle_event, activate_thread, maybe_handle_interrupt
  for (empty_fail) empty_fail[wp, EmptyFail_AI_assms]
  (simp: cap.splits arch_cap.splits split_def invocation_label.splits Let_def
         kernel_object.splits arch_kernel_obj.splits option.splits pde.splits pte.splits
         bool.splits apiobject_type.splits aobject_type.splits notification.splits
         thread_state.splits endpoint.splits catch_def sum.splits cnode_invocation.splits
         page_table_invocation.splits page_invocation.splits asid_control_invocation.splits
         asid_pool_invocation.splits arch_invocation.splits irq_state.splits syscall.splits)
end

global_interpretation EmptyFail_AI_call_kernel?: EmptyFail_AI_call_kernel
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

end
