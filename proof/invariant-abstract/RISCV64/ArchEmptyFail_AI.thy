(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchEmptyFail_AI
imports "../EmptyFail_AI"
begin

context Arch begin global_naming RISCV64

named_theorems EmptyFail_AI_assms

crunch_ignore (empty_fail)
  (add: setVSpaceRoot_impl sfence_impl hwASIDFlush_impl read_sbadaddr resetTimer_impl sbadaddr_val
        pt_lookup_from_level)

crunch (empty_fail) empty_fail[wp, EmptyFail_AI_assms]:
  loadWord, load_word_offs, storeWord, getRestartPC, get_mrs

end

global_interpretation EmptyFail_AI_load_word?: EmptyFail_AI_load_word
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin global_naming RISCV64

crunch (empty_fail) empty_fail[wp, EmptyFail_AI_assms]: handle_fault
  (simp: kernel_object.splits option.splits arch_cap.splits cap.splits endpoint.splits
         bool.splits list.splits thread_state.splits split_def catch_def sum.splits
         Let_def wp: zipWithM_x_empty_fail)

crunch (empty_fail) empty_fail[wp]:
  decode_tcb_configure, decode_bind_notification, decode_unbind_notification,
  decode_set_priority, decode_set_mcpriority, decode_set_sched_params,
  decode_set_tls_base
  (simp: cap.splits arch_cap.splits split_def)

lemma decode_tcb_invocation_empty_fail[wp]:
  "empty_fail (decode_tcb_invocation a b (ThreadCap p) d e)"
  by (simp add: decode_tcb_invocation_def split: invocation_label.splits | wp | intro conjI impI)+

crunch (empty_fail) empty_fail[wp]: find_vspace_for_asid, check_vp_alignment

lemma arch_decode_RISCVASIDControlMakePool_empty_fail:
  "invocation_type label = ArchInvocationLabel RISCVASIDControlMakePool
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (wpsimp simp: arch_decode_invocation_def)
  sorry (* FIXME RISCV
  apply (intro impI conjI allI)
   apply (simp split: arch_cap.splits)
   apply (intro conjI impI)
   apply (simp add: split_def)
   apply wp
    apply simp
   apply (subst bindE_assoc[symmetric])
   apply (rule empty_fail_bindE)
    subgoal by (fastforce simp: empty_fail_def whenE_def throwError_def select_ext_def bindE_def bind_def return_def
                                returnOk_def lift_def liftE_def fail_def gets_def get_def assert_def select_def split: if_split_asm)
  apply (simp add: Let_def split: cap.splits arch_cap.splits option.splits bool.splits | wp | intro conjI impI allI)+
  by (clarsimp simp add: decode_page_invocation_def decode_page_table_invocation_def
                         decode_page_directory_invocation_def decode_pdpt_invocation_def
                  split: arch_cap.splits | wp | intro conjI)+
  *)


lemma arch_decode_RISCVASIDPoolAssign_empty_fail:
  "invocation_type label = ArchInvocationLabel RISCVASIDPoolAssign
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (simp add: arch_decode_invocation_def Let_def split: arch_cap.splits)
  apply (intro impI allI conjI)
  sorry (* FIXME RISCV
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
   subgoal by (fastforce simp: empty_fail_def whenE_def throwError_def select_def bindE_def
                               bind_def return_def returnOk_def lift_def liftE_def select_ext_def
                               gets_def get_def assert_def fail_def)
  apply (clarsimp simp: decode_page_invocation_def decode_page_table_invocation_def
                         decode_page_directory_invocation_def decode_pdpt_invocation_def | wp | intro conjI)+
  done *)

lemma arch_decode_invocation_empty_fail[wp]:
  "empty_fail (arch_decode_invocation label b c d e f)"
  sorry (* FIXME RISCV
  apply (case_tac "invocation_type label")
  apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> \<open>-\<close>\<close>)
  apply (rename_tac alabel)
  apply (case_tac alabel; simp)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_RISCVASIDControlMakePool_empty_fail\<close>\<close>)
  apply (find_goal \<open>succeeds \<open>erule arch_decode_RISCVASIDPoolAssign_empty_fail\<close>\<close>)
  apply ((simp add: arch_decode_RISCVASIDControlMakePool_empty_fail arch_decode_RISCVASIDPoolAssign_empty_fail)+)[2]
  by ((simp add: arch_decode_invocation_def decode_page_invocation_def Let_def decode_page_table_invocation_def
                         decode_page_directory_invocation_def decode_pdpt_invocation_def
             split: arch_cap.splits cap.splits option.splits | wp | intro conjI impI allI)+)
  *)

end

global_interpretation EmptyFail_AI_derive_cap?: EmptyFail_AI_derive_cap
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin global_naming RISCV64

lemma empty_fail_pt_lookup_from_level[wp]:
  "empty_fail (pt_lookup_from_level level pt_ptr vptr target_pt_ptr)"
  sorry (* FIXME RISCV *)

crunch (empty_fail) empty_fail[wp, EmptyFail_AI_assms]: maskInterrupt, empty_slot,
    finalise_cap, preemption_point,
    cap_swap_for_delete, decode_invocation
  (simp: Let_def catch_def split_def OR_choiceE_def mk_ef_def option.splits endpoint.splits
         notification.splits thread_state.splits sum.splits cap.splits arch_cap.splits
         kernel_object.splits vmpage_size.splits pte.splits bool.splits list.splits
         forM_x_def empty_fail_mapM_x)

crunch (empty_fail) empty_fail[wp, EmptyFail_AI_assms]: setRegister, setNextPC

end

global_interpretation EmptyFail_AI_rec_del?: EmptyFail_AI_rec_del
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact EmptyFail_AI_assms)?)
  qed

context Arch begin global_naming RISCV64
crunch (empty_fail) empty_fail[wp, EmptyFail_AI_assms]:
  cap_delete, choose_thread
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

crunch (empty_fail) empty_fail[wp]: read_sbadaddr

lemma empty_fail_handle_vm_fault[wp]: (* FIXME RISCV: currently false, SELFOUR-1955 *)
  "empty_fail (handle_vm_fault thread fault)"
  sorry (* FIXME RISCV: should work in crunch below once fixed *)

declare handle_vm_fault.simps[simp del] (* FIXME RISCV: remove after SELFOUR-1955 *)

crunch (empty_fail) empty_fail[wp, EmptyFail_AI_assms]: handle_event, activate_thread
  (simp: cap.splits arch_cap.splits split_def invocation_label.splits Let_def
         kernel_object.splits arch_kernel_obj.splits option.splits pte.splits
         bool.splits apiobject_type.splits aobject_type.splits notification.splits
         thread_state.splits endpoint.splits catch_def sum.splits cnode_invocation.splits
         page_table_invocation.splits page_invocation.splits asid_control_invocation.splits
         asid_pool_invocation.splits arch_invocation.splits irq_state.splits syscall.splits)

declare handle_vm_fault.simps[simp] (* FIXME RISCV: remove after SELFOUR-1955 *)

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
