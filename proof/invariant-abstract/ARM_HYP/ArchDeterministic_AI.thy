(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchDeterministic_AI
imports "../Deterministic_AI"
begin

context Arch begin global_naming ARM

named_theorems Deterministic_AI_assms

crunch valid_list[wp, Deterministic_AI_assms]:
 vcpu_save, vcpu_enable, vcpu_disable, vcpu_restore, arch_tcb_set_ipc_buffer, arch_tcb_sanitise_condition valid_list
  (wp: crunch_wps simp: unless_def crunch_simps)

lemma vcpu_switch_valid_list[wp, Deterministic_AI_assms]:
  "\<lbrace>valid_list\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (rule hoare_pre)
    apply(wpsimp)+
  done

crunch valid_list[wp, Deterministic_AI_assms]: cap_swap_for_delete,set_cap,finalise_cap valid_list
  (wp: crunch_wps simp: unless_def crunch_simps)

end

global_interpretation Deterministic_AI_1?: Deterministic_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

context Arch begin global_naming ARM

crunch valid_list[wp]: invalidate_tlb_by_asid valid_list
  (wp: crunch_wps preemption_point_inv' simp: crunch_simps filterM_mapM unless_def
   ignore: without_preemption filterM )


crunch valid_list[wp]: invoke_untyped valid_list
  (wp: crunch_wps preemption_point_inv' hoare_unless_wp mapME_x_wp'
    simp: mapM_x_def_bak crunch_simps
    ignore: Deterministic_A.OR_choiceE)

crunch valid_list[wp]: invoke_irq_control valid_list

lemma perform_page_table_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_table_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_table_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' | intro impI conjI allI | wpc | simp split: cap.splits arch_cap.splits option.splits)+
  done

lemma perform_page_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases a,simp_all)
  apply (wp mapM_x_wp' mapM_wp' crunch_wps | intro impI conjI allI | wpc | simp add: set_message_info_def set_mrs_def split: cap.splits arch_cap.splits option.splits sum.splits)+
  done

crunch valid_list[wp]: perform_invocation valid_list
  (wp: crunch_wps simp: crunch_simps ignore: without_preemption)

crunch valid_list[wp, Deterministic_AI_assms]: handle_invocation valid_list
  (wp: crunch_wps syscall_valid simp: crunch_simps ignore: without_preemption)

crunch valid_list[wp, Deterministic_AI_assms]: handle_recv, handle_yield, handle_call valid_list
  (wp: crunch_wps simp: crunch_simps)

lemma handle_vm_fault_valid_list[wp, Deterministic_AI_assms]:
"\<lbrace>valid_list\<rbrace> handle_vm_fault thread fault \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (cases fault,simp_all)
  apply (wp|simp)+
  done

lemma vgic_maintenance_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> vgic_maintenance \<lbrace>\<lambda>_. valid_list\<rbrace>"
  unfolding vgic_maintenance_def by (wpsimp wp: hoare_drop_imps)

lemma handle_interrupt_valid_list[wp, Deterministic_AI_assms]:
  "\<lbrace>valid_list\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding handle_interrupt_def ackInterrupt_def handle_reserved_irq_def
  by (wpsimp wp: hoare_drop_imps)

crunch valid_list[wp, Deterministic_AI_assms]: handle_send,handle_reply valid_list

crunch valid_list[wp, Deterministic_AI_assms]: handle_hypervisor_fault valid_list

end

global_interpretation Deterministic_AI_2?: Deterministic_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

end

