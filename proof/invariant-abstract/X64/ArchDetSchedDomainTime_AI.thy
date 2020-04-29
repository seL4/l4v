(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedDomainTime_AI
imports "../DetSchedDomainTime_AI"
begin

context Arch begin global_naming X64

named_theorems DetSchedDomainTime_AI_assms

lemma flush_table_domain_list_inv[wp]: "\<lbrace>\<lambda>s. P (domain_list s)\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

lemma flush_table_domain_time_inv[wp]: "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_finalise_cap "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp mapM_x_wp' subset_refl simp: crunch_simps)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply,
  arch_invoke_irq_control, handle_vm_fault, arch_post_modify_registers,
  prepare_thread_delete, handle_hypervisor_fault, arch_post_cap_deletion,
  make_arch_fault_msg, arch_get_sanitise_register_info, handle_reserved_irq,
  arch_invoke_irq_handler, arch_mask_irq_signal
  "\<lambda>s. P (domain_list s)"

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: arch_finalise_cap "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects,
  arch_invoke_irq_control, handle_vm_fault, arch_post_modify_registers,
  prepare_thread_delete, handle_hypervisor_fault, arch_post_cap_deletion,
  arch_get_sanitise_register_info, handle_reserved_irq, arch_invoke_irq_handler,
  arch_mask_irq_signal
  "\<lambda>s. P (domain_time s)"

declare init_arch_objects_exst[DetSchedDomainTime_AI_assms]
        make_arch_fault_msg_invs[DetSchedDomainTime_AI_assms]

end

global_interpretation DetSchedDomainTime_AI?: DetSchedDomainTime_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

context Arch begin global_naming X64

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_perform_invocation "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: arch_perform_invocation "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps check_cap_inv)

crunch exst[wp]: do_machine_op "\<lambda>s. P (exst s)"

crunch inv[wp]: get_irq_slot P

lemma handle_interrupt_valid_domain_time [DetSchedDomainTime_AI_assms]:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s \<rbrace> handle_interrupt i
   \<lbrace>\<lambda>rv s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
  apply (unfold handle_interrupt_def)
  apply (case_tac "maxIRQ < i"; simp)
    subgoal by (wp hoare_false_imp, simp)
  apply (rule hoare_pre)
   apply (wp do_machine_op_exst | simp add: arch_mask_irq_signal_def | wpc)+
      apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
      apply wp
     apply (wp get_cap_wp)
     apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
     apply wp+
    apply simp (* dxo_eq *)
    apply (clarsimp simp: timer_tick_def num_domains_def)
    apply (wp reschedule_required_valid_domain_time
          | simp add: handle_reserved_irq_def
          | wp (once) hoare_drop_imp)+
   apply clarsimp
  done

end

global_interpretation DetSchedDomainTime_AI_2?: DetSchedDomainTime_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

end
