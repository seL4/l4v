(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedDomainTime_AI
imports DetSchedDomainTime_AI
begin

context Arch begin arch_global_naming

named_theorems DetSchedDomainTime_AI_assms

crunch arch_finalise_cap
  for domain_list_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply,
  arch_invoke_irq_control, handle_vm_fault, arch_get_sanitise_register_info,
  prepare_thread_delete, handle_hypervisor_fault, init_arch_objects,
  arch_post_modify_registers, arch_post_cap_deletion, arch_invoke_irq_handler,
  arch_prepare_next_domain, arch_prepare_set_domain, arch_post_set_flags
  for domain_list_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps)

crunch arch_finalise_cap
   for domain_time_inv[wp, DetSchedDomainTime_AI_assms]:
         "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

crunch arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
         handle_arch_fault_reply, init_arch_objects, arch_invoke_irq_control, handle_vm_fault,
         prepare_thread_delete, handle_hypervisor_fault, arch_post_modify_registers,
         arch_post_cap_deletion, arch_invoke_irq_handler
  for domain_time_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s :: det_state. P (domain_time s)"
  (wp: crunch_wps)

crunch arch_finalise_cap
 for domain_time_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

crunch
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects,
  arch_invoke_irq_control, handle_vm_fault,
  prepare_thread_delete, handle_hypervisor_fault,
  arch_post_modify_registers, arch_post_cap_deletion,
  arch_invoke_irq_handler, arch_prepare_next_domain, arch_prepare_set_domain, arch_post_set_flags
  for domain_time_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_time s)"
  (wp: crunch_wps)

declare init_arch_objects_exst[DetSchedDomainTime_AI_assms]
        arch_get_sanitise_register_info_inv[DetSchedDomainTime_AI_assms]

end

global_interpretation DetSchedDomainTime_AI?: DetSchedDomainTime_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
qed

context Arch begin arch_global_naming

crunch arch_perform_invocation, arch_mask_irq_signal
  for domain_list_inv [wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

crunch handle_reserved_irq, handle_spurious_irq
  for domain_time_inv[wp, DetSchedDomainTime_AI_assms]:
         "\<lambda>s. P (domain_time s) (scheduler_action s)"
  and domain_list_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps)

crunch handle_spurious_irq
  for scheduler_action[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (scheduler_action s)"

end

global_interpretation DetSchedDomainTime_AI_2?: DetSchedDomainTime_AI_2
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
qed

end
