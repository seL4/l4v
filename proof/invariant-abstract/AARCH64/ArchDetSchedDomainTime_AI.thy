(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedDomainTime_AI
imports DetSchedDomainTime_AI
begin

context Arch begin arch_global_naming

named_theorems DetSchedDomainTime_AI_assms

crunch
  vcpu_update, vcpu_save_reg, vgic_update, vcpu_enable, vcpu_disable, vcpu_restore,
  vcpu_write_reg, vcpu_read_reg, vcpu_save, vcpu_switch, set_vcpu, vgic_update_lr,
  read_vcpu_register, write_vcpu_register
  for domain_fields_invs[wp]: "domain_fields P"
  (wp: crunch_wps simp: crunch_simps)

crunch arch_finalise_cap
  for domain_fields_invs[wp, DetSchedDomainTime_AI_assms]: "domain_fields P"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch set_extra_badge
  for domain_time_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects,
  arch_invoke_irq_control, arch_get_sanitise_register_info,
  prepare_thread_delete, handle_hypervisor_fault, init_arch_objects,
  arch_post_modify_registers, arch_post_cap_deletion, handle_vm_fault,
  arch_invoke_irq_handler, arch_prepare_next_domain, arch_prepare_set_domain,
  arch_post_set_flags, handle_spurious_irq, handle_reserved_irq, arch_mask_irq_signal
  for domain_fields_invs[wp, DetSchedDomainTime_AI_assms]: "domain_fields P"
  (simp: crunch_simps isFpuEnable_def wp: mapM_wp' transfer_caps_loop_pres crunch_wps)

crunch handle_spurious_irq
  for scheduler_action[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (scheduler_action s)"

lemmas [DetSchedDomainTime_AI_assms] =
  init_arch_objects_exst
  arch_get_sanitise_register_info_inv
  arch_post_modify_registers_inv

end

global_interpretation DetSchedDomainTime_AI?: DetSchedDomainTime_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
qed

context Arch begin arch_global_naming

crunch arch_perform_invocation
  for domain_fields_invs[wp, DetSchedDomainTime_AI_assms]: "domain_fields P"
  (wp: crunch_wps check_cap_inv simp: if_apply_def2)

lemma vgic_maintenance_valid_domain_time:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
    vgic_maintenance \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding vgic_maintenance_def
  apply (rule hoare_strengthen_post[where Q'="\<lambda>_ s. 0 < domain_time s"])
   apply (wpsimp wp: hoare_drop_imps)
  apply clarsimp
  done

lemma vppi_event_valid_domain_time:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s\<rbrace>
    vppi_event irq \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding vppi_event_def
  apply (rule hoare_strengthen_post[where Q'="\<lambda>_ s. 0 < domain_time s"])
   apply (wpsimp wp: hoare_drop_imps)
  apply clarsimp
  done

lemma irq_vppi_event_index_irqVGICMaintenance[simp]:
  "irq_vppi_event_index irqVGICMaintenance = None"
  by (simp add: irq_vppi_event_index_def irqVGICMaintenance_def irqVTimerEvent_def)

lemma handle_reserved_irq_valid_domain_time:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s\<rbrace>
   handle_reserved_irq i
   \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding handle_reserved_irq_def
  by (wpsimp wp: vppi_event_valid_domain_time vgic_maintenance_valid_domain_time)

end

global_interpretation DetSchedDomainTime_AI_2?: DetSchedDomainTime_AI_2
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
qed

end
