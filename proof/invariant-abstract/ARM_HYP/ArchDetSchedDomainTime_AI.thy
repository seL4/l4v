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

crunch
  vcpu_update, vcpu_save_reg, vgic_update, vcpu_enable, vcpu_disable, vcpu_restore,
  vcpu_write_reg, vcpu_read_reg, vcpu_save, vcpu_switch, set_vcpu, vgic_update_lr,
  read_vcpu_register, write_vcpu_register
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"
  and domain_time_inv[wp]: "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps simp: crunch_simps)

crunch arch_finalise_cap
  for domain_list_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply,
  arch_invoke_irq_control, arch_get_sanitise_register_info,
  prepare_thread_delete, handle_hypervisor_fault, make_arch_fault_msg, init_arch_objects,
  arch_post_modify_registers, arch_post_cap_deletion, handle_vm_fault,
  arch_invoke_irq_handler, arch_prepare_next_domain, arch_prepare_set_domain, arch_post_set_flags
  for domain_list_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_list s)"
  (simp: crunch_simps wp: mapM_wp' transfer_caps_loop_pres crunch_wps)
declare init_arch_objects_exst[DetSchedDomainTime_AI_assms]
        make_arch_fault_msg_inv[DetSchedDomainTime_AI_assms]

crunch arch_finalise_cap, arch_get_sanitise_register_info
  for domain_time_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects,
  arch_invoke_irq_control, arch_get_sanitise_register_info,
  prepare_thread_delete, handle_hypervisor_fault, handle_vm_fault,
  arch_post_modify_registers, arch_post_cap_deletion, make_arch_fault_msg,
  arch_invoke_irq_handler, handle_reserved_irq, arch_mask_irq_signal,
  arch_prepare_next_domain, arch_prepare_set_domain, arch_post_set_flags,
  handle_spurious_irq
  for domain_time_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_time s)"
  (simp: crunch_simps wp: transfer_caps_loop_pres crunch_wps)

crunch handle_spurious_irq
  for scheduler_action[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s. P (scheduler_action s)"
  and domain_list_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_list s)"

end

global_interpretation DetSchedDomainTime_AI?: DetSchedDomainTime_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch arch_perform_invocation
  for domain_time_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_time s)"
  and domain_list_inv[wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

lemma vgic_maintenance_valid_domain_time:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
    vgic_maintenance \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding vgic_maintenance_def
  apply (rule hoare_strengthen_post[where Q'="\<lambda>_ s. 0 < domain_time s"])
   apply (wpsimp wp: handle_fault_domain_time_inv hoare_drop_imps)
  apply clarsimp
  done

lemma vppi_event_valid_domain_time:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
    vppi_event irq \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding vppi_event_def
  apply (rule hoare_strengthen_post[where Q'="\<lambda>_ s. 0 < domain_time s"])
   apply (wpsimp wp: handle_fault_domain_time_inv hoare_drop_imps)
  apply clarsimp
  done

lemma handle_reserved_irq_valid_domain_time:
  "\<lbrace>\<lambda>s::det_state. 0 < domain_time s\<rbrace>
     handle_reserved_irq i \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding handle_reserved_irq_def
  by (wpsimp wp: vgic_maintenance_valid_domain_time vppi_event_valid_domain_time)

lemma timer_tick_valid_domain_time:
  "\<lbrace> \<lambda>s :: det_ext state. 0 < domain_time s \<rbrace>
   timer_tick
   \<lbrace>\<lambda>x s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>" (is "\<lbrace> ?dtnot0 \<rbrace> _ \<lbrace> _ \<rbrace>")
  unfolding timer_tick_def
  supply if_split[split del]
  supply thread_get_wp[wp del]
  supply if_apply_def2[simp]
  apply (wpsimp
           wp: reschedule_required_valid_domain_time hoare_vcg_const_imp_lift gts_wp
               (* unless we hit dec_domain_time we know ?dtnot0 holds on the state, so clean up the
                  postcondition once we hit thread_set_time_slice *)
               hoare_post_imp[where Q'="\<lambda>_. ?dtnot0" and Q="\<lambda>_ s. domain_time s = 0 \<longrightarrow> X s"
                                and f="thread_set_time_slice t ts" for X t ts]
               hoare_drop_imp[where f="thread_get t f" for t f])
  apply fastforce
  done

crunch do_machine_op
  for domain_time_sched[wp]: "\<lambda>s. P (domain_time s) (scheduler_action s)"

lemma handle_interrupt_valid_domain_time [DetSchedDomainTime_AI_assms]:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s \<rbrace>
   handle_interrupt i
   \<lbrace>\<lambda>rv s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>" (is "\<lbrace> ?dtnot0 \<rbrace> _ \<lbrace> _ \<rbrace>")
  unfolding handle_interrupt_def
  supply if_split[split del]
  supply if_apply_def2[simp]
  apply (case_tac "maxIRQ < i", solves \<open>wpsimp wp: hoare_false_imp\<close>)
  apply clarsimp
  apply (wpsimp simp: arch_mask_irq_signal_def)
        apply (rule hoare_post_imp[where Q'="\<lambda>_. ?dtnot0" and f="send_signal p c" for p c], fastforce)
        apply wpsimp
       apply (rule hoare_post_imp[where Q'="\<lambda>_. ?dtnot0" and f="get_cap p" for p], fastforce)
       apply (wpsimp wp: timer_tick_valid_domain_time simp: handle_reserved_irq_def)+
     apply (rule hoare_post_imp[where Q'="\<lambda>_. ?dtnot0" and f="vgic_maintenance"], fastforce)
     apply wpsimp+
     apply (rule hoare_post_imp[where Q'="\<lambda>_. ?dtnot0" and f="vppi_event i" for i], fastforce)
     apply wpsimp+
   apply (rule hoare_post_imp[where Q'="\<lambda>_. ?dtnot0" and f="get_irq_state i" for i], fastforce)
   apply wpsimp+
  done

crunch handle_reserved_irq, arch_mask_irq_signal
  for domain_list_inv [wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps)

end

global_interpretation DetSchedDomainTime_AI_2?: DetSchedDomainTime_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

end
