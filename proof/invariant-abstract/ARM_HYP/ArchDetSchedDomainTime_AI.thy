(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchDetSchedDomainTime_AI
imports "../DetSchedDomainTime_AI"
begin

context Arch begin global_naming ARM_HYP

named_theorems DetSchedDomainTime_AI_assms

lemma set_vcpu_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_list s)\<rbrace> set_vcpu p vcpu \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (wp set_vcpu_wp) simp

crunch domain_list_inv[wp]: vcpu_update, vcpu_save_register, vgic_update "\<lambda>s. P (domain_list s)"
crunch domain_list_inv[wp]: vcpu_enable, vcpu_disable, vcpu_restore "\<lambda>s. P (domain_list s)"

lemma vcpu_save_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_list s)\<rbrace> vcpu_save v \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  apply (simp add: vcpu_save_def)
  apply (cases v; simp)
  apply (case_tac a; simp)
  apply (wp | wpc | clarsimp | rule_tac S="set [0..<num_list_regs]" in mapM_wp)+
  done

lemma vcpu_switch_domain_list_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_list s)\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (rule hoare_pre)
   apply (wp | wpc | clarsimp)+
  done

lemma set_vcpu_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace> set_vcpu p vcpu \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  by (wp set_vcpu_wp) simp

crunch domain_time_inv[wp]:
  vcpu_update, vcpu_save_register, vgic_update "\<lambda>s. P (domain_time s)"

crunch domain_time_inv[wp]:
  vcpu_enable, vcpu_disable, vcpu_restore "\<lambda>s. P (domain_time s)"

lemma vcpu_save_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace> vcpu_save v \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  apply (simp add: vcpu_save_def)
  apply (cases v; simp)
  apply (case_tac a; simp)
  apply (wp | wpc | clarsimp | rule_tac S="set [0..<num_list_regs]" in mapM_wp)+
  done

lemma vcpu_switch_domain_time_inv[wp]:
  "\<lbrace>\<lambda>s. P (domain_time s)\<rbrace> vcpu_switch param_a \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (rule hoare_pre)
   apply (wp | wpc | clarsimp)+
  done

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_finalise_cap "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects, arch_tcb_set_ipc_buffer,
  arch_invoke_irq_control, handle_vm_fault, arch_get_sanitise_register_info,
  prepare_thread_delete, arch_post_modify_registers
  "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: arch_finalise_cap, arch_get_sanitise_register_info "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects, arch_tcb_set_ipc_buffer,
  arch_invoke_irq_control, handle_vm_fault,
  prepare_thread_delete, arch_post_modify_registers
  "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: make_arch_fault_msg "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: make_arch_fault_msg "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

end

global_interpretation DetSchedDomainTime_AI?: DetSchedDomainTime_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

context Arch begin global_naming ARM_HYP

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: handle_hypervisor_fault "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: handle_reserved_irq "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: handle_hypervisor_fault "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: handle_reserved_irq "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_perform_invocation "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: arch_perform_invocation "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps check_cap_inv)

lemma vgic_maintenance_valid_domain_time:
  "\<lbrace>\<lambda>s. 0 < domain_time s\<rbrace>
    vgic_maintenance \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding vgic_maintenance_def
  apply (rule hoare_strengthen_post [where Q="\<lambda>_ s. 0 < domain_time s"])
   apply (wpsimp wp: handle_fault_domain_time_inv hoare_drop_imps)
  apply clarsimp
  done

lemma handle_reserved_irq_valid_domain_time:
  "\<lbrace>\<lambda>s. 0 < domain_time s\<rbrace>
     handle_reserved_irq i \<lbrace>\<lambda>y s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding handle_reserved_irq_def by (wpsimp wp: vgic_maintenance_valid_domain_time)

lemma handle_interrupt_valid_domain_time [DetSchedDomainTime_AI_assms]:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s \<rbrace> handle_interrupt i
   \<lbrace>\<lambda>rv s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
   apply (unfold handle_interrupt_def)
   apply (case_tac "maxIRQ < i"; simp)
    subgoal by (wp hoare_false_imp, simp)
   apply (rule hoare_pre)
    apply (wp do_machine_op_exst | simp | wpc)+
       apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
       apply wp
      apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
      apply wp+
     apply simp (* dxo_eq *)
     apply (clarsimp simp: timer_tick_def num_domains_def)
     apply (wp reschedule_required_valid_domain_time handle_reserved_irq_valid_domain_time
           | simp
           | wp_once hoare_drop_imp)+
   done


end

global_interpretation DetSchedDomainTime_AI_2?: DetSchedDomainTime_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

end
