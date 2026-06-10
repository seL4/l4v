(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIRQMasks_IF
imports IRQMasks_IF
begin

context Arch begin global_naming AARCH64

named_theorems IRQMasks_IF_assms

declare storeWord_irq_masks_inv[IRQMasks_IF_assms]

lemma resetTimer_irq_masks[IRQMasks_IF_assms, wp]:
  "resetTimer \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  by (simp add: resetTimer_def | wp no_irq)+

lemma delete_objects_irq_masks[IRQMasks_IF_assms, wp]:
  "delete_objects ptr bits \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wp dmo_wp no_irq_mapM_x no_irq | simp add: freeMemory_def no_irq_storeWord)+
  done

crunch invoke_untyped
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (ignore: delete_objects wp: crunch_wps dmo_wp
       wp: mapME_x_inv_wp preemption_point_inv
     simp: crunch_simps no_irq_clearMemory mapM_x_def_bak unless_def)

lemma vcpu_invalidate_active_irq_masks[wp]:
  "vcpu_invalidate_active \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  unfolding vcpu_invalidate_active_def vcpu_disable_def
  by (wpsimp wp: dmo_wp)

crunch finalise_cap
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps)

crunch send_signal, timer_tick
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps ignore: do_machine_op wp: dmo_wp simp: crunch_simps)

lemma handle_interrupt_irq_masks[IRQMasks_IF_assms]:
  notes no_irq[wp del]
  shows
    "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and K (irq \<le> maxIRQ)\<rbrace>
     handle_interrupt irq
     \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: handle_interrupt_def split del: if_split)
  apply (rule hoare_pre)
   apply (rule hoare_if)
    apply simp
   apply (wp dmo_wp
          | simp add: ackInterrupt_def maskInterrupt_def when_def split del: if_split
          | wpc
          | simp add: get_irq_state_def
          | wp (once) hoare_drop_imp hoare_pre_cont)+
  apply (fastforce simp: domain_sep_inv_def)
  done

lemma arch_invoke_irq_control_irq_masks[IRQMasks_IF_assms]:
  "\<lbrace>domain_sep_inv False st and arch_irq_control_inv_valid invok\<rbrace>
   arch_invoke_irq_control invok
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  by (cases invok) (auto simp: arch_irq_control_inv_valid_def domain_sep_inv_def valid_def)

lemma dmo_getActiveIRQ_irq_masks[IRQMasks_IF_assms, wp]:
  "do_machine_op (getActiveIRQ in_kernel) \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  apply (rule hoare_pre, rule dmo_wp)
  apply (simp add: getActiveIRQ_def | wp | simp add: no_irq_def | clarsimp)+
  done

lemma dmo_getActiveIRQ_return_axiom[IRQMasks_IF_assms, wp]:
  "\<lbrace>\<top>\<rbrace> do_machine_op (getActiveIRQ in_kernel) \<lbrace>\<lambda>rv s. (\<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ)\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply (rule hoare_pre, rule dmo_wp)
   apply (insert irq_oracle_max_irq)
   apply (wp dmo_getActiveIRQ_irq_masks)
  apply (clarsimp simp: maxIRQ_def)
  done

crunch activate_thread, handle_spurious_irq, handle_vm_fault
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp no_irq)

end


global_interpretation IRQMasks_IF_1?: IRQMasks_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact IRQMasks_IF_assms)?)
qed


context Arch begin global_naming AARCH64

crunch handle_vm_fault, handle_hypervisor_fault
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp no_irq)

crunch do_reply_transfer, set_priority, set_flags, arch_post_set_flags
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps dmo_wp empty_slot_irq_masks simp: crunch_simps unless_def)

lemma no_irq_do_flush[wp,simp]:
  "no_irq (do_flush type vstart vend pstart)"
  by (wpsimp simp: do_flush_def)

crunch perform_vspace_invocation, perform_page_table_invocation, perform_asid_control_invocation,
       perform_asid_pool_invocation, perform_sgi_invocation, perform_page_invocation
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp crunch_wps no_irq simp: crunch_simps)

(* FIXME: remove duplication in this proof -- requires getting the wp automation
          to do the right thing with dropping imps in validE goals *)
lemma invoke_tcb_irq_masks[IRQMasks_IF_assms]:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and tcb_inv_wf tinv\<rbrace>
   invoke_tcb tinv
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply (case_tac tinv)
         apply((wp restart_irq_masks hoare_vcg_if_lift  mapM_x_wp[OF _ subset_refl]
                | wpc
                | simp split del: if_split add: check_cap_at_def
                | clarsimp)+)[3]
      defer
      apply ((wp | simp )+)[2]
    (* NotificationControl *)
    apply (rename_tac option)
    apply (case_tac option)
     apply ((wp | simp)+)[2]
   (* just ThreadControl left *)
   apply (simp add: split_def cong: option.case_cong)
   apply wpsimp+
       apply (rule hoare_strengthen_postE[OF cap_delete_irq_masks[where P=P]])
        apply blast
       apply blast
      apply (wpsimp wp: hoare_vcg_all_liftE_R hoare_vcg_const_imp_liftE_R hoare_vcg_all_lift hoare_drop_imps
                        checked_cap_insert_domain_sep_inv)+
      apply (rule_tac Q'="\<lambda> r s. domain_sep_inv False st s \<and> P (irq_masks_of_state s)"
                  and E'="\<lambda>_ s. P (irq_masks_of_state s)" in hoare_strengthen_postE)
        apply (wp hoare_vcg_conj_liftE1 cap_delete_irq_masks)
       apply fastforce
      apply blast
     apply (wpsimp wp: hoare_weak_lift_imp hoare_vcg_all_lift checked_cap_insert_domain_sep_inv)+
     apply (rule_tac Q'="\<lambda> r s. domain_sep_inv False st s \<and> P (irq_masks_of_state s)"
                 and E'="\<lambda>_ s. P (irq_masks_of_state s)" in hoare_strengthen_postE)
       apply (wp hoare_vcg_conj_liftE1 cap_delete_irq_masks)
      apply fastforce
     apply blast
    apply (simp add: option_update_thread_def | wp hoare_weak_lift_imp hoare_vcg_all_lift | wpc)+
  by fastforce+

crunch arch_prepare_set_domain,
       invoke_vcpu_inject_irq, invoke_vcpu_read_register,
       invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for irq_masks[IRQMasks_IF_assms,wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp mapM_x_wp_inv mapM_wp_inv)

lemma inactive_irqVTimerEvent:
  "\<lbrace>domain_sep_inv False st and R False\<rbrace>
   is_irq_active irqVTimerEvent
   \<lbrace>\<lambda>rv. if rv then Q rv else R rv\<rbrace>"
  unfolding is_irq_active_def get_irq_state_def
  apply wpsimp
  apply (fastforce simp: domain_sep_inv_def non_kernel_IRQs_def)
  done

crunch vcpu_restore_reg, vcpu_restore_reg_range
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp mapM_x_wp)

lemma restore_virt_timer_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   restore_virt_timer vcpu_ptr
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding restore_virt_timer_def
  by (wpsimp wp: inactive_irqVTimerEvent[where st=st] | wp hoare_pre_cont)+

lemma vcpu_enable_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   vcpu_enable vr
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding vcpu_enable_def
  by (wpsimp wp: restore_virt_timer_irq_masks[where st=st] dmo_wp)

lemma vcpu_restore_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   vcpu_restore vr
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding vcpu_restore_def
  by (wpsimp wp: vcpu_enable_irq_masks[where st=st] mapM_wp_inv dmo_wp)

lemma vcpu_switch_Some_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   vcpu_switch (Some vcpu)
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding vcpu_switch_def
  by (wpsimp wp: vcpu_restore_irq_masks[where st=st] vcpu_enable_irq_masks[where st=st] dmo_wp)

lemma associate_vcpu_tcb_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   associate_vcpu_tcb vcpu_ptr t
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding associate_vcpu_tcb_def
  by (wpsimp wp: vcpu_switch_Some_irq_masks[where st=st] hoare_weak_lift_imp | wps)+

lemma perform_vcpu_invocation_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   perform_vcpu_invocation i
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding perform_vcpu_invocation_def
  by (wpsimp wp: associate_vcpu_tcb_irq_masks[where st=st])

lemma perform_smc_invocation_irq_masks[wp]:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s))\<rbrace>
   perform_smc_invocation i
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding perform_smc_invocation_def doSMC_mop_def
  by (wpsimp simp: dmo_distr wp: hoare_drop_imps dmo_wp)

lemma arch_perform_invocation_irq_masks[IRQMasks_IF_assms, wp]:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   arch_perform_invocation i
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding arch_perform_invocation_def fun_app_def
  by (wpsimp wp: perform_vcpu_invocation_irq_masks[where st=st])

lemma maskVTimer_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and valid_irq_states\<rbrace>
   do_machine_op (maskInterrupt True irqVTimerEvent)
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding maskInterrupt_def
  apply (wpsimp wp: dmo_machine_state_lift)
  apply (erule_tac P=P in rsubst)
  apply (fastforce simp: domain_sep_inv_def non_kernel_IRQs_def valid_irq_states_def valid_irq_masks_def)
  done

lemma vcpu_disable_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and valid_irq_states\<rbrace>
   vcpu_disable vo
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  by (wpsimp wp: maskVTimer_irq_masks[where st=st] hoare_drop_imps dmo_machine_state_lift
           simp: vcpu_disable_def dmo_distr)

lemma vcpu_switch_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and valid_irq_states\<rbrace>
   vcpu_switch vo
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding vcpu_switch_def
  by (wpsimp wp: vcpu_disable_irq_masks[where st=st]
                 vcpu_restore_irq_masks[where st=st]
                 vcpu_enable_irq_masks[where st=st]
                 dmo_machine_state_lift)

lemma arch_switch_to_idle_thread_irq_masks[IRQMasks_IF_assms]:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and valid_irq_states\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding arch_switch_to_idle_thread_def
  by (wpsimp wp: vcpu_switch_irq_masks[where st=st])

lemma arch_switch_to_thread_irq_masks[IRQMasks_IF_assms]:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and valid_irq_states\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  unfolding arch_switch_to_thread_def
  by (wpsimp wp: vcpu_switch_irq_masks[where st=st])

crunch arch_prepare_next_domain
  for irq_masks[IRQMasks_IF_assms,wp]: "\<lambda>s. P (irq_masks_of_state s)"
  and valid_irq_states[IRQMasks_IF_assms,wp]: "valid_irq_states"
  (wp: crunch_wps)

end


global_interpretation IRQMasks_IF_2?: IRQMasks_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact IRQMasks_IF_assms)?)
qed


arch_requalify_facts
  init_arch_objects_irq_masks
  arch_activate_idle_thread_irq_masks
  retype_region_irq_masks

declare
  init_arch_objects_irq_masks[wp]
  arch_activate_idle_thread_irq_masks[wp]
  retype_region_irq_masks[wp]

end
