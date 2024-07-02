(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIRQMasks_IF
imports IRQMasks_IF
begin

context Arch begin global_naming ARM

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
     simp: crunch_simps no_irq_clearMemory
           mapM_x_def_bak unless_def)

crunch finalise_cap
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps dmo_wp no_irq
   simp: crunch_simps no_irq_setHardwareASID  no_irq_invalidateLocalTLB_ASID
         no_irq_set_current_pd no_irq_invalidateLocalTLB_VAASID no_irq_cleanByVA_PoU)

crunch send_signal
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
          | simp add: get_irq_state_def handle_reserved_irq_def
          | wp (once) hoare_drop_imp)+
  apply (fastforce simp: domain_sep_inv_def)
  done

lemma arch_invoke_irq_control_irq_masks[IRQMasks_IF_assms]:
  "\<lbrace>domain_sep_inv False st and arch_irq_control_inv_valid invok\<rbrace>
   arch_invoke_irq_control invok
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply (case_tac invok)
  apply (clarsimp simp: arch_irq_control_inv_valid_def domain_sep_inv_def valid_def)
  done

crunch handle_vm_fault, handle_hypervisor_fault
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp no_irq simp: no_irq_getDFSR no_irq_getFAR no_irq_getIFSR)

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
  apply clarsimp
  done

crunch activate_thread
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"

crunch schedule
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp crunch_wps simp: crunch_simps clearExMonitor_def)

end


global_interpretation IRQMasks_IF_1?: IRQMasks_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact IRQMasks_IF_assms)?)
qed


context Arch begin global_naming ARM

crunch do_reply_transfer
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps empty_slot_irq_masks simp: crunch_simps unless_def)

crunch arch_perform_invocation
  for irq_masks[IRQMasks_IF_assms, wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp crunch_wps no_irq
   simp: no_irq_cleanByVA_PoU no_irq_invalidateLocalTLB_ASID no_irq_do_flush)

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
      apply (wpsimp wp: hoare_vcg_all_liftE_R hoare_vcg_const_imp_lift_R hoare_vcg_all_lift hoare_drop_imps
                        checked_cap_insert_domain_sep_inv)+
      apply (rule_tac Q="\<lambda> r s. domain_sep_inv False st s \<and> P (irq_masks_of_state s)"
                  and E="\<lambda>_ s. P (irq_masks_of_state s)" in hoare_strengthen_postE)
        apply (wp hoare_vcg_conj_liftE1 cap_delete_irq_masks)
       apply fastforce
      apply blast
     apply (wpsimp wp: hoare_weak_lift_imp hoare_vcg_all_lift checked_cap_insert_domain_sep_inv)+
     apply (rule_tac Q="\<lambda> r s. domain_sep_inv False st s \<and> P (irq_masks_of_state s)"
                 and E="\<lambda>_ s. P (irq_masks_of_state s)" in hoare_strengthen_postE)
       apply (wp hoare_vcg_conj_liftE1 cap_delete_irq_masks)
      apply fastforce
     apply blast
    apply (simp add: option_update_thread_def | wp hoare_weak_lift_imp hoare_vcg_all_lift | wpc)+
  by fastforce+

end


global_interpretation IRQMasks_IF_2?: IRQMasks_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact IRQMasks_IF_assms)?)
qed


context begin interpretation Arch .

requalify_facts
  init_arch_objects_irq_masks
  arch_activate_idle_thread_irq_masks
  retype_region_irq_masks

end

declare
  init_arch_objects_irq_masks[wp]
  arch_activate_idle_thread_irq_masks[wp]
  retype_region_irq_masks[wp]

end
