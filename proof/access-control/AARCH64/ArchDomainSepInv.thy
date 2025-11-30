(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDomainSepInv
imports
  "DomainSepInv"
begin

context Arch begin arch_global_naming

named_theorems DomainSepInv_assms

crunch arch_post_cap_deletion, set_pt, set_asid_pool, init_arch_objects
  for domain_sep_inv[DomainSepInv_assms, wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv crunch_wps set_asid_pool_cte_wp_at set_pt_cte_wp_at)

crunch vcpu_update
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv crunch_wps set_asid_pool_cte_wp_at set_pt_cte_wp_at)

crunch vcpu_save_reg, vcpu_invalidate_active, dissociate_vcpu_tcb, fpu_release
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

crunch prepare_thread_delete
  for domain_sep_inv[DomainSepInv_assms, wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv crunch_wps)

crunch arch_finalise_cap
  for domain_sep_inv[DomainSepInv_assms, wp]: "domain_sep_inv irqs st"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_finalise_cap_rv[DomainSepInv_assms]:
  "\<lbrace>\<lambda>_. P (NullCap,NullCap)\<rbrace> arch_finalise_cap c x \<lbrace>\<lambda>rv _. P rv\<rbrace>"
  unfolding arch_finalise_cap_def by wpsimp

lemma arch_derive_cap_domain_sep_inv[DomainSepInv_assms, wp]:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv _. domain_sep_inv_cap irqs rv\<rbrace>,-"
  unfolding arch_derive_cap_def
  by wpsimp

lemma arch_post_modify_registers_domain_sep_inv[DomainSepInv_assms, wp]:
  "arch_post_modify_registers cur t \<lbrace>domain_sep_inv irqs st\<rbrace>"
  unfolding arch_post_modify_registers_def by wpsimp

lemma arch_thread_set_domain_sep_inv[wp]:
  "arch_thread_set f t \<lbrace>domain_sep_inv irqs st\<rbrace>"
  by (wpsimp wp: arch_thread_set_wp
           simp: domain_sep_inv_def cte_wp_at_after_update' obj_at_def get_tcb_def tcb_cap_cases_def
          split: option.splits kernel_object.splits)

crunch handle_vm_fault, handle_vm_fault, perform_pg_inv_unmap,
       perform_pg_inv_get_addr, perform_pt_inv_map, perform_pt_inv_unmap,
       handle_arch_fault_reply, arch_mask_irq_signal, arch_switch_to_thread,
       arch_switch_to_idle_thread, arch_activate_idle_thread, store_asid_pool_entry,
       arch_prepare_set_domain, arch_prepare_next_domain, arch_post_set_flags
  for domain_sep_inv[DomainSepInv_assms, wp]: "domain_sep_inv irqs st"
  (wp: crunch_wps)

end


global_interpretation DomainSepInv_1?: DomainSepInv_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact DomainSepInv_assms)?)
qed

context Arch begin arch_global_naming

crunch perform_pg_inv_map, perform_flush
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: crunch_wps simp: crunch_simps)

lemma perform_page_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_page_inv pgi\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_ s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  apply (rule hoare_pre)
   apply (wp mapM_wp[OF _ subset_refl] set_cap_domain_sep_inv mapM_x_wp[OF _ subset_refl]
             perform_page_invocation_domain_sep_inv_get_cap_helper
          | simp add: perform_page_invocation_def o_def | wpc)+
  done

lemma perform_page_table_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_pti pgi\<rbrace>
   perform_page_table_invocation pgi
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: perform_page_table_invocation_def)
   apply (wpsimp wp: perform_page_invocation_domain_sep_inv_get_cap_helper
                     crunch_wps set_cap_domain_sep_inv)
  apply (clarsimp simp: valid_pti_def)
  done

lemma perform_asid_control_invocation_domain_sep_inv:
  "perform_asid_control_invocation iv \<lbrace>domain_sep_inv irqs st\<rbrace>"
  unfolding perform_asid_control_invocation_def
  apply (rule hoare_pre)
  apply (wp modify_wp cap_insert_domain_sep_inv' set_cap_domain_sep_inv
            get_cap_domain_sep_inv_cap[where st=st] hoare_vcg_imp_lift
         | wpc | simp )+
  done

crunch perform_sgi_invocation, perform_asid_pool_invocation
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: crunch_wps)

lemma perform_vspace_invocation_domain_sep_inv[wp]:
  "perform_vspace_invocation iv \<lbrace>domain_sep_inv irqs st\<rbrace>"
  by (wpsimp simp: perform_vspace_invocation_def)

crunch invoke_vcpu_inject_irq, invoke_vcpu_read_register, invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"

lemma associate_vcpu_tcb_domain_sep_inv[wp]:
  "associate_vcpu_tcb a b \<lbrace>domain_sep_inv irqs st\<rbrace>"
  unfolding associate_vcpu_tcb_def
  by (wpsimp | wp domain_sep_inv_triv)+

lemma perform_vcpu_invocation_domain_sep_inv[wp]:
  "perform_vcpu_invocation vcpu \<lbrace>domain_sep_inv irqs st\<rbrace>"
  unfolding perform_vcpu_invocation_def
  by wpsimp

lemma arch_perform_invocation_domain_sep_inv[DomainSepInv_assms]:
  "\<lbrace>domain_sep_inv irqs st and valid_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_ s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  unfolding arch_perform_invocation_def
  apply (wpsimp wp: perform_page_table_invocation_domain_sep_inv
                    perform_page_invocation_domain_sep_inv
                    perform_asid_control_invocation_domain_sep_inv
                    perform_asid_pool_invocation_domain_sep_inv)
  apply (clarsimp simp: valid_arch_inv_def split: arch_invocation.splits)
  done

lemma arch_invoke_irq_handler_domain_sep_inv[DomainSepInv_assms, wp]:
  "arch_invoke_irq_handler ihi \<lbrace>domain_sep_inv irqs st\<rbrace>"
  by (cases ihi; wpsimp split_del: if_split)

lemma arch_invoke_irq_control_domain_sep_inv[DomainSepInv_assms]:
  "\<lbrace>domain_sep_inv irqs st and arch_irq_control_inv_valid ivk\<rbrace>
   arch_invoke_irq_control ivk
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (cases ivk; wpsimp wp: cap_insert_domain_sep_inv' simp: set_irq_state_def)
   apply (rule_tac Q'="\<lambda>_. domain_sep_inv irqs st and arch_irq_control_inv_valid ivk"
                in hoare_strengthen_post[rotated])
    apply (fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def arch_irq_control_inv_valid_def)
   apply (wpsimp wp: do_machine_op_domain_sep_inv simp: arch_irq_control_inv_valid_def)+
  done

crunch handle_reserved_irq, handle_hypervisor_fault
  for domain_sep_inv[wp]:
  "\<lambda>s :: det_state. domain_sep_inv irqs (st :: 's :: state_ext state) s"
  (wp: crunch_wps simp: crunch_simps vcpu_update_def valid_vcpu_def valid_fault_def)

\<comment> \<open>Remove the parentheses\<close>
declare handle_reserved_irq_domain_sep_inv[simplified and_assoc, DomainSepInv_assms]
declare handle_hypervisor_fault_domain_sep_inv[simplified and_assoc, DomainSepInv_assms]

end


global_interpretation DomainSepInv_2?: DomainSepInv_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact DomainSepInv_assms)?)
qed

end
