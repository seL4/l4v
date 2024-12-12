(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDomainSepInv
imports
  "DomainSepInv"
begin

context Arch begin global_naming ARM_A

named_theorems DomainSepInv_assms

crunch arch_post_cap_deletion, set_pd, set_pt, set_asid_pool, prepare_thread_delete, init_arch_objects
  for domain_sep_inv[DomainSepInv_assms, wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv crunch_wps set_asid_pool_cte_wp_at set_pd_cte_wp_at set_pt_cte_wp_at)

crunch arch_finalise_cap
  for domain_sep_inv[DomainSepInv_assms, wp]: "domain_sep_inv irqs st"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_finalise_cap_rv[DomainSepInv_assms]:
  "\<lbrace>\<lambda>_. P (NullCap,NullCap)\<rbrace> arch_finalise_cap c x \<lbrace>\<lambda>rv _. P rv\<rbrace>"
  unfolding arch_finalise_cap_def by wpsimp

crunch
  invalidate_tlb_by_asid, handle_reserved_irq, handle_vm_fault,
  handle_hypervisor_fault, handle_arch_fault_reply, arch_mask_irq_signal,
  arch_switch_to_thread, arch_switch_to_idle_thread, arch_activate_idle_thread
  for domain_sep_inv[DomainSepInv_assms, wp]: "domain_sep_inv irqs st"

lemma arch_derive_cap_domain_sep_inv[DomainSepInv_assms, wp]:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv _. domain_sep_inv_cap irqs rv\<rbrace>,-"
  unfolding arch_derive_cap_def
  by wpsimp

lemma arch_post_modify_registers_domain_sep_inv[DomainSepInv_assms, wp]:
  "arch_post_modify_registers cur x31 \<lbrace>domain_sep_inv irqs st\<rbrace>"
  unfolding arch_post_modify_registers_def by wpsimp

end


global_interpretation DomainSepInv_1?: DomainSepInv_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact DomainSepInv_assms)
qed


context Arch begin global_naming ARM_A

lemma perform_page_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_page_inv pgi\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (rule hoare_pre)
   apply (wp mapM_wp[OF _ subset_refl] set_cap_domain_sep_inv mapM_x_wp[OF _ subset_refl]
             perform_page_invocation_domain_sep_inv_get_cap_helper hoare_weak_lift_imp
          | simp add: perform_page_invocation_def o_def | wpc)+
  apply (clarsimp simp: valid_page_inv_def)
  apply (case_tac xa, simp_all add: domain_sep_inv_cap_def is_pg_cap_def)
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
  apply (case_tac x, simp_all add: domain_sep_inv_cap_def is_pt_cap_def)
  done

lemma perform_page_directory_invocation_domain_sep_inv:
  "perform_page_directory_invocation pti \<lbrace>domain_sep_inv irqs st\<rbrace>"
  apply (simp add: perform_page_directory_invocation_def)
  apply (cases pti)
   apply (simp | wp)+
  done

lemma perform_asid_control_invocation_domain_sep_inv:
  "perform_asid_control_invocation iv \<lbrace>domain_sep_inv irqs st\<rbrace>"
  unfolding perform_asid_control_invocation_def
  apply (rule hoare_pre)
  apply (wp modify_wp cap_insert_domain_sep_inv' set_cap_domain_sep_inv
            get_cap_domain_sep_inv_cap[where st=st] hoare_weak_lift_imp
         | wpc | simp )+
  done

lemma perform_asid_pool_invocation_domain_sep_inv:
  "perform_asid_pool_invocation iv \<lbrace>domain_sep_inv irqs st\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (rule hoare_pre)
  apply (wp set_cap_domain_sep_inv get_cap_wp | wpc | simp)+
  done

lemma arch_perform_invocation_domain_sep_inv[DomainSepInv_assms]:
  "\<lbrace>domain_sep_inv irqs st and valid_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding arch_perform_invocation_def
  apply (wpsimp wp: perform_page_table_invocation_domain_sep_inv
                    perform_page_directory_invocation_domain_sep_inv
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
  apply (cases ivk)
  apply (wpsimp wp: cap_insert_domain_sep_inv' simp: set_irq_state_def)
   apply (rule_tac Q'="\<lambda>_. domain_sep_inv irqs st and arch_irq_control_inv_valid ivk"
                in hoare_strengthen_post[rotated])
    apply (fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def arch_irq_control_inv_valid_def)
   apply (wpsimp wp: do_machine_op_domain_sep_inv simp: arch_irq_control_inv_valid_def)+
  done

end


global_interpretation DomainSepInv_2?: DomainSepInv_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; wpsimp wp: DomainSepInv_assms)
qed

end
