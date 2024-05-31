(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSyscall_IF
imports Syscall_IF
begin

context Arch begin global_naming ARM

named_theorems Syscall_IF_assms

lemma globals_equiv_irq_state_update[Syscall_IF_assms, simp]:
  "globals_equiv st (s\<lparr>machine_state :=
                       machine_state s \<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   globals_equiv st s"
  by (auto simp: globals_equiv_def idle_equiv_def)

lemma thread_set_globals_equiv'[Syscall_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
   thread_set f tptr
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding thread_set_def
  apply (wp set_object_globals_equiv)
  apply simp
  apply (intro impI conjI allI)
  apply (fastforce simp: obj_at_def get_tcb_def valid_arch_state_def)+
  done

lemma sts_authorised_for_globals_inv[Syscall_IF_assms]:
  "set_thread_state d f \<lbrace>authorised_for_globals_inv oper\<rbrace>"
  unfolding authorised_for_globals_inv_def authorised_for_globals_arch_inv_def
            authorised_for_globals_page_table_inv_def authorised_for_globals_page_inv_def
  apply (case_tac oper)
           apply (wp | simp)+
  apply (rename_tac arch_invocation)
  apply (case_tac arch_invocation)
      apply simp
      apply (rename_tac page_table_invocation)
      apply (case_tac page_table_invocation)
       apply wpsimp+
    apply (rename_tac page_invocation)
    apply (case_tac page_invocation)
       apply (simp | wp hoare_vcg_ex_lift)+
  done

lemma dmo_maskInterrupt_globals_equiv[Syscall_IF_assms, wp]:
  "do_machine_op (maskInterrupt b irq) \<lbrace>globals_equiv s\<rbrace>"
  unfolding maskInterrupt_def
  apply (rule dmo_no_mem_globals_equiv)
    apply (wp modify_wp | simp)+
  done

lemma dmo_ackInterrupt_globals_equiv[Syscall_IF_assms, wp]:
  "do_machine_op (ackInterrupt irq) \<lbrace>globals_equiv s\<rbrace>"
  unfolding ackInterrupt_def by (rule dmo_mol_globals_equiv)

lemma dmo_resetTimer_globals_equiv[Syscall_IF_assms, wp]:
  "do_machine_op resetTimer \<lbrace>globals_equiv s\<rbrace>"
  unfolding resetTimer_def by (rule dmo_mol_globals_equiv)

lemma arch_mask_irq_signal_globals_equiv[Syscall_IF_assms, wp]:
  "arch_mask_irq_signal irq \<lbrace>globals_equiv st\<rbrace>"
  by wpsimp

lemma handle_reserved_irq_globals_equiv[Syscall_IF_assms, wp]:
  "handle_reserved_irq irq \<lbrace>globals_equiv st\<rbrace>"
  unfolding handle_reserved_irq_def by wpsimp

lemma handle_vm_fault_reads_respects[Syscall_IF_assms]:
  "reads_respects aag l (K (is_subject aag thread)) (handle_vm_fault thread vmfault_type)"
  apply (cases vmfault_type)
   apply (wp dmo_getDFSR_reads_respects dmo_getFAR_reads_respects
             dmo_getIFSR_reads_respects as_user_reads_respects
          | simp add: getRestartPC_def getRegister_def)+
  done

lemma handle_hypervisor_fault_reads_respects[Syscall_IF_assms]:
  "reads_respects aag l \<top> (handle_hypervisor_fault thread hypfault_type)"
  by (cases hypfault_type; wpsimp)

lemma handle_vm_fault_globals_equiv[Syscall_IF_assms]:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>r. globals_equiv st\<rbrace>"
  apply (cases vmfault_type)
   apply (wp dmo_no_mem_globals_equiv | simp add: getDFSR_def getFAR_def getIFSR_def)+
  done

lemma handle_hypervisor_fault_globals_equiv[Syscall_IF_assms]:
  "handle_hypervisor_fault thread hypfault_type \<lbrace>globals_equiv st\<rbrace>"
  by (cases hypfault_type; wpsimp)

crunches arch_activate_idle_thread
  for globals_equiv[Syscall_IF_assms, wp]: "globals_equiv st"

lemma select_f_setNextPC_reads_respects[Syscall_IF_assms, wp]:
  "reads_respects aag l \<top> (select_f (setNextPC a b))"
  unfolding setNextPC_def setRegister_def
  by (wpsimp simp: select_f_returns)

lemma select_f_getRestartPC_reads_respects[Syscall_IF_assms, wp]:
  "reads_respects aag l \<top> (select_f (getRestartPC a))"
  unfolding getRestartPC_def getRegister_def
  by (wpsimp simp: select_f_returns)

lemma arch_activate_idle_thread_reads_respects[Syscall_IF_assms, wp]:
  "reads_respects aag l \<top> (arch_activate_idle_thread t)"
  unfolding arch_activate_idle_thread_def by wpsimp

lemma decode_arch_invocation_authorised_for_globals[Syscall_IF_assms]:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding arch_decode_invocation_def authorised_for_globals_arch_inv_def
  apply (rule hoare_pre)
   apply (simp add: split_def Let_def
               cong: cap.case_cong arch_cap.case_cong if_cong option.case_cong
               split del: if_split)
   apply (wp select_ext_weak_wp whenE_throwError_wp check_vp_wpR unlessE_wp get_pde_wp
             get_master_pde_wp find_pd_for_asid_authority3 create_mapping_entries_parent_for_refs
          | wpc
          | simp add: authorised_for_globals_page_inv_def
                 del: hoareE_R_TrueI)+
     apply (simp cong: if_cong)
     apply (wp hoare_vcg_if_lift2)
     apply (rule hoare_conjI)
      apply (rule hoare_drop_imps)
      apply (simp add: authorised_for_globals_page_table_inv_def)
      apply wp
     apply (rule hoare_drop_imps)
     apply wp
    apply ((wp hoare_TrueI hoare_vcg_all_lift hoare_drop_imps | wpc | simp)+)[3]
  apply (clarsimp simp: authorised_asid_pool_inv_def authorised_page_table_inv_def
                        neq_Nil_conv invs_psp_aligned invs_vspace_objs cli_no_irqs)
  apply (drule cte_wp_valid_cap, clarsimp+)
  apply (cases cap, simp_all)
    \<comment> \<open>PageCap\<close>
    apply (clarsimp simp: valid_cap_simps cli_no_irqs)
    apply (cases "invocation_type label";
           (rename_tac arch, case_tac arch; simp add: isPageFlushLabel_def isPDFlushLabel_def))
          \<comment> \<open>Map\<close>
          apply (rename_tac word cap_rights vmpage_size option arch)
          apply (clarsimp simp: isPageFlushLabel_def isPDFlushLabel_def | rule conjI)+
            apply (drule cte_wp_valid_cap)
             apply (clarsimp simp: invs_def valid_state_def)
            apply (simp add: valid_cap_def)
           apply (simp add: vmsz_aligned_def)
           apply (drule_tac ptr="msg ! 0" and off="2 ^ pageBitsForSize vmpage_size - 1"
                         in is_aligned_no_wrap')
            apply (insert pbfs_less_wb')
            apply (clarsimp)
           apply (fastforce simp: x_power_minus_1)
          apply (clarsimp)
          apply (fastforce dest: cte_wp_valid_cap simp: invs_def valid_state_def valid_cap_def)
         \<comment> \<open>Unmap\<close>
         apply (simp add: authorised_for_globals_page_inv_def)+
   apply (clarsimp)
   \<comment> \<open>PageTableCap\<close>
   apply (clarsimp simp: authorised_for_globals_page_table_inv_def)
   apply (frule_tac vptr="msg ! 0" in pd_shifting')
   apply (clarsimp simp: invs_def valid_state_def valid_global_refs_def valid_refs_def global_refs_def)
   apply (erule_tac x=aa in allE)
   apply (erule_tac x=b in allE)
   apply (drule_tac P'="\<lambda>c. idle_thread s \<in> cap_range c
                          \<or> arm_global_pd (arch_state s) \<in> cap_range c
                          \<or> (range (interrupt_irq_node s) \<union> set (arm_global_pts (arch_state s)))
                             \<inter> cap_range c \<noteq> {}" in cte_wp_at_weakenE)
    apply (auto simp: cap_range_def)
  done

end


global_interpretation Syscall_IF_1?: Syscall_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Syscall_IF_assms)?)
qed

end
