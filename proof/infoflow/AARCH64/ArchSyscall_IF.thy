(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSyscall_IF
imports Syscall_IF
begin

context Arch begin arch_global_naming

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
  apply (fastforce simp: obj_at_def get_tcb_def valid_arch_state_def
                   dest: valid_global_arch_objs_pt_at)
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
  unfolding ackInterrupt_def by wpsimp

lemma dmo_resetTimer_globals_equiv[Syscall_IF_assms, wp]:
  "do_machine_op resetTimer \<lbrace>globals_equiv s\<rbrace>"
  unfolding resetTimer_def by (rule dmo_mol_globals_equiv)

lemma arch_mask_irq_signal_globals_equiv[Syscall_IF_assms, wp]:
  "arch_mask_irq_signal irq \<lbrace>globals_equiv st\<rbrace>"
  by wpsimp

lemma vppi_update_valid_objs[wp]:
  "vcpu_update vr (\<lambda>vcpu. vcpu\<lparr>vcpu_vppi_masked := f vcpu\<rparr>) \<lbrace>valid_objs\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp simp: valid_vcpu_def)

lemma vppi_update_valid_arch_state[wp]:
  "vcpu_update vr (\<lambda>vcpu. vcpu\<lparr>vcpu_vppi_masked := f vcpu\<rparr>) \<lbrace>valid_arch_state\<rbrace>"
  unfolding vcpu_update_def
  apply (wpsimp wp: set_vcpu_valid_arch_eq_hyp get_vcpu_wp)
  apply (auto simp: obj_at_def opt_map_def vcpu_tcb_refs_def split: option.splits)
  done

lemma vgic_update_valid_objs[wp]:
  "vcpu_update vr (\<lambda>vcpu. vcpu\<lparr>vcpu_vgic := f vcpu\<rparr>) \<lbrace>valid_objs\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp simp: valid_vcpu_def)

lemma vgic_update_valid_arch_state[wp]:
  "vcpu_update vr (\<lambda>vcpu. vcpu\<lparr>vcpu_vgic := f vcpu\<rparr>) \<lbrace>valid_arch_state\<rbrace>"
  unfolding vcpu_update_def
  apply (wpsimp wp: set_vcpu_valid_arch_eq_hyp get_vcpu_wp)
  apply (auto simp: obj_at_def opt_map_def vcpu_tcb_refs_def split: option.splits)
  done

crunch vcpu_update
  for valid_global_objs[wp]: valid_global_objs
  (wp: crunch_wps  simp: crunch_simps)

lemma vppi_event_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and invs\<rbrace> vppi_event irq \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding vppi_event_def
  apply (wpsimp wp: handle_fault_globals_equiv gts_wp hoare_vcg_all_lift hoare_drop_imps
              simp: crunch_simps split_del: if_split)
  apply (auto simp: valid_fault_def)
  done

lemma vgic_maintenance_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and invs\<rbrace> vgic_maintenance \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding vgic_maintenance_def vgic_update_lr_def vgic_update_def
  apply (wpsimp wp: handle_fault_globals_equiv gts_wp hoare_vcg_all_lift hoare_drop_imps dmo_globals_equiv
         split_del: if_split simp: crunch_simps valid_fault_def)
  apply auto
  done

lemma handle_reserved_irq_globals_equiv[Syscall_IF_assms, wp]:
  "\<lbrace>globals_equiv st and invs\<rbrace> handle_reserved_irq irq \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding handle_reserved_irq_def
  by wpsimp

(* FIXME AARCH64 IF: move *)
lemma gets_compE:
  "doE x <- liftE (gets f);
      m (g x)
   odE =
   doE x <- liftE (gets (g \<circ> f));
      m x
    odE"
  by (clarsimp simp: liftE_def bind_bindE_assoc gets_def return_bindE)

definition is_subject_cur_vcpu_2 where
  "is_subject_cur_vcpu_2 aag cf \<equiv> \<forall>ptr. cf = Some (ptr,True) \<longrightarrow> is_subject aag ptr"

locale_abbrev is_subject_cur_vcpu where
  "is_subject_cur_vcpu aag \<equiv> \<lambda>s. is_subject_cur_vcpu_2 aag (arm_current_vcpu (arch_state s))"

lemmas is_subject_cur_vcpu_def = is_subject_cur_vcpu_2_def

lemma active_vcpu_is_subject:
  "\<lbrakk> pas_refined aag s; is_subject aag (cur_thread s);
     valid_cur_vcpu s; schact_is_rct s; ct_in_cur_domain s \<rbrakk>
     \<Longrightarrow> is_subject_cur_vcpu aag s"
  apply (prop_tac "arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = active_cur_vcpu_of s) (cur_thread s) s")
   apply (clarsimp simp: valid_cur_vcpu_def schact_is_rct_def)
   apply (case_tac "cur_thread s = idle_thread s")
    apply (auto simp: ct_in_cur_domain_resume_cur_thread_not_idle)[2]
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_subject_cur_vcpu_def)
  apply (clarsimp simp: active_cur_vcpu_of_def split: option.splits)
  apply (erule associated_vcpu_is_subject)
    apply (fastforce simp: get_tcb_ko_at obj_at_def)
   apply auto
  done

lemma gets_current_vcpu_reads_respects:
  "reads_respects aag l (\<lambda>s. pas_refined aag s \<and> valid_cur_vcpu s \<and> schact_is_rct s
                                               \<and> ct_in_cur_domain s \<and> is_subject aag (cur_thread s))
                        (gets ((\<lambda>a. \<exists>v. a = Some (v, True)) \<circ> (arm_current_vcpu \<circ> arch_state)))"
  (is "reads_respects aag l ?P _")
  apply (wpsimp wp: gets_ev''[where P="?P"])
   apply (prop_tac "equiv_hyp (aag_can_read aag) s t")
    apply (clarsimp simp: reads_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)
   apply (drule (4) active_vcpu_is_subject)+
   apply (clarsimp simp: equiv_hyp_def equiv_for_def is_subject_cur_vcpu_def)
   apply (rule iffI; erule ex_forward)
    apply (erule_tac x=v in allE)+
    apply (clarsimp simp: cur_vcpu_of_def split: option.splits if_splits)
   apply (erule_tac x=v in allE)+
   apply (clarsimp simp: cur_vcpu_of_def split: option.splits if_splits)
  apply simp
  done

lemma handle_vm_fault_reads_respects[Syscall_IF_assms]:
  "reads_respects aag l (pas_refined aag and valid_cur_hyp and schact_is_rct and ct_in_cur_domain
                                         and is_subject aag \<circ> cur_thread and K (is_subject aag thread))
                  (handle_vm_fault thread vmfault_type)"
  unfolding handle_vm_fault_def fun_app_def valid_cur_hyp_def
  apply (cases vmfault_type; clarsimp; subst gets_compE)
  by (wpsimp wp: gets_current_vcpu_reads_respects as_user_reads_respects
                    dmo_getESR_reads_respects dmo_getFAR_reads_respects
                    dmo_addressTranslateS1_reads_respects
              simp: det_getRestartPC)+

lemma handle_hypervisor_fault_reads_respects[Syscall_IF_assms]:
  assumes pas_domains_distinct[wp]: "pas_domains_distinct (aag :: 'a subject_label PAS)"
  shows "reads_respects aag l (invs and pas_refined aag and pas_cur_domain aag
                                    and is_subject aag \<circ> cur_thread and K (is_subject aag thread))
                              (handle_hypervisor_fault thread hypfault_type)"
  apply (cases hypfault_type)
  apply (wpsimp wp: handle_fault_reads_respects dmo_getESR_reads_respects split_del: if_split)
  apply (auto simp: valid_fault_def)
  done

lemma handle_vm_fault_globals_equiv[Syscall_IF_assms]:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>r. globals_equiv st\<rbrace>"
  unfolding handle_vm_fault_def
  by (cases vmfault_type; wpsimp wp: dmo_no_mem_globals_equiv)

lemma handle_hypervisor_fault_globals_equiv[Syscall_IF_assms]:
  "\<lbrace>globals_equiv st and invs\<rbrace> handle_hypervisor_fault thread hypfault_type \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (cases hypfault_type)
  apply (wpsimp wp: handle_fault_globals_equiv split_del: if_split)+
  apply (auto simp: valid_fault_def)
  done

crunch arch_activate_idle_thread, handle_spurious_irq
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

lemma decode_asid_pool_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_asid_pool_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding authorised_for_globals_arch_inv_def decode_asid_pool_invocation_def Let_def
  by wpsimp

lemma decode_asid_control_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_asid_control_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding authorised_for_globals_arch_inv_def decode_asid_control_invocation_def Let_def
  by wpsimp

definition is_pt_cap_typ :: "cap \<Rightarrow> pt_type \<Rightarrow> bool" where
  "is_pt_cap_typ cap pt_t \<equiv>
     arch_cap_fun_lift (\<lambda>acap. is_PageTableCap acap \<and> acap_pt_type acap = pt_t) False cap"

(* FIXME AARCH64 IF: consolidate with pt_lookup_slot_cap_to *)
lemma pt_lookup_slot_cap_to_lvl:
  "\<lbrakk> invs s; \<exists>\<rhd>(max_pt_level, pt) s; is_aligned pt (pt_bits VSRootPT_T); vptr \<in> user_region;
     pt_lookup_slot pt vptr (ptes_of s) = Some (level, slot) \<rbrakk>
   \<Longrightarrow> \<exists>p cap. caps_of_state s p = Some cap \<and> is_pt_cap_typ cap (level_type level) \<and>
               obj_refs cap = {table_base level slot} \<and> s \<turnstile> cap \<and> cap_asid cap \<noteq> None"
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (frule pt_walk_max_level)
  apply (rename_tac pt_ptr asid vref)
  apply (subgoal_tac "vs_lookup_table level asid vptr s = Some (level, pt_ptr)")
   prefer 2
   apply (drule pt_walk_level)
   apply (clarsimp simp: vs_lookup_table_def in_omonad)
  apply (frule_tac level=level in valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (drule vs_lookup_table_target[where level=level], simp)
  apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
  apply (frule (1) cap_to_pt_is_pt_cap_and_type, simp)
   apply (fastforce intro: valid_objs_caps)
  apply (frule pts_of_Some_alignedD, fastforce)
  apply (frule caps_of_state_valid, fastforce)
  apply (fastforce simp: cap_asid_def is_cap_simps is_pt_cap_typ_def)
  done

lemma decode_frame_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_frame_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding authorised_for_globals_arch_inv_def authorised_for_globals_page_inv_def
            decode_frame_invocation_def decode_fr_inv_map_def
  apply (case_tac "invocation_type label = ArchInvocationLabel ARMPageMap \<and> is_FrameCap cap")
   defer
   apply (wpsimp simp: isPageFlushLabel_def Let_def decode_fr_inv_flush_def)
  apply (simp add: is_FrameCap_def Let_def cong: arch_cap.case_cong if_cong)
  apply (wpsimp wp: check_vp_wpR whenE_throwError_wp)
  apply (prop_tac "\<not> user_vtop < msg ! 0 + mask (pageBitsForSize xb) \<longrightarrow> msg ! 0 \<in> user_region")
   apply (clarsimp simp: user_region_def not_le)
   apply (rule user_vtop_leq_canonical_user)
   apply (simp add: vmsz_aligned_def not_less)
   apply (drule is_aligned_no_overflow_mask)
   apply simp
  apply (case_tac "msg ! 0 \<in> user_region")
   prefer 2
   apply (fastforce dest: cte_wp_valid_cap simp: valid_cap_def wellformed_mapdata_def)
  apply (clarsimp simp: parent_for_refs_def cte_wp_at_caps_of_state)
  apply (frule vspace_for_asid_vs_lookup)
  using pt_lookup_slot_cap_to_lvl[where vptr="msg ! 0"]
  by (fastforce dest: vs_lookup_table_is_aligned
                simp: is_pt_cap_typ_def is_PageTableCap_def
               split: option.splits)

lemma decode_page_table_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_page_table_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding decode_page_table_invocation_def decode_pt_inv_map_def
            authorised_for_globals_arch_inv_def authorised_for_globals_page_table_inv_def
  apply (simp add: split_def Let_def cong: arch_cap.case_cong if_cong split del: if_split)
  apply (wpsimp cong: if_cong wp: hoare_vcg_if_lift2)
  apply (clarsimp simp: pt_lookup_slot_from_level_def pt_lookup_slot_def)
  apply (frule (1) pt_lookup_vs_lookupI, clarsimp)
  apply (drule vs_lookup_level)
  apply (frule pt_walk_max_level)
  apply (subgoal_tac "msg ! 0 \<in> user_region")
   apply (frule reachable_page_table_not_global; clarsimp?)
   apply (frule vs_lookup_table_is_aligned; clarsimp?)
  apply (fastforce intro: user_vtop_leq_canonical_user simp: user_region_def)
  done

lemma decode_sgi_signal_invocation_authorised_for_globals:
  "\<lbrace>\<top>\<rbrace> decode_sgi_signal_invocation cap
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding decode_sgi_signal_invocation_def authorised_for_globals_arch_inv_def
  by wpsimp

lemma decode_smc_invocation_authorised_for_globals:
  "\<lbrace>\<top>\<rbrace> decode_smc_invocation label args acap
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding decode_smc_invocation_def authorised_for_globals_arch_inv_def
  by wpsimp

lemma decode_vspace_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_vspace_invocation label msg slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding decode_vspace_invocation_def decode_vs_inv_flush_def
  by (wpsimp simp: Let_def authorised_for_globals_arch_inv_def)

lemma decode_vcpu_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   decode_vcpu_invocation label msg cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding decode_vcpu_invocation_def decode_vcpu_set_tcb_def decode_vcpu_inject_irq_def
            decode_vcpu_read_register_def decode_vcpu_write_register_def decode_vcpu_ack_vppi_def
            range_check_def arch_check_irq_def authorised_for_globals_arch_inv_def
  by (wpc | wpsimp wp: whenE_throwError_wp)+

lemma decode_arch_invocation_authorised_for_globals[Syscall_IF_assms]:
  "\<lbrace>invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
   arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>authorised_for_globals_arch_inv\<rbrace>, -"
  unfolding arch_decode_invocation_def
  by (wpsimp wp: decode_sgi_signal_invocation_authorised_for_globals
                 decode_smc_invocation_authorised_for_globals
                 decode_vspace_invocation_authorised_for_globals
                 decode_vcpu_invocation_authorised_for_globals
                 decode_asid_pool_invocation_authorised_for_globals
                 decode_asid_control_invocation_authorised_for_globals
                 decode_frame_invocation_authorised_for_globals
                 decode_page_table_invocation_authorised_for_globals, fastforce)

crunch vcpu_flush_if_current
  for globals_equiv[wp]: "globals_equiv st"
  (wp: crunch_wps simp: crunch_simps invs_arch_state)

lemma arch_prepare_set_domain_globals_equiv[Syscall_IF_assms]:
  "\<lbrace>globals_equiv st and invs\<rbrace> arch_prepare_set_domain t new_dom \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding arch_prepare_set_domain_def
  by (wpsimp wp: fpu_release_globals_equiv)

crunch arch_prepare_set_domain
  for valid_arch_state[Syscall_IF_assms,wp]: valid_arch_state
  (wp: hoare_drop_imps)

end


global_interpretation Syscall_IF_1?: Syscall_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Syscall_IF_assms)?)
qed

end
