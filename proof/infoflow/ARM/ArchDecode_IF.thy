(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDecode_IF
imports Decode_IF
begin

context Arch begin global_naming ARM

named_theorems Decode_IF_assms

lemma data_to_obj_type_rev[Decode_IF_assms]:
  "reads_equiv_valid_inv A aag \<top> (data_to_obj_type type)"
  unfolding data_to_obj_type_def fun_app_def arch_data_to_obj_type_def
  apply (wp | wpc)+
  apply simp
  done

lemma check_valid_ipc_buffer_rev[Decode_IF_assms]:
  "reads_equiv_valid_inv A aag \<top> (check_valid_ipc_buffer vptr cap)"
  unfolding check_valid_ipc_buffer_def fun_app_def
  apply (rule equiv_valid_guard_imp)
   apply (wpc | wp)+
  apply simp
  done

lemma arch_check_irq_rev[Decode_IF_assms, wp]:
  "reads_equiv_valid_inv A aag \<top> (arch_check_irq irq)"
  unfolding arch_check_irq_def
  apply (rule equiv_valid_guard_imp)
   apply wpsimp+
  done

lemma vspace_cap_rights_to_auth_mono[Decode_IF_assms]:
  "R \<subseteq> S \<Longrightarrow> vspace_cap_rights_to_auth R \<subseteq> vspace_cap_rights_to_auth S"
  by (auto simp: vspace_cap_rights_to_auth_def)

lemma arch_decode_irq_control_invocation_rev[Decode_IF_assms]:
  "reads_equiv_valid_inv A aag
     (pas_refined aag and
      K (is_subject aag (fst slot) \<and> (\<forall>cap\<in>set caps. pas_cap_cur_auth aag cap) \<and>
      (args \<noteq> [] \<longrightarrow> (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0))) \<in> pasPolicy aag)))
     (arch_decode_irq_control_invocation label args slot caps)"
  unfolding arch_decode_irq_control_invocation_def arch_check_irq_def range_check_def unlessE_whenE
  apply (wp ensure_empty_rev lookup_slot_for_cnode_op_rev
            is_irq_active_rev whenE_inv
         | wp (once) hoare_drop_imps
         | simp add: Let_def)+
  apply (safe; simp?)
      apply (blast intro: aag_Control_into_owns_irq)
     apply (drule_tac x="caps ! 0" in bspec)
      apply (fastforce intro: bang_0_in_set)
     apply (drule (1) is_cnode_into_is_subject; blast dest: prop_of_obj_ref_of_cnode_cap)
    apply (fastforce dest: is_cnode_into_is_subject intro: bang_0_in_set)
   apply (drule_tac x="caps ! 0" in bspec)
    apply (fastforce intro: bang_0_in_set)
   apply (drule (1) is_cnode_into_is_subject; blast dest: prop_of_obj_ref_of_cnode_cap)
  apply (fastforce dest: is_cnode_into_is_subject intro: bang_0_in_set)
  done

requalify_facts check_valid_ipc_buffer_inv

end


global_interpretation Decode_IF_1?: Decode_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Decode_IF_assms)?)
qed


context Arch begin global_naming ARM

lemma ensure_safe_mapping_reads_respects:
  "reads_respects aag l (K (authorised_slots aag entries)) (ensure_safe_mapping entries)"
  apply (rule gen_asm_ev)
  apply (case_tac entries)
   apply (rename_tac a, case_tac a)
   apply (rename_tac aa b, case_tac aa)
     apply (fastforce intro: returnOk_ev_pre)
    apply (rule equiv_valid_guard_imp)
     apply (wp mapME_x_ev' get_master_pte_reads_respects get_pte_reads_respects | wpc | simp)+
    apply (clarsimp simp: authorised_slots_def)
   apply simp
   apply (rule equiv_valid_guard_imp)
    apply (wp mapME_x_ev' get_master_pte_reads_respects | wpc | simp)+
   apply (fastforce simp: authorised_slots_def)
  apply (rename_tac b, case_tac b)
  apply (rename_tac a ba, case_tac a)
     apply (fastforce intro: returnOk_ev)
    apply simp
    apply (rule fail_ev)
   apply simp
   apply (rule equiv_valid_guard_imp)
    apply (wp mapME_x_ev' get_master_pde_reads_respects | wpc | simp)+
   apply (fastforce simp: authorised_slots_def)
  apply simp
  apply (rule equiv_valid_guard_imp)
   apply (wp mapME_x_ev' get_master_pde_reads_respects | wpc | simp)+
  apply (fastforce simp: authorised_slots_def)
  done

lemma lookup_pt_slot_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits)))
                         (lookup_pt_slot pd vptr)"
  apply (simp add: lookup_pt_slot_def lookup_pd_slot_def)
  apply (wp get_pde_rev | wpc | simp)+
  done

lemma create_mapping_entries_rev:
  "reads_equiv_valid_inv A aag (K (typ \<in> {ARMSmallPage,ARMLargePage}
                                   \<longrightarrow> is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits)))
                         (create_mapping_entries bast vptr typ vm_rights attrib pd)"
  apply (rule gen_asm_ev)
  apply (case_tac "typ")
     apply (wp lookup_error_on_failure_rev lookup_pt_slot_rev | simp)+
  done

lemma check_vp_alignment_rev:
  "reads_equiv_valid_inv A aag \<top> (check_vp_alignment sz vptr)"
  unfolding check_vp_alignment_def
  by (wp | simp add: crunch_simps split del: if_split)+

lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq'':
  "\<lbrakk> \<forall>asid. is_subject_asid aag asid; reads_equiv aag s t; pas_refined aag x \<rbrakk>
     \<Longrightarrow> arm_asid_table (arch_state s) (asid_high_bits_of base) =
         arm_asid_table (arch_state t) (asid_high_bits_of base)"
  apply (subgoal_tac "asid_high_bits_of 0 = asid_high_bits_of 1")
   apply (case_tac "base = 0")
    apply (subgoal_tac "is_subject_asid aag 1")
     apply ((auto intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq) |
            (auto simp: asid_high_bits_of_def asid_low_bits_def))+
  done

lemma pas_cap_cur_auth_ASIDControlCap:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap ASIDControlCap); reads_equiv aag s t; pas_refined aag x \<rbrakk>
     \<Longrightarrow> arm_asid_table (arch_state s) = arm_asid_table (arch_state t)"
  apply (rule ext)
  apply (subst asid_high_bits_of_shift[symmetric])
  apply (subst (3) asid_high_bits_of_shift[symmetric])
  apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq'')
    apply (clarsimp simp: aag_cap_auth_def cap_links_asid_slot_def label_owns_asid_slot_def)
    apply (rule pas_refined_Control_into_is_subject_asid, blast+)
  done

lemma resolve_vaddr_reads_respects:
  "reads_respects aag l
     (K (is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits)) and
        (\<lambda>s. case kheap s (lookup_pd_slot pd vptr && ~~ mask pd_bits) of
               Some (ArchObj (PageDirectory pd')) \<Rightarrow>
               (case pd' (ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2)) of
                  PageTablePDE x y z \<Rightarrow> is_subject aag (lookup_pt_slot_no_fail (ptrFromPAddr x) vptr && ~~ mask pt_bits)
                | _ \<Rightarrow> True)
             | _ \<Rightarrow> True))
     (resolve_vaddr pd vptr)"
  apply (simp add: resolve_vaddr_def
         | wp get_master_pte_reads_respects get_master_pde_reads_respects get_master_pde_wp | wpc)+
  apply (fastforce simp: obj_at_def split: pde.splits)
  done

lemma lookup_pt_slot_no_fail_is_subject:
  "\<lbrakk> (\<exists>\<rhd> pd) s; valid_vspace_objs s; pspace_aligned s; pas_refined aag s;
     is_subject aag pd; is_aligned pd pd_bits; vptr < kernel_base;
     kheap s pd = Some (ArchObj (PageDirectory pdo)); pdo (ucast (vptr >> 20)) = PageTablePDE p x xa \<rbrakk>
     \<Longrightarrow> is_subject aag (lookup_pt_slot_no_fail (ptrFromPAddr p) vptr && ~~ mask pt_bits)"
  apply (clarsimp simp: lookup_pt_slot_no_fail_def)
  apply (drule valid_vspace_objsD)
    apply (simp add: obj_at_def)
   apply assumption
  apply (drule kheap_eq_state_vrefs_pas_refinedD)
    apply (erule vs_refs_no_global_pts_pdI)
    apply (drule(1) less_kernel_base_mapping_slots)
    apply (simp add: kernel_mapping_slots_def lookup_pd_slot_def pd_shifting_dual' triple_shift_fun)
   apply assumption
  apply (simp add: aag_has_Control_iff_owns)
  apply (drule_tac f="\<lambda>pde. valid_pde pde s" in arg_cong, simp)
  apply (clarsimp simp: obj_at_def kernel_base_kernel_mapping_slots)
  apply (erule pspace_alignedE, erule domI)
  apply (simp add: pt_bits_def pageBits_def)
  apply (subst is_aligned_add_helper, assumption)
   apply (rule shiftl_less_t2n)
    apply (rule order_le_less_trans, rule word_and_le1, simp)
   apply simp
  apply simp
  done

lemma decode_sgi_signal_invocation_reads_respects_f[wp]:
  "reads_respects_f aag l \<top> (decode_sgi_signal_invocation (SGISignalCap irq target))"
  by (wpsimp simp: decode_sgi_signal_invocation_def)

lemma arch_decode_invocation_reads_respects_f[Decode_IF_assms]:
  notes reads_respects_f_inv' = reads_respects_f_inv[where st=st]
  notes whenE_wps[wp_split del]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and invs and pas_refined aag and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
                        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
                        and K (\<forall>(cap, slot) \<in> {(cap.ArchObjectCap cap, slot)} \<union> set excaps.
                                 aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                 is_subject aag (fst slot) \<and>
                                 (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))
        (arch_decode_invocation label args cap_index slot cap excaps)"
  unfolding arch_decode_invocation_def
  apply (rule equiv_valid_guard_imp)
   apply (subst gets_applyE)+
   apply (wp check_vp_wpR  reads_respects_f_inv'[OF get_asid_pool_rev]
             reads_respects_f_inv'[OF ensure_empty_rev]
             reads_respects_f_inv'[OF lookup_slot_for_cnode_op_rev]
             reads_respects_f_inv'[OF ensure_no_children_rev]
             reads_respects_f_inv'[OF ensure_safe_mapping_reads_respects]
             reads_respects_f_inv'[OF resolve_vaddr_reads_respects]
             reads_respects_f_inv'[OF create_mapping_entries_rev]
             reads_respects_f_inv'[OF check_vp_alignment_rev]
             reads_respects_f_inv'[OF lookup_error_on_failure_rev]
             find_pd_for_asid_reads_respects gets_apply_ev
             reads_respects_f_inv'[OF get_master_pde_reads_respects]
             is_final_cap_reads_respects find_pd_for_asid_authority2
             select_ext_ev_bind_lift
             select_ext_ev_bind_lift[simplified]
          | wpc
          | simp add: Let_def unlessE_whenE
          | wp (once) whenE_throwError_wp)+
  apply (intro impI allI conjI)
                              apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq')
                                apply fastforce
                               apply (simp add: reads_equiv_f_def)
                              apply blast
                             apply (fastforce simp: aag_cap_auth_ASIDPoolCap)
                            apply (rule pas_cap_cur_auth_ASIDControlCap[where aag=aag])
                              apply fastforce
                             apply (simp add: reads_equiv_f_def)
                            apply blast
                           apply clarify
                           apply (subgoal_tac "excaps ! 0 \<in> set excaps", fastforce)
                           apply (rule nth_mem)
                            apply (erule less_trans[rotated], simp)
                          apply (subgoal_tac "excaps ! (Suc 0) \<in> set excaps")
                           apply (rule_tac slot="snd (excaps ! (Suc 0))"
                                        in owns_cnode_owns_obj_ref_of_child_cnodes)
                              apply blast
                             apply (fastforce)
                            apply (fastforce)
                           apply assumption
                          apply (fastforce intro: nth_mem)
                         apply clarify
                         apply (subgoal_tac "excaps ! Suc 0 \<in> set excaps")
                          apply (rule_tac cap="fst (excaps ! Suc 0)" and p="snd (excaps ! Suc 0)"
                                       in caps_of_state_pasObjectAbs_eq)
                              apply (rule cte_wp_at_caps_of_state')
                              apply fastforce
                             apply (erule cap_auth_conferred_cnode_cap)
                            apply fastforce
                           apply assumption
                          apply (fastforce intro: nth_mem)
                         apply (fastforce intro: nth_mem)
                        apply (subgoal_tac "excaps ! 0 \<in> set excaps")
                         apply (fastforce intro: aag_cap_auth_PageDirectoryCap_asid)
                        apply fastforce
                       apply (simp add: lookup_pd_slot_def)
                       apply (subgoal_tac "excaps ! 0 \<in> set excaps")
                        apply (subst vaddr_segment_nonsense)
                         apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                          simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                        apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
                       apply fastforce
                      apply (simp add: lookup_pd_slot_def)
                      apply (subgoal_tac "excaps ! 0 \<in> set excaps")
                       apply (subst vaddr_segment_nonsense)
                        apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                         simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                       apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
                      apply fastforce
                     apply fastforce
                    apply (subgoal_tac "excaps ! 0 \<in> set excaps")
                     apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
                    apply fastforce
                   apply fastforce
                  apply (simp add: linorder_not_le aligned_sum_less_kernel_base)
                 apply (rule ball_subset[OF _ vspace_cap_rights_to_auth_mask_vm_rights])
                 apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
                apply (simp add: lookup_pd_slot_def)
                apply (subgoal_tac "excaps ! 0 \<in> set excaps")
                 apply (subst vaddr_segment_nonsense)
                  apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                   simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                 apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
                apply fastforce
               apply (simp add: lookup_pd_slot_def)
               apply (subgoal_tac "excaps ! 0 \<in> set excaps")
                apply (subst vaddr_segment_nonsense)
                 apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                  simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
               apply fastforce
              apply fastforce
             apply (subgoal_tac "excaps ! 0 \<in> set excaps")
              apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
             apply fastforce
            apply fastforce
           apply (fastforce dest: cte_wp_valid_cap simp: valid_cap_simps)
          apply (rule ball_subset[OF _ vspace_cap_rights_to_auth_mask_vm_rights])
          apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
         apply (subgoal_tac "excaps ! 0 \<in> set excaps")
          apply (fastforce intro: aag_cap_auth_PageDirectoryCap_asid)
         apply fastforce
        apply (subgoal_tac "excaps ! 0 \<in> set excaps")
         apply (subst vaddr_segment_nonsense)
          apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                           simp: obj_ref_of_def cap_aligned_def cap_bits_def)
         apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
        apply fastforce
       apply blast
      apply blast
     apply (blast dest: aag_can_read_self)
    apply (force dest: silc_inv_not_subject)
   apply (simp add: lookup_pd_slot_def)
   apply (subst vaddr_segment_nonsense)
    apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                     simp: obj_ref_of_def cap_aligned_def cap_bits_def)
   apply (fastforce dest: aag_cap_auth_PageDirectoryCap)
  apply (clarsimp simp: lookup_pd_slot_def
                 split: option.splits kernel_object.splits arch_kernel_obj.splits pde.splits)
  apply (subst (asm) vaddr_segment_nonsense)
   apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                    simp: obj_ref_of_def cap_aligned_def cap_bits_def)
  apply (subst(asm) vaddr_segment_nonsense2)
   apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                    simp: obj_ref_of_def cap_aligned_def cap_bits_def)
  apply (rule_tac pd=x and s=s in lookup_pt_slot_no_fail_is_subject)
          apply (erule exI)
         apply (simp add: invs_def valid_state_def)
        apply (simp add: invs_def valid_state_def valid_pspace_def)
       apply assumption
      apply (erule(1) aag_cap_auth_PageDirectoryCap)
     apply (fastforce dest: cte_wp_valid_cap cap_aligned_valid
                      simp: obj_ref_of_def cap_aligned_def cap_bits_def pd_bits)
    apply simp
   apply assumption
  apply assumption
  done

end


global_interpretation Decode_IF_2?: Decode_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Decode_IF_assms)?)
qed

end
