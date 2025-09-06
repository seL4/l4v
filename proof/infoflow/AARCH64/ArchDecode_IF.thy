(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDecode_IF
imports Decode_IF
begin

context Arch begin global_naming AARCH64

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
  unfolding arch_decode_irq_control_invocation_def arch_check_irq_def
  apply (wp ensure_empty_rev lookup_slot_for_cnode_op_rev
            is_irq_active_rev whenE_inv
         | wp (once) hoare_drop_imps
         | simp add: Let_def)+
  apply safe
       apply simp+
    apply (blast intro: aag_Control_into_owns_irq )
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


context Arch begin global_naming AARCH64

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

lemma decode_asid_pool_invocation_reads_respects_f:
  notes reads_respects_f_inv' = reads_respects_f_inv[where st=st]
  notes whenE_wps[wp_split del]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and invs and pas_refined aag and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
                        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
                        and K (cap = ASIDPoolCap x xa)
                        and K (\<forall>(cap, slot) \<in> {(cap.ArchObjectCap cap, slot)} \<union> set excaps.
                                 aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                 is_subject aag (fst slot) \<and>
                                 (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))
        (decode_asid_pool_invocation label args slot cap excaps)"
  unfolding decode_asid_pool_invocation_def
  apply (rule equiv_valid_guard_imp)
   apply (subst gets_applyE)+
   apply (wp check_vp_wpR
             reads_respects_f_inv'[OF get_asid_pool_rev]
              gets_apply_ev
             select_ext_ev_bind_lift
           | wpc
           | simp add: Let_def unlessE_whenE
           | wp (once) whenE_throwError_wp)+
  apply (intro impI allI conjI)
   apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq')
     apply fastforce
    apply (simp add: reads_equiv_f_def)
   apply blast
  apply (fastforce simp: aag_cap_auth_ASIDPoolCap)
  done

lemma decode_asid_control_invocation_reads_respects_f:
  notes reads_respects_f_inv' = reads_respects_f_inv[where st=st]
  notes whenE_wps[wp_split del]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and invs and pas_refined aag and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
                        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
                        and K (cap = ASIDControlCap)
                        and K (\<forall>(cap, slot) \<in> {(cap.ArchObjectCap cap, slot)} \<union> set excaps.
                                 aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                 is_subject aag (fst slot) \<and>
                                 (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))
        (decode_asid_control_invocation label args slot cap excaps)"
  unfolding decode_asid_control_invocation_def
  apply (rule equiv_valid_guard_imp)
   apply (wp check_vp_wpR  reads_respects_f_inv'[OF get_asid_pool_rev]
             reads_respects_f_inv'[OF ensure_empty_rev]
             reads_respects_f_inv'[OF lookup_slot_for_cnode_op_rev]
             reads_respects_f_inv'[OF ensure_no_children_rev]
             reads_respects_f_inv'[OF lookup_error_on_failure_rev]
              gets_apply_ev
             is_final_cap_reads_respects
             select_ext_ev_bind_lift
             select_ext_ev_bind_lift[simplified]
          | wpc
          | simp add: Let_def unlessE_whenE
          | wp (once) whenE_throwError_wp)+
  apply clarsimp
  apply (prop_tac "excaps ! Suc 0 \<in> set excaps", fastforce)
  apply (drule_tac x="excaps ! Suc 0" in bspec, assumption)
  apply (frule_tac x="excaps ! Suc 0" in bspec, assumption)
  apply (drule_tac x="excaps ! 0" in bspec, fastforce intro!: bang_0_in_set)
  apply (intro impI allI conjI)
     apply (fastforce intro: pas_cap_cur_auth_ASIDControlCap[where aag=aag] simp: reads_equiv_f_def)
    apply fastforce
   apply (fastforce intro: owns_cnode_owns_obj_ref_of_child_cnodes[where slot="snd (excaps ! (Suc 0))"])
  apply clarify
  apply (rule_tac cap="fst (excaps ! Suc 0)" and p="snd (excaps ! Suc 0)" in caps_of_state_pasObjectAbs_eq)
      apply (rule cte_wp_at_caps_of_state')
      apply fastforce
     apply (erule cap_auth_conferred_cnode_cap)
    apply fastforce
   apply assumption
  apply fastforce
  done

lemma decode_frame_invocation_reads_respects_f:
  notes reads_respects_f_inv' = reads_respects_f_inv[where st=st]
  notes whenE_wps[wp_split del]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and invs and pas_refined aag and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
                        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
                        and K (cap = FrameCap p R sz dev m)
                        and K (\<forall>(cap, slot) \<in> {(cap.ArchObjectCap cap, slot)} \<union> set excaps.
                                 aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                 is_subject aag (fst slot) \<and>
                                 (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))
        (decode_frame_invocation label args slot cap excaps)"
  unfolding decode_frame_invocation_def decode_fr_inv_map_def
            check_slot_def check_vp_alignment_def gets_the_def
  supply gets_the_ev[wp del]
  apply (rule equiv_valid_guard_imp)
   apply ((wp gets_ev' check_vp_wpR  reads_respects_f_inv'[OF get_asid_pool_rev]
              reads_respects_f_inv'[OF ensure_empty_rev]
              reads_respects_f_inv'[OF get_pte_rev]
              reads_respects_f_inv'[OF lookup_slot_for_cnode_op_rev]
              reads_respects_f_inv'[OF ensure_no_children_rev]
              reads_respects_f_inv'[OF lookup_error_on_failure_rev]
              find_vspace_for_asid_reads_respects
              is_final_cap_reads_respects
              select_ext_ev_bind_lift
              select_ext_ev_bind_lift[simplified]
           | wpc
           | simp add: Let_def unlessE_whenE
           | wp (once) whenE_throwError_wp)+)[1]
  apply clarsimp
  apply (drule_tac x="excaps ! 0" in bspec, fastforce intro: bang_0_in_set)+
  apply (intro conjI; clarsimp)
   apply (fastforce dest: cte_wp_valid_cap simp: valid_cap_def wellformed_mapdata_def)
  apply (prop_tac "args ! 0 \<in> user_region")
   apply (drule not_le_imp_less)
   apply (frule order.strict_implies_order[where b=user_vtop])
   apply (drule order.strict_trans[OF _ user_vtop_pptr_base])
   apply (drule canonical_below_pptr_base_user)
    apply (erule below_user_vtop_canonical)
   apply (clarsimp simp: user_region_def)
   apply (drule is_aligned_no_overflow_mask)
   apply (erule (1) dual_order.trans)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: reads_equiv_f_def)
   apply (frule vspace_for_asid_vs_lookup)
   apply (frule_tac pt=xa and level=max_pt_level and bot_level=0 in pt_walk_reads_equiv,
          (fastforce dest: aag_has_Control_iff_owns
                     elim: vs_lookup_table_vref_independent
                     simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                           pt_lookup_slot_def pt_lookup_slot_from_level_def obind_def
                    split: option.splits)+)[1]
  apply (subgoal_tac "is_subject aag (table_base bb)", clarsimp)
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def vspace_for_asid_def)
  apply (frule pt_walk_is_aligned)
   apply (erule (1) vspace_for_pool_is_aligned[OF _ _ user_region0]; clarsimp)
  apply clarsimp
  apply (erule_tac asid=a in pt_walk_is_subject[rotated 4]; clarsimp?)
   apply (clarsimp simp: vs_lookup_table_def in_omonad)
  apply (fastforce intro: vspace_for_asid_is_subject simp: vspace_for_asid_def in_omonad)
  done

lemma decode_page_table_invocation_reads_respects_f:
  notes reads_respects_f_inv' = reads_respects_f_inv[where st=st]
  notes whenE_wps[wp_split del]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and invs and pas_refined aag and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
                        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
                        and K (cap = PageTableCap p m)
                        and K (\<forall>(cap, slot) \<in> {(cap.ArchObjectCap cap, slot)} \<union> set excaps.
                                 aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                 is_subject aag (fst slot) \<and>
                                 (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))
        (decode_page_table_invocation label args slot cap excaps)"
  unfolding decode_page_table_invocation_def decode_pt_inv_map_def gets_the_def
  supply gets_the_ev[wp del]
  apply (rule equiv_valid_guard_imp)
   apply ((wp gets_ev' check_vp_wpR reads_respects_f_inv'[OF get_asid_pool_rev]
              reads_respects_f_inv'[OF ensure_empty_rev]
              reads_respects_f_inv'[OF get_pte_rev]
              reads_respects_f_inv'[OF lookup_slot_for_cnode_op_rev]
              reads_respects_f_inv'[OF ensure_no_children_rev]
              reads_respects_f_inv'[OF lookup_error_on_failure_rev]
              find_vspace_for_asid_reads_respects
              is_final_cap_reads_respects
              select_ext_ev_bind_lift
              select_ext_ev_bind_lift[simplified]
           | simp add: Let_def unlessE_whenE if_fun_split
           | wpc
           | wp (once) whenE_throwError_wp hoare_drop_imps)+)[1]
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (drule_tac x="excaps ! 0" in bspec, fastforce intro: bang_0_in_set)+
   apply (prop_tac "args ! 0 \<in> user_region")
    apply (drule not_le_imp_less)
    apply (frule order.strict_implies_order[where b=user_vtop])
    apply (drule order.strict_trans[OF _ user_vtop_pptr_base])
    apply (drule canonical_below_pptr_base_user)
     apply (erule below_user_vtop_canonical)
    apply (clarsimp simp: user_region_def)
   apply clarsimp
   apply (intro conjI impI allI; clarsimp)
     apply (fastforce dest: cte_wp_valid_cap simp: valid_cap_def wellformed_mapdata_def)
    apply (clarsimp simp: reads_equiv_f_def)
    apply (frule vspace_for_asid_vs_lookup)
    apply (frule_tac pt=xa and level=max_pt_level and bot_level=0 in pt_walk_reads_equiv,
           (fastforce dest: aag_has_Control_iff_owns
                      elim: vs_lookup_table_vref_independent
                      simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                            pt_lookup_slot_def pt_lookup_slot_from_level_def obind_def
                     split: option.splits)+)[1]
   apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def vspace_for_asid_def)
   apply (frule pt_walk_is_aligned)
    apply (erule (1) vspace_for_pool_is_aligned[OF _ _ user_region0]; clarsimp)
   apply clarsimp
   apply (erule_tac asid=a in pt_walk_is_subject[rotated 4]; clarsimp?)
    apply (clarsimp simp: vs_lookup_table_def in_omonad)
   apply (fastforce intro: vspace_for_asid_is_subject simp: vspace_for_asid_def in_omonad)
  apply (rule conjI, fastforce elim!: is_subject_not_silc_inv)+
  apply (clarsimp simp: reads_equiv_f_def)
  apply (erule reads_equivE)
  apply (clarsimp simp: equiv_asids_def equiv_asid_def)
  apply (erule_tac x=a in allE)
  apply (fastforce simp: vspace_for_asid_def pool_for_asid_def vspace_for_pool_def
                         asid_pools_of_ko_at obj_at_def obind_def opt_map_def
                  split: option.splits)
  done

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
  apply (cases cap; rule equiv_valid_guard_imp)
  by (wpsimp wp: decode_asid_pool_invocation_reads_respects_f
                 decode_asid_control_invocation_reads_respects_f
                 decode_frame_invocation_reads_respects_f
                 decode_page_table_invocation_reads_respects_f | fastforce)+

end


global_interpretation Decode_IF_2?: Decode_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Decode_IF_assms)?)
qed

end
