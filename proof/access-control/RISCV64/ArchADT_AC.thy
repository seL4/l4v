(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchADT_AC
imports ADT_AC
begin

context Arch begin global_naming RISCV64

named_theorems ADT_AC_assms

lemma mask_ptTranslationBits_ucast_ucast:
  "(asid && mask ptTranslationBits) = ucast (ucast asid :: 9 word)"
  by (word_eqI_solve simp: ptTranslationBits_def)

lemma ptr_offset_in_ptr_range:
  "\<lbrakk> invs s; x \<notin> kernel_mappings;
     get_vspace_of_thread (kheap s) (arch_state s) tcb \<noteq> global_pt s;
     get_page_info (aobjs_of s)
                   (get_vspace_of_thread (kheap s) (arch_state s) tcb) x = Some (base, sz, attr, r) \<rbrakk>
     \<Longrightarrow> ptrFromPAddr base + (x && mask sz) \<in> ptr_range (ptrFromPAddr base) sz"
  apply (simp add: ptr_range_def mask_def)
  apply (rule conjI)
   apply (rule_tac b="2 ^ sz - 1" in word_plus_mono_right2)
    apply (frule some_get_page_info_umapsD)
           apply (fastforce dest: get_vspace_of_thread_reachable
                            simp: canonical_not_kernel_is_user get_page_info_def)+
    apply clarsimp
    apply (drule is_aligned_ptrFromPAddr_n)
     apply (simp add: pageBitsForSize_def pageBits_def canonical_bit_def ptTranslationBits_def
               split: vmpage_size.splits)
    apply (clarsimp simp: is_aligned_no_overflow' word_and_le1)+
  apply (subst p_assoc_help)
  apply (rule word_plus_mono_right)
   apply (rule word_and_le1)
  apply (frule some_get_page_info_umapsD)
         apply (fastforce dest: get_vspace_of_thread_reachable
                          simp: canonical_not_kernel_is_user get_page_info_def)+
  apply clarsimp
  apply (drule is_aligned_ptrFromPAddr_n)
   apply (simp add: pageBitsForSize_def pageBits_def canonical_bit_def ptTranslationBits_def
             split: vmpage_size.splits)
  apply (clarsimp simp: is_aligned_no_overflow')
  done

lemma user_op_access[ADT_AC_assms]:
  "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb; ptable_lift tcb s x = Some ptr;
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag auth tcb (ptrFromPAddr ptr)"
  apply (case_tac "x \<in> kernel_mappings")
  using get_vspace_of_thread_asid_or_global_pt
   apply (fastforce simp: ptable_rights_def vspace_cap_rights_to_auth_def invs_def
                          valid_state_def valid_arch_state_def kernel_mappings_canonical
                    dest: some_get_page_info_kmapsD split: option.splits)
  apply (clarsimp simp: ptable_lift_def split: option.splits)
  apply (insert get_vspace_of_thread_asid_or_global_pt)
  apply (erule_tac x=s in meta_allE)
  apply (erule_tac x=tcb in meta_allE)
  apply (cases "get_vspace_of_thread (kheap s) (arch_state s) tcb = global_pt s"; clarsimp)
   apply (frule get_page_info_gpd_kmaps[rotated 2]; fastforce simp: get_page_info_def)
  apply (frule (3) ptr_offset_in_ptr_range)
  apply (frule get_vspace_of_thread_reachable; clarsimp)
  apply (frule vs_lookup_table_vspace)
     apply fastforce+
  apply (clarsimp simp: get_vspace_of_thread_def get_page_info_def ptable_rights_def pt_lookup_slot_def
                 split: if_splits option.splits kernel_object.splits cap.splits arch_cap.splits)
  apply (frule (1) canonical_not_kernel_is_user)
  apply (frule pt_lookup_slot_from_level_is_subject)
          apply (fastforce elim: vs_lookup_table_vref_independent)+
   apply (rule aag_Control_into_owns)
    apply (clarsimp simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)
    apply (erule subsetD)
    apply (drule_tac addr="tcb_cnode_index 1" in caps_of_state_tcb)
    apply (clarsimp simp: tcb_cnode_map_def)
    apply (drule sbta_caps)
      apply (fastforce simp: obj_refs_def)
     apply (fastforce simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
    apply (rule_tac x=tcb in exI, fastforce)
   apply simp
  apply (clarsimp simp: pt_lookup_slot_from_level_def)
  apply (drule_tac vref'=x in vs_lookup_table_vref_independent, rule order_refl)
  apply (drule pt_walk_level)
  apply (drule (1) vs_lookup_table_extend, rule order_refl)
  apply (rename_tac level vref)
  apply (case_tac "level = asid_pool_level", simp add: pt_walk_top)
  apply (frule vs_lookup_table_is_aligned; clarsimp simp: canonical_not_kernel_is_user)
  apply (clarsimp simp: pas_refined_def pte_info_def split: pte.splits)
  apply (erule subsetD)
  apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
  apply (intro exI conjI sbta_vref | erule sym | rule refl)+
  apply (clarsimp simp: state_vrefs_def ptes_of_Some pts_of_Some)
  apply (intro exI conjI)
      apply (simp add: canonical_not_kernel_is_user)+
  apply (clarsimp simp: vs_refs_aux_def)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: graph_of_def pte_ref2_def Bex_def ptes_of_Some pts_of_Some aobjs_of_Some)
   apply (rule_tac x="table_index (pt_slot_offset max_pt_level vref x)" in exI)
   apply (fastforce simp: table_index_max_level_slots canonical_not_kernel_is_user
                          image_iff ptrFromPAddr_def mult_is_add.mult_ac)
  apply (clarsimp simp: graph_of_def pte_ref2_def ptes_of_Some pts_of_Some aobjs_of_Some)
  apply (rule_tac x="table_index (pt_slot_offset level vref x)" in exI)
  apply (fastforce simp: image_iff table_index_offset_pt_bits_left
                         ptrFromPAddr_def mult_is_add.mult_ac)
  done

lemma write_in_vspace_cap_rights[ADT_AC_assms]:
  "AllowWrite \<in> ptable_rights (cur_thread s) s va
   \<Longrightarrow> Write \<in> vspace_cap_rights_to_auth (ptable_rights (cur_thread s) s va)"
  by (clarsimp simp: vspace_cap_rights_to_auth_def)

end


global_interpretation ADT_AC_1?: ADT_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact ADT_AC_assms)
qed

end
