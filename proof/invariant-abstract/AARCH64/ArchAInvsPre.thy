(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAInvsPre
imports AInvsPre
begin

unbundle l4v_word_context

context Arch begin arch_global_naming

lemma ucast_ucast_mask_low: "(ucast (x && mask asid_low_bits) :: asid_low_index) = ucast x"
  by (rule ucast_mask_drop, simp add: asid_low_bits_def)

lemma ptes_of_idx:
  "\<lbrakk> ptes_of s (level_type level) (pt_slot_offset level pt_ptr p) = Some pte;
     pts_of s pt_ptr = Some pt; pt_type pt = level_type level; pspace_aligned s \<rbrakk> \<Longrightarrow>
   \<exists>idx. pt_apply pt idx = pte"
  apply (drule_tac pt_ptr=pt_ptr in pspace_aligned_pts_ofD, simp)
  apply (fastforce simp: level_pte_of_def in_omonad)
  done

lemma pte_info_not_InvalidPTE:
  "pte_info level pte = Some (b, a, attr, r) \<Longrightarrow> pte \<noteq> InvalidPTE"
  by (simp add: pte_info_def split: pte.splits)

lemma get_vspace_of_thread_reachable:
  "\<lbrakk> get_vspace_of_thread (kheap s) (arch_state s) t \<noteq> global_pt s;
     valid_uses s \<rbrakk>
   \<Longrightarrow> (\<exists>\<rhd> (max_pt_level, get_vspace_of_thread (kheap s) (arch_state s) t)) s"
  by (auto simp: get_vspace_of_thread_def
          split: option.splits cap.splits kernel_object.splits arch_cap.splits if_split_asm pt_type.splits
          intro: vspace_for_asid_vs_lookup)

lemma data_at_aligned:
  "\<lbrakk> data_at sz p s; pspace_aligned s\<rbrakk> \<Longrightarrow> is_aligned p (pageBitsForSize sz)"
  unfolding data_at_def by (auto simp: obj_at_def dest: pspace_alignedD)

lemma some_get_page_info_umapsD:
  "\<lbrakk>get_page_info (aobjs_of s) pt_ref vptr = Some (b, a, attr, r);
    \<exists>\<rhd> (max_pt_level, pt_ref) s; vptr \<in> user_region; valid_vspace_objs s; pspace_aligned s;
    valid_asid_table s; valid_objs s\<rbrakk>
   \<Longrightarrow> \<exists>sz. pageBitsForSize sz = a \<and> is_aligned b a \<and> data_at sz (ptrFromPAddr b) s"
  apply (clarsimp simp: get_page_info_def vs_lookup_table_def)
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (frule pt_walk_max_level)
  apply (drule pt_walk_level)
  apply (rename_tac pte asid pool_ptr vref level pt_ptr')
  apply (prop_tac "vs_lookup_table level asid vptr s = Some (level, pt_ptr')")
   apply (clarsimp simp: vs_lookup_table_def in_omonad)
  apply (drule (2) valid_vspace_objs_strongD; assumption?)
  apply (clarsimp simp: pte_info_def split: pte.splits)
  apply (rename_tac pt ppn)
  apply (frule pspace_aligned_pts_ofD, fastforce)
  apply (drule_tac x="PagePTE b ppn attr r" in bspec)
   apply (erule (1) pt_slot_offset_pt_range, simp)
  apply (subst (asm) valid_pte.simps)
  apply clarsimp
  apply (rule_tac x="vmsize_of_level level" in exI)
  apply (clarsimp simp: obj_at_def)
  apply (drule (1) data_at_aligned)
  apply (simp add: is_aligned_ptrFromPAddr_n_eq)
  done

lemma user_mem_dom_cong:
  "kheap s = kheap s' \<Longrightarrow> dom (user_mem s) = dom (user_mem s')"
  by (simp add: user_mem_def in_user_frame_def dom_def obj_at_def)

lemma device_mem_dom_cong:
  "kheap s = kheap s' \<Longrightarrow> dom (device_mem s) = dom (device_mem s')"
  by (simp add: device_mem_def in_device_frame_def dom_def obj_at_def)

lemma device_frame_in_device_region:
  "\<lbrakk>in_device_frame p s; pspace_respects_device_region s\<rbrakk>
  \<Longrightarrow> device_state (machine_state s) p \<noteq> None"
  by (auto simp add: pspace_respects_device_region_def dom_def device_mem_def)

named_theorems AInvsPre_assms

lemma get_vspace_of_thread_asid_or_global_pt:
  "(\<exists>asid. vspace_for_asid asid s = Some (get_vspace_of_thread (kheap s) (arch_state s) t))
    \<or> get_vspace_of_thread (kheap s) (arch_state s) t = global_pt s"
  by (auto simp: get_vspace_of_thread_def
           split: option.split kernel_object.split cap.split arch_cap.split pt_type.splits)

lemma get_page_info_gpd_kmaps:
  "\<lbrakk>valid_global_objs s; valid_arch_state s; pspace_aligned s;
    get_page_info (aobjs_of s) (global_pt s) vptr = Some (b, a, attr, r)\<rbrakk>
   \<Longrightarrow> False"
  apply (clarsimp simp: get_page_info_def in_omonad pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (clarsimp simp: valid_arch_state_def valid_global_tables_def)
  apply (subst (asm) pt_walk.simps)
  apply (drule (1) pspace_aligned_pts_ofD)
  apply (clarsimp simp: ptes_of_def in_omonad pte_info_def
                        table_base_pt_slot_offset[where level=max_pt_level, simplified])
  done

lemma ptable_rights_imp_frame[AInvsPre_assms]:
  assumes "valid_state s"
  shows "\<lbrakk> ptable_rights t s vptr \<noteq> {}; ptable_lift t s vptr = Some (addrFromPPtr p) \<rbrakk> \<Longrightarrow>
         in_user_frame p s \<or> in_device_frame p s"
  apply (rule ccontr, frule ptable_lift_Some_user_regionD)
  using assms get_vspace_of_thread_asid_or_global_pt[of s t]
  apply (clarsimp simp: ptable_lift_def ptable_rights_def in_user_frame_def in_device_frame_def
                 split: option.splits)
  apply (frule some_get_page_info_umapsD)
         apply (rule get_vspace_of_thread_reachable)
          apply clarsimp
          apply (frule get_page_info_gpd_kmaps[rotated 3])
            apply (simp_all add: valid_state_def valid_pspace_def valid_arch_state_def)
  apply clarsimp
  apply (drule_tac x=sz in spec)+
  apply (rename_tac p_addr attr rghts sz)
  apply (frule is_aligned_add_helper[OF _ and_mask_less', THEN conjunct2, of _ _ vptr])
   apply (simp only: pbfs_less_wb'[simplified word_bits_def])
  apply (clarsimp simp: data_at_def ptrFromPAddr_def addrFromPPtr_def field_simps)
  apply (subgoal_tac "p_addr + (pptrBaseOffset + (vptr && mask (pageBitsForSize sz)))
                        && ~~ mask (pageBitsForSize sz) = p_addr + pptrBaseOffset")
   apply simp
  apply (subst add.assoc[symmetric])
  apply (subst is_aligned_add_helper)
    apply (erule aligned_add_aligned)
     apply (case_tac sz; simp add: is_aligned_def pptrBaseOffset_def pptrBase_def paddrBase_def
                                   canonical_bit_def bit_simps)
    apply simp
   apply (rule and_mask_less')
   apply (case_tac sz; simp add: bit_simps)
  apply simp
  done

end

interpretation AInvsPre?: AInvsPre
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact AInvsPre_assms)?)
qed

end
