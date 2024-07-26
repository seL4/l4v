(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAInvsPre
imports AInvsPre
begin

context Arch begin arch_global_naming

lemma get_pd_of_thread_reachable:
  "get_pd_of_thread (kheap s) (arch_state s) t \<noteq> 0
   \<Longrightarrow> (\<exists>\<rhd> get_pd_of_thread (kheap s) (arch_state s) t) s"
  by (auto simp: get_pd_of_thread_vs_lookup
          split: Structures_A.kernel_object.splits if_split_asm option.splits
                 cap.splits arch_cap.splits)

lemma obj_bits_data_at:
  "data_at sz (ptrFromPAddr b) s
  \<Longrightarrow> obj_bits (the (kheap s (ptrFromPAddr b))) = pageBitsForSize sz"
  apply (clarsimp simp add: obj_at_def a_type_def data_at_def
                     split: kernel_object.splits arch_kernel_obj.split_asm if_splits)
  apply (case_tac ko,simp_all)
   apply fastforce
  subgoal for ko archko
   by (case_tac archko,fastforce+)
  done

lemma some_get_page_info_umapsD:
  "\<lbrakk>get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref p = Some (b, a, attr, r);
    (\<exists>\<rhd> pd_ref) s; valid_vspace_objs s; pspace_aligned s;
    valid_asid_table (arm_asid_table (arch_state s)) s; valid_objs s\<rbrakk>
   \<Longrightarrow> (\<exists>sz. pageBitsForSize sz = a \<and> is_aligned b a \<and>
             data_at sz (ptrFromPAddr b) s)"
  apply (clarsimp simp: get_page_info_def get_pd_entry_def get_arch_obj_def
                 split: option.splits Structures_A.kernel_object.splits
                        arch_kernel_obj.splits if_splits)
  apply (frule (1) valid_vspace_objsD[rotated 2])
   apply (simp add: obj_at_def)
  apply (simp add: valid_vspace_obj_def vspace_bits_defs)
  apply (drule_tac x="ucast (p >> 21)" in spec)
  apply (simp split: pde.splits)
    apply (rename_tac rs pd pt_ref)
    apply (subgoal_tac
        "((rs, pd_ref) \<rhd>1
          (VSRef (ucast (ucast (p >> 21))) (Some APageDirectory) # rs,
           ptrFromPAddr pt_ref)) s")
     prefer 2
     apply (rule vs_lookup1I[rotated 2], simp)
      apply (simp add: obj_at_def)
     apply (simp add: vs_refs_def pde_ref_def image_def graph_of_def)
     apply (rule_tac x="ucast (p >> 21)" in exI, rule conjI, simp+)
    apply (frule (1) vs_lookup_step)
    apply (drule (2) stronger_vspace_objsD[where ref="x # xs" for x xs])
    apply clarsimp
    apply (case_tac ao, simp_all add: a_type_simps obj_at_def)[1]
     apply (simp add: get_pt_info_def get_pt_entry_def)
     apply (drule_tac x="(ucast ((p >> 12) && mask 9))" in spec)
     apply (clarsimp simp: obj_at_def split: pte.splits,intro exI conjI,simp_all)[1]
      apply (frule obj_bits_data_at)
      apply (clarsimp simp: pspace_aligned_def data_at_def)
      apply (drule_tac x = "(ptrFromPAddr b)" in  bspec )
       apply (fastforce simp: obj_at_def)
      apply (clarsimp dest!: is_aligned_ptrFromPAddrD)
     apply (frule (1) data_at_aligned)
     apply (intro exI conjI, simp_all add: is_aligned_ptrFromPAddrD)[1]
    apply (simp add: get_pt_info_def get_pt_entry_def)
   apply (frule obj_bits_data_at)
   apply (intro exI conjI, simp_all add: pageBits_def)[1]
   apply (clarsimp simp: pspace_aligned_def data_at_def)
   apply (drule_tac x = "(ptrFromPAddr b)" in  bspec)
    apply (fastforce simp: obj_at_def)
   apply (clarsimp dest!: is_aligned_ptrFromPAddrD)
  apply (frule obj_bits_data_at)
  apply (intro exI conjI, simp_all add: pageBits_def)[1]
  apply (clarsimp simp: pspace_aligned_def data_at_def)
  apply (drule_tac x = "(ptrFromPAddr b)" in  bspec)
   apply (fastforce simp: obj_at_def)
  apply (clarsimp dest!: is_aligned_ptrFromPAddrD)
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

lemma get_page_info_0[simp]:
  "get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) 0 x = None"
  by (simp add: get_page_info_def)

lemma (* ptable_rights_imp_frame *)[AInvsPre_assms]:
  assumes "valid_state s"
  shows "ptable_rights t s x \<noteq> {} \<Longrightarrow>
         ptable_lift t s x = Some (addrFromPPtr y) \<Longrightarrow>
         in_user_frame y s \<or> in_device_frame y s"
  apply (clarsimp simp: ptable_rights_def ptable_lift_def in_user_frame_def
                        in_device_frame_def data_at_def
                 split: option.splits)
  apply (rename_tac b a r)
  apply (frule some_get_page_info_umapsD)
       apply (rule get_pd_of_thread_reachable, clarsimp)
      using assms
      apply (simp_all add: valid_state_def valid_pspace_def
                           valid_arch_state_def)
  apply clarsimp
  apply (frule is_aligned_add_helper[OF _ and_mask_less',
                                     THEN conjunct2, of _ _ x])
   apply (simp only: pbfs_less_wb'[simplified word_bits_def])
  apply (clarsimp simp: ptrFromPAddr_def addrFromPPtr_def
                        field_simps)
  apply (rule_tac x=sz in exI)
  apply (drule_tac x = sz in spec)
  apply (subst add.assoc[symmetric])
  apply (frule is_aligned_add_helper[OF aligned_add_aligned[OF _ is_aligned_pptrBaseOffset]])
    apply (rule le_refl)
   apply (rule_tac w = x in and_mask_less')
    apply (case_tac sz, simp_all add: word_bits_conv)[1]
  apply (clarsimp simp: field_simps simp: data_at_def)
  done
end

global_interpretation AInvsPre?: AInvsPre
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact AInvsPre_assms)?)
  qed

requalify_facts
  ARM_HYP.user_mem_dom_cong
  ARM_HYP.device_mem_dom_cong
  ARM_HYP.device_frame_in_device_region
  ARM_HYP.is_aligned_pptrBaseOffset
end
