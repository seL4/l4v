(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchAInvsPre
imports "../AInvsPre"
begin

context Arch begin

global_naming RISCV64

definition
  "kernel_mappings \<equiv> {x. x \<ge> pptr_base}"

lemma canonical_not_kernel_is_user:
  "\<lbrakk> v \<notin> kernel_mappings; canonical_address v; valid_uses s \<rbrakk> \<Longrightarrow> v \<in> user_region s"
  by (simp add: kernel_mappings_def not_le canonical_below_pptr_base_user)

lemma no_user_region_kernel_mappings:
  "\<lbrakk> p \<in> user_region s; p \<in> kernel_mappings; valid_uses s \<rbrakk> \<Longrightarrow> False"
  using canonical_user_pptr_base
  by (simp add: valid_uses_user_region_eq kernel_mappings_def)

lemma kernel_mappings_slots_eq:
  "canonical_address p \<Longrightarrow>
   ucast (p >> pt_bits_left max_pt_level) \<in> kernel_mapping_slots \<longleftrightarrow> p \<in> kernel_mappings"
  apply (simp add: kernel_mappings_def kernel_mapping_slots_def ucast_mask_drop canonical_address_range)
  apply word_bitwise
  by (auto simp: canonical_bit_def word_bits_def pt_bits_left_def bit_simps level_defs word_size
                 rev_bl_order_simps)

lemma ucast_ucast_mask_low: "(ucast (x && mask asid_low_bits) :: asid_low_index) = ucast x"
  by (rule ucast_mask_drop, simp add: asid_low_bits_def)

lemma some_get_page_info_kmapsD:
  "\<lbrakk>get_page_info (aobjs_of s) pt_ref p = Some (b, a, attr, r);
    p \<in> kernel_mappings; canonical_address p; valid_global_vspace_mappings s; equal_kernel_mappings s\<rbrakk>
   \<Longrightarrow> (\<exists>sz. pageBitsForSize sz = a) \<and> r = {}"
  apply (clarsimp simp: get_page_info_def in_omonad kernel_mappings_def)
  sorry (* FIXME RISCV: insufficient invariants to prove that kernel mappings have no user rights *)

lemma get_page_info_gpd_kmaps:
  "\<lbrakk>valid_global_vspace_mappings s; valid_arch_state s; canonical_address p;
    get_page_info (aobjs_of s) (riscv_global_pt (arch_state s)) p = Some (b, a, attr, r)\<rbrakk>
   \<Longrightarrow> p \<in> kernel_mappings"
  apply (simp add: get_page_info_def)
  sorry (* FIXME RISCV: insufficient invariants to prove that global PT does not have user mappings
  apply (clarsimp simp: valid_global_objs_def valid_arch_state_def
                        obj_at_def
                        empty_table_def kernel_mappings_slots_eq)
  apply (drule_tac x="ucast (p >> pml4_shift_bits)" in spec; clarsimp)
  apply (rule ccontr)
  apply (clarsimp simp: get_page_info_def get_pml4_entry_def get_arch_obj_def
                        bit_simps ucast_ucast_mask_low
                 split: option.splits pml4e.splits arch_kernel_obj.splits)
  done *)

lemma get_vspace_of_thread_reachable:
  "\<lbrakk> get_vspace_of_thread (kheap s) (arch_state s) t \<noteq> riscv_global_pt (arch_state s);
     valid_uses s \<rbrakk>
   \<Longrightarrow> (\<exists>\<rhd> (max_pt_level, get_vspace_of_thread (kheap s) (arch_state s) t)) s"
  by (auto simp: get_vspace_of_thread_def
          split: option.splits cap.splits kernel_object.splits arch_cap.splits if_split_asm
          intro: vspace_for_asid_vs_lookup)

lemma pageBitsForSize_vmpage_size_of_level[simp]:
  "level \<le> max_pt_level \<Longrightarrow>
   pageBitsForSize (vmpage_size_of_level level) = pt_bits_left level"
  apply (clarsimp simp: pageBitsForSize_def vmpage_size_of_level_def pt_bits_left_def)
  apply (simp add: level_defs)
  apply (cases level rule: bit0.of_nat_cases)
  apply ((case_tac m; clarsimp), (rename_tac m)?)+
  done

lemma data_at_aligned:
  "\<lbrakk> data_at sz p s; pspace_aligned s\<rbrakk> \<Longrightarrow> is_aligned p (pageBitsForSize sz)"
  unfolding data_at_def by (auto simp: obj_at_def dest: pspace_alignedD)

lemma is_aligned_ptrFromPAddr_n_eq:
  "sz \<le> canonical_bit \<Longrightarrow> is_aligned (ptrFromPAddr x) sz = is_aligned x sz"
  apply (rule iffI)
   apply (simp add: ptrFromPAddr_def baseOffset_def pptrBase_def pAddr_base_def canonical_bit_def)
   apply (drule is_aligned_addD2)
    apply (erule is_aligned_weaken[rotated])
    apply (simp add: is_aligned_def)
   apply assumption
  apply (erule (1) is_aligned_ptrFromPAddr_n)
  done

lemma some_get_page_info_umapsD:
  "\<lbrakk>get_page_info (aobjs_of s) pt_ref p = Some (b, a, attr, r);
    \<exists>\<rhd> (max_pt_level, pt_ref) s; p \<in> user_region s; valid_vspace_objs s; pspace_aligned s;
    canonical_address p;
    valid_asid_table s; valid_objs s; valid_uses s\<rbrakk>
   \<Longrightarrow> \<exists>sz. pageBitsForSize sz = a \<and> is_aligned b a \<and> data_at sz (ptrFromPAddr b) s"
  apply (clarsimp simp: get_page_info_def vs_lookup_table_def)
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (frule pt_walk_max_level)
  apply (drule pt_walk_level)
  apply (rename_tac pte asid pool_ptr vref level pt_ptr')
  apply (subgoal_tac "vs_lookup_table level asid p s = Some (level, pt_ptr')")
   prefer 2
   apply (clarsimp simp: vs_lookup_table_def in_omonad)
   apply (drule (2) valid_vspace_objs_strongD; assumption?)
   apply (clarsimp simp: pte_info_def split: pte.splits)
   apply (frule pspace_aligned_pts_ofD, fastforce)
   apply (drule_tac x="table_index (pt_slot_offset level pt_ptr' p)" in bspec)
   apply (clarsimp simp: table_index_offset_max_pt_level simp: kernel_mappings_slots_eq)
   apply (erule (2) no_user_region_kernel_mappings)
  apply (clarsimp simp: pte_of_def)
  apply (subgoal_tac "valid_pte level (PagePTE b attr r) s")
   prefer 2
   apply simp
  apply (subst (asm) valid_pte.simps)
  apply clarsimp
  apply (rule_tac x="vmpage_size_of_level level" in exI)
  apply (clarsimp simp: obj_at_def)
  apply (drule (1) data_at_aligned)
  apply (simp add: pt_bits_left_le_canoncial is_aligned_ptrFromPAddr_n_eq)
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

global_naming Arch
named_theorems AInvsPre_asms

lemma ptable_rights_imp_frame[AInvsPre_asms]:
  assumes "valid_state s"
  shows "\<lbrakk> ptable_rights t s x \<noteq> {}; ptable_lift t s x = Some (addrFromPPtr y) \<rbrakk> \<Longrightarrow>
         in_user_frame y s \<or> in_device_frame y s"
  apply (rule ccontr, frule ptable_lift_Some_canonical_addressD)
  using assms
  apply (clarsimp simp: ptable_lift_def ptable_rights_def in_user_frame_def in_device_frame_def
                 split: option.splits)
  apply (case_tac "x \<in> kernel_mappings")
   apply (drule (2) some_get_page_info_kmapsD; fastforce simp: valid_state_def)
  apply (frule some_get_page_info_umapsD)
          apply (rule get_vspace_of_thread_reachable)
           apply clarsimp
           apply (frule get_page_info_gpd_kmaps[rotated 2])
              apply (simp_all add: valid_state_def valid_pspace_def valid_arch_state_def)
     apply ((clarsimp simp: data_at_def canonical_not_kernel_is_user)+)[3]
  apply clarsimp
  apply (drule_tac x=sz in spec)+
  apply (rename_tac p_addr attr rghts sz)
  apply (frule is_aligned_add_helper[OF _ and_mask_less', THEN conjunct2, of _ _ x])
   apply (simp only: pbfs_less_wb'[simplified word_bits_def])
  apply (clarsimp simp: data_at_def ptrFromPAddr_def addrFromPPtr_def field_simps)
  apply (subgoal_tac "p_addr + (baseOffset + (x && mask (pageBitsForSize sz)))
                        && ~~ mask (pageBitsForSize sz) = p_addr + baseOffset")
   apply simp
  apply (subst add.assoc[symmetric])
  apply (subst is_aligned_add_helper)
    apply (erule aligned_add_aligned)
     apply (case_tac sz; simp add: is_aligned_def baseOffset_def pptrBase_def pAddr_base_def
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
  case 1 show ?case by (intro_locales; (unfold_locales; fact AInvsPre_asms)?)
  qed

requalify_facts
  RISCV64.user_mem_dom_cong
  RISCV64.device_mem_dom_cong
  RISCV64.device_frame_in_device_region

end
