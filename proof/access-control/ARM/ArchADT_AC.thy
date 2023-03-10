(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchADT_AC
imports ADT_AC
begin

context Arch begin global_naming ARM_A

named_theorems ADT_AC_assms

lemma invs_valid_global_pd_mappings:
  "invs s \<Longrightarrow> valid_global_vspace_mappings s"
  apply (simp add: invs_def valid_state_def)
  done

lemma pd_of_thread_same_agent:
  "\<lbrakk> pas_refined aag s; is_subject aag tcb_ptr;
     get_pd_of_thread (kheap s) (arch_state s) tcb_ptr = pd; pd \<noteq> arm_global_pd (arch_state s) \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag tcb_ptr = pasObjectAbs aag pd"
  apply (rule_tac aag="pasPolicy aag" in aag_wellformed_Control[rotated])
   apply (fastforce simp: pas_refined_def)
  apply (rule pas_refined_mem[rotated], simp)
  apply (clarsimp simp: get_pd_of_thread_eq)
  apply (cut_tac ptr="(tcb_ptr, tcb_cnode_index 1)" in sbta_caps)
     prefer 4
     apply (simp add: state_objs_to_policy_def)
    apply (subst caps_of_state_tcb_cap_cases)
      apply (simp add: get_tcb_def)
     apply (simp add: dom_tcb_cap_cases[simplified])
    apply simp
   apply (simp add: obj_refs_def)
  apply (simp add: cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def)
  done

lemma pd_of_thread_page_directory_at:
  "\<lbrakk> invs s; get_pd_of_thread (kheap s) (arch_state s) tcb \<noteq> arm_global_pd (arch_state s) \<rbrakk>
     \<Longrightarrow> page_directory_at ((get_pd_of_thread (kheap s) (arch_state s) tcb)) s"
  apply (clarsimp simp: get_pd_of_thread_def
                 split: option.splits kernel_object.splits cap.splits arch_cap.splits if_splits)
  apply (frule_tac t=tcb in objs_valid_tcb_vtable[OF invs_valid_objs])
   apply (simp add: get_tcb_def)
  apply (fastforce simp: valid_cap_def2 valid_cap_ref_def valid_arch_cap_ref_simps)
  done

lemma ptr_offset_in_ptr_range:
  "\<lbrakk> invs s; x \<notin> kernel_mappings;
     get_pd_of_thread (kheap s) (arch_state s) tcb \<noteq> arm_global_pd (arch_state s);
     get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
                   (get_pd_of_thread (kheap s) (arch_state s) tcb) x = Some (base, sz, attr, r) \<rbrakk>
     \<Longrightarrow> ptrFromPAddr base + (x && mask sz) \<in> ptr_range (ptrFromPAddr base) sz"
  apply (simp add: ptr_range_def mask_def)
  apply (rule conjI)
   apply (rule_tac b="2 ^ sz - 1" in word_plus_mono_right2)
    apply (frule some_get_page_info_umapsD)
          apply (clarsimp simp: get_pd_of_thread_reachable invs_vspace_objs
                                invs_psp_aligned invs_valid_asid_table invs_valid_objs)+
    apply (drule is_aligned_ptrFromPAddr_n)
     apply (simp add: pageBitsForSize_def split: vmpage_size.splits)
    apply (clarsimp simp: is_aligned_no_overflow' word_and_le1)+
  apply (subst p_assoc_help)
  apply (rule word_plus_mono_right)
   apply (rule word_and_le1)
  apply (frule some_get_page_info_umapsD)
        apply (clarsimp simp: get_pd_of_thread_reachable invs_vspace_objs
                              invs_psp_aligned invs_valid_asid_table invs_valid_objs)+
  apply (drule is_aligned_ptrFromPAddr_n)
   apply (simp add: pageBitsForSize_def split: vmpage_size.splits)
  apply (clarsimp simp: is_aligned_no_overflow')
  done

lemma kernel_mappings_kernel_mapping_slots:
  "x \<notin> kernel_mappings \<Longrightarrow> ucast (x >> 20) \<notin> kernel_mapping_slots"
  apply (rule kernel_base_kernel_mapping_slots)
  apply (simp add: kernel_mappings_def)
  done

lemmas kernel_mappings_kernel_mapping_slots' =
  kernel_mappings_kernel_mapping_slots[simplified kernel_mapping_slots_def, simplified]

lemma ptable_state_objs_to_policy:
  "\<lbrakk> invs s; ptable_lift tcb s x = Some ptr;
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x);
     get_pd_of_thread (kheap s) (arch_state s) tcb \<noteq> arm_global_pd (arch_state s);
     \<forall>word1 set1 word2. get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj))
                                     (get_pd_of_thread (kheap s) (arch_state s) tcb) x \<noteq>
                        Some (PageTablePDE word1 set1 word2); x \<notin> kernel_mappings \<rbrakk>
     \<Longrightarrow> (get_pd_of_thread (kheap s) (arch_state s) tcb, auth, ptrFromPAddr ptr) \<in>
           state_objs_to_policy s"
  apply (simp add: state_objs_to_policy_def)
  apply (rule sbta_vref)
  apply (clarsimp simp: ptable_lift_def ptable_rights_def state_vrefs_def
                  split: option.splits)
  apply (frule pd_of_thread_page_directory_at, simp)
  apply (clarsimp simp: typ_at_eq_kheap_obj)
  apply (clarsimp simp: vs_refs_no_global_pts_def)
  apply (rule_tac x="(ucast (x >> 20), ptrFromPAddr a, aa,
                      vspace_cap_rights_to_auth b)" in bexI)
   apply clarsimp
   apply (rule_tac x="(ptrFromPAddr a + (x && mask aa), auth)" in image_eqI)
    apply (simp add: ptrFromPAddr_def pptrBaseOffset_def pptrBase_def Kernel_Config.physBase_def)
   apply (simp add: ptr_offset_in_ptr_range)
  apply (simp add: kernel_mappings_kernel_mapping_slots')
  apply (clarsimp simp: graph_of_def)
  apply (clarsimp simp: get_page_info_def get_pd_entry_def pde_ref2_def
                  split: option.splits pde.splits arch_kernel_obj.splits)
   apply (clarsimp simp: get_arch_obj_def
                   split: option.splits kernel_object.splits arch_kernel_obj.splits)+
  done

lemma pt_in_pd_same_agent:
  "\<lbrakk> pas_refined aag s; is_subject aag pd_ptr; vptr \<notin> kernel_mappings;
     get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ptr vptr = Some (PageTablePDE p x xa) \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag pd_ptr = pasObjectAbs aag (ptrFromPAddr p)"
  apply (rule_tac aag="pasPolicy aag" in aag_wellformed_Control[rotated])
   apply (fastforce simp: pas_refined_def)
  apply (rule pas_refined_mem[rotated], simp)
  apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                 split: option.splits kernel_object.splits arch_kernel_obj.splits)
  apply (simp add: state_objs_to_policy_def)
  apply (rule sbta_vref)
  apply (simp add: state_vrefs_def split: option.splits)
  apply (clarsimp simp: vs_refs_no_global_pts_def)
  apply (rule_tac x="(ucast (vptr >> 20), ptrFromPAddr p, 0, {Control})" in bexI)
   apply simp
  apply (simp add: kernel_mappings_kernel_mapping_slots' graph_of_def pde_ref2_def)
  done

lemma pt_in_pd_page_table_at:
  "\<lbrakk> invs s; get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ptr x =
     Some (PageTablePDE word1 set1 word2); (\<exists>\<rhd> pd_ptr) s; x \<notin> kernel_mappings \<rbrakk>
     \<Longrightarrow> page_table_at (ptrFromPAddr word1) s"
  apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                  split: option.splits kernel_object.splits arch_kernel_obj.splits)
  apply (rename_tac "fun")
  apply (subgoal_tac "valid_vspace_obj (PageDirectory fun) s")
   apply (simp add: kernel_mappings_slots_eq)
   apply (drule bspec)
    apply simp+
  apply (drule invs_vspace_objs)
  apply (auto simp: obj_at_def invs_vspace_objs valid_vspace_objs_def)
  done

lemma get_page_info_state_objs_to_policy:
  "\<lbrakk> invs s; auth \<in> vspace_cap_rights_to_auth r;
     get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
                   (get_pd_of_thread (kheap s) (arch_state s) tcb) x =
     Some (base, sz, attr, r);
     get_pd_of_thread (kheap s) (arch_state s) tcb \<noteq> arm_global_pd (arch_state s);
     get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj))
                  (get_pd_of_thread (kheap s) (arch_state s) tcb) x =
     Some (PageTablePDE word1 set1 word2); x \<notin> kernel_mappings \<rbrakk>
     \<Longrightarrow> (ptrFromPAddr word1, auth, ptrFromPAddr (base + (x && mask sz))) \<in> state_objs_to_policy s"
  apply (simp add: state_objs_to_policy_def)
  apply (rule sbta_vref)
  apply (clarsimp simp: state_vrefs_def split: option.splits)
  apply (frule pt_in_pd_page_table_at)
     apply (simp add: get_pd_of_thread_reachable)+
  apply (clarsimp simp: typ_at_eq_kheap_obj)
  apply (clarsimp simp: vs_refs_no_global_pts_def)
  apply (rule_tac x="(ucast ((x >> 12) && mask 8),  ptrFromPAddr base, sz,
                      vspace_cap_rights_to_auth r)" in bexI)
   apply clarsimp
   apply (rule_tac x="(ptrFromPAddr base + (x && mask sz), auth)" in image_eqI)
    apply (simp add: ptrFromPAddr_def pptrBaseOffset_def pptrBase_def Kernel_Config.physBase_def)
   apply (simp add: ptr_offset_in_ptr_range)
  apply (clarsimp simp: get_page_info_def get_pd_entry_def get_pt_info_def
                        get_pt_entry_def get_arch_obj_def pte_ref_def graph_of_def
                 split: option.splits pte.splits pde.splits arch_kernel_obj.splits)
  done

lemma user_op_access[ADT_AC_assms]:
  "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb; ptable_lift tcb s x = Some ptr;
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag auth tcb (ptrFromPAddr ptr)"
  apply (case_tac "x \<in> kernel_mappings")
   apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                          ptable_lift_def ptable_rights_def vspace_cap_rights_to_auth_def
                    dest: some_get_page_info_kmapsD split: option.splits)
  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) tcb =
                   arm_global_pd (arch_state s)")
   apply (fastforce simp: invs_valid_global_objs invs_arch_state
                          ptable_lift_def ptable_rights_def
                   split: option.splits
                    dest: get_page_info_gpd_kmaps[rotated 2])
  apply (subst pd_of_thread_same_agent)
      apply fastforce+
  apply (cases "\<exists>word1 set1 word2. get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj))
                                                (get_pd_of_thread (kheap s) (arch_state s) tcb) x =
                                   Some (PageTablePDE word1 set1 word2)")
   apply (clarsimp simp: ptable_lift_def ptable_rights_def split: option.splits)
   apply (frule pd_of_thread_same_agent)
      apply fastforce+
   apply (subst pt_in_pd_same_agent)
       apply fastforce+
   apply (rule pas_refined_mem[rotated], simp)
   apply (rule get_page_info_state_objs_to_policy)
        apply fastforce+
  apply (rule pas_refined_mem[rotated], simp)
  apply (rule ptable_state_objs_to_policy)
       apply simp+
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
