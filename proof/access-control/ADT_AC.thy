(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ADT_AC
imports Syscall_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma pd_of_thread_same_agent:
  "\<lbrakk> pas_refined aag s; is_subject aag tcb_ptr;
     get_pd_of_thread (kheap s) (arch_state s) tcb_ptr = pd;
     pd \<noteq> arm_global_pd (arch_state s) \<rbrakk>
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

lemma invs_valid_global_pd_mappings:
  "invs s \<Longrightarrow> valid_global_vspace_mappings s"
  apply (simp add: invs_def valid_state_def)
  done

lemma objs_valid_tcb_vtable:
  "\<lbrakk>valid_objs s; get_tcb t s = Some tcb\<rbrakk> \<Longrightarrow> s \<turnstile> tcb_vtable tcb"
  apply (clarsimp simp: get_tcb_def split: option.splits Structures_A.kernel_object.splits)
  apply (erule cte_wp_valid_cap[rotated])
  apply (rule cte_wp_at_tcbI[where t="(a, b)" for a b, where b3="tcb_cnode_index 1"])
    apply fastforce+
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
  "\<lbrakk> invs s; get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
           (get_pd_of_thread (kheap s) (arch_state s) tcb) x =
          Some (base, sz, attr, r); x \<notin> kernel_mappings;
     get_pd_of_thread (kheap s) (arch_state s) tcb \<noteq> arm_global_pd (arch_state s) \<rbrakk>
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
  \<Longrightarrow> (get_pd_of_thread (kheap s) (arch_state s) tcb, auth, ptrFromPAddr ptr)
          \<in> state_objs_to_policy s"
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
    apply (simp add: ptrFromPAddr_def pptrBaseOffset_def pptrBase_def physBase_def)
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
           (get_pd_of_thread (kheap s) (arch_state s) tcb) x = Some (base, sz, attr, r);
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
    apply (simp add: ptrFromPAddr_def pptrBaseOffset_def pptrBase_def physBase_def)
   apply (simp add: ptr_offset_in_ptr_range)

  apply (clarsimp simp: graph_of_def)
  apply (clarsimp simp: get_page_info_def get_pd_entry_def get_pt_info_def
                        get_pt_entry_def pte_ref_def
                  split: option.splits pte.splits pde.splits arch_kernel_obj.splits)
   apply (clarsimp simp: get_arch_obj_def
                   split: option.splits kernel_object.splits arch_kernel_obj.splits)+
  done

lemma user_op_access:
  "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb;
     ptable_lift tcb s x = Some ptr;
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
   \<Longrightarrow> (pasObjectAbs aag tcb, auth, pasObjectAbs aag (ptrFromPAddr ptr)) \<in> pasPolicy aag"
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_lift_def ptable_rights_def split: option.splits)
   apply (frule some_get_page_info_kmapsD)
      apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                             vspace_cap_rights_to_auth_def)+

  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) tcb
                 = arm_global_pd (arch_state s)")
   apply (clarsimp simp: ptable_lift_def ptable_rights_def split: option.splits)
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply (fastforce simp: invs_valid_global_objs invs_arch_state)+

  apply (subst pd_of_thread_same_agent)
      apply fastforce+

  apply (case_tac "\<exists>word1 set1 word2. get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj))
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

lemma user_op_access':
  "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb;
     ptable_lift tcb s x = Some (addrFromPPtr ptr);
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
   \<Longrightarrow> (pasObjectAbs aag tcb, auth, pasObjectAbs aag ptr) \<in> pasPolicy aag"
  apply (drule user_op_access)
        apply auto
  done

lemma integrity_underlying_mem_update:
  "\<lbrakk> integrity aag X st s;
     \<forall>x\<in>xs. (pasSubject aag, Write, pasObjectAbs aag x) \<in> pasPolicy aag;
     \<forall>x\<in>-xs. um' x = underlying_memory (machine_state s) x\<rbrakk>
    \<Longrightarrow> integrity aag X st
          (machine_state_update (\<lambda>ms. underlying_memory_update (\<lambda>_. um') ms) s)"
  apply (clarsimp simp: integrity_def)
  apply (case_tac "x \<in> xs")
   apply (erule_tac x=x in ballE)
    apply (rule trm_write)
    apply simp+
  done

lemma dmo_user_memory_update_respects_Write:
  "\<lbrace>integrity aag X st and K (\<forall>p \<in> dom um. aag_has_auth_to aag Write p)\<rbrace>
  do_machine_op (user_memory_update um)
  \<lbrace>\<lambda>a. integrity aag X st\<rbrace>"
  unfolding user_memory_update_def
  apply (wp dmo_wp)
  apply clarsimp
  apply (simp cong: abstract_state.fold_congs option.case_cong_weak)
  apply (rule integrity_underlying_mem_update)
    apply simp+
  apply (simp add: dom_def)+
  done

lemma integrity_device_state_update:
  "\<lbrakk>integrity aag X st s;
    \<forall>x\<in>xs. (pasSubject aag, Write, pasObjectAbs aag x) \<in> pasPolicy aag;
    \<forall>x\<in>-xs. um' x = None
    \<rbrakk> \<Longrightarrow>  integrity aag X st (machine_state_update (\<lambda>v. v\<lparr>device_state := device_state v ++ um'\<rparr>) s)"
  apply (clarsimp simp: integrity_def)
  apply (case_tac "x \<in> xs")
   apply (erule_tac x=x in ballE)
    apply (rule trd_write)
    apply simp+
  apply (erule_tac x = x in allE, erule integrity_device.cases)
    apply (erule trd_lrefl)
   apply (rule trd_orefl)
   apply (clarsimp simp: map_add_def)
  apply (erule trd_write)
  done

lemma dmo_device_update_respects_Write:
  "\<lbrace>integrity aag X st and (\<lambda>s. device_state (machine_state s) = um)
    and K (\<forall>p \<in> dom um'. aag_has_auth_to aag Write p)\<rbrace>
    do_machine_op (device_memory_update um')
  \<lbrace>\<lambda>a. integrity aag X st\<rbrace>"
  apply (simp add: device_memory_update_def)
  apply (rule hoare_pre)
   apply (wp dmo_wp)
  apply clarsimp
  apply (simp cong: abstract_state.fold_congs)
  apply (rule integrity_device_state_update)
    apply simp
   apply clarify
   apply (drule(1) bspec)
   apply simp
  apply fastforce
  done

lemma dmo_um_upd_machine_state:
  "\<lbrace>\<lambda>s. P (device_state (machine_state s))\<rbrace>
       do_machine_op (user_memory_update ms)
   \<lbrace>\<lambda>_ s. P (device_state (machine_state s))\<rbrace>"
  including no_pre
  apply (wp dmo_wp)
  by (simp add:user_memory_update_def simpler_modify_def valid_def)

lemma do_user_op_respects:
 "\<lbrace> invs and integrity aag X st and is_subject aag \<circ> cur_thread and pas_refined aag \<rbrace>
    do_user_op uop tc
  \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: do_user_op_def)
  apply (wp | simp | wpc)+
           apply (rule dmo_device_update_respects_Write)
          apply (wp dmo_um_upd_machine_state
                    dmo_user_memory_update_respects_Write hoare_vcg_all_lift hoare_vcg_imp_lift
                  | wpc | clarsimp)+
          apply (rule hoare_pre_cont)
         apply (wp   select_wp | wpc | clarsimp)+
  apply (simp add: restrict_map_def split:if_splits)
  apply (rule conjI)
   apply (clarsimp split: if_splits)
   apply (drule_tac auth=Write in user_op_access')
       apply (simp add: vspace_cap_rights_to_auth_def)+
  apply (rule conjI,simp)
  apply (clarsimp split: if_splits)
  apply (drule_tac auth=Write in user_op_access')
      apply (simp add: vspace_cap_rights_to_auth_def)+
  done

end

end
