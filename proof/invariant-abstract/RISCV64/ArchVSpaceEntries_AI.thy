(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVSpaceEntries_AI
imports VSpaceEntries_AI
begin

context Arch begin arch_global_naming

primrec pte_range :: "pte \<Rightarrow> pt_index \<Rightarrow> pt_index set" where
  "pte_range (InvalidPTE) p = {}"
| "pte_range (PagePTE ptr x y) p = {p}"
| "pte_range (PageTablePTE ptr x) p = {p}"

abbreviation "valid_pt_entries \<equiv> \<lambda>pt. valid_entries pte_range pt"

definition obj_valid_vspace :: "kernel_object \<Rightarrow> bool" where
 "obj_valid_vspace obj \<equiv> case obj of
    ArchObj (PageTable pt) \<Rightarrow> valid_pt_entries pt
  | _ \<Rightarrow> True"

lemmas obj_valid_vspace_simps[simp]
    = obj_valid_vspace_def
        [split_simps Structures_A.kernel_object.split
                     arch_kernel_obj.split]

abbreviation
  valid_vspace_objs' :: "'z state \<Rightarrow> bool"
where
 "valid_vspace_objs' s \<equiv> \<forall>x \<in> ran (kheap s). obj_valid_vspace x"

lemma set_object_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and K (obj_valid_vspace obj)\<rbrace>
      set_object ptr obj
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: set_object_def, wp assert_inv)
  apply (auto simp: fun_upd_def[symmetric] del: ballI elim: ball_ran_updI)
  done

crunch cap_insert, cap_swap_for_delete,empty_slot
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps simp: crunch_simps ignore:set_object)

lemma mapM_x_store_pte_updates:
  "\<forall>x \<in> set xs. f x && ~~ mask pt_bits = p \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> pt_at p s \<longrightarrow> Q s) \<and>
        (\<forall>pt. ko_at (ArchObj (PageTable pt)) p s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p := Some (ArchObj (PageTable (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pt_bits >> pte_bits)) ` set xs then pte else pt y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. store_pte (f x) pte) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def fun_upd_idem)
  apply (simp add: mapM_x_Cons)
  apply (rule bind_wp, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: store_pte_def set_pt_def set_object_def word_size_bits_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp)
  apply (rule ext, clarsimp)
  done

lemma valid_pt_entries_invalid[simp]:
  "valid_pt_entries (\<lambda>x. InvalidPTE)"
   by (simp add:valid_entries_def)

lemma valid_vspace_objs'_ptD:
  "\<lbrakk>valid_vspace_objs' s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageTable pt))\<rbrakk>
   \<Longrightarrow> valid_pt_entries pt"
  by (fastforce simp:ran_def)

lemma store_pte_valid_vspace_objs'[wp]:
  "store_pte p pte \<lbrace>valid_vspace_objs'\<rbrace>"
  apply (simp add: store_pte_def set_pt_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_entries_overwrite_0)
   apply (fastforce simp:ran_def)
  apply (drule bspec)
   apply fastforce
  apply (case_tac "pt pa"; case_tac pte; simp)
  done

lemma unmap_page_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> unmap_page sz asid vptr pptr \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: unmap_page_def mapM_discarded
             cong: vmpage_size.case_cong)
  apply (wpsimp wp: store_pte_valid_vspace_objs')
  done

lemma unmap_page_table_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> unmap_page_table asid vptr pt \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (wp get_object_wp store_pte_valid_vspace_objs' | wpc)+
  apply (simp add: obj_at_def)
  done

crunch set_simple_ko
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps)

crunch finalise_cap, cap_swap_for_delete, empty_slot
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps preemption_point_inv simp: crunch_simps unless_def ignore:set_object)

lemma preemption_point_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> preemption_point \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (wp preemption_point_inv | simp)+

lemmas cap_revoke_preservation_valid_vspace_objs = cap_revoke_preservation[OF _,
                                                          where E=valid_vspace_objs',
                                                          simplified, THEN validE_valid]

lemmas rec_del_preservation_valid_vspace_objs = rec_del_preservation[OF _ _ _ _,
                                                    where P=valid_vspace_objs', simplified]

crunch cap_delete, cap_revoke
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (rule: cap_revoke_preservation_valid_vspace_objs)

lemma copy_global_mappings_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_arch_state and pspace_aligned
            and K (is_aligned p pt_bits)\<rbrace>
       copy_global_mappings p \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  unfolding copy_global_mappings_def
  by (wpsimp wp: mapM_x_wp')

lemma in_pte_rangeD:
  "x \<in> pte_range v y \<Longrightarrow> x = y"
  by (case_tac v,simp_all split:if_splits)

lemma non_invalid_in_pte_range:
  "pte \<noteq> InvalidPTE
  \<Longrightarrow> x \<in> pte_range pte x"
  by (case_tac pte,simp_all)

crunch cancel_badged_sends
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps filterM_mapM wp: crunch_wps ignore: filterM)

crunch cap_move, cap_insert
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"

lemma invoke_cnode_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp | wpc | simp split del: if_split)+
  done

crunch invoke_tcb, invoke_domain
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: check_cap_inv crunch_wps simp: crunch_simps
       ignore: check_cap_at)

crunch set_extra_badge, transfer_caps_loop
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (rule: transfer_caps_loop_pres)

crunch send_ipc, send_signal,
    do_reply_transfer, invoke_irq_control, invoke_irq_handler
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps simp: crunch_simps
         ignore: clearMemory const_on_failure set_object)

lemma valid_vspace_objs'_trans_state[simp]: "valid_vspace_objs' (trans_state f s) = valid_vspace_objs' s"
  apply (simp add: obj_valid_vspace_def)
  done

lemma retype_region_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> retype_region ptr bits o_bits type dev \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: retype_region_def split del: if_split)
  apply (wp | simp only: valid_vspace_objs'_trans_state trans_state_update[symmetric])+
  apply (clarsimp simp: retype_addrs_fold foldr_upd_app_if ranI
                 elim!: ranE split: if_split_asm simp del:fun_upd_apply)
  apply (simp add: default_object_def default_arch_object_def
            split: Structures_A.kernel_object.splits
    Structures_A.apiobject_type.split aobject_type.split)+
  done

lemma detype_valid_vspace[elim!]:
  "valid_vspace_objs' s \<Longrightarrow> valid_vspace_objs' (detype S s)"
  by (auto simp add: detype_def ran_def)

crunch create_cap
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (ignore: clearMemory simp: crunch_simps)

lemma init_arch_objects_valid_vspace:
  "\<lbrace>valid_vspace_objs' and pspace_aligned and valid_arch_state
           and K (orefs = retype_addrs ptr type n us)
           and K (range_cover ptr sz (obj_bits_api type us) n)\<rbrace>
     init_arch_objects type dev ptr n obj_sz orefs
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  unfolding init_arch_objects_def by wpsimp

lemma delete_objects_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (rule delete_objects_reduct) (wp detype_valid_vspace)

crunch reset_untyped_cap
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: mapME_x_inv_wp crunch_wps simp: crunch_simps unless_def)

lemma invoke_untyped_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active
          and valid_untyped_inv ui\<rbrace>
       invoke_untyped ui
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q)
      apply (wp init_arch_objects_valid_vspace | simp)+
     apply (auto simp: post_retype_invs_def split: if_split_asm)[1]
    apply (wp | simp)+
  done

crunch store_asid_pool_entry
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"

lemma perform_asid_pool_invocation_valid_vspace_objs'[wp]:
  "\<lbrace> valid_vspace_objs' and valid_arch_state and pspace_aligned and
     (\<lambda>s. valid_caps (caps_of_state s) s) \<rbrace>
   perform_asid_pool_invocation iv
   \<lbrace> \<lambda>_. valid_vspace_objs' \<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (wpsimp wp: get_cap_wp)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule (1) valid_capsD)
  apply (clarsimp simp: is_ArchObjectCap_def is_PageTableCap_def valid_cap_def)
  apply (erule (1) is_aligned_pt)
  done

crunch perform_asid_pool_invocation,
     perform_asid_control_invocation
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (ignore: delete_objects set_object
       wp: hoare_weak_lift_imp crunch_wps
     simp: crunch_simps unless_def)

lemma pte_range_interD:
 "pte_range pte p \<inter> pte_range pte' p' \<noteq> {}
  \<Longrightarrow> pte \<noteq> InvalidPTE \<and> pte' \<noteq> InvalidPTE
      \<and> p = p'"
  apply (drule int_not_emptyD)
  apply (case_tac pte,simp_all split:if_splits)
   apply (case_tac pte',simp_all split:if_splits)
  apply (case_tac pte',simp_all split:if_splits)
  done

lemma perform_page_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_page_inv pinv\<rbrace>
        perform_page_invocation pinv \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases pinv,
         simp_all add: mapM_discarded
                split: sum.split arch_cap.split option.split,
         safe intro!: hoare_gen_asm hoare_gen_asm[unfolded K_def],
         simp_all add: mapM_x_Nil mapM_x_Cons mapM_x_map)
    apply (wp store_pte_valid_vspace_objs' hoare_vcg_imp_lift[OF set_cap_arch_obj_neg]
              hoare_vcg_all_lift
           | clarsimp simp: cte_wp_at_weakenE[OF _ TrueI] obj_at_def swp_def valid_page_inv_def
                            valid_slots_def perform_pg_inv_map_def perform_pg_inv_unmap_def
                            perform_pg_inv_get_addr_def
                     split: pte.splits
           | wpc
           | wp (once) hoare_drop_imps)+
  done

lemma perform_page_table_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_pti pinv\<rbrace>
      perform_page_table_invocation pinv \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: perform_page_table_invocation_def split_def perform_pt_inv_map_def
                   perform_pt_inv_unmap_def
             cong: page_table_invocation.case_cong
                   option.case_cong cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift store_pte_valid_vspace_objs'
             set_cap_arch_obj hoare_vcg_all_lift mapM_x_wp'
              | wpc
              | simp add: swp_def
              | strengthen all_imp_ko_at_from_ex_strg
              | wp (once) hoare_drop_imps)+
  done

lemma perform_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i and valid_vspace_objs'\<rbrace>
      perform_invocation blocking call i
         \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (cases i, simp_all)
  apply (wp send_signal_interrupt_states | simp)+
  apply (simp add: arch_perform_invocation_def)
  apply (wp | wpc | simp)+
  apply (auto simp: valid_arch_inv_def intro: valid_objs_caps)
  done

crunch handle_fault, reply_from_kernel
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps wp: crunch_wps)

lemma handle_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active\<rbrace>
        handle_invocation calling blocking \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid set_thread_state_ct_st
               | simp add: split_def | wpc
               | wp (once) hoare_drop_imps)+
  apply (auto simp: ct_in_state_def elim: st_tcb_ex_cap)
  done


crunch activate_thread,switch_to_thread, handle_hypervisor_fault,
       switch_to_idle_thread, handle_call, handle_recv, handle_reply,
       handle_send, handle_yield, handle_interrupt,
       schedule_choose_new_thread, arch_prepare_next_domain
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps wp: crunch_wps OR_choice_weak_wp select_ext_weak_wp
      ignore: without_preemption getActiveIRQ resetTimer ackInterrupt
              OR_choice set_scheduler_action)

lemma handle_event_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active\<rbrace> handle_event e \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (case_tac e; simp) (wpsimp simp: Let_def handle_vm_fault_def | wp (once) hoare_drop_imps)+

lemma schedule_valid_vspace_objs'[wp]:
  "schedule \<lbrace>valid_vspace_objs'\<rbrace>"
  unfolding schedule_def by (wpsimp wp: hoare_drop_imps)

lemma call_kernel_valid_vspace_objs'[wp]:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and valid_vspace_objs'\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  apply (cases e, simp_all add: call_kernel_def)
      apply (rule hoare_pre)
       apply (wp | simp add: Let_def handle_vm_fault_def | wpc
                 | rule conjI | clarsimp simp: ct_in_state_def
                 | erule pred_tcb_weakenE
                 | wp (once) hoare_drop_imps)+
  done

end

end
