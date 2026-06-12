(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVSpaceEntries_AI
imports VSpaceEntries_AI
begin

context Arch begin arch_global_naming

(* Since we're not doing anything with the index apart from returning it, this definition works
   for both, NormalPTs and VSRootPTs *)
primrec pt_valid_idxs :: "pte \<Rightarrow> 'a word \<Rightarrow> ('a word) set" where
  "pt_valid_idxs (InvalidPTE) p = {}"
| "pt_valid_idxs (PagePTE ptr sm attr rights) p = {p}"
| "pt_valid_idxs (PageTablePTE ptr) p = {p}"

abbreviation "valid_pt_entries \<equiv> valid_entries pt_valid_idxs"

definition obj_valid_vspace :: "kernel_object \<Rightarrow> bool" where
 "obj_valid_vspace obj \<equiv> case obj of
    ArchObj (PageTable (VSRootPT pt)) \<Rightarrow> valid_pt_entries pt
  | ArchObj (PageTable (NormalPT pt)) \<Rightarrow> valid_pt_entries pt
  | _ \<Rightarrow> True"

lemmas obj_valid_vspace_simps[simp]
    = obj_valid_vspace_def
        [split_simps Structures_A.kernel_object.split
                     arch_kernel_obj.split]

locale_abbrev
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

crunch
  vcpu_save, vcpu_restore, vcpu_enable, get_vcpu, set_vcpu, vcpu_disable, vcpu_read_reg,
  read_vcpu_register,write_vcpu_register
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps simp: crunch_simps ignore: set_object do_machine_op)

lemma vcpu_switch_valid_vspace_objs'[wp]:
  "vcpu_switch v \<lbrace> valid_vspace_objs'\<rbrace>"
  unfolding vcpu_switch_def
  by wpsimp

lemma valid_pt_entries_invalid[simp]:
  "valid_pt_entries (\<lambda>x. InvalidPTE)"
   by (simp add:valid_entries_def)

lemma valid_vspace_objs'_ptD:
  "\<lbrakk>valid_vspace_objs' s;
    kheap s ptr = Some (ArchObj (PageTable (NormalPT pt)))\<rbrakk>
   \<Longrightarrow> valid_pt_entries pt"
  by (fastforce simp:ran_def)

lemma valid_vspace_objs'_vsD:
  "\<lbrakk>valid_vspace_objs' s;
    kheap s ptr = Some (ArchObj (PageTable (VSRootPT pt)))\<rbrakk>
   \<Longrightarrow> valid_pt_entries pt"
  by (fastforce simp:ran_def)

lemma store_pte_valid_vspace_objs'[wp]:
  "store_pte pt_t p pte \<lbrace>valid_vspace_objs'\<rbrace>"
  apply (simp add: store_pte_def set_pt_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def pt_upd_def split: pt.splits)
  apply (rule conjI; clarsimp; rename_tac pt)
   apply (rule valid_entries_overwrite_0, fastforce simp:ran_def)
   apply (case_tac "pt pa"; case_tac pte; simp)
  apply (rule valid_entries_overwrite_0, fastforce simp:ran_def)
  apply (case_tac "pt pa"; case_tac pte; simp)
  done

crunch invalidate_tlb_by_asid_va, invalidate_tlb_by_asid, unmap_page_table
  for vspace_objs'[wp]: valid_vspace_objs'

lemma unmap_page_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> unmap_page sz asid vptr pptr \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: unmap_page_def mapM_discarded
             cong: vmpage_size.case_cong)
  apply wpsimp
  done

crunch set_simple_ko, set_thread_state
 for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps)

lemma set_reply_obj_ref_valid_vspace_objs'[wp]:
  "set_reply_obj_ref upd r new \<lbrace>valid_vspace_objs'\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma set_ntfn_obj_ref_valid_vspace_objs'[wp]:
  "set_ntfn_obj_ref upd r new \<lbrace>valid_vspace_objs'\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

crunch finalise_cap, cap_swap_for_delete, empty_slot
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps preemption_point_inv hoare_vcg_all_lift
   simp: crunch_simps unless_def ignore:set_object set_thread_state_act update_sk_obj_ref)

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

crunch cancel_badged_sends
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps filterM_mapM wp: crunch_wps ignore: filterM)

crunch cap_move, cap_insert
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"

lemma invoke_cnode_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  unfolding invoke_cnode_def
  by (wpsimp wp: get_cap_wp split_del: if_split)

crunch invoke_tcb, invoke_domain
  for valid_vspace_objs'[wp]: valid_vspace_objs'
  (wp: check_cap_inv crunch_wps simp: crunch_simps is_round_robin_def
       ignore: check_cap_at update_sk_obj_ref)

crunch set_extra_badge, transfer_caps_loop
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (rule: transfer_caps_loop_pres)

crunch
  send_ipc, send_signal, do_reply_transfer, invoke_irq_control, invoke_irq_handler
  for valid_vspace_objs'[wp]: valid_vspace_objs'
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps
   ignore: clearMemory const_on_failure set_object update_sk_obj_ref)

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
            split: kernel_object.splits apiobject_type.split aobject_type.split)+
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
  unfolding init_arch_objects_def by (wpsimp wp: mapM_x_wp')

lemma delete_objects_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (rule delete_objects_reduct) (wp detype_valid_vspace)

crunch reset_untyped_cap
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: mapME_x_inv_wp crunch_wps simp: crunch_simps unless_def)

lemma invoke_untyped_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread)
    and valid_untyped_inv ui\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q)
      apply (wp init_arch_objects_valid_vspace | simp)+
     apply (auto simp: post_retype_invs_def split: if_split_asm)[1]
    apply (wp | simp)+
  done

crunch store_asid_pool_entry
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"

crunch perform_vcpu_invocation
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (ignore: delete_objects wp: hoare_drop_imps)

lemma decode_vcpu_invocation_valid_vspace_objs'[wp]:
  "\<lbrace> valid_vspace_objs' \<rbrace>
     decode_vcpu_invocation label args vcap excaps
   \<lbrace>\<lambda>_. valid_vspace_objs' \<rbrace>, -"
  unfolding decode_vcpu_invocation_def
  by (wpsimp wp: get_cap_wp)

lemma perform_asid_pool_invocation_valid_vspace_objs'[wp]:
  "\<lbrace> valid_vspace_objs' and valid_arch_state and pspace_aligned and
     (\<lambda>s. valid_caps (caps_of_state s) s) \<rbrace>
   perform_asid_pool_invocation iv
   \<lbrace> \<lambda>_. valid_vspace_objs' \<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (wpsimp wp: get_cap_wp)
  done

crunch perform_asid_pool_invocation,
     perform_asid_control_invocation
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (ignore: delete_objects set_object
       wp: hoare_weak_lift_imp crunch_wps
     simp: crunch_simps unless_def)

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
              hoare_vcg_all_lift hoare_vcg_const_imp_lift hoare_vcg_if_lift
           | clarsimp simp: cte_wp_at_weakenE[OF _ TrueI] obj_at_def swp_def valid_page_inv_def
                            valid_slots_def perform_pg_inv_map_def perform_pg_inv_unmap_def
                            perform_pg_inv_get_addr_def perform_flush_def
                     split: pte.splits
                     split del: if_split
           | rule conjI
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

crunch invoke_sched_context, invoke_sched_control_configure_flags
  for valid_vspace_objs'[wp]: valid_vspace_objs'
  (ignore: update_sk_obj_ref wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps cong: if_cong)

(* FIXME RT: move to Invariants_AI *)
lemma invs_valid_caps[elim]:
  "invs s \<Longrightarrow> valid_caps (caps_of_state s) s"
  by (fastforce intro: valid_objs_caps)

lemma perform_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i and valid_vspace_objs' and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   perform_invocation blocking call can_donate i
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  by (cases i;
      wpsimp wp: send_signal_interrupt_states hoare_drop_imps
           simp: arch_perform_invocation_def perform_vspace_invocation_def perform_flush_def
                 perform_sgi_invocation_def perform_smc_invocation_def)
     (auto simp add: valid_arch_inv_def)

crunch handle_fault, reply_from_kernel
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps wp: crunch_wps)

lemma handle_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_vspace_objs' s \<and> invs s \<and> ct_active s \<and>
        scheduler_action s = resume_cur_thread \<and> ct_schedulable s\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid set_thread_state_ct_st sts_schedulable_scheduler_action
         | simp add: split_def cong: conj_cong | wpc
         | wp (once) hoare_drop_imps)+
  apply (fastforce simp: ct_in_state_def)
  done

crunch
  activate_thread, switch_to_thread, handle_hypervisor_fault,
  switch_to_idle_thread, handle_call, handle_recv, handle_vm_fault,
  handle_send, handle_yield, handle_interrupt, check_budget_restart, update_time_stamp,
  schedule_choose_new_thread, arch_prepare_next_domain, maybe_handle_interrupt,
  activate_thread, switch_to_thread, check_domain_time, preemption_path
  for valid_vspace_objs'[wp]: valid_vspace_objs'
  (simp: crunch_simps wp: crunch_wps hoare_vcg_all_lift
   ignore: without_preemption getActiveIRQ resetTimer ackInterrupt update_sk_obj_ref)

crunch awaken, sc_and_timer
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: hoare_drop_imps hoare_vcg_if_lift2 crunch_wps)

lemma handle_event_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active
    and (\<lambda>s. scheduler_action s = resume_cur_thread) and ct_schedulable\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  by (case_tac e; wpsimp wp: check_budget_restart_true hoare_vcg_if_lift2 hoare_drop_imps)

lemma schedule_valid_vspace_objs'[wp]:
  "schedule \<lbrace>valid_vspace_objs'\<rbrace>"
  unfolding schedule_def by (wpsimp wp: hoare_drop_imps)

lemma call_kernel_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread) and ct_schedulable\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  apply (cases e, simp_all add: call_kernel_def)
      apply (rule hoare_pre)
       by (wp | simp add: Let_def handle_vm_fault_def | wpc
              | rule conjI | clarsimp simp: ct_in_state_def
              | erule pred_tcb_weakenE
              | wp (once) check_budget_restart_true hoare_vcg_if_lift2 hoare_drop_imps)+

end

end
