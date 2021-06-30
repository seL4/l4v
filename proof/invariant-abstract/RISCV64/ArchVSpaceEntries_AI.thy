(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVSpaceEntries_AI
imports "../VSpaceEntries_AI"
begin

context Arch begin global_naming RISCV64

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

crunch valid_vspace_objs'[wp]: cap_insert, cap_swap_for_delete,empty_slot "valid_vspace_objs'"
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
  apply (rule hoare_seq_ext, assumption)
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

crunch valid_vspace_objs'[wp]: set_simple_ko, set_thread_state "valid_vspace_objs'"
  (wp: crunch_wps)

lemma set_reply_obj_ref_valid_vspace_objs'[wp]:
  "set_reply_obj_ref upd r new \<lbrace>valid_vspace_objs'\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma set_ntfn_obj_ref_valid_vspace_objs'[wp]:
  "set_ntfn_obj_ref upd r new \<lbrace>valid_vspace_objs'\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

crunch valid_vspace_objs'[wp]: finalise_cap, cap_swap_for_delete, empty_slot "valid_vspace_objs'"
  (wp: crunch_wps select_wp preemption_point_inv hoare_vcg_all_lift
   simp: crunch_simps unless_def ignore:set_object set_thread_state_act update_sk_obj_ref)

lemma preemption_point_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> preemption_point \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (wp preemption_point_inv | simp)+

lemmas cap_revoke_preservation_valid_vspace_objs = cap_revoke_preservation[OF _,
                                                          where E=valid_vspace_objs',
                                                          simplified, THEN validE_valid]

lemmas rec_del_preservation_valid_vspace_objs = rec_del_preservation[OF _ _ _ _,
                                                    where P=valid_vspace_objs', simplified]

crunch valid_vspace_objs'[wp]: cap_delete, cap_revoke "valid_vspace_objs'"
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

crunch valid_vspace_objs'[wp]: cancel_badged_sends "valid_vspace_objs'"
  (simp: crunch_simps filterM_mapM wp: crunch_wps ignore: filterM)

crunch valid_vspace_objs'[wp]: cap_move, cap_insert "valid_vspace_objs'"

lemma invoke_cnode_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp | wpc | simp split del: if_split)+
  done

crunch valid_vspace_objs'[wp]: invoke_tcb "valid_vspace_objs'"
  (wp: check_cap_inv crunch_wps simp: crunch_simps
       ignore: check_cap_at update_sk_obj_ref)

crunch valid_vspace_objs'[wp]: invoke_domain "valid_vspace_objs'"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_vspace_objs'[wp]: set_extra_badge, transfer_caps_loop "valid_vspace_objs'"
  (rule: transfer_caps_loop_pres)

crunch valid_vspace_objs'[wp]: send_ipc, send_signal,
    do_reply_transfer, invoke_irq_control, invoke_irq_handler "valid_vspace_objs'"
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
            split: Structures_A.kernel_object.splits
    Structures_A.apiobject_type.split aobject_type.split)+
  done

lemma detype_valid_vspace[elim!]:
  "valid_vspace_objs' s \<Longrightarrow> valid_vspace_objs' (detype S s)"
  by (auto simp add: detype_def ran_def)

crunch valid_vspace_objs'[wp]: create_cap "valid_vspace_objs'"
  (ignore: clearMemory simp: crunch_simps)

lemma init_arch_objects_valid_vspace:
  "\<lbrace>valid_vspace_objs' and pspace_aligned and valid_arch_state
           and K (orefs = retype_addrs ptr type n us)
           and K (range_cover ptr sz (obj_bits_api type us) n)\<rbrace>
     init_arch_objects type ptr n obj_sz orefs
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  unfolding init_arch_objects_def by wpsimp

lemma delete_objects_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (rule delete_objects_reduct) (wp detype_valid_vspace)

crunch valid_vspace_objs'[wp]: reset_untyped_cap "valid_vspace_objs'"
  (wp: mapME_x_inv_wp crunch_wps simp: crunch_simps unless_def)

lemma invoke_untyped_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread)
          and valid_untyped_inv ui\<rbrace>
       invoke_untyped ui
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q)
      apply (wp init_arch_objects_valid_vspace | simp)+
     apply (auto simp: post_retype_invs_def split: if_split_asm)[1]
    apply (wp | simp)+
  done

crunches store_asid_pool_entry
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

crunch valid_vspace_objs'[wp]: perform_asid_pool_invocation,
     perform_asid_control_invocation "valid_vspace_objs'"
  (ignore: delete_objects set_object
       wp: static_imp_wp select_wp crunch_wps
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

context
notes if_cong[cong]
begin

crunches invoke_sched_context, invoke_sched_control_configure_flags
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (ignore: update_sk_obj_ref wp: crunch_wps)

end

(* FIXME RT: move to Invariants_AI *)
lemma invs_valid_caps[elim]:
  "invs s \<Longrightarrow> valid_caps (caps_of_state s) s"
  by (fastforce intro: valid_objs_caps)

lemma perform_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i and valid_vspace_objs' and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   perform_invocation blocking call can_donate i
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  by (cases i; wpsimp wp: send_signal_interrupt_states simp: arch_perform_invocation_def)
     (auto simp add: valid_arch_inv_def)

crunch valid_vspace_objs'[wp]: handle_fault, reply_from_kernel "valid_vspace_objs'"
  (simp: crunch_simps wp: crunch_wps)

lemma handle_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_vspace_objs' s \<and> invs s \<and> ct_active s \<and>
        scheduler_action s = resume_cur_thread \<and> is_schedulable_bool (cur_thread s) s\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid set_thread_state_ct_st sts_schedulable_scheduler_action
         | simp add: split_def cong: conj_cong | wpc
         | wp (once) hoare_drop_imps)+
  apply (fastforce simp: ct_in_state_def)
  done

crunches activate_thread,switch_to_thread, handle_hypervisor_fault,
         switch_to_idle_thread, handle_call, handle_recv, handle_vm_fault,
         handle_send, handle_yield, handle_interrupt, check_budget_restart, update_time_stamp,
         schedule_choose_new_thread, activate_thread, switch_to_thread
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps wp: crunch_wps
   ignore: without_preemption getActiveIRQ resetTimer ackInterrupt update_sk_obj_ref)

crunches awaken, sc_and_timer
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: hoare_drop_imps hoare_vcg_if_lift2 crunch_wps)

lemma schedule_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> schedule :: (unit,unit) s_monad \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  unfolding schedule_def by (wpsimp wp: alternative_wp select_wp hoare_drop_imps)

(* FIXME RT: clean up the duplication here (also in ARM); factor out handle_event? *)
lemma call_kernel_valid_vspace_objs'[wp]:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and valid_vspace_objs' and
    (\<lambda>s. scheduler_action s = resume_cur_thread) and (\<lambda>s. is_schedulable_bool (cur_thread s) s)\<rbrace>
      (call_kernel e) :: (unit,unit) s_monad
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  apply (cases e, simp_all add: call_kernel_def preemption_path_def)
       apply (rule hoare_seq_ext[rotated])
        apply (rule validE_valid)
        apply (rule_tac Q="\<lambda>_. valid_vspace_objs'" in handleE_wp[rotated])
         apply (rule_tac B="\<lambda>_. invs and ct_running and valid_vspace_objs' and
           (\<lambda>s. scheduler_action s = resume_cur_thread) and
           (\<lambda>s. is_schedulable_bool (cur_thread s) s)" in seqE)
          apply (rule liftE_wp)
          apply (wpsimp wp: hoare_vcg_ex_lift)
         apply (rule_tac B="\<lambda>rv. invs and (\<lambda>s. rv \<longrightarrow> ct_running s) and
           valid_vspace_objs' and
           (\<lambda>s. rv \<longrightarrow> scheduler_action s = resume_cur_thread) and
           (\<lambda>s. rv \<longrightarrow> (is_schedulable_bool (cur_thread s) s))" in seqE)
          apply (rule liftE_wp)
          apply (wpsimp wp: check_budget_restart_true)
         apply (rule valid_validE)
         apply (wpsimp)
         apply (fastforce simp: ct_in_state_def pred_tcb_weakenE)
        apply (wpsimp wp: is_schedulable_wp hoare_vcg_all_lift hoare_drop_imps hoare_vcg_if_lift2)
       apply wpsimp
    (***)
      apply (rule_tac B="\<lambda>_. valid_vspace_objs'" in hoare_seq_ext[rotated])
       apply (rule validE_valid)
       apply (rule liftE_wp)
       apply (rule_tac B="\<lambda>_. invs and ct_running and
           valid_vspace_objs' and
           (\<lambda>s. bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) (cur_thread s) s)" in hoare_seq_ext[rotated])
        apply wpsimp
        apply (clarsimp simp: pred_tcb_at_def obj_at_def is_schedulable_bool_def')
       apply (rule_tac B="\<lambda>rv. invs and (\<lambda>s. rv \<longrightarrow> ct_running s) and valid_vspace_objs'"
                       in hoare_seq_ext[rotated])
        apply (wpsimp wp: check_budget_restart_true)
       apply (wpsimp+)[2]
    (***)
     apply (rule_tac B="\<lambda>_. valid_vspace_objs'" in hoare_seq_ext[rotated])
      apply (rule validE_valid)
      apply (rule liftE_wp)
      apply (rule_tac B="\<lambda>_. invs and ct_running and
           valid_vspace_objs' and
           (\<lambda>s. bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) (cur_thread s) s)" in hoare_seq_ext[rotated])
       apply wpsimp
       apply (clarsimp simp: pred_tcb_at_def obj_at_def is_schedulable_bool_def')
      apply (rule_tac B="\<lambda>rv. invs and (\<lambda>s. rv \<longrightarrow> ct_running s) and valid_vspace_objs'"
                      in hoare_seq_ext[rotated])
       apply (wpsimp wp: check_budget_restart_true)
      apply (wpsimp+)[2]
    (***)
    apply (wpsimp wp: hoare_vcg_if_lift2)
    (***)
   apply (rule_tac B="\<lambda>_. valid_vspace_objs'" in hoare_seq_ext[rotated])
    apply (rule validE_valid)
    apply (rule liftE_wp)
    apply (rule_tac B="\<lambda>_. invs and ct_running and
           valid_vspace_objs' and
           (\<lambda>s. bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) (cur_thread s) s)" in hoare_seq_ext[rotated])
     apply wpsimp
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_schedulable_bool_def')
    apply (rule_tac B="\<lambda>rv. invs and (\<lambda>s. rv \<longrightarrow> ct_running s) and
           valid_vspace_objs'" in hoare_seq_ext[rotated])
     apply (wpsimp wp: check_budget_restart_true)
    apply (wpsimp+)[2]
    (***)
  apply wpsimp
  done

end

end
