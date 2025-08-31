(*
 * Copyright 2024, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVCPUDomain_AI
imports ArchVCPU_AI
begin

context Arch begin arch_global_naming

section \<open>cur_vcpu_in_cur_domain\<close>
\<comment> \<open>FIXME: @{term cur_vcpu} could be reworked so that it could be reused here\<close>
definition cur_vcpu_tcb :: "'z::state_ext state \<Rightarrow> obj_ref option" where
  "cur_vcpu_tcb s \<equiv>
     case arm_current_vcpu (arch_state s) of
       Some (v, _) \<Rightarrow> vcpu_tcbs_of s v
     | None \<Rightarrow> None"

definition cur_vcpu_in_cur_domain :: "det_ext state \<Rightarrow> bool" where
  "cur_vcpu_in_cur_domain s \<equiv>
     case cur_vcpu_tcb s of
       Some t \<Rightarrow> in_cur_domain t s
     | None \<Rightarrow> True"

lemmas cur_vcpu_in_cur_domain_defs = cur_vcpu_in_cur_domain_def cur_vcpu_tcb_def in_cur_domain_def

lemma cur_vcpu_in_cur_domain_lift_strong:
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (arm_current_vcpu (arch_state s))\<rbrace>"
                "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
                "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
                "\<And>P t. f \<lbrace>etcb_at (\<lambda>t. P (etcb_domain t)) t\<rbrace>"
  shows "f \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding cur_vcpu_in_cur_domain_defs
  by (wp_pre, wps, wpsimp wp: valid_case_option_post_wp split: option.splits)

lemma cur_vcpu_in_cur_domain_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arm_current_vcpu (arch_state s))\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
          "\<And>P. f \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  shows "f \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
 by (rule cur_vcpu_in_cur_domain_lift_strong assms)+

\<comment> \<open>This simp could possibly be avoided if arm_current_vcpu updates were wrapped in a function
    instead of directly using modifies.\<close>
lemma cur_vcpu_in_cur_domain_current_vcpu_update[simp]:
  "cur_vcpu_in_cur_domain (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (v, b)\<rparr>\<rparr>)
   = (\<forall>t. vcpu_tcbs_of s v = Some t \<longrightarrow> in_cur_domain t s)"
  "cur_vcpu_in_cur_domain (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := None\<rparr>\<rparr>)"
  by (auto simp: cur_vcpu_in_cur_domain_defs split: option.splits)

\<comment> \<open>FIXME: use projections instead of this\<close>
lemma cur_vcpu_in_cur_domain_updates[simp]:
  "cur_vcpu_in_cur_domain (cur_thread_update f_ct s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (machine_state_update f_ms s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (cdt_update f_cdt s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (cdt_list_update f_cdt_list s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (work_units_completed_update f_work_units s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (interrupt_states_update f_interrupt_states s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (is_original_cap_update f_orig_cap s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (arch_state_update (arm_asid_table_update f_asid_table) s) = cur_vcpu_in_cur_domain s"
  "cur_vcpu_in_cur_domain (s\<lparr>arch_state := (arm_asid_table_update f_asid_table) (arch_state s)\<rparr>) = cur_vcpu_in_cur_domain s" \<comment> \<open>FIXME: previous line doesn't work for this, can it be generalised?\<close>
  by (auto simp: cur_vcpu_in_cur_domain_defs)

\<comment> \<open>schedule\<close>

lemma as_user_vcpus_of[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding as_user_def
  by (wpsimp wp: set_object_wp_strong)
     (fastforce simp: opt_map_def obj_at_def split: option.splits elim!: rsubst[where P=P])

crunch set_scheduler_action, tcb_sched_action, as_user
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift)

lemma vcpu_write_reg_vcpu_tcbs_of[wp]:
  "vcpu_write_reg vr reg val \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vcpu_write_reg_def
  by wpsimp (fastforce simp: opt_map_def elim!: rsubst[where P=P])

lemma vgic_update_vcpu_tcbs_of[wp]:
  "vgic_update vr f \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vgic_update_def
  by wpsimp (fastforce simp: opt_map_def elim!: rsubst[where P=P])

lemma vcpu_save_reg_vcpu_tcbs_of[wp]:
  "vcpu_save_reg vr reg \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vcpu_save_reg_def
  apply wpsimp
  by (fastforce simp: opt_map_def elim!: rsubst[where P=P])

lemma save_virt_timer_vcpu_tcbs_of[wp]:
  "save_virt_timer vcpu_ptr \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding save_virt_timer_def
  apply wpsimp
         apply (rule hoare_post_imp[where Q'="\<lambda>_ s. P (vcpu_tcbs_of s)"])
          apply (fastforce simp: opt_map_def elim!: rsubst[where P=P])
         by wpsimp+

crunch vcpu_disable, vcpu_restore, vcpu_save
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  (wp: crunch_wps)

lemma vcpu_switch_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> none_top ((\<lambda>t. in_cur_domain t s) |< vcpu_tcbs_of s) v\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift in_cur_domain_lift_weak)
  by (auto simp: cur_vcpu_in_cur_domain_defs opt_pred_def)

crunch set_vm_root, lazy_fpu_restore
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  (wp: crunch_wps set_object_wp_strong simp: crunch_simps)

crunch set_vm_root, set_global_user_vspace, lazy_fpu_restore
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift)

\<comment> \<open>FIXME: move (where?)\<close>
lemma bound_tcb_bound_vcpu_at:
  "\<lbrakk>sym_refs (state_hyp_refs_of s); valid_objs s;
    arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = (Some vcpuptr)) tcbptr s \<rbrakk>
  \<Longrightarrow> vcpu_tcbs_of s vcpuptr = Some tcbptr"
  apply (drule_tac x=tcbptr in sym_refsD[rotated])
   apply (fastforce simp: state_hyp_refs_of_def pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: pred_tcb_def2)
  apply (frule (1) valid_tcb_objs)
  apply (clarsimp simp: valid_tcb_def valid_arch_tcb_def typ_at_eq_kheap_obj)
  apply (fastforce simp: in_omonad valid_obj_def valid_vcpu_def state_hyp_refs_of_def
                  split: option.splits)
  done

lemma arch_switch_to_thread_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_objs s \<and> in_cur_domain t s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding arch_switch_to_thread_def
  apply wpsimp
  apply (frule (1) valid_tcb_objs)
  apply (clarsimp simp: valid_tcb_def valid_arch_tcb_def typ_at_eq_kheap_obj)
  apply (drule (1) bound_tcb_bound_vcpu_at[where tcbptr=t])
   apply (fastforce simp: pred_tcb_def2)
  apply (auto simp: in_omonad)
  done

crunch guarded_switch_to, switch_to_idle_thread
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps)

lemma choose_thread_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_queues s \<and> valid_objs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   choose_thread
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding choose_thread_def
  apply wpsimp
  apply (fastforce dest!: next_thread_queued split: option.splits
                   simp: etcb_at_def next_thread_def valid_queues_def in_cur_domain_def)
  done

lemma next_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. arm_current_vcpu (arch_state s) = None\<rbrace> next_domain \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding next_domain_def Let_def
  by (wpsimp wp: dxo_wp_weak simp: cur_vcpu_in_cur_domain_defs)

lemma vcpu_flush_arm_current_vcpu_None[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_flush \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None\<rbrace>"
  unfolding vcpu_flush_def
  by wpsimp

crunch next_domain, vcpu_flush, switch_local_fpu_owner
  for hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_objs[wp]: valid_objs
  (simp: crunch_simps wp: dxo_wp_weak crunch_wps ignore: arch_thread_set)

lemma schedule_choose_new_thread_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_queues s \<and> valid_objs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding schedule_choose_new_thread_def arch_prepare_next_domain_def
  by wpsimp

lemma schedule_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> valid_sched s \<and> valid_objs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   schedule
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding schedule_def schedule_switch_thread_fastfail_def
  apply (wpsimp wp: hoare_drop_imps gts_wp)
  by (safe; (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                             switch_in_cur_domain_def st_tcb_at_def obj_at_def)?)


\<comment> \<open>handle_interrupt\<close>

lemma set_endpoint_vcpus_of[wp]:
  "set_endpoint p ep \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_simple_ko_def
  by (wpsimp wp: set_object_wp get_object_wp)
     (fastforce simp: opt_map_def obj_at_def elim!: rsubst[where P=P])

lemma set_notification_vcpus_of[wp]:
  "set_notification p ntfn \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_simple_ko_def
  by (wpsimp wp: set_object_wp get_object_wp)
     (fastforce simp: opt_map_def obj_at_def elim!: rsubst[where P=P])

lemma thread_set_vcpus_of[wp]:
  "thread_set p t \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding thread_set_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

lemma set_bound_notification_vcpus_of[wp]:
  "set_bound_notification p ntfn \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_bound_notification_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

crunch store_word_offs
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"

lemma set_mrs_vcpus_of[wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_mrs_def zipWithM_x_mapM
  by (wpsimp wp: mapM_wp[where S=UNIV] set_object_wp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

crunch set_extra_badge, handle_fault
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"
  (wp: crunch_wps transfer_caps_loop_pres
   simp: crunch_simps
   ignore: set_simple_ko)

lemma vppi_event_vcpu_tcbs_of[wp]:
  "vppi_event irq \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding vppi_event_def
  by (wpsimp)
     (fastforce simp: opt_map_def get_tcb_def split: option.splits elim!: rsubst[where P=P])

crunch handle_interrupt
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong dxo_wp_weak crunch_wps
   simp: crunch_simps
   ignore: set_simple_ko)


\<comment> \<open>handle_event\<close>

lemma retype_region_valid_cur_vcpu[wp]:
  "retype_region ptr numObjects o_bits type dev \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding retype_region_def
  apply (wpsimp simp_del: fun_upd_apply simp: foldr_fun_upd_value)
  by (auto simp: cur_vcpu_in_cur_domain_defs etcb_at'_def
                 default_object_def default_arch_object_def default_tcb_def default_arch_tcb_def
                 default_vcpu_def opt_map_def etcbs_of'_def
          split: option.splits apiobject_type.splits aobject_type.splits)

crunch do_machine_op, create_cap, init_arch_objects
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift crunch_wps simp: crunch_simps)

lemma delete_objects_valid_cur_vcpu[wp]:
  "delete_objects ptr bits \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding delete_objects_def
  apply wpsimp
   apply (rule hoare_strengthen_post, rule do_machine_op_cur_vcpu_in_cur_domain)
  by (auto simp: cur_vcpu_in_cur_domain_defs etcb_at'_def detype_def opt_map_def etcbs_of'_def
          split: option.splits)

crunch invoke_untyped
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps mapME_x_wp' preemption_point_inv' simp: crunch_simps mapM_x_def_bak) \<comment> \<open>FIXME: change invoke_untyped to use mapM_x\<close>

lemma set_vcpu_None_valid_cur_vcpu[wp]:
  "set_vcpu vcpu_ptr (v\<lparr>vcpu_tcb := None\<rparr>) \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding cur_vcpu_in_cur_domain_defs
  apply (wp_pre, wps, wpsimp)
  by (auto split: option.splits simp: opt_map_def)

crunch arch_thread_set, vcpu_disable
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift crunch_wps simp: crunch_simps)

lemma vcpu_invalidate_active_valid_cur_vcpu[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by wpsimp

lemma dissociate_vcpu_tcb_valid_cur_vcpu[wp]:
  "dissociate_vcpu_tcb vcpu_ptr tcb_ptr \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  by (wpsimp wp: hoare_drop_imps)

crunch cap_move, suspend, delete_asid_pool, unmap_page, cancel_badged_sends
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps filterM_mapM)

crunch
  cap_insert, cap_move, cap_swap, set_thread_state, unbind_maybe_notification, unbind_notification,
  cancel_all_ipc, suspend, cancel_all_signals, delete_asid_pool, unmap_page, delete_asid,
  unmap_page_table, cancel_badged_sends, empty_slot, fpu_release
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong crunch_wps dxo_wp_weak
   simp: crunch_simps filterM_mapM
   ignore: set_simple_ko tcb_sched_action)

crunch invoke_cnode
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps preemption_point_inv' cap_revoke_preservation dxo_wp_weak
   simp: crunch_simps)

crunch set_priority
  for etcb_at_domain[wp]: "etcb_at (\<lambda>t. P (etcb_domain t)) t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: thread_set_no_change_etcb_at)

crunch set_mcpriority, bind_notification
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps thread_set_no_change_etcb_at simp: crunch_simps etcb_of_def)

crunch cancel_ipc, set_mcpriority, set_priority, bind_notification
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong ignore: set_simple_ko)

lemma thread_set_no_etcb_change_cur_vcpu_in_cur_domain:
  assumes x: "\<And>P tcb. P (tcb_domain (f tcb)) = (P (tcb_domain tcb) :: bool)"
  shows      "thread_set f t' \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  by (wpsimp wp: cur_vcpu_in_cur_domain_lift_strong thread_set_no_change_etcb_at simp: x)

lemma option_update_thread_no_etcb_change_cur_vcpu_in_cur_domain:
  assumes x: "\<And>P val tcb. P (tcb_domain (f val tcb)) = (P (tcb_domain tcb) :: bool)"
  shows      "option_update_thread t f opt \<lbrace>cur_vcpu_in_cur_domain\<rbrace>"
  unfolding option_update_thread_def
  by (wpsimp wp: cur_vcpu_in_cur_domain_lift_strong thread_set_no_change_etcb_at simp: x)

crunch invoke_tcb
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps check_cap_inv thread_set_no_etcb_change_cur_vcpu_in_cur_domain
       option_update_thread_no_etcb_change_cur_vcpu_in_cur_domain)

lemma set_vcpu_not_current_cur_vcpu_in_cur_domain:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> map_option fst (arm_current_vcpu (arch_state s)) \<noteq> Some vcpu_ptr\<rbrace>
   set_vcpu vcpu_ptr v
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding cur_vcpu_in_cur_domain_defs
  apply (wp_pre, wps, wpsimp)
  by (auto split: option.splits simp: opt_map_def)

lemma dissociate_vcpu_tcb_not_current_vcpu[wp]:
  "\<lbrace>\<top>\<rbrace> dissociate_vcpu_tcb vcpu_ptr tcb_ptr \<lbrace>\<lambda>_ s. map_option fst (arm_current_vcpu (arch_state s)) \<noteq> Some vcpu_ptr\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  by (wpsimp wp: get_vcpu_wp arch_thread_get_wp vcpu_invalid_active_arm_current_vcpu_None[THEN hoare_strengthen_post])

crunch dissociate_vcpu_tcb
  for vcpus_of_None[wp]: "\<lambda>s. vcpus_of s vcpu_ptr = None"
  (wp: hoare_vcg_imp_lift' get_vcpu_wp arch_thread_get_wp simp: if_option_eq)

crunch dissociate_vcpu_tcb
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)

lemma vcpu_invalidate_active_cur_vcpu[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>_ s. cur_vcpu_2 (arm_current_vcpu (arch_state s)) (P s)\<rbrace>"
  unfolding vcpu_invalidate_active_def cur_vcpu_def
  by wpsimp

lemma dissociate_vcpu_tcb_cur_vcpu[wp]:
  "dissociate_vcpu_tcb vcpu_ptr tcb_ptr \<lbrace>cur_vcpu\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (wpsimp wp: hoare_vcg_imp_lift' get_vcpu_wp arch_thread_get_wp | wps)+
  apply (clarsimp simp: cur_vcpu_def in_omonad split: option.splits)
  done

lemma associate_vcpu_tcb_valid_cur_vcpu[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and (\<lambda>s. tcb_ptr \<noteq> idle_thread s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   associate_vcpu_tcb vcpu_ptr tcb_ptr
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>" (is "\<lbrace>?P\<rbrace> _ \<lbrace>_\<rbrace>")
  unfolding associate_vcpu_tcb_def
  apply wpsimp
        apply (solves \<open>(wpsimp wp: hoare_vcg_imp_lift' set_vcpu_not_current_cur_vcpu_in_cur_domain get_vcpu_wp
                        | wps
                        | clarsimp simp: in_omonad)+\<close>)+
    apply (rule_tac Q'="\<lambda>_. ?P" in hoare_post_imp)
     apply (fastforce simp: in_omonad ct_in_cur_domain_def cur_vcpu_def)
    apply (wpsimp | wps)+
  done

lemma invoke_vcpu_ack_vppi_vcpu_tcbs_of[wp]:
  "invoke_vcpu_ack_vppi vcpu_ptr vppi \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  unfolding invoke_vcpu_ack_vppi_def
  apply wpsimp
  by (fastforce simp: opt_map_def elim!: rsubst[where P=P])

crunch invoke_vcpu_inject_irq, invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong)

crunch invoke_vcpu_read_register
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain

lemma perform_vcpu_invocation_valid_cur_vcpu[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and valid_vcpu_invocation vi
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   perform_vcpu_invocation vi
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding perform_vcpu_invocation_def
  by (wpsimp simp: valid_vcpu_invocation_def)

crunch store_pte, store_asid_pool_entry
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift)

crunch
  perform_vspace_invocation, perform_page_table_invocation, perform_page_invocation,
  perform_asid_control_invocation, perform_asid_pool_invocation, perform_sgi_invocation
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps  simp: crunch_simps)

lemma arch_perform_invocation_valid_cur_vcpu[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and valid_arch_inv ai
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding arch_perform_invocation_def
  by (wpsimp simp: valid_arch_inv_def)

\<comment> \<open>FIXME: move (where?)\<close>
lemma bound_vcpu_bound_tcb_at:
  "\<lbrakk>sym_refs (state_hyp_refs_of s); valid_objs s; vcpu_tcbs_of s vcpuptr = Some tcbptr\<rbrakk>
   \<Longrightarrow> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = (Some vcpuptr)) tcbptr s"
  apply (drule_tac x=vcpuptr in sym_refsD[rotated])
   apply (fastforce simp: state_hyp_refs_of_def pred_tcb_at_def obj_at_def in_omonad)
  apply (clarsimp simp: in_omonad)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_vcpu_def typ_at_eq_kheap_obj)
  apply (fastforce simp: pred_tcb_at_def obj_at_def state_hyp_refs_of_def tcb_vcpu_refs_def
                  split: option.splits)
  done

lemma thread_set_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> sym_refs (state_hyp_refs_of s) \<and> valid_objs s
        \<and> (arm_current_vcpu (arch_state s) = None
           \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s
           \<or> cur_domain s = new_dom)\<rbrace>
   thread_set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_wp)
  by (auto simp: cur_vcpu_in_cur_domain_defs pred_tcb_at_def obj_at_def etcb_at_def etcbs_of'_def
          split: option.splits dest: bound_vcpu_bound_tcb_at)

lemma set_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> sym_refs (state_hyp_refs_of s) \<and> valid_objs s
        \<and> (arm_current_vcpu (arch_state s) = None
           \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s
           \<or> cur_domain s = new_dom)\<rbrace>
   set_domain tptr new_dom
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding set_domain_def
  by (wpsimp wp: thread_set_domain_cur_vcpu_in_cur_domain hoare_vcg_disj_lift | wps)+

crunch fpu_release
  for arch_tcb_vcpu_at[wp]: "\<lambda>s. (arch_tcb_at (\<lambda>itcb. P (itcb_vcpu itcb)) t s)"
  (simp: crunch_simps wp: crunch_wps)

lemma vcpu_flush_if_current_arm_current_vcpu_None[wp]:
  "\<lbrace>\<top>\<rbrace>
   vcpu_flush_if_current tptr
   \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None
          \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s\<rbrace>"
  unfolding vcpu_flush_if_current_def
  apply (wpsimp wp: vcpu_flush_arm_current_vcpu_None[THEN hoare_strengthen_post] arch_thread_get_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma arch_prepare_set_domain_make_vcpu_safe[wp]:
  "\<lbrace>\<top>\<rbrace>
   arch_prepare_set_domain tptr new_dom
   \<lbrace>\<lambda>_ s. arm_current_vcpu (arch_state s) = None
          \<or> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb \<noteq> map_option fst (arm_current_vcpu (arch_state s))) tptr s
          \<or> cur_domain s = new_dom\<rbrace>"
  unfolding arch_prepare_set_domain_def
  by (wpsimp wp: hoare_vcg_disj_lift[where f="fpu_release tptr"]
                 vcpu_flush_if_current_arm_current_vcpu_None[THEN hoare_strengthen_post]
      | wps)+

lemma vcpu_flush_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_flush \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding vcpu_flush_def
  by (wpsimp simp: cur_vcpu_in_cur_domain_defs)

crunch arch_prepare_set_domain
  for hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_objs[wp]: valid_objs
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: crunch_wps simp: crunch_simps)

lemma invoke_domain_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_in_cur_domain s \<and> sym_refs (state_hyp_refs_of s) \<and> valid_objs s\<rbrace>
   invoke_domain thread domain
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding invoke_domain_def
  by wpsimp

crunch do_reply_transfer, handle_recv, handle_vm_fault
  for etcb_at[wp]: "etcb_at P t"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps preemption_point_inv' simp: crunch_simps filterM_mapM)

crunch do_reply_transfer, handle_recv, handle_vm_fault
  for vcpu_tcbs_of[wp]: "\<lambda>s. P (vcpu_tcbs_of s)"
  and arm_current_vcpu[wp]: "\<lambda>s. P (arm_current_vcpu (arch_state s))"
  and cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong crunch_wps dxo_wp_weak
   simp: crunch_simps
   ignore: set_simple_ko)

crunch
  handle_fault, reply_from_kernel, send_ipc, send_signal, invoke_irq_control, invoke_irq_handler,
  reschedule_required, handle_hypervisor_fault
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift_strong dxo_wp_weak crunch_wps
   simp: crunch_simps)

lemma perform_invocation_valid_cur_vcpu[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and ct_in_cur_domain and cur_vcpu and valid_invocation iv
    and valid_objs and (\<lambda>s. sym_refs (state_hyp_refs_of s))
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   perform_invocation blocking call iv
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  by (case_tac iv, simp_all; (solves wpsimp)?)

lemma set_thread_state_runnable_scheduler_action:
  "\<lbrace>\<lambda>s. P (scheduler_action s) \<and> runnable ts\<rbrace> set_thread_state t ts \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_act_def set_object_def get_object_def set_scheduler_action_def)
  apply (wpsimp wp: gts_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma handle_invocation_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and invs and ct_in_cur_domain and ct_active
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding handle_invocation_def
  apply (wpsimp wp: syscall_valid)
          apply (wp gts_wp hoare_vcg_all_lift hoare_drop_imps cur_vcpu_typ_lift
                    set_thread_state_runnable_scheduler_action
                | simp add: split_def)+
  apply (fastforce simp: invs_def valid_state_def valid_arch_state_def valid_pspace_def
                         valid_tcb_state_def ct_in_state_def
                  elim!: pred_tcb_weakenE)
  done

lemma handle_event_cur_vcpu_in_cur_domain[wp]:
  "\<lbrace>cur_vcpu_in_cur_domain and invs and ct_in_cur_domain and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  apply (cases e; clarsimp; (solves wpsimp)?)
  unfolding handle_call_def handle_send_def handle_reply_def handle_yield_def
  by (wpsimp wp: get_cap_wp)+

crunch activate_thread
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain

lemma call_kernel_cur_vcpu_in_cur_domain:
  "\<lbrace>cur_vcpu_in_cur_domain and invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding call_kernel_def
  apply (wpsimp | strengthen invs_valid_objs invs_hyp_sym_refs)+
    apply (rule hoare_post_imp[where Q'="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> cur_vcpu_in_cur_domain s \<and> valid_sched s \<and> invs s"])
     apply fastforce
    apply (wpsimp wp: getActiveIRQ_neq_non_kernel handle_event_valid_sched
           | strengthen invs_valid_objs invs_hyp_sym_refs)+
  apply (clarsimp simp: valid_sched_def)
  done

end

end
