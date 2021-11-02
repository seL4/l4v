(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
The main theorem
*)

theory AInvs
imports ArchDetSchedSchedule_AI
begin

lemma st_tcb_at_nostate_upd:
  "\<lbrakk> get_tcb t s = Some y; tcb_state y = tcb_state y' \<rbrakk> \<Longrightarrow>
  st_tcb_at P t' (s \<lparr>kheap := kheap s(t \<mapsto> TCB y')\<rparr>) = st_tcb_at P t' s"
  by (clarsimp simp add: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma pred_tcb_at_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := p'\<rparr>) =
  pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t := p' t)\<rparr>)"
  by (simp add: pred_tcb_at_def obj_at_def)

lemma thread_set_tcb_arch_ct_schedulable[wp]:
  "thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set us (tcb_arch tcb)\<rparr>) t \<lbrace>ct_schedulable\<rbrace>"
  apply (simp add: thread_set_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: schedulable_def is_sc_active_def get_tcb_def ko_atD
                         in_release_queue_def
                  split: option.splits )
  done

lemma thread_set_tcb_arch_ct_not_running[wp]:
  "thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set us (tcb_arch tcb)\<rparr>) t \<lbrace>\<lambda>s. \<not> ct_running s\<rbrace>"
  apply (simp add: thread_set_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def split: if_splits)
  done

text \<open>The top-level invariance\<close>

lemma akernel_invs:
  "\<lbrace>\<lambda>s. invs s \<and> schact_is_rct s \<and> cur_sc_active s \<and> ct_not_in_release_q s
        \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   (call_kernel e) :: (unit, unit) s_monad
   \<lbrace>\<lambda>_ s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
  unfolding call_kernel_def preemption_path_def
  apply (wpsimp wp: activate_invs check_budget_invs charge_budget_invs is_schedulable_wp
                    update_time_stamp_invs hoare_drop_imps hoare_vcg_all_lift hoare_vcg_if_lift2)
  apply (fastforce intro: schact_is_rct_ct_active_sc
                    simp: schedulable_def2 ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma akernel_invs_det_ext:
  "\<lbrace>\<lambda>s. invs s \<and> schact_is_rct s \<and> cur_sc_active s \<and> ct_not_in_release_q s
        \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   (call_kernel e) :: (unit, det_ext) s_monad
   \<lbrace>\<lambda>_ s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
  unfolding call_kernel_def preemption_path_def
  apply (wpsimp wp: activate_invs check_budget_invs charge_budget_invs is_schedulable_wp
                    update_time_stamp_invs hoare_drop_imps hoare_vcg_all_lift hoare_vcg_if_lift2)
  apply (fastforce intro: schact_is_rct_ct_active_sc
                    simp: schedulable_def2 ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma kernel_entry_invs:
  "\<lbrace>\<lambda>s. invs s \<and> schact_is_rct s \<and> cur_sc_active s \<and> ct_not_in_release_q s
          \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   (kernel_entry e us) :: (user_context, unit) s_monad
   \<lbrace>\<lambda>_ s. invs s \<and> (ct_running s \<or> ct_idle s)\<rbrace>"
  apply (simp add: kernel_entry_def)
  apply (wp akernel_invs thread_set_invs_trivial thread_set_ct_in_state select_wp
            static_imp_wp hoare_vcg_disj_lift hoare_vcg_imp_lift'
         | clarsimp simp add: tcb_cap_cases_def)+
  done

lemma device_update_invs:
  "\<lbrace>invs and (\<lambda>s. (dom ds) \<subseteq>  (device_region s))\<rbrace> do_machine_op (device_memory_update ds)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: do_machine_op_def device_memory_update_def simpler_modify_def select_f_def
                   gets_def get_def bind_def valid_def return_def)
  apply (clarsimp simp: invs_def valid_state_def valid_irq_states_def valid_machine_state_def
                        cur_tcb_def pspace_respects_device_region_def cap_refs_respects_device_region_def
                  cong: user_mem_dom_cong
              simp del: split_paired_All)
  apply (clarsimp cong: device_mem_dom_cong simp:cap_range_respects_device_region_def
              simp del: split_paired_All split_paired_Ex)
  apply (intro conjI)
     apply fastforce
    apply fastforce
   apply (clarsimp simp del: split_paired_All split_paired_Ex)
   apply (drule_tac x = "(a,b)" in spec)
   apply (erule notE)
   apply (erule cte_wp_at_weakenE)
   apply clarsimp
   apply (fastforce split: if_splits) (* takes 20 secs *)
  apply (clarsimp simp: cur_sc_tcb_def)
  done

crunch device_state_inv[wp]: user_memory_update "\<lambda>ms. P (device_state ms)"

(* FIXME: move or delete *)
lemma dom_restrict_plus_eq:
  "a \<inter> b \<union> b = b"
  by auto

lemma user_memory_update[wp]:
  "\<lbrace>\<lambda>s. P (device_region s) \<rbrace> do_machine_op (user_memory_update a)
   \<lbrace>\<lambda>rv s. P (device_region s)\<rbrace>"
  by (simp add: do_machine_op_def user_memory_update_def simpler_modify_def
                valid_def bind_def gets_def return_def get_def select_f_def)

lemma do_user_op_invs:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_def split_def)
  apply (wp device_update_invs)
  apply (wp select_wp dmo_invs | simp add:dom_restrict_plus_eq)+
  apply (clarsimp simp: user_memory_update_def simpler_modify_def
                        restrict_map_def invs_def cur_tcb_def
                 split: option.splits if_split_asm)
  apply (frule ptable_rights_imp_frame)
     apply fastforce+
  apply (clarsimp simp: valid_state_def device_frame_in_device_region)
  done

lemma schedule_ct_activateable:
  "\<lbrace>invs and valid_sched\<rbrace>
   schedule
   \<lbrace>\<lambda>_. ct_in_state activatable\<rbrace>"
  supply if_split [split del]
  apply (simp add: Schedule_A.schedule_def)
  apply wp
        apply wpc
          (* resume current thread *)
          apply wp
         prefer 2
         (* choose new thread *)
         apply wp
        (* switch to thread *)
        apply (wpsimp simp: schedule_switch_thread_fastfail_def tcb_sched_action_def
                            set_tcb_queue_def get_tcb_queue_def
                        wp: thread_get_wp' stt_activatable)
       apply (wp add: is_schedulable_wp)+
    apply (rule hoare_strengthen_post[where
             Q="\<lambda>_. invs and valid_sched"])
     apply wp
    apply (subgoal_tac "\<forall>x. scheduler_action s = switch_thread x \<longrightarrow> st_tcb_at activatable x s")
     apply (subgoal_tac "scheduler_action s = resume_cur_thread \<longrightarrow> ct_in_state activatable s")
      apply (clarsimp split: if_split option.splits
                       simp: schedulable_def)
     apply (clarsimp simp: valid_sched_def valid_sched_action_def is_activatable_def ct_in_state_kh_simp)
     apply (clarsimp simp: valid_sched_def valid_sched_action_def is_activatable_def ct_in_state_kh_simp)
    apply (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def tcb_at_kh_simps
                     elim: pred_map_imp)
   apply (wpsimp wp: awaken_valid_sched)
  apply clarsimp
  done

crunches send_signal, do_reply_transfer, invoke_irq_control, invoke_irq_handler, set_consumed,
         sched_context_resume, preemption_path, deleting_irq_handler, cancel_badged_sends, restart,
         bind_notification, awaken, check_domain_time, if_cond_refill_unblock_check, activate_thread
  for is_active_sc[wp]: "\<lambda>s. P (is_active_sc sc_ptr s)"
  (wp: crunch_wps check_cap_inv filterM_preserved simp: crunch_simps)

lemma sched_context_yield_to_is_active_sc[wp]:
  "sched_context_yield_to sc_ptr' buffer \<lbrace>\<lambda>s. P (is_active_sc sc_ptr s)\<rbrace>"
  apply (clarsimp simp: sched_context_yield_to_def)
  apply (wpsimp wp: is_schedulable_wp hoare_drop_imps)
  done

lemma sched_context_bind_tcb_is_active_sc[wp]:
  "sched_context_bind_tcb sc_ptr' tcb_ptr \<lbrace>\<lambda>s. P (is_active_sc sc_ptr s)\<rbrace>"
  apply (clarsimp simp: sched_context_bind_tcb_def if_cond_refill_unblock_check_def)
  apply (wpsimp wp: is_schedulable_wp hoare_drop_imps)
  done

crunches handle_fault, check_budget_restart, charge_budget, handle_interrupt, preemption_path
  for is_active_sc[wp]: "\<lambda>s. P (is_active_sc sc_ptr s)"
  (wp: crunch_wps check_cap_inv filterM_preserved simp: crunch_simps)

lemma maybe_return_sc_is_active_sc[wp]:
  "maybe_return_sc a b \<lbrace>\<lambda>s. P (is_active_sc sc_ptr s)\<rbrace>"
  apply (clarsimp simp: maybe_return_sc_def)
  apply (wpsimp wp: get_tcb_obj_ref_wp get_sk_obj_ref_wp)
  done

lemma handle_yield_sc_is_active_sc[wp]:
  "handle_yield \<lbrace>\<lambda>s. P (is_active_sc sc_ptr s)\<rbrace>"
  apply (clarsimp simp: handle_yield_def)
  apply (wpsimp wp: get_tcb_obj_ref_wp get_sk_obj_ref_wp)
  done

crunches handle_fault, check_budget_restart, handle_recv
  for is_active_sc[wp]: "\<lambda>s. P (is_active_sc sc_ptr s)"
  (wp: crunch_wps check_cap_inv filterM_preserved simp: crunch_simps)

crunches sched_context_yield_to, sched_context_bind_tcb, cancel_all_ipc, cancel_all_signals,
         cancel_badged_sends, restart, maybe_sched_context_unbind_tcb, maybe_sched_context_bind_tcb,
         sched_context_bind_tcb, bind_notification, send_signal
  for cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  (wp: crunch_wps check_cap_inv filterM_preserved simp: crunch_simps)

crunches install_tcb_frame_cap, install_tcb_cap, do_reply_transfer, invoke_irq_handler, awaken,
         check_domain_time, if_cond_refill_unblock_check, activate_thread, handle_fault, handle_recv,
         handle_yield, handle_interrupt, preemption_path
  for cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  (wp: crunch_wps check_cap_inv filterM_preserved preemption_point_inv simp: crunch_simps)

crunches perform_invocation
  for cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  (wp: crunch_wps preemption_point_inv check_cap_inv filterM_preserved cap_revoke_preservation
   simp: crunch_simps)

lemma invoke_sched_context_cur_sc_active[wp]:
  "invoke_sched_context i \<lbrace>\<lambda>s. cur_sc_active s\<rbrace>"
  apply (simp add: invoke_sched_context_def)
  apply (cases i; clarsimp; wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
  done

lemma invoke_sched_context_cur_sc_tcb_are_bound_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> valid_sched_control_inv iv s\<rbrace>
   invoke_sched_control_configure_flags iv
   \<lbrace>\<lambda>_ s. cur_sc_active s\<rbrace>"
  apply (simp add: invoke_sched_control_configure_flags_def)
  apply (cases iv; clarsimp)
  apply (rule hoare_weaken_pre)
   apply (rule_tac f=cur_sc in hoare_lift_Pf2)
    apply (wpsimp wp: update_sched_context_wp)
   apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: active_sc_def MIN_REFILLS_def vs_all_heap_simps)
  done

lemma set_thread_state_schact_is_not_rct[wp]:
  "set_thread_state ref ts \<lbrace>\<lambda>s. \<not> schact_is_rct s\<rbrace>"
  apply (clarsimp simp: set_thread_state_def set_thread_state_act_def)
  apply (wpsimp wp: set_scheduler_action_wp is_schedulable_wp set_object_wp)
  apply (clarsimp simp: schact_is_rct_def)
  done

crunches possible_switch_to
  for schact_is_not_rct[wp]: "\<lambda>s. \<not> schact_is_rct s"
  (wp: crunch_wps set_scheduler_action_wp simp: schact_is_rct_def)

crunches restart_thread_if_no_fault, cancel_all_signals, cancel_ipc,
         reply_remove, suspend, reply_remove, unbind_from_sc, set_priority, set_mcpriority,
         sched_context_bind_tcb, restart, bind_notification
  for schact_is_not_rct[wp]: "\<lambda>s. \<not> schact_is_rct s"
  (wp: crunch_wps hoare_vcg_all_lift)

crunches perform_invocation, handle_fault, handle_recv, preemption_path, activate_thread, awaken,
         check_domain_time, if_cond_refill_unblock_check, handle_yield
  for schact_is_not_rct[wp]: "\<lambda>s. \<not> schact_is_rct s"
  (wp: crunch_wps preemption_point_inv check_cap_inv filterM_preserved cap_revoke_preservation
   simp: crunch_simps)

lemma sched_context_unbind_tcb_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s\<rbrace>
   sched_context_unbind_tcb sc_ptr
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> sc_ptr \<noteq> cur_sc s \<and> cur_sc_active s\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>?Q\<rbrace>")
  apply (clarsimp simp: sched_context_unbind_tcb_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ assert_opt_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac B="?Q" in hoare_seq_ext[rotated])
   apply (rule hoare_when_cases)
    apply (clarsimp simp: invs_def cur_sc_tcb_def sc_at_pred_n_def obj_at_def schact_is_rct_def)
   apply (wpsimp wp: valid_sched_wp)
   apply (clarsimp simp: schact_is_rct_def)
  apply wpsimp
  done

lemma sched_context_unbind_tcb_schact_is_rct_imp_cur_sc_active_inv[wp]:
  "sched_context_unbind_tcb sc_ptr \<lbrace>\<lambda>s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  by (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)

lemma finalise_cap_sc_tcb_are_bound_imp_is_active_sc:
  "finalise_cap cap final
   \<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> cur_sc_active s)
                            \<and> (\<exists>slot. cte_wp_at ((=) cap) slot s) \<and> invs s\<rbrace>"
  apply (intro hoare_vcg_conj_lift_pre_fix)
    subgoal
      apply (cases cap; clarsimp; (solves wpsimp)?)
          apply (find_goal \<open>match premises in "_ = SchedContextCap _ _" \<Rightarrow> \<open>-\<close>\<close>)
          apply (rename_tac sc_ptr n)
          apply (clarsimp simp: sched_context_unbind_all_tcbs_def)
          apply (rule_tac B="\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s)
                                   \<and> (final \<and> schact_is_rct s \<longrightarrow> sc_ptr \<noteq> cur_sc s \<and> cur_sc_active s)"
                       in hoare_seq_ext[rotated])
           apply (rule hoare_when_cases)
            apply (clarsimp simp: sched_context_unbind_all_tcbs_def)
           apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
           apply (rule hoare_when_cases)
            apply (intro conjI impI; fastforce?)
            apply clarsimp
            apply (elim disjE)
             apply (clarsimp simp: invs_def cur_sc_tcb_def sc_at_pred_n_def obj_at_def
                                   schact_is_rct_def)
            apply (clarsimp dest!: no_cap_to_idle_sc_ptr)
           apply (wpsimp wp: sched_context_unbind_tcb_schact_is_rct_imp_cur_sc_active)
          apply (rule hoare_seq_ext_skip, solves wpsimp)+
          apply (clarsimp simp: sched_context_zero_refill_max_def)
          apply (wpsimp wp: update_sched_context_wp)
          apply (clarsimp simp: obj_at_def vs_all_heap_simps)
         apply (wpsimp wp: hoare_vcg_imp_lift' gts_wp get_simple_ko_wp cur_sc_active_lift
                | intro conjI impI)+
     done
   apply (rule hoare_weaken_pre)
    apply (rule hoare_vcg_ex_lift)
    apply wpsimp
   apply fastforce
  apply (rule hoare_weaken_pre)
   apply (rule hoare_ex_pre)
   apply (wpsimp wp: finalise_cap_invs)
  apply fastforce
  done

lemma rec_del_schact_is_rct_imp_cur_sc_active:
 "\<lbrace>(\<lambda>s. schact_is_rct s \<longrightarrow> cur_sc_active s) and invs and valid_rec_del_call args
        and (\<lambda>s. \<not> exposed_rdcall args
               \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall args) s)
        and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                       \<not> cap_removeable cap sl
                       \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s)
                  | _ \<Rightarrow> True)\<rbrace>
  rec_del args
  \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  apply (rule validE_valid)
  apply (rule hoare_post_impErr)
  apply (rule hoare_pre)
    apply (rule use_spec)
    apply (rule rec_del_invs''[where Q="(\<lambda>s. schact_is_rct s \<longrightarrow> cur_sc_active s)"])
         apply (wpsimp | wpsimp wp: preemption_point_inv simp: ct_in_state_def)+
       apply (rule_tac Q="\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s)
                                \<and> (\<exists>slot. cte_wp_at ((=) cap) slot s) \<and> invs s"
                   in  hoare_strengthen_post)
        apply (wpsimp wp: finalise_cap_sc_tcb_are_bound_imp_is_active_sc)
       apply blast
      apply (wpsimp wp: hoare_vcg_imp_lift')
     apply (wpsimp wp: preemption_point_inv)
    apply blast+
  done

lemma cap_revoke_schact_is_rct_imp_cur_sc_active:
  "cap_revoke cap \<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s\<rbrace>"
  apply (rule validE_valid)
  apply (rule cap_revoke_preservation)
   apply (clarsimp simp: cap_delete_def)
   apply (rule hoare_vcg_conj_lift_pre_fix)
    apply (wpsimp wp: rec_del_schact_is_rct_imp_cur_sc_active[THEN valid_validE])
   apply (wpsimp wp: rec_del_invs)
  apply (wpsimp wp: preemption_point_inv)
  done

lemma invoke_cnode_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> invs s\<rbrace>
   invoke_cnode iv
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  apply (clarsimp simp: invoke_cnode_def)
  apply (cases iv; clarsimp; (intro conjI impI)?;
         (solves \<open>wpsimp wp: hoare_drop_imps cur_sc_active_lift\<close>)?)
   apply (rule_tac Q="\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s" in hoare_strengthen_post)
    apply (wpsimp wp: cap_revoke_schact_is_rct_imp_cur_sc_active)
   apply blast
  apply (rule_tac Q="\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s" in hoare_strengthen_post)
   apply (clarsimp simp: cap_delete_def)
   apply (wpsimp wp: rec_del_schact_is_rct_imp_cur_sc_active rec_del_invs)
  apply blast
  done

lemma install_tcb_cap_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s\<rbrace>
   install_tcb_cap target slot n slot_opt
   \<lbrace>\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s)\<rbrace>"
  apply (clarsimp simp: install_tcb_cap_def)
  apply (cases slot_opt; clarsimp; (solves wpsimp)?)
  apply (rule validE_valid)
  apply (rule hoare_seq_ext_skipE)
   apply (rule_tac E="\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s" in hoare_post_impErr)
     apply (clarsimp simp: cap_delete_def)
     apply (rule valid_validE)
     apply (intro hoare_vcg_conj_lift_pre_fix)
      apply (wpsimp wp: rec_del_schact_is_rct_imp_cur_sc_active)
     apply (wpsimp wp: rec_del_invs)
    apply blast
   apply blast
  apply (wpsimp wp: rec_del_schact_is_rct_imp_cur_sc_active check_cap_inv)
  done

lemma install_tcb_frame_cap_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s\<rbrace>
   install_tcb_frame_cap target slot buffer
   \<lbrace>\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s)\<rbrace>"
  apply (clarsimp simp: install_tcb_frame_cap_def)
  apply (cases buffer; clarsimp; (solves wpsimp)?)
  apply (rule validE_valid)
  apply (rule hoare_seq_ext_skipE)
   apply (rule_tac E="\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> invs s" in hoare_post_impErr)
     apply (clarsimp simp: cap_delete_def)
     apply (rule valid_validE)
     apply (intro hoare_vcg_conj_lift_pre_fix)
      apply (wpsimp wp: rec_del_schact_is_rct_imp_cur_sc_active)
     apply (wpsimp wp: rec_del_invs)
    apply blast
   apply blast
  apply (wpsimp wp: rec_del_schact_is_rct_imp_cur_sc_active check_cap_inv hoare_vcg_imp_lift')
  done

lemma invoke_tcb_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> invs s \<and> tcb_inv_wf iv s\<rbrace>
   invoke_tcb iv
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  apply (cases iv; clarsimp;
         (solves \<open>wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift mapM_x_inv_wp\<close>)?)
    subgoal for target cnode_index cslot_ptr fault_handler timeout_handler croot vroot buffer
      apply wp
           apply (wpsimp wp: install_tcb_frame_cap_schact_is_rct_imp_cur_sc_active)
          apply (invoke_tcb_install_tcb_cap_helper wp: install_tcb_cap_schact_is_rct_imp_cur_sc_active)+
      apply simp
      apply (strengthen tcb_cap_valid_ep_strgs)
      apply (clarsimp cong: conj_cong)
      apply (intro conjI impI;
             clarsimp simp: is_cnode_or_valid_arch_is_cap_simps tcb_ep_slot_cte_wp_ats real_cte_at_cte
                     dest!: is_valid_vtable_root_is_arch_cap)
         apply (all \<open>clarsimp simp: is_cap_simps cte_wp_at_caps_of_state valid_fault_handler_def\<close>)
        apply (all \<open>clarsimp simp: obj_at_def is_tcb typ_at_eq_kheap_obj cap_table_at_typ\<close>)
        by auto
   apply (rename_tac target cnode_index cslot_ptr fault_handler mcp priority sc)
   apply (rule validE_valid)
   apply (rule_tac B= "\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s) \<and> tcb_at target s"
               and E="\<lambda>_ s. (schact_is_rct s \<longrightarrow> cur_sc_active s)"
                in hoare_vcg_seqE[rotated])
    apply (invoke_tcb_install_tcb_cap_helper wp: install_tcb_cap_schact_is_rct_imp_cur_sc_active)+
   apply (rule hoare_seq_ext_skipE, solves \<open>wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift\<close>)+
   apply (rule hoare_seq_ext_skipE)
    apply simp
    apply (rule maybeM_inv)
    apply (clarsimp split: option.splits)
    apply (intro conjI impI)
     apply (clarsimp simp: maybe_sched_context_unbind_tcb_def)
     apply (wpsimp wp: thread_get_wp simp: get_tcb_obj_ref_def)
    apply (clarsimp simp: maybe_sched_context_bind_tcb_def)
    apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
   apply wpsimp
  apply (rename_tac t ntfn)
  apply (case_tac ntfn; wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
  done

lemma perform_invocation_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> invs s \<and> ct_active s \<and> schact_is_rct s \<and> valid_invocation iv s\<rbrace>
   perform_invocation block call can_donate iv
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  apply (cases iv; simp, (solves \<open>wpsimp wp: hoare_drop_imps cur_sc_active_lift\<close>)?)
       apply (wpsimp wp: invoke_untyped_cur_sc_active hoare_drop_imps)
      apply (wpsimp wp: invoke_tcb_schact_is_rct_imp_cur_sc_active)
     apply (wpsimp wp: invoke_sched_context_cur_sc_tcb_are_bound_imp_cur_sc_active hoare_drop_imps)
    apply (wpsimp wp: invoke_sched_context_cur_sc_tcb_are_bound_imp_cur_sc_active hoare_drop_imps)
   apply (wpsimp wp: invoke_cnode_schact_is_rct_imp_cur_sc_active)
  apply (wpsimp wp: hoare_drop_imps)
  done

lemma handle_invocation_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> invs s \<and> ct_active s \<and> ct_not_in_release_q s \<and> schact_is_rct s\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  (is "\<lbrace>?P\<rbrace> _ \<lbrace>\<lambda>_. ?Q\<rbrace>")
  apply (clarsimp simp: handle_invocation_def)
  apply (subst liftE_bindE)
  apply (rule hoare_seq_ext[OF _  gets_sp])
  apply (subst liftE_bindE)
  apply (rule_tac B="\<lambda>rv. ?P and (\<lambda>s. cur_thread s = thread) and K (valid_message_info rv)"
               in hoare_seq_ext[rotated])
   apply wpsimp
  apply (rule validE_valid)
  apply (rule_tac P_flt="\<lambda>_. ?Q" and P_err="\<lambda>_. ?Q"
              and P_no_err="\<lambda>rv. ?P and (\<lambda>s. cur_thread s = thread) and valid_invocation rv"
               in syscall_valid)
      apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
     apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
    apply (wpsimp wp: perform_invocation_schact_is_rct_imp_cur_sc_active)
              apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
             apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
            apply (wpsimp wp: gts_wp')+
      apply (rule_tac Q="\<lambda>_. ?Q" and E="\<lambda>_. ?Q" in hoare_post_impErr[rotated]; fastforce?)
      apply (wpsimp wp: perform_invocation_schact_is_rct_imp_cur_sc_active)
     apply (wpsimp wp: ct_in_state_set set_thread_state_schact_is_rct_strong)
    apply (fastforce intro: cur_sc_active_active_sc_tcb_at_cur_thread
                      simp: ct_in_state_def)
   apply (wp hoare_vcg_E_conj | simp add: split_def)+
  by fastforce

method handle_event_schact_is_rct_imp_cur_sc_active_single for e
  = rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift',
    rule_tac B="\<lambda>rv s. (rv \<longrightarrow> (cur_sc_active s \<and> invs s \<and> (ct_running s \<or> ct_idle s)
                                \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s) \<and> ct_not_in_release_q s
                                \<and> schact_is_rct s))
                       \<and> (\<not>rv \<longrightarrow> cur_sc_active s)"
          in hoare_seq_ext[rotated],
    wpsimp wp: check_budget_restart_true,
    rule check_budget_restart_false,
    wpsimp wp: cur_sc_active_lift,
    fast,
    wpsimp wp: handle_invocation_schact_is_rct_imp_cur_sc_active check_budget_restart_true,
    (cases e; clarsimp simp: runnable_eq_active ct_in_state_def pred_tcb_at_def obj_at_def)

method handle_event_schact_is_rct_imp_cur_sc_active_recv for e
  = rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift',
    rule_tac B="\<lambda>rv s. (rv \<longrightarrow> (cur_sc_active s \<and> invs s \<and>  (ct_running s \<or> ct_idle s)
                                \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s) \<and> ct_not_in_release_q s
                                \<and> schact_is_rct s))
                       \<and> (\<not>rv \<longrightarrow> cur_sc_active s)"
          in hoare_seq_ext[rotated],
    wpsimp wp: check_budget_restart_true,
    rule check_budget_restart_false,
    wpsimp wp: cur_sc_active_lift, fast,
    (wpsimp wp: handle_invocation_schact_is_rct_imp_cur_sc_active,
    wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)+,
    (cases e; clarsimp simp: runnable_eq_active ct_in_state_def pred_tcb_at_def obj_at_def)

method handle_event_schact_is_rct_imp_cur_sc_active_misc
  =  rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift',
     rule_tac B="\<lambda>rv s. (rv \<longrightarrow> (cur_sc_active s \<and> invs s \<and> (ct_running s \<or> ct_idle s)
                                 \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s) \<and> ct_not_in_release_q s
                                 \<and> schact_is_rct s))
                        \<and> (\<not>rv \<longrightarrow> cur_sc_active s)"
           in hoare_seq_ext[rotated],
     wpsimp wp: check_budget_restart_true,
     rule check_budget_restart_false,
     wpsimp wp: cur_sc_active_lift,
     fast,
     clarsimp simp: whenE_def,
     (intro conjI impI; (solves wpsimp)?),
     wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift

lemma handle_event_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> invs s \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)
        \<and> ct_not_in_release_q s \<and> schact_is_rct s\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  apply (cases e; (solves \<open>wpsimp wp: hoare_drop_imps cur_sc_active_lift\<close>)?)
  apply (rename_tac syscall)
  by (case_tac syscall; clarsimp simp: handle_send_def handle_call_def liftE_bindE;
      (solves \<open>handle_event_schact_is_rct_imp_cur_sc_active_single e\<close>)?,
      (solves \<open>handle_event_schact_is_rct_imp_cur_sc_active_misc\<close>)?,
      (solves \<open>handle_event_schact_is_rct_imp_cur_sc_active_recv e\<close>)?)

lemma handle_event_preemption_path_schact_is_rct_imp_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> invs s \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)
        \<and> ct_not_in_release_q s \<and> schact_is_rct s\<rbrace>
   handle_event e <handle> (\<lambda>_. liftE preemption_path)
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s\<rbrace>"
  apply (rule validE_valid)
  apply (rule_tac F="\<lambda>_ s. schact_is_rct s \<longrightarrow> cur_sc_active s" in handleE_wp)
   apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
  apply (wpsimp wp: handle_event_schact_is_rct_imp_cur_sc_active)
  done

lemma switch_sched_context_cur_sc_active[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
   switch_sched_context
   \<lbrace>\<lambda>_ s. cur_sc_active s\<rbrace>"
  apply (clarsimp simp: switch_sched_context_def)
  apply (wpsimp wp : get_tcb_obj_ref_wp)
  apply (clarsimp simp: vs_all_heap_simps obj_at_def)
  done

lemma sc_and_timer_cur_sc_active[wp]:
  "\<lbrace>\<lambda>s. active_sc_tcb_at (cur_thread s) s\<rbrace>
   sc_and_timer
   \<lbrace>\<lambda>_ s. cur_sc_active s\<rbrace>"
  by (wpsimp simp: sc_and_timer_def)

lemma switch_to_thread_active_sc_tcb_at_cur_thread:
  "\<lbrace>active_sc_tcb_at thread\<rbrace>
   switch_to_thread thread
   \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  by (wpsimp simp: switch_to_thread_def)

lemma choose_thread_active_sc_tcb_at_cur_thread:
  "\<lbrace>valid_idle\<rbrace>
   choose_thread
   \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: choose_thread_def)
  apply (intro hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_if)
   apply (clarsimp simp: switch_to_idle_thread_def)
   apply (intro hoare_seq_ext[OF _ gets_sp])
   apply wpsimp
   apply (clarsimp simp: valid_idle_def vs_all_heap_simps pred_tcb_at_def obj_at_def
                         MIN_REFILLS_def active_sc_def)
  apply (clarsimp simp: guarded_switch_to_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (rule hoare_seq_ext[OF _ assert_opt_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (wpsimp wp: switch_to_thread_active_sc_tcb_at_cur_thread hoare_vcg_imp_lift')
  apply (frule hd_max_non_empty_queue_in_ready_queues)
  apply (prop_tac "tcb_at (hd (max_non_empty_queue (ready_queues s (cur_domain s)))) s")
   apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (frule schedulable_unfold)
  apply (clarsimp simp: vs_all_heap_simps obj_at_def pred_tcb_at_def is_sc_active_def2)
  done

lemma schedule_choose_new_thread_active_sc_tcb_at_cur_thread:
  "\<lbrace>valid_idle\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  apply (clarsimp simp: schedule_choose_new_thread_def)
  apply (wpsimp wp: choose_thread_active_sc_tcb_at_cur_thread)
  done

lemma schedule_switch_thread_branch_active_sc_tcb_at_cur_thread:
  "\<lbrace>\<lambda>s. active_sc_tcb_at candidate s \<and> valid_idle s\<rbrace>
   schedule_switch_thread_branch candidate ct ct_schdble
   \<lbrace>\<lambda>_ s. active_sc_tcb_at (cur_thread s) s\<rbrace>"
  apply clarsimp
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (wpsimp wp: schedule_choose_new_thread_active_sc_tcb_at_cur_thread
                    switch_to_thread_active_sc_tcb_at_cur_thread)
  done

lemma schedule_cur_sc_active:
  "\<lbrace>\<lambda>s. valid_sched s \<and> invs s \<and> (schact_is_rct s \<longrightarrow> cur_sc_active s)\<rbrace>
   schedule
   \<lbrace>\<lambda>_ s. cur_sc_active s\<rbrace>"
  apply (clarsimp simp: schedule_def)
  apply (rule hoare_seq_ext_skip, wpsimp wp: awaken_valid_sched hoare_vcg_imp_lift')
  apply (rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac action)
  apply (rule hoare_seq_ext[OF sc_and_timer_cur_sc_active])
  apply (case_tac action; clarsimp)
    apply wpsimp
    apply (fastforce intro: cur_sc_active_active_sc_tcb_at_cur_thread
                      simp: schact_is_rct_def)
   apply (subst bind_dummy_ret_val)+
   apply (rule hoare_weaken_pre)
    apply (rule schedule_switch_thread_branch_active_sc_tcb_at_cur_thread)
   apply (fastforce dest: valid_sched_weak_valid_sched_action
                    simp: weak_valid_sched_action_def vs_all_heap_simps)
  apply (wpsimp wp: schedule_choose_new_thread_active_sc_tcb_at_cur_thread)
  done

lemma call_kernel_cur_sc_active:
  "\<lbrace>\<lambda>s. cur_sc_active s \<and> invs s \<and> schact_is_rct s \<and> valid_sched s \<and> ct_not_in_release_q s
        \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)
        \<and> cur_sc_offset_ready (consumed_time s) s \<and> current_time_bounded 5 s
        \<and> valid_machine_time s \<and> consumed_time_bounded s\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_ s :: det_state. cur_sc_active s\<rbrace>"
  apply (clarsimp simp: call_kernel_def)
  apply (simp flip: bind_assoc)
  apply (rule hoare_seq_ext)
   apply (wpsimp wp: cur_sc_active_lift)
  apply (rule hoare_seq_ext[OF schedule_cur_sc_active])
  apply (intro hoare_vcg_conj_lift_pre_fix)
    apply (wpsimp wp: handle_event_preemption_path_valid_sched)
   apply wpsimp
   apply (fastforce dest!: cur_sc_active_ct_not_in_release_q_imp_ct_running_imp_ct_schedulable)
  apply (wpsimp wp: handle_event_preemption_path_schact_is_rct_imp_cur_sc_active)
  done

lemma invoke_sched_control_configure_flags_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>ct_not_in_release_q and invs and schact_is_rct and valid_sched_control_inv iv\<rbrace>
   invoke_sched_control_configure_flags iv
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (simp add: invoke_sched_control_configure_flags_def)
  apply (cases iv; clarsimp)
  apply (rename_tac sc_ptr budget period mrefills badge flag)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule_tac B="\<lambda>_ s. ct_not_in_release_q s \<and> invs s \<and> schact_is_rct s
                           \<and> ex_nonz_cap_to sc_ptr s
                           \<and> sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr s"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: update_sc_badge_invs')
    apply (wpsimp wp: update_sched_context_wp)
   apply (fastforce dest: ex_nonz_cap_to_not_idle_sc_ptr
                    simp: sc_at_pred_n_def obj_at_def)
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: update_sc_sporadic_invs')
    apply (wpsimp wp: update_sched_context_wp)
   apply (fastforce dest: ex_nonz_cap_to_not_idle_sc_ptr
                    simp: sc_at_pred_n_def obj_at_def)
  apply (rule hoare_seq_ext_skip)
   apply (intro hoare_vcg_conj_lift_pre_fix; (solves \<open>wpsimp wp: commit_time_invs\<close>)?)
   apply (rule hoare_when_cases, simp)
   apply (rule_tac Q="sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr" in hoare_weaken_pre[rotated], simp)
    apply (rule hoare_seq_ext_skip, wpsimp)+
    apply wpsimp
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: refill_update_invs gts_wp)
   apply (fastforce dest: ex_nonz_cap_to_not_idle_sc_ptr)
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ assert_opt_sp])
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule_tac B="\<lambda>_ s. in_release_q (cur_thread s) s \<longrightarrow> tcb_ptr = cur_thread s"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: hoare_vcg_imp_lift' sched_context_resume_ct_not_in_release_q)+
   apply (metis option.sel pred_map_simps(1) sc_at_kh_simps(4) sc_at_pred_n_eq_commute)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_if)
   apply (rule_tac Q="\<lambda>_ s. scheduler_action s = choose_new_thread" in hoare_post_imp)
    apply (clarsimp simp: schact_is_rct_def)
   apply (wpsimp wp: reschedule_cnt)
  apply (wpsimp wp: hoare_drop_imps)
  done

crunches cancel_badged_sends
  for ct_not_in_release_q[wp]: ct_not_in_release_q
  (wp: crunch_wps preemption_point_inv check_cap_inv filterM_preserved cap_revoke_preservation
   simp: crunch_simps)

lemma invoke_cnode_ct_not_in_release_q[wp]:
  "invoke_cnode iv \<lbrace>ct_not_in_release_q\<rbrace>"
  by (clarsimp simp: invoke_cnode_def)
     (cases iv; clarsimp; (intro conjI impI)?; wpsimp)

crunches install_tcb_frame_cap
  for ct_not_in_release_q[wp]: ct_not_in_release_q
  (wp: crunch_wps preemption_point_inv ignore: check_cap_at simp: check_cap_at_def)

crunches maybe_sched_context_unbind_tcb, bind_notification
  for ct_not_in_release_q[wp]: ct_not_in_release_q
  (wp: crunch_wps)

lemma restart_ct_not_in_release_q_active:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> st_tcb_at active thread s\<rbrace>
   restart thread
   \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  apply (clarsimp simp: restart_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_when_cases)
   apply fast
  apply (wpsimp wp: hoare_pre_cont)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  by auto

crunches test_possible_switch_to
  for ct_not_in_release_q[wp]: ct_not_in_release_q

crunches if_cond_refill_unblock_check
  for bound_sc_tcb_at_ct'[wp]: "\<lambda>s. Q (bound_sc_tcb_at P (cur_thread s) s)"
  (wp: crunch_wps hoare_vcg_if_lift2 ignore: update_sched_context)

lemma restart_ct_not_in_release_q_not_cur_thread:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> thread \<noteq> cur_thread s
        \<and> bound_sc_tcb_at bound (cur_thread s) s \<and> invs s\<rbrace>
   restart thread
   \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  apply (clarsimp simp: restart_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_when_cases, simp)
  apply (rule_tac B="\<lambda>_ s. ct_not_in_release_q s \<and> thread \<noteq> cur_thread s
                           \<and> bound_sc_tcb_at ((=) sc_opt) thread s \<and> invs s"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (wpsimp wp: sched_context_resume_ct_not_in_release_q)
  apply (frule invs_sym_refs)
  apply (clarsimp simp: vs_all_heap_simps pred_tcb_at_def obj_at_def)
  apply (metis kernel_object.inject(5) option.inject sym_ref_tcb_sc)
  done

lemma sched_context_bind_tcb_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> tcb_ptr \<noteq> cur_thread s\<rbrace>
   sched_context_bind_tcb sc_ptr tcb_ptr
   \<lbrace>\<lambda>_ s. schact_is_rct s  \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: sched_context_bind_tcb_def)
  apply wpsimp
         apply (rule_tac Q="\<lambda>_ s. scheduler_action s = choose_new_thread" in hoare_post_imp)
          apply (clarsimp simp: schact_is_rct_def)
         apply (wpsimp wp: reschedule_cnt)
        apply wpsimp
       apply (wpsimp wp: is_schedulable_wp)
      apply (wpsimp wp: hoare_drop_imps sched_context_resume_ct_not_in_release_q
                        update_sched_context_wp set_object_wp
                  simp: set_tcb_obj_ref_def)+
  apply (clarsimp simp: vs_all_heap_simps pred_map_simps obj_at_def)
  done

lemma invoke_tcb_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> invs s \<and> schact_is_rct s \<and> tcb_inv_wf iv s \<and> ct_active s\<rbrace>
   invoke_tcb iv
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>, -"
  apply (cases iv; clarsimp;
         (solves \<open>wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift mapM_x_inv_wp\<close>)?)

   apply (find_goal \<open>match premises in \<open>_ = NotificationControl _ _ \<close> \<Rightarrow> \<open>-\<close>\<close>)
      apply (rename_tac t ntfn)
      apply (case_tac ntfn; wpsimp wp: hoare_vcg_imp_lift')

     apply (find_goal \<open>match premises in \<open>_ = Resume _ \<close> \<Rightarrow> \<open>-\<close>\<close>)
     apply (rename_tac thread)
     apply (rule valid_validE_R)
     apply (rule_tac P="\<lambda>s. thread = cur_thread s" in hoare_pre_tautI)
      apply (wpsimp wp: restart_ct_not_in_release_q_active hoare_drop_imps)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb_def ct_in_state_def
                      split: kernel_object.splits)
     apply (wpsimp wp: restart_ct_not_in_release_q_not_cur_thread hoare_drop_imps)
     apply (fastforce dest: invs_strengthen_cur_sc_tcb_are_bound
                      simp: obj_at_def pred_tcb_at_def vs_all_heap_simps)

    apply (find_goal \<open>match premises in \<open>_ = WriteRegisters _  _ _ _ \<close> \<Rightarrow> \<open>-\<close>\<close>)
    apply (rename_tac dest resume_target vals arch)
    apply (rule valid_validE_R)
    apply (rule_tac P="\<lambda>s. dest = cur_thread s" in hoare_pre_tautI)
     apply (wpsimp wp: hoare_vcg_imp_lift' restart_ct_not_in_release_q_active
                       hoare_vcg_disj_lift
            | intro conjI impI)+
      apply (fastforce simp: pred_tcb_at_def obj_at_def is_tcb_def ct_in_state_def
                      split: kernel_object.splits)
    apply (wpsimp wp: hoare_vcg_imp_lift' restart_ct_not_in_release_q_not_cur_thread
           | intro conjI impI)+
     apply (fastforce dest: invs_strengthen_cur_sc_tcb_are_bound
                      simp: obj_at_def pred_tcb_at_def vs_all_heap_simps)

   apply (find_goal \<open>match premises in \<open>_ = CopyRegisters _  _ _ _ _ _ _\<close> \<Rightarrow> \<open>-\<close>\<close>)
   apply (rule valid_validE_R)
   apply (rename_tac dest src suspend_source resume_target transfer_frame transfer_integer transfer_arch)
   apply (rule validE_valid)
   apply (subst liftE_validE)
   apply (rule_tac B="\<lambda>_ s. ct_not_in_release_q s \<and> cur_sc_tcb_are_bound s \<and> invs s
                            \<and> ex_nonz_cap_to src s \<and> ex_nonz_cap_to dest s"
                in hoare_seq_ext[rotated])
    apply (wpsimp wp: suspend_invs)
    apply (frule invs_strengthen_cur_sc_tcb_are_bound, fastforce+)
    using idle_no_ex_cap idle_thread_idle_thread_ptr
    apply (metis invs_valid_global_refs invs_valid_idle invs_valid_objs)
   apply (rule_tac B="\<lambda>_ s. in_release_q (cur_thread s) s \<longrightarrow> dest = cur_thread s"
                in hoare_seq_ext[rotated])
    apply (wpsimp wp: hoare_vcg_imp_lift' restart_ct_not_in_release_q_not_cur_thread)
    apply (fastforce dest: invs_strengthen_cur_sc_tcb_are_bound
                     simp: obj_at_def pred_tcb_at_def vs_all_heap_simps)
   apply (rule hoare_seq_ext_skip)
    apply (wpsimp wp: hoare_vcg_imp_lift' mapM_x_wp_inv)
   apply (rule hoare_seq_ext_skip)
    apply (wpsimp wp: hoare_vcg_imp_lift' mapM_x_wp_inv)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (rule hoare_seq_ext)
    apply (rule return_inv)
   apply (rule hoare_when_cases, simp)
   apply (rule_tac Q="\<lambda>_ s. scheduler_action s = choose_new_thread" in hoare_post_imp)
    apply (clarsimp simp: schact_is_rct_def)
   apply (wpsimp wp: reschedule_cnt)

  \<comment> \<open>iv = ThreadControlSched\<close>
  apply (rename_tac target a b fault_handler mcp priority sc)
  apply (clarsimp simp: validE_R_def)
  apply (rule_tac Q="\<lambda>s. ct_not_in_release_q s
                         \<and> invs s \<and> schact_is_rct s \<and> tcb_at target s
                         \<and> (case sc of None \<Rightarrow> \<lambda>_. True
                                     | Some None \<Rightarrow> \<lambda>s. True
                                     | Some (Some scptr) \<Rightarrow> (bound_sc_tcb_at ((=) None) target)
                                                             and sc_tcb_sc_at ((=) None) scptr) s"
               in hoare_weaken_preE[rotated])
   apply (clarsimp split: option.splits)
  apply (rule_tac B="\<lambda>_ s. ct_not_in_release_q s
                           \<and> bound_sc_tcb_at bound (cur_thread s) s
                           \<and> tcb_at target s
                           \<and> (case sc of None \<Rightarrow> \<lambda>_. True
                                       | Some None \<Rightarrow> \<lambda>s. True
                                       | Some (Some scptr) \<Rightarrow> (bound_sc_tcb_at ((=) None) target)
                                                               and sc_tcb_sc_at ((=) None) scptr) s"
               in hoare_vcg_seqE[rotated])
   apply (rule hoare_weaken_preE)
    apply (subst validE_R_def[symmetric])
    apply (rule hoare_vcg_conj_lift_R)
     apply wpsimp
    apply (rule hoare_vcg_conj_lift_R)
     apply (rule valid_validE_R)
     apply (rule_tac f=cur_thread in hoare_lift_Pf2)
      apply (wpsimp wp: hoare_case_option_wp install_tcb_cap_bound_sc_tcb_at)
     apply wpsimp
    apply (wpsimp wp: hoare_case_option_wp install_tcb_cap_sc_tcb_sc_at)
    apply (fastforce dest: invs_strengthen_cur_sc_tcb_are_bound
                     simp: obj_at_def pred_tcb_at_def vs_all_heap_simps
                    split: option.splits)
  apply (rule hoare_seq_ext_skipE)
   apply (wpsimp wp: hoare_case_option_wp install_tcb_cap_sc_tcb_sc_at)
   apply (clarsimp split: option.splits)
  apply (rule hoare_seq_ext_skipE)
   apply (wpsimp wp: hoare_case_option_wp install_tcb_cap_sc_tcb_sc_at)
   apply (clarsimp split: option.splits)
  apply (subst liftE_bindE)
  apply (clarsimp simp: maybeM_def)
  apply (case_tac sc; clarsimp)
   apply wpsimp
  apply (clarsimp split: option.splits)
  apply (intro conjI)
   apply (wpsimp wp: hoare_drop_imps)
  apply (clarsimp simp: maybe_sched_context_bind_tcb_def bind_assoc)
  apply (wpsimp wp: sched_context_bind_tcb_schact_is_rct_imp_ct_not_in_release_q hoare_vcg_if_lift2)
    apply (wpsimp wp: hoare_drop_imps)
   apply wpsimp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

crunches invoke_irq_handler
  for ct_not_in_release_q[wp]: ct_not_in_release_q

lemma perform_invocation_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> invs s \<and> schact_is_rct s \<and> valid_invocation iv s \<and> ct_active s\<rbrace>
   perform_invocation block call can_donate iv
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>, -"
  apply (cases iv; simp, (solves \<open>wpsimp wp: hoare_drop_imps\<close>)?)
    apply (wpsimp wp: hoare_vcg_imp_lift')
    apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def split: if_splits)
   apply (wpsimp wp: invoke_tcb_schact_is_rct_imp_ct_not_in_release_q)
  apply (wpsimp wp: invoke_sched_control_configure_flags_schact_is_rct_imp_ct_not_in_release_q)
  done

lemma handle_invocation_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s.  ct_not_in_release_q s \<and> cur_sc_active s \<and> invs s \<and> schact_is_rct s \<and> ct_active s\<rbrace>
   handle_invocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  (is "\<lbrace>?P\<rbrace> _ \<lbrace>\<lambda>_. ?Q\<rbrace>")
  apply (clarsimp simp: handle_invocation_def)
  apply (subst liftE_bindE)
  apply (rule hoare_seq_ext[OF _  gets_sp])
  apply (subst liftE_bindE)
  apply (rule_tac B="\<lambda>rv. ?P and (\<lambda>s. cur_thread s = thread) and K (valid_message_info rv)"
               in hoare_seq_ext[rotated])
   apply wpsimp
  apply (rule validE_valid)
  apply (rule_tac P_flt="\<lambda>_. ?Q" and P_err="\<lambda>_. ?Q"
              and P_no_err="\<lambda>rv. ?P and (\<lambda>s. cur_thread s = thread) and valid_invocation rv"
               in syscall_valid)
      apply (wpsimp wp: hoare_vcg_imp_lift')
     apply (wpsimp wp: hoare_vcg_imp_lift')
    apply (rule hoare_weaken_preE)
     apply (rule hoare_vcg_E_elim)
      apply (wpsimp wp: handle_invocation_ct_not_in_release_qE_E hoare_drop_impE_E)
     apply (wpsimp wp: perform_invocation_schact_is_rct_imp_ct_not_in_release_q)
              apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
             apply (wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
            apply (wpsimp wp: gts_wp')+
      apply (clarsimp simp: validE_R_def)
      apply (rule_tac Q="\<lambda>_. ?Q" and E="\<lambda>_. ?Q" in hoare_post_impErr[rotated]; fastforce?)
      apply (rule hoare_vcg_E_elim)
       apply (wpsimp wp: handle_invocation_ct_not_in_release_qE_E hoare_drop_impE_E)
      apply (wpsimp wp: perform_invocation_schact_is_rct_imp_ct_not_in_release_q)
     apply (wpsimp wp: perform_invocation_schact_is_rct_imp_ct_not_in_release_q)
     apply (wpsimp wp: ct_in_state_set set_thread_state_schact_is_rct_strong)
    apply (fastforce intro: cur_sc_active_active_sc_tcb_at_cur_thread
                      simp: ct_in_state_def)
   apply (wp hoare_vcg_E_conj | simp add: split_def)+
  by fastforce

lemma charge_budget_schact_is_rct_imp_ct_not_in_release_q[wp]:
  "charge_budget consumed canTimeout \<lbrace>\<lambda>s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: charge_budget_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (rule hoare_when_cases, simp)
  apply wpsimp
      apply (rule_tac Q="\<lambda>_ s. scheduler_action s = choose_new_thread" in hoare_post_imp)
       apply (clarsimp simp: schact_is_rct_def)
      apply (wpsimp wp: reschedule_cnt hoare_drop_imps)+
  done

crunches handle_yield, check_budget
  for schact_is_rct_imp_ct_not_in_release_q[wp]: "\<lambda>s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s"

lemma check_budget_restart_schact_is_rct_imp_ct_not_in_release_q[wp]:
  "check_budget_restart \<lbrace>\<lambda>s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: hoare_vcg_imp_lift')
  done

crunches receive_ipc, handle_fault
  for ct_not_in_release_q[wp]: ct_not_in_release_q
  (wp: crunch_wps simp: crunch_simps)

lemma maybe_donate_sc_ct_not_in_release_q_thread_bound:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> thread = cur_thread s \<and> bound_sc_tcb_at bound (cur_thread s) s\<rbrace>
   maybe_donate_sc thread sc_ptr
   \<lbrace>\<lambda>_. ct_not_in_release_q\<rbrace>"
  apply (clarsimp simp: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_when_cases, simp)
  apply (wpsimp wp: hoare_pre_cont)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma receive_signal_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s \<and> thread = cur_thread s\<rbrace>
   receive_signal thread cap is_blocking
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: receive_signal_def)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (case_tac "ntfn_obj ntfn"; clarsimp?, (solves \<open>wpsimp wp: hoare_vcg_imp_lift'\<close>)?)
  apply (rule hoare_vcg_imp_lift_pre_add; (solves wpsimp)?)
  apply (rule hoare_seq_ext_skip, solves wpsimp)
  apply (wpsimp wp: maybe_donate_sc_ct_not_in_release_q_thread_bound set_simple_ko_wp)
  apply (fastforce dest: invs_strengthen_cur_sc_tcb_are_bound
                   simp: obj_at_def pred_tcb_at_def vs_all_heap_simps sk_obj_at_pred_def)
  done

lemma handle_recv_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s\<rbrace>
   handle_recv is_blocking can_reply
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: handle_recv_def Let_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule catch_wp)
   apply (wpsimp wp: hoare_vcg_imp_lift')
  apply clarsimp
  apply (rule hoare_seq_ext_skipE, wpsimp)
  apply (case_tac ep_cap; clarsimp; (solves \<open>wpsimp wp: hoare_vcg_imp_lift'\<close>)?)
   apply (wpsimp wp: hoare_vcg_imp_lift')
   apply fastforce
  apply (wpsimp wp: receive_signal_schact_is_rct_imp_ct_not_in_release_q get_sk_obj_ref_wp)
  done

method handle_event_schact_is_rct_imp_ct_not_in_release_q for e
  = rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift',
    rule_tac B="\<lambda>rv s. (rv \<longrightarrow> (ct_not_in_release_q s \<and> invs s \<and> schact_is_rct s
                                \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)
                                \<and> cur_sc_active s ))
                       \<and> (\<not>rv \<longrightarrow> (schact_is_rct s \<longrightarrow> ct_not_in_release_q s))"
          in hoare_seq_ext[rotated],
    intro hoare_vcg_conj_lift_pre_fix,
    wpsimp wp: check_budget_restart_true,
    rule check_budget_restart_false,
    wpsimp,
    clarsimp simp: whenE_def,
    (intro conjI impI; (solves wpsimp)?),
    wpsimp wp: handle_invocation_schact_is_rct_imp_ct_not_in_release_q
               handle_recv_schact_is_rct_imp_ct_not_in_release_q,
    ((cases e;
     fastforce dest: invs_strengthen_cur_sc_tcb_are_bound
               simp: obj_at_def pred_tcb_at_def vs_all_heap_simps schedulable_def2 ct_in_state_def
                     runnable_eq_active)?)

method handle_event_schact_is_rct_imp_ct_not_in_release_q_misc for e
  = clarsimp simp: liftE_def bind_assoc,
    rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift',
    rule_tac B="\<lambda>rv s. (rv \<longrightarrow> ((schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s
                                \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)
                                \<and> cur_sc_active s))
                       \<and> (\<not>rv \<longrightarrow> (schact_is_rct s \<longrightarrow> ct_not_in_release_q s))"
          in hoare_seq_ext[rotated],
    intro hoare_vcg_conj_lift_pre_fix,
    wpsimp wp: check_budget_restart_true,
    rule check_budget_restart_false,
    wpsimp,
    wpsimp wp: hoare_vcg_imp_lift'

method handle_event_schact_is_rct_imp_ct_not_in_release_q_yield for e
  = clarsimp simp: liftE_def bind_assoc,
    rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift',
    rule_tac B="\<lambda>rv s. (rv \<longrightarrow> ((schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s
                                \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)
                                \<and> cur_sc_active s))
                       \<and> (\<not>rv \<longrightarrow> (schact_is_rct s \<longrightarrow> ct_not_in_release_q s))"
          in hoare_seq_ext[rotated],
    intro hoare_vcg_conj_lift_pre_fix,
    wpsimp wp: check_budget_restart_true,
    rule check_budget_restart_false,
    wpsimp,
    clarsimp simp: whenE_def,
    (intro conjI impI; (solves wpsimp)?)

lemma handle_interrupt_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s
         \<and> ct_not_blocked_on_receive s \<and> ct_not_blocked_on_ntfn s\<rbrace>
   handle_interrupt irq
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: handle_interrupt_def)
  apply (rule hoare_if; (solves wpsimp)?)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext, wpsimp)
  apply (case_tac st; clarsimp?, (solves wpsimp)?)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (wpsimp wp: hoare_vcg_imp_lift')
  apply (clarsimp split: if_splits)
  done

lemma handle_event_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> invs s \<and> schact_is_rct s \<and> cur_sc_active s
        \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   handle_event e
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (cases e; (solves \<open>wpsimp wp: hoare_drop_imps cur_sc_active_lift\<close>)?)
  apply (rename_tac syscall)

       \<comment> \<open>SyscallEvent\<close>
       subgoal for syscall
       by (case_tac syscall, simp_all add: handle_send_def handle_call_def liftE_bindE;
           (handle_event_schact_is_rct_imp_ct_not_in_release_q e
            | handle_event_schact_is_rct_imp_ct_not_in_release_q_yield e))

      apply (find_goal \<open>match premises in "_ = Interrupt" \<Rightarrow> \<open>-\<close>\<close>)
      defer

      apply (handle_event_schact_is_rct_imp_ct_not_in_release_q_misc e)+

  \<comment> \<open>Interrupt\<close>
  apply (clarsimp simp: liftE_def bind_assoc)
  apply (rule hoare_seq_ext_skip, wpsimp)
    apply (clarsimp simp: ct_in_state_def)
   apply simp
  apply (rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_disj_lift hoare_vcg_imp_lift')
  apply (rule_tac B="\<lambda>_ s. (schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s \<and> cur_sc_active s
                           \<and> ct_not_blocked_on_receive s \<and> ct_not_blocked_on_ntfn s"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: cur_sc_active_lift)
   apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def
                   split: thread_state.splits)
  apply (wpsimp wp: handle_interrupt_schact_is_rct_imp_ct_not_in_release_q)
  done

lemma preemption_path_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. (schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s
        \<and> ct_not_blocked_on_receive s \<and> ct_not_blocked_on_ntfn s\<rbrace>
   preemption_path
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: preemption_path_def)
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp simp: ct_in_state_def\<close>)+
  apply (wpsimp wp: handle_interrupt_schact_is_rct_imp_ct_not_in_release_q)
  done

lemma handle_event_preemption_path_schact_is_rct_imp_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> invs s \<and> schact_is_rct s \<and> cur_sc_active s
        \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
   handle_event e <handle> (\<lambda>_. liftE preemption_path)
   \<lbrace>\<lambda>_ s. schact_is_rct s \<longrightarrow> ct_not_in_release_q s\<rbrace>"
  apply (rule validE_valid)
  apply (rule_tac F="\<lambda>_ s. (schact_is_rct s \<longrightarrow> ct_not_in_release_q s) \<and> invs s \<and> ct_not_blocked s"
               in handleE_wp)
   apply (wpsimp wp: preemption_path_schact_is_rct_imp_ct_not_in_release_q)
   apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
   apply (rename_tac tcb, case_tac "tcb_state tcb"; clarsimp)
  apply (rule hoare_vcg_E_elim[where P=P and P'=P for P, simplified])
   apply (intro hoare_validE_E_conjI)
     apply (rule valid_validE_E)
     apply (wpsimp wp: handle_event_schact_is_rct_imp_ct_not_in_release_q)
    apply wpsimp
    apply (fastforce dest!: cur_sc_active_ct_not_in_release_q_imp_ct_running_imp_ct_schedulable
                      simp: schact_is_rct_def)
   apply (rule_tac Q'="\<lambda>_. ct_not_blocked" in hoare_post_imp_E)
    apply wpsimp
    apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def
                    split: thread_state.splits)
   apply simp
  apply (wpsimp wp: handle_event_schact_is_rct_imp_ct_not_in_release_q)
  done

crunches awaken, check_domain_time, sc_and_timer, tcb_sched_action
  for ct_not_in_release_q[wp]: ct_not_in_release_q
  (wp: crunch_wps)

lemma schedule_switch_thread_branch_ct_not_in_release_q:
  "\<lbrace>valid_release_q and valid_idle and ready_or_release and (\<lambda>s. ct_schdble = ct_schedulable s)
    and (not_in_release_q candidate) and (\<lambda>s. ct = cur_thread s)\<rbrace>
   schedule_switch_thread_branch candidate ct ct_schdble
   \<lbrace>\<lambda>_ s :: det_state. ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: schedule_switch_thread_fastfail_def)
  apply (rule_tac B="\<lambda>_. valid_release_q and valid_idle and ready_or_release
                         and (not_in_release_q candidate)"
               in hoare_seq_ext[rotated])
   apply (wpsimp simp: schedulable_def2)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (wpsimp wp: schedule_choose_new_thread_ct_not_in_release_q
                    switch_to_thread_active_sc_tcb_at_cur_thread thread_get_wp)
  done

lemma schedule_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. valid_sched s \<and> invs s \<and> (schact_is_rct s \<longrightarrow> ct_not_in_release_q s)\<rbrace>
   schedule
   \<lbrace>\<lambda>_ s :: det_state. ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: schedule_def)
  apply (rule hoare_seq_ext_skip, wpsimp wp: awaken_valid_sched hoare_vcg_imp_lift')
  apply (rule hoare_seq_ext_skip, wpsimp wp: hoare_vcg_imp_lift' cur_sc_active_lift)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac action)
  apply (rule hoare_seq_ext)
   apply wpsimp
  apply (case_tac action; clarsimp)
    apply wpsimp
    apply (fastforce simp: schact_is_rct_def)
   apply (subst bind_dummy_ret_val)+
   apply (rule hoare_weaken_pre)
    apply (rule schedule_switch_thread_branch_ct_not_in_release_q)
   apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                         not_in_release_q_def)
  apply (wpsimp wp: schedule_choose_new_thread_ct_not_in_release_q)
  by (fastforce simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                      not_in_release_q_def schedulable_def2)

lemma call_kernel_ct_not_in_release_q:
  "\<lbrace>\<lambda>s. ct_not_in_release_q s \<and> cur_sc_active s \<and> invs s \<and> schact_is_rct s \<and> valid_sched s
        \<and> (ct_running s \<or> ct_idle s) \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s)
        \<and> cur_sc_offset_ready (consumed_time s) s \<and> current_time_bounded 5 s
        \<and> valid_machine_time s \<and> consumed_time_bounded s\<rbrace>
   call_kernel e
   \<lbrace>\<lambda>_ s :: det_state. ct_not_in_release_q s\<rbrace>"
  apply (clarsimp simp: call_kernel_def)
  apply (simp flip: bind_assoc)
  apply (rule hoare_seq_ext)
   apply (wpsimp wp: cur_sc_active_lift)
  apply (rule hoare_seq_ext[OF schedule_ct_not_in_release_q])
  apply (intro hoare_vcg_conj_lift_pre_fix)
    apply (wpsimp wp: handle_event_preemption_path_valid_sched)
   apply wpsimp
   apply (fastforce dest!: cur_sc_active_ct_not_in_release_q_imp_ct_running_imp_ct_schedulable)
  apply (wpsimp wp: handle_event_preemption_path_schact_is_rct_imp_ct_not_in_release_q)
  done

end
