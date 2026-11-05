(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IpcCancel_AI
imports ArchSchedule_AI
begin

arch_requalify_facts
  arch_post_cap_deletion_pred_tcb_at
  arch_post_cap_deletion_cur_thread
  as_user_hyp_refs_of

declare arch_post_cap_deletion_pred_tcb_at[wp]
declare as_user_hyp_refs_of[wp]

crunch is_final_cap
  for inv[wp]: P

lemma blocked_cancel_ipc_simple:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: blocked_cancel_ipc_def | wp)+

lemma cancel_signal_simple:
  "\<lbrace>\<top>\<rbrace> cancel_signal t ntfn \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: cancel_signal_def | wp)+

crunch cancel_all_ipc
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)

crunch restart_thread_if_no_fault
  for valid_objs[wp]: valid_objs
  (wp: crunch_wps)

lemma tcb_ep_dequeue_valid_objs[wp]:
  "tcb_ep_dequeue tptr ep_ptr \<lbrace>valid_objs\<rbrace>"
  apply (clarsimp simp: tcb_ep_dequeue_def)
  apply (wpsimp wp: get_simple_ko_wp)
  apply (rename_tac ep)
  apply (prop_tac "valid_ep ep s")
   apply (force simp: valid_objs_def valid_obj_def valid_ep_def obj_at_def)
  apply (clarsimp simp: valid_ep_def split: list.splits)
  apply (prop_tac "set (filter ((\<noteq>) tptr) (ep_queue ep)) \<subseteq> set (ep_queue ep)")
   apply (rule filter_is_subset)
  apply (prop_tac "distinct (filter ((\<noteq>) tptr) (ep_queue ep))")
   apply (force intro!: distinct_filter split: endpoint.splits)
  apply (force simp: removeAll_filter_not_eq split: endpoint.splits)
  done

lemma tcb_ntfn_dequeue_valid_objs[wp]:
  "tcb_ntfn_dequeue tptr ntfn_ptr \<lbrace>valid_objs\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  apply (wpsimp wp: get_simple_ko_wp)
  apply (frule (1) valid_objs_ko_at)
  apply (rename_tac ntfn)
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
  apply (rename_tac q)
  apply (clarsimp simp: valid_ntfn_def valid_obj_def split: option.splits list.splits)
  apply (frule distinct_filter[where P="(\<noteq>) tptr"])
  apply (cut_tac P="(\<noteq>) tptr" and xs=q in filter_is_subset)
  apply (force simp: removeAll_filter_not_eq)
  done

crunch cancel_all_ipc, cancel_all_signals, cancel_badged_sends
  for valid_objs[wp]: valid_objs
  (wp: crunch_wps)

lemma unbind_notification_valid_objs[wp]:
  "unbind_notification ptr \<lbrace>valid_objs\<rbrace>"
  apply (wpsimp simp: unbind_notification_def update_sk_obj_ref_def wp: maybeM_inv)
     apply (rule hoare_strengthen_post)
      apply (rule get_ntfn_valid_ntfn)
     apply (wpsimp simp: valid_ntfn_def split: ntfn.splits)+
  done

lemma sched_context_maybe_unbind_ntfn_valid_objs[wp]:
  notes refs_of_simps[simp del]
  shows
  "\<lbrace>valid_objs\<rbrace> sched_context_maybe_unbind_ntfn ntfn_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: sched_context_maybe_unbind_ntfn_def )
  apply (wpsimp simp: update_sk_obj_ref_def
                  wp: valid_irq_node_typ set_simple_ko_valid_objs get_simple_ko_wp get_sk_obj_ref_wp)
  apply (auto simp: obj_at_def valid_obj_def valid_ntfn_def split: ntfn.splits)
  done

lemma possible_switch_to_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   possible_switch_to ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by wpsimp

lemma reply_unlink_tcb_st_tcb_at:
  "\<lbrace>\<lambda>s. if t'=t then P (P' Inactive) else P (st_tcb_at P' t' s)\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_ s. P (st_tcb_at P' t' s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def
                  wp: sts_st_tcb_at_cases_strong gts_wp get_simple_ko_wp update_reply_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma unbind_notification_st_tcb_at[wp]:
  "unbind_notification t' \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: unbind_notification_def update_sk_obj_ref_def wp: maybeM_inv)

lemma unbind_maybe_notification_st_tcb_at[wp]:
  "unbind_maybe_notification r \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def update_sk_obj_ref_def get_sk_obj_ref_def wp: maybeM_inv)

crunch tcb_ep_dequeue, tcb_ntfn_dequeue
  for st_tcb_at[wp]: "\<lambda>s. P (st_tcb_at P' t s)"
  and tcb_at[wp]: "\<lambda>s. P (tcb_at t s)"
  (wp: crunch_wps)

lemma thread_set_ntfn_at_pred[wp]:
  "thread_set a b \<lbrace>\<lambda>s. Q (ntfn_at_pred P p s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: ntfn_at_pred_def get_tcb_def)
  done

crunch possible_switch_to, if_cond_refill_unblock_check, set_thread_state
  for ntfn_at_pred[wp]: "\<lambda>s. Q (ntfn_at_pred P p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma cancel_all_signals_st_tcb_at':
  "\<lbrace>\<lambda>s. if ntfn_at_pred (\<lambda>notification. t \<in> set (ntfn_queue (ntfn_obj notification))) ntfn_ptr s
        then P (P' Restart)
        else P (st_tcb_at P' t s)\<rbrace>
   cancel_all_signals ntfn_ptr
   \<lbrace>\<lambda>_ s. P (st_tcb_at P' t s)\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp], rename_tac notification)
  apply wpsimp
     apply (rule_tac V="\<lambda>q s. if t \<in> set q then P (P' Restart) else P (st_tcb_at P' t s)"
                  in mapM_x_inv_wp2[where I=\<top>, simplified])
      apply fastforce
     apply (wpsimp simp: remove_and_restart_ntfn_queued_thread_def
                     wp: sts_st_tcb_at_cases_strong hoare_vcg_imp_lift')+
  apply (fastforce simp: obj_at_def ntfn_at_pred_def st_tcb_at_def)
  done

lemma cancel_all_signals_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  by (auto intro: hoare_weaken_pre[OF cancel_all_signals_st_tcb_at'])

lemmas cancel_all_signals_makes_simple[wp] =
       cancel_all_signals_st_tcb_at[where P=simple, simplified]

lemma get_blocking_object_inv[wp]:
  "\<lbrace>P\<rbrace> get_blocking_object st \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases st, simp_all add: get_blocking_object_def ep_blocked_def assert_opt_def)

crunch reply_pop, break_reply_chain_at
  for st_tcb_at[wp]: "\<lambda>s. Q (st_tcb_at P t s)"
  (wp: crunch_wps)

crunch test_reschedule, tcb_release_remove
  for reply_tcb_reply_at[wp]: "\<lambda>s. P (reply_at_pred P' p s)"
  (wp: crunch_wps simp: crunch_simps)

global_interpretation sched_context_donate: non_reply_op "sched_context_donate scp tp"
  by unfold_locales (wpsimp simp: sched_context_donate_def
                              wp: hoare_vcg_if_lift2 hoare_drop_imps)

global_interpretation reply_pop: non_reply_tcb_op "reply_pop reply_ptr sc_ptr"
  by unfold_locales
     (wpsimp simp: reply_pop_def
               wp: hoare_vcg_all_lift hoare_drop_imps)

global_interpretation break_reply_chain_at: non_reply_tcb_op "break_reply_chain_at reply_ptr"
  by unfold_locales
     (wpsimp simp: break_reply_chain_at_def
               wp: get_sk_obj_ref_wp)

lemma reply_remove_st_tcb_at[wp]:
  "\<lbrace> \<lambda>s. if t'=t then P (P' Inactive) else P (st_tcb_at P' t' s) \<rbrace>
    reply_remove t r
   \<lbrace> \<lambda>rv s. P (st_tcb_at P' t' s) \<rbrace>"
  supply if_split[split del]
  by (wpsimp simp: reply_remove_def wp: reply_unlink_tcb_st_tcb_at get_simple_ko_wp)
     (clarsimp split: if_splits)

lemmas set_thread_state_st_tcb_at = sts_st_tcb_at_cases

lemma blocked_ipc_st_tcb_at_general:
  "\<lbrace>\<lambda>s. if t'=t then P (P' Inactive) else P (st_tcb_at P' t' s)\<rbrace>
   blocked_cancel_ipc st t rptropt
   \<lbrace>\<lambda>rv s. P (st_tcb_at P' t' s)\<rbrace>"
  unfolding blocked_cancel_ipc_def
  by (wpsimp wp: sts_st_tcb_at_cases_strong reply_unlink_tcb_st_tcb_at
                 hoare_drop_imp[where Q'="\<lambda>rv. tcb_at t"])

lemma cancel_signal_st_tcb_at_general:
  "\<lbrace>\<lambda>s. if t'=t then P (P' Inactive) else P (st_tcb_at P' t' s) \<rbrace>
   cancel_signal t ntfn
   \<lbrace>\<lambda>rv s. P (st_tcb_at P' t' s)\<rbrace>"
  by (wpsimp simp: cancel_signal_def
               wp: sts_st_tcb_at_cases_strong ntfn_cases_weak_wp hoare_weak_lift_imp
                   set_simple_ko_pred_tcb_at hoare_drop_imp[where Q'="\<lambda>rv. tcb_at t"])

lemma sched_context_maybe_unbind_ntfn_st_tcb_at[wp]:
  "sched_context_maybe_unbind_ntfn ntfnptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
   by (wpsimp simp: sched_context_maybe_unbind_ntfn_def sched_context_unbind_ntfn_def
                    update_sk_obj_ref_def get_sc_obj_ref_def get_sk_obj_ref_def
                wp: hoare_drop_imps)

lemma sched_context_unbind_ntfn_st_tcb_at[wp]:
  "sched_context_unbind_ntfn scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_ntfn_def update_sk_obj_ref_def
                   get_sc_obj_ref_def)

lemma sched_context_update_consumed_st_tcb_at[wp]:
  "sched_context_update_consumed scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

lemma set_message_info_st_tcb_at[wp]:
  "set_message_info a b \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
   by (wpsimp simp: set_message_info_def)

lemma sched_context_cancel_yield_to_st_tcb_at[wp]:
  "sched_context_cancel_yield_to scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_cancel_yield_to_def wp: hoare_drop_imp)

lemma complete_yield_to_st_tcb_at[wp]:
  "complete_yield_to scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: complete_yield_to_def set_consumed_def wp: hoare_drop_imp)

lemma sched_context_unbind_yield_from_st_tcb_at[wp]:
  "sched_context_unbind_yield_from scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_yield_from_def)

crunch tcb_release_remove, sched_context_unbind_all_tcbs
 for st_tcb_at[wp]: "\<lambda>s. Q (st_tcb_at P t s)"
  (wp: crunch_wps ignore: thread_set)


locale IpcCancel_AI =
    fixes state_ext :: "('a::state_ext) itself"
    assumes arch_post_cap_deletion_typ_at[wp]:
      "\<And>P T p acap. \<lbrace>\<lambda>(s :: 'a state). P (typ_at T p s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
    assumes arch_post_cap_deletion_idle_thread[wp]:
      "\<And>P acap. \<lbrace>\<lambda>(s :: 'a state). P (idle_thread s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"

crunch update_restart_pc
  for typ_at[wp]: "\<lambda>s. P (typ_at ty ptr s)"
  (* NB: Q needed for following has_reply_cap proof *)
  and cte_wp_at[wp]: "\<lambda>s. Q (cte_wp_at P cte s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and pred_tcb_at[wp]: "\<lambda>s. pred_tcb_at P proj tcb s"
  and invs[wp]: "\<lambda>s. invs s"

lemma update_restart_pc_has_reply_cap[wp]:
  "\<lbrace>\<lambda>s. \<not> has_reply_cap t s\<rbrace> update_restart_pc t \<lbrace>\<lambda>_ s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: has_reply_cap_def)
  apply (wp hoare_vcg_all_lift)
  done

crunch reply_remove, reply_remove_tcb
  for st_tcb_at_simple[wp]: "st_tcb_at simple t"
  (wp: crunch_wps sts_st_tcb_at_cases)

lemma cancel_ipc_simple [wp]:
  "\<lbrace>\<top>\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule bind_wp [OF _ gts_sp])
  apply (case_tac state, simp_all)
         apply (wp hoare_strengthen_post [OF blocked_cancel_ipc_simple]
                   hoare_strengthen_post [OF cancel_signal_simple]
                   sts_st_tcb_at_cases thread_set_no_change_tcb_state hoare_drop_imps
                | (rule pred_tcb_weakenE, fastforce)
                | clarsimp elim!: pred_tcb_weakenE pred_tcb_at_tcb_at)+
  done

lemma reply_remove_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> reply_remove t r \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: reply_unlink_tcb_typ_at hoare_drop_imp)

crunch tcb_ep_dequeue, tcb_ntfn_dequeue
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

lemma blocked_cancel_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> blocked_cancel_ipc st t r \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: blocked_cancel_ipc_def wp: reply_unlink_tcb_typ_at get_simple_ko_inv assert_inv)

lemma blocked_cancel_ipc_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc st t' r \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp

crunch cancel_ipc, reply_remove_tcb, unbind_maybe_notification
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

lemma cancel_ipc_tcb [wp]:
  "\<lbrace>tcb_at t\<rbrace> cancel_ipc t' \<lbrace>\<lambda>rv. (tcb_at t) \<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma gbep_ret:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr r d \<or>
     st = Structures_A.BlockedOnSend epPtr p \<rbrakk>
   \<Longrightarrow> get_blocking_object st = return epPtr"
  by (auto simp add: get_blocking_object_def ep_blocked_def assert_opt_def)

locale delete_one_abs =
  fixes state_ext_type :: "('a :: state_ext) itself"
  assumes delete_one_invs:
    "\<And>p. \<lbrace>invs\<rbrace> (cap_delete_one p :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"

  assumes delete_one_deletes:
    "\<lbrace>\<top>\<rbrace> (cap_delete_one sl :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) sl\<rbrace>"

  assumes delete_one_caps_of_state:
    "\<And>P p. \<lbrace>\<lambda>s. cte_wp_at can_fast_finalise p s
                  \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap))\<rbrace>
             (cap_delete_one p :: (unit,'a) s_monad)
            \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"

lemma ep_redux_simps2:
  "ep \<noteq> Structures_A.IdleEP \<Longrightarrow>
   valid_ep (case xs of [] \<Rightarrow> Structures_A.endpoint.IdleEP
            | a # list \<Rightarrow> update_ep_queue ep xs is_recv)
     = (\<lambda>s. distinct xs \<and> (\<forall>t\<in>set xs. tcb_at t s))"
  "ep \<noteq> Structures_A.IdleEP \<Longrightarrow>
   ep_q_refs_of (case xs of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                   | a # list \<Rightarrow> update_ep_queue ep xs is_recv)
     = (set xs \<times> {case ep of Structures_A.SendEP xs \<Rightarrow> EPSend | Structures_A.RecvEP xs \<Rightarrow> EPRecv})"
 by (cases ep, simp_all cong: list.case_cong add: ep_redux_simps)+

lemma gbi_ep_sp:
  "\<lbrace>P\<rbrace>
     get_blocking_object st
   \<lbrace>\<lambda>ep. P and K ((\<exists>r d. st = Structures_A.BlockedOnReceive ep r d)
                    \<or> (\<exists>d. st = Structures_A.BlockedOnSend ep d))\<rbrace>"
  apply (cases st, simp_all add: get_blocking_object_def ep_blocked_def assert_opt_def)
   apply (wp | simp)+
  done

crunch reply_unlink_tcb
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and cte_wp_at[wp]: "cte_wp_at P c"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_global_objs[wp]: "valid_global_objs"
  and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
  and valid_arch_caps[wp]: "valid_arch_caps"
  and ifunsafe[wp]: "if_unsafe_then_cap"
  and valid_arch[wp]: "valid_arch_state"
  and valid_irq_states[wp]: "valid_irq_states"
  and vms[wp]: "valid_machine_state"
  and valid_vspace_objs[wp]: "valid_vspace_objs"
  and valid_global_refs[wp]: "valid_global_refs"
  and v_ker_map[wp]: "valid_kernel_mappings"
  and equal_mappings[wp]: "equal_kernel_mappings"
  and valid_asid_map[wp]: "valid_asid_map"
  and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
  and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  and pspace_respects_device_region[wp]: "pspace_respects_device_region"
  and cur_tcb[wp]: "cur_tcb"
  and cur_sc_tcb[wp]: "cur_sc_tcb"
  and valid_mdb[wp]: "valid_mdb"
  and valid_ioc[wp]: "valid_ioc"
  and valid_cur_fpu[wp]: valid_cur_fpu
  (simp: Let_def wp: hoare_drop_imps)

crunch reply_unlink_tcb
  for sc_at[wp]: "sc_at sc_ptr"
  (wp: crunch_wps)

lemma reply_unlink_tcb_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> reply_unlink_tcb t rp \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def get_simple_ko_def
                      get_object_def)
  apply (auto simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_rev)
  done

lemma reply_unlink_tcb_fault_tcbs_valid_states[wp]:
  "reply_unlink_tcb tp rp \<lbrace>fault_tcbs_valid_states_except_set TS\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def
                      get_simple_ko_def get_object_def
                  wp: sts_fault_tcbs_valid_states)
  done

lemma sts_only_idle:
  "\<lbrace>K (\<not> idle st) and only_idle\<rbrace> set_thread_state t st \<lbrace>\<lambda>_. only_idle\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def)
  done

lemma reply_unlink_tcb_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> reply_unlink_tcb t rp \<lbrace>\<lambda>_. only_idle\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: sts_only_idle
           simp: thread_get_def only_idle_def pred_tcb_at_def set_simple_ko_def get_object_def
                 get_simple_ko_def get_thread_state_def)

lemma reply_unlink_tcb_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> reply_unlink_tcb t rp \<lbrace>\<lambda>_. valid_irq_node\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def wp: valid_irq_node_typ hoare_drop_imp)

lemma reply_unlink_tcb_refs_of:
  "\<lbrace>\<lambda>s. \<forall>reply. kheap s r = Some (Reply reply) \<and> reply_tcb reply = Some t
        \<longrightarrow> P (\<lambda>p. if p = t then {r \<in> state_refs_of s p. snd r \<in> {TCBBound, TCBSchedContext, TCBYieldTo}}
                   else (if p = r then {r \<in> state_refs_of s p. snd r = ReplySchedContext}
                                  else state_refs_of s p))\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: reply_unlink_tcb_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule bind_wp[OF _ gts_inv])
  apply (rule bind_wp[OF _ assert_inv])
  apply (wpsimp split_del: if_split simp: obj_at_def)
  apply (erule rsubst[where P=P], rule ext)
  by (auto simp: in_state_refs_of_iff get_refs_def split: option.splits)

lemma tcb_at_no_sc_reply:
  "\<lbrakk> valid_objs s; tcb_at x s \<rbrakk> \<Longrightarrow> (t, SCReply) \<notin> state_refs_of s x"
  by (auto elim!: obj_at_valid_objsE
            simp: state_refs_of_def is_tcb get_refs_def tcb_st_refs_of_def
           split: thread_state.splits option.splits if_splits)

lemma tcb_at_ko_at:
  "tcb_at p s \<Longrightarrow> \<exists>tcb. ko_at (TCB tcb) p s"
  by (fastforce simp: obj_at_def is_tcb)

lemma tcb_state_refs_no_tcb:
  "\<lbrakk>valid_objs s; tcb_at y s; (x, ref) \<in> state_refs_of s y\<rbrakk> \<Longrightarrow> ~ tcb_at x s"
  apply (clarsimp simp: ko_at_state_refs_ofD dest!: tcb_at_ko_at)
  apply (erule (1) obj_at_valid_objsE)
  apply (auto simp: valid_obj_def obj_at_def valid_tcb_def valid_tcb_state_def get_refs_def
                    is_sc_obj_def is_ep is_reply is_ntfn
             split: thread_state.splits option.splits)
  done

global_interpretation set_endpoint: non_reply_op "set_endpoint p ep"
  by unfold_locales (clarsimp simp add: reply_at_ppred_def set_endpoint_obj_at_impossible)

global_interpretation set_simple_ko: non_sc_op "set_endpoint p ep"
  by unfold_locales
     (wpsimp wp: set_simple_ko_wp simp: sc_at_pred_n_def sk_obj_at_pred_def obj_at_def)

lemma set_endpoint_valid_replies[wp]:
  "set_endpoint p ep \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma reply_tcb_not_idle_thread_helper:
  "reply_tcb r = Some tp \<Longrightarrow>
   kheap s rp = Some (Reply r) \<Longrightarrow>
   sym_refs (state_refs_of s) \<Longrightarrow>
   (rp, TCBReply) \<in> state_refs_of s tp"
  by (clarsimp elim!: sym_refsE simp: state_refs_of_def)

lemma reply_unlink_tcb_valid_replies:
  "\<lbrace> \<lambda>s. P (replies_with_sc s) (replies_blocked_upd_tcb_st Inactive t (replies_blocked s)) \<rbrace>
    reply_unlink_tcb t r
   \<lbrace> \<lambda>r. valid_replies_pred P \<rbrace>"
  unfolding reply_unlink_tcb_def
  apply (wp sts_valid_replies gts_wp get_simple_ko_wp)
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def st_tcb_at_def)

lemma set_endpoint_invs:
  "\<lbrace> \<lambda>s. sym_refs (\<lambda>p'. if p' = p then ep_q_refs_of ep else state_refs_of s p')
         \<and> sym_refs (state_hyp_refs_of s)
         \<and> valid_ep ep s
         \<and> (ep \<noteq> IdleEP \<longrightarrow> ex_nonz_cap_to p s)
         \<and> all_invs_but_sym_refs s \<rbrace>
    set_endpoint p ep
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def live_def
               wp: valid_irq_node_typ)

definition mk_ep ::
  "(obj_ref list \<Rightarrow> endpoint) \<Rightarrow> obj_ref list \<Rightarrow> endpoint"
  where
  "mk_ep C \<equiv> \<lambda>queue. if queue = [] then IdleEP else C queue"

lemma ep_q_refs_of_mk_ep[simp]:
  "ep_q_refs_of (mk_ep SendEP queue) = set queue \<times> {EPSend}"
  "ep_q_refs_of (mk_ep RecvEP queue) = set queue \<times> {EPRecv}"
  by (auto simp: mk_ep_def)

abbreviation tcb_non_st_state_refs_of ::
  "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
  where
  "tcb_non_st_state_refs_of s t \<equiv>
    {r \<in> state_refs_of s t. snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo}"

lemma tcb_non_st_state_refs_of_state_refs_of:
  "ko_at (TCB tcb) t s \<Longrightarrow> tcb_st_refs_of (tcb_state tcb) = {}
    \<Longrightarrow> tcb_non_st_state_refs_of s t = state_refs_of s t"
  by (auto simp: state_refs_of_def obj_at_def tcb_st_refs_of_def get_refs_def
          split: thread_state.splits option.splits if_splits)

lemma st_tcb_at_tcb_non_st_state_refs_of:
  "st_tcb_at ((=) st) t s \<Longrightarrow> tcb_non_st_state_refs_of s t = state_refs_of s t - tcb_st_refs_of st"
  by (rule set_eqI) (auto simp add: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2)

lemmas st_tcb_at_tcb_non_st_state_refs_of' =
  st_tcb_at_tcb_non_st_state_refs_of[simplified pred_tcb_at_eq_commute]

lemma sym_refs_insert_delete:
  "sym_refs (refs(p := refs_p))
    \<Longrightarrow> refs_p = insert (q,t) (refs p)
    \<Longrightarrow> refs_q = refs q - {(p, symreftype t)}
    \<Longrightarrow> (q,t) \<notin> refs p
    \<Longrightarrow> sym_refs (refs(q := refs_q))"
  by (erule delta_sym_refs; fastforce split: if_splits)

lemmas sym_refs_insert_delete' =
  sym_refs_insert_delete[simplified fun_upd_def]

lemma valid_objs_valid_ep:
  "\<lbrakk>kheap s ep_ptr = Some (Endpoint ep); valid_objs s\<rbrakk> \<Longrightarrow> valid_ep ep s"
  by (fastforce simp: valid_objs_def valid_obj_def valid_ep_def)

lemma blocked_cancel_ipc_invs:
  "\<lbrace>\<lambda>s. invs s
        \<and> st_tcb_at ((=) st) t s
        \<and> (\<exists>ep. (\<exists>sender_data. st = BlockedOnSend ep sender_data \<and> r = None)
                \<or> (\<exists>rcv_data. st = BlockedOnReceive ep r rcv_data))\<rbrace>
   blocked_cancel_ipc st t r
   \<lbrace>\<lambda>_. invs\<rbrace>"
  supply if_split[split del] reply_unlink_tcb_iflive[wp del]
  apply (simp add: blocked_cancel_ipc_def tcb_ep_dequeue_def)
  apply (rule bind_wp[OF _ gbi_ep_sp])
  apply (clarsimp simp: bind_assoc)
  apply (rule bind_wp[OF _ get_simple_ko_sp], rename_tac ep)
  apply (rule bind_wp[OF _ assert_sp])
  apply clarsimp
  apply (rule_tac P'1="valid_ep ep" in hoare_pre_add[THEN iffD2])
   apply (fastforce dest: valid_objs_valid_ep simp: obj_at_def)
  apply (rule_tac S="(\<exists>rcv_data. st = BlockedOnReceive epptr r rcv_data)
                     \<or> r = None \<and> (\<exists>sender_data. st = BlockedOnSend epptr sender_data)"
           in hoare_gen_asm_spec, fastforce)
  apply (rule_tac S="ep \<noteq> IdleEP \<and> t \<noteq> epptr" in hoare_gen_asm_spec)
   apply (fastforce simp: st_tcb_at_def obj_at_def valid_ep_def split: endpoint.splits)
  apply (rule_tac Q'="\<lambda>_ s. ko_at (Endpoint (case removeAll t (ep_queue ep)
                                              of [] \<Rightarrow> IdleEP
                                                | a # list \<Rightarrow> update_ep_queue ep (removeAll t (ep_queue ep)) True))
                                 epptr s
                            \<and> st_tcb_at (\<lambda>st'. st' = st) t s
                            \<and> t \<noteq> idle_thread s
                            \<and> distinct (ep_queue ep)
                            \<and> sym_refs ((state_refs_of s)(epptr := ep_q_refs_of ep))
                            \<and> sym_refs (state_hyp_refs_of s)
                            \<and> all_invs_but_sym_refs s"
               in bind_wp_fwd)
   apply (wpsimp wp: set_simple_ko_at valid_irq_node_typ)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def pred_tcb_at_eq_commute)
   apply (rule conjI, clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
   apply (frule (1) if_live_then_nonz_capD; clarsimp simp: live_def)
   apply (simp add: ep_redux_simps2 st_tcb_at_tcb_non_st_state_refs_of cong: if_cong)
   apply (rule_tac V="distinct (ep_queue ep) \<and> (\<forall>t \<in> set (ep_queue ep). tcb_at t s)" in revcut_rl)
    apply (clarsimp simp: valid_ep_def split: endpoint.splits)
   apply (clarsimp simp: removeAll_filter_not_eq)
   apply (erule rsubst[of sym_refs "state_refs_of s" for s], rule ext)
   apply (clarsimp split: if_splits simp: obj_at_def state_refs_of_def)
  apply clarsimp
  apply (cases r; clarsimp)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def fun_upd_def
                   wp: sts_valid_replies sts_only_idle valid_irq_node_typ sts_fault_tcbs_valid_states)
   apply (rule conjI, clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp, fastforce+)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (erule delta_sym_refs)
    apply (case_tac ep;
           clarsimp simp: removeAll_filter_not_eq state_refs_of_def ep_redux_simps2 get_refs_def2
                   split: if_splits list.splits;
           metis (no_types, lifting) cons_set_intro list.set_intros(2) mem_Collect_eq set_filter)
   apply (case_tac "filter ((\<noteq>) t) (ep_queue ep)"; clarsimp)
    apply (case_tac ep;
           fastforce simp: removeAll_filter_not_eq state_refs_of_def filter_empty_conv get_refs_def2
                    split: if_splits)
   apply (prop_tac "t \<notin> set (filter ((\<noteq>) t) (ep_queue ep))")
    apply (smt (verit, best) filter_id_conv removeAll_filter_not removeAll_filter_not_eq)
   apply (prop_tac "y \<in> set (ep_queue ep) \<and> y \<noteq> t \<longrightarrow> y \<in> set (filter ((\<noteq>) t) (ep_queue ep))")
    apply (fastforce dest: in_filter_neq)
   subgoal for epptr ep s tcb x y tp head tail
     by (case_tac ep;
         clarsimp simp: removeAll_filter_not_eq state_refs_of_def ep_redux_simps2
                        tcb_st_refs_of_def refs_of_def get_refs_def2
                 split: if_splits list.splits option.splits kernel_object.splits
                        thread_state.splits)
  apply (rule bind_wp[where Q'="\<lambda>rv s. st_tcb_at inactive t s \<and> invs s"])
   apply (wpsimp wp: sts_invs_minor)
   apply (fastforce simp: pred_tcb_at_def obj_at_def valid_idle_def dest!: invs_valid_idle)
  apply (rename_tac r_ptr rcv_data)
  apply (rule hoare_vcg_conj_lift[where P=P and P'=P for P, simplified])
   apply (wpsimp wp: reply_unlink_tcb_st_tcb_at)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: reply_unlink_tcb_refs_of reply_unlink_tcb_valid_replies
                      reply_unlink_tcb_iflive)
  apply (rule conjI)
   apply (clarsimp simp: sym_refs_def[of "(state_refs_of _)(_ := _)"])
   apply (drule_tac x=t in spec)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (drule_tac x="(r_ptr, TCBReply)" in bspec)
    apply (clarsimp simp: state_refs_of_def get_refs_def2)
   apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp+)
  apply (clarsimp simp: st_tcb_at_tcb_non_st_state_refs_of' cong: if_cong)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rule_tac V="ep = RecvEP (ep_queue ep)" in revcut_rl)
   apply (rule_tac V="(t, EPRecv) \<in> ((state_refs_of s)(epptr := ep_q_refs_of ep)) epptr" in revcut_rl,
          erule sym_refsE, clarsimp simp: state_refs_of_def, clarsimp)
   apply (case_tac ep; clarsimp)
  apply (rule_tac V="state_refs_of s epptr = ep_q_refs_of ep - {(t, EPRecv)}" in revcut_rl)
   apply (clarsimp simp: state_refs_of_def ep_redux_simps2 Times_Diff_distrib1)
   apply (case_tac ep; fastforce)
  by (erule delta_sym_refs;
      clarsimp split: if_splits;
      fastforce simp: state_refs_of_def get_refs_def2)

lemma cancel_signal_invs:
  "\<lbrace>invs and st_tcb_at ((=) (BlockedOnNotification ntfn)) t\<rbrace>
   cancel_signal t ntfn
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: cancel_signal_def tcb_ntfn_dequeue_def
                   bind_assoc invs_def valid_state_def valid_pspace_def )
  apply (rule bind_wp [OF _ get_simple_ko_sp], rename_tac notification)
  apply (rule bind_wp [OF _ assert_sp])
  apply (case_tac "ntfn_obj notification", simp_all)[1]
  apply (rule hoare_pre)
   apply (wp set_simple_ko_valid_objs valid_irq_node_typ sts_only_idle
             sts_valid_replies hoare_vcg_all_lift hoare_vcg_imp_lift sts_fault_tcbs_valid_states
           | simp add: refs_of_ntfn_def
           | wpc)+
  apply (clarsimp simp: refs_of_ntfn_def ep_redux_simps cong: list.case_cong if_cong)
  apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def live_ntfn_def)+)
  apply (frule ko_at_state_refs_ofD)
  apply (frule st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (case_tac notification)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: removeAll_filter_not_eq)
  apply (rule conjI)
   apply (clarsimp split:option.split)
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp;
          clarsimp simp: is_blocked_thread_state_defs)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)+
   apply (fastforce dest: refs_in_get_refs symreftype_inverse')
  apply (fastforce simp: obj_at_def is_ntfn idle_not_queued
                   dest: idle_only_sc_refs elim: pred_tcb_weakenE)
  done

crunch reply_pop, break_reply_chain_at
  for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)"
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps ignore: set_simple_ko)

crunch reply_unlink_tcb
  for reply_at[wp]: "reply_at reply_ptr"
  (wp: crunch_wps)

crunch test_reschedule, get_sc_obj_ref
  for hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_idle[wp]: valid_idle
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and only_idle[wp]: only_idle
  and valid_arch_state[wp]: valid_arch_state

lemma sched_context_donate_hyp_refs_of [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def wp: get_sched_context_wp)

lemma sched_context_donate_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> tp \<noteq> idle_thread s \<and>
        sc_tcb_sc_at (\<lambda>x. x \<noteq> Some (idle_thread s)) scp s\<rbrace>
   sched_context_donate scp tp \<lbrace>\<lambda>s. valid_idle\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def sc_tcb_sc_at_def
                  wp: update_sched_context_valid_idle)
  apply (auto simp: valid_idle_def obj_at_def)
  done

crunch sched_context_donate
  for only_idle[wp]: only_idle
  and valid_arch_state[wp]: valid_arch_state
  and valid_irq_states[wp]: valid_irq_states
  and valid_machine_state[wp]: valid_machine_state
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_global_objs[wp]: valid_global_objs
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_asid_map[wp]: valid_asid_map
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and arch_tcb_at[wp]: "\<lambda>s. P' (arch_tcb_at P t s)"
  and valid_cur_fpu[wp]: valid_cur_fpu
  (ignore: set_object thread_set wp: crunch_wps simp: crunch_simps)

lemma sched_context_donate_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_irq_node\<rbrace>"
  by (wp valid_irq_node_typ)

lemma restart_thread_if_no_fault_fault_tcbs_valid_states[wp]:
  "\<lbrace>fault_tcbs_valid_states\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>_. fault_tcbs_valid_states\<rbrace>"
  apply (simp add: restart_thread_if_no_fault_def)
  apply (wpsimp wp: sts_fault_tcbs_valid_states thread_get_wp')+
  apply (auto simp: pred_tcb_at_def obj_at_def)
  done

lemma break_reply_chain_at_valid_idle[wp]:
  "break_reply_chain_at reply_ptr \<lbrace>valid_idle\<rbrace>"
  unfolding break_reply_chain_at_def
  apply (wpsimp wp: update_sched_context_valid_idle get_sk_obj_ref_wp)
  apply (clarsimp simp: valid_idle_def obj_at_def)
  apply (fastforce dest: sc_with_reply_SomeD)
  done

crunch reply_pop
  for valid_idle[wp]: valid_idle
  (wp: crunch_wps)

crunch reply_pop, break_reply_chain_at, restart_thread_if_no_fault
  for cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and only_idle[wp]: only_idle
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_arch_state[wp]: valid_arch_state
  and valid_asid_map[wp]: valid_asid_map
  and valid_global_objs[wp]: valid_global_objs
  and valid_global_refs[wp]: valid_global_refs
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and valid_ioc[wp]: valid_ioc
  and fault_tcbs_valid_states[wp]: fault_tcbs_valid_states
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_irq_node[wp]: valid_irq_node
  and valid_irq_states[wp]: valid_irq_states
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and valid_machine_state[wp]: valid_machine_state
  and valid_mdb[wp]: valid_mdb
  and valid_vspace_objs[wp]: valid_vspace_objs
  and zombies_final[wp]: zombies_final
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and valid_cur_fpu[wp]: valid_cur_fpu
  (wp: get_simple_ko_wp valid_irq_node_typ crunch_wps hoare_vcg_all_lift sts_only_idle
       valid_cur_fpu_lift)

crunch reply_pop, break_reply_chain_at
  for sc_at[wp]: "sc_at sc_ptr"
  (wp: crunch_wps)

lemma reply_unlink_tcb_sc_tcb_sc_at [wp]:
  "\<lbrace>\<lambda>s. Q (sc_tcb_sc_at (P (idle_thread s)) scp' s)\<rbrace>
   reply_unlink_tcb t rp
   \<lbrace>\<lambda>_ s. Q (sc_tcb_sc_at (P (idle_thread s)) scp' s)\<rbrace>"
  apply (rule hoare_lift_Pf[where f=idle_thread, rotated], wp)
  by (wpsimp simp: reply_unlink_tcb_def wp: gts_wp get_simple_ko_wp)

lemma sc_tcb_not_idle_thread_helper:
  "sc_tcb sc = Some tp \<Longrightarrow>
   kheap s scp = Some (SchedContext sc n) \<Longrightarrow>
   sym_refs (state_refs_of s) \<Longrightarrow>
   (scp, TCBSchedContext) \<in> state_refs_of s tp"
  by (fastforce simp: state_refs_of_def elim!: sym_refsE)

lemma sc_tcb_not_idle_thread:
  "kheap s scp = Some (SchedContext sc n) \<Longrightarrow>
   scp \<noteq> idle_sc_ptr \<Longrightarrow>
   sym_refs (state_refs_of s) \<Longrightarrow>
   valid_global_refs s \<Longrightarrow>
   valid_objs s \<Longrightarrow>
   if_live_then_nonz_cap s \<Longrightarrow>
   sc_tcb sc \<noteq> Some (idle_thread s)"
  apply (frule (1) idle_no_ex_cap)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_sched_context_def is_tcb obj_at_def)
  apply (fastforce simp: state_refs_of_def live_def
                  dest!: sc_tcb_not_idle_thread_helper if_live_then_nonz_capD2)
  done

lemma thread_not_idle_implies_sc_not_idle_helper:
  "tcb_sched_context tcb = Some scp \<Longrightarrow>
   kheap s tp = Some (TCB tcb) \<Longrightarrow>
   sym_refs (state_refs_of s) \<Longrightarrow>
   (tp, SCTcb) \<in> state_refs_of s scp"
  by (fastforce simp: state_refs_of_def elim!: sym_refsE)

lemma thread_not_idle_implies_sc_not_idle:
  "kheap s tp = Some (TCB tcb) \<Longrightarrow>
   tp \<noteq> idle_thread_ptr \<Longrightarrow> \<comment> \<open>idle_thread s\<close>
   sym_refs (state_refs_of s) \<Longrightarrow>
   valid_global_refs s \<Longrightarrow>
   valid_objs s \<Longrightarrow>
   valid_idle s \<Longrightarrow>
   if_live_then_nonz_cap s \<Longrightarrow>
   tcb_sched_context tcb \<noteq> Some idle_sc_ptr"
  apply (frule (1) idle_sc_no_ex_cap)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def is_sc_obj_def obj_at_def)
  apply (case_tac ko; clarsimp)
  apply (drule (2) thread_not_idle_implies_sc_not_idle_helper)
  apply (drule (1) if_live_then_nonz_capD2[where p=idle_sc_ptr])
   apply (fastforce simp: state_refs_of_def live_def pred_tcb_at_def obj_at_def valid_idle_def
                          get_refs_def2
                   dest!: thread_not_idle_implies_sc_not_idle_helper if_live_then_nonz_capD2)
  apply fastforce
  done

lemma reply_tcb_not_idle_thread:
  "kheap s reply = Some (Reply r) \<Longrightarrow>
   sym_refs (state_refs_of s) \<Longrightarrow>
   valid_global_refs s \<Longrightarrow>
   valid_objs s \<Longrightarrow>
   if_live_then_nonz_cap s \<Longrightarrow>
   reply_tcb r \<noteq> Some (idle_thread s)"
  apply (frule (1) idle_no_ex_cap)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_reply_def is_tcb obj_at_def)
  apply (fastforce simp: state_refs_of_def live_def
                  dest!: reply_tcb_not_idle_thread_helper if_live_then_nonz_capD2)
  done

lemma sym_refs_reply_sc_reply_at:
  "\<lbrakk>sym_refs (state_refs_of s); sc_replies_sc_at ((=) (reply_ptr # list)) sc_ptr s\<rbrakk>
   \<Longrightarrow> reply_sc_reply_at ((=) (Some sc_ptr)) reply_ptr s"
  apply (subgoal_tac "(sc_ptr, ReplySchedContext) \<in> state_refs_of s reply_ptr")
   apply (clarsimp simp: state_refs_of_def split: option.splits)
   apply (rename_tac ko, case_tac ko;
          clarsimp simp: get_refs_def reply_sc_reply_at_def obj_at_def split: option.splits)
  apply (fastforce elim!: sym_refsE
                    simp: sc_replies_sc_at_def obj_at_def state_refs_of_def get_refs_def
                   split: option.splits)
  done

lemma reply_not_head_reply_sc_None:
  "\<lbrakk>valid_replies s; sc_replies_sc_at (\<lambda>rs. reply_ptr \<in> set rs \<and> reply_ptr \<noteq> hd rs) sc_ptr s;
    sym_refs (state_refs_of s); reply_at reply_ptr s\<rbrakk>
   \<Longrightarrow> reply_sc_reply_at ((=) None) reply_ptr s"
  apply (clarsimp simp: reply_at_ppred_def obj_at_def is_reply)
  apply (rule sym)
  apply (rule ccontr)
  apply clarsimp
  apply (rename_tac sc_ptr')
  apply (frule_tac sc_ptr=sc_ptr' in sym_refs_sc_replies_sc_at[where reply_ptr=reply_ptr])
   apply (clarsimp simp: reply_at_ppred_def obj_at_def)
  apply (frule valid_replies_sc_replies_unique[where r=reply_ptr])
   apply (force simp: sc_at_ppred_def obj_at_def)
  apply (clarsimp simp: sc_at_ppred_def obj_at_def)
  apply (metis list.sel(1) Structures_A.kernel_object.inject(5) option.simps(1) cons_set_intro)
  done

lemma sc_with_reply_None_reply_sc_reply_at:
  "\<lbrakk>sc_with_reply rp s = None; reply_at rp s; sym_refs (state_refs_of s); valid_replies s\<rbrakk>
   \<Longrightarrow> reply_sc_reply_at ((=) None) rp s"
  apply (rule ccontr, clarsimp simp: obj_at_def reply_sc_reply_at_def is_reply)
  apply (drule not_sym, clarsimp)
  apply (rename_tac sc_ptr)
  apply (drule sym_refs_sc_replies_sc_at)
   apply (fastforce simp: obj_at_def reply_sc_reply_at_def)
  apply (drule_tac sc=sc_ptr in valid_replies_sc_with_reply_None, simp)
  apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  apply (metis list.set_intros(1))
  done

lemma reply_pop_sym_refs:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s \<and> valid_replies s
        \<and> sc_with_reply reply_ptr s = Some sc_ptr\<rbrace>
   reply_pop reply_ptr sc_ptr
   \<lbrace>\<lambda>_ s. sym_refs (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: reply_pop_def liftM_def)
  apply (rule bind_wp[OF _ get_sched_context_sp], rename_tac sc)
  apply (rule bind_wp[OF _ assert_sp])
  apply (case_tac "tl (sc_replies sc)")
   apply (wpsimp wp: update_sched_context_refs_of_update update_reply_wp)
   apply (frule_tac reply_ptr=reply_ptr
                and list="tl (sc_replies sc)"
                and sc_ptr=sc_ptr
                 in sym_refs_reply_sc_reply_at)
    apply (case_tac "sc_replies sc"; clarsimp simp: sc_at_ppred_def obj_at_def)
   apply (fastforce elim!: delta_sym_refs
                     simp: reply_at_ppred_def obj_at_def in_state_refs_of_iff get_refs_def2
                    split: if_splits)
  \<comment> \<open>the tail of the reply stack is not empty\<close>
  apply ((wpsimp wp: update_sched_context_refs_of_update | wpsimp wp: update_reply_wp)+)[1]
  apply (frule reply_not_head_reply_sc_None; fastforce?)
    apply (case_tac "sc_replies sc";
           force simp: sc_at_ppred_def obj_at_def valid_obj_def valid_sched_context_def)
   apply (case_tac "sc_replies sc"; force simp: obj_at_def valid_obj_def valid_sched_context_def)
  apply (clarsimp simp: reply_at_ppred_def obj_at_def)
  apply (intro conjI impI)
   apply fastforce
  apply (erule delta_sym_refs;
         clarsimp simp: in_state_refs_of_iff split: if_splits;
         force simp: get_refs_def2 refs_of_def sc_with_reply_def2
              split: if_splits kernel_object.splits)
  done

lemma break_reply_chain_at_sym_refs:
  "break_reply_chain_at reply_ptr \<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace>"
  unfolding break_reply_chain_at_def
  apply (wpsimp wp: update_sched_context_refs_of_update hoare_vcg_if_lift2)
  apply (frule sym_refs_reply_sc_reply_at)
   apply (fastforce intro!: list.collapse
                      dest: sc_with_reply_SomeD
                      simp: sc_at_ppred_def obj_at_def)
  apply (clarsimp simp: reply_at_ppred_def obj_at_def)
  by (fastforce elim!: delta_sym_refs
                 simp: takeWhile_eq_Cons_iff in_state_refs_of_iff get_refs_def2
                split: if_splits)

crunch test_reschedule
 for refs_of[wp]: "\<lambda>s. P (state_refs_of s)"

lemma sched_context_donate_refs_of:
  "\<lbrace>\<lambda>s. tcb_at tp s \<and>
        P (\<lambda>a. if a = scp then
                 {(tp, SCTcb)} \<union> {x \<in> state_refs_of s a. snd x \<noteq> SCTcb}
               else (if a = tp then
                       {(scp, TCBSchedContext)} \<union> {x \<in> state_refs_of s a. snd x \<noteq> TCBSchedContext}
                     else (if sc_tcb_sc_at (\<lambda>x. x = Some a) scp s then
                             {x \<in> state_refs_of s a. snd x \<noteq> TCBSchedContext}
                           else state_refs_of s a)))\<rbrace>
   sched_context_donate scp tp
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
                      get_object_def is_tcb obj_at_def sc_tcb_sc_at_def)
  apply safe
           apply clarsimp+
       apply (erule rsubst[where P = P], rule ext, fastforce simp: sc_tcb_sc_at_def obj_at_def)
      apply (erule rsubst[where P = P], rule ext, fastforce simp: sc_tcb_sc_at_def obj_at_def)
     apply (erule rsubst[where P = P], rule ext,
            fastforce simp: sc_tcb_sc_at_def obj_at_def is_tcb state_refs_of_def get_refs_def2)
     apply (erule rsubst[where P = P], rule ext,
            fastforce simp: sc_tcb_sc_at_def obj_at_def is_tcb state_refs_of_def get_refs_def2)
  apply (erule rsubst[where P = P], rule ext, fastforce simp: sc_tcb_sc_at_def obj_at_def is_tcb)+
  done

lemma replies_blocked_inj:
  "sym_refs (state_refs_of s) \<Longrightarrow> inj_on fst (replies_blocked s)"
  apply (clarsimp simp: inj_on_def replies_blocked_def pred_tcb_at_def obj_at_def
         , rename_tac r t t' tcb tcb')
  apply (frule_tac x=t and y=r and tp=ReplyTCB in sym_refsE, fastforce simp: state_refs_of_def)
  apply (drule_tac x=t' and y=r and tp=ReplyTCB in sym_refsE, fastforce simp: state_refs_of_def)
  by (fastforce simp: state_refs_of_def refs_of_rev split: option.splits)

lemma replies_blocked_upd_tcb_st_valid_replies:
  assumes "valid_replies_2 with_sc blocked"
  assumes "\<forall>r. r \<in> fst ` with_sc \<and> (r,t) \<in> blocked \<longrightarrow> st = BlockedOnReply r"
  shows "valid_replies_2 with_sc (replies_blocked_upd_tcb_st st t blocked)"
  using assms by (fastforce simp: valid_replies_defs replies_blocked_upd_tcb_st_def image_def)

lemma replies_blocked_upd_tcb_st_valid_replies_not_blocked:
  assumes "valid_replies_2 with_sc blocked"
  assumes "\<forall>r. (r,t) \<notin> blocked"
  shows "valid_replies_2 with_sc (replies_blocked_upd_tcb_st st t blocked)"
  using assms by (fastforce simp: valid_replies_defs replies_blocked_upd_tcb_st_def image_def)

lemma reply_unlink_tcb_assume_asserts:
  assumes "\<lbrace> P and reply_tcb_reply_at (\<lambda>t'. t' = Some t) r
               and st_tcb_at (\<lambda>st. reply_object st = Some r) t \<rbrace>
            reply_unlink_tcb t r
           \<lbrace> Q \<rbrace>"
  shows "\<lbrace> P \<rbrace> reply_unlink_tcb t r \<lbrace> Q \<rbrace>"
  apply (rule hoare_strengthen_pre[OF _ assms[unfolded pred_conj_assoc[symmetric]]])
  apply (simp add: reply_unlink_tcb_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule bind_wp[OF _ gts_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule hoare_weaken_pre[OF hoare_vcg_prop])
  by (auto simp: reply_tcb_reply_at_def pred_tcb_at_def obj_at_def)

text \<open>@{term reply_unlink_tcb} does not preserve @{term invs} when the
      associated thread is @{term BlockedOnReceive}, because it drops a
      reference to an endpoint. For that case, rebalancing @{term sym_refs}
      happens elsewhere.\<close>
lemma reply_unlink_tcb_invs_BlockedOnReply':
  "\<lbrace> \<lambda>s. invs s \<and> r \<notin> fst ` replies_with_sc s
                \<and> (\<exists>t'. st_tcb_at ((=) (BlockedOnReply r)) t' s) \<rbrace>
    reply_unlink_tcb t r
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  apply (rule reply_unlink_tcb_assume_asserts)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def pred_tcb_at_eq_commute
                  wp: reply_unlink_tcb_refs_of reply_unlink_tcb_valid_replies)
  apply (rule_tac V="t'=t" in revcut_rl)
   apply (subgoal_tac "(t', ReplyTCB) \<in> state_refs_of s r"
          , fastforce simp: in_state_refs_of_iff refs_of_rev reply_tcb_reply_at_def obj_at_def)
   apply (erule sym_refsE, fastforce simp: in_state_refs_of_iff pred_tcb_at_def obj_at_def refs_of_rev)
  apply (rule conjI)
   apply (erule replies_blocked_upd_tcb_st_valid_replies)
   apply (force simp: replies_with_sc_def replies_blocked_def pred_tcb_at_def obj_at_def)
  apply (clarsimp, rule delta_sym_refs, assumption)
   apply (clarsimp split: if_splits)
  by (clarsimp simp: pred_tcb_at_def obj_at_def in_state_refs_of_iff get_refs_def2
              split: if_splits)

lemma reply_unlink_tcb_invs_BlockedOnReply:
  "\<lbrace> \<lambda>s. invs s
         \<and> rptr \<notin> fst ` replies_with_sc s
         \<and> rptr \<in> fst ` replies_blocked s \<rbrace>
    reply_unlink_tcb t rptr
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  by (wpsimp wp: reply_unlink_tcb_invs_BlockedOnReply' simp: pred_tcb_at_eq_commute)
     (fastforce simp: replies_with_sc_def replies_blocked_def image_iff)

lemma reply_pop_valid_replies[wp]:
  "reply_pop reply_ptr sc_ptr \<lbrace>valid_replies\<rbrace>"
  unfolding reply_pop_def
  apply (wpsimp wp: update_sc_replies_valid_replies get_simple_ko_wp hoare_vcg_all_lift
                    hoare_vcg_imp_lift'
         | wpsimp wp: update_reply_wp)+
  apply (intro conjI impI allI;
         erule replies_with_sc_upd_replies_subset_valid_replies_2;
         clarsimp simp: sc_replies_sc_at_def obj_at_def;
         metis list.sel(2) list.set_sel(2))
  done

lemma break_reply_chain_at_valid_replies[wp]:
  "break_reply_chain_at reply_ptr \<lbrace>valid_replies\<rbrace>"
  apply (wpsimp simp: break_reply_chain_at_def
                  wp: update_sc_replies_valid_replies get_sk_obj_ref_wp)
  apply (erule replies_with_sc_upd_replies_subset_valid_replies_2;
         clarsimp simp: sc_replies_sc_at_def obj_at_def
                 dest!: set_takeWhileD)
  done

lemma get_reply_sp:
  "\<lbrace>P\<rbrace> get_reply rptr
   \<lbrace> \<lambda>r s. P s \<and> (\<exists>n. ko_at (Reply r) rptr s)\<rbrace>"
  apply (simp add: get_simple_ko_def)
  apply (rule bind_wp_fwd)
   apply (rule get_object_sp)
  apply wpsimp
  done

crunch reply_pop, break_reply_chain_at
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps ignore: update_sched_context)

crunch reply_pop, break_reply_chain_at
  for cur_sc_tcb[wp]: cur_sc_tcb
  (wp: crunch_wps ignore: update_sched_context)

lemma reply_pop_invs[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> sc_with_reply reply_ptr s = Some sc_ptr\<rbrace>
   reply_pop reply_ptr sc_ptr \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def pred_conj_def)
  apply (intro hoare_vcg_conj_lift_pre_fix; (solves \<open>wpsimp wp: reply_pop_sym_refs\<close>)?)
  \<comment> \<open>only valid_idle remains\<close>
  apply (clarsimp simp: reply_pop_def)
  apply (wpsimp wp: get_simple_ko_wp update_sched_context_valid_idle hoare_vcg_all_lift
         | wp (once) hoare_drop_imps)+
  apply (fastforce simp: valid_idle_def obj_at_def)
  done

lemma break_reply_chain_at_invs[wp]:
  "break_reply_chain_at reply_ptr \<lbrace>invs\<rbrace>"
  by (wpsimp wp: break_reply_chain_at_sym_refs simp: invs_def valid_state_def valid_pspace_def)

lemma set_thread_state_act_inv:
  "(\<And>s. P (s\<lparr>scheduler_action := choose_new_thread\<rparr>) = P s) \<Longrightarrow> set_thread_state_act t \<lbrace>P\<rbrace>"
  by (wpsimp simp: set_thread_state_act_def set_scheduler_action_def)

lemma state_refs_of_scheduler_action_kheap[simp]:
  "state_refs_of (s\<lparr>scheduler_action := sa, kheap := h\<rparr>) = state_refs_of (s\<lparr>kheap := h\<rparr>)"
  by (simp add: state_refs_of_def)

lemma sc_tcb_sc_at_scheduler_action_kheap[simp]:
  "sc_tcb_sc_at a b (s\<lparr>scheduler_action := sa, kheap := h\<rparr>) = sc_tcb_sc_at a b (s\<lparr>kheap := h\<rparr>)"
  by (simp add: sc_tcb_sc_at_def obj_at_def)

lemma sched_context_donate_sym_refs:
  "\<lbrace>\<lambda>s. valid_objs s \<and> sym_refs (state_refs_of s) \<and> tcb_at tcb_ptr s \<and>
        bound_sc_tcb_at ((=) None) tcb_ptr s\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: sched_context_donate_def)
  apply (rule bind_wp[OF _ gsct_sp])
  apply (simp add: when_def)
  apply (intro conjI)
   apply wpsimp
   apply (intro conjI, clarsimp)
    apply (intro conjI)
     apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_tcb)
    apply clarsimp
    apply (rule delta_sym_refs, assumption)
     apply (clarsimp split: if_splits, fastforce)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_tcb split: if_splits)
   apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_tcb)
   apply (rule conjI; clarsimp)
    apply (rule delta_sym_refs, assumption)
     apply (clarsimp split: if_splits)
    apply (clarsimp split: if_splits)
     apply (clarsimp simp: obj_at_def state_refs_of_def get_refs_def2 pred_tcb_at_def)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def state_refs_of_def get_refs_def2)
   apply (intro conjI)
    apply (fastforce simp: sc_tcb_sc_at_def valid_obj_def valid_sched_context_def
                           valid_bound_obj_def is_tcb obj_at_def state_refs_of_def get_refs_def2
                    split: option.splits)
   apply clarsimp
   apply (rule delta_sym_refs, assumption)
    apply (clarsimp split: if_splits)
   apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
   apply (clarsimp split: if_splits)
     apply (clarsimp simp: obj_at_def state_refs_of_def get_refs_def2 pred_tcb_at_def)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def state_refs_of_def get_refs_def2)
   apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply (fastforce simp: valid_obj_def valid_sched_context_def valid_bound_obj_def is_tcb
      obj_at_def get_refs_def2 state_refs_of_def
      split: option.splits)
  apply wpsimp
  apply (fastforce simp: sc_tcb_sc_at_def pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
      split: if_splits
      elim!: delta_sym_refs)
  done

lemma test_reschedule_valid_replies[wp]:
  "test_reschedule from_tptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: test_reschedule_def)

lemma sched_context_donate_valid_replies[wp]:
  "sched_context_donate sc_ptr tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: sched_context_donate_def wp: get_sc_obj_ref_wp)

lemma test_reschedule_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> test_reschedule from_tptr \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: test_reschedule_def)

lemma test_reschedule_cur_sc [wp]:
  "\<lbrace>\<lambda>s. P (cur_sc s)\<rbrace> test_reschedule from_tptr \<lbrace>\<lambda>rv s. P (cur_sc s)\<rbrace>"
  by (wpsimp simp: test_reschedule_def)

lemma test_reschedule_cur_thread_scheduler_action [wp]:
  "\<lbrace>\<lambda>s. from_tptr = cur_thread s \<or> scheduler_action s \<noteq> resume_cur_thread\<rbrace>
   test_reschedule from_tptr
   \<lbrace>\<lambda>rv s. scheduler_action s \<noteq> resume_cur_thread\<rbrace>"
  by (wpsimp simp: test_reschedule_def)

lemma sched_context_donate_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> sched_context_donate sc_ptr tcb_ptr \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  apply (simp add: sched_context_donate_def)
  apply (rule bind_wp[OF _ gsct_sp])
  apply (case_tac from_opt)
   apply (wpsimp simp: sc_tcb_sc_at_def obj_at_def cur_sc_tcb_def
                   wp: sc_tcb_update_cur_sc_tcb)
  apply (wpsimp wp: sc_tcb_update_cur_sc_tcb hoare_vcg_disj_lift
              simp: cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)
  done

lemma sched_context_donate_invs:
  "\<lbrace>\<lambda>s. invs s \<and> tcb_at tcb_ptr s \<and> ex_nonz_cap_to sc_ptr s \<and> ex_nonz_cap_to tcb_ptr s \<and>
        bound_sc_tcb_at ((=) None) tcb_ptr s \<and> sc_at sc_ptr s\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: sched_context_donate_sym_refs)
  apply (intro conjI)
   apply (clarsimp simp: idle_no_ex_cap)
  apply (thin_tac "tcb_at tcb_ptr s")
  apply (subgoal_tac "sc_tcb_sc_at (\<lambda>x. (\<forall>t. x = Some t \<longrightarrow> obj_at live t s)) sc_ptr s")
   apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def if_live_then_nonz_cap_def
                  dest!: idle_no_ex_cap)
  apply (clarsimp simp: is_sc_obj_def obj_at_def sc_tcb_sc_at_def)
  apply (subgoal_tac "sc_ptr \<noteq> idle_sc_ptr")
   apply (case_tac ko; simp)
   apply (frule (5) sc_tcb_not_idle_thread)
   apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply (fastforce simp: valid_obj_def valid_sched_context_def is_tcb obj_at_def
                          live_def)
  apply (fastforce dest!: idle_sc_no_ex_cap)
  done

crunch reply_pop, break_reply_chain_at
  for pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"
  (wp: crunch_wps)

lemma sc_replies_update_fst_replies_with_sc:
  "\<lbrace>\<lambda>s. ((r, sc) \<in> replies_with_sc s) \<and> (r \<notin> set k) \<and> valid_replies s\<rbrace>
   set_sc_obj_ref sc_replies_update sc k
   \<lbrace>\<lambda>rv s. r \<notin> fst ` replies_with_sc s\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def split: if_splits)
  apply (clarsimp simp: valid_replies_2_def inj_on_def)
  done

lemma update_sched_context_sc_replies_fst_replies_with_sc:
  "\<lbrace>\<lambda>s. ((r, sc) \<in> replies_with_sc s) \<and> sc_replies_sc_at (\<lambda>k. r \<notin> set (f k)) sc s \<and> valid_replies s\<rbrace>
   update_sched_context sc (sc_replies_update f)
   \<lbrace>\<lambda>rv s. r \<notin> fst ` replies_with_sc s\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def split: if_splits)
  apply (clarsimp simp: valid_replies_2_def inj_on_def)
  done

lemma reply_pop_fst_replies_with_sc:
  "\<lbrace>\<lambda>s. sc_replies_sc_at (\<lambda>l. distinct l \<and> l \<noteq> [] \<and> reply_ptr = hd l) sc_ptr s \<and> valid_replies s\<rbrace>
   reply_pop reply_ptr sc_ptr
   \<lbrace>\<lambda>_ s. reply_ptr \<notin> fst ` replies_with_sc s\<rbrace>"
  unfolding reply_pop_def
  apply (wpsimp wp: update_sched_context_sc_replies_fst_replies_with_sc
                    get_simple_ko_wp hoare_vcg_all_lift hoare_drop_imp)
  apply (rename_tac sc n)
  apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def
                 split: if_splits list.splits)
  apply (case_tac "sc_replies sc"; clarsimp)
  done

lemma break_reply_chain_at_replies_with_sc[wp]:
  "\<lbrace>valid_replies\<rbrace> break_reply_chain_at reply_ptr \<lbrace>\<lambda>_ s. reply_ptr \<notin> fst ` replies_with_sc s\<rbrace>"
  unfolding break_reply_chain_at_def
  apply (wpsimp wp: sc_replies_update_fst_replies_with_sc get_sk_obj_ref_wp
                    update_sched_context_sc_replies_fst_replies_with_sc get_simple_ko_wp)
  apply (fastforce dest: valid_replies_sc_with_reply_None' sc_with_reply_replies_with_sc
                         set_takeWhileD
                  intro: sc_replies_sc_at_ko_atI)
  done

lemma break_reply_chain_at_replies_with_sc_other:
  "\<lbrace>\<lambda>s. reply_ptr \<notin> fst ` replies_with_sc s \<and> reply_ptr \<noteq> reply_ptr'\<rbrace>
   break_reply_chain_at reply_ptr'
   \<lbrace>\<lambda>_ s. reply_ptr \<notin> fst ` replies_with_sc s\<rbrace>"
  unfolding break_reply_chain_at_def
  apply (wpsimp wp: update_sched_context_wp get_sk_obj_ref_wp)
  apply (clarsimp simp: sc_at_ppred_def obj_at_def replies_with_sc_def)
  apply (fastforce simp: image_Collect dest: set_takeWhileD split: if_splits)
  done

lemma update_reply_ko_at_sc[wp]:
  "update_reply f reply_ptr  \<lbrace>\<lambda>s. Q (ko_at (SchedContext sc n) sc_ptr s)\<rbrace>"
  apply (wpsimp wp: update_reply_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: obj_at_def)
  done

lemma reply_pop_not_fst_replies_blocked[wp]:
  "reply_pop reply_ptr sc_ptr \<lbrace>\<lambda>s. r \<notin> fst ` replies_blocked s\<rbrace>"
  unfolding reply_pop_def
  apply (wpsimp wp: get_simple_ko_wp update_sched_context_wp update_reply_wp)
  apply (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def image_Collect)
  done

lemma break_reply_chain_at_not_fst_replies_blocked[wp]:
  "break_reply_chain_at reply_ptr \<lbrace>\<lambda>s. r \<notin> fst ` replies_blocked s\<rbrace>"
  unfolding break_reply_chain_at_def
  apply (wpsimp wp: update_sched_context_wp get_sk_obj_ref_wp)
  apply (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def image_Collect split: if_splits)
  done

lemma fst_replies_blocked_strengthen:
  "(reply_tcb_reply_at (\<lambda>p. \<exists>tp. p = Some tp \<and>
                            st_tcb_at ((=) (BlockedOnReply r)) tp s) r s)
    \<Longrightarrow> (r \<in> fst ` replies_blocked s)"
  by (fastforce simp: replies_blocked_def reply_tcb_reply_at_def obj_at_def image_def
                      pred_tcb_at_eq_commute)

lemma update_sched_context_sc_replies_sc_at:
  "(\<And>sc. sc_replies (f sc) = sc_replies sc)
   \<Longrightarrow> update_sched_context sc_ptr' f \<lbrace>\<lambda>s. Q (sc_replies_sc_at P sc_ptr s)\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: sc_at_ppred_def obj_at_def)
  done

crunch reschedule_required, tcb_release_remove
  for sc_replies_sc_at[wp]: "\<lambda>s. Q (sc_replies_sc_at P sc_ptr s)"
  (wp: crunch_wps simp: crunch_simps)

lemma sched_context_donate_sc_replies_sc_at[wp]:
  "sched_context_donate sc_ptr' tcb_ptr \<lbrace>\<lambda>s. Q (sc_replies_sc_at P sc_ptr s)\<rbrace>"
  unfolding sched_context_donate_def test_reschedule_def
  apply (wpsimp wp: update_sched_context_sc_replies_sc_at simp: get_sc_obj_ref_def)
  done

lemma not_in_replies_with_sc_not_in_sc_replies_sc_at:
  "\<lbrakk>reply_ptr \<notin> fst ` replies_with_sc s\<rbrakk>
   \<Longrightarrow> \<not> sc_replies_sc_at (\<lambda>ls. reply_ptr \<in> set ls) sc_ptr s"
  by (force simp: replies_with_sc_def sc_at_ppred_def obj_at_def)

lemma reply_remove_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (\<exists>t. st_tcb_at ((=) (BlockedOnReply r)) t s)\<rbrace>
   reply_remove t r
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: reply_remove_def pred_tcb_at_eq_commute)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule bind_wp[OF _ gets_sp], rename_tac r_sc_opt)
  apply (rule bind_wp[OF reply_unlink_tcb_invs_BlockedOnReply'])
  apply (case_tac r_sc_opt; clarsimp)
   apply wpsimp
   apply (fastforce dest: valid_replies_sc_with_reply_None'
                    simp: pred_tcb_at_def obj_at_def)
  apply (rename_tac sc_ptr)
  apply (clarsimp simp: liftM_def)
  apply (rule bind_wp[OF _ get_sched_context_sp], rename_tac sc)
  apply (intro hoare_vcg_conj_lift_pre_fix)
    \<comment> \<open>invs conjunct\<close>
    apply (case_tac "r = hd (sc_replies sc)"; clarsimp)
     apply (wpsimp wp: sched_context_donate_invs thread_get_wp simp: get_tcb_obj_ref_def)
      apply (rule_tac Q'="\<lambda>_. invs and tcb_at t and sc_at sc_ptr
                              and ex_nonz_cap_to sc_ptr and ex_nonz_cap_to t"
                   in hoare_post_imp)
       apply (force simp: pred_tcb_at_def obj_at_def is_tcb)
      apply wpsimp
     apply (clarsimp simp: obj_at_def)
     apply (intro conjI)
        apply (fastforce dest: valid_objs_valid_reply[OF invs_valid_objs]
                         simp: valid_reply_def obj_at_def)
       apply (fastforce dest: sc_with_reply_Some_sc_at simp: obj_at_def)
      apply (fastforce dest: sc_with_reply_SomeD
                      intro: if_live_then_nonz_capD2
                       simp: live_def live_sc_def)
     apply (fastforce dest!: reply_tcb_not_idle_thread_helper
                      intro: if_live_then_nonz_capD2
                       simp: live_def state_refs_of_def get_refs_def2
                      split: option.splits kernel_object.splits)
    apply wpsimp
   apply (wpsimp wp: reply_pop_fst_replies_with_sc)
   apply (fastforce dest: valid_objs_valid_sched_context[OF invs_valid_objs] sc_with_reply_SomeD
                    simp: sc_at_ppred_def obj_at_def valid_sched_context_def)
  apply (wpsimp wp: hoare_vcg_ex_lift)
  apply (fastforce elim: st_tcb_weakenE)
  done

lemma sc_replies_update_valid_replies_cons:
  "\<lbrace>valid_replies
    and (sc_replies_sc_at ((=) sc_replies') sc_ptr)
    and (\<lambda>s. r_ptr \<in> fst ` replies_blocked s)
    and (\<lambda>s. r_ptr \<notin> fst ` replies_with_sc s)\<rbrace>
   set_sc_obj_ref sc_replies_update sc_ptr (r_ptr # sc_replies')
   \<lbrace>\<lambda>r. valid_replies \<rbrace>"
  apply (wpsimp wp: set_sc_replies_valid_replies)
  apply (clarsimp simp: replies_with_sc_upd_replies_def valid_replies_2_def)
  apply (intro conjI, clarsimp simp:)
   apply safe
       apply ((fastforce simp: image_def)+)[3]
    apply (subgoal_tac "a \<in> fst ` replies_with_sc s")
     apply (fastforce simp: image_def)
    apply (fastforce simp: image_def sc_replies_sc_at_def obj_at_def replies_with_sc_def)
   apply (fastforce simp: image_def)
  apply (clarsimp simp: inj_on_def)
  apply (case_tac "ba = sc_ptr"; case_tac "bb = sc_ptr"; simp)
    apply (elim disjE,
           fastforce simp: image_def,
           clarsimp simp: image_def sc_replies_sc_at_def obj_at_def replies_with_sc_def)
   apply (elim disjE,
          fastforce simp: image_def,
          clarsimp simp: image_def sc_replies_sc_at_def obj_at_def replies_with_sc_def)
  apply fastforce
  done

lemma sc_replies_update_replies_blocked:
  "ko_at (SchedContext sc n) scp s
   \<Longrightarrow> {(r, t). st_tcb_at (\<lambda>st. st = BlockedOnReply r) t
                          (s\<lparr>kheap := (kheap s)(scp \<mapsto> SchedContext (sc_replies_update f sc) n)\<rparr>)}
       = replies_blocked s"
  apply (clarsimp simp: replies_blocked_def pred_tcb_at_def obj_at_def)
  apply fastforce
  done

lemma break_reply_chain_at_replies_blocked[wp]:
  "break_reply_chain_at reply_ptr \<lbrace>\<lambda>s. P (replies_blocked s)\<rbrace>"
  by (wp replies_blocked_lift)

lemma reply_remove_tcb_invs:
  "reply_remove_tcb t r \<lbrace>invs\<rbrace>"
  apply (simp add: reply_remove_tcb_def)
  apply (wpsimp wp: reply_unlink_tcb_invs_BlockedOnReply break_reply_chain_at_replies_with_sc gts_wp)
  apply (fastforce elim: st_tcb_weakenE simp: replies_blocked_def image_def)
  done

lemma cancel_ipc_invs[wp]:
  "\<lbrace>invs\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_ipc_def)
  by (wpsimp wp: blocked_cancel_ipc_invs cancel_signal_invs reply_remove_tcb_invs
                 thread_set_no_change_tcb_state gts_wp
                 hoare_vcg_imp_lift hoare_vcg_all_lift ball_tcb_cap_casesI)

context IpcCancel_AI begin

lemma cancel_ipc_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> cancel_ipc p \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)


lemma cancel_ipc_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> cancel_ipc t \<lbrace>\<lambda>_. (cte_at p) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cte_at_typ)

end

crunch blocked_cancel_ipc, cancel_signal
  for valid_objs[wp]: valid_objs

lemma tcb_in_valid_state:
  "\<lbrakk> st_tcb_at P t s; valid_objs s \<rbrakk> \<Longrightarrow> \<exists>st. P st \<and> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def pred_tcb_at_def obj_at_def)
  apply (erule my_BallE, erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  apply blast
  done

lemma schedule_tcb_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> schedule_tcb tcb_ptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

crunch
  cancel_all_ipc, cancel_signal, cancel_all_signals, unbind_notification, unbind_notification,
  fast_finalise, sched_context_unbind_all_tcbs, sched_context_unbind_yield_from,
  sched_context_unbind_reply, sched_context_unbind_ntfn
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma sym_refs_bound_yt_tcb_at:
  "sym_refs (state_refs_of s) \<Longrightarrow> bound_yt_tcb_at ((=) (Some sc)) t s \<Longrightarrow>
   (t', SCYieldFrom) \<in> state_refs_of s sc \<Longrightarrow>  t' = t"
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (frule sym_refs_ko_atD[unfolded obj_at_def, simplified], assumption)
  apply (clarsimp simp: state_refs_of_def refs_of_rev split: option.splits)
  apply (erule_tac x = "(sc, TCBYieldTo)" in ballE)
   apply (auto simp: get_refs_def2)
  done

lemma as_user_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> as_user r f \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (wp set_object_valid_ioc_caps)
  apply (clarsimp simp: valid_ioc_def obj_at_def get_tcb_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: if_split_asm)
  done

crunch as_user
  for replies_with_sc[wp]: "\<lambda>s. P (replies_with_sc s)"
  and irq_states[wp]: "valid_irq_states"
  and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
  and pspace_respects_device_region[wp]: "pspace_respects_device_region"
  and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  and cur_sc_tcb[wp]: "cur_sc_tcb"
  (rule: pspace_in_kernel_window_atyp_lift as_user_wp_thread_set_helper
   simp: crunch_simps tcb_cap_cases_def)

declare as_user_only_idle[wp]

lemma as_user_replies_blocked[wp]:
  "as_user f t \<lbrace>\<lambda>s. P (replies_blocked s)\<rbrace>"
  unfolding replies_blocked_def
  by (rule hoare_vcg_set_pred_lift) wpsimp

lemma as_user_replies[wp]:
  "as_user f t \<lbrace>\<lambda>s. P (replies_with_sc s) (replies_blocked s)\<rbrace>"
  by (wp|wps)+

lemma blocked_cancel_ipc_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (simp add: blocked_cancel_ipc_def | wp)+

lemma cancel_signal_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> cancel_signal t ntfn \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (simp add: cancel_signal_def | wp)+

lemma reply_unlink_tcb_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def)

lemma reply_remove_tcb_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> reply_remove_tcb t r \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (wpsimp simp: reply_remove_tcb_def)

lemma sched_context_cancel_yield_to_invs:
  "sched_context_cancel_yield_to thread \<lbrace>invs\<rbrace>"
  apply (clarsimp simp: sched_context_cancel_yield_to_def)
  apply (rule bind_wp[OF _ gyt_sp])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: valid_irq_node_typ maybeM_wp update_sched_context_valid_idle)
  apply (intro conjI)
    apply (rule delta_sym_refs, assumption)
     apply (clarsimp split: if_splits)
    apply (clarsimp split: if_splits)
      apply ((fastforce simp: state_refs_of_def get_refs_def2 pred_tcb_at_def obj_at_def)+)[2]
    apply (clarsimp simp: sym_refs_bound_yt_tcb_at)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
   apply (subgoal_tac "tcb_yield_to tcb = Some idle_sc_ptr")
    apply (fastforce dest!: sym_ref_tcb_yt)
   apply fastforce
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma cancel_ipc_simple_except_awaiting_reply:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
   cancel_ipc t
   \<lbrace>\<lambda>_. st_tcb_at ((=) Running or (=) Inactive or (=) Restart or (=) IdleThreadState) t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule bind_wp[OF _ gts_sp])
  apply (case_tac state; simp)
         prefer 8
         apply ((wpsimp wp: thread_set_no_change_tcb_pred simp: st_tcb_at_def obj_at_def)+)[4]
     apply ((rule hoare_strengthen_post[where Q'="\<lambda>s. st_tcb_at ((=) Inactive) t"], wpsimp,
             clarsimp simp: st_tcb_at_def obj_at_def)+)[4]
  done

lemma cancel_ipc_no_refs:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace>
   cancel_ipc t
   \<lbrace>\<lambda>_. st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = {}) t\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule cancel_ipc_simple_except_awaiting_reply)
  apply (auto elim: st_tcb_weakenE)
  done

lemma suspend_invs[wp]:
  "\<lbrace>invs and K (t \<noteq> idle_thread_ptr)\<rbrace> suspend t \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding suspend_def
  apply (wpsimp wp: sts_invs_minor sched_context_cancel_yield_to_invs cancel_ipc_no_refs)
  apply (fastforce elim: st_tcb_weakenE
                   simp: invs_def valid_state_def only_idle_def valid_idle_def)
  done

context IpcCancel_AI begin

lemma suspend_typ_at [wp]:
  "\<lbrace>\<lambda>(s::'a state). P (typ_at T p s)\<rbrace> suspend t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: suspend_def sched_context_cancel_yield_to_def wp: hoare_drop_imps)


lemma suspend_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> suspend tcb \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)

lemma suspend_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> suspend t \<lbrace>\<lambda>rv. (tcb_at t')  :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

crunch blocked_cancel_ipc
 for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps maybeM_inv)

crunch cancel_signal
  for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps)

crunch reply_remove_tcb
 for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps)

locale delete_one_pre =
  fixes state_ext_type :: "('a :: state_ext) itself"
  assumes delete_one_cte_wp_at_preserved:
    "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
     \<lbrace>cte_wp_at P sl\<rbrace> (cap_delete_one sl' :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"

context delete_one_pre begin

lemma cancel_ipc_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (wpsimp wp: thread_set_cte_wp_at_trivial ball_tcb_cap_casesI hoare_drop_imps)
  done

lemma suspend_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (suspend tcb :: (unit,'a) s_monad) \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>"
  by (simp add: suspend_def sched_context_cancel_yield_to_def)
     (wpsimp wp: cancel_ipc_cte_wp_at_preserved hoare_drop_imps)

end

crunch empty_slot
 for pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"

lemma set_thread_state_bound_tcb_at[wp]:
  "set_thread_state p ts \<lbrace>bound_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma reply_unlink_tcb_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t'\<rbrace> reply_unlink_tcb t rptr \<lbrace>\<lambda>_. bound_tcb_at P t'\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def wp: hoare_drop_imp)

crunch cancel_all_ipc, is_final_cap, get_cap, tcb_release_remove
 for bound_tcb_at[wp]: "bound_tcb_at P t"
  (wp: mapM_x_wp_inv crunch_wps simp: crunch_simps)

lemma in_release_queue_ready_queues_update[simp]:
  "in_release_queue t (ready_queues_update f s) = in_release_queue t s"
  by (clarsimp simp: in_release_queue_def)

lemma set_tcb_sc_bound_tcb_at [wp]:
  "set_tcb_obj_ref tcb_sched_context_update ref new \<lbrace>bound_tcb_at P t\<rbrace>"
  by (wpsimp wp: thread_set_no_change_tcb_pred)

lemma sched_context_donate_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> sched_context_donate scptr tcbptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def test_reschedule_def
               wp: weak_if_wp hoare_drop_imp)

lemma reply_remove_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t'\<rbrace> reply_remove t rptr \<lbrace>\<lambda>_. bound_tcb_at P t'\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: get_simple_ko_wp)

lemma reply_remove_tcb_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t'\<rbrace> reply_remove_tcb t rptr \<lbrace>\<lambda>_. bound_tcb_at P t'\<rbrace>"
  by (wpsimp simp: reply_remove_tcb_def wp: hoare_drop_imps)

crunch cancel_ipc
  for bound_tcb_at[wp]: "bound_tcb_at P t"
  (wp: assert_inv thread_set_no_change_tcb_pred)

lemma fast_finalise_bound_tcb_at:
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>tt r. cap = ReplyCap tt r) \<rbrace> fast_finalise cap final \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  apply (case_tac cap, simp_all)
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)
  done

lemma get_cap_reply_cap_helper:
  "\<lbrace>\<lambda>s. \<exists>t r. Some (ReplyCap t r) = caps_of_state s slot \<rbrace> get_cap slot \<lbrace>\<lambda>rv s. \<exists>t r. rv = ReplyCap t r\<rbrace>"
  by (auto simp: valid_def get_cap_caps_of_state[symmetric])


lemma cap_delete_one_bound_tcb_at:
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>t r. caps_of_state s c = Some (ReplyCap t r)) \<rbrace>
      cap_delete_one c \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: cap_delete_one_def unless_def
               wp: fast_finalise_bound_tcb_at hoare_vcg_if_lift2 get_cap_reply_cap_helper
                   hoare_drop_imp)

lemma caps_of_state_tcb_index_trans:
  "\<lbrakk>get_tcb p s = Some tcb \<rbrakk> \<Longrightarrow> caps_of_state s (p, tcb_cnode_index n) = (tcb_cnode_map tcb) (tcb_cnode_index n)"
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: caps_of_state_def)
  apply (safe)
   apply (clarsimp simp: get_object_def get_cap_def)
   apply (simp add:set_eq_iff)
   apply (drule_tac x=cap in spec)
   apply (drule_tac x=s in spec)
   apply (clarsimp simp: in_monad)
  apply (clarsimp simp: get_cap_def get_object_def)
  apply (rule ccontr)
  apply (drule not_sym)
  apply (auto simp: set_eq_iff in_monad)
  done


lemma descendants_of_nullcap:
  "\<lbrakk>descendants_of (a, b) (cdt s) \<noteq> {}; valid_mdb s \<rbrakk> \<Longrightarrow> caps_of_state s (a, b) \<noteq> Some NullCap"
  apply clarsimp
  apply (drule_tac cs="caps_of_state s" and p="(a,b)" and m="(cdt s)" in mdb_cte_at_Null_descendants)
   apply (clarsimp simp: valid_mdb_def2)+
  done

lemma set_thread_state_bound_sc_tcb_at[wp]:
  "set_thread_state t ts \<lbrace>\<lambda>s. Q (bound_sc_tcb_at P t' s)\<rbrace>"
  unfolding set_thread_state_def set_thread_state_act_def
  apply (wpsimp wp: thread_set_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def
                 split: option.splits kernel_object.splits)
  done

lemma reply_unlink_tcb_bound_sc_tcb_at[wp]:
  "\<lbrace>\<lambda>s. Q (bound_sc_tcb_at P t' s)\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>rv s. Q (bound_sc_tcb_at P t' s)\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: hoare_drop_imp)

crunch blocked_cancel_ipc, cancel_signal, test_reschedule
  for bound_sc_tcb_at[wp]:  "bound_sc_tcb_at P t"
  (wp: crunch_wps)

lemma sched_context_cancel_yield_to_bound_yt_tcb_at[wp]:
  "\<lbrace>\<top>\<rbrace> sched_context_cancel_yield_to t \<lbrace>\<lambda>_. bound_yt_tcb_at ((=) None) t\<rbrace>"
  apply (clarsimp simp: sched_context_cancel_yield_to_def)
  apply (rule bind_wp[OF _ gyt_sp])
  apply (wpsimp wp: thread_set_wp update_sched_context_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma set_thread_state_not_live0:
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t and bound_yt_tcb_at ((=) None) t\<rbrace>
   set_thread_state t Inactive
   \<lbrace>\<lambda>_. obj_at (Not \<circ> live0) t\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: thread_set_wp)
  by (clarsimp simp: obj_at_def pred_tcb_at_def get_tcb_def)

crunch tcb_sched_action
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"

lemma obj_at_bound_yt_tcb_at_eq[simp]:
  "obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> bound_yt_tcb_at ((=) (tcb_yield_to tcb)) t s) t s
           = tcb_at t s"
  by (auto simp: obj_at_def pred_tcb_at_def is_tcb)

lemma obj_at_pred_tcb_at_peel:
  "obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> pred_tcb_at proj P t s \<and> Q t s tcb) t s
       = (pred_tcb_at proj P t s \<and> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> Q t s tcb) t s)"
  by (auto simp: obj_at_def pred_tcb_at_def)

crunch tcb_release_remove
 for obj_at_not_live0[wp]: "obj_at (Not \<circ> live0) t"
  (simp: crunch_simps)

lemma set_tcb_yt_update_bound_tcb_at[wp]:
  "set_tcb_obj_ref tcb_yield_to_update scp tcb \<lbrace>bound_tcb_at P t\<rbrace>"
  by (wpsimp wp: thread_set_no_change_tcb_pred)

lemma sched_context_cancel_yield_to_bound_tcb_at[wp]:
  "sched_context_cancel_yield_to scptr \<lbrace>bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_cancel_yield_to_def wp: hoare_drop_imp)

crunch set_consumed
  for pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj test t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma complete_yield_to_bound_tcb_at[wp]:
  "complete_yield_to scptr \<lbrace>bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: complete_yield_to_def wp: hoare_drop_imp)

lemma sched_context_cancel_yield_to_bound_sc_tcb_at[wp]:
  "sched_context_cancel_yield_to scptr \<lbrace>bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_cancel_yield_to_def wp: hoare_drop_imp)

lemma complete_yield_to_bound_sc_tcb_at[wp]:
  "complete_yield_to scptr \<lbrace>bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: complete_yield_to_def wp: hoare_drop_imp)

lemma ssc_bound_yt_tcb_at[wp]:
  "set_tcb_obj_ref tcb_sched_context_update tcb ntfn \<lbrace>bound_yt_tcb_at P t\<rbrace>"
  by (wpsimp wp: thread_set_no_change_tcb_pred)

lemma sched_context_unbind_tcb_bound_tcb_at[wp]:
  "sched_context_unbind_tcb a \<lbrace>bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp)

lemma sched_context_unbind_tcb_bound_yt_tcb_at[wp]:
  "sched_context_unbind_tcb a \<lbrace>bound_yt_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp)

lemma unbind_from_sc_bound_tcb_at[wp]:
  "unbind_from_sc tcb_ptr \<lbrace>bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: unbind_from_sc_def wp: hoare_drop_imps hoare_vcg_all_lift)

crunch sched_context_cancel_yield_to, update_restart_pc
  for tcb_at[wp]: "tcb_at t"
  (wp: crunch_wps)

crunch cancel_ipc
  for bound_sc_tcb_at[wp]: "bound_sc_tcb_at P t"
  (wp: crunch_wps thread_set_no_change_tcb_sched_context)

context IpcCancel_AI begin

lemma suspend_unlive:
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t\<rbrace>
   suspend t
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  unfolding suspend_def
  by (wpsimp wp: set_thread_state_not_live0)

end

definition bound_refs_of_tcb :: "'a state \<Rightarrow> machine_word \<Rightarrow> (machine_word \<times> reftype) set"
where
  "bound_refs_of_tcb s t \<equiv> case kheap s t of
                              Some (TCB tcb) \<Rightarrow> get_refs TCBBound (tcb_bound_notification tcb)
                            | _ \<Rightarrow> {}"

lemma set_thread_state_fault_tcb_at[wp]:
  "set_thread_state p ts \<lbrace>\<lambda>s. Q (fault_tcb_at P t s)\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: thread_set_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def
                 split: kernel_object.splits option.splits)
  done

crunch tcb_sched_action, possible_switch_to
  for valid_cur_fpu[wp]: valid_cur_fpu

lemma cancel_all_signals_invs_helper:
  "\<lbrace>all_invs_but_sym_refs
          and (\<lambda>s. (\<forall>x\<in>set q. ex_nonz_cap_to x s)
                  \<and> sym_refs (\<lambda>x. if x \<in> set q then
                                    {r \<in> state_refs_of s x. snd r = TCBBound \<or>
                                     snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                                  else state_refs_of s x)
                  \<and> sym_refs (\<lambda>x. state_hyp_refs_of s x)
                  \<and> valid_replies s
                  \<and> (\<forall>x\<in>set q. st_tcb_at (Not \<circ> (halted or awaiting_reply)) x s
                                \<and> fault_tcb_at ((=) None) x s))\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                    sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context t;
                    y \<leftarrow> if_sporadic_cur_sc_assert_refill_unblock_check sc_opt;
                    possible_switch_to t od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2, fastforce)
  apply (wpsimp wp: hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle
                    sts_st_tcb_at_cases sts_valid_replies sts_fault_tcbs_valid_states
              cong: conj_cong)
  apply (intro conjI)
    apply (fastforce simp: idle_no_ex_cap)
   apply (subgoal_tac "replies_blocked_upd_tcb_st Restart a (replies_blocked s) = replies_blocked s")
    apply clarsimp
   apply (clarsimp simp: replies_blocked_upd_tcb_st_def pred_tcb_at_def obj_at_def
                         replies_blocked_def split_def)
   apply (case_tac "tcb_state tcb"; fastforce?)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def replies_blocked_upd_tcb_st
                 elim!: rsubst[where P=sym_refs])
  by (auto simp: pred_tcb_at_def obj_at_def replies_blocked_upd_tcb_st
          elim!: rsubst[where P=sym_refs]
          split: if_splits)

lemma ep_no_bound_refs:
  "ep_at p s \<Longrightarrow> {r \<in> state_refs_of s p. snd r = TCBBound} = {}"
  by (clarsimp simp: obj_at_def state_refs_of_def refs_of_def is_ep ep_q_refs_of_def split: endpoint.splits)

lemma obj_at_conj_distrib:
  "obj_at (\<lambda>ko. P ko \<and> Q ko) p s \<Longrightarrow> obj_at (\<lambda>ko. P ko) p s \<and> obj_at (\<lambda>ko. Q ko) p s"
  by (auto simp:obj_at_def)

lemma ep_q_refs_of_no_ntfn_bound:
  "(x, tp) \<in> ep_q_refs_of ep \<Longrightarrow> tp \<noteq> NTFNBound"
  by (auto simp: ep_q_refs_of_def split:endpoint.splits)

lemma ep_q_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> ep_q_refs_of ep"
  by (clarsimp simp: ep_q_refs_of_def split:endpoint.splits)

lemma ep_list_tcb_at:
  "\<lbrakk>ep_at p s; valid_objs s; state_refs_of s p = set q \<times> {k}; x \<in> set q \<rbrakk> \<Longrightarrow> tcb_at x s"
  apply (erule (1) obj_at_valid_objsE)
  apply (fastforce simp:is_ep valid_obj_def valid_ep_def state_refs_of_def split:endpoint.splits)
  done

lemma tcb_at_no_sc_yield_from:
  "\<lbrakk> valid_objs s; tcb_at x s \<rbrakk> \<Longrightarrow> (t, SCYieldFrom) \<notin> state_refs_of s x"
  by (auto elim!: obj_at_valid_objsE
            simp: state_refs_of_def is_tcb get_refs_def tcb_st_refs_of_def
           split: thread_state.splits option.splits if_splits)

lemma tcb_at_no_sc_tcb:
  "\<lbrakk> valid_objs s; tcb_at x s \<rbrakk> \<Longrightarrow> (t, SCTcb) \<notin> state_refs_of s x"
  by (auto elim!: obj_at_valid_objsE
            simp: state_refs_of_def is_tcb get_refs_def tcb_st_refs_of_def
           split: thread_state.splits option.splits if_splits)

lemma tcb_at_no_ntfn_bound:
  "\<lbrakk> valid_objs s; tcb_at x s \<rbrakk> \<Longrightarrow> (t, NTFNBound) \<notin> state_refs_of s x"
  by (auto elim!: obj_at_valid_objsE
           simp: state_refs_of_def is_tcb valid_obj_def get_refs_def tcb_st_refs_of_def
           split:thread_state.splits option.splits if_splits)

lemma ep_no_sc_yield_from:
  "\<lbrakk>is_ep ko; refs_of ko = set q \<times> {SCYieldFrom}; y \<in> set q \<rbrakk> \<Longrightarrow> False"
  apply (subst (asm) set_eq_iff)
  apply (drule_tac x="(y, SCYieldFrom)" in spec)
  apply (clarsimp simp: refs_of_rev is_ep)
  done

lemma ep_no_sc_tcb:
  "\<lbrakk>is_ep ko; refs_of ko = set q \<times> {SCTcb}; y \<in> set q \<rbrakk> \<Longrightarrow> False"
  apply (subst (asm) set_eq_iff)
  apply (drule_tac x="(y, SCTcb)" in spec)
  apply (clarsimp simp: refs_of_rev is_ep)
  done

lemma ep_no_ntfn_bound:
  "\<lbrakk>is_ep ko; refs_of ko = set q \<times> {NTFNBound}; y \<in> set q \<rbrakk> \<Longrightarrow> False"
  apply (subst (asm) set_eq_iff)
  apply (drule_tac x="(y, NTFNBound)" in spec)
  apply (clarsimp simp: refs_of_rev is_ep)
  done

lemma reply_unlink_tcb_st_tcb_at':
  "\<lbrace>\<lambda>s. st_tcb_at P t' s \<and> reply_tcb_reply_at (\<lambda>x. x \<noteq> Some t') rptr s\<rbrace>
   reply_unlink_tcb t rptr \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: reply_unlink_tcb_def)
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_thread_state_def
                      thread_get_def st_tcb_at_def obj_at_def reply_tcb_reply_at_def
                  wp: sts_st_tcb_at_cases get_object_wp get_simple_ko_wp)
  done

lemma reply_unlink_tcb_reply_tcb_reply_at_other:
  "\<lbrace>\<lambda>s. reply_tcb_reply_at ((=) (Some t')) r' s \<and> t' \<noteq> t\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_ s. reply_tcb_reply_at ((=) (Some t')) r' s\<rbrace>"
  apply (wpsimp wp: update_reply_wp get_simple_ko_wp gts_wp
              simp: reply_unlink_tcb_def)
  apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_def)
  done

lemma valid_objs_reply_not_tcbD:
  "valid_objs s \<Longrightarrow> kheap s tptr = Some (TCB tcb) \<Longrightarrow>
   tcb_state tcb = BlockedOnReceive epptr (Some rptr) d \<Longrightarrow> \<not> tcb_at rptr s"
  by (fastforce simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_tcb is_reply obj_at_def)

lemma endpoint_reply_irrelevant:
  "st_tcb_at ((=) (BlockedOnReceive epptr (Some rptr) d)) tptr s
   \<Longrightarrow> valid_objs s
   \<Longrightarrow> \<exists>tptrs. sym_refs (\<lambda>x. if x = tptr \<or> x \<in> set tptrs
                             then {r \<in> state_refs_of s x. snd r \<noteq> TCBBlockedRecv \<and>
                                                          snd r \<noteq> TCBBlockedSend}
                             else state_refs_of s x)
   \<Longrightarrow> reply_tcb_reply_at (\<lambda>x. x = Some tptr) rptr s"
  apply (clarsimp simp: st_tcb_at_def reply_tcb_reply_at_def obj_at_def)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def obj_at_def is_reply
                 split: thread_state.splits)
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = tptr in allE)
  apply clarsimp
  apply (erule_tac x = rptr in allE)
  apply (fastforce simp: state_refs_of_def get_refs_def2 split: if_splits)
  done

(* May be useful in limited circumstances:
   - when set_thread_state is the last step in reestablishing invariants.
   - when the thread is not previously BlockedOnReply. *)
lemma set_thread_state_invs:
  shows "\<lbrace> \<lambda>s. valid_tcb_state st s
               \<and> (\<not> halted st \<longrightarrow> ex_nonz_cap_to t s)
               \<and> (idle st \<longleftrightarrow> t = idle_thread s)
               \<and> (\<forall>r. (r,t) \<in> replies_blocked s \<longrightarrow> st = BlockedOnReply r)
               \<and> sym_refs (\<lambda>p. if p = t
                                then tcb_st_refs_of st \<union> tcb_non_st_state_refs_of s t
                                else state_refs_of s p)
               \<and> sym_refs (state_hyp_refs_of s)
               \<and> (\<not> fault_tcb_states st \<longrightarrow> fault_tcb_at ((=) None) t s)
               \<and> all_invs_but_sym_refs s \<rbrace>
          set_thread_state t st
         \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: TcbAcc_AI.sts_only_idle sts_valid_replies sts_fault_tcbs_valid_states)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def
                 elim!: replies_blocked_upd_tcb_st_valid_replies)
  done

lemmas sts_st_tcb_at_other = sts_st_tcb_at_neq[where proj=itcb_state]

lemma restart_thread_if_no_fault_other:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s) \<and> t \<noteq> t'\<rbrace>
   restart_thread_if_no_fault t'
   \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  apply (simp add: restart_thread_if_no_fault_def)
  by (wpsimp wp: sts_st_tcb_at_other hoare_drop_imps)

lemma replies_blocked_upd_tcb_st_helper:
  "replies_blocked_upd_tcb_st Inactive t rs = replies_blocked_upd_tcb_st Restart t rs"
  by (simp add: replies_blocked_upd_tcb_st_def)

crunch restart_thread_if_no_fault
  for cte_wp_at[wp]: "cte_wp_at P c"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
  and cur_sc_tcb[wp]: "cur_sc_tcb"
  and if_live_then_nonz_cap[wp]: if_live_then_nonz_cap
  and valid_replies[wp]: valid_replies
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
  and tcb_at[wp]: "tcb_at p"
  and ep_at[wp]: "ep_at p"
  (simp: crunch_simps wp: crunch_wps sts_valid_replies)

lemma restart_thread_if_no_fault_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (t := tcb_non_st_state_refs_of s t))\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: restart_thread_if_no_fault_def)
  by (wpsimp wp: hoare_drop_imps simp: fun_upd_def)

(* This rule can cause problems with the simplifier if rule unification chooses a
   P' that does not specify proj. If necessary, this can be worked around by
   manually specifying proj. *)
lemma restart_thread_if_no_fault_pred_tcb_at':
  "\<forall>tcb ts. proj (tcb_to_itcb tcb) = proj (tcb_to_itcb (tcb\<lparr>tcb_state := ts\<rparr>))
   \<Longrightarrow> restart_thread_if_no_fault ref \<lbrace>\<lambda>s. P' (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: restart_thread_if_no_fault_def)
  by (wpsimp wp: set_thread_state_pred_tcb_at' hoare_drop_imps)

crunch reply_unlink_tcb, tcb_ep_dequeue, tcb_ep_append, tcb_ntfn_dequeue, tcb_ntfn_append
  for fault_tcb_at[wp]: "\<lambda>s. P (fault_tcb_at P' t s)"
  (wp: crunch_wps set_thread_state_pred_tcb_at' simp: crunch_simps)

crunch tcb_ep_dequeue, tcb_ep_append, tcb_ntfn_dequeue, tcb_ntfn_append
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to ptr"
  and fault_tcbs_valid_states[wp]: fault_tcbs_valid_states
  (wp: crunch_wps simp: tcb_append_def)

crunch tcb_ep_dequeue, tcb_ep_append, tcb_ntfn_dequeue, tcb_ntfn_append
  for valid_replies[wp]: valid_replies
  and valid_idle[wp]: valid_idle
  (wp: crunch_wps ignore: set_simple_ko)

crunch remove_and_restart_ep_queued_thread, remove_and_restart_ntfn_queued_thread,
       remove_and_restart_badged_thread
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and zombies_final[wp]: zombies_final
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_mdb[wp]: valid_mdb
  and valid_ioc[wp]: valid_ioc
  and only_idle[wp]: only_idle
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and valid_global_refs[wp]: valid_global_refs
  and valid_arch_state[wp]: valid_arch_state
  and valid_irq_node[wp]: valid_irq_node
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_irq_states[wp]: valid_irq_states
  and valid_machine_state[wp]: valid_machine_state
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_global_objs[wp]: valid_global_objs
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_asid_map[wp]: valid_asid_map
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and cur_sc_tcb[wp]: cur_sc_tcb
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to ptr"
  and valid_cur_fpu[wp]: valid_cur_fpu
  (wp: crunch_wps sts_only_idle simp: crunch_simps)

crunch remove_and_restart_ep_queued_thread
  for fault_tcbs_valid_states[wp]: fault_tcbs_valid_states
  (wp: crunch_wps sts_only_idle simp: crunch_simps)

lemma tcb_ep_dequeue_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to ep_ptr\<rbrace>
   tcb_ep_dequeue tptr ep_ptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (clarsimp simp: tcb_ep_dequeue_def)
  by (wpsimp wp: gts_wp  get_simple_ko_wp)

lemma remove_and_restart_ep_queued_thread_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to t and ex_nonz_cap_to ep_ptr\<rbrace>
   remove_and_restart_ep_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  by (wpsimp wp: gts_wp hoare_vcg_all_lift hoare_drop_imps)

lemma remove_and_restart_ep_queued_thread_valid_replies[wp]:
  "\<lbrace>valid_replies and st_tcb_at (\<lambda>st. is_blocked_on_receive st \<or> is_blocked_on_send st) t\<rbrace>
   remove_and_restart_ep_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. valid_replies\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  apply forward_inv_step
  apply (wpsimp wp: reply_unlink_tcb_valid_replies gts_wp)
  apply (fastforce simp: pred_tcb_at_def obj_at_def is_blocked_thread_state_defs
                         replies_blocked_upd_tcb_st_not_BlockedonReply)
  done

crunch restart_thread_if_no_fault
  for valid_idle[wp]: valid_idle
  (wp: crunch_wps)

lemma remove_and_restart_ep_queued_thread_valid_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> t \<noteq> idle_thread s\<rbrace>
   remove_and_restart_ep_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  by (wpsimp wp: gts_wp hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma in_send_ep_queue_st_tcb_at:
  "\<lbrakk>kheap s ep_ptr = Some (Endpoint (SendEP q)); t \<in> set q; sym_refs (state_refs_of s)\<rbrakk>
   \<Longrightarrow> st_tcb_at (\<lambda>st. \<exists>data. st = BlockedOnSend ep_ptr data) t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x=ep_ptr in allE)
  apply (clarsimp simp: state_refs_of_def)
  apply (drule_tac x=t in bspec, fastforce)
  apply (fastforce simp: obj_at_def pred_tcb_at_def tcb_st_refs_of_def get_refs_def2 refs_of_def
                  split: thread_state.splits if_splits option.splits kernel_object.splits)
  done

lemma in_receive_ep_queue_st_tcb_at:
  "\<lbrakk>kheap s ep_ptr = Some (Endpoint (RecvEP q)); t \<in> set q; sym_refs (state_refs_of s)\<rbrakk>
   \<Longrightarrow> st_tcb_at (\<lambda>st. \<exists>data pl. st = BlockedOnReceive ep_ptr data pl) t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x=ep_ptr in allE)
  apply (clarsimp simp: state_refs_of_def)
  apply (drule_tac x=t in bspec, fastforce)
  apply (fastforce simp: obj_at_def pred_tcb_at_def tcb_st_refs_of_def get_refs_def2 refs_of_def
                  split: thread_state.splits if_splits option.splits kernel_object.splits)
  done

lemma remove_and_restart_ep_queued_thread_sym_refs:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s
        \<and> st_tcb_at (\<lambda>st. is_blocked_on_receive st \<or> is_blocked_on_send st) t s
        \<and> ep_at_pred (\<lambda>ep. \<exists>tail. ep_queue ep = t # tail \<and> distinct (t # tail)) ep_ptr s\<rbrace>
   remove_and_restart_ep_queued_thread t ep_ptr
   \<lbrace>\<lambda>_ s. sym_refs (state_refs_of s)\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def tcb_ep_dequeue_def
  apply (wpsimp wp: get_simple_ko_wp reply_unlink_tcb_refs_of gts_wp set_simple_ko_wp)
  apply (rename_tac ep st)
  apply (clarsimp simp: ep_at_pred_def pred_tcb_at_def obj_at_def
                        is_blocked_on_receive_def is_blocked_on_send_def)
  apply (rename_tac tail tcb)
  apply (prop_tac "filter ((\<noteq>) t) (t # tail) = tail")
   apply (fastforce simp: filter_id_conv)
  apply (prop_tac "ep \<noteq> IdleEP")
   apply (fastforce dest: valid_objs_valid_ep)
  by (case_tac ep; intro conjI impI allI;
      rule delta_sym_refs, assumption;
      clarsimp simp: in_state_refs_of_iff split: if_splits;
      intro conjI impI allI;
      force dest: in_send_ep_queue_st_tcb_at[where t=t] in_receive_ep_queue_st_tcb_at[where t=t]
            simp: refs_of_def get_refs_def2 obj_at_def ep_at_pred_def pred_tcb_at_def
           split: list.splits)

lemma remove_and_restart_ep_queued_thread_invs:
  "\<lbrace>\<lambda>s. invs s \<and> ex_nonz_cap_to t s \<and> ex_nonz_cap_to ep_ptr s
        \<and> st_tcb_at (\<lambda>st. is_blocked_on_receive st \<or> is_blocked_on_send st) t s
        \<and> ep_at_pred (\<lambda>ep. \<exists>tail. ep_queue ep = t # tail \<and> distinct (t # tail)) ep_ptr s\<rbrace>
   remove_and_restart_ep_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wpsimp wp: remove_and_restart_ep_queued_thread_sym_refs)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma endpoint_IdleEP_split:
  "(case ep of IdleEP \<Rightarrow> f | _ \<Rightarrow> g) = (if ep = IdleEP then f else g)"
  by (cases ep; clarsimp)

lemma reply_unlink_tcb_st_tcb_at_other:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t' s) \<and> t \<noteq> t'\<rbrace>
   reply_unlink_tcb t r
   \<lbrace>\<lambda>_ s. Q (st_tcb_at P t' s)\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (rule bind_wp_fwd_skip, wpsimp)+
  apply (wpsimp wp: sts_st_tcb_at_cases_strong)
  done

lemma remove_and_restart_ep_queued_thread_other:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s) \<and> t' \<noteq> t\<rbrace>
   remove_and_restart_ep_queued_thread t' epptr
   \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  by (wpsimp wp: restart_thread_if_no_fault_other reply_unlink_tcb_st_tcb_at_other gts_wp
                 hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma tcb_ep_dequeue_dequeues_head:
  "\<lbrace>ep_at_pred (\<lambda>ep. ep_queue ep = t # q \<and> distinct (t # q)) epptr\<rbrace>
   tcb_ep_dequeue t epptr
   \<lbrace>\<lambda>_. ep_at_pred (\<lambda>ep. ep_queue ep = q) epptr\<rbrace>"
  apply (clarsimp simp: tcb_ep_dequeue_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp], rename_tac ep)
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (clarsimp simp: ep_at_pred_def obj_at_def)
  apply (prop_tac "distinct (ep_queue ep)", fastforce)
  apply (case_tac ep; fastforce dest!: filter_hd_equals_tl split: list.splits)
  done

lemma tcb_ntfn_dequeue_dequeues_head:
  "\<lbrace>ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = t # q \<and> distinct (t # q)) ntfnptr\<rbrace>
   tcb_ntfn_dequeue t ntfnptr
   \<lbrace>\<lambda>_. ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = q) ntfnptr\<rbrace>"
  apply (clarsimp simp: tcb_ntfn_dequeue_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp], rename_tac notification)
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (clarsimp simp: ntfn_at_pred_def obj_at_def split: ntfn.splits)
  apply (prop_tac "distinct (t # q)", fastforce)
  apply (fastforce dest!: filter_hd_equals_tl split: list.splits)
  done

lemma thread_set_ep_at_pred[wp]:
  "thread_set f tptr \<lbrace>\<lambda>s. Q (ep_at_pred P ep_ptr s)\<rbrace>"
  apply (wpsimp wp: thread_set_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: ep_at_pred_def get_tcb_def)
  done

lemma update_sched_context_ep_at_pred[wp]:
  "update_sched_context ptr f \<lbrace>\<lambda>s. Q (ep_at_pred P ep_ptr s)\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: ep_at_pred_def obj_at_def get_tcb_def)
  done

lemma update_reply_ep_at_pred[wp]:
  "update_reply f reply_ptr \<lbrace>\<lambda>s. Q (ep_at_pred P ep_ptr s)\<rbrace>"
  apply (wpsimp wp: update_reply_wp)
  apply (fastforce elim: rsubst[where P=Q] simp: ep_at_pred_def obj_at_def get_tcb_def)
  done

crunch restart_thread_if_no_fault, reply_unlink_tcb
  for ep_at_pred[wp]: "\<lambda>s. Q (ep_at_pred P ep_ptr s)"
  (wp: crunch_wps simp: crunch_simps)

lemma remove_and_restart_ep_queued_thread_dequeues_head:
  "\<lbrace>ep_at_pred (\<lambda>ep. ep_queue ep = t # q \<and> distinct (t # q)) epptr\<rbrace>
   remove_and_restart_ep_queued_thread t epptr
   \<lbrace>\<lambda>_. ep_at_pred (\<lambda>ep. ep_queue ep = q) epptr\<rbrace>"
  unfolding remove_and_restart_ep_queued_thread_def
  by (wpsimp wp: hoare_vcg_all_lift tcb_ep_dequeue_dequeues_head hoare_drop_imps)

lemma cancel_all_ipc_invs[wp]:
  "cancel_all_ipc epptr \<lbrace>invs\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp], rename_tac ep)
  apply (subst endpoint_IdleEP_split)
  apply (rule hoare_if; (solves wpsimp)?)
  apply (subst bind_assoc[symmetric])
  apply (rule bind_wp, wpsimp)
  apply (rule_tac S="distinct (ep_queue ep)" in hoare_gen_asm_spec)
   apply (fastforce dest!: invs_valid_objs valid_objs_valid_ep simp: valid_ep_def obj_at_def
                    split: endpoint.splits)
  apply clarsimp
  apply (rule hoare_weaken_pre)
   apply (rule mapM_x_inv_wp2[
                 where I="invs and ex_nonz_cap_to epptr"
                   and V="\<lambda>xs s. (\<forall>x \<in> set xs. st_tcb_at (\<lambda>st. is_blocked_on_receive st
                                                               \<or> is_blocked_on_send st) x s
                                               \<and> ex_nonz_cap_to x s)
                                 \<and> ep_at_pred (\<lambda>ep. ep_queue ep = xs) epptr s"])
    apply (case_tac "ep = IdleEP")
     apply wpsimp
    apply (case_tac ep; simp)
   apply (wpsimp wp: remove_and_restart_ep_queued_thread_invs hoare_vcg_ball_lift
                     remove_and_restart_ep_queued_thread_other
                     remove_and_restart_ep_queued_thread_dequeues_head)
   apply (fastforce dest: simp: suffix_def ep_at_pred_def)
  apply (case_tac ep;
         fastforce dest: in_receive_ep_queue_st_tcb_at in_send_ep_queue_st_tcb_at
                  intro: if_live_then_nonz_capD2
                   simp: st_tcb_at_def obj_at_def live_def ep_at_pred_def)
  done

lemma restart_thread_if_no_fault_st_tcb_at_cases_strong:
  "\<lbrace>\<lambda>s. tcb_at t s \<longrightarrow> (t = t' \<longrightarrow> (if fault_tcb_at ((=) None) t s
                                    then P (P' Restart)
                                    else P (P' Inactive)))
                        \<and> (t \<noteq> t' \<longrightarrow> P (st_tcb_at P' t' s))\<rbrace>
   restart_thread_if_no_fault t
   \<lbrace>\<lambda>rv s. P (st_tcb_at P' t' s) \<rbrace>"
  by (wpsimp simp: restart_thread_if_no_fault_def
               wp: sts_st_tcb_at_cases_strong thread_get_wp')
     (auto simp: pred_tcb_at_def obj_at_def)

crunch remove_and_restart_ep_queued_thread
  for fault_tcb_at[wp]: "\<lambda>s. Q (fault_tcb_at P t s)"
  (wp: crunch_wps)

lemma reply_unlink_tcb_tcb_at[wp]:
  "reply_unlink_tcb t rp \<lbrace>\<lambda>s. P (tcb_at t' s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def wp: update_reply_wp gts_wp get_simple_ko_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  done

lemma cancel_all_ipc_st_tcb_at':
  "\<lbrace>\<lambda>s. if ep_at_pred (\<lambda>ep. t \<in> set (ep_queue ep)) epptr s
        then if fault_tcb_at ((=) None) t s
             then P (P' Restart)
             else P (P' Inactive)
        else P (st_tcb_at P' t s)\<rbrace>
   cancel_all_ipc epptr
   \<lbrace>\<lambda>_ s. P (st_tcb_at P' t s)\<rbrace>"
  apply (simp add: cancel_all_ipc_def remove_and_restart_ep_queued_thread_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (subst endpoint_IdleEP_split)
  apply (rule hoare_if)
   apply wpsimp
   apply (clarsimp simp: obj_at_def ep_at_pred_def)
  apply (subst bind_assoc[symmetric])
  apply (rule bind_wp, wpsimp)
  apply clarsimp
  apply (rule hoare_weaken_pre)
   apply (rule_tac V="\<lambda>q s. if t \<in> set q
                            then if fault_tcb_at ((=) None) t s then P (P' Restart) else P (P' Inactive)
                            else P (st_tcb_at P' t s)"
                in mapM_x_inv_wp2[where I=\<top>, simplified])
    apply fastforce
   apply (rename_tac a as)
   apply (case_tac "t \<in> set as";
          wpsimp wp: gts_wp hoare_vcg_all_lift restart_thread_if_no_fault_st_tcb_at_cases_strong
                     reply_unlink_tcb_st_tcb_at hoare_vcg_imp_lift'
               simp: remove_and_restart_ep_queued_thread_def;
          fastforce)
  apply (force simp: obj_at_def ep_at_pred_def)
  done

lemma cancel_all_ipc_no_fault_st_tcb_at:
  "P Restart \<Longrightarrow>
   \<lbrace>st_tcb_at P t and fault_tcb_at ((=) None) t\<rbrace>
     cancel_all_ipc e
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (auto intro: hoare_weaken_pre[OF cancel_all_ipc_st_tcb_at'])

lemma cancel_all_ipc_has_fault_st_tcb_at:
  "P Inactive \<Longrightarrow>
   \<lbrace>st_tcb_at P t and fault_tcb_at ((\<noteq>) None) t\<rbrace>
     cancel_all_ipc e
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (rule hoare_weaken_pre[OF cancel_all_ipc_st_tcb_at'])
     (auto simp: pred_tcb_at_def obj_at_def)

lemma cancel_all_ipc_st_tcb_at:
  "P Restart \<Longrightarrow> P Inactive
   \<Longrightarrow> \<lbrace>st_tcb_at P t\<rbrace> cancel_all_ipc e \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (auto intro: hoare_weaken_pre[OF cancel_all_ipc_st_tcb_at'])

lemmas cancel_all_ipc_makes_simple[wp] =
  cancel_all_ipc_st_tcb_at[where P=simple, simplified]

lemma cancel_ipc_simple':
  "\<lbrace>st_tcb_at simple t' and invs\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  by (wpsimp simp: cancel_ipc_def get_thread_state_def thread_get_def
               wp: blocked_ipc_st_tcb_at_general cancel_signal_st_tcb_at_general
                   thread_set_no_change_tcb_pred hoare_vcg_imp_lift
            split: option.split)

lemma cancel_ipc_invs_st_tcb_at:
  "\<lbrace>invs\<rbrace> cancel_ipc t
   \<lbrace>\<lambda>rv. invs and st_tcb_at ((=) Running or (=) Inactive or (=) Restart or
                             (=) IdleThreadState) t\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def
               wp: cancel_ipc_simple_except_awaiting_reply)

lemma sched_context_unbind_reply_st_tcb_at[wp]:
  "sched_context_unbind_reply scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_reply_def)

lemma fast_finalise_misc:
"\<lbrace>st_tcb_at simple t and invs\<rbrace> fast_finalise a b \<lbrace>\<lambda>_. st_tcb_at simple t\<rbrace>"
  by (case_tac a; wpsimp wp: cancel_ipc_simple' get_simple_ko_wp gts_wp)

lemma ntfn_q_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)

lemma ntfn_q_refs_no_TCBBound:
  "(x, TCBBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)

lemma set_tcb_obj_ref_valid_irq_node[wp]:
  "set_tcb_obj_ref f t new \<lbrace>valid_irq_node\<rbrace>"
  apply (wpsimp wp: thread_set_wp
              simp: get_tcb_def
             split: option.splits kernel_object.splits)
  apply (clarsimp simp: valid_irq_node_def obj_at_def is_cap_table_def)
  apply (erule_tac x = irq in allE)
  apply auto
  done

lemma set_ntfn_bound_tcb_none_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr None \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def obj_at_def wp: get_simple_ko_wp)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def split: ntfn.splits)
  done

lemma do_unbind_notification_valid_objs[wp]:
  "do_unbind_notification ntfnptr tcbptr \<lbrace>valid_objs\<rbrace>"
  by (wpsimp wp: )

lemma unbind_maybe_notification_valid_objs[wp]:
  "unbind_maybe_notification ntfnptr \<lbrace>valid_objs\<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def wp: hoare_drop_imps)

lemma set_ntfn_bound_tcb_none_if_live_then_nonz_cap [wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr None \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def obj_at_def wp: get_simple_ko_wp)
  apply (fastforce simp: live_def live_ntfn_def elim!: if_live_then_nonz_capD2)
  done

lemma unbind_notification_invs:
  notes refs_of_simps[simp del] if_cong[cong]
  shows "\<lbrace>invs\<rbrace> unbind_notification t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unbind_notification_def invs_def valid_state_def valid_pspace_def maybeM_def)
  apply (rule bind_wp [OF _ gbn_sp])
  apply (case_tac ntfnptr; clarsimp)
  apply wpsimp
  apply (wpsimp wp: valid_irq_node_typ set_simple_ko_valid_objs get_simple_ko_wp
              simp: update_sk_obj_ref_def split_del: if_split)
  apply (intro conjI impI;
    (match conclusion in "sym_refs r" for r \<Rightarrow> \<open>-\<close>
        | auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                       simp: live_def is_ntfn valid_obj_def live_ntfn_def
    )?)
  apply (clarsimp simp: if_split)
  apply (rule conjI, clarsimp simp: pred_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp simp: refs_of_ntfn_def refs_in_get_refs split: if_splits)
   apply (auto simp: get_refs_def2 refs_of_def[split_simps kernel_object.split] refs_of_ntfn_def
              dest!: ko_at_state_refs_ofD)[1]
  apply (clarsimp split: if_split_asm)
   apply (frule pred_tcb_at_tcb_at)
   apply (frule_tac p=t in obj_at_ko_at, clarsimp)
   apply (subst (asm) ko_at_state_refs_ofD, assumption)
   apply (auto simp: obj_at_def is_tcb ntfn_q_refs_no_NTFNBound tcb_at_no_ntfn_bound refs_of_rev
                          tcb_ntfn_is_bound_def refs_of_ntfn_def get_refs_def2
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)[1]
  apply (subst (asm) ko_at_state_refs_ofD, assumption)
  by (auto simp: get_refs_def2 refs_of_ntfn_def obj_at_def ntfn_q_refs_no_TCBBound refs_of_def
                  elim!: pred_tcb_weakenE
                  dest!: bound_tcb_bound_notification_at symreftype_inverse'
                  split: option.splits)

lemma cancel_all_signals_bound_tcb_at[wp]:
  "cancel_all_signals param_a \<lbrace>bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: cancel_all_signals_def remove_and_restart_ntfn_queued_thread_def
               wp: mapM_x_wp_inv get_simple_ko_wp)

lemma waiting_ntfn_list_tcb_at:
  "\<lbrakk>valid_objs s; ko_at (Notification ntfn) ntfnptr s; ntfn_obj ntfn = WaitingNtfn x\<rbrakk> \<Longrightarrow>
   \<forall>t \<in> set x. tcb_at t s"
  by (fastforce elim!: obj_at_valid_objsE simp:valid_obj_def valid_ntfn_def)

lemma tcb_ntfn_dequeue_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to ep_ptr\<rbrace>
   tcb_ntfn_dequeue tptr ep_ptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  by (wpsimp wp: gts_wp get_simple_ko_wp)

lemma remove_and_restart_ntfn_queued_thread_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to t and ex_nonz_cap_to ep_ptr\<rbrace>
   remove_and_restart_ntfn_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def
  by (wpsimp wp: gts_wp hoare_vcg_all_lift hoare_drop_imps)

lemma remove_and_restart_ntfn_queued_thread_valid_replies[wp]:
  "\<lbrace>valid_replies and st_tcb_at is_blocked_on_ntfn t\<rbrace>
   remove_and_restart_ntfn_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. valid_replies\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def
  apply forward_inv_step
  apply (wpsimp wp: sts_valid_replies gts_wp)
  apply (fastforce simp: pred_tcb_at_def obj_at_def is_blocked_thread_state_defs
                         replies_blocked_upd_tcb_st_not_BlockedonReply)
  done

lemma remove_and_restart_ntfn_queued_thread_valid_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> t \<noteq> idle_thread s\<rbrace>
   remove_and_restart_ntfn_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def
  by (wpsimp wp: gts_wp hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma remove_and_restart_ntfn_queued_thread_fault_tcbs_valid_states[wp]:
  "\<lbrace>fault_tcbs_valid_states and st_tcb_at is_blocked_on_ntfn t\<rbrace>
   remove_and_restart_ntfn_queued_thread t ep_ptr
   \<lbrace>\<lambda>_. fault_tcbs_valid_states\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def
  apply (wpsimp wp: sts_fault_tcbs_valid_states)
  apply (erule fault_tcbs_valid_states_not_fault_tcb_states)
  apply (erule st_tcb_weakenE)
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma st_in_waitingntfn:
  "\<lbrakk>kheap s ntfnptr = Some (Notification ntfn); ntfn_obj ntfn = WaitingNtfn q;
    sym_refs (state_refs_of s)\<rbrakk>
   \<Longrightarrow> \<forall>t \<in> set q. st_tcb_at (\<lambda>st. st = BlockedOnNotification ntfnptr) t s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ntfnptr in allE)
  apply (erule_tac x = "(t, NTFNSignal)" in ballE)
  apply (auto simp: state_refs_of_def is_tcb obj_at_def pred_tcb_at_def tcb_st_refs_of_def
                    get_refs_def2 refs_of_def
             split: thread_state.splits if_splits option.splits kernel_object.splits)
  done

lemma remove_and_restart_ntfn_queued_thread_sym_refs:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s)
        \<and> st_tcb_at is_blocked_on_ntfn t s
        \<and> ntfn_at_pred (\<lambda>notification. \<exists>tail. ntfn_queue (ntfn_obj notification) = t # tail
                                       \<and> distinct (t # tail)) ntfnptr s\<rbrace>
   remove_and_restart_ntfn_queued_thread t ntfnptr
   \<lbrace>\<lambda>_ s. sym_refs (state_refs_of s)\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def tcb_ntfn_dequeue_def
  apply (wpsimp wp: get_simple_ko_wp reply_unlink_tcb_refs_of gts_wp set_simple_ko_wp)
  apply (clarsimp simp: ntfn_at_pred_def pred_tcb_at_def obj_at_def is_blocked_on_ntfn_def)
  apply (rename_tac tail tcb ntfn)
  apply (prop_tac "filter ((\<noteq>) t) (t # tail) = tail")
   apply (fastforce simp: filter_id_conv)
  by (case_tac "ntfn_obj obj";
      rule delta_sym_refs, assumption;
      clarsimp simp: in_state_refs_of_iff split: if_splits ntfn.splits;
      intro conjI impI allI; \<comment> \<open>intro conjI impI allI speeds up the rest of the proof\<close>
      force dest: st_in_waitingntfn
            simp: refs_of_def get_refs_def2 obj_at_def ntfn_at_pred_def pred_tcb_at_def
           split: list.splits)

lemma remove_and_restart_ntfn_queued_thread_invs:
  "\<lbrace>\<lambda>s. invs s \<and> ex_nonz_cap_to t s \<and> ex_nonz_cap_to ntfnptr s
        \<and> st_tcb_at is_blocked_on_ntfn t s
        \<and> ntfn_at_pred (\<lambda>notification. \<exists>tail. ntfn_queue (ntfn_obj notification) = t # tail
                                       \<and> distinct (t # tail)) ntfnptr s\<rbrace>
   remove_and_restart_ntfn_queued_thread t ntfnptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_sym_refs)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma remove_and_restart_ntfn_queued_thread_other:
  "\<lbrace>\<lambda>s. Q (st_tcb_at P t s) \<and> t' \<noteq> t\<rbrace>
   remove_and_restart_ntfn_queued_thread t' ntfnptr
   \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def
  by (wpsimp wp: sts_st_tcb_at_other)

lemma remove_and_restart_ntfn_queued_thread_dequeues_head:
  "\<lbrace>ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = t # q \<and> distinct (t # q)) ntfnptr\<rbrace>
   remove_and_restart_ntfn_queued_thread t ntfnptr
   \<lbrace>\<lambda>_. ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = q) ntfnptr\<rbrace>"
  unfolding remove_and_restart_ntfn_queued_thread_def
  by (wpsimp wp: tcb_ntfn_dequeue_dequeues_head)

lemma cancel_all_signals_invs:
  "cancel_all_signals ntfnptr \<lbrace>invs\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp], rename_tac notification)
  apply (case_tac "ntfn_obj notification"; (solves wpsimp)?)
  apply clarsimp
  apply (rename_tac q)
  apply (rule bind_wp, wp)
  apply (rule_tac S="distinct q" in hoare_gen_asm_spec)
   apply (fastforce dest: invs_valid_objs valid_objs_ko_at simp: valid_obj_def valid_ntfn_def)
  apply (rule hoare_weaken_pre)
   apply (rule mapM_x_inv_wp2[
                 where I="invs and ex_nonz_cap_to ntfnptr"
                   and V="\<lambda>xs s. (\<forall>x \<in> set xs. st_tcb_at is_blocked_on_ntfn x s
                                               \<and> ex_nonz_cap_to x s)
                                 \<and> ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = xs) ntfnptr s"])
    apply fastforce
   apply (wpsimp wp: remove_and_restart_ntfn_queued_thread_invs hoare_vcg_ball_lift
                     remove_and_restart_ntfn_queued_thread_other
                     remove_and_restart_ntfn_queued_thread_dequeues_head)
   apply (fastforce simp: suffix_def ntfn_at_pred_def)
  apply (fastforce dest: st_in_waitingntfn
                  intro: if_live_then_nonz_capD2
                   simp: st_tcb_at_def obj_at_def live_def live_ntfn_def ntfn_at_pred_def)
  done

crunch possible_switch_to
 for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma refill_unblock_check_obj_at_impossible':
  "\<lbrakk>\<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk> \<Longrightarrow>
   refill_unblock_check sc_opt
   \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  unfolding refill_unblock_check_def
  by (wpsimp wp: whileLoop_valid_inv update_sched_context_wp get_refills_wp
           simp: refill_head_overlapping_loop_def merge_overlapping_refills_def update_refill_hd_def
                 refill_pop_head_def is_round_robin_def
    | clarsimp elim!: rsubst[where P=P] simp: obj_at_def)+

lemma misc_refill_unblock_check_obj_at_impossible':
  "\<lbrakk>\<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk> \<Longrightarrow>
   if_sporadic_cur_sc_assert_refill_unblock_check sc_opt
   \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  "\<lbrakk>\<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk> \<Longrightarrow>
   if_sporadic_active_cur_sc_assert_refill_unblock_check sc_opt
   \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  "\<lbrakk>\<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk> \<Longrightarrow>
   if_sporadic_cur_sc_test_refill_unblock_check sc_opt
   \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  "\<lbrakk>\<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk> \<Longrightarrow>
   if_sporadic_active_cur_sc_test_refill_unblock_check sc_opt
   \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  "\<lbrakk>\<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk> \<Longrightarrow>
   if_sporadic_and_active_refill_unblock_check sc_opt
   \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  "\<lbrakk>\<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk> \<Longrightarrow>
   if_constant_bandwidth_refill_unblock_check sc_opt
   \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  unfolding if_cond_refill_unblock_check_def
  by (wpsimp wp: sts_obj_at_impossible' refill_unblock_check_obj_at_impossible')+


lemma restart_thread_if_no_fault_obj_at_impossible':
  "\<lbrakk>\<And>tcb. \<not> P' (TCB tcb); \<And>sc n. \<not> P' (SchedContext sc n)\<rbrakk>
   \<Longrightarrow> restart_thread_if_no_fault t \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  unfolding restart_thread_if_no_fault_def
  by (wpsimp wp: sts_obj_at_impossible' hoare_drop_imps misc_refill_unblock_check_obj_at_impossible')

lemmas
  restart_thread_if_no_fault_obj_at_impossible =
    restart_thread_if_no_fault_obj_at_impossible'[where P= id, simplified]

lemma restart_thread_if_no_fault_reply_tcb_reply_at[wp]:
  "restart_thread_if_no_fault t \<lbrace>reply_tcb_reply_at ((=) (Some t')) r_opt\<rbrace>"
  apply (clarsimp simp: sk_obj_at_pred_def)
  apply (wpsimp wp: restart_thread_if_no_fault_obj_at_impossible')
  done

lemma cancel_all_ipc_unlive:
  "\<lbrace>valid_objs\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>_. obj_at (Not \<circ> live) epptr\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (subst endpoint_IdleEP_split)
  apply (rule hoare_if)
   apply wpsimp
   apply (clarsimp simp: live_def elim!: obj_at_weakenE)
  apply clarsimp
  \<comment>\<open>break off @{const reschedule_required}\<close>
  apply (rule bind_wp, wpsimp)
  apply (rule hoare_weaken_pre)
   apply (rule mapM_x_inv_wp2[
                 where I=valid_objs
                   and V="\<lambda>xs. ep_at_pred (\<lambda>ep. ep_queue ep = xs) epptr"])
    apply (fastforce simp: ep_at_pred_def obj_at_def valid_obj_def valid_ep_def endpoint.case_eq_if
                           live_def)
   apply (wpsimp wp: remove_and_restart_ep_queued_thread_dequeues_head)
   apply (fastforce simp: ep_at_pred_def valid_obj_def valid_ep_def endpoint.case_eq_if
                   split: if_splits)
  apply (fastforce simp: ep_at_pred_def obj_at_def)
  done

lemma tcb_ntfn_dequeue_ntfn_bound_tcb[wp]:
  "tcb_ntfn_dequeue t ntfnptr \<lbrace>\<lambda>s. Q (ntfn_at_pred (\<lambda>ntfn. P (ntfn_bound_tcb ntfn)) ntfnptr s)\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: ntfn_at_pred_def obj_at_def)
  done

lemma tcb_ntfn_dequeue_ntfn_sc[wp]:
  "tcb_ntfn_dequeue t ntfnptr \<lbrace>\<lambda>s. Q (ntfn_at_pred (\<lambda>ntfn. P (ntfn_sc ntfn)) ntfnptr s)\<rbrace>"
  unfolding tcb_ntfn_dequeue_def
  apply (wpsimp wp: set_simple_ko_wp get_simple_ko_wp)
  apply (erule rsubst[where P=Q])
  apply (clarsimp simp: ntfn_at_pred_def obj_at_def)
  done

(* This lemma should be sufficient provided that each notification object is unbound BEFORE the
   'cancel_all_signals' function is invoked. TODO: Check the abstract specification and the C and
   Haskell implementations that this is indeed the case. *)
lemma cancel_all_signals_unlive[wp]:
  "\<lbrace>valid_objs
    and ntfn_at_pred (\<lambda>ntfn. ntfn_bound_tcb ntfn = None) ntfnptr
    and ntfn_at_pred (\<lambda>ntfn. ntfn_sc ntfn = None) ntfnptr\<rbrace>
   cancel_all_signals ntfnptr
   \<lbrace>\<lambda>_. obj_at (Not \<circ> live) ntfnptr\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp], rename_tac ntfn)
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    apply (find_goal \<open>match premises in "_ = WaitingNtfn _" \<Rightarrow> \<open>-\<close>\<close>)
    \<comment>\<open>break off @{const reschedule_required}\<close>
    apply (rule bind_wp, wp)
    apply (rule hoare_weaken_pre)
     apply (rule mapM_x_inv_wp2[
                   where I="valid_objs
                            and ntfn_at_pred (\<lambda>ntfn. ntfn_bound_tcb ntfn = None) ntfnptr
                            and ntfn_at_pred (\<lambda>ntfn. ntfn_sc ntfn = None) ntfnptr"
                     and V="\<lambda>xs. ntfn_at_pred (\<lambda>ntfn. ntfn_queue (ntfn_obj ntfn) = xs) ntfnptr"])
      apply (fastforce simp: ntfn_at_pred_def obj_at_def valid_obj_def valid_ntfn_def live_def
                             live_ntfn_def)
     apply (wpsimp wp: tcb_ntfn_dequeue_dequeues_head
                 simp: remove_and_restart_ntfn_queued_thread_def)
     apply (fastforce simp: ntfn_at_pred_def valid_obj_def valid_ntfn_def split: ntfn.splits)
    apply (clarsimp simp: ntfn_at_pred_def obj_at_def)
   apply wpsimp
   apply (clarsimp simp: ntfn_at_pred_def obj_at_def live_def live_ntfn_def)
  apply wpsimp
  apply (clarsimp simp: ntfn_at_pred_def obj_at_def live_def live_ntfn_def)
  done

crunch cancel_all_ipc
 for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp)

crunch cancel_all_signals
  for cte_wp_at[wp]: "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp thread_set_cte_wp_at_trivial
   simp: tcb_cap_cases_def)

lemma tcb_st_refs_of_TCBBlockedOnSend:
  "(ep, TCBBlockedSend) \<in> tcb_st_refs_of st \<longleftrightarrow> (\<exists>d. st = BlockedOnSend ep d)"
  by (cases st) auto

lemma update_sched_context_ko_at_endpoint[wp]:
  "update_sched_context ptr f \<lbrace>\<lambda>s. P (ko_at (Endpoint ep) ep_ptr s)\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (fastforce intro: rsubst[where P=P] simp: obj_at_def)
  done

crunch update_refill_hd, set_thread_state_act
  for endpoint_ko_at[wp]: "\<lambda>s. P (ko_at (Endpoint ep) ep_ptr s)"

lemma set_thread_state_ko_at_endpoint[wp]:
  "set_thread_state ref ts \<lbrace>\<lambda>s. P (ko_at (Endpoint ep) ep_ptr s)\<rbrace>"
  apply (clarsimp simp: set_thread_state_def)
  apply (wpsimp wp: thread_set_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: obj_at_def get_tcb_def)
  done

crunch restart_thread_if_no_fault
  for endpoint_ko_at[wp]: "\<lambda>s. P (ko_at (Endpoint ep) ep_ptr s)"
  and ep_at_pred[wp]: "\<lambda>s. Q (ep_at_pred P ep_ptr s)"
  (wp: crunch_wps simp: crunch_simps ignore: set_thread_state update_sched_context)

lemma set_endpoint_ep_at_pred[wp]:
  "\<lbrace>K (P ep)\<rbrace> set_endpoint ep_ptr ep \<lbrace>\<lambda>_. ep_at_pred P ep_ptr\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  apply (clarsimp simp: ep_at_pred_def)
  done

lemma sym_ref_BlockedOnReceive_RecvEP:
  "\<lbrakk>sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
    tcb_state tcb = Structures_A.BlockedOnReceive eptr ropt pl\<rbrakk>
   \<Longrightarrow> \<exists>list. kheap s eptr = Some (Endpoint (RecvEP list)) \<and> tp \<in> set list"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def)
  apply (drule_tac x="(eptr, TCBBlockedRecv)" in bspec)
   apply (fastforce split: if_split_asm)
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac koa; case_tac koa;
         clarsimp simp: ep_q_refs_of_def get_refs_def2)
  apply (rename_tac ep; case_tac ep; simp)
  done

lemma sym_ref_BlockedOnSend_SendEP:
  "\<lbrakk>sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
    tcb_state tcb = Structures_A.BlockedOnSend eptr pl\<rbrakk>
   \<Longrightarrow> \<exists>list. kheap s eptr = Some (Endpoint (SendEP list)) \<and> tp \<in> set list"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def)
  apply (drule_tac x="(eptr, TCBBlockedSend)" in bspec)
   apply (fastforce split: if_split_asm)
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac koa; case_tac koa;
         clarsimp simp: ep_q_refs_of_def get_refs_def2)
  apply (rename_tac ep; case_tac ep; simp)
  done

lemma cancel_badged_sends_invs[wp]:
  "cancel_badged_sends epptr badge \<lbrace>invs\<rbrace>"
  apply (clarsimp simp: cancel_badged_sends_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp], rename_tac ep)
  apply (case_tac ep; (solves wpsimp)?)
  apply clarsimp
  apply (rule bind_wp)
   apply wpsimp
  apply (rename_tac q)
  apply (rule_tac S="distinct q" in hoare_gen_asm_spec)
   apply (fastforce dest: invs_valid_objs valid_objs_ko_at simp: valid_obj_def valid_ep_def)
  apply (rule hoare_weaken_pre)
   apply (rule mapM_x_inv_wp2[
                 where I="invs and ep_at_pred (\<lambda>ep. \<exists>q. ep = SendEP q \<or> ep = IdleEP) epptr"
                   and V="\<lambda>xs s. \<forall>x \<in> set xs. st_tcb_at (\<lambda>st. \<exists>pl. st = BlockedOnSend epptr pl) x s"])
    apply simp
   prefer 2
   apply (fastforce dest!: in_send_ep_queue_st_tcb_at simp: st_tcb_at_def ep_at_pred_def obj_at_def)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (clarsimp simp: remove_and_restart_badged_thread_def)
  apply (wpsimp wp: hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle
                    sts_st_tcb_at_cases sts_valid_replies gts_wp
                    hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_if_lift2 get_simple_ko_wp
              simp: tcb_ep_dequeue_def
         | rule restart_thread_if_no_fault_other)+
  apply (rename_tac s st)
  apply (prop_tac "\<not> (\<exists>q. ko_at (Endpoint (RecvEP q)) epptr s)")
   apply (clarsimp simp: ep_at_pred_def obj_at_def)
  apply clarsimp
  apply (intro conjI impI allI)
         apply (fastforce dest: sym_ref_BlockedOnSend_SendEP
                         intro: if_live_then_nonz_capD2
                          simp: ep_at_pred_def st_tcb_at_def obj_at_def live_def)
        apply (fastforce intro: if_live_then_nonz_capD2
                          simp: st_tcb_at_def obj_at_def live_def)
       apply (clarsimp simp: st_tcb_at_def obj_at_def replies_blocked_upd_tcb_st_not_BlockedonReply)
      apply (clarsimp simp: st_tcb_at_def obj_at_def replies_blocked_upd_tcb_st_not_BlockedonReply)
     defer \<comment> \<open>defer the sym_refs argument\<close>
     apply (clarsimp simp: st_tcb_at_refs_of_rev pred_tcb_def2 valid_idle_def)
    apply (rename_tac ep, case_tac ep; clarsimp simp: obj_at_def split: list.splits)
   apply (metis distinct_imply_not_in_tail)
  apply (rename_tac ep)
  apply (clarsimp simp: st_tcb_at_def ep_at_pred_def obj_at_def split: list.splits
             simp flip: removeAll_filter_not_eq)
  apply (prop_tac "set (removeAll a (ep_queue ep)) = set (ep_queue ep) - {a}")
   apply (rule set_removeAll)
  apply (prop_tac "ep \<noteq> IdleEP")
   apply (fastforce dest: valid_objs_valid_ep)
  apply (intro conjI impI)
  apply (erule delta_sym_refs; clarsimp simp: in_state_refs_of_iff split: if_splits)
    subgoal by (fastforce simp: get_refs_def2 st_tcb_at_def obj_at_def)
   apply fastforce
  apply (subst removeAll_filter_not_eq)+
  apply (erule delta_sym_refs; clarsimp simp: in_state_refs_of_iff split: if_splits)
  by (fastforce simp: get_refs_def2 st_tcb_at_def obj_at_def)

(** complete_yield_to_invs **)

lemma set_message_info_ex_nonz[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_message_info scptr args \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: set_message_info_def)

lemma set_mrs_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_mrs p' b m \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_cte_wp_at_trivial
         ball_tcb_cap_casesI | simp)+

lemma set_mrs_ex_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_mrs thread buf args \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp wp: ex_nonz_cap_to_pres)

crunch reply_from_kernel
  for ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
  (wp: crunch_wps simp: crunch_simps)

lemma set_consumed_ex_nonz[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_tcb_yield_to_ex_nonz_cap_to[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update p' new
   \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

crunch set_consumed
 for st_tcb_at[wp]: "st_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

crunch set_consumed
 for pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"
  (wp: crunch_wps simp: crunch_simps)

crunch complete_yield_to
  for invs[wp]: invs
  (wp: sched_context_cancel_yield_to_invs crunch_wps)

crunch
  unbind_maybe_notification, sched_context_maybe_unbind_ntfn, sched_context_donate,
  sched_context_unbind_yield_from, sched_context_unbind_all_tcbs, empty_slot,
  cancel_all_ipc, thread_set
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunch
  unbind_maybe_notification, sched_context_maybe_unbind_ntfn, sched_context_donate,
  sched_context_unbind_yield_from, sched_context_unbind_all_tcbs, empty_slot
  for ct_in_state[wp]: "ct_in_state P"
  (wp: ct_in_state_thread_state_lift crunch_wps ignore: set_object set_tcb_obj_ref)

lemma reply_unlink_tcb_ct_active[wp]:
  "reply_unlink_tcb t r \<lbrace>ct_active\<rbrace>"
  apply (simp add: reply_unlink_tcb_def)
  apply (wpsimp wp: sts_ctis_neq gts_wp update_reply_wp get_simple_ko_wp)
  apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

crunch
  tcb_sched_action, reschedule_required, tcb_sched_action, tcb_release_remove,
  test_reschedule, tcb_release_enqueue, sched_context_unbind_reply,
  sched_context_unbind_ntfn
  for ct_in_state[wp]: "ct_in_state P"
  (wp: crunch_wps simp: crunch_simps)

crunch cancel_all_signals, is_final_cap, reply_remove, reply_remove_tcb
  for ct_active[wp]: "ct_active"
  (wp: thread_set_ct_in_state crunch_wps set_thread_state_ct_in_state simp: crunch_simps
   ignore: set_tcb_obj_ref)

lemma cancel_all_ipc_ct_active[wp]:
  "\<lbrace>ct_active and fault_tcbs_valid_states\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>_. ct_active\<rbrace>"
  by (wpsimp wp: ct_in_state_thread_state_lift'
                 cancel_all_ipc_no_fault_st_tcb_at
           simp: fault_tcbs_valid_states_active ct_in_state_def)

crunch tcb_ep_dequeue, tcb_ntfn_dequeue
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and ct_active[wp]: ct_active
  (wp: crunch_wps)

lemma blocked_cancel_ipc_ct_active[wp]:
  "\<lbrace>\<lambda>s. ct_active s \<and> tptr \<noteq> cur_thread s\<rbrace>
     blocked_cancel_ipc state tptr reply_opt
   \<lbrace>\<lambda>_. ct_active\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  by (wpsimp wp: sts_ctis_neq hoare_drop_imps)

lemma cancel_signal_ct_active[wp]:
  "\<lbrace>\<lambda>s. ct_active s \<and> tptr \<noteq> cur_thread s\<rbrace>
     cancel_signal tptr ntfnptr
   \<lbrace>\<lambda>_. ct_active\<rbrace>"
  apply (simp add: cancel_signal_def)
  by (wpsimp wp: sts_ctis_neq hoare_drop_imps)

lemma cancel_ipc_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     cancel_ipc tptr
   \<lbrace>\<lambda>_. ct_active\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (wpsimp wp: gts_wp thread_set_ct_in_state hoare_vcg_imp_lift)
  apply (auto simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma reply_push_valid_objs[wp]:
  "\<lbrace>valid_objs and reply_at reply_ptr and sc_at sc_ptr and
    sc_replies_sc_at (\<lambda>rs. reply_ptr \<notin> set rs) sc_ptr\<rbrace>
   reply_push sc_ptr reply_ptr
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  unfolding reply_push_def
  apply (wpsimp wp: hoare_list_all_lift)
  apply (fastforce simp: valid_obj_def valid_sched_context_def sc_at_pred_n_def obj_at_def)
  done

crunch reply_link_caller
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)

end
