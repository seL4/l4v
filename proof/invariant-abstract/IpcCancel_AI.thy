(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory IpcCancel_AI
imports "./$L4V_ARCH/ArchSchedule_AI"
begin

context begin interpretation Arch .

requalify_facts
  arch_post_cap_deletion_pred_tcb_at

end

declare arch_post_cap_deletion_pred_tcb_at[wp]

lemma blocked_cancel_ipc_simple:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: blocked_cancel_ipc_def | wp sts_st_tcb_at')+

lemma cancel_signal_simple:
  "\<lbrace>\<top>\<rbrace> cancel_signal t ntfn \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: cancel_signal_def | wp sts_st_tcb_at')+

crunch typ_at[wp]: cancel_all_ipc "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)

lemma cancel_all_ipc_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_all_ipc ptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by (wpsimp simp: cancel_all_ipc_def valid_tcb_state_def get_thread_state_def thread_get_def
                   get_ep_queue_def get_simple_ko_def get_object_def valid_ep_def
               wp: mapM_x_wp_inv)

lemma unbind_notification_valid_objs:
  "\<lbrace>valid_objs\<rbrace>
   unbind_notification ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: unbind_notification_def update_sk_obj_ref_def wp: maybeM_inv)
     apply (rule hoare_strengthen_post)
      apply (rule get_ntfn_valid_ntfn)
      apply (wpsimp simp: valid_ntfn_def split: ntfn.splits)+
  done

lemma possible_switch_to_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   possible_switch_to ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by wpsimp

lemma cancel_all_signals_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_all_signals ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: cancel_all_signals_def valid_tcb_state_def get_simple_ko_def get_object_def
                  wp: mapM_x_wp_inv)
  apply (auto simp: valid_obj_def valid_ntfn_def)
  done

lemma get_ep_queue_inv[wp]:
  "\<lbrace>P\<rbrace> get_ep_queue ep \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases ep, simp_all add: get_ep_queue_def)

lemma reply_unlink_tcb_st_tcb_at:
  "\<lbrace>st_tcb_at P t and
   reply_tcb_reply_at (\<lambda>ko. \<exists>t'. ko = Some t' \<and> (t = t' \<longrightarrow> P Inactive)) rptr\<rbrace>
   reply_unlink_tcb rptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: reply_unlink_tcb_def)
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_thread_state_def
                      thread_get_def st_tcb_at_def obj_at_def reply_tcb_reply_at_def
                  wp: sts_st_tcb_at_cases get_object_wp get_simple_ko_wp)
  done

lemma reply_unlink_tcb_st_tcb_at_tcb:
  "\<lbrace>st_tcb_at P t and
   (st_tcb_at (\<lambda>st. ((\<exists>ep. st = BlockedOnReceive ep (Some rptr)) \<or> st = BlockedOnReply (Some rptr)) \<longrightarrow>  P Inactive) t)\<rbrace>
   reply_unlink_tcb rptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: reply_unlink_tcb_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "reply_tcb reply"; clarsimp simp: assert_opt_def)
  apply (case_tac "a=t", clarsimp)
   defer
   apply (wpsimp wp: sts_st_tcb_at_cases assert_inv)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rename_tac state)
  apply (case_tac state; clarsimp simp: assert_def)
   apply (wpsimp simp: set_simple_ko_def set_thread_state_def set_object_def
                a_type_def partial_inv_def wp: get_object_wp)
   apply (clarsimp dest!: get_tcb_SomeD split: if_split_asm simp: pred_tcb_at_def obj_at_def)
   apply (rename_tac ep s tcb)
   apply (drule_tac x=ep in spec, simp)
  apply (wpsimp simp: set_simple_ko_def set_thread_state_def set_object_def
       a_type_def partial_inv_def wp: get_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD split: if_split_asm simp: pred_tcb_at_def obj_at_def)
  done

lemma unbind_notification_st_tcb_at[wp]:
  "unbind_notification t' \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: unbind_notification_def update_sk_obj_ref_def wp: maybeM_inv)

lemma unbind_maybe_notification_st_tcb_at[wp]:
  "unbind_maybe_notification r \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def update_sk_obj_ref_def get_sk_obj_ref_def wp: maybeM_inv)

lemma cancel_all_signals_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  unfolding cancel_all_signals_def unbind_maybe_notification_def
  by (wp ntfn_cases_weak_wp mapM_x_wp' sts_st_tcb_at_cases
         hoare_drop_imps unbind_notification_st_tcb_at
    | simp | wpc)+

lemmas cancel_all_signals_makes_simple[wp] =
       cancel_all_signals_st_tcb_at[where P=simple, simplified]

lemma get_blocking_object_inv[wp]:
  "\<lbrace>P\<rbrace> get_blocking_object st \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases st, simp_all add: get_blocking_object_def ep_blocked_def assert_opt_def)

lemma reply_unlink_sc_st_tcb_at [wp]:
  "reply_unlink_sc scp rp \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def wp: hoare_drop_imps)

crunches test_reschedule, tcb_release_remove
  for reply_tcb_reply_at[wp]: "\<lambda>s. P (reply_at_pred P' p s)"
  (wp: crunch_wps)

global_interpretation sched_context_donate: non_reply_op "sched_context_donate scp tp"
  by unfold_locales (wpsimp simp: sched_context_donate_def
                              wp: hoare_vcg_if_lift2 hoare_drop_imps)

global_interpretation reply_unlink_sc: non_reply_tcb_op "reply_unlink_sc scp rp"
  apply unfold_locales
  apply (wpsimp simp: reply_unlink_sc_def wp: set_simple_ko_wps get_simple_ko_wp)
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def)

lemma reply_unlink_tcb_st_tcb_at_strong:
  "\<lbrace> \<lambda>s. if reply_tcb_reply_at (\<lambda>t'. t' = Some t) r s then P (P' Inactive) else P (st_tcb_at P' t s) \<rbrace>
    reply_unlink_tcb r
   \<lbrace> \<lambda>rv s. P (st_tcb_at P' t s) \<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def pred_tcb_at_eq_commute
                  wp: sts_st_tcb_at_cases_strong set_simple_ko_wps gts_wp get_simple_ko_wp)
  by (auto simp: reply_tcb_reply_at_def pred_tcb_at_def obj_at_def is_tcb)

lemma reply_remove_st_tcb_at[wp]:
  "\<lbrace> \<lambda>s. if reply_tcb_reply_at (\<lambda>t'. t' = Some t) r s then P (P' Inactive) else P (st_tcb_at P' t s) \<rbrace>
    reply_remove r
   \<lbrace> \<lambda>rv s. P (st_tcb_at P' t s) \<rbrace>"
  supply if_split[split del]
  apply (wpsimp simp: reply_remove_def
                  wp: reply_unlink_tcb_st_tcb_at_strong get_simple_ko_wp
                      hoare_lift_Pf2[where f="\<lambda>s. P (st_tcb_at P' t s)"
                                       and P="\<lambda>x s. if reply_tcb_reply_at (\<lambda>t'. t' = Some t) r s
                                                      then P (P' Inactive)
                                                      else x"])
  by (clarsimp split: if_splits)

lemmas set_thread_state_st_tcb_at = sts_st_tcb_at_cases

lemma blocked_ipc_st_tcb_at_general:
  "\<lbrace>st_tcb_at P t' and K (t = t' \<longrightarrow> (P Structures_A.Inactive))
    and (case rptropt of Some r \<Rightarrow>
            reply_tcb_reply_at (\<lambda>ko. \<exists>t''. ko = Some t'' \<and> (t' = t'' \<longrightarrow> (P Inactive))) r
           | _ \<Rightarrow> \<top>)\<rbrace>
   blocked_cancel_ipc st t rptropt
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_blocking_object_inv])
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ get_ep_queue_inv])
  apply (wpsimp simp: blocked_cancel_ipc_def set_simple_ko_def set_object_def
                  wp: sts_st_tcb_at_cases reply_unlink_tcb_st_tcb_at static_imp_wp
                      hoare_vcg_all_lift get_ep_queue_inv
       | wp_once hoare_drop_imps)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
  done

lemma cancel_signal_st_tcb_at_general:
  "\<lbrace>st_tcb_at P t' and K (t = t' \<longrightarrow> (P Structures_A.Running \<and> P Structures_A.Inactive))\<rbrace>
     cancel_signal t ntfn
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (wp sts_st_tcb_at_cases ntfn_cases_weak_wp static_imp_wp)
  apply simp
  done

lemma sched_context_maybe_unbind_ntfn_st_tcb_at[wp]:
  "sched_context_maybe_unbind_ntfn ntfnptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
   by (wpsimp simp: sched_context_maybe_unbind_ntfn_def sched_context_unbind_ntfn_def
                    set_sc_obj_ref_def update_sk_obj_ref_def get_sc_obj_ref_def get_sk_obj_ref_def
                wp: hoare_drop_imps)

lemma sched_context_unbind_ntfn_st_tcb_at[wp]:
  "sched_context_unbind_ntfn scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_ntfn_def set_sc_obj_ref_def update_sk_obj_ref_def
                   get_sc_obj_ref_def)

lemma sched_context_update_consumed_st_tcb_at[wp]:
  "sched_context_update_consumed scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

lemma set_message_info_st_tcb_at[wp]:
  "set_message_info a b \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
   by (wpsimp simp: set_message_info_def)

lemma complete_yield_to_st_tcb_at[wp]:
  "complete_yield_to scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: complete_yield_to_def set_sc_obj_ref_def set_consumed_def get_sc_obj_ref_def
         wp: set_thread_state_st_tcb_at set_message_info_st_tcb_at hoare_drop_imp)

lemma sched_context_unbind_yield_from_st_tcb_at[wp]:
  "sched_context_unbind_yield_from scptr \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_yield_from_def)

crunch st_tcb_at[wp]: tcb_release_remove, sched_context_unbind_all_tcbs "\<lambda>s. Q (st_tcb_at P t s)"
  (ignore: set_tcb_obj_ref)


locale IpcCancel_AI =
    fixes state_ext :: "('a::state_ext) itself"
    assumes arch_post_cap_deletion_typ_at[wp]:
      "\<And>P T p. \<lbrace>\<lambda>(s :: 'a state). P (typ_at T p s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
    assumes arch_post_cap_deletion_idle_thread[wp]:
      "\<And>P. \<lbrace>\<lambda>(s :: 'a state). P (idle_thread s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"

crunch st_tcb_at_simple[wp]: reply_remove,reply_cancel_ipc "st_tcb_at simple t"
  (wp: crunch_wps select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state maybeM_inv
   simp: crunch_simps unless_def fast_finalise.simps wp_del: reply_remove_st_tcb_at)

lemma cancel_ipc_simple [wp]:
  "\<lbrace>\<top>\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state, simp_all)
         defer 6
         apply (wp hoare_strengthen_post [OF blocked_cancel_ipc_simple]
      hoare_strengthen_post [OF cancel_signal_simple]
      sts_st_tcb_at_cases hoare_drop_imps
    | (rule pred_tcb_weakenE, fastforce)
    | clarsimp elim!: pred_tcb_weakenE pred_tcb_at_tcb_at)+
  apply wpc
    apply wpsimp
   apply (rule reply_cancel_ipc_st_tcb_at_simple)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (case_tac "tcb_state tcb"; clarsimp)
  done

lemma reply_remove_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> reply_remove r \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: reply_unlink_tcb_typ_at hoare_drop_imp)

lemma blocked_cancel_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> blocked_cancel_ipc st t r \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: blocked_cancel_ipc_def wp: reply_unlink_tcb_typ_at get_simple_ko_inv assert_inv)

lemma blocked_cancel_ipc_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc st t' r \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp

context IpcCancel_AI begin

crunch typ_at[wp]: cancel_ipc, reply_cancel_ipc
                   "\<lambda>(s::'a state). P (typ_at T p s)"
  (wp: crunch_wps hoare_vcg_if_splitE select_wp maybeM_inv
     simp: crunch_simps unless_def)

crunch typ_at[wp]: get_notification
                   "\<lambda>(s::'a state). P (typ_at T p s)"
  (wp: crunch_wps hoare_vcg_if_splitE select_wp
     simp: crunch_simps unless_def)

lemma unbind_maybe_notification_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     unbind_maybe_notification t \<lbrace>\<lambda>_ (s::'a state). P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def wp: hoare_drop_imps)

lemma cancel_ipc_tcb [wp]:
  "\<lbrace>tcb_at t\<rbrace> cancel_ipc t' \<lbrace>\<lambda>rv. (tcb_at t) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

lemma gbep_ret:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr r \<or>
     st = Structures_A.BlockedOnSend epPtr p \<rbrakk> \<Longrightarrow>
  get_blocking_object st = return epPtr"
  by (auto simp add: get_blocking_object_def ep_blocked_def assert_opt_def)

lemma st_tcb_at_valid_st2:
  "\<lbrakk> st_tcb_at ((=) st) t s; valid_objs s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def get_tcb_def pred_tcb_at_def
                  obj_at_def)
  apply (drule_tac x=t in bspec)
   apply (erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  done

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
            | a # list \<Rightarrow> update_ep_queue ep xs)
     = (\<lambda>s. distinct xs \<and> (\<forall>t\<in>set xs. tcb_at t s))"
  "ep \<noteq> Structures_A.IdleEP \<Longrightarrow>
   ep_q_refs_of (case xs of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                   | a # list \<Rightarrow> update_ep_queue ep xs)
     = (set xs \<times> {case ep of Structures_A.SendEP xs \<Rightarrow> EPSend | Structures_A.RecvEP xs \<Rightarrow> EPRecv})"
 by (cases ep, simp_all cong: list.case_cong add: ep_redux_simps)+

lemma gbi_ep_sp:
  "\<lbrace>P\<rbrace>
     get_blocking_object st
   \<lbrace>\<lambda>ep. P and K ((\<exists>r. st = Structures_A.BlockedOnReceive ep r)
                    \<or> (\<exists>d. st = Structures_A.BlockedOnSend ep d))\<rbrace>"
  apply (cases st, simp_all add: get_blocking_object_def ep_blocked_def assert_opt_def)
   apply (wp | simp)+
  done

lemma get_epq_sp:
  "\<lbrace>P\<rbrace>
  get_ep_queue ep
  \<lbrace>\<lambda>q. P and K (ep \<in> {Structures_A.SendEP q, Structures_A.RecvEP q})\<rbrace>"
  apply (simp add: get_ep_queue_def)
  apply (cases ep)
  apply (wp|simp)+
  done

crunches set_thread_state_act
 for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

crunches reply_unlink_tcb
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and iflive[wp]: if_live_then_nonz_cap
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
 and valid_mdb[wp]: "valid_mdb"
 and valid_ioc[wp]: "valid_ioc"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: Let_def wp: hoare_drop_imps)

lemma reply_unlink_tcb_sc_at[wp]: "\<lbrace>sc_at sc_ptr\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. sc_at sc_ptr\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def set_simple_ko_def
            wp: set_object_wp hoare_drop_imp get_simple_ko_wp)
  by (clarsimp simp: obj_at_def is_sc_obj_def)

lemma reply_unlink_tcb_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def get_simple_ko_def
                      get_object_def)
  apply (auto simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_rev)
  done

lemma sts_only_idle:
  "\<lbrace> K (\<not>idle st) and only_idle \<rbrace> set_thread_state t st \<lbrace>\<lambda>_. only_idle\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp simp: only_idle_def pred_tcb_at_def set_object_def obj_at_def)

lemma reply_unlink_tcb_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. only_idle\<rbrace>"
  unfolding reply_unlink_tcb_def
  by (wpsimp wp: sts_only_idle
           simp: thread_get_def only_idle_def pred_tcb_at_def set_simple_ko_def get_object_def
                 get_simple_ko_def get_thread_state_def)

lemma reply_unlink_tcb_zombie_final[wp]: "\<lbrace>zombies_final\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def set_simple_ko_def
            wp: set_object_wp hoare_drop_imp get_simple_ko_wp)
  apply (rule zombies_kheap_update, simp)
  by (clarsimp simp: obj_at_def is_reply)

lemma reply_unlink_tcb_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. valid_irq_node\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def wp: valid_irq_node_typ hoare_drop_imp)

lemma reply_unlink_tcb_refs_of:
  "\<lbrace>\<lambda>s. \<forall>tp reply. kheap s rp = Some (Reply reply) \<and> reply_tcb reply = Some tp \<longrightarrow>
                   P (\<lambda>a. if a = tp then {r \<in> state_refs_of s a. snd r = TCBBound \<or>
                                          snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                          else (if a = rp then {r \<in> state_refs_of s a.
                                                snd r = ReplySchedContext}
                                else state_refs_of s a))\<rbrace>
   reply_unlink_tcb rp
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def get_simple_ko_def
                      get_object_def update_sk_obj_ref_def split_del: if_split)
  apply (clarsimp simp: a_type_def partial_inv_def split: kernel_object.splits split del: if_split)
  apply (clarsimp dest!: get_tcb_SomeD split del: if_split)
  apply (rule conjI; rule impI; clarsimp elim!: rsubst[where P = P] intro!: ext split del: if_split)
   by (case_tac "a=ya"; clarsimp; fastforce simp: get_refs_def state_refs_of_def split: option.splits)+

lemma tcb_at_no_sc_reply:
  "\<lbrakk> valid_objs s; tcb_at x s \<rbrakk> \<Longrightarrow> (t, SCReply) \<notin> state_refs_of s x"
  by (auto elim!: obj_at_valid_objsE
            simp: state_refs_of_def is_tcb get_refs_def tcb_st_refs_of_def
           split: thread_state.splits option.splits if_splits)

lemma endpoint_state_refs_of_subset:
  "kheap s epptr = Some (Endpoint (RecvEP queue)) \<Longrightarrow>
   (y, tp) \<in> state_refs_of (s\<lparr>kheap := kheap s(epptr \<mapsto> Endpoint (
     case remove1 t queue of [] \<Rightarrow> IdleEP
                     | a # list \<Rightarrow> update_ep_queue (RecvEP queue) (remove1 t queue)))\<rparr>) x \<Longrightarrow>
   (y, tp) \<notin> state_refs_of s x \<Longrightarrow> False"
  by (fastforce simp: state_refs_of_def ep_q_refs_of_def
               split: endpoint.splits if_splits list.splits)

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
  "\<lbrace> \<lambda>s. \<forall>t st. reply_tcb_reply_at (\<lambda>t'. t' = Some t) r s \<longrightarrow>
                P (replies_with_sc s) (replies_blocked_upd_tcb_st Inactive t (replies_blocked s)) \<rbrace>
    reply_unlink_tcb r
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
               wp: valid_irq_node_typ valid_ioports_lift)

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

lemma assert_opt_sp:
  "\<lbrace> P \<rbrace> assert_opt x \<lbrace> \<lambda>rv s. x = Some rv \<and> P s\<rbrace>"
  by (wpsimp wp: assert_opt_wp)

lemma blocked_cancel_ipc_invs:
  "\<lbrace> \<lambda>s. invs s
         \<and> st_tcb_at ((=) st) t s
         \<and> (\<exists>ep sender_data. (st = BlockedOnSend ep sender_data \<and> r = None)
                              \<or> (st = BlockedOnReceive ep r))\<rbrace>
    blocked_cancel_ipc st t r
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  supply if_split[split del] reply_unlink_tcb_iflive[wp del]
  apply (simp add: blocked_cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gbi_ep_sp])
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ get_epq_sp])
  apply (rule_tac S="st = BlockedOnReceive epptr r
                     \<or> r = None \<and> (\<exists>sender_data. st = BlockedOnSend epptr sender_data)"
           in hoare_gen_asm'', fastforce)
  apply (rule_tac S="ep \<in> {SendEP queue, RecvEP queue} \<and> ep \<noteq> IdleEP \<and> t \<noteq> epptr" in hoare_gen_asm''
         , fastforce simp: pred_tcb_at_def obj_at_def)
  apply (rule_tac B="\<lambda>rv s. ko_at (Endpoint (case remove1 t queue
                                               of [] \<Rightarrow> IdleEP
                                                | a # list \<Rightarrow> update_ep_queue ep (remove1 t queue)))
                                  epptr s
                            \<and> st_tcb_at (\<lambda>st'. st' = st) t s
                            \<and> t \<noteq> idle_thread s
                            \<and> distinct queue
                            \<and> sym_refs ((state_refs_of s)(epptr := ep_q_refs_of ep))
                            \<and> sym_refs (state_hyp_refs_of s)
                            \<and> all_invs_but_sym_refs s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: set_simple_ko_at valid_irq_node_typ valid_ioports_lift)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def pred_tcb_at_eq_commute)
   apply (rule conjI, clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
   apply (frule (1) if_live_then_nonz_capD; clarsimp simp: live_def)
   apply (simp add: ep_redux_simps2 st_tcb_at_tcb_non_st_state_refs_of cong: if_cong)
   apply (rule_tac V="distinct queue \<and> (\<forall>t \<in> set queue. tcb_at t s)" in revcut_rl)
    apply (erule (1) obj_at_valid_objsE, fastforce simp: valid_obj_def valid_ep_def, clarsimp)
   apply (erule rsubst[of sym_refs "state_refs_of s" for s], rule ext)
   apply (clarsimp split: if_splits simp: obj_at_def state_refs_of_def)
  apply (cases r; clarsimp)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def fun_upd_def
                   wp: sts_valid_replies sts_only_idle valid_irq_node_typ)
   apply (rule conjI, clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp, fastforce+)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (rule_tac V="state_refs_of s epptr
                       = ep_q_refs_of ep - {(t, case ep of SendEP xs \<Rightarrow> EPSend | RecvEP xs \<Rightarrow> EPRecv)}"
            in revcut_rl)
    apply (case_tac ep; simp add: state_refs_of_def ep_redux_simps2 Times_Diff_distrib1)
   apply (erule delta_sym_refs
          ; clarsimp split: if_splits
          ; fastforce simp: state_refs_of_def get_refs_def2)
  apply (rule hoare_seq_ext[where B="\<lambda>rv s. st_tcb_at inactive t s \<and> invs s"])
   apply (wpsimp wp: sts_invs_minor)
   apply (fastforce simp: pred_tcb_at_def obj_at_def valid_idle_def dest!: invs_valid_idle)
  apply (rename_tac r_ptr)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_inv], simp)
  apply (rule_tac S="r_ptr \<notin> {t, epptr}" in hoare_gen_asm''
         , fastforce simp: pred_tcb_at_def obj_at_def)
  apply (rule hoare_vcg_conj_lift[where P=P and P'=P for P, simplified])
   apply (clarsimp simp: reply_unlink_tcb_def)
   apply (rule hoare_seq_ext[OF _ get_simple_ko_sp], rename_tac reply)
   apply (rule hoare_seq_ext[OF _ assert_opt_sp], rename_tac t')
   apply (rule_tac S="t'=t" in hoare_gen_asm''; wpsimp wp: sts_st_tcb_at')
   apply (subgoal_tac "(t, ReplyTCB) \<in> ((state_refs_of s)(epptr := ep_q_refs_of ep)) r_ptr"
          , clarsimp simp: state_refs_of_def obj_at_def get_refs_def2)
   apply (erule sym_refsE, clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: reply_unlink_tcb_refs_of reply_unlink_tcb_valid_replies
                      reply_unlink_tcb_iflive valid_ioports_lift)
  apply (case_tac "reply_tcb reply"; clarsimp simp: reply_at_ppred_def obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp: sym_refs_def)
   apply (drule_tac x=t in spec)
   apply (subgoal_tac "t \<noteq> epptr"; clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (drule_tac x="(r_ptr, TCBReply)" in bspec)
    apply (clarsimp simp: state_refs_of_def get_refs_def2)+
   apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp+)
  apply (rename_tac t', rule_tac V="t'=t" in revcut_rl)
   apply (subgoal_tac "(t, ReplyTCB) \<in> ((state_refs_of s)(epptr := ep_q_refs_of ep)) r_ptr"
      , clarsimp simp: state_refs_of_def obj_at_def get_refs_def2)
   apply (erule sym_refsE, clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def)
  apply (clarsimp simp: st_tcb_at_tcb_non_st_state_refs_of' cong: if_cong)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (rule_tac V="ep = RecvEP queue" in revcut_rl)
   apply (rule_tac V="(t, EPRecv) \<in> ((state_refs_of s)(epptr := ep_q_refs_of ep)) epptr" in revcut_rl
          , erule sym_refsE, clarsimp simp: state_refs_of_def, clarsimp)
  apply (rule_tac V="state_refs_of s epptr = ep_q_refs_of ep - {(t, EPRecv)}" in revcut_rl)
   apply (simp add: state_refs_of_def ep_redux_simps2 Times_Diff_distrib1)
  by (erule delta_sym_refs
      ; clarsimp split: if_splits
      ; fastforce simp: state_refs_of_def get_refs_def2)

lemma cancel_signal_invs:
  "\<lbrace>invs and st_tcb_at ((=) (Structures_A.BlockedOnNotification ntfn)) t\<rbrace>
  cancel_signal t ntfn
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_signal_def
                   invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfna", simp_all)[1]
  apply (rule hoare_pre)
   apply (wp set_simple_ko_valid_objs valid_irq_node_typ sts_only_idle valid_ioports_lift
             sts_valid_replies hoare_vcg_all_lift hoare_vcg_imp_lift
           | simp add: valid_tcb_state_def refs_of_ntfn_def
           | wpc)+
  apply (clarsimp simp: refs_of_ntfn_def ep_redux_simps cong: list.case_cong if_cong)
  apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def live_ntfn_def)+)
  apply (frule ko_at_state_refs_ofD)
  apply (frule st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (case_tac ntfna)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp split:option.split)
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp, clarsimp+)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)+
   apply (fastforce dest: refs_in_get_refs symreftype_inverse')
  apply (fastforce simp: obj_at_def is_ntfn idle_not_queued
                   dest: idle_only_sc_refs elim: pred_tcb_weakenE)
  done

lemma reply_unlink_sc_sc_tcb_sc_at [wp]:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (P (idle_thread s)) scp' s\<rbrace>
   reply_unlink_sc scp rp
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (P (idle_thread s)) scp' s\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sched_context_def set_object_def
                      get_object_def update_sk_obj_ref_def set_simple_ko_def get_simple_ko_def
                      get_sched_context_def)
  apply (auto simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma reply_unlink_tcb_reply_at [wp]:
  "\<lbrace>reply_at rp'\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. reply_at rp'\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def get_thread_state_def
                      thread_get_def
                  wp: get_simple_ko_wp)

lemma reply_unlink_sc_hyp_refs_of [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def wp: get_simple_ko_wp)

crunches test_reschedule, set_sc_obj_ref, get_sc_obj_ref
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
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
                   get_object_def sc_tcb_sc_at_def obj_at_def)

crunches sched_context_donate
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
  (ignore: set_object set_tcb_obj_ref wp: crunch_wps simp: crunch_simps)

lemma sched_context_donate_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_irq_node\<rbrace>"
  by (wp valid_irq_node_typ)

crunches reply_unlink_sc
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
  and valid_idle[wp]: valid_idle
  and valid_ioc[wp]: valid_ioc
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
  (wp: get_simple_ko_wp valid_irq_node_typ)

lemma reply_unlink_sc_it [wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def wp: get_simple_ko_wp)

lemma reply_unlink_sc_sc_at [wp]:
  "\<lbrace>sc_at scp'\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>rv. sc_at scp'\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def update_sk_obj_ref_def set_simple_ko_def set_object_def
                      get_object_def get_simple_ko_def obj_at_def is_sc_obj_def set_sc_obj_ref_def
                      update_sched_context_def)
  apply auto
  done

lemma reply_unlink_tcb_sc_tcb_sc_at [wp]:
  "\<lbrace>\<lambda>s. sc_tcb_sc_at (P (idle_thread s)) scp' s\<rbrace>
   reply_unlink_tcb rp
   \<lbrace>\<lambda>_ s. sc_tcb_sc_at (P (idle_thread s)) scp' s\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def sc_tcb_sc_at_def set_object_def
                      update_sk_obj_ref_def set_simple_ko_def get_object_def get_simple_ko_def
                      get_thread_state_def thread_get_def set_thread_state_act_def
                      set_scheduler_action_def is_schedulable_def)
  by (auto simp: obj_at_def get_tcb_def)

lemma sc_tcb_not_idle_thread_helper:
  "sc_tcb sc = Some tp \<Longrightarrow>
   kheap s scp = Some (SchedContext sc n) \<Longrightarrow>
   sym_refs (state_refs_of s) \<Longrightarrow>
   (scp, TCBSchedContext) \<in> state_refs_of s tp"
  by (fastforce simp: state_refs_of_def elim!: sym_refsE)

lemma sc_tcb_not_idle_thread:
  "kheap s scp = Some (SchedContext sc n) \<Longrightarrow>
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

text \<open>Describing exactly how @{term reply_unlink_sc} updates @{term state_refs_of}
      is quite cumbersome, so instead we prove that it preserves @{term sym_refs}
      under some additional assumptions. Since @{term reply_unlink_sc} called in
      contexts where these conditions hold, this should be sufficient.\<close>
lemma reply_unlink_sc_sym_refs:
  "\<lbrace> \<lambda>s. valid_objs s \<and> valid_replies s \<and> sym_refs (state_refs_of s) \<rbrace>
    reply_unlink_sc scp rp
   \<lbrace> \<lambda>rv s. sym_refs (state_refs_of s) \<rbrace>"
  apply (clarsimp simp: reply_unlink_sc_def)
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[simplified]])
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rename_tac replies reply)
  apply (case_tac "hd replies \<noteq> rp"; clarsimp)
   apply wpsimp
   apply (rule_tac rfs'="state_refs_of s" in delta_sym_refs
          ; clarsimp simp: in_state_refs_of_iff sc_replies_sc_at_def obj_at_def get_refs_def2
                    split: if_splits)
   apply (case_tac tp; case_tac "sc_replies sc"; clarsimp)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule_tac S="\<exists>replies'. replies = rp # replies'" in hoare_gen_asm'')
   apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
   apply (frule_tac x=rp and y=scp and tp=SCReply in sym_refsE
          ; fastforce simp: in_state_refs_of_iff get_refs_def2)
  apply (case_tac replies
         ; clarsimp simp: sc_at_pred_n_eq_commute
         ; rename_tac replies)
  apply (case_tac replies; wpsimp)
   apply (rule_tac rfs'="state_refs_of s" in delta_sym_refs
          ; fastforce simp: in_state_refs_of_iff sc_replies_sc_at_def obj_at_def get_refs_def2
                     split: if_splits)
  apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  apply (rename_tac reply rp' rps s sc n)
  apply (erule (1) pspace_valid_objsE[where ko="SchedContext _ _"])
  apply (clarsimp simp: valid_obj_def valid_sched_context_def is_reply list_all_iff)
  apply (rule_tac V="scp \<notin> set (rp # rp' # rps)" in revcut_rl
         , fastforce simp: obj_at_def is_reply)
  apply (clarsimp cong: if_cong split del: if_split)
  apply (rule_tac rfs'="state_refs_of s" in delta_sym_refs
         ; clarsimp simp: in_state_refs_of_iff is_reply get_refs_def2 refs_of_rev
                   split: if_splits
         ; fastforce?)
  apply (rename_tac reply rp' rps s sc n scp' reply' sc' rps' n')
  by (frule_tac sc=scp and sc'=scp' and r=rp' in valid_repliesD2
      ; fastforce simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)

crunch refs_of[wp]: test_reschedule "\<lambda>s. P (state_refs_of s)"

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
  assumes "valid_replies' with_sc blocked"
  assumes "\<forall>r. r \<in> fst ` with_sc \<and> (r,t) \<in> blocked \<longrightarrow> st = BlockedOnReply (Some r)"
  shows "valid_replies' with_sc (replies_blocked_upd_tcb_st st t blocked)"
  using assms by (fastforce simp: valid_replies_defs replies_blocked_upd_tcb_st_def image_def)

lemma replies_blocked_upd_tcb_st_valid_replies_not_blocked:
  assumes "valid_replies' with_sc blocked"
  assumes "\<forall>r. (r,t) \<notin> blocked"
  shows "valid_replies' with_sc (replies_blocked_upd_tcb_st st t blocked)"
  using assms by (fastforce simp: valid_replies_defs replies_blocked_upd_tcb_st_def image_def)

text \<open>@{term reply_unlink_tcb} does not preserve @{term invs} when the
      associated thread is @{term BlockedOnReceive}, because it drops a
      reference to an endpoint. For that case, rebalancing @{term sym_refs}
      happens elsewhere.\<close>
lemma reply_unlink_tcb_invs_BlockedOnReply':
  "\<lbrace> \<lambda>s. invs s
         \<and> (\<nexists>sc_ptr. sc_replies_sc_at (\<lambda>rs. rptr \<in> set rs) sc_ptr s)
         \<and> (\<exists>tptr. st_tcb_at ((=) (BlockedOnReply (Some rptr))) tptr s) \<rbrace>
    reply_unlink_tcb rptr
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def pred_tcb_at_eq_commute
                  wp: reply_unlink_tcb_refs_of reply_unlink_tcb_valid_replies valid_ioports_lift)
  apply (rule conjI)
   apply (clarsimp simp: reply_at_ppred_def pred_tcb_at_def obj_at_def)
   apply (rule_tac V="tptr = t" in revcut_rl)
    apply (subgoal_tac "(tptr, ReplyTCB) \<in> state_refs_of s rptr"
           , fastforce simp: in_state_refs_of_iff get_refs_def2)
    apply (erule sym_refsE, fastforce simp: state_refs_of_def, clarsimp)
   apply (erule replies_blocked_upd_tcb_st_valid_replies)
   apply (fastforce simp: replies_with_sc_def replies_blocked_def pred_tcb_at_def obj_at_def)
  apply (clarsimp, rule delta_sym_refs, assumption)
   apply (clarsimp split: if_splits)
  apply (fastforce simp: state_refs_of_def st_tcb_def2 tcb_st_refs_of_def obj_at_def get_refs_def2
                  dest!: get_tcb_ko_atD sym_refs_ko_atD
                  split: thread_state.splits if_splits)
  done

lemma reply_unlink_tcb_invs_BlockedOnReply:
  "\<lbrace> \<lambda>s. invs s
         \<and> rptr \<notin> fst ` replies_with_sc s
         \<and> rptr \<in> fst ` replies_blocked s \<rbrace>
    reply_unlink_tcb rptr
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  by (wpsimp wp: reply_unlink_tcb_invs_BlockedOnReply' simp: pred_tcb_at_eq_commute)
     (fastforce simp: replies_with_sc_def replies_blocked_def image_iff)

lemma reply_unlink_sc_valid_replies:
  "\<lbrace> valid_replies \<rbrace>
    reply_unlink_sc scp rp
   \<lbrace> \<lambda>rv. valid_replies \<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def wp: set_sc_replies_valid_replies get_simple_ko_wp)
  apply (intro conjI impI allI
         ; erule replies_with_sc_upd_replies_subset_valid_replies'
         ; clarsimp simp: sc_replies_sc_at_def obj_at_def dest!: set_takeWhileD)
  by (case_tac "sc_replies sc"; fastforce)

lemma reply_unlink_sc_invs:
  "\<lbrace>\<lambda>s. invs s\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def
               wp: valid_ioports_lift reply_unlink_sc_sym_refs reply_unlink_sc_valid_replies)

lemma set_thread_state_act_inv:
  "(\<And>s. P (s\<lparr>scheduler_action := choose_new_thread\<rparr>) = P s) \<Longrightarrow> set_thread_state_act t \<lbrace>P\<rbrace>"
  by (wpsimp simp: set_thread_state_act_def set_scheduler_action_def is_schedulable_def)

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
  apply (rule hoare_seq_ext[OF _ gsct_sp])
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

lemma sched_context_donate_invs:
  "\<lbrace>\<lambda>s. invs s \<and> tcb_at tcb_ptr s \<and> ex_nonz_cap_to sc_ptr s \<and> ex_nonz_cap_to tcb_ptr s \<and>
    bound_sc_tcb_at ((=) None) tcb_ptr s \<and> sc_at sc_ptr s\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: sched_context_donate_sym_refs valid_ioports_lift)
  apply (rule conjI)
   apply (clarsimp simp: idle_no_ex_cap)
  apply (thin_tac "tcb_at tcb_ptr s")
  apply (subgoal_tac "sc_tcb_sc_at (\<lambda>x. (\<forall>t. x = Some t \<longrightarrow> obj_at live t s)) sc_ptr s")
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def if_live_then_nonz_cap_def
                 dest!: idle_no_ex_cap)
  apply (clarsimp simp: is_sc_obj_def obj_at_def sc_tcb_sc_at_def)
  apply (case_tac ko; simp)
  apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
  apply (fastforce simp: valid_obj_def valid_sched_context_def is_tcb obj_at_def live_def)
  done

lemma reply_unlink_sc_pred_tcb_at [wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sk_obj_ref_def
               wp: get_simple_ko_wp)

lemma sc_replies_update_fst_replies_with_sc:
  "\<lbrace>\<lambda>s. ((r, sc) \<in> replies_with_sc s) \<and> (r \<notin> set k) \<and> valid_replies s\<rbrace>
   set_sc_obj_ref sc_replies_update sc k
   \<lbrace>\<lambda>rv s. r \<notin> fst ` replies_with_sc s\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def
                  wp: update_sched_context_wp)
  apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def split: if_splits)
  apply (clarsimp simp: valid_replies'_def inj_on_def)
  done

lemma reply_unlink_sc_fst_replies_with_sc:
  "\<lbrace>\<lambda>s. sc_replies_sc_at (\<lambda>l. l\<noteq>[] \<and> distinct l \<and> r \<in> set l) sc s \<and> valid_replies s\<rbrace>
   reply_unlink_sc sc r
   \<lbrace>\<lambda>rv s. r \<notin> fst ` replies_with_sc s\<rbrace>"
  unfolding reply_unlink_sc_def
  apply (wpsimp wp: sc_replies_update_fst_replies_with_sc
                    get_simple_ko_wp)
  apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def
                 split: if_splits)
  apply (safe; clarsimp?)
  apply (case_tac "sc_replies sca"; simp)
  apply (fastforce dest: distinct_hd_not_in_tl)
  apply (fastforce dest: set_takeWhileD)
  done

lemma reply_unlink_sc_not_fst_replies_blocked[wp]:
  "\<lbrace>(\<lambda>s. r \<notin> fst ` replies_blocked s) \<rbrace>
   reply_unlink_sc sc r
   \<lbrace>\<lambda>rv s. r \<notin> fst ` replies_blocked s\<rbrace>"
  unfolding reply_unlink_sc_def
  apply (wpsimp simp: set_sc_obj_ref_def
                  wp: update_sched_context_wp update_sk_obj_ref_wps' set_simple_ko_wp
                      get_simple_ko_wp)
  apply (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def image_def
                 split: if_splits)
  done

lemma reply_unlink_sc_fst_replies_blocked[wp]:
  "\<lbrace>(\<lambda>s. r \<in>  fst ` replies_blocked s) \<rbrace>
   reply_unlink_sc sc r
   \<lbrace>\<lambda>rv s. r \<in> fst ` replies_blocked s\<rbrace>"
  unfolding reply_unlink_sc_def
  apply (wpsimp simp: set_sc_obj_ref_def
                  wp: update_sched_context_wp update_sk_obj_ref_wps' set_simple_ko_wp
                      get_simple_ko_wp)
  apply (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def image_def
                 split: if_splits)
  apply (safe; rule_tac x=b in exI, fastforce)
  done

lemma fst_replies_blocked_strengthen:
  "(reply_tcb_reply_at (\<lambda>p. \<exists>tp. p = Some tp \<and>
                            st_tcb_at ((=) (BlockedOnReply (Some r))) tp s) r s)
    \<Longrightarrow> (r \<in> fst ` replies_blocked s)"
  by (fastforce simp: replies_blocked_def reply_tcb_reply_at_def obj_at_def image_def
                      pred_tcb_at_eq_commute)

lemma reply_remove_invs:
  "\<lbrace>\<lambda>s. invs s \<and>
       reply_tcb_reply_at (\<lambda>p. \<exists>tp. p = Some tp \<and>
                                    st_tcb_at ((=) (BlockedOnReply (Some r))) tp s) r s\<rbrace>
   reply_remove r
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_split[split del]
  apply (rule hoare_weaken_pre[where Q="invs and (\<lambda>s. r \<in> fst ` replies_blocked s)"])
   prefer 2
   apply (clarsimp, erule fst_replies_blocked_strengthen)
  apply (simp add: reply_remove_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (simp add: assert_opt_def2)
  apply (rule hoare_seq_ext[OF _ assert_inv], simp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF reply_unlink_tcb_invs_BlockedOnReply])
  apply (case_tac r_sc_opt; clarsimp)
   apply (wpsimp)
   apply (fastforce dest: valid_replies_sc_with_reply_None invs_valid_replies
                    simp: replies_with_sc_def)
  apply (rename_tac sc)
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (wpsimp wp: sched_context_donate_invs  hoare_vcg_if_lift2 reply_unlink_sc_fst_replies_with_sc
                    hoare_vcg_imp_lift reply_unlink_sc_invs)
  apply (clarsimp simp: pred_tcb_at_eq_commute)
  apply (clarsimp simp: pred_tcb_at_def sc_at_pred_def reply_at_ppred_def obj_at_def is_tcb is_sc_obj)
  apply (rename_tac sc_obj n)
  apply (subgoal_tac "reply_tcb reply \<noteq> None")
   prefer 2
   apply (drule replies_blocked_imp_TCBReply_ref)
   apply (drule_tac st="state_refs_of s" in sym_refsD)
    apply (erule invs_sym_refs)
   apply (clarsimp simp: state_refs_of_def get_refs_def split: option.splits)
  apply (clarsimp)
  apply (intro impI conjI)
   apply (case_tac "tcb_sched_context tcb"; simp)
   apply (drule sc_with_reply_SomeD)
   apply (subgoal_tac "sc_replies sc_obj \<noteq> []")
    apply (rule conjI, fastforce simp: live_def live_sc_def dest: invs_iflive if_live_then_nonz_capD2)
    apply (rule conjI)
     apply (rule if_live_then_nonz_capD2)
       apply (rule invs_iflive, assumption)
      apply (assumption)
     apply (clarsimp simp: live_def) (* use symrefs for tcb_sched_context tcb = Some _ *)
     apply (subgoal_tac "(hd (sc_replies sc_obj), TCBReply) \<in> state_refs_of s y")
      apply (fastforce simp: state_refs_of_def tcb_st_refs_of_def)
     apply (erule sym_refsE[OF invs_sym_refs])
     apply (fastforce simp: state_refs_of_def)
    apply (rule conjI)
     apply (drule invs_valid_objs)
     apply (subgoal_tac "valid_obj sc (SchedContext sc_obj n) s")
      apply (clarsimp simp: valid_obj_def)
     apply (fastforce simp: valid_objs_def dom_def)
    apply (rule conjI, clarsimp)
    apply (rule conjI)
     apply (drule invs_valid_objs)
     apply (subgoal_tac "valid_obj sc (SchedContext sc_obj n) s")
      apply (clarsimp simp: valid_obj_def valid_sched_context_def)
     apply (fastforce simp: valid_objs_def dom_def)
    apply (rule conjI, clarsimp)
    apply clarsimp
   apply clarsimp
  apply (drule sc_with_reply_SomeD)
  apply (safe; clarsimp?)
   apply (drule invs_valid_objs)
   apply (subgoal_tac "valid_obj sc (SchedContext sc_obj n) s")
    apply (clarsimp simp: valid_obj_def valid_sched_context_def)
   apply (fastforce simp: valid_objs_def dom_def)
  apply (drule invs_valid_objs)
  apply (subgoal_tac "valid_obj sc (SchedContext sc_obj n) s")
   apply (clarsimp simp: valid_obj_def valid_sched_context_def)
  apply (fastforce simp: valid_objs_def dom_def)
  done

lemma sc_with_reply_SomeD1:
  "sc_with_reply rptr s = Some sc_ptr \<Longrightarrow> sc_replies_sc_at (\<lambda>rs. rptr \<in> set rs) sc_ptr s"
  by (auto simp add: sc_with_reply_def' elim: the_pred_option_SomeD)

lemma reply_sc_update_None_invs:
  "\<lbrace>all_invs_but_sym_refs and (\<lambda>s. sym_refs
               (\<lambda>x. if x = r
                     then {p. (snd p = ReplySchedContext \<longrightarrow> None = Some (fst p)) \<and>
                              (snd p \<noteq> ReplySchedContext \<longrightarrow> p \<in> state_refs_of s r)}
                     else state_refs_of s x) \<and>
              sym_refs (state_hyp_refs_of s))\<rbrace>
   set_reply_obj_ref reply_sc_update r None
   \<lbrace>\<lambda>r. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_ioports_lift)

lemma sc_replies_update_valid_replies_cons:
  "\<lbrace>valid_replies
    and (sc_replies_sc_at ((=) sc_replies') sc_ptr)
    and (\<lambda>s. r_ptr \<in> fst ` replies_blocked s)
    and (\<lambda>s. r_ptr \<notin> fst ` replies_with_sc s)\<rbrace>
   set_sc_obj_ref sc_replies_update sc_ptr (r_ptr # sc_replies')
   \<lbrace>\<lambda>r. valid_replies \<rbrace>"
  apply (wpsimp wp: set_sc_replies_valid_replies)
  apply (clarsimp simp: replies_with_sc_upd_replies_def valid_replies'_def)
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

lemma replies_with_sc_takeWhile_subset:
  "(sc_replies_sc_at (\<lambda>rs. rs = replies) sc_ptr s) \<Longrightarrow> r' \<in> set replies \<Longrightarrow>
  replies_with_sc
             (s\<lparr>kheap := kheap s(sc_ptr \<mapsto>
                  SchedContext (x\<lparr>sc_replies := takeWhile (\<lambda>r. r \<noteq> r') replies\<rparr>) xa)\<rparr>) \<subseteq> replies_with_sc s"
   apply (clarsimp simp: image_def replies_with_sc_def sc_replies_sc_at_def obj_at_def
                         replies_blocked_def st_tcb_at_def)
   by (fastforce dest: set_takeWhileD)

lemma replies_blocked_takeWhile_eq:
  "(sc_replies_sc_at (\<lambda>rs. rs = replies) sc_ptr s) \<Longrightarrow>  r' \<in> set replies \<Longrightarrow>
  replies_blocked
             (s\<lparr>kheap := kheap s(sc_ptr \<mapsto>
                  SchedContext (x\<lparr>sc_replies := takeWhile (\<lambda>r. r \<noteq> r') replies\<rparr>) xa)\<rparr>) = replies_blocked s"
   apply (clarsimp simp: image_def replies_blocked_def st_tcb_at_def obj_at_def)
   by (fastforce simp: sc_replies_sc_at_def obj_at_def)

(* this is true but precondition could be weaker? *)
lemma sc_replies_update_take_While_valid_replies:
  "\<lbrace> valid_replies and (\<lambda>s. sc_replies_sc_at (\<lambda>rs. rs = replies) sc_ptr s \<and> r' \<in> set replies)\<rbrace>
   set_sc_obj_ref sc_replies_update sc_ptr (takeWhile (\<lambda>r. r \<noteq> r') replies)
   \<lbrace>\<lambda>rv. valid_replies\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def
                  wp: set_object_wp get_object_wp)
  apply (clarsimp simp: valid_replies'_def)
  apply (intro conjI)
   apply (simp add: replies_blocked_takeWhile_eq)
   apply (rule subset_trans, erule replies_with_sc_takeWhile_subset[THEN image_mono], assumption, assumption)
  apply (rule inj_on_subset, assumption, rule replies_with_sc_takeWhile_subset, assumption, assumption)
  done

lemma sc_replies_update_takeWhile_not_fst_replies_with_sc:
  "\<lbrace>valid_replies and (\<lambda>s. sc_replies_sc_at (\<lambda>rs. r' \<in> set rs) sc_ptr s)\<rbrace>
   set_sc_obj_ref sc_replies_update sc_ptr (takeWhile (\<lambda>r. r \<noteq> r') replies)
   \<lbrace>\<lambda>rv s. r' \<notin> fst ` replies_with_sc s\<rbrace>"
   apply (wpsimp simp: set_sc_obj_ref_def update_sched_context_def
                   wp: set_object_wp get_object_wp)
   apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def split: option.splits if_splits)
  apply (fastforce dest: set_takeWhileD)
  apply (clarsimp simp: valid_replies'_def inj_on_def)
  done

lemma reply_remove_tcb_invs:
  "\<lbrace>invs\<rbrace> reply_remove_tcb t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: reply_remove_tcb_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac ts; clarsimp simp: pred_tcb_at_eq_commute)
  apply (rename_tac r_opt)
  apply (rule hoare_seq_ext[OF _ assert_opt_sp])
  apply (rule_tac S="r_opt = Some rptr" in hoare_gen_asm''; clarsimp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF reply_unlink_tcb_invs_BlockedOnReply])
  apply (case_tac sc_ptr_opt; simp)
   apply wpsimp
   apply (fastforce simp: replies_with_sc_def replies_blocked_def image_iff
                          valid_replies_sc_with_reply_None[OF _ invs_valid_replies])
  apply (rename_tac sc_ptr)
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[simplified]]; clarsimp)
  apply (rename_tac replies)
  apply (rule_tac S="replies \<noteq> []" in hoare_gen_asm''
         , fastforce simp: sc_replies_sc_at_def obj_at_def dest: sc_with_reply_SomeD1)
  apply (case_tac "hd replies = rptr"; clarsimp)
   apply (wpsimp wp: reply_sc_update_None_invs sc_replies_update_take_While_valid_replies
                     set_sc_replies_valid_replies)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (rule conjI, clarsimp simp: list_all_def)
    apply (subgoal_tac "rp \<in> set (replies)";
           fastforce dest: valid_objs_sc_replies_reply_at set_takeWhileD)
   apply (rule conjI, fastforce dest: valid_objs_sc_replies_distinct distinct_takeWhile)
   apply (rule conjI, fastforce simp: sc_replies_sc_at_def obj_at_def live_def live_sc_def
                                dest: if_live_then_nonz_capD2)
   apply (rule conjI, clarsimp simp: sc_at_pred_n_eq_commute)
   apply (rule conjI, clarsimp simp: sc_at_pred_n_eq_commute)
    defer (* ? *)
    apply (rule conjI)
     apply (clarsimp simp: replies_with_sc_upd_replies_def)
     apply (case_tac "b = sc_ptr"; simp)
      apply (fastforce dest: set_takeWhileD)
     apply (fastforce dest: valid_repliesD2 sc_with_reply_replies_with_sc)
    apply (subgoal_tac "hd replies \<in> fst ` replies_with_sc s")
     apply (fastforce simp: valid_replies'_def image_def)
    apply (fastforce dest!: sc_with_reply_SomeD1
                      simp: replies_with_sc_def image_def sc_replies_sc_at_def obj_at_def)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: reply_sc_update_None_invs sc_replies_update_take_While_valid_replies
                     set_sc_replies_valid_replies)
   apply (rule conjI, clarsimp simp: list_all_def)
    apply (subgoal_tac "rp \<in> set (replies)";
           fastforce dest: valid_objs_sc_replies_reply_at set_takeWhileD)
   apply (rule conjI, fastforce dest: valid_objs_sc_replies_distinct distinct_takeWhile)
   apply (rule conjI, fastforce simp: sc_replies_sc_at_def obj_at_def live_def live_sc_def
                                dest: if_live_then_nonz_capD2)
   apply (rule conjI)
    apply (clarsimp dest!: sc_with_reply_replies_with_sc
                     simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)
   apply (rule conjI)
    apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def
                   dest!: sc_with_reply_replies_with_sc)
   apply (rule conjI)
    (* symrefs proof *)
    apply (rule_tac rfs'="state_refs_of s" in delta_sym_refs;
           clarsimp simp: in_state_refs_of_iff get_refs_def2 split: if_splits;
           clarsimp simp: sc_replies_sc_at_def obj_at_def get_refs_def split: option.splits)
   apply (rule conjI)
    apply (clarsimp simp: replies_with_sc_upd_replies_def)
    apply (case_tac "b = sc_ptr"; simp)
     apply (fastforce dest: set_takeWhileD)
    apply (fastforce dest: valid_repliesD2 sc_with_reply_replies_with_sc)
   apply (subgoal_tac "rptr \<in> fst ` replies_with_sc s")
    apply (fastforce simp: valid_replies'_def image_def)
   apply (fastforce dest!: sc_with_reply_SomeD1
                     simp: replies_with_sc_def image_def sc_replies_sc_at_def obj_at_def)
                   (* symrefs proof *)
  apply (subgoal_tac "reply_at (hd replies) s")
   prefer 2
   apply (erule valid_objs_sc_replies_reply_at[simplified sc_at_pred_n_eq_commute], assumption)
  using list.set_sel(1)
   apply fastforce
  apply (rule_tac rfs'="state_refs_of s" in delta_sym_refs;
         clarsimp simp: in_state_refs_of_iff get_refs_def2 split: if_splits)
      apply (clarsimp simp: sc_replies_sc_at_def obj_at_def get_refs_def split: option.splits)
     apply (clarsimp simp: sc_replies_sc_at_def obj_at_def get_refs_def split: option.splits)
    apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_reply)
   apply (safe; clarsimp?)
     apply (case_tac replies; simp)
    apply (clarsimp simp: obj_at_def is_reply get_refs_def split: option.splits)
   apply (subgoal_tac "y = sc_ptr", simp)
   apply (erule_tac r="hd replies" in valid_repliesD2)
    apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)
    apply (case_tac koa;
           clarsimp simp: refs_of_def obj_at_def is_reply refs_of_tcb_def
                          get_refs_def refs_of_ntfn_def refs_of_sc_def
                   split: option.splits)
    apply (clarsimp simp: refs_of_reply_def get_refs_def split: option.splits)
   apply (erule sc_with_reply_replies_with_sc)
  apply (clarsimp simp: sc_replies_sc_at_def obj_at_def get_refs_def split: option.splits)
  done

lemma reply_cancel_ipc_invs:
  "\<lbrace>invs\<rbrace> reply_cancel_ipc t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: reply_cancel_ipc_def wp: reply_remove_tcb_invs)
   apply (wpsimp wp: thread_set_invs_trivial)
          apply (auto simp: tcb_cap_cases_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma cancel_ipc_invs[wp]:
  "\<lbrace>invs\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state, simp_all split: option.splits)
        apply (auto intro!: hoare_weaken_pre [OF return_wp]
                            hoare_weaken_pre [OF blocked_cancel_ipc_invs]
                            hoare_weaken_pre [OF cancel_signal_invs]
                            hoare_weaken_pre [OF reply_cancel_ipc_invs]
                     elim!: pred_tcb_weakenE)
  done

context IpcCancel_AI begin

lemma cancel_ipc_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> cancel_ipc p \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)


lemma cancel_ipc_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> cancel_ipc t \<lbrace>\<lambda>_. (cte_at p) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cte_at_typ)

end

lemma valid_ep_queue_subset:
  "\<lbrace>\<lambda>s. valid_ep ep s\<rbrace>
     get_ep_queue ep
   \<lbrace>\<lambda>queue s. valid_ep (case (remove1 t queue) of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                       | a # list \<Rightarrow> update_ep_queue ep (remove1 t queue)) s\<rbrace>"
  apply (simp add: get_ep_queue_def)
  apply (case_tac ep, simp_all)
   apply wp
   apply (clarsimp simp: ep_redux_simps2 valid_ep_def)
  apply wp
  apply (clarsimp simp: ep_redux_simps2 valid_ep_def)
  done

lemma blocked_cancel_ipc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> blocked_cancel_ipc st t r \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wp get_simple_ko_valid[where f=Endpoint, simplified valid_ep_def2[symmetric]]
            valid_ep_queue_subset
         | simp only: valid_inactive simp_thms
                cong: imp_cong
         | wpc
         | wp_once hoare_drop_imps
         | clarsimp)+
  done

lemma cancel_signal_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> cancel_signal t ntfnptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp set_simple_ko_valid_objs
          | simp only: valid_inactive
          | simp
          | wpc)+
  apply (clarsimp simp: ep_redux_simps cong: list.case_cong)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (auto split: option.splits list.splits)
  done


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

crunch it[wp]: set_thread_state "\<lambda>(s::det_ext state). P (idle_thread s)"
  (wp: crunch_wps select_wp simp: unless_def crunch_simps)


lemma cancel_all_ipc_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> cancel_all_ipc tcb_ptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: cancel_all_ipc_def set_thread_state_def reply_unlink_tcb_def
               wp: mapM_x_wp' hoare_drop_imp)

lemma cancel_signal_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> cancel_signal tcb_ptr ntfnptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: cancel_signal_def set_thread_state_def set_simple_ko_def set_object_def
                   get_object_def get_simple_ko_def)

lemma cancel_all_signals_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> cancel_all_signals tcb_ptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: cancel_all_signals_def set_thread_state_def get_simple_ko_def get_object_def
               wp: mapM_x_wp')

crunch it[wp]: unbind_notification "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp maybeM_inv simp: unless_def crunch_simps)

crunch it[wp]: tcb_release_remove,test_reschedule "\<lambda>s. P (idle_thread s)"

crunch it[wp]: fast_finalise "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp maybeM_inv simp: unless_def crunch_simps
    ignore: test_reschedule tcb_release_remove)

context IpcCancel_AI begin
lemma reply_cancel_ipc_it[wp]:
  "\<lbrace>\<lambda>(s::'a state). P (idle_thread s)\<rbrace> reply_cancel_ipc param_a
    \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: reply_cancel_ipc_def reply_remove_tcb_def reply_remove_def
                   sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
                   reply_unlink_sc_def set_sc_obj_ref_def update_sched_context_def set_object_def
                   update_sk_obj_ref_def set_simple_ko_def get_simple_ko_def get_object_def
                   reply_unlink_tcb_def set_thread_state_def get_thread_state_def thread_get_def
                   thread_set_def
               wp: hoare_drop_imp)

crunch it[wp]: reply_cancel_ipc  "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp maybeM_inv simp: unless_def crunch_simps)

crunch it[wp]: cancel_ipc "\<lambda>(s::'a state). P (idle_thread s)"
  (wp: maybeM_inv)
end

lemma sym_refs_bound_yt_tcb_at:
  "sym_refs (state_refs_of s) \<Longrightarrow> bound_yt_tcb_at ((=) (Some sc)) t s \<Longrightarrow>
   (t', SCYieldFrom) \<in> state_refs_of s sc \<Longrightarrow>  t' = t"
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (frule sym_refs_ko_atD[unfolded obj_at_def, simplified], assumption)
  apply (clarsimp simp: state_refs_of_def refs_of_rev split: option.splits)
  apply (erule_tac x = "(sc, TCBYieldTo)" in ballE)
   apply (auto simp: get_refs_def2)
  done

crunches tcb_release_remove
  for valid_ioports[wp]: valid_ioports

lemma suspend_invs_helper:
  "\<lbrace>invs and st_tcb_at (\<lambda>st. st \<in> {Running, Inactive, Restart, IdleThreadState}) t\<rbrace>
   do yt_opt <- get_tcb_obj_ref tcb_yield_to t;
      y <- maybeM (\<lambda>sc_ptr. do y <- set_sc_obj_ref sc_yield_from_update sc_ptr None;
                                set_tcb_obj_ref tcb_yield_to_update t None
                             od)
            yt_opt;
      y <- set_thread_state t Inactive;
      y <- tcb_sched_action tcb_sched_dequeue t;
      tcb_release_remove t
   od
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ gyt_sp])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: sts_only_idle valid_irq_node_typ maybeM_wp
                      sts_valid_replies hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (simp cong: if_cong)
  apply (rule_tac V="valid_replies' (replies_with_sc s) (replies_blocked_upd_tcb_st Inactive t (replies_blocked s))" in revcut_rl
         , clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp, clarsimp+)
  apply (rule_tac V="t \<noteq> idle_thread s" in revcut_rl
         , clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def
         , fastforce simp: live_def dest!: if_live_then_nonz_capD2 idle_no_ex_cap)
  apply simp
  apply (intro conjI | clarsimp)+
   apply (rule delta_sym_refs, assumption)
    apply (clarsimp split: if_splits)
   apply (clarsimp split: if_splits)
     apply ((fastforce simp: state_refs_of_def get_refs_def2 pred_tcb_at_def obj_at_def)+)[2]
   apply (clarsimp simp: sym_refs_bound_yt_tcb_at)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_splits)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                        tcb_st_refs_of_def
                 split: if_splits thread_state.splits)
  done

lemma blocked_cancel_ipc_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (simp add: blocked_cancel_ipc_def | wp sts_st_tcb_at')+

lemma cancel_signal_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> cancel_signal t ntfn \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (simp add: cancel_signal_def | wp sts_st_tcb_at')+

lemma reply_unlink_tcb_inactive [wp]:
  "\<lbrace>reply_tcb_reply_at (\<lambda>x. x = Some t) r\<rbrace> reply_unlink_tcb r \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def update_sk_obj_ref_def
                      set_simple_ko_def get_object_def get_thread_state_def thread_get_def
                      reply_tcb_reply_at_def
                  wp: get_simple_ko_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma reply_remove_inactive [wp]:
  "\<lbrace>reply_tcb_reply_at (\<lambda>x. x = Some t) r\<rbrace> reply_remove r \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: get_simple_ko_wp wp_del: reply_remove_st_tcb_at)

lemma reply_remove_tcb_inactive [wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace> reply_remove_tcb t
   \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
   apply (wpsimp simp: reply_remove_tcb_def wp: gts_wp)
   apply (frule (1) st_tcb_at_valid_st2)
   apply (clarsimp simp: pred_tcb_at_def reply_tcb_reply_at_def obj_at_def valid_tcb_state_def is_reply_def)
   apply (case_tac koa; clarsimp)
   apply (frule_tac p=t in sym_refs_ko_atD[rotated], simp add: obj_at_def)
   apply (clarsimp simp: get_refs_def2 tcb_st_refs_of_def obj_at_def
                   split: if_split_asm thread_state.splits)
  done

lemma reply_cancel_ipc_inactive [wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace> reply_cancel_ipc t
   \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) t\<rbrace>"
  apply (wpsimp simp: reply_cancel_ipc_def)
   apply (rule hoare_vcg_conj_lift)
    apply (wpsimp simp: thread_set_def set_object_def)
   apply (wpsimp simp: tcb_cap_cases_def wp: thread_set_valid_objs_triv)
  apply auto[8]
  apply safe
  apply (rule delta_sym_refs, assumption)
   apply (auto simp: state_refs_of_def get_tcb_SomeD split: if_splits)
  done

lemma suspend_invs:
  shows
  "\<lbrace>invs\<rbrace> suspend t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: suspend_def)
  apply (wp suspend_invs_helper)
   apply (clarsimp simp: cancel_ipc_def)
   apply (wpsimp wp: gts_wp
         | (strengthen st_tcb_weakenE[mk_strg I], wp_once))+
  apply (auto elim: st_tcb_weakenE)
  done

context IpcCancel_AI begin

lemma suspend_typ_at [wp]:
  "\<lbrace>\<lambda>(s::'a state). P (typ_at T p s)\<rbrace> suspend t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: suspend_def wp: hoare_drop_imps)


lemma suspend_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> suspend tcb \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)


lemma suspend_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> suspend t \<lbrace>\<lambda>rv. (tcb_at t')  :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

crunch cte_wp_at[wp]: blocked_cancel_ipc "cte_wp_at P p"
  (wp: crunch_wps maybeM_inv)

crunch cte_wp_at[wp]: cancel_signal "cte_wp_at P p"
  (wp: crunch_wps)

crunch cte_wp_at[wp]: reply_remove_tcb "cte_wp_at P p"
  (wp: crunch_wps)

locale delete_one_pre =
  fixes state_ext_type :: "('a :: state_ext) itself"
  assumes delete_one_cte_wp_at_preserved:
    "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
     \<lbrace>cte_wp_at P sl\<rbrace> (cap_delete_one sl' :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"


lemma (in delete_one_pre) reply_cancel_ipc_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (reply_cancel_ipc t:: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  unfolding reply_cancel_ipc_def
  apply (wpsimp wp: select_wp)
   apply (rule_tac Q="\<lambda>_. cte_wp_at P p" in hoare_post_imp, clarsimp)
   apply (wpsimp wp: thread_set_cte_wp_at_trivial simp: ran_tcb_cap_cases)
  apply assumption
  done


lemma (in delete_one_pre) cancel_ipc_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_pre)
   apply (wp reply_cancel_ipc_cte_wp_at_preserved | wpcw | simp)+
  done

lemma (in delete_one_pre) suspend_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (suspend tcb :: (unit,'a) s_monad) \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>"
  by (simp add: suspend_def) (wpsimp wp: cancel_ipc_cte_wp_at_preserved hoare_drop_imps)

lemma set_thread_state_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> set_thread_state p ts \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def set_object_def
  by (wpsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma reply_unlink_tcb_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> reply_unlink_tcb rptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def wp: hoare_drop_imp)

crunch bound_tcb_at[wp]: cancel_all_ipc, empty_slot, is_final_cap, get_cap, tcb_release_remove "bound_tcb_at P t"
  (wp: mapM_x_wp_inv crunch_wps simp: crunch_simps)

lemma in_release_queue_ready_queues_update[simp]:
  "in_release_queue t (ready_queues_update f s) = in_release_queue t s"
  by (clarsimp simp: in_release_queue_def)

lemma set_tcb_sc_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update ref new \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma sched_context_donate_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> sched_context_donate scptr tcbptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_donate_def set_sc_obj_ref_def get_sc_obj_ref_def test_reschedule_def
               wp: weak_if_wp hoare_drop_imp)

lemma reply_remove_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> reply_remove rptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: get_simple_ko_wp)

lemma reply_cancel_ipc_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> reply_cancel_ipc p \<lbrace>\<lambda>rv. bound_tcb_at P t\<rbrace>"
  apply (wpsimp simp: reply_cancel_ipc_def reply_remove_tcb_def get_thread_state_def thread_get_def
                      thread_set_def set_object_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunch bound_tcb_at[wp]: cancel_ipc "bound_tcb_at P t"
(ignore: set_object thread_set wp: mapM_x_wp_inv maybeM_inv get_simple_ko_inv assert_inv)

lemma fast_finalise_bound_tcb_at:
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>tt. cap = ReplyCap tt) \<rbrace> fast_finalise cap final \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  apply (case_tac cap, simp_all)
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)
  done

lemma get_cap_reply_cap_helper:
  "\<lbrace>\<lambda>s. \<exists>t b. Some (ReplyCap t) = caps_of_state s slot \<rbrace> get_cap slot \<lbrace>\<lambda>rv s. \<exists>t. rv = ReplyCap t\<rbrace>"
  by (auto simp: valid_def get_cap_caps_of_state[symmetric])


lemma cap_delete_one_bound_tcb_at:
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>t b. caps_of_state s c = Some (ReplyCap t)) \<rbrace>
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
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def pred_tcb_at_def obj_at_def get_tcb_def)

lemma reply_unlink_tcb_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> reply_unlink_tcb r \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def
                      update_sk_obj_ref_def set_simple_ko_def get_object_def get_simple_ko_def
                      get_thread_state_def thread_get_def)
  apply (auto simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma blocked_cancel_ipc_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  by (wpsimp simp: blocked_cancel_ipc_def
               wp: set_thread_state_bound_sc_tcb_at reply_unlink_tcb_bound_sc_tcb_at
                   assert_inv get_simple_ko_inv hoare_drop_imps)

lemma cancel_signal_bound_sc_tcb_at[wp]:
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> cancel_signal r ntfn \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  by (wpsimp simp: cancel_signal_def get_simple_ko_def get_object_def
               wp: set_thread_state_bound_sc_tcb_at)

lemma suspend_unlive_helper:
  shows
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t and
    bound_yt_tcb_at ((=) yt_opt) t\<rbrace>
   maybeM (\<lambda>sc_ptr. do set_sc_obj_ref sc_yield_from_update sc_ptr None;
                       set_tcb_obj_ref tcb_yield_to_update t None
                    od) yt_opt
   \<lbrace>\<lambda>rv. bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t and
         bound_yt_tcb_at ((=) None) t\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def set_sc_obj_ref_def update_sched_context_def
                   get_object_def pred_tcb_at_def obj_at_def get_tcb_def)

lemma set_thread_state_not_live0:
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t
    and bound_yt_tcb_at ((=) None) t\<rbrace>
   set_thread_state t Inactive
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def obj_at_def pred_tcb_at_def get_tcb_def)

crunch obj_at[wp]: tcb_sched_action "\<lambda>s. P (obj_at Q p s)"

lemma obj_at_bound_yt_tcb_at_eq[simp]:
  "obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> bound_yt_tcb_at ((=) (tcb_yield_to tcb)) t s) t s
           = tcb_at t s"
  by (auto simp: obj_at_def pred_tcb_at_def is_tcb)

lemma obj_at_pred_tcb_at_peel:
  "obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> pred_tcb_at proj P t s \<and> Q t s tcb) t s
       = (pred_tcb_at proj P t s \<and> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> Q t s tcb) t s)"
  by (auto simp: obj_at_def pred_tcb_at_def)

crunch typ_at[wp]: cancel_ipc, reply_cancel_ipc "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps hoare_vcg_if_splitE select_wp maybeM_inv
     simp: crunch_simps unless_def)

crunch obj_at_not_live0[wp]: tcb_release_remove "obj_at (Not \<circ> live0) t"

lemma suspend_unlive:
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t
    and st_tcb_at (Not \<circ> awaiting_reply) t\<rbrace>
   suspend t
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  unfolding suspend_def
  apply_trace (wpsimp simp: suspend_def wp: set_thread_state_not_live0 suspend_unlive_helper gbn_wp)
    apply (simp add: cancel_ipc_def obj_at_pred_tcb_at_peel)
   apply (subst obj_at_pred_tcb_at_peel)+
   apply (wpsimp wp: blocked_cancel_ipc_bound_sc_tcb_at)
      apply (rule hoare_pre_cont)
     apply (wpsimp wp: cancel_signal_bound_sc_tcb_at tcb_at_typ_at cancel_ipc_typ_at gts_wp)+
  apply (clarsimp simp: st_tcb_at_tcb_at pred_tcb_at_def obj_at_def is_tcb)
  done

definition bound_refs_of_tcb :: "'a state \<Rightarrow> machine_word \<Rightarrow> (machine_word \<times> reftype) set"
where
  "bound_refs_of_tcb s t \<equiv> case kheap s t of
                              Some (TCB tcb) \<Rightarrow> get_refs TCBBound (tcb_bound_notification tcb)
                            | _ \<Rightarrow> {}"

crunches possible_switch_to
  for valid_irq_node[wp]: valid_irq_node
  (wp: crunch_wps simp: crunch_simps)

lemma cancel_all_invs_helper:
  "\<lbrace>all_invs_but_sym_refs
          and (\<lambda>s. (\<forall>x\<in>set q. ex_nonz_cap_to x s)
                  \<and> sym_refs (\<lambda>x. if x \<in> set q then
                                    {r \<in> state_refs_of s x. snd r = TCBBound \<or>
                                     snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                                  else state_refs_of s x)
                  \<and> sym_refs (\<lambda>x. state_hyp_refs_of s x)
                  \<and> valid_replies s
                  \<and> (\<forall>x\<in>set q. st_tcb_at (Not \<circ> (halted or awaiting_reply)) x s))\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                    possible_switch_to t od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2, fastforce)
  apply (wpsimp wp: valid_ioports_lift hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle
                    sts_st_tcb_at_cases sts_valid_replies
              cong: conj_cong)
  apply (clarsimp simp: valid_tcb_state_def, intro conjI)
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
  "\<lbrace>\<lambda>s. st_tcb_at P t s \<and> reply_tcb_reply_at (\<lambda>x. x \<noteq> Some t) rptr s\<rbrace>
   reply_unlink_tcb rptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: reply_unlink_tcb_def)
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_thread_state_def
                      thread_get_def st_tcb_at_def obj_at_def reply_tcb_reply_at_def
                  wp: sts_st_tcb_at_cases get_object_wp get_simple_ko_wp)
  done

lemma valid_objs_reply_not_tcbD:
  "valid_objs s \<Longrightarrow> kheap s tptr = Some (TCB tcb) \<Longrightarrow>
   tcb_state tcb = BlockedOnReceive epptr (Some rptr) \<Longrightarrow> \<not> tcb_at rptr s"
  by (fastforce simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_tcb is_reply obj_at_def)

lemma endpoint_reply_irrelevant:
  "st_tcb_at ((=) (BlockedOnReceive epptr (Some rptr))) tptr s
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

lemma set_thread_state_valid_irq_node[wp]:
  "set_thread_state t st \<lbrace> valid_irq_node \<rbrace>"
  by (wpsimp simp: valid_irq_node_def cap_table_at_typ wp: hoare_vcg_all_lift | wps)+

(* May be useful in limited circumstances:
   - when set_thread_state is the last step in reestablishing invariants.
   - when the thread is not previously BlockedOnReply. *)
lemma set_thread_state_invs:
  shows "\<lbrace> \<lambda>s. valid_tcb_state st s
               \<and> (\<not> halted st \<longrightarrow> ex_nonz_cap_to t s)
               \<and> (idle st \<longleftrightarrow> t = idle_thread s)
               \<and> (\<forall>r. (r,t) \<in> replies_blocked s \<longrightarrow> st = BlockedOnReply (Some r))
               \<and> sym_refs (\<lambda>p. if p = t
                                then tcb_st_refs_of st \<union> tcb_non_st_state_refs_of s t
                                else state_refs_of s p)
               \<and> sym_refs (state_hyp_refs_of s)
               \<and> all_invs_but_sym_refs s \<rbrace>
          set_thread_state t st
         \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: TcbAcc_AI.sts_only_idle sts_valid_replies)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def
                 elim!: replies_blocked_upd_tcb_st_valid_replies)
  done

lemma sts_st_tcb_at_cases_different_thread:
  "t' \<noteq> t \<Longrightarrow> set_thread_state t ts \<lbrace> \<lambda>s. P (st_tcb_at P' t' s) \<rbrace>"
  by (wpsimp wp: sts_st_tcb_at_cases_strong)

lemma cancel_all_ipc_invs_helper':
  "\<lbrace>all_invs_but_sym_refs and valid_replies and
     (\<lambda>s. (\<forall>x\<in>set q. ex_nonz_cap_to x s \<and> tcb_at x s
                     \<and> st_tcb_at (\<lambda>st. (\<exists>epptr ro. st = BlockedOnReceive epptr ro) \<or>
                                       (\<exists>epptr pl. st = BlockedOnSend epptr pl)) x s)
          \<and> distinct q
          \<and> sym_refs (\<lambda>x. if x \<in> set q
                          then {r \<in> state_refs_of s x. snd r \<noteq> TCBBlockedRecv \<and>
                                                       snd r \<noteq> TCBBlockedSend}
                          else state_refs_of s x)
          \<and> sym_refs (\<lambda>x. state_hyp_refs_of s x))\<rbrace>
    mapM_x (\<lambda>t. do st <- get_thread_state t;
                   reply_opt <- case st of BlockedOnReceive _ ro \<Rightarrow> return ro | _ \<Rightarrow> return None;
                   _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb (the reply_opt));
                   _ <- set_thread_state t Restart;
                   possible_switch_to t
                od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_cong[cong]
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2, fastforce, rename_tac t q')
  apply (rule_tac S="distinct (t # q')" in hoare_gen_asm'', simp)
  apply (rule hoare_conjI)
   apply (rule hoare_seq_ext[OF _ gts_sp], rename_tac st)
   apply (wpsimp wp: valid_ioports_lift sts_only_idle sts_valid_replies
                     reply_unlink_tcb_st_tcb_at_strong reply_unlink_tcb_valid_replies
               simp: valid_tcb_state_def pred_tcb_at_eq_commute)
   apply (rule_tac V="t \<noteq> idle_thread s" in revcut_rl, fastforce simp: idle_no_ex_cap)
   apply (clarsimp simp: reply_at_ppred_def pred_tcb_at_def obj_at_def)
   apply (erule disjE; clarsimp simp: reply_at_ppred_def pred_tcb_at_def obj_at_def)
    apply (rule conjI; clarsimp)
     apply (rule_tac V="r \<notin> insert t (set q')" in revcut_rl, fastforce)
     apply (drule_tac x=t and y=r and tp=ReplyTCB in sym_refsE
      ; clarsimp simp: state_refs_of_def get_refs_def2 refs_of_rev split: option.splits)
     apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp+)+
  apply (rule hoare_seq_ext[OF _ gts_sp], rename_tac st)
  (* To avoid case-splitting on st in the main proof, we'll isolate the one case
     that is interesting, and prove the remainder by extracting a smaller problem
     which is much easier to solve by cases on st. First, the simpler cases. *)
  apply (case_tac "\<forall>ep r. st \<noteq> BlockedOnReceive ep (Some r)"; clarsimp)
   apply (subst bind_assoc[symmetric])
   apply (rule_tac s="return ()" in ssubst[where P="\<lambda>a. \<lbrace>P\<rbrace> do _ <- a; _ <- b; c od \<lbrace>Q\<rbrace>" for P a b c Q])
    apply (case_tac st; fastforce)
   apply (wpsimp wp: hoare_vcg_ball_lift sts_st_tcb_at_cases_different_thread
                     reply_unlink_tcb_st_tcb_at_strong reply_unlink_tcb_refs_of
               simp: pred_tcb_at_eq_commute)
   apply (erule delta_sym_refs
          ; fastforce simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                    split: if_splits)
  (* now the interesting case *)
  apply (wpsimp wp: hoare_vcg_ball_lift sts_st_tcb_at_cases_different_thread
                    reply_unlink_tcb_st_tcb_at_strong reply_unlink_tcb_refs_of
              simp: pred_tcb_at_eq_commute)
  apply (intro conjI impI allI ballI
         ; clarsimp simp: reply_at_ppred_def pred_tcb_at_def obj_at_def is_tcb)
    apply (rename_tac t q' ep r s t' tcb reply)
    apply (rule_tac V="r \<notin> insert t (set q')" in revcut_rl, force)
    apply (drule_tac x=t and y=r and tp=ReplyTCB in sym_refsE
           ; fastforce simp: state_refs_of_def get_refs_def2)
   apply (erule delta_sym_refs
          ; fastforce simp: state_refs_of_def get_refs_def2
                     split: if_splits)
  apply (rename_tac t q' ep r s t' reply tcb, rule FalseE)
  apply (rule_tac V="r \<notin> insert t (set q')" in revcut_rl, force)
  by (drule_tac x=t and y=r and tp=ReplyTCB in sym_refsE
      ; fastforce simp: state_refs_of_def get_refs_def2)

lemma ep_list_tcb_at':
  "x \<in> set q
   \<Longrightarrow> valid_objs s \<and> (ko_at (Endpoint (SendEP q)) epptr s \<or> ko_at (Endpoint (RecvEP q)) epptr s)
   \<Longrightarrow> tcb_at x s"
  by (auto simp: valid_obj_def valid_ep_def obj_at_def)

lemma cancel_all_ipc_invs_helper:
  "ep = SendEP q \<or> ep = RecvEP q \<Longrightarrow>
   \<lbrace>ko_at (Endpoint ep) epptr and invs\<rbrace>
   do _ <- set_endpoint epptr IdleEP;
      _ <- mapM_x (\<lambda>t. do st <- get_thread_state t;
                          reply_opt <- case st of BlockedOnReceive _ ro \<Rightarrow> return ro
                                                                    | _ \<Rightarrow> return None;
                          _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb (the reply_opt));
                          _ <- set_thread_state t Restart;
                          possible_switch_to t
                       od) q;
      reschedule_required
   od
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (subst bind_assoc[symmetric])
  apply (rule hoare_seq_ext)
   apply wpsimp
  apply (rule hoare_pre)
   apply (wpsimp wp: valid_ioports_lift cancel_all_ipc_invs_helper' valid_irq_node_typ hoare_vcg_const_Ball_lift)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_ep_def live_def)
  apply (intro conjI, clarsimp, intro conjI)
      apply (drule (1) sym_refs_obj_atD)
      apply (clarsimp simp: obj_at_def)
      apply (erule disjE;
             fastforce intro!: refs_of_live elim!: if_live_then_nonz_capD2 dest!: bspec)
     apply (fastforce simp: valid_obj_def valid_ep_def elim!: obj_at_valid_objsE)
    apply (frule sym_refs_ko_atD, assumption)
    apply (fastforce simp: get_tcb_def tcb_st_refs_of_def get_refs_def2 is_tcb st_tcb_def2
                           valid_obj_def valid_ep_def
                    elim!: obj_at_valid_objsE
                    split: thread_state.splits if_splits)
   apply (fastforce simp: valid_obj_def valid_ep_def elim!: obj_at_valid_objsE)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp simp: if_splits)+
  apply (safe, (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def,
         (((drule ep_list_tcb_at', fastforce)+,
           fastforce dest!: tcb_state_refs_no_tcb)+)[2],
         ((drule ep_list_tcb_at', fastforce, clarsimp simp: obj_at_def is_tcb)+)[2],
         ((frule ep_list_tcb_at', fastforce,
           drule sym_refs_ko_atD[rotated], assumption, clarsimp,
           fastforce simp: obj_at_def state_refs_of_def is_tcb get_refs_def2
                           tcb_st_refs_of_def
                    split: thread_state.splits if_splits)+)[6],
         fastforce simp: state_refs_of_def obj_at_def)+)
  done


lemma cancel_all_ipc_invs:
  "\<lbrace>invs\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: get_ep_queue_def)
    apply (wp, fastforce)
   apply (auto simp: cancel_all_ipc_invs_helper)
  done

lemma cancel_all_ipc_st_tcb_at_helper':
  assumes x[simp]: "P Structures_A.Restart"
(*  notes hoare_pre [wp_pre del]*)
  shows
   "\<lbrace>\<lambda>s. st_tcb_at P t s \<and> distinct q \<and> valid_objs s
         \<and> (\<forall>x\<in>set q. st_tcb_at (\<lambda>st. (\<exists>epptr ro. st = BlockedOnReceive epptr ro) \<or>
                                       (\<exists>epptr pl. st = BlockedOnSend epptr pl)) x s)
         \<and> sym_refs (\<lambda>x. if x \<in> set q
                         then {r \<in> state_refs_of s x. snd r \<noteq> TCBBlockedRecv \<and>
                                                      snd r \<noteq> TCBBlockedSend}
                         else state_refs_of s x)\<rbrace>
   mapM_x (\<lambda>t. do st <- get_thread_state t;
                  reply_opt <- case st of BlockedOnReceive _ ro \<Rightarrow> return ro | _ \<Rightarrow> return None;
                  _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb (the reply_opt));
                  _ <- set_thread_state t Restart;
                  possible_switch_to t
                od) q
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  supply if_cong[cong]
  apply (rule mapM_x_inv_wp2[unfolded pred_conj_def], assumption)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac x, simp_all)
         defer 4
         defer 4
         apply ((wpsimp wp: hoare_pre_cont, fastforce simp: st_tcb_at_def obj_at_def)+)[6]
   apply (wpsimp wp: hoare_vcg_const_Ball_lift)
    apply (wpsimp wp: hoare_vcg_conj_lift hoare_vcg_const_Ball_lift sts_st_tcb_at_cases)
    apply (wpsimp wp: hoare_vcg_const_imp_lift reply_unlink_tcb_st_tcb_at')
    apply (wpsimp simp: valid_tcb_state_def wp: hoare_vcg_const_Ball_lift hoare_drop_imp reply_unlink_tcb_st_tcb_at')
    apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def
                        update_sk_obj_ref_def set_simple_ko_def get_object_def get_simple_ko_def
                        get_thread_state_def thread_get_def)
   apply (clarsimp, intro conjI, clarsimp, intro conjI)
      apply ((fastforce simp: reply_tcb_reply_at_def obj_at_def dest!: endpoint_reply_irrelevant)+)[2]
    apply (clarsimp, intro conjI, clarsimp+)
    apply (rule conjI; clarsimp)
     apply (((rule delta_sym_refs, assumption),
          (fastforce simp: state_refs_of_def dest!: get_tcb_SomeD split: if_splits),
          (frule endpoint_reply_irrelevant, assumption, fastforce,
           force simp: state_refs_of_def get_refs_def2 st_tcb_at_def obj_at_def
                      reply_tcb_reply_at_def
               dest!: get_tcb_SomeD
               split: if_splits))+)[2]
   apply (clarsimp simp: valid_tcb_state_def)
   apply (rule conjI, (fastforce simp: reply_tcb_reply_at_def obj_at_def dest!: endpoint_reply_irrelevant))
   apply (((rule delta_sym_refs, assumption),
          (fastforce simp: state_refs_of_def dest!: get_tcb_SomeD split: if_splits),
          (force simp: state_refs_of_def get_refs_def2 st_tcb_at_def obj_at_def
                      reply_tcb_reply_at_def
               dest!: get_tcb_SomeD
               split: if_splits))+)[1]
  apply (wpsimp wp: hoare_vcg_conj_lift hoare_vcg_const_Ball_lift sts_st_tcb_at_cases)
  apply (fastforce simp: valid_tcb_state_def state_refs_of_def obj_at_def get_refs_def2
                         st_tcb_at_def
                  elim!: delta_sym_refs
                  split: if_splits)
  done

lemma cancel_all_ipc_st_tcb_at_helper:
  assumes x[simp]: "P Structures_A.Restart"
  shows
  "ep = SendEP q \<or> ep = RecvEP q \<Longrightarrow>
   \<lbrace>\<lambda>s. ko_at (Endpoint ep) epptr s \<and> st_tcb_at P t s \<and> invs s\<rbrace>
   do _ <- set_endpoint epptr IdleEP;
      _ <- mapM_x (\<lambda>t. do st <- get_thread_state t;
                          reply_opt <- case st of BlockedOnReceive _ ro \<Rightarrow> return ro
                                                                    | _ \<Rightarrow> return None;
                          _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb (the reply_opt));
                          _ <- set_thread_state t Restart;
                          possible_switch_to t
                       od) q;
      reschedule_required
   od
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (wpsimp wp: cancel_all_ipc_st_tcb_at_helper' hoare_vcg_const_Ball_lift)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_ep_def)
  apply (intro conjI)
    apply (fastforce simp: valid_obj_def valid_ep_def elim!: obj_at_valid_objsE)
   apply (frule sym_refs_ko_atD, assumption)
   apply (fastforce simp: get_tcb_def tcb_st_refs_of_def get_refs_def2 is_tcb st_tcb_def2
                          valid_obj_def valid_ep_def
                   elim!: obj_at_valid_objsE
                   split: thread_state.splits if_splits)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp simp: if_splits)+
  apply (safe, (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def,
                (((drule ep_list_tcb_at', fastforce)+,
                  fastforce dest!: tcb_state_refs_no_tcb)+)[2],
                ((drule ep_list_tcb_at', fastforce, clarsimp simp: obj_at_def is_tcb)+)[2],
                ((frule ep_list_tcb_at', fastforce,
                  drule sym_refs_ko_atD[rotated], assumption, clarsimp,
                  fastforce simp: obj_at_def state_refs_of_def is_tcb get_refs_def2
                                  tcb_st_refs_of_def
                           split: thread_state.splits if_splits)+)[6],
                fastforce simp: state_refs_of_def obj_at_def)+)
  done

lemma cancel_all_ipc_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart"
  shows
  "\<lbrace>st_tcb_at P t and invs\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: get_ep_queue_def)
    apply (wp, fastforce)
   apply (auto simp: pred_conj_def cancel_all_ipc_st_tcb_at_helper)
  done

lemmas cancel_all_ipc_makes_simple[wp] =
  cancel_all_ipc_st_tcb_at[where P=simple, simplified]

lemma cancel_ipc_simple':
  "\<lbrace>st_tcb_at simple t' and invs\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  apply (wpsimp simp: cancel_ipc_def get_thread_state_def thread_get_def
               wp: blocked_ipc_st_tcb_at_general cancel_signal_st_tcb_at_general split: option.split)
  apply (clarsimp dest!: get_tcb_SomeD invs_sym_refs, drule sym_refs_ko_atD[rotated, where p=t])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: refs_of_rev obj_at_def)
  apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def)
  done

lemma cancel_ipc_simple_except_awaiting_reply:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace> cancel_ipc t
   \<lbrace>\<lambda>rv. st_tcb_at ((=) Running or (=) Inactive or (=) Restart or (=) IdleThreadState) t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; simp)
         prefer 8
         apply ((wpsimp simp: st_tcb_at_def obj_at_def)+)[4]
     apply ((rule hoare_strengthen_post[where Q = "\<lambda>s. st_tcb_at ((=) Inactive) t"], wpsimp,
             clarsimp simp: st_tcb_at_def obj_at_def)+)[4]
  done

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

lemma ntfn_bound_tcb_at:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
    ntfn_bound_tcb ntfn = Some tcbptr; P (Some ntfnptr)\<rbrakk>
  \<Longrightarrow> bound_tcb_at P tcbptr s"
  apply (drule_tac x=ntfnptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def is_tcb
                    state_refs_of_def refs_of_rev
          simp del: refs_of_simps
             elim!: valid_objsE)
  done

lemma bound_tcb_bound_notification_at:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
    bound_tcb_at (\<lambda>ptr. ptr = (Some ntfnptr)) tcbptr s \<rbrakk>
  \<Longrightarrow> ntfn_bound_tcb ntfn = Some tcbptr"
  apply (drule_tac x=tcbptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def pred_tcb_at_def obj_at_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def is_tcb
                    state_refs_of_def refs_of_rev
          simp del: refs_of_simps
             elim!: valid_objsE)
  done

lemma set_tcb_obj_ref_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node\<rbrace> set_tcb_obj_ref f t new \<lbrace>\<lambda>_. valid_irq_node\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def get_tcb_def
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

lemma set_ntfn_bound_tcb_none_if_live_then_nonz_cap [wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr None \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def obj_at_def wp: get_simple_ko_wp)
  apply (fastforce simp: live_def live_ntfn_def elim!: if_live_then_nonz_capD2)
  done

lemma unbind_notification_invs:
  notes refs_of_simps[simp del] if_cong[cong]
  shows "\<lbrace>invs\<rbrace> unbind_notification t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unbind_notification_def invs_def valid_state_def valid_pspace_def maybeM_def)
  apply (rule hoare_seq_ext [OF _ gbn_sp])
  apply (case_tac ntfnptr; clarsimp)
  apply wpsimp
  apply (wpsimp wp: valid_irq_node_typ set_simple_ko_valid_objs valid_ioports_lift get_simple_ko_wp split_del: if_split
              simp: update_sk_obj_ref_def)
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
  "\<lbrace>bound_tcb_at P t\<rbrace> cancel_all_signals param_a \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: cancel_all_signals_def get_simple_ko_def get_object_def wp: mapM_x_wp_inv)

lemma waiting_ntfn_list_tcb_at:
  "\<lbrakk>valid_objs s; ko_at (Notification ntfn) ntfnptr s; ntfn_obj ntfn = WaitingNtfn x\<rbrakk> \<Longrightarrow>
   \<forall>t \<in> set x. tcb_at t s"
  by (fastforce elim!: obj_at_valid_objsE simp:valid_obj_def valid_ntfn_def)

lemma cancel_all_signals_invs:
  "\<lbrace>invs\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp cancel_all_invs_helper set_simple_ko_valid_objs valid_irq_node_typ
             hoare_vcg_const_Ball_lift valid_ioports_lift
        | wpc
        | simp add: live_def)+
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (intro conjI)
      apply (clarsimp simp: valid_obj_def valid_ntfn_def elim!: obj_at_valid_objsE)
     apply (fastforce simp: live_def live_ntfn_def elim!: if_live_then_nonz_capD)
    apply (fastforce simp: st_tcb_at_refs_of_rev
                     dest: bspec sym_refs_ko_atD
                     elim: st_tcb_ex_cap)
   apply (rule delta_sym_refs, assumption)
    apply (fastforce simp: refs_of_ntfn_def state_refs_of_def obj_at_def
                    split: if_splits)
   apply (clarsimp split: if_splits)
     apply (fastforce simp: valid_obj_def valid_ntfn_def is_tcb_def
                     elim!: obj_at_valid_objsE)
    apply (rule conjI, clarsimp, rule conjI)
      apply (fastforce simp: valid_obj_def valid_ntfn_def is_tcb_def obj_at_def)
     apply (clarsimp simp: refs_of_ntfn_def get_refs_def2)
     apply (case_tac tp; simp)
     apply (clarsimp simp: valid_obj_def valid_ntfn_def
                    elim!: obj_at_valid_objsE)
     apply (fastforce simp: obj_at_def is_tcb_def is_sc_obj_def split: kernel_object.splits)
    apply (fastforce simp: get_refs_def2 st_tcb_at_refs_of_rev
                    dest!: bspec sym_refs_ko_atD st_tcb_at_state_refs_ofD)
   apply (clarsimp simp: refs_of_ntfn_def dest!: ko_at_state_refs_ofD)
  apply (fastforce elim!: ntfn_queued_st_tcb_at)
  done

lemma cancel_all_unlive_helper':
  "\<lbrace>obj_at (\<lambda>x. \<not> live x \<and> is_ep x) ptr\<rbrace>
   reply_unlink_tcb r \<lbrace>\<lambda>rv. obj_at (\<lambda>x. \<not> live x \<and> is_ep x) ptr\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def
                      update_sk_obj_ref_def set_simple_ko_def get_object_def get_simple_ko_def
                      get_thread_state_def thread_get_def obj_at_def)
  apply (fastforce simp: get_tcb_SomeD is_ep)
  done

crunch obj_at[wp]: possible_switch_to "\<lambda>s. P (obj_at Q p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma cancel_all_unlive_helper:
  "\<lbrace>obj_at (\<lambda>obj. \<not> live obj \<and> is_ep obj) ptr\<rbrace>
     mapM_x (\<lambda>t. do st <- get_thread_state t;
                    reply_opt <- case st of BlockedOnReceive _ ro \<Rightarrow> return ro | _ \<Rightarrow> return None;
                    _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb (the reply_opt));
                    _ <- set_thread_state t Restart;
                    possible_switch_to t
                 od) q
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (rule hoare_strengthen_post [OF mapM_x_wp'])
   apply (rule hoare_seq_ext[OF _ gts_sp])
   apply (wpsimp simp: is_ep wp: sts_obj_at_impossible cancel_all_unlive_helper')
  apply (clarsimp simp: obj_at_def)
  done

lemma cancel_all_ipc_unlive:
  "\<lbrace>\<top>\<rbrace> cancel_all_ipc ptr \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: set_simple_ko_def get_ep_queue_def)
    apply wp
    apply (clarsimp simp: live_def elim!: obj_at_weakenE)
   apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: more_update.obj_at_update)+
   apply (clarsimp simp: live_def is_ep)
  apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: more_update.obj_at_update)+
  apply (clarsimp simp: live_def is_ep)
  done

(* This lemma should be sufficient provided that each notification object is unbound BEFORE the
   'cancel_all_signals' function is invoked. TODO: Check the abstract specification and the C and
   Haskell implementations that this is indeed the case. *)
lemma cancel_all_signals_unlive[wp]:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None \<and>
                            ntfn_sc ntfn = None) ntfnptr s\<rbrace>
     cancel_all_signals ntfnptr
   \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ntfnptr\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp
        | wpc
        | simp add: unbind_maybe_notification_def)+
     apply (rule_tac Q="\<lambda>_. obj_at (is_ntfn and Not \<circ> live) ntfnptr" in hoare_post_imp)
      apply (fastforce elim: obj_at_weakenE)
     apply (wp mapM_x_wp' sts_obj_at_impossible
      | simp add: is_ntfn)+
    apply (wpsimp simp: set_simple_ko_def set_object_def get_object_def)
   apply wpsimp
  apply (auto simp: obj_at_def live_def live_ntfn_def)
  done

crunch cte_wp_at[wp]: cancel_all_ipc "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp)

crunch cte_wp_at[wp]: cancel_all_signals "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp thread_set_cte_wp_at_trivial
   simp: tcb_cap_cases_def)

lemma tcb_st_refs_of_TCBBlockedOnSend:
  "(ep, TCBBlockedSend) \<in> tcb_st_refs_of st \<longleftrightarrow> (\<exists>d. st = BlockedOnSend ep d)"
  by (cases st) auto

lemma cancel_badged_sends_filterM_helper':
  "\<forall>ys.
   \<lbrace>\<lambda>s. all_invs_but_sym_refs s
           \<and> valid_replies s
           \<and> sym_refs (state_hyp_refs_of s) \<and> distinct (xs @ ys) \<and> ep_at epptr s
           \<and> ex_nonz_cap_to epptr s
           \<and> sym_refs ((state_refs_of s) (epptr := ((set (xs @ ys)) \<times> {EPSend})))
           \<and> (\<forall>x \<in> set (xs @ ys). {r \<in> state_refs_of s x. snd r \<noteq> TCBBound \<and>
                                   snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
              = {(epptr, TCBBlockedSend)})\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> possible_switch_to t;
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_sym_refs s
            \<and> valid_replies s
            \<and> sym_refs (state_hyp_refs_of s)
            \<and> ep_at epptr s \<and> (\<forall>x \<in> set (xs @ ys). tcb_at x s)
            \<and> ex_nonz_cap_to epptr s
            \<and> (\<forall>y \<in> set ys. {r \<in> state_refs_of s y. snd r \<noteq> TCBBound \<and>
                             snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
               = {(epptr, TCBBlockedSend)})
            \<and> distinct rv \<and> distinct (xs @ ys) \<and> (set rv \<subseteq> set xs)
            \<and> sym_refs ((state_refs_of s) (epptr := ((set rv \<union> set ys) \<times> {EPSend})))\<rbrace>"
  supply if_cong[cong]
  apply (rule rev_induct[where xs=xs])
   apply (rule allI, simp)
   apply wp
   apply clarsimp
   apply (drule(1) bspec, drule singleton_eqD, clarsimp, drule state_refs_of_elemD)
   apply (clarsimp simp: st_tcb_at_refs_of_rev pred_tcb_at_def is_tcb
                  elim!: obj_at_weakenE)
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (wpsimp wp: valid_irq_node_typ sts_only_idle hoare_vcg_const_Ball_lift
                    valid_ioports_lift sts_valid_replies)
  apply (clarsimp simp: valid_tcb_state_def)
  apply (rule conjI[rotated])
   apply blast
  apply clarsimp
  apply (thin_tac "obj_at f epptr s" for f s)
  apply (thin_tac "tcb_at x s" for x s)
  apply (thin_tac "sym_refs (state_hyp_refs_of s)" for s)
  apply (frule singleton_eqD, clarify, drule state_refs_of_elemD)
  apply (frule (1) if_live_then_nonz_capD, rule refs_of_live, clarsimp)
  apply (clarsimp simp: st_tcb_at_refs_of_rev)
  apply (clarsimp simp: pred_tcb_def2 valid_idle_def)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp dest!: get_tcb_SomeD)
   apply (subst replies_blocked_upd_tcb_st_not_BlockedonReply, simp+)
  apply (rule conjI, force)
  apply (erule delta_sym_refs)
   apply (simp split: if_split_asm)
  apply (simp split: if_split_asm)
   apply fastforce
  apply (subgoal_tac "(y, tp) \<in> {r \<in> state_refs_of s x.
                      snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}")
   apply clarsimp
   apply fastforce
  apply fastforce
  done

lemmas cancel_badged_sends_filterM_helper
    = spec [where x=Nil, OF cancel_badged_sends_filterM_helper', simplified]

lemma cancel_badged_sends_invs[wp]:
  "\<lbrace>invs\<rbrace> cancel_badged_sends epptr badge \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_cong[cong]
  apply (simp add: cancel_badged_sends_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep; simp)
    apply wpsimp
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (wpsimp wp: valid_irq_node_typ valid_ioports_lift)
     apply (simp add: fun_upd_def[symmetric] ep_redux_simps ep_at_def2[symmetric, simplified]
                cong: list.case_cong)
  apply (rule hoare_strengthen_post,
            rule cancel_badged_sends_filterM_helper[where epptr=epptr])
     apply (auto intro:obj_at_weakenE)[1]
    apply (wpsimp wp: valid_irq_node_typ set_endpoint_ep_at valid_ioports_lift)
   apply (clarsimp simp: valid_ep_def conj_comms)
   apply (subst obj_at_weakenE, simp, clarsimp simp: is_ep_def)
   apply (clarsimp simp: is_ep_def)
   apply (frule(1) sym_refs_ko_atD, clarsimp)
   apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def)+)
   apply (erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ep_def st_tcb_at_refs_of_rev)
   apply (simp add: fun_upd_idem obj_at_def is_ep_def | subst fun_upd_def[symmetric])+
   apply (clarsimp, drule(1) bspec)
   apply (drule st_tcb_at_state_refs_ofD)
   apply (intro conjI)
    apply (fastforce simp: set_eq_subset)
   apply (fastforce simp: get_refs_def2)
  apply wpsimp
  done

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

lemma set_consumed_ex_nonz[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_consumed scptr args \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: set_consumed_def)

lemma set_tcb_yield_to_ex_nonz_cap_to[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update p' new
   \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

crunch st_tcb_at[wp]: set_consumed "st_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

crunch pred_tcb_at[wp]: set_consumed "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

lemma complete_yield_to_invs:
  "\<lbrace>invs\<rbrace> complete_yield_to tcb_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: complete_yield_to_def get_tcb_obj_ref_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac yt_opt; simp)
   apply wpsimp
  apply (rule hoare_seq_ext[OF _ lookup_ipc_buffer_inv])
  apply (rule hoare_seq_ext[OF _ assert_opt_inv])
  apply (rule hoare_seq_ext[rotated])
   apply (rule_tac Q="K (yt_opt = Some a) and
         (bound_yt_tcb_at ((=) (Some a)) tcb_ptr and
         (invs and ex_nonz_cap_to tcb_ptr))"
         in hoare_weaken_pre)
    apply (rule hoare_pre, rule hoare_vcg_conj_lift
      [OF set_consumed_pred_tcb_at[where proj=itcb_yield_to and t=tcb_ptr and P="(=) (Some _)"]
          hoare_vcg_conj_lift[OF set_consumed_invs
                                  set_consumed_ex_nonz]])
    apply (auto)[2]
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (drule (1) if_live_then_nonz_capD; clarsimp simp: live_def)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
      wp: sts_only_idle valid_irq_node_typ split_del: if_split)
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def split del: if_split)
   apply (rule pspace_valid_objsE, simp, simp)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def ran_tcb_cap_cases
                   split del: if_split)
   apply (drule sym, clarsimp simp: is_sc_obj_def obj_at_def split del: if_split)
   apply (case_tac ko; clarsimp split del: if_split)
   apply (rename_tac sc n)
   apply (subgoal_tac "sc_yield_from sc = Some tcb_ptr")
    apply (erule delta_sym_refs)
     apply (clarsimp split: if_split_asm simp: st_tcb_at_def)
    apply (clarsimp split: if_split_asm simp:  split del: if_split)
        apply ((fastforce simp: state_refs_of_def get_refs_def2 dest!: symreftype_inverse')+)[4]
   apply (fastforce dest!: sym_ref_tcb_yt)
  apply (clarsimp dest!: idle_no_ex_cap)
  done

end
