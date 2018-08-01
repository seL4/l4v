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

crunch  typ_at: cancel_all_ipc "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)

lemma cancel_all_helper:
  " \<lbrace>valid_objs and
    (\<lambda>s. \<forall>t \<in> set queue. st_tcb_at (\<lambda>st. \<not> halted st) t s) \<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) queue
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp [where S="set queue", simplified])
    apply (wp, simp, wp hoare_vcg_const_Ball_lift sts_st_tcb_at_cases, simp)
    apply (clarsimp elim: pred_tcb_weakenE)
    apply (erule(1) my_BallE)
    apply (clarsimp simp: st_tcb_def2)
    apply (frule(1) valid_tcb_objs)
    apply (clarsimp simp: valid_tcb_def valid_tcb_state_def
                          cte_wp_at_cases tcb_cap_cases_def
                   dest!: get_tcb_SomeD)
   apply simp+
  done


lemma set_thread_state_valid_objs_minorpre[wp]: (* FIXME: replace set_thread_state_valid_objs ? *)
 "\<lbrace>valid_objs and valid_tcb_state st\<rbrace>
  set_thread_state thread st
  \<lbrace>\<lambda>r. valid_objs\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp, simp, (wp set_object_valid_objs)+)
  apply (clarsimp simp: obj_at_def get_tcb_def
                 split: Structures_A.kernel_object.splits option.splits)
  apply (simp add: valid_objs_def dom_def)
  apply (erule allE, erule impE, blast)
  apply (simp add: valid_obj_def valid_tcb_def a_type_def tcb_cap_cases_def)
  done


lemma cancel_all_ipc_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_all_ipc ptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by (wpsimp simp: cancel_all_ipc_def valid_tcb_state_def get_thread_state_def thread_get_def
                   get_ep_queue_def get_simple_ko_def get_object_def valid_ep_def
               wp: mapM_x_wp_inv)

(*
lemma unbind_notification_valid_objs_helper:
  "valid_ntfn ntfn s \<longrightarrow> valid_ntfn (set_ntfn_obj_ref ntfn_bound_tcb_update ntfn None) s "
  by (clarsimp simp:  valid_ntfn_def
                  split: option.splits ntfn.splits)
*)

lemma get_ntfn_valid_ntfn_minor[wp]: (* FIXME: replace get_ntfn_valid_ntfn ? *)
  "\<lbrace> valid_objs \<rbrace>
   get_notification ntfn
   \<lbrace> valid_ntfn \<rbrace>"
  apply (wpsimp simp: get_simple_ko_def get_object_def wp_del: get_ntfn_valid_ntfn)
  apply (auto simp: valid_obj_def)
  done

lemma unbind_notification_valid_objs:
  "\<lbrace>valid_objs\<rbrace>
   unbind_notification ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: unbind_notification_def update_sk_obj_ref_def)
     apply (rule hoare_strengthen_post)
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
  "\<lbrace>st_tcb_at P t\<rbrace> unbind_notification t' \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: unbind_notification_def update_sk_obj_ref_def)

lemma unbind_maybe_notification_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> unbind_maybe_notification r \<lbrace>\<lambda>rv. st_tcb_at P t \<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def update_sk_obj_ref_def get_sk_obj_ref_def)


lemma cancel_all_signals_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
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
  "\<lbrace>st_tcb_at P t\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sk_obj_ref_def
               wp: get_simple_ko_wp)

lemma reply_remove_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t and
   reply_tcb_reply_at (\<lambda>ko. \<exists>t'. ko = Some t' \<and> (t = t' \<longrightarrow> P Inactive)) rptr\<rbrace>
   reply_remove rptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_remove_def reply_tcb_reply_at_def split_del: if_split cong: conj_cong
          wp: hoare_vcg_if_lift2 hoare_drop_imp reply_unlink_sc_st_tcb_at
              reply_unlink_tcb_st_tcb_at)

lemma set_thread_state_st_tcb_at:  (* FIXME: is the precondition necessary? *)
  "\<lbrace>\<lambda>s. st_tcb_at P t' s \<and> (t = t' \<longrightarrow> P st)\<rbrace> set_thread_state t st
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def pred_tcb_at_def obj_at_def)

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
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_maybe_unbind_ntfn ntfnptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
   by (wpsimp simp: sched_context_maybe_unbind_ntfn_def sched_context_unbind_ntfn_def
                    set_sc_obj_ref_def update_sk_obj_ref_def get_sc_obj_ref_def get_sk_obj_ref_def)

lemma sched_context_unbind_ntfn_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_unbind_ntfn scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_ntfn_def set_sc_obj_ref_def update_sk_obj_ref_def
                   get_sc_obj_ref_def)

lemma sched_context_update_consumed_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_update_consumed scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

lemma set_message_info_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_message_info a b \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
   by (wpsimp simp: set_message_info_def)

lemma complete_yield_to_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> complete_yield_to scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: complete_yield_to_def set_sc_obj_ref_def set_consumed_def get_sc_obj_ref_def
         wp: set_thread_state_st_tcb_at set_message_info_st_tcb_at hoare_drop_imp)

lemma sched_context_unbind_yield_from_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_unbind_yield_from scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_yield_from_def)


lemma sched_context_clear_replies_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_clear_replies scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_clear_replies_def reply_unlink_sc_def set_sc_obj_ref_def
                   update_sk_obj_ref_def
               wp: mapM_x_wp' hoare_drop_imp)

lemma sched_context_unbind_all_tcbs_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_unbind_all_tcbs scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def sched_context_unbind_tcb_def set_sc_obj_ref_def
               wp: hoare_drop_imp)



locale IpcCancel_AI =
    fixes state_ext :: "('a::state_ext) itself"
    assumes arch_post_cap_deletion_typ_at[wp]:
      "\<And>P T p. \<lbrace>\<lambda>(s :: 'a state). P (typ_at T p s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
    assumes arch_post_cap_deletion_idle_thread[wp]:
      "\<And>P. \<lbrace>\<lambda>(s :: 'a state). P (idle_thread s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"

crunch st_tcb_at_simple[wp]: reply_cancel_ipc "st_tcb_at simple t"
  (wp: crunch_wps select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state maybeM_inv
   simp: crunch_simps unless_def fast_finalise.simps)

lemma scyf_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_sc_obj_ref sc_yield_from_update sc tcb \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  apply (simp add: set_sc_obj_ref_def set_object_def)
  apply wp
  done

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
  by (wpsimp simp: unbind_maybe_notification_def)

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
crunches set_thread_state_ext
 for no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

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
  (simp: Let_def wp: hoare_drop_imps ignore: set_thread_state_ext)

lemma sc_at[wp]: "\<lbrace>sc_at sc_ptr\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. sc_at sc_ptr\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def set_simple_ko_def
            wp: set_object_wp hoare_drop_imp get_simple_ko_wp)
  by (clarsimp simp: obj_at_def is_sc_obj_def)

lemma valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def get_simple_ko_def
                      get_object_def)
  apply (auto simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_rev)
  done

lemma only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def update_sk_obj_ref_def
                   set_simple_ko_def get_object_def get_simple_ko_def get_thread_state_def
                   thread_get_def only_idle_def pred_tcb_at_def obj_at_def)

lemma zombie_final[wp]: "\<lbrace>zombies_final\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. zombies_final\<rbrace>"
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
                                else state_refs_of s a))
\<rbrace>
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

lemma blocked_cancel_ipc_invs:
  notes reply_unlink_tcb_iflive[wp del]
shows

  "\<lbrace>invs and st_tcb_at ((=) st) t and K (\<exists>x y. (st = BlockedOnSend x y \<and> r = None) \<or>
                                                (st = BlockedOnReceive x r))\<rbrace>
   blocked_cancel_ipc st t r \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (case_tac r)
   apply (simp add: blocked_cancel_ipc_def)
   apply (rule hoare_seq_ext [OF _ gbi_ep_sp])
   apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
   apply (rule hoare_seq_ext [OF _ get_epq_sp])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre, wp valid_irq_node_typ sts_only_idle)
    apply (simp add: valid_tcb_state_def)
    apply (wp valid_irq_node_typ)
   apply (subgoal_tac "ep \<noteq> Structures_A.IdleEP")
    apply (clarsimp simp: ep_redux_simps2 cong: if_cong)
    apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def)+)
    apply (frule ko_at_state_refs_ofD)
    apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def)
    apply (frule st_tcb_at_state_refs_ofD)
    apply (subgoal_tac "epptr \<notin> set (remove1 t queue)")
(*
     apply (case_tac ep, simp_all add: valid_ep_def)[1]
      apply (intro conjI)
       apply (clarsimp simp: get_refs_def2 tcb_st_refs_of_def  split: thread_state.splits)
        apply (drule equalityD1, blast)
       apply (drule equalityD1, blast)
      apply (clarsimp simp: get_refs_def2 tcb_st_refs_of_def  split: thread_state.splits)
  sorry
*)
     apply (case_tac ep, simp_all add: valid_ep_def)
      apply (fastforce simp: get_refs_def2 valid_idle_def pred_tcb_at_def obj_at_def
                      elim!: delta_sym_refs
                      split: if_splits)
     apply (fastforce simp: get_refs_def2 valid_idle_def pred_tcb_at_def obj_at_def
                     elim!: delta_sym_refs
                     split: if_splits)
    apply (fastforce simp: valid_ep_def obj_at_def is_tcb_def)
   apply clarsimp
  apply (simp add: blocked_cancel_ipc_def)
  apply (rule hoare_seq_ext [OF _ gbi_ep_sp])
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext [OF _ get_epq_sp])
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext)
   apply (wp sts_only_idle valid_irq_node_typ)
     apply (simp add: valid_tcb_state_def)
     apply (wp reply_unlink_tcb_refs_of)
    apply (wp assert_inv)
   apply (wp get_simple_ko_inv)
  apply wp
   apply (rule hoare_vcg_conj_lift)
    apply (wpsimp simp: set_simple_ko_def set_object_def get_object_def split_del: if_split)
   apply (wpsimp wp: valid_irq_node_typ)
  apply (clarsimp simp: obj_at_def split del: if_split)
  apply (erule disjE, drule sym_refs_st_tcb_atD, assumption)
   apply (clarsimp simp: obj_at_def)
  apply (intro conjI)
     apply (erule (1) valid_objsE)
     apply (clarsimp simp: valid_obj_def valid_ep_def split: endpoint.splits)
     apply (fastforce split: list.splits)
    apply (fastforce simp: if_live_then_nonz_cap_def obj_at_def live_def)
   apply (clarsimp simp: partial_inv_def split del: if_split)
   apply (rule delta_sym_refs, assumption)
    apply (clarsimp split: if_splits)
        apply (fastforce dest!: endpoint_state_refs_of_subset)+
   apply (clarsimp split: if_splits)
        apply (intro conjI, clarsimp simp: is_tcb obj_at_def dest!: st_tcb_at_tcb_at)
        apply (clarsimp, intro conjI,
               fastforce dest!: st_tcb_at_tcb_at tcb_at_no_sc_reply symreftype_inverse')
        apply (clarsimp, intro conjI, fastforce dest!: tcb_state_refs_no_tcb st_tcb_at_tcb_at)
        apply (clarsimp simp: state_refs_of_def split: option.splits if_splits)
         apply (clarsimp simp: tcb_at_typ obj_at_def dest!: st_tcb_at_tcb_at)
        apply (fastforce simp: ep_q_refs_of_def valid_obj_def valid_ep_def pred_tcb_at_def
                               get_refs_def2 tcb_st_refs_of_def
                        elim!: obj_at_valid_objsE
                        split: endpoint.splits list.splits thread_state.splits)
       apply (drule sym_refs_st_tcb_atD, assumption, clarsimp simp: obj_at_def get_refs_def2)+
    apply (clarsimp simp: state_refs_of_def get_refs_def2)
   apply (intro conjI, clarsimp simp: obj_at_def is_tcb dest!: st_tcb_at_tcb_at)
   apply (clarsimp simp: state_refs_of_def valid_obj_def valid_ep_def is_tcb obj_at_def
                         ep_q_refs_of_def
                  split: if_splits endpoint.splits list.splits)
    apply (fastforce simp: in_set_remove1[where b = t, symmetric])
   apply (subgoal_tac "y = t", simp)
   apply (rule ccontr, simp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def tcb_st_refs_of_def
                 dest!: idle_only_sc_refs
                 split: thread_state.splits)
  done


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

lemma sched_context_donate_hyp_refs_of [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def wp: get_sched_context_wp)

lemma sched_context_donate_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> tp \<noteq> idle_thread s \<and>
        sc_tcb_sc_at (\<lambda>x. x \<noteq> Some (idle_thread s)) scp s\<rbrace>
   sched_context_donate scp tp \<lbrace>\<lambda>s. valid_idle\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
                      get_object_def sc_tcb_sc_at_def obj_at_def)

lemma sched_context_donate_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. only_idle\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
                   get_object_def)

lemma sched_context_donate_valid_arch_state [wp]:
  "\<lbrace>valid_arch_state\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_arch_state\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
                   get_object_def)

lemma sched_context_donate_valid_irq_node [wp]:
  "\<lbrace>valid_irq_node\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_irq_node\<rbrace>"
  by (wp valid_irq_node_typ)

lemma sched_context_donate_valid_irq_states [wp]:
  "\<lbrace>valid_irq_states\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_irq_states\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_valid_machine_state [wp]:
  "\<lbrace>valid_machine_state\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_machine_state\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_valid_vspace_objs [wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_vspace_objs\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_valid_arch_caps [wp]:
  "\<lbrace>valid_arch_caps\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_arch_caps\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_valid_global_objs [wp]:
  "\<lbrace>valid_global_objs\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_global_objs\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_valid_kernel_mappings [wp]:
  "\<lbrace>valid_kernel_mappings\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_kernel_mappings\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_equal_kernel_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. equal_kernel_mappings\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_valid_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_asid_map\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_valid_global_vspace_mappings [wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace> sched_context_donate scp tp \<lbrace>\<lambda>s. valid_global_vspace_mappings\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

lemma sched_context_donate_cap_refs_respects_device_region [wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> sched_context_donate scp tp
   \<lbrace>\<lambda>s. cap_refs_respects_device_region\<rbrace>"
  by (wpsimp simp: sched_context_donate_def get_sc_obj_ref_def get_sched_context_def
               wp: get_object_wp)

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
                      get_thread_state_def thread_get_def)
  apply (auto simp: obj_at_def get_tcb_def)
  done

lemma sc_tcb_sc_at_update:
  "sc_tcb_sc_at P p (trans_state f s) = sc_tcb_sc_at P p s"
  by (clarsimp simp: sc_tcb_sc_at_def)

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

lemma reply_tcb_not_idle_thread_helper:
  "reply_tcb r = Some tp \<Longrightarrow>
   kheap s rp = Some (Reply r) \<Longrightarrow>
   sym_refs (state_refs_of s) \<Longrightarrow>
   (rp, TCBReply) \<in> state_refs_of s tp"
  by (fastforce simp: state_refs_of_def elim!: sym_refsE)

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

lemma reply_unlink_sc_refs_of:
  "\<lbrace>\<lambda>s. \<forall>sc n.
          kheap s scp = Some (SchedContext sc n) \<longrightarrow>
          P (\<lambda>a. if a = scp then
                   {r \<in> state_refs_of s a. snd r = SCNtfn \<or> snd r = SCTcb \<or> snd r = SCYieldFrom} \<union>
                   set (map (\<lambda>r. (r, SCReply)) (remove1 rp (sc_replies sc)))
                 else (if a = rp then {r \<in> state_refs_of s a. snd r = ReplyTCB}
                       else state_refs_of s a))\<rbrace>
   reply_unlink_sc scp rp
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def get_simple_ko_def get_object_def get_sched_context_def)
  apply (fastforce simp: state_refs_of_def get_refs_def2
                  elim!: rsubst[where P = P]
                  split: list.splits)
  done

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

lemma reply_unlink_tcb_invs_BlockedOnReply:
  "\<lbrace>\<lambda>s. invs s \<and> (\<exists>tptr. st_tcb_at (op = (BlockedOnReply (Some rptr))) tptr s)\<rbrace>
   reply_unlink_tcb rptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: reply_unlink_tcb_refs_of)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_splits)
  apply (fastforce simp: state_refs_of_def st_tcb_def2 tcb_st_refs_of_def obj_at_def get_refs_def2
                  dest!: get_tcb_ko_atD sym_refs_ko_atD
                  split: thread_state.splits if_splits)
  done

lemma reply_unlink_sc_sym_refs:
  "\<lbrace>\<lambda>s. invs s \<and> sym_refs (state_refs_of s)\<rbrace> reply_unlink_sc scp rp
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def get_simple_ko_def get_object_def get_sched_context_def)
  apply (rename_tac sc n reply)
  apply safe
   apply clarsimp
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_splits)
    apply (case_tac "sc_replies sc"; simp)
    apply (fastforce simp: state_refs_of_def get_refs_def2 image_def split: list.splits)
   apply (clarsimp simp: state_refs_of_def)
  apply (case_tac "sc_replies sc")
   apply (fastforce simp: state_refs_of_def get_refs_def2 split: if_splits)
  apply (fastforce simp: state_refs_of_def get_refs_def2 valid_obj_def valid_sched_context_def
                  split: if_splits list.splits)
  done

lemma reply_unlink_sc_invs:
  "\<lbrace>\<lambda>s. invs s\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: reply_unlink_sc_sym_refs)

lemma reply_remove_tcb_invs:
  "\<lbrace>invs\<rbrace> reply_remove_tcb t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: reply_remove_tcb_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac ts; simp)
  apply (rename_tac rp_op)
  apply (simp add: assert_opt_def2)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (simp add: reply_remove_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (simp add: assert_opt_def2)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac "hd replies = the rp_op \<and> caller_sc = None")
   defer
   apply (rule hoare_seq_ext[rotated])
    apply (wpsimp wp: reply_unlink_tcb_invs_BlockedOnReply)
    apply fastforce
   apply (rule hoare_seq_ext[rotated])
    apply (wpsimp wp: reply_unlink_sc_invs)
   apply wpsimp
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: sched_context_donate_refs_of)
    apply (rule hoare_vcg_conj_lift)
     apply (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sched_context_def
                         set_object_def get_object_def set_simple_ko_def get_simple_ko_def
                         get_sched_context_def)
    apply wpsimp
   apply wpsimp
   apply (rule hoare_vcg_conj_lift[rotated])
    apply wpsimp
   apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def)
          apply (simp only: trans_state_update[symmetric] more_update.state_refs_update
                            sc_tcb_sc_at_update more_update.pspace)
         apply (wpsimp simp: set_simple_ko_def set_object_def get_thread_state_def
                             thread_get_def obj_at_def
                         wp: get_object_wp get_simple_ko_wp)+
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (rename_tac t' scp)
  apply (subgoal_tac "t = t'")
   apply safe
         apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
        apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
        apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
        apply (fastforce simp: live_def live_sc_def elim!: if_live_then_nonz_capD2)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def)
       apply (fastforce simp: live_def elim!: if_live_then_nonz_capD2)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
     apply (rule delta_sym_refs, assumption)
      apply (fastforce simp: image_def state_refs_of_def get_tcb_def
                      dest!: get_tcb_SomeD
                      split: if_splits)
     apply (clarsimp split: if_splits)
        apply (fastforce simp: state_refs_of_def get_refs_def2 sc_tcb_sc_at_def obj_at_def
                        split: if_splits)
       apply (intro conjI)
        apply (erule (1) pspace_valid_objsE)
        apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
        apply (fastforce simp: valid_obj_def valid_sched_context_def tcb_at_def
                        dest!: tcb_state_refs_no_tcb[unfolded tcb_at_def, simplified])
       apply (fastforce simp: state_refs_of_def get_refs_def2 get_tcb_def obj_at_def
                              pred_tcb_at_def
                       dest!: get_tcb_SomeD
                       split: thread_state.splits)
      apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
      apply (fastforce simp: state_refs_of_def refs_of_rev
                      dest!: sc_tcb_not_idle_thread_helper
                      split: option.splits if_splits)
     apply (fastforce simp: state_refs_of_def get_refs_def2 valid_obj_def valid_sched_context_def
                     split: if_splits)
     apply (clarsimp simp: a_type_def partial_inv_def pred_tcb_at_def obj_at_def
      dest!: get_tcb_SomeD)
    apply (clarsimp simp: reply_tcb_not_idle_thread)
   apply (erule (1) pspace_valid_objsE)
   apply (clarsimp simp: sc_tcb_sc_at_def valid_reply_def sc_at_typ2 valid_obj_def obj_at_def
      sc_tcb_not_idle_thread)
  apply (fastforce simp: st_tcb_def2 tcb_st_refs_of_def obj_at_def
      dest!: get_tcb_ko_atD sym_refs_ko_atD
      split: thread_state.splits)
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

lemma blocked_cancel_ipc_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> blocked_cancel_ipc param_a param_b r
    \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: blocked_cancel_ipc_def set_thread_state_def reply_unlink_tcb_def
               wp: hoare_drop_imp)

crunch it[wp]: cancel_ipc "\<lambda>(s::'a state). P (idle_thread s)"
  (wp: maybeM_inv)
end

lemma sym_refs_bound_yt_tcb_at:
  "sym_refs (state_refs_of s) \<Longrightarrow> bound_yt_tcb_at (op = (Some sc)) t s \<Longrightarrow>
   (t', SCYieldFrom) \<in> state_refs_of s sc \<Longrightarrow>  t' = t"
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (frule sym_refs_ko_atD[unfolded obj_at_def, simplified], assumption)
  apply (clarsimp simp: state_refs_of_def refs_of_rev split: option.splits)
  apply (erule_tac x = "(sc, TCBYieldTo)" in ballE)
   apply (auto simp: get_refs_def2)
  done

lemma suspend_invs_helper:
  "\<lbrace>invs and st_tcb_at (op = Running or op = Inactive or op = Restart or op = IdleThreadState) t\<rbrace>
   do yt_opt <- get_tcb_obj_ref tcb_yield_to t;
      _ <- maybeM (\<lambda>sc_ptr. do y <- set_sc_obj_ref sc_yield_from_update sc_ptr None;
                               set_tcb_obj_ref tcb_yield_to_update t None
                            od) yt_opt;
      _ <- set_thread_state t Inactive;
      do_extended_op (tcb_sched_action tcb_sched_dequeue t)
   od
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gyt_sp])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: sts_only_idle valid_irq_node_typ maybeM_wp)
  apply (intro conjI | clarsimp)+
    apply (rule delta_sym_refs, assumption)
     apply (clarsimp split: if_splits)
    apply (clarsimp split: if_splits)
      apply ((fastforce simp: state_refs_of_def get_refs_def2 pred_tcb_at_def obj_at_def)+)[2]
    apply (clarsimp simp: sym_refs_bound_yt_tcb_at)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (clarsimp, intro conjI)
   apply (rule delta_sym_refs, assumption)
    apply (clarsimp split: if_splits)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                         tcb_st_refs_of_def
                  split: if_splits thread_state.splits)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (fastforce simp: live_def dest!: if_live_then_nonz_capD2 idle_no_ex_cap)
  done

lemma blocked_cancel_ipc_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. st_tcb_at (op = Inactive) t\<rbrace>"
  by (simp add: blocked_cancel_ipc_def | wp sts_st_tcb_at')+

lemma cancel_signal_inactive [wp]:
  "\<lbrace>\<top>\<rbrace> cancel_signal t ntfn \<lbrace>\<lambda>rv. st_tcb_at (op = Inactive) t\<rbrace>"
  by (simp add: cancel_signal_def | wp sts_st_tcb_at')+

lemma reply_unlink_tcb_inactive [wp]:
  "\<lbrace>reply_tcb_reply_at (\<lambda>x. x = Some t) r\<rbrace> reply_unlink_tcb r \<lbrace>\<lambda>rv. st_tcb_at (op = Inactive) t\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def update_sk_obj_ref_def
                      set_simple_ko_def get_object_def get_thread_state_def thread_get_def
                      reply_tcb_reply_at_def
                  wp: get_simple_ko_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma reply_remove_inactive [wp]:
  "\<lbrace>reply_tcb_reply_at (\<lambda>x. x = Some t) r\<rbrace> reply_remove r \<lbrace>\<lambda>rv. st_tcb_at (op = Inactive) t\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: get_simple_ko_wp wp_del: reply_remove_st_tcb_at)

lemma reply_remove_tcb_inactive [wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace> reply_remove_tcb t
   \<lbrace>\<lambda>rv. st_tcb_at (op = Inactive) t\<rbrace>"
  apply (wpsimp simp: reply_remove_tcb_def get_thread_state_def thread_get_def
                      reply_tcb_reply_at_def)
  apply (frule get_tcb_ko_atD)
  apply (frule (1) sym_refs_ko_atD)
  apply (clarsimp simp: obj_at_def)
  apply (fastforce simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_reply obj_at_def
                         get_refs_def2
                  elim!: valid_objsE)
  done

lemma reply_cancel_ipc_inactive [wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace> reply_cancel_ipc t
   \<lbrace>\<lambda>rv. st_tcb_at (op = Inactive) t\<rbrace>"
  apply (wpsimp simp: reply_cancel_ipc_def)
   apply (rule hoare_vcg_conj_lift)
    apply (wpsimp simp: thread_set_def set_object_def)
   apply (wpsimp simp: tcb_cap_cases_def wp: thread_set_valid_objs_triv)
  apply safe
  apply (rule delta_sym_refs, assumption)
   apply (auto simp: state_refs_of_def get_tcb_SomeD split: if_splits)
  done

lemma suspend_invs:
  notes hoare_pre [wp_pre del]
  shows
  "\<lbrace>invs\<rbrace> (suspend t :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: suspend_def)
  apply (wp suspend_invs_helper)
   apply (clarsimp simp: cancel_ipc_def)
   apply (rule hoare_seq_ext[OF _ gts_sp])
   apply (case_tac state; simp)
          apply ((wpsimp simp: st_tcb_at_def obj_at_def)+)[3]
       apply ((rule hoare_strengthen_post, wp, clarsimp simp: st_tcb_at_def obj_at_def)+)[2]
       apply (case_tac x6; simp)
       apply (wpsimp simp: pred_disj_def)+
     apply (rule hoare_strengthen_post, wp,
            clarsimp simp: invs_def valid_state_def valid_pspace_def,
            clarsimp simp: st_tcb_at_def obj_at_def)
    apply (rule hoare_strengthen_post, wp, clarsimp simp: st_tcb_at_def obj_at_def)
   apply (wpsimp simp: st_tcb_at_def obj_at_def)
  apply simp
  done

context IpcCancel_AI begin

lemma suspend_typ_at [wp]:
  "\<lbrace>\<lambda>(s::'a state). P (typ_at T p s)\<rbrace> suspend t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: suspend_def)


lemma suspend_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> suspend tcb \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)


lemma suspend_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> suspend t \<lbrace>\<lambda>rv. (tcb_at t')  :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

declare if_cong [cong del]


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

(* RT: FIXME move *)
crunch cte_wp_at[wp]: get_sched_context "cte_wp_at P c"

(* RT: FIXME move *)
lemma set_sc_yield_from_update_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_sc_obj_ref sc_yield_from_update t sc \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by wp

lemma (in delete_one_pre) suspend_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (suspend tcb :: (unit,'a) s_monad) \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>"
  by (simp add: suspend_def) (wpsimp wp: cancel_ipc_cte_wp_at_preserved)

lemma set_thread_state_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> set_thread_state p ts \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def set_object_def
  by (wpsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma reply_unlink_tcb_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> reply_unlink_tcb rptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def wp: hoare_drop_imp)

crunch bound_tcb_at[wp]: cancel_all_ipc, empty_slot, is_final_cap, get_cap "bound_tcb_at P t"
  (wp: mapM_x_wp_inv)

lemma reply_unlink_sc_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> reply_unlink_sc scptr replyptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sk_obj_ref_def
               wp: get_simple_ko_wp)

lemma sched_context_donate_bound_tcb_at [wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> sched_context_donate scptr tcbptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def set_tcb_obj_ref_def set_object_def
                      set_sc_obj_ref_def update_sched_context_def get_object_def
                      pred_tcb_at_def obj_at_def get_tcb_def get_sc_obj_ref_def
                  wp: get_sched_context_wp)
  apply auto
  done

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
  apply (wpsimp wp: hoare_drop_imps)
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

lemma set_thread_state_bound_sc_tcb_at:
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def pred_tcb_at_def obj_at_def get_tcb_def)

lemma reply_unlink_tcb_bound_sc_tcb_at:
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> reply_unlink_tcb r \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def
                      update_sk_obj_ref_def set_simple_ko_def get_object_def get_simple_ko_def
                      get_thread_state_def thread_get_def)
  apply (auto simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma blocked_cancel_ipc_bound_sc_tcb_at:
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  by (wpsimp simp: blocked_cancel_ipc_def
               wp: set_thread_state_bound_sc_tcb_at reply_unlink_tcb_bound_sc_tcb_at
                   assert_inv get_simple_ko_inv hoare_drop_imps)

lemma cancel_signal_bound_sc_tcb_at:
  "\<lbrace>bound_sc_tcb_at P t'\<rbrace> cancel_signal r ntfn \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  by (wpsimp simp: cancel_signal_def get_simple_ko_def get_object_def
               wp: set_thread_state_bound_sc_tcb_at)

lemma suspend_unlive_helper:
  notes hoare_pre [wp_pre del]
  shows
  "\<lbrace>bound_tcb_at (op = None) t and bound_sc_tcb_at (op = None) t and
    bound_yt_tcb_at (op = yt_opt) t\<rbrace>
   maybeM (\<lambda>sc_ptr. do _ <- set_sc_obj_ref sc_yield_from_update sc_ptr None;
                       set_tcb_obj_ref tcb_yield_to_update t None
                    od) yt_opt
   \<lbrace>\<lambda>rv. bound_tcb_at (op = None) t and bound_sc_tcb_at (op = None) t and
         bound_yt_tcb_at (op = None) t\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def set_sc_obj_ref_def update_sched_context_def
                   get_object_def pred_tcb_at_def obj_at_def get_tcb_def
               wp: maybeM_wp)

lemma set_thread_state_not_live0:
  "\<lbrace>bound_tcb_at (op = None) t and bound_sc_tcb_at (op = None) t
    and bound_yt_tcb_at (op = None) t\<rbrace>
   set_thread_state t Inactive
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def obj_at_def pred_tcb_at_def get_tcb_def)

lemma suspend_unlive:
  notes hoare_pre [wp_pre del]
  shows
  "\<lbrace>bound_tcb_at (op = None) t and bound_sc_tcb_at (op = None) t
    and st_tcb_at (Not \<circ> awaiting_reply) t\<rbrace>
   suspend t
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  apply (wpsimp simp: suspend_def)
     apply (wpsimp wp: set_thread_state_not_live0)
    apply (wpsimp wp: suspend_unlive_helper)
   apply (wpsimp simp: get_tcb_obj_ref_def thread_get_def)
  apply (wpsimp simp: pred_conj_def)
   apply (rule hoare_conjI)
    apply (simp add: cancel_ipc_def)
    apply (rule hoare_seq_ext[OF _ gts_sp])
    apply (simp add: pred_conj_def)
    apply (case_tac state; wpsimp)
       apply (wpsimp wp: blocked_cancel_ipc_bound_sc_tcb_at)+
     apply (wpsimp simp: st_tcb_at_def obj_at_def wp: hoare_pre_cont)
     apply (case_tac "tcb_state tcb"; simp)
    apply (wpsimp wp: cancel_signal_bound_sc_tcb_at)
   apply (rule hoare_strengthen_post)
    apply (wp hoare_TrueI)
   apply (auto simp: pred_tcb_at_def)
  done

definition bound_refs_of_tcb :: "'a state \<Rightarrow> machine_word \<Rightarrow> (machine_word \<times> reftype) set"
where
  "bound_refs_of_tcb s t \<equiv> case kheap s t of
                              Some (TCB tcb) \<Rightarrow> get_refs TCBBound (tcb_bound_notification tcb)
                            | _ \<Rightarrow> {}"

lemma bound_refs_of_tcb_trans:
  "bound_refs_of_tcb (trans_state f s) x = bound_refs_of_tcb s x"
  by (clarsimp simp:bound_refs_of_tcb_def trans_state_def)

lemma cancel_all_invs_helper:
  "\<lbrace>all_invs_but_sym_refs
          and (\<lambda>s. (\<forall>x\<in>set q. ex_nonz_cap_to x s)
                  \<and> sym_refs (\<lambda>x. if x \<in> set q then
                                    {r \<in> state_refs_of s x. snd r = TCBBound \<or>
                                     snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                                  else state_refs_of s x)
                  \<and> sym_refs (\<lambda>x. state_hyp_refs_of s x)
                  \<and> (\<forall>x\<in>set q. st_tcb_at (Not \<circ> (halted or awaiting_reply)) x s))\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2)
   apply wpsimp
  apply wp
    apply (simp add:bound_refs_of_tcb_trans)
   apply wp[1]
   apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle)
    apply (rule sts_st_tcb_at_cases)
   apply (auto simp: valid_tcb_state_def idle_no_ex_cap o_def if_split_asm
              elim!: rsubst[where P=sym_refs] st_tcb_weakenE
             intro!: ext)
  done

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
  "st_tcb_at (op = (BlockedOnReceive epptr (Some rptr))) tptr s
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

lemma cancel_all_ipc_invs_helper':
  notes hoare_pre [wp_pre del]
  shows
   "\<lbrace>all_invs_but_sym_refs and
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
                  do_extended_op (possible_switch_to t)
                od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2, clarsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac x, simp_all)
         defer 4
         defer 4
         apply ((wpsimp wp: hoare_pre_cont, fastforce simp: st_tcb_at_def obj_at_def)+)[6]
   apply (wpsimp wp: sts_only_idle valid_irq_node_typ hoare_vcg_const_Ball_lift)
     apply (rule sts_st_tcb_at_cases)
    apply wpsimp
   apply (rename_tac ro, case_tac ro)
    apply wpsimp
    apply (fastforce simp: valid_tcb_state_def idle_no_ex_cap state_refs_of_def obj_at_def
                           get_refs_def2 get_tcb_SomeD st_tcb_at_def tcb_st_refs_of_def
                           is_reply is_tcb
                    elim!: delta_sym_refs
                    split: if_splits thread_state.splits)
   apply (wpsimp simp: valid_tcb_state_def
                   wp: hoare_vcg_const_Ball_lift hoare_drop_imp reply_unlink_tcb_st_tcb_at')
    apply (wp hoare_vcg_conj_lift)
     apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def
                         update_sk_obj_ref_def set_simple_ko_def get_object_def get_simple_ko_def
                         get_thread_state_def thread_get_def)
    apply wpsimp
   apply (clarsimp, intro conjI)
     apply (clarsimp simp: idle_no_ex_cap)
    apply (fastforce simp: reply_tcb_reply_at_def obj_at_def dest!: endpoint_reply_irrelevant)
   apply (clarsimp simp: a_type_def partial_inv_def, intro conjI; clarsimp)
   apply (((rule delta_sym_refs, assumption),
           (fastforce simp: state_refs_of_def dest!: get_tcb_SomeD split: if_splits),
           (frule endpoint_reply_irrelevant, assumption, fastforce,
            force simp: state_refs_of_def get_refs_def2 st_tcb_at_def obj_at_def
                      reply_tcb_reply_at_def
                  dest!: get_tcb_SomeD
                  split: if_splits))+)[2]
  apply (wpsimp wp: sts_only_idle valid_irq_node_typ hoare_vcg_conj_lift hoare_vcg_const_Ball_lift)
    apply (rule sts_st_tcb_at_cases)
   apply wpsimp
  apply (fastforce simp: valid_tcb_state_def idle_no_ex_cap state_refs_of_def obj_at_def
      get_refs_def2 st_tcb_at_def
      elim!: delta_sym_refs
      split: if_splits)
  done

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
                          do_extended_op (possible_switch_to t)
                       od) q;
      do_extended_op reschedule_required
   od
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (subst bind_assoc[symmetric])
  apply (rule hoare_seq_ext)
   apply wpsimp
  apply (rule hoare_pre)
(*
   apply (wp cancel_all_invs_helper' hoare_vcg_const_Ball_lift valid_irq_node_typ valid_ioports_lift)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_ep_def live_def)
*)
apply (wpsimp wp: cancel_all_ipc_invs_helper' valid_irq_node_typ hoare_vcg_const_Ball_lift)
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
  notes hoare_pre [wp_pre del]
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
                  do_extended_op (possible_switch_to t)
                od) q
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (rule mapM_x_inv_wp2[unfolded pred_conj_def], assumption)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac x, simp_all)
         defer 4
         defer 4
         apply ((wpsimp wp: hoare_pre_cont, fastforce simp: st_tcb_at_def obj_at_def)+)[6]
   apply wpsimp
    apply (wpsimp wp: hoare_vcg_conj_lift hoare_vcg_const_Ball_lift sts_st_tcb_at_cases)
   apply (rename_tac ro, case_tac ro)
    apply (wpsimp simp: valid_tcb_state_def)
    apply (fastforce simp: state_refs_of_def obj_at_def get_refs_def2 st_tcb_at_def
                    elim!: delta_sym_refs
                    split: if_splits)
   apply (rule hoare_conjI)
    apply (case_tac "a = t", wpsimp)
    apply (wpsimp wp: reply_unlink_tcb_st_tcb_at')
     apply (fastforce simp: reply_tcb_reply_at_def obj_at_def dest!: endpoint_reply_irrelevant)
    apply simp
   apply (wpsimp simp: valid_tcb_state_def wp: hoare_vcg_conj_lift)
     apply (wpsimp wp: hoare_vcg_const_Ball_lift hoare_drop_imp reply_unlink_tcb_st_tcb_at')
    apply (wpsimp simp: reply_unlink_tcb_def set_thread_state_def set_object_def
                        update_sk_obj_ref_def set_simple_ko_def get_object_def get_simple_ko_def
                        get_thread_state_def thread_get_def)
   apply (clarsimp, intro conjI)
    apply (fastforce simp: reply_tcb_reply_at_def obj_at_def dest!: endpoint_reply_irrelevant)
   apply (clarsimp, intro conjI, clarsimp+)
   apply (rule conjI; clarsimp)
   apply (((rule delta_sym_refs, assumption),
          (fastforce simp: state_refs_of_def dest!: get_tcb_SomeD split: if_splits),
          (frule endpoint_reply_irrelevant, assumption, fastforce,
           force simp: state_refs_of_def get_refs_def2 st_tcb_at_def obj_at_def
                      reply_tcb_reply_at_def
               dest!: get_tcb_SomeD
               split: if_splits))+)[2]
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
                          do_extended_op (possible_switch_to t)
                       od) q;
      do_extended_op reschedule_required
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
   \<lbrace>\<lambda>rv. st_tcb_at (op = Running or op = Inactive or op = Restart or op = IdleThreadState) t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; simp)
         prefer 8
         apply ((wpsimp simp: st_tcb_at_def obj_at_def)+)[4]
     apply ((rule hoare_strengthen_post[where Q = "\<lambda>s. st_tcb_at (op = Inactive) t"], wpsimp,
             clarsimp simp: st_tcb_at_def obj_at_def)+)[4]
  done

lemma cancel_ipc_invs_st_tcb_at:
  "\<lbrace>invs\<rbrace> cancel_ipc t
   \<lbrace>\<lambda>rv. invs and st_tcb_at (op = Running or op = Inactive or op = Restart or
                             op = IdleThreadState) t\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def
               wp: cancel_ipc_simple_except_awaiting_reply)

lemma fast_finalise_misc:
"\<lbrace>st_tcb_at simple t and invs\<rbrace> fast_finalise a b \<lbrace>\<lambda>_. st_tcb_at simple t\<rbrace>"
  by (case_tac a; wpsimp wp: cancel_ipc_simple' get_simple_ko_wp)

lemma ntfn_q_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)

lemma ntfn_q_refs_no_TCBBound:
  "(x, TCBBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)

(*
lemma ntfn_bound_tcb_get_set[simp]:
  "ntfn_bound_tcb (set_ntfn_obj_ref ntfn_bound_tcb_update ntfn ntfn') = ntfn'"
  by auto

lemma ntfn_obj_tcb_get_set[simp]:
  "ntfn_obj (ntfn_set_bound_tcb ntfn ntfn') = ntfn_obj ntfn"
  by auto

lemma valid_ntfn_set_bound_None:
  "valid_ntfn ntfn s \<Longrightarrow> valid_ntfn (set_ntfn_obj_ref ntfn_bound_tcb_update ntfn None) s"
  by (auto simp: valid_ntfn_def split:ntfn.splits)
*)
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
  notes hoare_pre [wp_pre del] refs_of_simps[simp del]
  shows "\<lbrace>invs\<rbrace> unbind_notification t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unbind_notification_def invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext [OF _ gbn_sp])
(*
  apply (case_tac ntfnptr, clarsimp, wp, simp)
  apply clarsimp
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (wp valid_irq_node_typ set_simple_ko_valid_objs valid_ioports_lift
       | clarsimp split del: if_split)+
  apply (intro conjI impI;
    (match conclusion in "sym_refs r" for r \<Rightarrow> \<open>-\<close>
        | auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                       simp: live_def valid_ntfn_set_bound_None is_ntfn valid_obj_def
    )?)
*)
  apply (case_tac ntfnptr, clarsimp, wpsimp wp: maybeM_inv)
(*  apply clarsimp
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (wp valid_irq_node_typ set_simple_ko_valid_objs
       | clarsimp)+
          defer 5
          apply (auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                       simp: live_def valid_ntfn_set_bound_None is_ntfn valid_obj_def)[9]
  apply (clarsimp simp: if_split)
  apply (clarsimp simp: maybeM_def)
  apply (case_tac ntfnptr)
   apply wpsimp
  apply clarsimp
  apply (rule hoare_seq_ext)
   apply wp
  apply (rule hoare_weaken_pre)
   apply wpsimp
   apply (wpsimp simp: update_sk_obj_ref_def wp: valid_irq_node_typ get_simple_ko_wp)
  apply clarsimp
  apply safe
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (frule (1) sym_refs_obj_atD)
  apply (clarsimp simp: pred_tcb_at_def, frule (1) sym_refs_obj_atD)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm split del: if_split)
   apply (clarsimp simp: refs_of_def refs_of_ntfn_def)
  apply (clarsimp split: if_split_asm split del: if_split)
       apply (clarsimp simp: refs_of_def refs_of_tcb_def get_refs_def2 tcb_st_refs_of_def
                      split: thread_state.splits if_splits)
      apply (clarsimp simp: refs_of_ntfn_def get_refs_def2 ntfn_q_refs_of_def split: ntfn.splits)
     apply (clarsimp simp: refs_of_def refs_of_tcb_def get_refs_def2 tcb_st_refs_of_def
                    split: thread_state.splits if_splits)
    apply (fastforce simp: refs_of_def refs_of_ntfn_def get_refs_def2)
   apply (fastforce simp: refs_of_def refs_of_ntfn_def get_refs_def2 ntfn_q_refs_of_def
                   split: ntfn.splits)
  apply (clarsimp simp: refs_of_ntfn_def refs_of_def)
  apply (subgoal_tac "ntfn_bound_tcb ntfn = Some t")
   apply clarsimp
  apply (fastforce simp: pred_tcb_at_def obj_at_def elim!: bound_tcb_bound_notification_at)
  done

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

lemma cancel_all_unlive_helper:
  "\<lbrace>obj_at (\<lambda>obj. \<not> live obj \<and> is_ep obj) ptr\<rbrace>
     mapM_x (\<lambda>t. do st <- get_thread_state t;
                    reply_opt <- case st of BlockedOnReceive _ ro \<Rightarrow> return ro | _ \<Rightarrow> return None;
                    _ <- when (\<exists>r. reply_opt = Some r) (reply_unlink_tcb (the reply_opt));
                    _ <- set_thread_state t Restart;
                    do_extended_op (possible_switch_to t)
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

lemma cancel_badged_sends_filterM_helper':
  "\<forall>ys.
   \<lbrace>\<lambda>s. all_invs_but_sym_refs s  \<and> sym_refs (state_hyp_refs_of s) \<and> distinct (xs @ ys) \<and> ep_at epptr s
           \<and> ex_nonz_cap_to epptr s
           \<and> sym_refs ((state_refs_of s) (epptr := ((set (xs @ ys)) \<times> {EPSend})))
           \<and> (\<forall>x \<in> set (xs @ ys). {r \<in> state_refs_of s x. snd r \<noteq> TCBBound \<and>
                                   snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
              = {(epptr, TCBBlockedSend)})\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> do_extended_op (possible_switch_to t);
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_sym_refs s \<and> sym_refs (state_hyp_refs_of s)
            \<and> ep_at epptr s \<and> (\<forall>x \<in> set (xs @ ys). tcb_at x s)
            \<and> ex_nonz_cap_to epptr s
            \<and> (\<forall>y \<in> set ys. {r \<in> state_refs_of s y. snd r \<noteq> TCBBound \<and>
                             snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
               = {(epptr, TCBBlockedSend)})
            \<and> distinct rv \<and> distinct (xs @ ys) \<and> (set rv \<subseteq> set xs)
            \<and> sym_refs ((state_refs_of s) (epptr := ((set rv \<union> set ys) \<times> {EPSend})))\<rbrace>"
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
  apply (rule hoare_pre,
         wpsimp wp: valid_irq_node_typ sts_only_idle hoare_vcg_const_Ball_lift)
  apply (clarsimp simp: valid_tcb_state_def)
  apply (rule conjI[rotated])
   apply blast
  apply clarsimp
  apply (thin_tac "obj_at f epptr s" for f s)
  apply (thin_tac "tcb_at x s" for x s)
  apply (thin_tac "sym_refs (state_hyp_refs_of s)" for s)
  apply (frule singleton_eqD, clarify, drule state_refs_of_elemD)
  apply (frule(1) if_live_then_nonz_capD)
  apply (rule refs_of_live, clarsimp)
  apply (clarsimp simp: st_tcb_at_refs_of_rev)
  apply (clarsimp simp: pred_tcb_def2 valid_idle_def)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
  apply force
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
         (bound_yt_tcb_at (op = (Some a)) tcb_ptr and
         (invs and ex_nonz_cap_to tcb_ptr))"
         in hoare_weaken_pre)
    apply (wp hoare_vcg_conj_lift
      [OF set_consumed_pred_tcb_at[where proj=itcb_yield_to and t=tcb_ptr and P="op = (Some _)"]
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
