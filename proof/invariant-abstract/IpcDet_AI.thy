(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IpcDet_AI
imports
  "Lib.MonadicRewrite"
  "./$L4V_ARCH/ArchIpc_AI"
begin

context begin interpretation Arch .

requalify_consts
  make_arch_fault_msg

requalify_facts
  make_arch_fault_msg_invs
  make_arch_fault_msg_valid_replies

end

lemma replies_with_sc_kh_update_sc:
  "sc_replies (f sc v) = sc_replies sc
   \<Longrightarrow> replies_with_sc (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext (f sc v) n)\<rparr>)
       = replies_with_sc (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext sc n)\<rparr>)"
   by (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def,
       fastforce?)

lemma replies_blocked_kh_update_sc:
  "replies_blocked (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext (f sc v) n)\<rparr>)
   = replies_blocked (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext sc n)\<rparr>)"
   by (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def,
       fastforce?)

lemma replies_with_sc_kh_update_tcb:
  "replies_with_sc (s\<lparr>kheap := kheap s(p \<mapsto> TCB (f tcb v))\<rparr>)
   = replies_with_sc (s\<lparr>kheap := kheap s(p \<mapsto> TCB tcb)\<rparr>)"
   by (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def,
       fastforce?)

lemma replies_blocked_kh_update_tcb:
  "tcb_state (f tcb v) = tcb_state tcb
   \<Longrightarrow> replies_blocked (s\<lparr>kheap := kheap s(p \<mapsto> TCB (f tcb v))\<rparr>)
       = replies_blocked (s\<lparr>kheap := kheap s(p \<mapsto> TCB tcb)\<rparr>)"
   by (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def,
       fastforce?)

lemmas replies_with_sc_safe_kheap_updates[simp] =
       replies_with_sc_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_period := v\<rparr>", simplified]
       replies_with_sc_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_budget := v\<rparr>", simplified]
       replies_with_sc_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_refill_max := v\<rparr>", simplified]
       replies_with_sc_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_refills := v\<rparr>", simplified]
       replies_with_sc_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_badge := v\<rparr>", simplified]
       replies_with_sc_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_sporadic := v\<rparr>", simplified]
       replies_with_sc_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_consumed := v\<rparr>", simplified]
       replies_with_sc_kh_update_tcb[where f="\<lambda>sc v. sc\<lparr>tcb_arch := v\<rparr>"]

lemmas replies_blocked_safe_kheap_updates[simp] =
       replies_blocked_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_period := v\<rparr>"]
       replies_blocked_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_budget := v\<rparr>"]
       replies_blocked_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_refill_max := v\<rparr>"]
       replies_blocked_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_refills := v\<rparr>"]
       replies_blocked_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_badge := v\<rparr>"]
       replies_blocked_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_sporadic := v\<rparr>"]
       replies_blocked_kh_update_sc[where f="\<lambda>sc v. sc\<lparr>sc_consumed := v\<rparr>"]
       replies_blocked_kh_update_tcb[where f="\<lambda>sc v. sc\<lparr>tcb_arch := v\<rparr>", simplified]

lemma ko_at_kheap_upd_id[simp]:
  "ko_at ko p s \<Longrightarrow> (s\<lparr>kheap := kheap s(p \<mapsto> ko)\<rparr> = s)"
  unfolding obj_at_def fun_upd_def
  by (rule abstract_state.equality, rule ext; simp)

crunch typ_at[wp]: send_ipc "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps mapM_wp_inv maybeM_inv simp: crunch_simps)

lemma si_tcb_at [wp]:
  "\<And>t' call bl w d cd t ep.
    \<lbrace>tcb_at t'\<rbrace>
      send_ipc call bl w d gr cd t ep
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma handle_fault_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> handle_fault t f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: handle_fault_def unless_def handle_no_fault_def send_fault_ipc_def)

lemma hf_tcb_at [wp]:
  "\<And>t' t x.
    \<lbrace>tcb_at t'\<rbrace>
      handle_fault t x
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma sfi_tcb_at [wp]:
  "\<And>t tptr handler_cap fault can_donate.
    \<lbrace>tcb_at t\<rbrace>
      send_fault_ipc tptr handler_cap fault can_donate
    \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (wpsimp simp: send_fault_ipc_def)

lemma tcb_ep_find_index_wp:
  "\<lbrace>\<lambda>s. (\<forall>i j. 0 \<le> i \<and> i \<le> Suc sz \<longrightarrow>
               (\<forall>tcb tcba. ko_at (TCB tcb) tptr s \<and> ko_at (TCB tcba) (queue ! j) s \<longrightarrow>
                           (Suc j = i \<longrightarrow> tcb_priority tcba \<ge> tcb_priority tcb) \<longrightarrow>
                           (i < j \<and> j \<le> sz \<longrightarrow> tcb_priority tcba < tcb_priority tcb) \<longrightarrow> Q i s))\<rbrace>
   tcb_ep_find_index tptr queue sz \<lbrace>Q\<rbrace>"
  by (induct sz) (wp thread_get_wp' | simp add: tcb_ep_find_index.simps obj_at_def le_Suc_eq)+

lemma tcb_ep_append_valid_SendEP:
  "\<lbrace>valid_ep (SendEP (t#q)) and K (t \<notin> set q)\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>q'. valid_ep (SendEP q')\<rbrace>"
  apply (simp only: tcb_ep_append_def)
  apply (case_tac q; wpsimp wp: tcb_ep_find_index_wp)
  apply (fastforce simp: valid_ep_def set_take_disj_set_drop_if_distinct
                   dest: in_set_takeD in_set_dropD)
  done

lemma tcb_ep_append_valid_RecvEP:
  "\<lbrace>valid_ep (RecvEP (t#q)) and K (t \<notin> set q)\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>q'. valid_ep (RecvEP q')\<rbrace>"
  apply (simp only: tcb_ep_append_def)
  apply (case_tac q; wpsimp wp: tcb_ep_find_index_wp)
  apply (fastforce simp: valid_ep_def set_take_disj_set_drop_if_distinct
                   dest: in_set_takeD in_set_dropD)
  done

lemma tcb_ep_append_valid_ep:
  "\<lbrace>valid_ep (update_ep_queue ep (t#q)) and K (ep \<noteq> IdleEP \<and> t \<notin> set q)\<rbrace>
   tcb_ep_append t q
   \<lbrace>\<lambda>q'. valid_ep (update_ep_queue ep q')\<rbrace>"
  by (cases ep) (wpsimp wp: tcb_ep_append_valid_SendEP tcb_ep_append_valid_RecvEP)+

lemma tcb_ep_append_rv_wf:
  "\<lbrace>\<top>\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>rv s. set rv = set (t#q)\<rbrace>"
  apply (simp only: tcb_ep_append_def)
  apply (wp tcb_ep_find_index_wp)
  apply (auto simp: set_append[symmetric])
  done

lemma tcb_ep_append_rv_wf'[wp]:
  "\<lbrace>P (set (t#q))\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>rv. P (set rv)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid[OF _ tcb_ep_append_rv_wf], simp, simp)
  apply (frule use_valid[OF _ tcb_ep_append_inv, where P = "P (set (t#q))"], simp+)
  done

lemma tcb_ep_append_rv_wf''[wp]:
  "\<lbrace>P (ep_q_refs_of (SendEP (t#q)))\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>rv. P (ep_q_refs_of (SendEP rv))\<rbrace>"
  "\<lbrace>P (ep_q_refs_of (RecvEP (t#q)))\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>rv. P (ep_q_refs_of (RecvEP rv))\<rbrace>"
  by (simp only: ep_q_refs_of_def endpoint.case; rule tcb_ep_append_rv_wf')+

lemma tcb_ep_append_rv_wf''':
  "\<lbrace>P (ep_q_refs_of (update_ep_queue ep (t#q))) and K (ep \<noteq> IdleEP)\<rbrace>
   tcb_ep_append t q
   \<lbrace>\<lambda>rv. P (ep_q_refs_of (update_ep_queue ep rv))\<rbrace>"
  by (cases ep; wpsimp)

lemma tcb_ep_append_distinct[wp]:
  "\<lbrace>\<lambda>s. distinct q \<and> t \<notin> set q\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>q' s. distinct q'\<rbrace>"
  apply (simp only: tcb_ep_append_def)
  apply (wpsimp wp: tcb_ep_find_index_wp)
  apply (auto simp: set_take_disj_set_drop_if_distinct dest: in_set_dropD in_set_takeD)
  done

lemma tcb_ep_dequeue_valid_SendEP:
  "\<lbrace>valid_ep (SendEP q) and K (t \<in> set q)\<rbrace> tcb_ep_dequeue t q \<lbrace>\<lambda>q'. valid_ep (SendEP (t#q'))\<rbrace>"
  apply (case_tac q; simp)
  apply (wpsimp simp: tcb_ep_dequeue_def valid_ep_def)
  by (fastforce simp: findIndex_def findIndex'_app
                dest: in_set_takeD in_set_dropD findIndex_member)

lemma tcb_ep_dequeue_valid_RecvEP:
  "\<lbrace>valid_ep (RecvEP q) and K (t \<in> set q)\<rbrace> tcb_ep_dequeue t q \<lbrace>\<lambda>q'. valid_ep (RecvEP (t#q'))\<rbrace>"
  apply (case_tac q; simp)
  apply (wpsimp simp: tcb_ep_dequeue_def valid_ep_def)
  by (fastforce simp: findIndex_def findIndex'_app
                dest: in_set_takeD in_set_dropD findIndex_member)

lemma tcb_ep_dequeue_valid_ep:
  "\<lbrace>valid_ep (update_ep_queue ep q) and K (ep \<noteq> IdleEP \<and> t \<in> set q)\<rbrace>
   tcb_ep_dequeue t q
   \<lbrace>\<lambda>q'. valid_ep (update_ep_queue ep (t#q'))\<rbrace>"
  by (cases ep) (wpsimp wp: tcb_ep_dequeue_valid_SendEP tcb_ep_dequeue_valid_RecvEP)+

lemma tcb_ep_dequeue_rv_wf:
  "\<lbrace>\<lambda>_. t \<in> set q \<and> distinct q\<rbrace> tcb_ep_dequeue t q \<lbrace>\<lambda>rv s. set rv = set q - {t}\<rbrace>"
  apply (wpsimp simp: tcb_ep_dequeue_def)
  apply (fastforce dest: findIndex_member)
  done

lemma tcb_ep_dequeue_rv_wf':
  "\<lbrace>P (set q - {t}) and K (t \<in> set q \<and> distinct q)\<rbrace> tcb_ep_dequeue t q \<lbrace>\<lambda>rv. P (set rv)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid[OF _ tcb_ep_dequeue_rv_wf], simp, simp)
  apply (frule use_valid[OF _ tcb_ep_dequeue_inv, where P = "P (set q - {t})"], simp+)
  done

lemma tcb_ep_dequeue_rv_wf'':
  "\<lbrace>P (ep_q_refs_of (update_ep_queue ep q)) and K (t \<in> set q \<and> distinct q \<and> ep \<noteq> IdleEP)\<rbrace>
   tcb_ep_dequeue t q
   \<lbrace>\<lambda>rv. P (ep_q_refs_of (update_ep_queue ep (t#rv)))\<rbrace>"
  by (cases ep; wpsimp wp: tcb_ep_dequeue_rv_wf' simp: Times_Diff_distrib1 insert_absorb)

lemma gt_reply_sp:
  "\<lbrace>P\<rbrace> get_reply_obj_ref reply_tcb rptr
   \<lbrace>\<lambda>t s. (\<exists>r. kheap s rptr = Some (Reply r) \<and> reply_tcb r = t) \<and> P s\<rbrace>"
  apply (wpsimp simp: get_sk_obj_ref_def get_simple_ko_def get_object_def)
  apply auto
  done

lemma cancel_ipc_st_tcb_at_different_thread:
  "\<lbrace>\<lambda>s. st_tcb_at st t' s \<and> t \<noteq> t'\<rbrace>
   cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at st t'\<rbrace>"
  by (wpsimp wp: cancel_ipc_st_tcb_at)

lemma update_sk_obj_ref_valid_ep[wp]:
  "update_sk_obj_ref C f ref new \<lbrace> valid_ep ep \<rbrace>"
  by (rule valid_ep_typ, wp)

(* Taken from near the beginning of receive_ipc.
   We will prove some lemmas about this piece of code separately from the
   main receive_ipc proof, because we want to use case analysis here, but don't
   want to do the rest of the receive_ipc proof twice. *)
definition receive_ipc_preamble ::
  "cap \<Rightarrow> obj_ref \<Rightarrow> ('a::state_ext state, obj_ref option) nondet_monad"
  where
  "receive_ipc_preamble reply t \<equiv>
    case reply of NullCap \<Rightarrow> return None
                | ReplyCap r _ \<Rightarrow>
                    do tptr <- get_reply_tcb r;
                       when (tptr \<noteq> None \<and> the tptr \<noteq> t) $ cancel_ipc (the tptr);
                       return (Some r)
                    od
                | _ \<Rightarrow> fail"

crunches receive_ipc_preamble
  for invs: "invs"
  and caps_of_state: "\<lambda>s. P (caps_of_state s)"

lemma receive_ipc_preamble_st_tcb_at:
  "\<lbrace>\<lambda>s. P (st_tcb_at P' t s)\<rbrace> receive_ipc_preamble reply t \<lbrace>\<lambda>rv s. P (st_tcb_at P' t s)\<rbrace>"
  by (wpsimp simp: receive_ipc_preamble_def
               wp: cancel_ipc_st_tcb_at hoare_vcg_if_lift2 get_simple_ko_wp)

global_interpretation set_tcb_obj_ref: non_reply_op "set_tcb_obj_ref f ref new"
  apply unfold_locales
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (clarsimp simp: reply_at_ppred_def obj_at_def get_tcb_def
              split: option.splits kernel_object.splits)

global_interpretation set_tcb_obj_ref: non_ntfn_op "set_tcb_obj_ref f ref new"
  apply unfold_locales
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (clarsimp simp: ntfn_at_ppred_def obj_at_def get_tcb_def
              split: option.splits kernel_object.splits)

global_interpretation reply_unlink_tcb: non_reply_sc_op "reply_unlink_tcb t r"
  apply unfold_locales
  apply (wpsimp simp: reply_unlink_tcb_def wp: get_simple_ko_wp update_sk_obj_ref_wps gts_wp)
  by (auto simp: reply_sc_reply_at_def obj_at_def)

lemma reply_unlink_tcb_reply_tcb_reply_at:
  "\<lbrace> \<lambda>s. P (P' None) \<and> (p \<noteq> r \<longrightarrow> P (reply_tcb_reply_at P' p s)) \<rbrace>
    reply_unlink_tcb t r
   \<lbrace> \<lambda>rv s. P (reply_tcb_reply_at P' p s) \<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def wp: update_sk_obj_ref_wps get_simple_ko_wp gts_wp)
     (clarsimp simp: reply_tcb_reply_at_def obj_at_def)

lemma reply_remove_reply_tcb_reply_at:
  "\<lbrace> \<lambda>s. P (P' None) \<and> (p \<noteq> r \<longrightarrow> P (reply_tcb_reply_at P' p s)) \<rbrace>
    reply_remove t r
   \<lbrace> \<lambda>rv s. P (reply_tcb_reply_at P' p s) \<rbrace>"
  by (wpsimp simp: reply_remove_def
               wp: reply_unlink_tcb_reply_tcb_reply_at get_simple_ko_wp)

lemma get_blocking_object_wp:
  "\<lbrace> \<lambda>s. \<forall>ep. (\<exists>r d. st = BlockedOnReceive ep r d) \<or> (\<exists>d. st = BlockedOnSend ep d) \<longrightarrow> Q ep s \<rbrace>
    get_blocking_object st
   \<lbrace> Q \<rbrace>"
  by (cases st; wpsimp simp: get_blocking_object_def ep_blocked_def)

lemma reply_tcb_reply_at_kheap_update:
  "reply_tcb_reply_at P r (s\<lparr>kheap := kheap s(p \<mapsto> v)\<rparr>) =
    (if p = r then \<exists>r. v = Reply r \<and> P (reply_tcb r) else reply_tcb_reply_at P r s)"
  by (simp add: reply_tcb_reply_at_def obj_at_update)

lemma reply_tcb_reply_at_kheap_update':
  "p \<noteq> q \<Longrightarrow> reply_tcb_reply_at P r (s\<lparr>kheap := kheap s(p \<mapsto> v, q \<mapsto> w)\<rparr>) =
    (if p = r then \<exists>r. v = Reply r \<and> P (reply_tcb r)
     else if q = r then \<exists>r. w = Reply r \<and> P (reply_tcb r)
     else reply_tcb_reply_at P r s)"
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_update')

abbreviation reply_at_tcb_in ::
  "obj_ref set \<Rightarrow> obj_ref \<Rightarrow> 'a::state_ext state \<Rightarrow> bool"
  where
  "reply_at_tcb_in tcbs \<equiv> reply_tcb_reply_at (\<lambda>t. set_option t \<subseteq> tcbs)"

lemma cancel_ipc_reply_at_tcb_in:
  "\<lbrace>invs and reply_at_tcb_in (insert t tcbs) r\<rbrace>
    cancel_ipc t
   \<lbrace>\<lambda>rv. reply_at_tcb_in tcbs r\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (wpsimp simp: cancel_ipc_def blocked_cancel_ipc_def cancel_signal_def
                      reply_remove_tcb_def
                  wp: get_simple_ko_wp set_simple_ko_wps gts_wp get_ep_queue_wp get_sk_obj_ref_wp
                      get_blocking_object_wp reply_unlink_tcb_reply_tcb_reply_at thread_set_wp)
  apply (frule invs_valid_objs, drule invs_sym_refs)
  apply (intro conjI impI allI)
  (* 14 subgoals *)
  apply (all \<open>clarsimp simp: obj_at_update reply_tcb_reply_at_kheap_update pred_tcb_upd_apply
                             reply_tcb_reply_at_kheap_update'
                       cong: conj_cong
                      split: if_splits\<close>)
  apply (all \<open>(intro conjI)?\<close>)
  (* 21 subgoals *)
  apply (all \<open>clarsimp simp: reply_tcb_reply_at_def obj_at_def get_tcb_def
                             is_ep_def is_ntfn_def
                      split: option.splits kernel_object.splits\<close>)
  (* 14 subgoals *)
  apply (all \<open>frule (3) reply_tcb_state_refs\<close>)
  apply (all \<open>clarsimp simp: pred_tcb_at_def obj_at_def
                      dest!: sym[where t="tcb_state t" for t]\<close>)
  done

lemma get_notification_default_sp:
  "\<lbrace> P \<rbrace>
    case ptr_opt of None \<Rightarrow> return default_notification | Some p \<Rightarrow> get_notification p
   \<lbrace> \<lambda>rv. P and (case_option (\<lambda>s. rv = default_notification) (ko_at (Notification rv)) ptr_opt) \<rbrace>"
  by (wpsimp wp: get_simple_ko_wp)

lemma tcb_ep_append_not_null [wp]:
  "\<lbrace>\<top>\<rbrace> tcb_ep_append t q \<lbrace>\<lambda>rv _. rv \<noteq> []\<rbrace>"
  apply (simp only: tcb_ep_append_def)
  apply (wpsimp wp: tcb_ep_find_index_wp)
  done

definition receive_ipc_blocked ::
  "bool \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> receiver_payload \<Rightarrow> obj_ref list \<Rightarrow>
    ('a::state_ext state, unit) nondet_monad"
  where
  "receive_ipc_blocked is_blocking t ep_ptr reply pl queue \<equiv>
    case is_blocking of True \<Rightarrow> do _ <- set_thread_state t (BlockedOnReceive ep_ptr reply pl);
                                   _ <- when (\<exists>r. reply = Some r) (set_reply_obj_ref reply_tcb_update (the reply) (Some t));
                                   q <- tcb_ep_append t queue;
                                   set_endpoint ep_ptr (RecvEP q)
                                od
                      | False \<Rightarrow> do_nbrecv_failed_transfer t"

definition receive_ipc_idle ::
  "bool \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> receiver_payload \<Rightarrow> ('a::state_ext state, unit) nondet_monad"
  where
  "receive_ipc_idle is_blocking t ep_ptr reply pl \<equiv>
    case is_blocking of True \<Rightarrow> do _ <- set_thread_state t (BlockedOnReceive ep_ptr reply pl);
                                   _ <- when (\<exists>r. reply = Some r) (set_reply_obj_ref reply_tcb_update (the reply) (Some t));
                                   set_endpoint ep_ptr (RecvEP [t])
                                od
                      | False \<Rightarrow> do_nbrecv_failed_transfer t"

lemma monadic_rewrite_sort_queue_singleton:
  "monadic_rewrite False True (tcb_at t) (tcb_ep_append t []) (return [t])"
  proof -
    have rewrite_if:
      "\<And>e s n. (if \<exists>v. e = Some v then s else n) = (case e of None \<Rightarrow> n | Some v \<Rightarrow> s)"
        by fastforce
    show ?thesis
      by (simp add: monadic_rewrite_def tcb_ep_append_def mapM_def sequence_def thread_get_def
                    gets_the_def bind_assoc gets_def get_def get_tcb_def assert_opt_def
                    state_assert_def assert_def rewrite_if return_def fail_def tcb_at_def bind_def
             split: option.splits)
  qed

lemma monadic_rewrite_receive_ipc_idle:
  "monadic_rewrite False True (tcb_at t) (receive_ipc_blocked is_blocking t ep_ptr reply pl [])
                                         (receive_ipc_idle is_blocking t ep_ptr reply pl)"
  apply (cases is_blocking; simp add: receive_ipc_blocked_def receive_ipc_idle_def
                                      monadic_rewrite_imp[OF monadic_rewrite_refl])
  apply (rule monadic_rewrite_bind_tail[OF _ set_thread_state_tcb])
  apply (rule monadic_rewrite_bind_tail[where Q="\<lambda>_. tcb_at t", rotated], wpsimp)
  apply (subst return_bind[where x="[t]" and f="\<lambda>q. set_endpoint ep_ptr (RecvEP q)", symmetric])
  apply (rule monadic_rewrite_bind_head[OF monadic_rewrite_sort_queue_singleton])
  done

primrec receive_ipc_preamble_rv ::
  "cap \<Rightarrow> obj_ref option \<Rightarrow> 'a::state_ext state \<Rightarrow> bool"
  where
  "receive_ipc_preamble_rv reply None = (\<lambda>s. reply = NullCap)"
| "receive_ipc_preamble_rv reply (Some reply_ptr) =
    (\<lambda>s. (\<exists>R. reply = ReplyCap reply_ptr R) \<and> reply_tcb_reply_at (\<lambda>t. t = None) reply_ptr s
                                            \<and> reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr s)"

(* Preconditions for the guts of receive_ipc, after the reply preamble *)
abbreviation (input) receive_ipc_preconds ::
  "obj_ref \<Rightarrow> obj_ref \<Rightarrow> cap \<Rightarrow> obj_ref option \<Rightarrow> endpoint \<Rightarrow> ('a::state_ext state \<Rightarrow> bool)
    \<Rightarrow> 'a::state_ext state \<Rightarrow> bool"
  where
  "receive_ipc_preconds t ep_ptr reply reply_opt ep ex_invs \<equiv>
    \<lambda>s. st_tcb_at active t s
         \<and> ex_nonz_cap_to t s
         \<and> ex_nonz_cap_to ep_ptr s
         \<and> (\<forall>r\<in>zobj_refs reply. ex_nonz_cap_to r s)
         \<and> receive_ipc_preamble_rv reply reply_opt s
         \<and> ko_at (Endpoint ep) ep_ptr s
         \<and> ex_invs s"

lemma not_idle_thread':
  "valid_idle s \<Longrightarrow> st_tcb_at P t s \<Longrightarrow> (\<And>st. P st \<Longrightarrow> \<not> idle st) \<Longrightarrow> t \<noteq> idle_thread s"
  by (fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def)

lemma not_idle_thread:
  "valid_idle s \<Longrightarrow> st_tcb_at active t s \<Longrightarrow> t \<noteq> idle_thread s"
  by (erule (1) not_idle_thread'; fastforce)

lemma ko_at_Endpoint_ep_at:
  "ko_at (Endpoint ep) ep_ptr s \<Longrightarrow> ep_at ep_ptr s"
  by (fastforce elim!: obj_at_weakenE simp: is_ep_def)

lemma reply_tcb_reply_at_ReplyTCB_in_state_refs_of:
  "reply_tcb_reply_at P r_ptr s \<Longrightarrow> (t, ReplyTCB) \<in> state_refs_of s r_ptr \<Longrightarrow> P (Some t)"
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def state_refs_of_def get_refs_def
              split: option.splits)

lemma st_tcb_at_TCBReply_in_state_refs_of:
  "st_tcb_at P t s \<Longrightarrow> (r, TCBReply) \<in> state_refs_of s t \<Longrightarrow>
     P (BlockedOnReply r) \<or> (\<exists>ep pl. P (BlockedOnReceive ep (Some r) pl))"
  by (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2 tcb_st_refs_of_def
              split: thread_state.splits if_splits)

global_interpretation set_reply_tcb_obj_ref:
  non_reply_sc_op "set_reply_obj_ref reply_tcb_update ref new"
  by unfold_locales (wpsimp wp: update_sk_obj_ref_wp  simp: reply_sc_reply_at_def obj_at_def)

lemma receive_ipc_blocked_invs':
  assumes ep: "case ep of IdleEP \<Rightarrow> queue = [] | RecvEP q \<Rightarrow> queue = q | SendEP _ \<Rightarrow> False"
  shows "\<lbrace> receive_ipc_preconds t ep_ptr reply reply_opt ep invs \<rbrace>
          receive_ipc_blocked is_blocking t ep_ptr reply_opt pl queue
         \<lbrace> \<lambda>rv. invs \<rbrace>"
  proof -
    have ep_valid:
      "\<And>s. invs s \<Longrightarrow> st_tcb_at active t s \<Longrightarrow> ko_at (Endpoint ep) ep_ptr s
            \<Longrightarrow> (\<forall>t \<in> set queue. tcb_at t s) \<and> distinct queue \<and> t \<notin> set queue"
      using ep
      apply (cases ep; clarsimp)
      apply (frule invs_valid_objs, erule valid_objsE, simp add: obj_at_def)
      apply (clarsimp simp add: valid_obj_def valid_ep_def)
      by (fastforce dest!: ep_queued_st_tcb_at[where P="is_blocked_on_send or is_blocked_on_receive"]
                     simp: ep_q_refs_of_def invs_valid_objs invs_sym_refs pred_tcb_at_def obj_at_def)+
    have ep_queue:
      "ep_q_refs_of ep = set queue \<times> {EPRecv}"
      using ep by (cases ep; clarsimp simp: ep_q_refs_of_def)
    show ?thesis
      apply (cases reply_opt)
       apply (all \<open>wpsimp wp: valid_irq_node_typ sts_only_idle set_endpoint_invs hoare_vcg_ball_lift
                              sts_valid_replies valid_ioports_lift sts_fault_tcbs_valid_states
                        simp: receive_ipc_blocked_def valid_ep_def do_nbrecv_failed_transfer_def\<close>)
       apply (all \<open>clarsimp simp: ep_valid\<close>)
       apply (all \<open>clarsimp simp: invs_def valid_state_def valid_pspace_def st_tcb_at_tcb_at
                                  valid_tcb_state_def not_idle_thread
                                  ko_at_Endpoint_ep_at reply_tcb_reply_at\<close>)
       apply (all \<open>apply_conjunct \<open>rule replies_blocked_upd_tcb_st_valid_replies_not_blocked\<close>
                                   , assumption
                                   , fastforce simp: replies_blocked_def st_tcb_at_def obj_at_def\<close>)
       apply (all \<open>rule revcut_rl[where V="ep_ptr \<noteq> t"], fastforce simp: obj_at_def pred_tcb_at_def\<close>)
       apply (all \<open>(match premises in \<open>reply = ReplyCap r_ptr R\<close> for r_ptr R \<Rightarrow>
                     \<open>rule revcut_rl[where V="r_ptr \<notin> {t, ep_ptr}"]\<close>
                   , fastforce simp: obj_at_def reply_tcb_reply_at_def pred_tcb_at_def)?\<close>)
       apply (all \<open>frule obj_at_state_refs_ofD; clarsimp simp: ep_queue\<close>)
       apply (all \<open>frule(1) fault_tcbs_valid_states_active\<close>)
       apply (all \<open>drule active_st_tcb_at_state_refs_ofD; drule st_tcb_at_ko_atD\<close>)
       apply (all \<open>clarsimp simp: tcb_non_st_state_refs_of_state_refs_of
                            cong: if_cong\<close>)
       apply (all \<open>erule delta_sym_refs
                   ; fastforce dest: reply_tcb_reply_at_ReplyTCB_in_state_refs_of
                              split: if_splits\<close>)
      done
  qed

lemma receive_ipc_idle_invs:
  "\<lbrace> receive_ipc_preconds t ep_ptr reply reply_opt IdleEP invs \<rbrace>
    receive_ipc_idle is_blocking t ep_ptr reply_opt pl
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  apply (rule hoare_weaken_pre, rule monadic_rewrite_refine_valid[where P''=\<top>])
  apply (rule monadic_rewrite_receive_ipc_idle)
  apply (rule receive_ipc_blocked_invs'[where ep=IdleEP and reply=reply])
  by (auto simp: st_tcb_at_tcb_at)

lemmas receive_ipc_blocked_invs =
  receive_ipc_blocked_invs'[where ep="RecvEP queue" and queue=queue for queue, simplified]
  receive_ipc_idle_invs

lemma (in non_reply_op) non_reply_receive_ipc_preamble_rv[wp]:
  "f \<lbrace>receive_ipc_preamble_rv reply reply_opt\<rbrace>"
  by (cases reply_opt; wpsimp)

global_interpretation as_user: tcb_op "as_user t f"
  apply unfold_locales
  apply (wpsimp simp: as_user_def wp: set_object_wp simp: obj_at_def get_tcb_ko_at)
  by (erule_tac P=P in bool_to_boolE; fastforce simp: tcb_agnostic_pred_def)

global_interpretation set_message_info: tcb_op "set_message_info t f"
  by (simp add: set_message_info_def) unfold_locales

global_interpretation copy_mrs: tcb_op "copy_mrs sender sbuf receiver rbuf n"
  by unfold_locales (wpsimp simp: copy_mrs_def wp: mapM_wp' as_user.tcb_agnostic_obj_at)

global_interpretation set_mrs: tcb_op "set_mrs thread buf msgs"
  apply unfold_locales
  apply (wpsimp simp: set_mrs_def wp: zipWithM_x_inv' set_object_wp)
  by (erule_tac P=P in bool_to_boolE;
      fastforce simp: tcb_agnostic_pred_def obj_at_def get_tcb_ko_at split: if_splits)

global_interpretation transfer_caps_loop:
  cspace_op "transfer_caps_loop ep rcv_buffer n cap_slots slots mi"
  by unfold_locales (rule transfer_caps_loop_cspace_agnostic_obj_at)

global_interpretation transfer_caps:
  tcb_cspace_op "transfer_caps info caps endpoint receiver recv_buffer"
  by unfold_locales (wpsimp simp: transfer_caps_def
                              wp: transfer_caps_loop.tcb_cspace_agnostic_obj_at)

global_interpretation do_normal_transfer:
  tcb_cspace_op "do_normal_transfer sender sbuf endpoint badge grant receiver rbuf"
  by unfold_locales (wpsimp simp: do_normal_transfer_def
                              wp: transfer_caps.tcb_cspace_agnostic_obj_at
                                  as_user.tcb_cspace_agnostic_obj_at
                                  set_message_info.tcb_cspace_agnostic_obj_at
                                  copy_mrs.tcb_cspace_agnostic_obj_at)

global_interpretation get_sched_context: non_reply_op "get_sched_context ptr"
  by unfold_locales wpsimp

global_interpretation sched_context_update_consumed:
  non_reply_op "sched_context_update_consumed sc_ptr"
  by unfold_locales (wpsimp simp: sched_context_update_consumed_def)

global_interpretation make_arch_fault_msg: non_reply_op "make_arch_fault_msg f t"
  by unfold_locales (rule sk_obj_at_pred_valid_lift, rule make_arch_fault_msg_obj_at)

global_interpretation make_fault_msg: non_reply_op "make_fault_msg fault t"
  by unfold_locales (cases fault; wpsimp split_del: if_split)

global_interpretation do_fault_transfer: non_reply_op "do_fault_transfer badge sender receiver buf"
  by unfold_locales (wpsimp simp: do_fault_transfer_def thread_get_def)

global_interpretation do_ipc_transfer: non_reply_op "do_ipc_transfer sender ep badge grant receiver"
  by unfold_locales (wpsimp simp: do_ipc_transfer_def)

global_interpretation get_sched_context: non_sc_op "get_sched_context ptr"
  by unfold_locales wpsimp

lemma make_fault_msg_ko_at_Endpoint[wp]:
  "make_fault_msg f sender \<lbrace>\<lambda>s. P (ko_at (Endpoint ep) p s)\<rbrace>"
  by (cases f;
      wpsimp simp: tcb_agnostic_pred_def sched_context_update_consumed_def update_sched_context_def
               wp: as_user.tcb_agnostic_obj_at set_object_wp get_object_wp
        split_del: if_split;
      clarsimp simp: obj_at_def)

lemma do_fault_transfer_ko_at_Endpoint[wp]:
  "do_fault_transfer badge sender receiver buf \<lbrace> \<lambda>s. P (ko_at (Endpoint ep) p s) \<rbrace>"
  by (wpsimp simp: do_fault_transfer_def tcb_agnostic_pred_def thread_get_def
               wp: as_user.tcb_agnostic_obj_at
                   set_message_info.tcb_agnostic_obj_at
                   set_mrs.tcb_agnostic_obj_at)

lemma do_ipc_transfer_ko_at_Endpoint[wp]:
  "do_ipc_transfer sender ep_ptr badge grant receiver \<lbrace> \<lambda>s. P (ko_at (Endpoint ep) p s) \<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def tcb_cspace_agnostic_pred_def
               wp: do_normal_transfer.tcb_cspace_agnostic_obj_at)

lemma do_ipc_transfer_valid_irq_node[wp]:
  "do_ipc_transfer sender ep_ptr badge grant receiver \<lbrace> valid_irq_node \<rbrace>"
  by (wpsimp simp: valid_irq_node_def cap_table_at_typ wp: hoare_vcg_all_lift | wps)+

lemma TCBBlockedSend_in_state_refs_of:
  assumes "(ep, TCBBlockedSend) \<in> state_refs_of s t"
  shows "\<exists>data. st_tcb_at ((=) (BlockedOnSend ep data)) t s"
  using assms
  by (clarsimp simp: state_refs_of_def refs_of_def get_refs_def2 tcb_st_refs_of_def
                     pred_tcb_at_def obj_at_def
              split: option.splits kernel_object.splits thread_state.splits if_splits)

lemma TCBBlockedSend_in_state_refs_of_unique:
  assumes sr: "(ep, TCBBlockedSend) \<in> state_refs_of s t"
  assumes st: "st_tcb_at ((=) (BlockedOnSend ep' data)) t s"
  shows "ep' = ep"
  using TCBBlockedSend_in_state_refs_of[OF sr] st
  by (clarsimp simp: pred_tcb_at_def obj_at_def dest!: sym[where t="tcb_state t" for t])

lemma pred_tcb_at_state_refs_ofD:
  assumes "pred_tcb_at proj P t s"
  shows "\<exists>tcb. P (proj (tcb_to_itcb tcb)) \<and> state_refs_of s t = refs_of_tcb tcb"
  using assms by (auto simp: pred_tcb_at_def dest!: obj_at_state_refs_ofD)

lemma pred_tcb_at_eq_state_refs_ofD:
  assumes "pred_tcb_at proj ((=) v) t s"
  shows "\<exists>tcb. proj (tcb_to_itcb tcb) = v \<and> state_refs_of s t = refs_of_tcb tcb"
  using pred_tcb_at_state_refs_ofD[OF assms] by auto

lemma si_blk_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t')\<rbrace>
   send_ipc True call bdg x can_reply_grant can_donate t' epptr
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac ep; simp)
    apply (wpsimp wp: sts_st_tcb_at_cases)
   apply (wpsimp wp: sts_st_tcb_at_cases)
  apply (rule hoare_gen_asm[simplified])
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rule hoare_seq_ext [OF _ set_simple_ko_pred_tcb_at])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  supply maybeM_inv[wp]
  apply (wpsimp wp: sts_st_tcb_at_cases hoare_drop_imp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (case_tac "tcb_state tcb"; simp)
  done

lemma sfi_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t')\<rbrace>
   send_fault_ipc t' handler_cap ft can_donate
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: send_fault_ipc_def)
  apply (case_tac handler_cap; simp)
   apply wpsimp
  apply (wpsimp simp: thread_set_def wp: si_blk_makes_simple set_object_wp)
  apply (auto simp: st_tcb_at_def obj_at_def)
  done

lemma hf_makes_simple:
  notes hoare_pre [wp_pre del]
  shows
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t')\<rbrace>
     handle_fault t ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  apply (simp add: handle_fault_def handle_no_fault_def send_fault_ipc_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: sts_st_tcb_at_cases si_blk_makes_simple
                     thread_set_no_change_tcb_state)
  apply clarsimp
  done

lemma grt_sp:
  "\<lbrace>P\<rbrace> get_reply_tcb reply_ptr \<lbrace>\<lambda>rv. reply_tcb_reply_at (\<lambda>x. x = rv) reply_ptr and P\<rbrace>"
  apply (wpsimp simp: get_simple_ko_def get_object_def)
  apply (auto simp: reply_tcb_reply_at_def obj_at_def)
  done

lemma no_reply_in_ts_inv[wp]:
  "\<lbrace>P\<rbrace> no_reply_in_ts t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: no_reply_in_ts_def get_thread_state_def thread_get_def)

lemmas tcb_agnostic_predE' = tcb_agnostic_predE[of "\<lambda>b. b" P for P, rotated]

lemma set_reply_tcb_valid_tcb_state:
  "\<lbrace>reply_at reply_ptr'\<rbrace>
   set_reply_obj_ref reply_tcb_update reply_ptr t
   \<lbrace>\<lambda>rv. valid_tcb_state (BlockedOnReply reply_ptr')\<rbrace>"
  unfolding valid_tcb_state_def by wpsimp

lemma reply_unlink_tcb_sym_refs_BlockedOnReceive:
  "\<lbrace>\<lambda>s. (\<exists>epptr pl. st_tcb_at ((=) (BlockedOnReceive epptr (Some rptr) pl)) tptr s \<and>
                      sym_refs (\<lambda>x. if x = tptr then
                                      {r \<in> state_refs_of s x. snd r = TCBBound \<or>
                                       snd r = TCBSchedContext \<or> snd r = TCBYieldTo
                                       \<or> snd r = TCBReply}
                                    else state_refs_of s x))\<rbrace>
   reply_unlink_tcb tptr rptr \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def pred_tcb_at_eq_commute)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj], clarsimp)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj], clarsimp)
  apply wpsimp
  apply (rule_tac V="tptr \<noteq> rptr" in revcut_rl; clarsimp simp: pred_tcb_at_def obj_at_def)
  by (erule delta_sym_refs
      ; fastforce simp: in_state_refs_of_iff get_refs_def2
                split: if_splits)

lemma reply_unlink_tcb_valid_replies_BlockedOnReceive:
  "\<lbrace>\<lambda>s. (\<exists>epptr pl. st_tcb_at ((=) (BlockedOnReceive epptr (Some rptr) pl)) tptr s) \<and>
        valid_replies s\<rbrace>
   reply_unlink_tcb tptr rptr
   \<lbrace>\<lambda>_. valid_replies\<rbrace>"
  apply (wpsimp wp: reply_unlink_tcb_valid_replies)
  apply (erule replies_blocked_upd_tcb_st_valid_replies_not_blocked)
  apply (clarsimp simp: replies_blocked_def pred_tcb_at_def obj_at_def)
  done

lemma set_original_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> set_original slot v \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: set_original_def reply_tcb_reply_at_def)

lemma set_original_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> set_original slot v \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: set_original_def reply_sc_reply_at_def)

lemmas set_cap_reply_tcb =
  set_cap.reply_tcb_obj_at[where P="\<lambda>c. c" and p'=cslot_ptr and P'=P for P cslot_ptr]

lemmas set_cap_reply_sc =
  set_cap.reply_sc_obj_at[where P="\<lambda>c. c" and p'=cslot_ptr and P'=P for P cslot_ptr]

global_interpretation set_untyped_cap_as_full:
  cspace_non_astate_non_mem_op "set_untyped_cap_as_full src_cap new_cap src_slot"
  by unfold_locales (wpsimp simp: set_untyped_cap_as_full_def wp: set_cap.cspace_agnostic_obj_at)+

crunches update_cdt
  for obj_at[wp]: "\<lambda>s. P (obj_at P' p s)"
  (simp: reply_sc_reply_at_def)

lemma store_word_offs_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: store_word_offs_def do_machine_op_def reply_tcb_reply_at_def)

lemma store_word_offs_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: store_word_offs_def do_machine_op_def reply_sc_reply_at_def)

crunch bound_sc_tcb_at[wp]: do_ipc_transfer "\<lambda>s. Q (bound_sc_tcb_at P t s)"
  (wp: crunch_wps)

lemma set_reply_tcb_rv[wp]:
  "\<lbrace> \<lambda>s. P t \<rbrace> set_reply_obj_ref reply_tcb_update r t \<lbrace> \<lambda>rv s. reply_tcb_reply_at P r s \<rbrace>"
  by (wpsimp wp: update_sk_obj_ref_wp simp: sk_obj_at_pred_def obj_at_def)+

lemma sc_at_pred_n_sc_at:
  "valid_objs s \<Longrightarrow> sc_at_pred_n N proj P sc s \<Longrightarrow> sc_at sc s"
  by (fastforce simp: sc_at_pred_n_def obj_at_def is_sc_obj_def
                elim: valid_objs_valid_sched_context_size)

lemma sc_at_pred_nE:
  assumes "sc_at_pred_n N proj P ref s"
  assumes "\<And>sc n. kheap s ref = Some (SchedContext sc n) \<Longrightarrow> P (proj sc) \<Longrightarrow> N n \<Longrightarrow> R"
  shows R
  using assms by (auto simp: sc_at_pred_n_def obj_at_def)

lemmas sc_replies_sc_atE =
  sc_at_pred_nE[where N=\<top> and proj=sc_replies, simplified]

lemma sc_replies_sc_at_state_refs_of:
  assumes equiv: "\<And>rs. P rs \<longleftrightarrow> rs = replies"
  assumes sc_at: "sc_replies_sc_at P sc s" "replies \<noteq> []"
  shows "r = hd replies \<longleftrightarrow> (r, SCReply) \<in> state_refs_of s sc"
  using sc_at
  by (auto simp: equiv sc_replies_sc_at_def obj_at_def state_refs_of_def get_refs_def2)
     (rule_tac x="tl (sc_replies sca)" in exI, clarsimp)

lemma sc_replies_sc_at_state_refs_of2:
  assumes equiv: "\<And>rs. P rs \<longleftrightarrow> rs = replies"
  assumes sc_at: "sc_replies_sc_at P sc s" "replies = []"
  shows "(r, SCReply) \<notin> state_refs_of s sc"
  using sc_at
  by (auto simp: equiv sc_replies_sc_at_def obj_at_def state_refs_of_def get_refs_def2)

lemma reply_sc_reply_at_ReplySchedContext_in_state_refs_of:
  "reply_sc_reply_at P r_ptr s \<Longrightarrow> (sc, ReplySchedContext) \<in> state_refs_of s r_ptr \<Longrightarrow> P (Some sc)"
  by (clarsimp simp: reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def
              split: option.splits)

lemma reply_tcb_reply_at_None_imp_reply_sc_reply_at_None':
  "invs s \<Longrightarrow>
   reply_tcb_reply_at (\<lambda>f. f = None) reply_ptr s \<Longrightarrow>
   reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr s"
   using invs_reply_tcb_None_reply_sc_None
   by (fastforce simp: reply_sc_reply_at_def reply_tcb_reply_at_def obj_at_def
                split: option.splits)

lemma receive_ipc_preamble_rv:
  "\<lbrace>st_tcb_at active t and invs\<rbrace> receive_ipc_preamble reply t \<lbrace>receive_ipc_preamble_rv reply\<rbrace>"
  unfolding receive_ipc_preamble_def
  apply (cases reply; clarsimp intro!: hoare_weaken_pre[OF return_wp])
  apply (thin_tac _, rename_tac reply_ptr R)
  apply (rule hoare_seq_ext[OF _ grt_sp]; simp?)
  apply (rename_tac t_opt)
  apply (case_tac t_opt;
         clarsimp intro!: hoare_weaken_pre[OF return_wp] reply_tcb_reply_at_None_imp_reply_sc_reply_at_None'
                    simp: )
  apply (rename_tac t_ptr)
  apply (rule hoare_seq_ext[OF return_wp], simp)
  apply (rule hoare_when_cases, clarsimp)
   apply (drule_tac x=reply_ptr and y=t and tp=TCBReply in sym_refsE[OF invs_sym_refs];
          fastforce simp: reply_at_ppred_def pred_tcb_at_def obj_at_def state_refs_of_def refs_of_rev
                   split: option.splits)
  apply (strengthen reply_tcb_reply_at_None_imp_reply_sc_reply_at_None')
  apply (wpsimp wp: cancel_ipc_reply_at_tcb_in[where tcbs="{}", simplified])
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def)

crunches set_message_info, transfer_caps, copy_mrs
  for valid_replies_pred[wp]: "valid_replies_pred P"
  (wp: crunch_wps)

lemma set_mrs_valid_replies[wp]:
  "set_mrs receiver recv_buffer x2 \<lbrace> valid_replies_pred P \<rbrace>"
  unfolding set_mrs_def
  by (wpsimp wp:zipWithM_x_inv' set_object_wp,
      clarsimp dest!: get_tcb_SomeD simp: obj_at_def)

lemma sched_context_update_consumed_valid_replies[wp]:
  "sched_context_update_consumed p \<lbrace> valid_replies_pred P \<rbrace>"
  unfolding sched_context_update_consumed_def
  by (wpsimp wp: update_sched_context_wp)

crunch valid_replies[wp]: do_ipc_transfer "valid_replies_pred P"
  (simp: crunch_simps wp: crunch_wps make_arch_fault_msg_valid_replies)

lemma set_reply_sc_valid_replies_already_BlockedOnReply:
  "\<lbrace> \<lambda>s. valid_replies s \<and> r \<in> fst ` replies_blocked s \<rbrace>
    set_reply_obj_ref reply_sc_update r (Some sc)
   \<lbrace> \<lambda>rv. valid_replies \<rbrace>"
  by wpsimp

lemma reply_sc_update_None_reply_sc_reply_at_None[wp]:
  "set_reply_obj_ref reply_sc_update t None \<lbrace>reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr\<rbrace>"
  apply (wpsimp wp: update_sk_obj_ref_wp)
  apply (clarsimp simp: reply_sc_reply_at_def obj_at_def)
  done

lemma reply_sc_update_Some_invs:
  "\<lbrace>all_invs_but_sym_refs
    and (\<lambda>s. sym_refs (\<lambda>x. if x = reply_ptr
                           then {p. (snd p = ReplySchedContext \<longrightarrow> Some sc_caller = Some (fst p)) \<and>
                                    (snd p \<noteq> ReplySchedContext \<longrightarrow> p \<in> state_refs_of s reply_ptr)}
                           else state_refs_of s x)
             \<and> sym_refs (state_hyp_refs_of s))
    and sc_at sc_caller
    and ex_nonz_cap_to reply_ptr\<rbrace>
   set_reply_obj_ref reply_sc_update reply_ptr (Some sc_caller)
   \<lbrace>\<lambda>r. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_ioports_lift)

(* FIXME move *)
lemma ReplyTCB_bound_reply_tcb_reply_at:
  "(t, ReplyTCB) \<in> state_refs_of s r_ptr \<Longrightarrow> reply_tcb_reply_at bound r_ptr s"
  by (frule reftypes_reply_at,
      simp,
      clarsimp simp: is_reply state_refs_of_def refs_of_def reply_tcb_reply_at_def
                     obj_at_def get_refs_def
              split: option.splits)

(* FIXME move *)
lemma replies_blocked_list_all_reply_at:
  "valid_objs s \<Longrightarrow>
   (set list \<subseteq> fst ` replies_blocked s) \<Longrightarrow>
   list_all (\<lambda>r. reply_at r s) list"
  apply (clarsimp simp: list_all_def replies_blocked_def image_def st_tcb_at_def obj_at_def)
  apply (drule subsetD, assumption, clarsimp)
  apply (subgoal_tac "valid_tcb b tcb s")
   apply (clarsimp simp: valid_tcb_def valid_tcb_state_def obj_at_def)
  apply (fastforce simp: valid_objs_def valid_obj_def dom_def)
  done

lemma replies_with_sc_upd_replies_valid_replies_add_one:
  "valid_replies_2 (replies_with_sc s) (replies_blocked s)
   \<Longrightarrow> r \<in> fst ` replies_blocked s
   \<Longrightarrow> r \<notin> fst ` replies_with_sc s
   \<Longrightarrow> sc_replies_sc_at ((=) list) sc_ptr s
   \<Longrightarrow> valid_replies_2 (replies_with_sc_upd_replies (r # list) sc_ptr (replies_with_sc s)) (replies_blocked s)"
  unfolding valid_replies_2_def replies_with_sc_upd_replies_def
  apply (intro conjI; clarsimp)
   apply (case_tac "ba = sc_ptr"; simp;
          fastforce simp: image_def replies_with_sc_def sc_replies_sc_at_def obj_at_def)
  apply (clarsimp simp: inj_on_def)
  apply (case_tac "ba = sc_ptr"; case_tac "bb = sc_ptr"; simp)
    apply (elim disjE,
           fastforce simp: image_def,
           clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)+
  apply fastforce
  done

lemma sc_replies_sc_at_subset_fst_replies_with_sc:
  "sc_replies_sc_at ((=) w) sc_caller s \<Longrightarrow> set w \<subseteq> fst ` replies_with_sc s"
  by (fastforce simp: sc_replies_sc_at_def obj_at_def image_def replies_with_sc_def)

lemma sc_replies_sc_at_hd_SCReply_ref:
  "sc_replies_sc_at ((=) (x # xa)) sc s \<Longrightarrow> ((x, SCReply) \<in> state_refs_of s sc)"
  by (fastforce simp: sc_replies_sc_at_def obj_at_def state_refs_of_def get_refs_def
               split: option.splits)

lemma valid_objs_distinct_sc_replies:
  "sc_replies_sc_at ((=) w) sc_ptr s \<Longrightarrow> valid_objs s \<Longrightarrow> distinct w"
  apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
  apply (subgoal_tac "valid_sched_context sc s")
  apply (clarsimp simp: valid_sched_context_def)
  apply (fastforce simp: valid_objs_def valid_obj_def dom_def)
  done

lemma sc_at_pred_id_top_weaken:
  "sc_at_ppred proj P sc s \<Longrightarrow> sc_at_ppred id \<top> sc s"
  by (clarsimp simp: sc_at_ppred_def obj_at_def)

lemma SCReply_ref_fst_replies_with_sc:
  "(reply_ptr, SCReply) \<in> state_refs_of s y \<Longrightarrow> reply_ptr \<in> fst ` replies_with_sc s"
  by (fastforce simp: state_refs_of_def refs_of_rev replies_with_sc_def image_def
                      sc_replies_sc_at_def obj_at_def
               split: option.splits)

lemma SCReply_ref_replies_with_sc:
  "(reply_ptr, SCReply) \<in> state_refs_of s y \<Longrightarrow> (reply_ptr, y) \<in> replies_with_sc s"
  by (fastforce simp: state_refs_of_def refs_of_rev replies_with_sc_def image_def
                      sc_replies_sc_at_def obj_at_def
               split: option.splits)

(* FIXME RT: rule should not generate unbound schematics in precondition (reply) *)
lemma reply_push_sender_sc_Some_invs:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at ((=) sender_sc) sender s \<and>
        st_tcb_at active thread s \<and>
        ex_nonz_cap_to thread s \<and> reply_ptr \<notin> fst ` replies_with_sc s \<and>
        (\<forall>r\<in>zobj_refs reply. ex_nonz_cap_to r s) \<and>
        receive_ipc_preamble_rv reply (Some reply_ptr) s \<and>
        sym_refs
         (\<lambda>p. if p = sender then tcb_non_st_state_refs_of s sender else state_refs_of s p) \<and>
        sym_refs (state_hyp_refs_of s) \<and>
        st_tcb_at ((=) (BlockedOnSend ep_ptr sender_data)) sender s \<and>
        ex_nonz_cap_to sender s \<and> sender \<noteq> idle_thread s \<and>
        valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_ioc s \<and>
        if_live_then_nonz_cap s \<and> zombies_final s \<and> valid_mdb s \<and>
        valid_idle s \<and> only_idle s \<and> if_unsafe_then_cap s \<and>
        valid_global_refs s \<and> valid_arch_state s \<and> valid_machine_state s \<and>
        valid_irq_states s \<and> valid_irq_node s \<and> valid_irq_handlers s \<and>
        valid_vspace_objs s \<and> valid_arch_caps s \<and> valid_global_objs s \<and>
        valid_kernel_mappings s \<and> equal_kernel_mappings s \<and>
        valid_asid_map s \<and> valid_ioports s \<and> valid_global_vspace_mappings s \<and>
        pspace_in_kernel_window s \<and> cap_refs_in_kernel_window s \<and>
        pspace_respects_device_region s \<and> cap_refs_respects_device_region s \<and>
        valid_replies_2 (replies_with_sc s) (replies_blocked s) \<and>
        fault_tcbs_valid_states s \<and> cur_tcb s \<and> cur_sc_tcb s\<rbrace>
   reply_push sender thread reply_ptr ((\<exists>y. sender_sc = Some y) \<and>
             \<not> (case fault of None \<Rightarrow> False
                 | Some x \<Rightarrow> is_timeout_fault x))
   \<lbrace>\<lambda>r. invs\<rbrace>"
  apply (clarsimp simp: reply_push_def bind_sc_reply_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule_tac S="sender_sc = sc_caller \<and> sender \<noteq> thread \<and> sender \<noteq> reply_ptr \<and> thread \<noteq> reply_ptr"
           in hoare_gen_asm'', fastforce simp: sk_obj_at_pred_def pred_tcb_at_def obj_at_def)
  apply (rule subst[of "do _ <- do _ <- a; b od; c od"
                       "do _ <- a; _ <- b; c od"
                       "\<lambda>c. \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
                    for a b c P Q]
         , simp add: bind_assoc)
  apply (rule_tac B="\<lambda>_ s. st_tcb_at ((=) (BlockedOnReply reply_ptr)) sender s
                           \<and> bound_sc_tcb_at ((=) sc_callee) thread s
                           \<and> reply_tcb_reply_at (\<lambda>t. t = Some sender) reply_ptr s
                           \<and> reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr s
                           \<and> bound_sc_tcb_at ((=) sc_caller) sender s
                           \<and> st_tcb_at active thread s
                           \<and> ex_nonz_cap_to thread s
                           \<and> ex_nonz_cap_to reply_ptr s
                           \<and> ex_nonz_cap_to sender s
                           \<and> sender \<noteq> idle_thread s
                           \<and> reply_ptr \<notin> fst ` replies_with_sc s
                           \<and> invs s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: sts_st_tcb_at_cases set_thread_state_bound_sc_tcb_at sts_only_idle
                     sts_valid_replies sts_fault_tcbs_valid_states valid_ioports_lift
               simp: invs_def valid_state_def valid_pspace_def valid_tcb_state_def
                     st_tcb_at_tcb_at reply_tcb_reply_at
               cong: if_cong)
   apply (intro conjI)
    apply (fastforce simp: replies_blocked_def st_tcb_at_def obj_at_def
                    elim!: replies_blocked_upd_tcb_st_valid_replies)
   apply (erule delta_sym_refs; clarsimp split: if_splits
          ; fastforce dest: reply_tcb_reply_at_ReplyTCB_in_state_refs_of
                            st_tcb_at_TCBReply_in_state_refs_of)
  apply (rule hoare_when_cases; clarsimp)
    (* reset *)
  apply (rename_tac sc_caller)
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[simplified]])
  apply (wpsimp wp: sched_context_donate_invs reply_sc_update_Some_invs
                    sc_replies_update_valid_replies_cons valid_sc_typ_list_all_reply
                    valid_ioports_lift get_simple_ko_wp update_sched_context_valid_idle)
  apply (rule conjI, clarsimp simp: invs_def valid_state_def valid_pspace_def)
    (* sc_caller has empty sc_replies *)
   apply (rule conjI, clarsimp simp: reply_sc_reply_at_def obj_at_def is_reply_def)
   apply (subgoal_tac "ex_nonz_cap_to sc_caller s", clarsimp)
    apply (rule conjI)
     apply (subgoal_tac "sc_tcb_sc_at ((=) (Some sender)) sc_caller s")
      apply (fastforce simp: sc_at_pred_n_def obj_at_def valid_idle_def)
     apply (clarsimp simp: pred_tcb_at_eq_commute sc_at_pred_n_eq_commute
                           sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at)
    apply (rule conjI, fastforce simp: replies_blocked_def image_def pred_tcb_at_eq_commute)
    apply (rule conjI, erule delta_sym_refs)
      apply (fastforce simp: image_iff sc_tcb_sc_at_def obj_at_def is_reply
                             sc_replies_sc_at_state_refs_of2[OF eq_commute]
                       dest: reply_sc_reply_at_ReplySchedContext_in_state_refs_of
                      split: if_splits)
     apply (clarsimp simp: image_iff sc_tcb_sc_at_def obj_at_def is_reply
                           sc_replies_sc_at_state_refs_of2[OF eq_commute]
                     dest: reply_sc_reply_at_ReplySchedContext_in_state_refs_of
                    split: if_splits)
      apply (case_tac "y = reply_ptr"; clarsimp)
      apply (safe; simp)[1]
       apply (drule sc_reftypes)
        apply (rule sc_at_pred_id_top_weaken, assumption)
       apply (clarsimp)
      apply (clarsimp simp: sc_replies_sc_at_state_refs_of2[OF eq_commute] )
     apply (drule SCReply_ref_fst_replies_with_sc)
     apply fastforce
    apply (fastforce intro: sc_at_pred_n_sc_at pred_tcb_at_tcb_at)
   apply (subgoal_tac "sc_tcb_sc_at ((=) (Some sender)) sc_caller s")
    apply (fastforce simp: sc_at_pred_n_def obj_at_def live_def live_sc_def valid_idle_def
                     elim: if_live_then_nonz_capD2)
   apply (clarsimp simp: pred_tcb_at_eq_commute sc_at_pred_n_eq_commute
                         sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at)
                       (* sc_caller has non-empty sc_replies *)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (rename_tac sc_caller s x xa)
  apply (prop_tac "reply_at reply_ptr s",
         clarsimp simp: reply_sc_reply_at_def obj_at_def is_reply_def, simp)
  apply (prop_tac "reply_at x s",
         erule_tac sc_ptr=sc_caller in valid_objs_sc_replies_reply_at)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
   apply (metis list.set_intros(1))
  apply (rule conjI, simp)
  apply (rule conjI, rule replies_blocked_list_all_reply_at, assumption)
   apply (drule valid_replies_2D1)
   apply (rule_tac B="fst ` replies_with_sc s" in subset_trans; simp?)
   apply (drule sc_replies_sc_at_subset_fst_replies_with_sc)
   apply fastforce
  apply (rule conjI, clarsimp)
   apply (drule sc_replies_sc_at_hd_SCReply_ref)
   apply (drule sym_refsD, assumption)
   apply (clarsimp simp: state_refs_of_def reply_sc_reply_at_def obj_at_def get_refs_def
                  split: option.splits)
  apply (rule conjI, clarsimp)
   apply (subgoal_tac "(reply_ptr, sc_caller) \<in> replies_with_sc s", fastforce simp: image_def)
   apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)
   apply (drule_tac s="x # xa" in sym, fastforce)
  apply (rule conjI, clarsimp)
   apply (subgoal_tac "distinct (x # xa)")
    apply fastforce
   apply (rule valid_objs_distinct_sc_replies; assumption)
  apply (rule conjI)
   apply (subgoal_tac "distinct (x # xa)")
    apply (drule distinct_tl, simp)
   apply (rule valid_objs_distinct_sc_replies; assumption)
  apply (subgoal_tac "ex_nonz_cap_to sc_caller s", clarsimp)
   apply (rule conjI)
    apply (subgoal_tac "sc_tcb_sc_at ((=) (Some sender)) sc_caller s")
     apply (fastforce simp: sc_at_pred_n_def obj_at_def valid_idle_def)
    apply (clarsimp simp: pred_tcb_at_eq_commute sc_at_pred_n_eq_commute
                          sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at)
   apply (rule conjI, fastforce simp: replies_blocked_def image_def pred_tcb_at_eq_commute)
   apply (rule conjI, rule delta_sym_refs, assumption)
     apply (fastforce simp: image_iff sc_tcb_sc_at_def obj_at_def is_reply
                            sc_replies_sc_at_state_refs_of2[OF eq_commute]
                      dest: reply_sc_reply_at_ReplySchedContext_in_state_refs_of
                     split: if_splits)
    apply (clarsimp simp: image_iff sc_tcb_sc_at_def obj_at_def is_reply reply_at_ppred_reply_at
                          sc_replies_sc_at_state_refs_of2[OF eq_commute]
                    dest: SCReply_ref_fst_replies_with_sc reply_reftypes
                   split: if_splits)
          apply (case_tac "y = reply_ptr"; clarsimp)
          apply (safe; simp)[1]
           apply (fastforce dest: SCReply_ref_fst_replies_with_sc)
          apply (fastforce dest: reply_reftypes reply_at_ppred_reply_at)
         apply (case_tac "y = x"; clarsimp)
          apply (safe; simp)[1]
          apply (fastforce dest: SCReply_ref_fst_replies_with_sc)
         apply (safe; simp)[1]
          apply (fastforce dest: SCReply_ref_fst_replies_with_sc)
         apply (fastforce dest: reply_reftypes reply_at_ppred_reply_at)
        apply (fastforce dest: SCReply_ref_fst_replies_with_sc)
       apply (case_tac "sc_caller = x"; clarsimp)
        apply (fastforce dest: SCReply_ref_fst_replies_with_sc)
       apply (case_tac "y = x"; clarsimp)
        apply (fastforce dest: SCReply_ref_fst_replies_with_sc)
       apply (fastforce dest: SCReply_ref_fst_replies_with_sc)
      apply (fastforce simp: sc_at_pred_n_def obj_at_def reply_sc_reply_at_def)
     apply (case_tac "reply_ptr = x"; clarsimp)
      apply (clarsimp simp: reply_sc_reply_at_def obj_at_def)
      apply (prop_tac "(reply_ptr, sc_caller) \<in> replies_with_sc s")
       apply (clarsimp simp: replies_with_sc_def sc_at_pred_n_def obj_at_def)
       apply (metis cons_set_intro)
      apply fastforce
     apply (clarsimp simp: reply_sc_reply_at_def obj_at_def)
     apply (fastforce dest: sc_replies_sc_at_state_refs_of[OF eq_commute, THEN iffD2])
    apply (safe; simp?)[1]
      apply (fastforce simp: sc_at_pred_n_def obj_at_def reply_sc_reply_at_def)
     apply (fastforce dest: reply_reftypes reply_at_ppred_reply_at)
    apply (drule SCReply_ref_replies_with_sc)
    apply (subgoal_tac "(x, sc_caller) \<in> replies_with_sc s")
     apply (fastforce dest: valid_repliesD2)
    apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)
    apply (drule_tac s="x # xa" in sym, fastforce)
   apply (fastforce intro: sc_at_pred_n_sc_at pred_tcb_at_tcb_at)
  apply (fastforce simp: sc_at_pred_n_def pred_tcb_at_def sk_obj_at_pred_def obj_at_def
                         live_def live_sc_def
                   elim: if_live_then_nonz_capD2)
  done

crunches maybe_return_sc
  for only_idle[wp]: only_idle
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
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and zombies_final[wp]: zombies_final
  and valid_mdb[wp]: valid_mdb
  and valid_ioc[wp]: valid_ioc
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (simp: crunch_simps wp: crunch_wps ignore: set_tcb_obj_ref)

lemma maybe_return_sc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def get_sk_obj_ref_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def get_sk_obj_ref_def get_simple_ko_def get_object_def
               wp: weak_if_wp)

lemma maybe_return_sc_sym_refs_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: maybe_return_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply wpsimp
  apply safe
   apply (fastforce simp: pred_tcb_at_def valid_obj_def valid_tcb_def valid_bound_obj_def
                          is_sc_obj_def obj_at_def
                  split: option.splits)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_splits)
  apply (clarsimp split: if_splits)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (rotate_tac -2)
   apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply (fastforce simp: sc_at_typ2 obj_at_def state_refs_of_def get_refs_def2 valid_obj_def
                          valid_ntfn_def valid_bound_obj_def
                   split: option.splits)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2)
  done

lemma maybe_return_sc_valid_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> sym_refs (state_refs_of s) \<and> tcb_ptr \<noteq> idle_thread s\<rbrace>
   maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (wpsimp simp: maybe_return_sc_def get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def
                      get_simple_ko_def get_object_def
                  wp: update_sched_context_valid_idle)
  apply (intro conjI)
    apply clarsimp
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = tcb_ptr in allE)
   apply (auto simp: valid_idle_def obj_at_def state_refs_of_def get_refs_def2
              dest!: get_tcb_SomeD)
  done

global_interpretation maybe_return_sc: non_reply_op "maybe_return_sc ntfn_ptr tcb_ptr"
  by unfold_locales (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps get_sk_obj_ref_wp
                          simp: maybe_return_sc_def)

lemma maybe_return_sc_valid_replies[wp]:
  "maybe_return_sc ntfn_ptr tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: hoare_vcg_if_lift2 hoare_drop_imps get_sk_obj_ref_wp)

lemma maybe_return_sc_pred_tcb_at:
  "\<lbrace>(\<lambda>s. Q (pred_tcb_at proj P tcb_ptr' s))
    and K (tcb_ptr = tcb_ptr' \<longrightarrow>
           (\<forall>tcb x. proj (tcb_to_itcb (tcb_sched_context_update x tcb)) = proj (tcb_to_itcb tcb)))\<rbrace>
   maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. Q (pred_tcb_at proj P tcb_ptr' s)\<rbrace>"
  apply (wpsimp simp: maybe_return_sc_def set_tcb_obj_ref_def set_object_def
                      get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def get_simple_ko_def
                      get_object_def)
  apply (auto simp: pred_tcb_at_def obj_at_def get_tcb_SomeD)
  done

lemma maybe_return_sc_st_tcb_at[wp]:
  "maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>st_tcb_at P t\<rbrace>"
  by (wpsimp wp: maybe_return_sc_pred_tcb_at)

(* FIXME RT: move *)
lemma receive_ipc_preamble_rv_lift:
  "(\<And>a P. f \<lbrace>reply_tcb_reply_at P a \<rbrace>)
   \<Longrightarrow> (\<And>a P. f \<lbrace>reply_sc_reply_at P a \<rbrace>)
   \<Longrightarrow> f \<lbrace>receive_ipc_preamble_rv reply reply_opt\<rbrace>"
  by (case_tac reply_opt; wpsimp wp: hoare_vcg_conj_lift; assumption)

lemma maybe_return_sc_fault_tcbs_valid_states[wp]:
  "maybe_return_sc ntfn_ptr thread \<lbrace>fault_tcbs_valid_states\<rbrace>"
  unfolding fault_tcbs_valid_states_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' maybe_return_sc_pred_tcb_at)

crunches maybe_return_sc
  for misc_proj[wp]: "\<lambda>s. P (cur_thread s) (cur_sc s) (release_queue s)
                                 (cur_domain s) (domain_time s) (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunches reschedule_required
  for sc_at_ppred[wp]: "sc_at_ppred proj P scp"
  (wp: crunch_wps simp: crunch_simps)

lemma maybe_return_sc_sc_at_ppred:
  "\<lbrace>sc_at_ppred proj P scp and bound_sc_tcb_at (\<lambda>x. x \<noteq> Some scp) tcb_ptr\<rbrace>
   maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. sc_at_ppred proj P scp\<rbrace>"
  apply (wpsimp simp: maybe_return_sc_def update_sched_context_def
                      set_tcb_obj_ref_def set_object_def
                      get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def get_simple_ko_def
                      get_object_def)
  by (auto simp: sc_at_pred_n_def obj_at_def pred_tcb_at_def get_tcb_SomeD)

lemma reschedule_required_cur_sc_tcb':
  "\<lbrace>\<lambda>s. sc_tcb_sc_at \<top> (cur_sc s) s\<rbrace> reschedule_required \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  supply set_scheduler_action_cur_sc_tcb [wp del]
  unfolding reschedule_required_def
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def
                   set_tcb_queue_def get_tcb_queue_def thread_get_def is_schedulable_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma maybe_return_sc_cur_sc_tcb[wp]:
  "\<lbrace>cur_sc_tcb and (\<lambda>s. sym_refs (state_refs_of s)) and valid_objs\<rbrace>
    maybe_return_sc ntfn_ptr thread
   \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  supply reschedule_required_cur_sc_tcb' [wp]
  supply reschedule_required_cur_sc_tcb [wp del]
  apply (wpsimp simp: maybe_return_sc_def update_sched_context_def
                      set_tcb_obj_ref_def set_object_def
                      get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def get_simple_ko_def
                      get_object_def)
  apply (case_tac "thread = cur_thread s"; simp)
   apply (fastforce split: if_split simp: sc_at_pred_n_def obj_at_def cur_sc_tcb_def)
  apply (clarsimp split: if_split simp: sc_at_pred_n_def obj_at_def cur_sc_tcb_def)
  apply (intro conjI allI impI; clarsimp?)
  apply (frule get_tcb_SomeD, clarsimp)
  apply (subgoal_tac "sc_tcb xa = Some thread", simp)
  apply (fastforce elim: bound_sc_tcb_bound_sc_at simp: pred_tcb_at_def obj_at_def)
  done

lemma maybe_return_sc_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
    maybe_return_sc ntfn_ptr thread
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: hoare_vcg_conj_lift valid_ioports_lift
           simp: invs_def valid_state_def valid_pspace_def)

lemma maybe_return_sc_ko_at_Endpoint[wp]:
  "maybe_return_sc ntfn_ptr thread \<lbrace>\<lambda>s. ko_at (Endpoint ep) ep_ptr s\<rbrace>"
  apply (wpsimp simp: maybe_return_sc_def update_sched_context_def
                      set_tcb_obj_ref_def set_object_def
                      get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def get_simple_ko_def
                      get_object_def)
  by (auto simp: obj_at_def)

crunches receive_ipc_preamble
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma ri_invs[wp]:
  fixes thread ep_cap is_blocking reply
  notes if_split[split del]
  notes hyp_refs_of_simps[simp del]
  notes complete_signal_invs[wp] set_endpoint_invs[wp]
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>\<lambda>s. invs s \<and> st_tcb_at active thread s
               \<and> ex_nonz_cap_to thread s
               \<and> (\<forall>r\<in>zobj_refs ep_cap. ex_nonz_cap_to r s)
               \<and> (\<forall>r\<in>zobj_refs reply. ex_nonz_cap_to r s)\<rbrace>
    receive_ipc thread ep_cap is_blocking reply
   \<lbrace>\<lambda>r s. invs s\<rbrace>" (is "\<lbrace>\<lambda>s. invs s \<and> ?pre s\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (cases ep_cap; simp cong: endpoint.case_cong bool.case_cong if_cong
                             add: receive_ipc_def split_def receive_ipc_preamble_def[symmetric]
                                  receive_ipc_blocked_def[symmetric]
                                  receive_ipc_idle_def[symmetric])
  apply (rename_tac ep_ptr ep_badge ep_rights)
  apply (rule hoare_seq_ext[where B="\<lambda>rv. invs and ?pre and receive_ipc_preamble_rv reply rv",
         rotated]; simp)
   apply (wpsimp wp: receive_ipc_preamble_invs receive_ipc_preamble_caps_of_state
                     receive_ipc_preamble_st_tcb_at receive_ipc_preamble_rv
               simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state)
  apply (rename_tac reply_opt)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp[simplified pred_conj_comm]])
  apply (rule hoare_seq_ext[OF _ gbn_sp[simplified pred_conj_comm]])
  apply (rule hoare_seq_ext[OF _ get_notification_default_sp])
  apply (rule hoare_weaken_pre)
   apply (rule_tac R="receive_ipc_preconds thread ep_ptr reply reply_opt ep invs"
          in hoare_vcg_if_split)
    apply (wp complete_signal_invs)
   prefer 2 apply (clarsimp simp: st_tcb_at_tcb_at)
  apply (thin_tac "\<not> (_ \<and> _)", clarsimp)
  apply (rule_tac B="\<lambda>r s. st_tcb_at active thread s \<and>
             ex_nonz_cap_to thread s \<and>
             ex_nonz_cap_to ep_ptr s \<and>
             (\<forall>r\<in>zobj_refs reply. ex_nonz_cap_to r s) \<and>
             receive_ipc_preamble_rv reply reply_opt s \<and>
             ko_at (Endpoint ep) ep_ptr s \<and> invs s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: hoare_vcg_ball_lift split: if_split)
    apply (fastforce dest: st_tcb_at_idle_thread split: if_split)
    (* IdleEP, RecvEP *)
  apply (case_tac ep; clarsimp simp: receive_ipc_blocked_invs[where reply=reply])
    (* SendEP *)
  apply (rename_tac queue)
  apply (rule hoare_seq_ext[OF _ assert_sp], simp)
  apply (case_tac queue; clarsimp cong: if_cong list.case_cong)
  apply (rename_tac sender queue)
  apply (rule_tac s="mk_ep SendEP queue"
           in subst[where P="\<lambda>c. \<lbrace>P\<rbrace> set_endpoint p c >>= r \<lbrace>Q\<rbrace>" for P p r Q]
         , simp add: mk_ep_def split: list.splits)
       (* set_endpoint *)
  apply (rule_tac B="\<lambda>r. receive_ipc_preconds thread ep_ptr reply reply_opt
                           (mk_ep SendEP queue)
                           (\<lambda>s. sym_refs (\<lambda>p. if p = ep_ptr then set (sender # queue) \<times> {EPSend}
                                                            else state_refs_of s p)
                                \<and> sym_refs (state_hyp_refs_of s)
                                \<and> sender \<notin> set queue
                                \<and> all_invs_but_sym_refs s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: hoare_vcg_ball_lift set_simple_ko_at valid_ioports_lift)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (apply_conjunct \<open>erule delta_sym_refs; fastforce simp: ko_at_state_refs_ofD
                                                         split: if_splits\<close>)
   apply (fastforce elim!: obj_at_valid_objsE
                     simp: valid_obj_def valid_ep_def mk_ep_def
                    split: endpoint.splits if_splits)
                  (* get_thread_state *)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac sender_state; clarsimp)
  apply (rename_tac ep_ptr' sender_data)
    (* do_ipc_transfer, and stash some knowledge that will be useful later *)
  apply (rule_tac B="\<lambda>r. receive_ipc_preconds thread ep_ptr reply reply_opt
                           (mk_ep SendEP queue)
                           (\<lambda>s. sym_refs (\<lambda>p. if p = sender then tcb_non_st_state_refs_of s sender
                                                         else state_refs_of s p)
                                \<and> sym_refs (state_hyp_refs_of s)
                                \<and> st_tcb_at ((=) (BlockedOnSend ep_ptr sender_data)) sender s
                                \<and> sender \<notin> set queue
                                \<and> ep_ptr \<notin> set queue
                                \<and> sender \<noteq> ep_ptr
                                \<and> ex_nonz_cap_to sender s
                                \<and> sender \<noteq> idle_thread s
                                \<and> state_refs_of s ep_ptr = set queue \<times> {EPSend}
                                \<and> all_invs_but_sym_refs s)"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: do_ipc_transfer_tcb_caps[where t=thread] hoare_vcg_ball_lift
               simp: st_tcb_at_tcb_at)
   apply (rule_tac V="sender \<noteq> ep_ptr" in revcut_rl, fastforce simp: obj_at_def pred_tcb_at_def)
   apply (rule_tac V="ep_ptr \<notin> set queue" in revcut_rl
          , fastforce elim: obj_at_valid_objsE
                      simp: valid_obj_def valid_ep_def obj_at_def is_tcb_def mk_ep_def
                     split: if_splits)
   apply (rule_tac V="ex_nonz_cap_to sender s" in revcut_rl, erule (1) st_tcb_ex_cap, fastforce)
   apply (rule_tac V="sender \<noteq> idle_thread s" in revcut_rl, erule (1) not_idle_thread', fastforce)
   apply (frule ko_at_state_refs_ofD)
   apply (subgoal_tac "ep_ptr' = ep_ptr"; clarsimp)
    apply (erule sym_refs_insert_delete'[where t=EPSend];
           simp add: st_tcb_at_tcb_non_st_state_refs_of)
   apply (clarsimp simp: sym_refs_def)
   apply (drule_tac x=ep_ptr in spec; clarsimp simp: mk_ep_def split: if_splits;
          erule (1) TCBBlockedSend_in_state_refs_of_unique)
        (* thread_get tcb_fault *)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
    (* if not call and no fault: sender \<rightarrow> Running *)
  apply (rule hoare_if[rotated]
         , wpsimp wp: set_thread_state_invs cong: if_cong
         , fastforce simp: replies_blocked_def pred_tcb_at_def obj_at_def)
       (* if not grant or no reply: sender \<longrightarrow> Inactive *)
  apply (rule hoare_if[rotated]
         , wpsimp wp: set_thread_state_invs cong: if_cong
         , fastforce simp: replies_blocked_def st_tcb_at_def obj_at_def)
       (* otherwise (grant and reply and (call or fault)): reply_push *)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (clarsimp)
  apply (rename_tac rply)
  apply (wp reply_push_sender_sc_Some_invs)
  apply (clarsimp)
  apply (intro conjI)
     prefer 3
     apply fastforce
    apply clarsimp
    apply (drule valid_repliesD1_simp, assumption, clarsimp)
    apply (subgoal_tac "t \<noteq> sender")
     apply (drule replies_blocked_imp_TCBReply_ref)
     apply (subgoal_tac "(t, ReplyTCB) \<in> state_refs_of s a")
      apply (clarsimp simp: state_refs_of_def refs_of_def reply_tcb_reply_at_def obj_at_def
                            get_refs_def
                     split: option.splits)
     apply (clarsimp simp:sym_refs_def)
     apply (drule_tac x=t in spec)
     apply (drule_tac x="(a, TCBReply)" in bspec)
      apply (clarsimp split: if_splits)
     apply (clarsimp split: if_splits)
    apply (clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def)
   apply clarsimp
  apply assumption
  done

lemma sched_context_donate_sym_refs_BlockedOnReceive:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
        sym_refs (\<lambda>a. if a = dest
                      then {r \<in> state_refs_of s dest. snd r = TCBBound \<or> snd r = TCBSchedContext
                            \<or> snd r = TCBYieldTo}
                      else state_refs_of s a) \<and>
        sc_tcb_sc_at (\<lambda>t. \<exists>caller. t = Some caller \<and> st_tcb_at active caller s) scptr s \<and>
        st_tcb_at (\<lambda>st. \<exists>epptr pl. st = BlockedOnReceive epptr None pl) dest s \<and>
        bound_sc_tcb_at ((=) None) dest s\<rbrace>
   sched_context_donate scptr dest
   \<lbrace>\<lambda>rv s. sym_refs (\<lambda>a. if a = dest
                         then {r \<in> state_refs_of s dest. snd r = TCBBound \<or>
                               snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                         else state_refs_of s a)\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: sched_context_donate_def)
  apply (rule hoare_seq_ext[OF _ gsct_sp])
  apply (simp add: when_def)
  apply (intro conjI)
   apply wpsimp
   apply (intro conjI)
    apply (clarsimp simp: sc_tcb_sc_at_def pred_tcb_at_def obj_at_def)
   apply (rename_tac caller s)
   apply (clarsimp, intro conjI)
    apply (clarsimp simp: st_tcb_at_def obj_at_def sc_tcb_sc_at_def)
   apply (clarsimp, intro conjI)
    apply (fastforce simp: sc_tcb_sc_at_def valid_obj_def valid_sched_context_def is_tcb obj_at_def)
   apply (clarsimp simp: sym_refs_def)
   apply (intro conjI)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def
                    dest!: symreftype_inverse' st_tcb_at_tcb_at tcb_state_refs_no_tcb bspec)
   apply (clarsimp, intro conjI)
    apply (fastforce simp: symreftype_neq dest!: symreftype_inverse' bspec split: if_splits)
   apply (clarsimp, intro conjI)
    apply (fastforce dest!: bspec)
   apply (clarsimp, intro conjI)
    apply (frule_tac x = scptr in spec, drule_tac x = x in spec)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def st_tcb_at_def
                           state_refs_of_def get_refs_def2)
   apply (clarsimp, intro conjI)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def state_refs_of_def get_refs_def2
                    dest!: bspec)
   apply (fastforce simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                   dest!: bspec)
  apply (wpsimp simp: obj_at_def sc_tcb_sc_at_def)
  done

lemma get_tcb_obj_ref_wp: (* FIXME: move up *)
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at (TCB tcb) ptr s \<longrightarrow>  P (f tcb) s\<rbrace> get_tcb_obj_ref f ptr \<lbrace>P\<rbrace>"
  by (wpsimp simp: get_tcb_obj_ref_def wp: thread_get_wp')

lemma reply_push_st_tcb_at_Inactive:
  "\<lbrace>st_tcb_at ((=) Inactive) callee and K (callee \<noteq> caller)\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. st_tcb_at ((=) Inactive) callee\<rbrace>"
  unfolding reply_push_def bind_sc_reply_def update_sk_obj_ref_def comp_def
  by (wpsimp wp: get_simple_ko_wp get_tcb_obj_ref_wp hoare_vcg_if_lift hoare_vcg_all_lift
                 sts_st_tcb_at_cases
     | wp (once) hoare_drop_imp)+

lemma valid_replies_2_inj_onD:
  "valid_replies_2 S T \<Longrightarrow> \<forall>x y a. (a,x) \<in> S \<longrightarrow> (a,y) \<in> S \<longrightarrow> x=y"
  by (fastforce simp: valid_replies_2_def inj_on_def)

lemma reply_push_invs_helper:
  "\<lbrace> \<lambda>s. invs s
         \<and> reply_at reply_ptr s
         \<and> bound_sc_tcb_at ((=) sc_callee) callee s
         \<and> sc_at sc_ptr s
         \<and> ex_nonz_cap_to reply_ptr s
         \<and> ex_nonz_cap_to callee s
         \<and> ex_nonz_cap_to sc_ptr s
         \<and> reply_sc_reply_at (\<lambda>sc_ptr'. sc_ptr' = None) reply_ptr s
         \<and> reply_ptr \<in> fst ` replies_blocked s
         \<and> reply_ptr \<notin> fst ` replies_with_sc s \<rbrace>
    when (sc_callee = None \<and> donate) (do
      sc_replies <- liftM sc_replies (get_sched_context sc_ptr);
      y <- case sc_replies of [] \<Rightarrow> return ()
              | r # x \<Rightarrow> set_reply_obj_ref reply_sc_update r None;
      y <- set_sc_obj_ref sc_replies_update sc_ptr (reply_ptr # sc_replies);
      y <- set_reply_obj_ref reply_sc_update reply_ptr (Some sc_ptr);
      sched_context_donate sc_ptr callee
    od)
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  supply if_weak_cong[cong del] if_split[split del]
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
  apply (rename_tac sc_replies')
  apply (case_tac sc_replies'; simp)
   apply (wpsimp wp: sched_context_donate_invs)
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: valid_irq_node_typ set_reply_sc_valid_replies_already_BlockedOnReply
                         valid_ioports_lift)
    apply (wpsimp wp: set_sc_replies_valid_replies update_sched_context_valid_idle)
   apply clarsimp
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                          reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                          sc_replies_sc_at_def pred_tcb_at_def is_tcb is_reply is_sc_obj_def
                  split: if_splits
                  elim!: delta_sym_refs)
   apply safe
        apply fastforce
       apply fastforce
      apply (clarsimp simp: valid_idle_def)
     apply (rule replies_with_sc_upd_replies_new_valid_replies)
       apply fastforce
      apply (clarsimp simp: image_def)
      apply (rule_tac x="(reply_ptr, b)" in bexI; fastforce)
     apply (clarsimp simp: image_def)
    apply (fastforce simp: invs_def valid_state_def valid_pspace_def
                           reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                           sc_replies_sc_at_def pred_tcb_at_def is_tcb is_reply is_sc_obj_def
                    split: if_splits
                    elim!: delta_sym_refs)
   apply (clarsimp simp: idle_sc_no_ex_cap)
  apply (wpsimp wp: sched_context_donate_invs)
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: valid_irq_node_typ set_reply_sc_valid_replies_already_BlockedOnReply
                         valid_ioports_lift valid_sc_typ_list_all_reply)
    apply (wpsimp wp: set_sc_replies_valid_replies update_sched_context_valid_idle)
   apply (wpsimp simp: get_simple_ko_def get_object_def
                   wp: valid_sc_typ_list_all_reply valid_ioports_lift)
  apply (subgoal_tac "list_all (\<lambda>r. reply_at r s) (a # list) \<and> reply_ptr \<notin> set (a # list) \<and> distinct (a # list)")
   apply (clarsimp simp: invs_def valid_pspace_def valid_state_def)
   apply (intro conjI)
      apply (rule replies_with_sc_upd_replies_valid_replies_add_one, simp)
        apply (clarsimp simp:replies_blocked_def image_def, fastforce)
       apply simp
      apply (clarsimp simp:sc_replies_sc_at_def obj_at_def)
     apply (erule delta_sym_refs)
      apply (clarsimp split: if_splits
                      elim!: delta_sym_refs)
     apply (clarsimp simp: reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                           pred_tcb_at_def is_tcb is_reply is_sc_obj sc_at_pred_n_def
                    split: if_splits
                    elim!: delta_sym_refs)
     apply (safe; clarsimp?)
     apply (subgoal_tac "(a,y) \<in> replies_with_sc s \<and> (a,sc_ptr) \<in> replies_with_sc s")
      apply (clarsimp dest!: valid_replies_2_inj_onD )
     apply (intro conjI)
      apply (subgoal_tac "valid_reply reply s")
       apply (clarsimp simp: valid_reply_def refs_of_def obj_at_def is_sc_obj_def
                      split: option.splits)
       apply (case_tac x2; clarsimp simp: get_refs_def)
       apply (erule disjE, clarsimp split: option.splits)+
       apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def split: option.splits)
      apply (erule valid_objs_valid_reply, assumption)
     apply (clarsimp simp: replies_with_sc_def sc_replies_sc_at_def obj_at_def)
     apply (metis cons_set_intro)
    apply (fastforce simp: idle_sc_no_ex_cap tcb_at_def is_tcb_def
                     dest: pred_tcb_at_tcb_at get_tcb_SomeD)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply (clarsimp simp del: distinct.simps list.pred_inject insert_iff)
  apply (frule sc_replies_sc_at_subset_fst_replies_with_sc)
  apply (frule invs_valid_objs)
  apply (intro conjI)
    apply (erule replies_blocked_list_all_reply_at)
    apply (meson dual_order.trans invs_valid_replies valid_replies_defs(1))
   apply fastforce
  apply (erule (1) valid_objs_sc_replies_distinct)
  done

lemma sts_in_replies_blocked:
  "\<lbrace>\<top>\<rbrace> set_thread_state t (BlockedOnReply r) \<lbrace>\<lambda>rv s. r \<in> fst ` replies_blocked s\<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_strengthen_post)
    apply (rule sts_st_tcb_at'[where P="\<lambda>st. st = BlockedOnReply r"])
   apply (erule in_replies_blockedI)
  by simp

lemma active_st_tcb_at_not_in_replies_blocked:
  " st_tcb_at active caller s \<Longrightarrow> (a, caller) \<notin> replies_blocked s"
  by (clarsimp simp: st_tcb_at_def replies_blocked_def obj_at_def)

lemma no_reply_in_ts_rv_False:
  "\<lbrace>st_tcb_at (\<lambda>st. (\<exists>y. reply_object st = Some y)) caller\<rbrace>
   no_reply_in_ts caller
   \<lbrace>\<lambda>ts_reply s. \<not> ts_reply\<rbrace>"
  apply (wpsimp simp: no_reply_in_ts_def get_thread_state_def wp: thread_get_wp)
  apply (fastforce simp: obj_at_def is_tcb st_tcb_at_def)
  done

lemma reply_push_invs':
  "\<lbrace>all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {caller} and
    ex_nonz_cap_to callee and ex_nonz_cap_to caller and ex_nonz_cap_to reply_ptr and
    st_tcb_at active caller and st_tcb_at ((=) Inactive) callee and
    reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr and reply_tcb_reply_at (\<lambda>tptr. tptr = None) reply_ptr\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def bind_sc_reply_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ set_reply_tcb_valid_tcb_state
                       sts_valid_replies sts_fault_tcbs_valid_states_except_set valid_ioports_lift
            split_del: if_split)
   apply clarsimp
   apply (intro conjI)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (intro conjI)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
      apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
     apply (rule replies_blocked_upd_tcb_st_valid_replies_not_blocked;
            clarsimp intro!: not_BlockedOnReply_not_in_replies_blocked elim!: st_tcb_weakenE)
    apply (rule delta_sym_refs, assumption)
     apply (clarsimp split: if_splits)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                          tcb_st_refs_of_def reply_tcb_reply_at_def
                   split: if_splits thread_state.splits)
   apply (clarsimp simp: idle_no_ex_cap)
  apply (wpsimp wp: reply_push_invs_helper)
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                    wp: sts_only_idle valid_irq_node_typ sts_valid_replies
                        sts_in_replies_blocked valid_ioports_lift
                        sts_fault_tcbs_valid_states_except_set)
   apply (wpsimp wp: set_reply_tcb_valid_tcb_state valid_irq_node_typ valid_ioports_lift)
  apply clarsimp
  apply (intro conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (intro conjI)
           apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
          apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
         apply (fastforce intro!: replies_blocked_upd_tcb_st_valid_replies
                           dest: active_st_tcb_at_not_in_replies_blocked)
        apply (rule delta_sym_refs, assumption)
         apply (clarsimp split: if_splits)
        apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                              tcb_st_refs_of_def reply_tcb_reply_at_def
                       split: thread_state.splits if_splits)
       apply (clarsimp simp: idle_no_ex_cap)
      apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
     apply (clarsimp simp: pred_tcb_at_def valid_obj_def valid_tcb_def
                    elim!: obj_at_valid_objsE)
     apply (rename_tac tcb')
     apply (case_tac "tcb_sched_context tcb'"; simp)
    apply (rename_tac sc_ptr s)
    apply (subgoal_tac "sc_tcb_sc_at ((=) (Some caller)) sc_ptr s")
     apply (fastforce simp: live_def live_sc_def pred_tcb_at_def obj_at_def valid_idle_def
                            sc_at_pred_n_def
                      elim: if_live_then_nonz_capD2)
    apply (clarsimp simp: pred_tcb_at_eq_commute sc_at_pred_n_eq_commute
                          sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at)
   apply (simp add: replies_blocked_upd_tcb_st_def, rule in_image_fst, fastforce)
  apply clarsimp
  apply (drule valid_repliesD1_simp, assumption, clarsimp)
  apply (drule replies_blocked_imp_TCBReply_ref)
  apply (drule sym_refsD, assumption)
  apply (clarsimp simp: state_refs_of_def reply_tcb_reply_at_def obj_at_def get_refs_def
                 split: option.splits)
  done

lemma reply_push_invs:
  "\<lbrace>invs and ex_nonz_cap_to callee and ex_nonz_cap_to caller and ex_nonz_cap_to reply_ptr and
    st_tcb_at active caller and st_tcb_at ((=) Inactive) callee and
    reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr and
    reply_tcb_reply_at (\<lambda>tptr. tptr = None) reply_ptr\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp wp: reply_push_invs' simp: invs_def valid_state_def valid_pspace_def) auto

crunches reply_push
  for fault_tcb_at[wp]: "fault_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

global_interpretation set_thread_state: non_sc_op "set_thread_state t st"
  by unfold_locales (wpsimp simp: sc_at_pred_n_def wp: sts_obj_at_impossible')

lemma reply_tcb_None_imp_not_in_sc_replies:
  "\<lbrakk>reply_tcb_reply_at (\<lambda>r. r = None) rp s;
    valid_replies s;
    sym_refs (state_refs_of s);
    sc_at scp s\<rbrakk>
    \<Longrightarrow> sc_replies_sc_at (\<lambda>a. rp \<notin> set a) scp s"
  apply (clarsimp simp: sc_replies_sc_at_def obj_at_def is_sc_obj_def split: option.splits)
  apply (case_tac ko; clarsimp)
  apply (subgoal_tac "(rp, scp) \<in> replies_with_sc s")
   apply (frule valid_repliesD1_simp, assumption)
   apply (clarsimp)
   apply (frule replies_blocked_imp_TCBReply_ref)
   apply (subgoal_tac "(t, ReplyTCB) \<in> state_refs_of s rp")
    apply (clarsimp simp: state_refs_of_def refs_of_def replies_blocked_def st_tcb_at_def obj_at_def
                          replies_with_sc_def sc_replies_sc_at_def reply_tcb_reply_at_def
                          get_refs_def
                   split: option.splits)
   apply (fastforce simp: sym_refs_def symreftype_def)
  apply (clarsimp simp: state_refs_of_def refs_of_def replies_blocked_def st_tcb_at_def obj_at_def
                        replies_with_sc_def sc_replies_sc_at_def reply_tcb_reply_at_def get_refs_def
                 split: option.splits)
  done

lemma si_invs'_helper_no_reply_sts_helper:
  "\<lbrace>\<lambda>s. valid_replies_2 (replies_with_sc s)
         (replies_blocked_upd_tcb_st Running dest (replies_blocked s)) \<and> st_tcb_at active tptr s\<rbrace>
    set_thread_state tptr Inactive
   \<lbrace>\<lambda>rv s. valid_replies_2 (replies_with_sc s)
         (replies_blocked_upd_tcb_st Running dest (replies_blocked s))\<rbrace>"
  apply (wpsimp wp: sts_valid_replies)
  apply (clarsimp simp: replies_blocked_upd_tcb_st_def pred_tcb_at_def obj_at_def cong: conj_cong)
  apply (subgoal_tac "{(r, t'). t' \<noteq> tptr \<and> t' \<noteq> dest \<and> (r, t') \<in> replies_blocked s} =
                      {(r, t'). if t' = dest
                                then Running = BlockedOnReply r
                                else (r, t') \<in> replies_blocked s}", simp)
  apply (clarsimp simp:  pred_tcb_at_def obj_at_def replies_blocked_def)
  apply (fastforce)
  done

lemma sts_refs_of_no_state_refs:
  "\<lbrace>(\<lambda>s. P (state_refs_of s))
        and (st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) t)
        and K (tcb_st_refs_of st = {})\<rbrace>
    set_thread_state t st
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: state_refs_of_def pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                   simp: state_refs_of_def
                 intro!: ext)
  done

lemma si_invs'_helper_no_reply:
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. st_tcb_at active tptr s \<and>
        st_tcb_at (\<lambda>st. \<exists>epptr pl. st = BlockedOnReceive epptr None pl) dest s \<and>
        all_invs_but_sym_refs_and_fault_tcbs s \<and>
        fault_tcbs_valid_states_except_set {tptr} s \<and>
        sym_refs (\<lambda>x. if x = dest
                      then {r \<in> state_refs_of s dest. snd r = TCBBound \<or>
                            snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                      else state_refs_of s x) \<and>
        sym_refs (state_hyp_refs_of s) \<and> (can_donate \<longrightarrow> bound_sc_tcb_at bound tptr s) \<and> Q s\<rbrace>
   do
     sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     fault <- thread_get tcb_fault tptr;
     y <- if call \<or> (\<exists>y. fault = Some y)
          then set_thread_state tptr Inactive
          else when (can_donate \<and> sc_opt = None)
                 (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                     sched_context_donate (the caller_sc_opt) dest
                  od);
     y <- set_thread_state dest Running;
     possible_switch_to dest
  od
  \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac "call \<or> (\<exists>y. fault = Some y)"; simp)
   apply wpsimp
        apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: sts_only_idle valid_irq_node_typ sts_valid_replies
                         sts_fault_tcbs_valid_states valid_ioports_lift)
       apply (wpsimp wp: assert_inv sts_only_idle si_invs'_helper_no_reply_sts_helper
                         sts_refs_of_no_state_refs sts_fault_tcbs_valid_states_except_set
                 wp_del: sts_refs_of)+
   apply (intro conjI)
        apply (fastforce simp: st_tcb_at_def live_def elim!: if_live_then_nonz_capD)
       apply (rule replies_blocked_upd_tcb_st_valid_replies;
              clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def)
      apply (subgoal_tac "dest \<noteq> tptr")
       apply (fastforce elim!: fault_tcbs_valid_states_except_set_not_fault_tcb_states
                               pred_tcb_weakenE
                         simp: pred_neg_def)
      apply (fastforce simp: st_tcb_at_def obj_at_def)
     apply (fastforce simp: st_tcb_at_def obj_at_def)
    apply (subgoal_tac "ex_nonz_cap_to tptr s")
     apply (clarsimp simp: idle_no_ex_cap)
    apply (fastforce simp: st_tcb_at_def live_def obj_at_def elim!: if_live_then_nonz_capD)
   apply (subgoal_tac "ex_nonz_cap_to dest s")
    apply (clarsimp simp: idle_no_ex_cap)
   apply (fastforce simp: st_tcb_at_def live_def elim!: if_live_then_nonz_capD)
  apply (simp add: when_def bind_assoc)
  apply (intro conjI)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ sts_valid_replies
                       sched_context_donate_sym_refs_BlockedOnReceive
                       sts_fault_tcbs_valid_states valid_ioports_lift hoare_drop_imps)
    apply (wpsimp simp: get_tcb_obj_ref_def thread_get_def)
   apply (clarsimp, intro conjI)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply (fastforce simp: live_def elim!: if_live_then_nonz_capD2)
   apply clarsimp
   apply (rename_tac tcb)
   apply (clarsimp cong: conj_cong)
   apply (subgoal_tac "sc_tcb_sc_at (\<lambda>t. t = Some tptr) (the (tcb_sched_context tcb)) s \<and>
                       ex_nonz_cap_to dest s")
    apply (clarsimp, intro conjI)
          apply (fastforce simp: live_def live_sc_def pred_tcb_at_def obj_at_def valid_idle_def
                                 sc_at_pred_n_def
                           elim: if_live_then_nonz_capD2)
         apply (rule replies_blocked_upd_tcb_st_valid_replies;
                clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def)
        apply (erule fault_tcbs_valid_states_from_except_set)
        apply (fastforce simp: pred_tcb_at_def obj_at_def)
       apply (subgoal_tac "dest \<noteq> tptr")
        apply (fastforce elim!: fault_tcbs_valid_states_except_set_not_fault_tcb_states
                                pred_tcb_weakenE
                          simp: pred_neg_def)
       apply (fastforce simp: st_tcb_at_def obj_at_def)
      apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
     apply (clarsimp simp: idle_no_ex_cap)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def st_tcb_at_def live_def idle_no_ex_cap
                    dest!: if_live_then_nonz_capD)
   apply (clarsimp simp: st_tcb_at_def is_tcb obj_at_def)
   apply (intro conjI)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def get_tcb_def pred_tcb_at_def)
    apply (rename_tac scptr)
    apply (subgoal_tac "sc_at scptr s")
     apply (clarsimp simp: sym_refs_def)
     apply (erule_tac x = tptr in allE)
     apply (erule_tac x = "(scptr, TCBSchedContext)" in ballE)
      apply (clarsimp simp: is_sc_obj_def obj_at_def split: if_splits)
      apply (case_tac ko; simp)
      apply (clarsimp simp: state_refs_of_def get_refs_def2)
     apply (clarsimp simp: state_refs_of_def split: if_splits)
    apply (subgoal_tac "valid_obj tptr (TCB tcb) s")
     apply (clarsimp simp: valid_obj_def valid_tcb_def)
    apply (fastforce simp: valid_objsE)
   apply (rule if_live_then_nonz_capD; simp add: pred_tcb_at_def obj_at_def live_def)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: valid_irq_node_typ sts_only_idle sts_valid_replies
                      sts_fault_tcbs_valid_states valid_ioports_lift hoare_drop_imps)
  apply (apply_conjunct \<open>rule replies_blocked_upd_tcb_st_valid_replies;
         clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def\<close>)
  apply (subgoal_tac "ex_nonz_cap_to dest s", clarsimp)
   apply (intro conjI)
     apply (erule fault_tcbs_valid_states_from_except_set)
     apply (fastforce simp: pred_tcb_at_def obj_at_def)
    apply (subgoal_tac "dest \<noteq> tptr")
     apply (fastforce elim!: fault_tcbs_valid_states_except_set_not_fault_tcb_states
                             pred_tcb_weakenE
                       simp: pred_neg_def)
    apply (fastforce simp: st_tcb_at_def obj_at_def)
   apply (clarsimp simp: idle_no_ex_cap)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (fastforce simp: live_def elim!: if_live_then_nonz_capD2)
  done

lemma si_invs'_helper_some_reply:
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. \<exists>rptr. st_tcb_at active tptr s \<and> st_tcb_at ((=) Inactive) dest s \<and>
        all_invs_but_fault_tcbs s \<and>
        fault_tcbs_valid_states_except_set {tptr} s \<and>
        ex_nonz_cap_to tptr s \<and> ex_nonz_cap_to dest s \<and> reply = Some rptr \<and> ex_nonz_cap_to rptr s \<and>
        reply_sc_reply_at (\<lambda>sc. sc = None) rptr s \<and> fault_tcb_at ((=) None) dest s \<and>
        (can_donate \<longrightarrow> bound_sc_tcb_at bound tptr s) \<and> reply_tcb_reply_at (\<lambda>tptr. tptr = None) rptr s
        \<and> Q s\<rbrace>
   do sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then if cg \<and> (\<exists>y. reply = Some y)
                then reply_push tptr dest (the reply) can_donate
                else set_thread_state tptr Inactive
           else when (can_donate \<and> sc_opt = None)
                  (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                      sched_context_donate (the caller_sc_opt) dest
                   od);
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac "call \<or> fault \<noteq> None"; clarsimp split del: if_split)
   apply wpsimp
        apply (strengthen invs_valid_objs, clarsimp cong: conj_cong)
        apply (wpsimp wp: sts_invs_minor2)
    apply (wpsimp wp: hoare_vcg_conj_lift wp_del: reply_push_st_tcb_at)
     apply (rule_tac Q="\<lambda>_. st_tcb_at ((=) Inactive) dest" in hoare_strengthen_post)
      apply (wpsimp wp: reply_push_st_tcb_at_Inactive)
           apply (clarsimp simp: pred_tcb_at_def obj_at_def)
          apply (rule_tac Q="\<lambda>_. st_tcb_at ((=) Inactive) dest" in hoare_strengthen_post)
           apply (wpsimp wp: sts_st_tcb_at_other)
          apply (clarsimp simp: pred_tcb_at_def obj_at_def)
         apply (wpsimp wp: reply_push_invs' sts_invs_minor2')+
   apply (frule active_st_tcb_at_state_refs_ofD)
   apply (frule st_tcb_weakenE[where P'="\<lambda>st. \<not> awaiting_reply st"], fastforce)
   apply (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (intro conjI)
     apply fastforce
    apply (drule (1) idle_no_ex_cap, clarsimp)
   apply (drule (1) idle_no_ex_cap, clarsimp)
  apply wpsimp
    apply (strengthen invs_valid_objs, clarsimp cong: conj_cong)
    apply (wpsimp wp: sts_invs_minor2)
   apply (wpsimp wp: hoare_vcg_conj_lift sched_context_donate_invs
               simp: get_tcb_obj_ref_def thread_get_def)
  apply (subgoal_tac "dest \<noteq> idle_thread s")
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (clarsimp simp: is_tcb pred_tcb_at_def obj_at_def reply_sc_reply_at_def is_sc_obj_def)
   apply (clarsimp simp: get_tcb_rev dest!: get_tcb_SomeD)
   apply (drule fault_tcbs_valid_states_from_except_set)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (rule valid_objsE[where x=tptr]; assumption?)
   apply (clarsimp simp: valid_obj_def valid_tcb_def obj_at_def is_sc_obj_def)
   apply (rename_tac sc_ptr ko n)
   apply (subgoal_tac "sc_tcb_sc_at ((=) (Some tptr)) sc_ptr s")
    apply (fastforce simp: live_def live_sc_def pred_tcb_at_def obj_at_def valid_idle_def
                           sc_at_pred_n_def
                     elim: if_live_then_nonz_capD2)
   apply (case_tac ko; clarsimp)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
   apply (force simp: pred_tcb_at_def obj_at_def
               dest!: bound_sc_tcb_bound_sc_at)
  apply clarsimp
  apply (drule (1) idle_no_ex_cap)
  by simp

lemma not_sk_obj_at_pred:
  "\<not> sk_obj_at_pred C proj' P' p s \<Longrightarrow> sk_obj_at_pred C proj P p s
    \<Longrightarrow> sk_obj_at_pred C proj' (\<lambda>x. \<not> (P' x)) p s"
  by (fastforce simp: sk_obj_at_pred_def obj_at_def)

lemma valid_replies_st_tcb_at_BlockedOnReply:
  assumes invs: "invs s"
  assumes valid_replies: "valid_replies s"
  assumes P: "\<And>sc. P sc \<longleftrightarrow> sc \<noteq> None"
  assumes reply_sc: "reply_sc_reply_at P r s"
  shows "\<exists>t. st_tcb_at (\<lambda>st. st = BlockedOnReply r) t s"
  using invs valid_replies reply_sc[unfolded P]
  apply (subgoal_tac "\<exists>t. (r,t) \<in> replies_blocked s", clarsimp simp: replies_blocked_def)
  apply (clarsimp simp: replies_with_sc_def reply_sc_reply_at_def obj_at_def)
  apply (drule_tac x=r and y=y and tp=SCReply in sym_refsE[OF invs_sym_refs])
   apply (fastforce simp: reply_at_ppred_def pred_tcb_at_def obj_at_def state_refs_of_def refs_of_rev
                   split: option.splits)
  apply (rule valid_repliesD1_simp, assumption)
   apply (clarsimp simp: replies_with_sc_def reply_sc_reply_at_def obj_at_def)
  apply (fastforce simp: state_refs_of_def refs_of_def get_refs_def replies_with_sc_def
                         sc_replies_sc_at_def obj_at_def
          split: option.splits kernel_object.splits)
  done

lemma sym_refs_ignore_update:
  "sym_refs (\<lambda>x. if x = a then S x else T x) \<Longrightarrow>
   \<forall>x y tp. (x\<noteq>a) \<longrightarrow> (y\<noteq>a) \<longrightarrow> ((y, symreftype tp) \<in> T x \<longrightarrow> (x, tp) \<in> T y)"
  apply (clarsimp simp: sym_refs_def)
  apply (drule_tac x=x in spec)
  apply (drule_tac x="(y,symreftype tp)" in bspec; clarsimp)
  done

lemma si_invs'_helper_fault:
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. all_invs_but_sym_refs_and_fault_tcbs s \<and>
        fault_tcbs_valid_states_except_set {tptr} s \<and>
        Q s \<and> st_tcb_at active tptr s \<and> ex_nonz_cap_to tptr s \<and>
        (can_donate \<longrightarrow> bound_sc_tcb_at bound tptr s) \<and> ep_at epptr s \<and>
        (\<forall>x. (dest, x) \<notin> state_refs_of s epptr) \<and>
        st_tcb_at (\<lambda>st. \<exists>r pl. st = BlockedOnReceive epptr r pl) dest s \<and> ex_nonz_cap_to epptr s \<and>
        sym_refs (\<lambda>x. if x = dest
                      then {r \<in> state_refs_of s x. snd r = TCBBound \<or> snd r = TCBSchedContext \<or>
                            snd r = TCBYieldTo \<or> snd r = TCBReply}
                      else state_refs_of s x) \<and>
        sym_refs (state_hyp_refs_of s)\<rbrace>
    do
      recv_state <- get_thread_state dest;
      reply <- case recv_state of BlockedOnReceive _ reply data \<Rightarrow>
                                      return reply
                                  | _ \<Rightarrow> fail;
      y <- do_ipc_transfer tptr (Some epptr) ba cg dest;
      y <- maybeM (reply_unlink_tcb dest) reply;
      sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then if (cg \<or> cgr) \<and> (\<exists>y. reply = Some y)
                then reply_push tptr dest (the reply) can_donate
                else set_thread_state tptr Inactive
           else when (can_donate \<and> sc_opt = None) (do thread_sc <- get_tcb_obj_ref tcb_sched_context tptr;
                                                       sched_context_donate (the thread_sc) dest
                                                   od);
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  supply if_weak_cong[cong del]
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac recv_state; simp split del: if_split)
  apply (rename_tac r pl)
  apply (case_tac r, simp split del: if_split)
   apply (wpsimp wp: si_invs'_helper_no_reply)
   apply (intro conjI)
       apply (clarsimp simp: st_tcb_at_def obj_at_def)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
   apply (clarsimp simp: sym_refs_def)
   apply (intro conjI)
    apply (fastforce dest!: st_tcb_at_tcb_at tcb_state_refs_no_tcb bspec)
   apply clarsimp
   apply (intro conjI)
    apply clarsimp
    apply (rename_tac s x reftype)
    apply (subgoal_tac "(x, symreftype reftype) \<in> state_refs_of s dest")
     apply (fastforce simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2)
    apply (erule_tac x = x in allE, fastforce)
   apply (fastforce dest!: bspec)
  apply (rename_tac rptr)
  apply (wpsimp wp: si_invs'_helper_some_reply wp_del: maybeM_inv split_del: if_split)
    apply (rule hoare_vcg_conj_lift)
     apply (wpsimp wp: reply_unlink_tcb_st_tcb_at')
    apply (wpsimp wp: reply_unlink_tcb_sym_refs_BlockedOnReceive
                      reply_unlink_tcb_valid_replies_BlockedOnReceive
                      reply_unlink_tcb_bound_sc_tcb_at hoare_vcg_imp_lift
                      reply_unlink_tcb_reply_tcb_reply_at)
   apply (wpsimp wp: hoare_ex_wp valid_irq_node_typ hoare_vcg_imp_lift)
  apply clarsimp
  apply (subgoal_tac "reply_tcb_reply_at (\<lambda>b. b = Some dest) rptr s")
   apply (intro conjI)
            apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def st_tcb_at_def)
           apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
          apply fastforce
         apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
        apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
       apply fastforce
      apply (clarsimp simp: st_tcb_at_def obj_at_def)
      apply (fastforce simp: live_def elim!: if_live_then_nonz_capD2)
     apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def)
     apply (fastforce simp: live_def live_reply_def elim!: if_live_then_nonz_capD2)
    apply (rule ccontr)
    apply (drule (1) not_sk_obj_at_pred)
    apply (subgoal_tac "\<exists>t. st_tcb_at (\<lambda>st. st = BlockedOnReply rptr) t s")
     apply (clarsimp simp: reply_at_ppred_def pred_tcb_at_def obj_at_def is_ep)
     apply (rule_tac V="rptr \<noteq> dest \<and> t \<noteq> dest" in revcut_rl, fastforce, elim conjE)
     apply (drule_tac x=t and y=rptr and tp=ReplyTCB in sym_refsE; clarsimp simp: state_refs_of_def)
    apply (rule valid_repliesE1, simp)
    apply (drule sym_refs_ignore_update)
    apply (clarsimp simp: reply_sc_reply_at_def obj_at_def)
    apply (frule valid_objs_Some_reply_sc, assumption+, elim exE)
    apply (subgoal_tac "(y, ReplySchedContext) \<in> state_refs_of s rptr")
     apply (subgoal_tac "(rptr, SCReply) \<in> state_refs_of s y")
      apply (clarsimp simp: sc_replies_sc_at_def obj_at_def)
      apply (rule_tac x=y in exI)
      apply (rule_tac x="SchedContext sc n" in exI, clarsimp)
      apply (fastforce simp: state_refs_of_def get_refs_def split: option.splits)
     apply (subgoal_tac "rptr\<noteq> dest \<and> y\<noteq>dest";
            fastforce simp: st_tcb_at_def obj_at_def symreftype_def)
    apply (fastforce simp: state_refs_of_def)
   apply (subgoal_tac "dest \<noteq> tptr")
    apply (fastforce elim!: fault_tcbs_valid_states_except_set_not_fault_tcb_states
                            pred_tcb_weakenE
                      simp: pred_neg_def is_blocked_thread_state_defs)
   apply (fastforce simp: st_tcb_at_def obj_at_def)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (subgoal_tac "valid_obj dest (TCB tcb) s")
   apply (fastforce simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_reply sym_refs_def
                          reply_tcb_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                   split: if_splits)
  apply fastforce
  done

lemma si_invs'_helper:
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. all_invs_but_sym_refs s \<and>
        Q s \<and> st_tcb_at active tptr s \<and> ex_nonz_cap_to tptr s \<and>
        (can_donate \<longrightarrow> bound_sc_tcb_at bound tptr s) \<and> ep_at epptr s \<and>
        (\<forall>x. (dest, x) \<notin> state_refs_of s epptr) \<and>
        st_tcb_at (\<lambda>st. \<exists>r pl. st = BlockedOnReceive epptr r pl) dest s \<and> ex_nonz_cap_to epptr s \<and>
        sym_refs (\<lambda>x. if x = dest
                      then {r \<in> state_refs_of s x. snd r = TCBBound \<or> snd r = TCBSchedContext \<or>
                            snd r = TCBYieldTo \<or> snd r = TCBReply}
                      else state_refs_of s x) \<and>
        sym_refs (state_hyp_refs_of s)\<rbrace>
    do
      recv_state <- get_thread_state dest;
      reply <- case recv_state of
                                    BlockedOnReceive _ reply data \<Rightarrow>
                                      return reply
                                  | _ \<Rightarrow> fail;
      y <- do_ipc_transfer tptr (Some epptr) ba cg dest;
      y <- maybeM (reply_unlink_tcb dest) reply;
      sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then if (cg \<or> cgr) \<and> (\<exists>y. reply = Some y)
                then reply_push tptr dest (the reply) can_donate
                else set_thread_state tptr Inactive
           else when (can_donate \<and> sc_opt = None) (do thread_sc <- get_tcb_obj_ref tcb_sched_context tptr;
                                                       sched_context_donate (the thread_sc) dest
                                                   od);
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  by (wpsimp wp: si_invs'_helper_fault simp: fault_tcbs_valid_states_to_except_set)

lemma si_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>invs and Q and st_tcb_at active tptr and ex_nonz_cap_to tptr and (\<lambda>s. can_donate \<longrightarrow> bound_sc_tcb_at bound tptr s)
    and ex_nonz_cap_to epptr\<rbrace>
   send_ipc bl call ba cg crg can_donate tptr epptr
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (cases bl, simp_all)[1]
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (wpsimp wp: valid_irq_node_typ valid_ioports_lift)
      apply (simp add: live_def valid_ep_def)
      apply (wp valid_irq_node_typ sts_only_idle sts_typ_ats(1)[simplified ep_at_def2, simplified]
                sts_valid_replies sts_fault_tcbs_valid_states)
     apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at valid_ep_def)
     apply (apply_conjunct \<open>rule replies_blocked_upd_tcb_st_valid_replies; clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def\<close>)
     apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
     apply (rule conjI, subgoal_tac "tptr \<noteq> epptr")
       apply (drule active_st_tcb_at_state_refs_ofD)
       apply (rule delta_sym_refs, assumption)
        apply (clarsimp split: if_splits)
       apply (clarsimp simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                      split: if_splits)
      apply (clarsimp simp: st_tcb_at_def obj_at_def)
     apply (clarsimp simp: idle_no_ex_cap)
    apply wpsimp
   apply (case_tac bl; simp)
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wpsimp simp: live_def
                    wp: tcb_ep_append_valid_SendEP sts_valid_replies
                        sts_fault_tcbs_valid_states valid_ioports_lift)
     apply (wpsimp simp: valid_ep_def
                     wp: hoare_vcg_const_Ball_lift sts_only_idle valid_irq_node_typ)
    apply (clarsimp simp: valid_tcb_state_def valid_ep_def)
    apply (intro conjI)
            apply (clarsimp simp: is_ep obj_at_def)
           apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb_def)
          apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def elim!: valid_objsE)
         apply (fastforce simp: st_tcb_at_def get_refs_def2 obj_at_def dest!: sym_refs_ko_atD)
        apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def)
       apply (fastforce simp: st_tcb_at_def get_refs_def2 obj_at_def dest!: sym_refs_ko_atD)
      apply (rule replies_blocked_upd_tcb_st_valid_replies_not_blocked;
             clarsimp intro!: not_BlockedOnReply_not_in_replies_blocked elim!: st_tcb_weakenE)
     apply (rule delta_sym_refs, assumption)
      apply (fastforce simp: obj_at_def pred_tcb_at_def state_refs_of_def split: if_splits)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                           tcb_st_refs_of_def
                    split: if_splits thread_state.splits)
    apply (fastforce simp: idle_no_ex_cap)
   apply wpsimp
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rename_tac dest tail)
  apply (wpsimp wp: si_invs'_helper valid_ioports_lift)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (intro conjI)
      apply (fastforce simp: valid_ep_def obj_at_def valid_obj_def
                      split: list.splits
                      elim!: valid_objsE)
     apply (clarsimp simp: is_ep obj_at_def)
    apply (fastforce simp: obj_at_def valid_obj_def valid_ep_def split: list.splits)
   apply (frule (1) sym_refs_ko_atD)
   apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def get_refs_def2
                          tcb_st_refs_of_def st_tcb_at_def
                   elim!: valid_objsE
                   split: thread_state.splits if_splits)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def state_refs_of_def split: list.splits if_splits)
  apply clarsimp
  apply (intro conjI)
   apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def)
  apply (clarsimp, intro conjI)
   apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def
                   split: list.splits if_splits)
  apply (clarsimp, intro conjI)
   apply (clarsimp simp: obj_at_def split: if_splits)
   apply (erule (1) pspace_valid_objsE)
   apply (fastforce simp: state_refs_of_def)
  apply (clarsimp simp: obj_at_def split: if_splits)
   apply (subgoal_tac "st_tcb_at (\<lambda>st. \<exists>r pl. st = BlockedOnReceive epptr r pl) dest s")
    apply (clarsimp simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                   split: if_splits)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ep_def st_tcb_at_def obj_at_def)
   apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply (clarsimp simp: is_tcb get_refs_def2 tcb_st_refs_of_def
                  split: thread_state.splits if_splits)
  apply (clarsimp simp: sym_refs_ko_atD obj_at_def split: list.splits)
  done

lemmas si_invs = si_invs'[where Q=\<top>,OF hoare_TrueI hoare_TrueI hoare_TrueI hoare_TrueI,simplified]

lemma si_invs'_fault:
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {tptr} and Q
    and st_tcb_at active tptr and ex_nonz_cap_to tptr
    and (\<lambda>s. can_donate \<longrightarrow> bound_sc_tcb_at bound tptr s) and ex_nonz_cap_to epptr\<rbrace>
   send_ipc True call ba cg crg can_donate tptr epptr
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wpsimp wp: valid_irq_node_typ valid_ioports_lift)
     apply (simp add: live_def valid_ep_def)
     apply (wp valid_irq_node_typ sts_only_idle sts_typ_ats(1)[simplified ep_at_def2, simplified]
               sts_valid_replies sts_fault_tcbs_valid_states_except_set)
    apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at valid_ep_def)
    apply (apply_conjunct \<open>rule replies_blocked_upd_tcb_st_valid_replies; clarsimp simp: replies_blocked_def st_tcb_at_def obj_at_def\<close>)
    apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
    apply (rule conjI, subgoal_tac "tptr \<noteq> epptr")
      apply (drule active_st_tcb_at_state_refs_ofD)
      apply (rule delta_sym_refs, assumption)
       apply (clarsimp split: if_splits)
      apply (clarsimp simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                     split: if_splits)
     apply (clarsimp simp: st_tcb_at_def obj_at_def)
    apply (clarsimp simp: idle_no_ex_cap)
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (wpsimp simp: live_def
                   wp: tcb_ep_append_valid_SendEP sts_valid_replies
                       sts_fault_tcbs_valid_states_except_set valid_ioports_lift)
    apply (wpsimp simp: valid_ep_def
                    wp: hoare_vcg_const_Ball_lift sts_only_idle valid_irq_node_typ)
   apply (clarsimp simp: valid_tcb_state_def valid_ep_def)
   apply (intro conjI)
 apply (clarsimp simp: is_ep obj_at_def)
           apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb_def)
          apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def elim!: valid_objsE)
         apply (fastforce simp: st_tcb_at_def get_refs_def2 obj_at_def dest!: sym_refs_ko_atD)
        apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def)
       apply (fastforce simp: st_tcb_at_def get_refs_def2 obj_at_def dest!: sym_refs_ko_atD)
     apply (rule replies_blocked_upd_tcb_st_valid_replies_not_blocked;
            clarsimp intro!: not_BlockedOnReply_not_in_replies_blocked elim!: st_tcb_weakenE)
    apply (rule delta_sym_refs, assumption)
     apply (fastforce simp: obj_at_def pred_tcb_at_def state_refs_of_def split: if_splits)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                          tcb_st_refs_of_def
                   split: if_splits thread_state.splits)
   apply (fastforce simp: idle_no_ex_cap)
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rename_tac dest tail)
  apply (wpsimp wp: si_invs'_helper_fault valid_ioports_lift)
  apply (intro conjI)
      apply (fastforce simp: valid_ep_def obj_at_def valid_obj_def
                      split: list.splits
                      elim!: valid_objsE)
     apply (clarsimp simp: is_ep obj_at_def)
    apply (fastforce simp: obj_at_def valid_obj_def valid_ep_def split: list.splits)
   apply (frule (1) sym_refs_ko_atD)
   apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def get_refs_def2
                          tcb_st_refs_of_def st_tcb_at_def
                   elim!: valid_objsE
                   split: thread_state.splits if_splits)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def state_refs_of_def split: list.splits if_splits)
  apply clarsimp
  apply (intro conjI)
   apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def)
  apply (clarsimp, intro conjI)
   apply (fastforce simp: valid_obj_def valid_ep_def is_tcb obj_at_def
                   split: list.splits if_splits)
  apply (clarsimp, intro conjI)
   apply (clarsimp simp: obj_at_def split: if_splits)
   apply (erule (1) pspace_valid_objsE)
   apply (fastforce simp: state_refs_of_def)
  apply (clarsimp simp: obj_at_def split: if_splits)
   apply (subgoal_tac "st_tcb_at (\<lambda>st. \<exists>r pl. st = BlockedOnReceive epptr r pl) dest s")
    apply (clarsimp simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                   split: if_splits)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ep_def st_tcb_at_def obj_at_def)
   apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply (clarsimp simp: is_tcb get_refs_def2 tcb_st_refs_of_def
                  split: thread_state.splits if_splits)
  apply (clarsimp simp: sym_refs_ko_atD obj_at_def split: list.splits)
  done

lemma hf_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace>
                                               do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes thread_set_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> thread_set a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>t r. \<lbrace>Q\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_. Q\<rbrace>"
  notes si_invs''[wp] = si_invs'_fault[where Q=Q]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and (\<lambda>_. valid_fault f)\<rbrace>
   handle_fault t f
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>" including no_pre
  apply (cases "valid_fault f"; simp)
  apply (rule hoare_pre)
  apply (simp add: handle_fault_def handle_no_fault_def)
   apply (wpsimp wp: sts_invs_minor)
     apply (simp add: send_fault_ipc_def)
     apply (wpsimp wp: test thread_set_invs_but_fault_tcbs
                       thread_set_no_change_tcb_state ex_nonz_cap_to_pres
                       thread_set_cte_wp_at_trivial
                       thread_set_no_change_tcb_sched_context
                       hoare_vcg_imp_lift gbn_wp
            | clarsimp simp: tcb_cap_cases_def
            | erule disjE)+
  apply (rule conjI)
   apply (fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def
                    dest: invs_valid_idle)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_ko_at)
  apply (rule conjI)
   apply fastforce
  apply (simp (no_asm) add: ex_nonz_cap_to_def cte_wp_at_cases2)
  apply (rule_tac x = t in exI)
  apply (rule_tac x = "tcb_cnode_index 3" in exI)
  apply (clarsimp simp: obj_at_def tcb_cnode_map_def)
  done

lemmas hf_invs[wp] = hf_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI TrueI,simplified]

lemma valid_bound_sc_typ_at:
  "\<forall>p. \<lbrace>\<lambda>s. sc_at p s\<rbrace> f \<lbrace>\<lambda>_ s. sc_at p s\<rbrace>
    \<Longrightarrow> \<lbrace>\<lambda>s. valid_bound_sc sc s\<rbrace> f \<lbrace>\<lambda>_ s. valid_bound_sc sc s\<rbrace>"
  apply (clarsimp simp: valid_bound_obj_def split: option.splits)
  apply (wpsimp wp: hoare_vcg_all_lift static_imp_wp)
   defer
   apply assumption
  apply fastforce
  done

lemma set_thread_state_set_tcb_at[wp]:
  "\<lbrace>\<lambda>s. \<forall>t\<in>set q. tcb_at t s\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. \<forall>t\<in>set q. tcb_at t s\<rbrace>"
  by (wpsimp wp: hoare_vcg_ball_lift)

lemma valid_bound_tcb_scheduler_action_update[simp]: (* FIXME: move *)
  "valid_bound_tcb t (scheduler_action_update f s) = valid_bound_tcb t s"
  by (auto simp: valid_bound_obj_def split: option.splits)

lemma valid_bound_sc_scheduler_action_update[simp]: (* FIXME: move *)
  "valid_bound_sc t (scheduler_action_update f s) = valid_bound_sc t s"
  by (auto simp: valid_bound_obj_def split: option.splits)

crunches set_thread_state_act
  for valid_bound_tcb[wp]: "valid_bound_tcb t"
  and valid_bound_sc[wp]: "valid_bound_sc t"
  (ignore: set_object)

lemma set_thread_state_valid_bound_tcb[wp]:
  "\<lbrace>valid_bound_tcb t'\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. valid_bound_tcb t'\<rbrace>"
  by (wpsimp simp: set_thread_state_def valid_bound_obj_def is_tcb obj_at_def wp: set_object_wp
             split: option.splits)

lemma set_thread_state_valid_bound_sc[wp]:
  "\<lbrace>valid_bound_sc sc\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. valid_bound_sc sc\<rbrace>"
  apply (wpsimp simp: set_thread_state_def valid_bound_obj_def wp: set_object_wp
               split: option.splits)
  apply (clarsimp simp: is_sc_obj_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma as_user_bound_obj_typ_at[wp]:
  "as_user t f \<lbrace>valid_bound_obj (typ_at T) p\<rbrace>"
  apply (wpsimp simp: as_user_def valid_bound_obj_def wp: set_object_wp split: option.splits)
  apply (clarsimp simp: is_sc_obj_def obj_at_def get_tcb_SomeD)
  done

lemma as_user_bound_sc[wp]:
  "as_user t f \<lbrace>valid_bound_sc sc\<rbrace>"
  apply (wpsimp simp: as_user_def valid_bound_obj_def wp: set_object_wp split: option.splits)
  apply (clarsimp simp: is_sc_obj_def obj_at_def get_tcb_SomeD)
  done

lemma schedule_tcb_invs':
  "\<lbrace>\<lambda>s. (valid_state s \<and> cur_tcb s \<and>
         tcb_ptr = cur_thread s \<and> scheduler_action s = resume_cur_thread \<and>
         bound_sc_tcb_at ((=) None) (cur_thread s) s \<and>
         sc_tcb_sc_at ((=) None) (cur_sc s) s) \<or> invs s\<rbrace>
   schedule_tcb tcb_ptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_vcg_disj_lift[where Q = "\<lambda>_. invs" and Q' = "\<lambda>_. invs", simplified])
   apply (simp add: schedule_tcb_def)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
   apply (simp add: when_def reschedule_required_def)
   apply (intro conjI)
    prefer 2
    apply (wpsimp wp: hoare_pre_cont)
    apply (clarsimp simp: is_schedulable_opt_def pred_tcb_at_def obj_at_def get_tcb_def)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (case_tac action; simp)
     apply (wpsimp simp: set_scheduler_action_def wp_del: set_scheduler_action_invs)
     apply (clarsimp simp: invs_def valid_state_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)
    apply (wpsimp wp: hoare_pre_cont)
   apply wpsimp
  apply wpsimp
  done

lemma set_sc_obj_ref_bound_sc_tcb_at_cur_thread [wp]:
  "\<lbrace>\<lambda>s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>
   set_sc_obj_ref f ref new
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at P (cur_thread s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def
                   pred_tcb_at_def obj_at_def)

lemma set_sc_tcb_cur_sc [wp]:
  "\<lbrace>\<lambda>s. sc_ptr = cur_sc s\<rbrace>
   set_sc_obj_ref sc_tcb_update sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. sc_tcb_sc_at ((=) tcb_ptr) (cur_sc s) s\<rbrace>"
  by (wpsimp simp: update_sched_context_def set_object_def get_object_def
                   sc_tcb_sc_at_def obj_at_def)

lemma set_tcb_sc_cur_thread [wp]:
  "\<lbrace>\<lambda>s. tcb_ptr = cur_thread s\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tcb_ptr sc_ptr
   \<lbrace>\<lambda>rv s. bound_sc_tcb_at ((=) sc_ptr) (cur_thread s) s\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def pred_tcb_at_def obj_at_def wp: set_object_wp)

lemma maybe_return_sc_schedule_tcb:
  "\<lbrace>invs and (\<lambda>s. tcb_ptr \<noteq> idle_thread s)\<rbrace>
   do
     _ <- maybe_return_sc ntfn_ptr tcb_ptr;
     schedule_tcb tcb_ptr
   od
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_seq_ext[OF schedule_tcb_invs'])
  apply (wpsimp wp: hoare_vcg_disj_lift)
  apply (rule hoare_pre_cont)
  apply (wpsimp wp: hoare_vcg_disj_lift)
  by auto

lemma rai_invs':
  assumes set_notification_Q[wp]: "\<And>a b.\<lbrace> Q\<rbrace> set_notification a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes smi_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_message_info a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes as_user_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> as_user a b \<lbrace>\<lambda>r::unit. Q\<rbrace>"
  assumes set_mrs_Q[wp]: "\<And>a b c. \<lbrace>Q\<rbrace> set_mrs a b c \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes schedule_tcb_Q[wp]: "\<And>t. \<lbrace>Q\<rbrace> schedule_tcb t \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes maybe_return_sc[wp]: "\<And>ntfn t. \<lbrace>Q\<rbrace> maybe_return_sc ntfn t \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes maybe_donate_sc[wp]: "\<And>t ntfn. \<lbrace>Q\<rbrace> maybe_donate_sc t ntfn \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
         and (\<lambda>s. \<exists>ntfnptr. is_ntfn_cap cap \<and> cap_ep_ptr cap = ntfnptr \<and>
                     obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_bound_tcb ntfn = None
                             \<or> ntfn_bound_tcb ntfn = Some t)) ntfnptr s)\<rbrace>
     receive_signal t cap is_blocking
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: receive_signal_def)
  apply (cases cap, simp_all)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rename_tac notification, case_tac "ntfn_obj notification"; simp)
    apply (case_tac is_blocking; simp)
     apply (wpsimp simp: live_def live_ntfn_def invs_def valid_state_def valid_pspace_def
                     wp: sts_only_idle sts_valid_replies
                         sts_fault_tcbs_valid_states valid_ioports_lift)
     apply (clarsimp simp: valid_tcb_state_def
                           ntfn_at_typ obj_at_def  is_tcb valid_ntfn_def)
     apply (intro conjI)
            apply (clarsimp simp: pred_tcb_at_def obj_at_def)
           apply (clarsimp split: option.splits)
          apply (clarsimp simp: valid_bound_obj_def is_tcb pred_tcb_at_def obj_at_def
                         split: option.splits)
         apply (fastforce simp: valid_obj_def valid_ntfn_def)
        apply (rule replies_blocked_upd_tcb_st_valid_replies_not_blocked;
               clarsimp intro!: not_BlockedOnReply_not_in_replies_blocked
                          simp: st_tcb_at_def obj_at_def)
       apply (fastforce elim: fault_tcbs_valid_states_active)
      apply (fastforce simp: state_refs_of_def get_refs_def2 pred_tcb_at_def obj_at_def
                      split: if_splits
                      elim!: delta_sym_refs)
     apply (clarsimp simp: idle_no_ex_cap)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def wp: valid_irq_node_typ)
   apply (case_tac is_blocking; simp)
    apply (rule hoare_weaken_pre)
     apply (rule_tac P="ntfn_bound_tcb notification = None" in hoare_gen_asm)
     apply (wpsimp wp: maybe_return_sc_schedule_tcb sts_only_idle sts_valid_replies
                       sts_fault_tcbs_valid_states valid_ioports_lift
                       valid_irq_node_typ[where f="as_user t f" for t f]
                 simp: invs_def valid_state_def valid_pspace_def valid_tcb_state_def
                       valid_ntfn_def live_ntfn_def live_def do_nbrecv_failed_transfer_def)+
    apply (rule conjI, clarsimp simp: is_ntfn obj_at_def)
    apply (rule conjI, clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
    apply (rule obj_at_valid_objsE, assumption+)
    apply (rule conjI, clarsimp simp: valid_obj_def valid_ntfn_def)
    apply (clarsimp simp: valid_obj_def valid_ntfn_def)
    apply (rule conjI,
           fastforce simp: obj_at_def st_tcb_at_def get_refs_def2 dest!: sym_refs_ko_atD bspec)
    apply (apply_conjunct \<open>rule replies_blocked_upd_tcb_st_valid_replies_not_blocked;
                          clarsimp intro!: not_BlockedOnReply_not_in_replies_blocked
                                     simp: st_tcb_at_def obj_at_def\<close>)
    apply (subgoal_tac "ntfn_bound_tcb notification = None")
     apply (rule conjI, fastforce elim: fault_tcbs_valid_states_active)
     apply (rule conjI, rule delta_sym_refs, assumption)
       apply (fastforce simp: state_refs_of_def obj_at_def st_tcb_at_def split: if_splits)
      apply (fastforce simp: state_refs_of_def st_tcb_at_def obj_at_def get_refs_def2
                      split: if_splits)
     apply (clarsimp simp: idle_no_ex_cap)
    apply (fastforce simp: idle_no_ex_cap obj_at_def st_tcb_at_def get_refs_def2
                    dest!: sym_refs_ko_atD bspec)
   apply (wpsimp simp: do_nbrecv_failed_transfer_def wp: valid_irq_node_typ)
  apply wpsimp
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: valid_ioports_lift)
   apply (wpsimp simp: valid_ntfn_def tcb_at_typ wp: static_imp_wp valid_irq_node_typ valid_ioports_lift)
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def state_refs_of_def valid_obj_def
                         valid_ntfn_def tcb_at_typ
                  elim!: obj_at_valid_objsE delta_sym_refs
                  split: if_splits)
  done

lemmas rai_invs[wp] =
  rai_invs'[where Q=\<top>, simplified hoare_post_taut, OF TrueI TrueI TrueI, simplified]

end
