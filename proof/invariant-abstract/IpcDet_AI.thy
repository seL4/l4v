(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory IpcDet_AI
imports
  "Lib.MonadicRewrite"
  "./$L4V_ARCH/ArchIpc_AI"
begin

crunch typ_at[wp]: send_ipc "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps mapM_wp_inv maybeM_inv simp: crunch_simps)

lemma si_tcb_at [wp]:
  "\<And>t' call bl w d cd t ep.
    \<lbrace>tcb_at t'\<rbrace>
      send_ipc call bl w d cd t ep
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

lemma sort_queue_valid_ep_helper:
  "distinct list \<Longrightarrow> (a, b) \<in> set (zip list' list) \<Longrightarrow> (a', b) \<in> set (zip list' list) \<Longrightarrow> a = a'"
  apply (induct list arbitrary: list')
   apply clarsimp
  apply (clarsimp simp: zip_Cons)
  apply (erule disjE, fastforce dest!: in_set_zipE)
  apply (erule disjE, fastforce dest!: in_set_zipE, clarsimp)
  done

lemma sort_queue_valid_ep_RecvEP:
  "\<lbrace>valid_ep (RecvEP q)\<rbrace> sort_queue q \<lbrace>\<lambda>q'. valid_ep (RecvEP q')\<rbrace>"
  apply (clarsimp simp: valid_def valid_ep_def)
  apply (case_tac q; simp)
  apply (intro conjI)
    apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (erule disjE)
    apply (frule use_valid[OF _ thread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (rename_tac tptr list s')
   apply (erule_tac x = tptr in ballE)
    apply (rotate_tac -1)
    apply (frule use_valid[OF _ thread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (erule in_set_zipE, clarsimp)
  apply (clarsimp simp: sort_queue_def return_def bind_def mapM_Cons)
  apply (clarsimp simp: distinct_map set_insort_key)
  apply (intro conjI)
    apply (fastforce simp: distinct_insort distinct_zipI2 dest!: in_set_zipE)
   apply (clarsimp simp: inj_on_def sort_queue_valid_ep_helper)
  apply (fastforce dest!: in_set_zipE)
  done

lemma sort_queue_valid_ep_SendEP:
  "\<lbrace>valid_ep (SendEP q)\<rbrace> sort_queue q \<lbrace>\<lambda>q'. valid_ep (SendEP q')\<rbrace>"
  apply (clarsimp simp: valid_def valid_ep_def)
  apply (case_tac q; simp)
  apply (intro conjI)
    apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (erule disjE)
    apply (frule use_valid[OF _ thread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (rename_tac tptr list s')
   apply (erule_tac x = tptr in ballE)
    apply (rotate_tac -1)
    apply (frule use_valid[OF _ thread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (erule in_set_zipE, clarsimp)
  apply (clarsimp simp: sort_queue_def return_def bind_def mapM_Cons)
  apply (clarsimp simp: distinct_map set_insort_key)
  apply (intro conjI)
    apply (fastforce simp: distinct_insort distinct_zipI2 dest!: in_set_zipE)
   apply (clarsimp simp: inj_on_def sort_queue_valid_ep_helper)
  apply (fastforce dest!: in_set_zipE)
  done

declare sort_queue_inv[wp]

lemma sort_queue_rv_wf:
  "\<lbrace>\<top>\<rbrace> sort_queue q \<lbrace>\<lambda>rv s. set rv = set q\<rbrace>"
  apply (clarsimp simp: valid_def sort_queue_def in_monad)
  apply (subgoal_tac "length prios = length q")
   apply (frule map_snd_zip)
   apply (simp add: image_set)
  apply (clarsimp simp: mapM_def)
  apply (induct q, clarsimp simp: sequence_def return_def)
  apply (clarsimp simp: sequence_def in_monad)
  done

lemma sort_queue_rv_wf'[wp]:
  "\<lbrace>P (set q)\<rbrace> sort_queue q \<lbrace>\<lambda>rv. P (set rv)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid[OF _ sort_queue_rv_wf], simp, simp)
  apply (frule use_valid[OF _ sort_queue_inv, where P = "P (set q)"], simp+)
  done

lemma sort_queue_distinct[wp]:
  "\<lbrace>\<lambda>s. distinct q\<rbrace> sort_queue q \<lbrace>\<lambda>q' s. distinct q'\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (case_tac q; simp)
   apply (clarsimp simp: sort_queue_def return_def bind_def)
  apply (clarsimp simp: sort_queue_def return_def bind_def mapM_Cons)
  apply (clarsimp simp: distinct_map set_insort_key)
  apply (intro conjI)
    apply (simp only: sort_key_simps[symmetric] distinct_sort)
    apply (clarsimp simp: distinct_zipI2 elim!: in_set_zipE)
   apply (clarsimp simp: inj_on_def sort_queue_valid_ep_helper)
  apply (clarsimp elim!: in_set_zipE)
  done

lemma gt_reply_sp:
  "\<lbrace>P\<rbrace> get_reply_obj_ref reply_tcb rptr
   \<lbrace>\<lambda>t s. (\<exists>r. kheap s rptr = Some (Reply r) \<and> reply_tcb r = t) \<and> P s\<rbrace>"
  apply (wpsimp simp: get_sk_obj_ref_def get_simple_ko_def get_object_def)
  apply auto
  done

(* FIXME: rename *)
lemma cancel_ipc_st_tcb_at_active:
  "\<lbrace>\<lambda>s. invs s \<and> st_tcb_at st t' s \<and> t \<noteq> t'\<rbrace>
   cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at st t'\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; simp)
         apply wpsimp+

      apply (wpsimp wp: blocked_ipc_st_tcb_at_general)
      apply (clarsimp simp: invs_def valid_state_def valid_pspace_def st_tcb_at_def obj_at_def
                     split: option.splits)
      apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
      apply (clarsimp simp: tcb_st_refs_of_def split: thread_state.splits)
      apply (erule (1) pspace_valid_objsE)
      apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_reply obj_at_def
                            get_refs_def2 reply_tcb_reply_at_def)
     apply (wpsimp wp: blocked_ipc_st_tcb_at_general)
    apply (wpsimp simp: st_tcb_at_def obj_at_def invs_def valid_state_def valid_pspace_def
                    wp: reply_ipc_st_tcb_at_general)
    apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
    apply (clarsimp simp: tcb_st_refs_of_def split: thread_state.splits)
    apply (erule (1) pspace_valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_reply obj_at_def
                          get_refs_def2 reply_tcb_reply_at_def)

   apply (wpsimp wp: cancel_signal_st_tcb_at_general)
  apply wpsimp
  done

crunches update_sk_obj_ref
  for valid_irq_node[wp]: "valid_irq_node"

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
                | ReplyCap r \<Rightarrow>
                    do tptr <- get_reply_obj_ref reply_tcb r;
                       when (tptr \<noteq> None \<and> the tptr \<noteq> t) $ cancel_ipc (the tptr);
                       return (Some r)
                    od
                | _ \<Rightarrow> fail"

crunches receive_ipc_preamble
  for invs: "invs"
  and caps_of_state: "\<lambda>s. P (caps_of_state s)"

lemma receive_ipc_preamble_st_tcb_at:
  "\<lbrace>invs and st_tcb_at st t\<rbrace> receive_ipc_preamble reply t \<lbrace>\<lambda>rv. st_tcb_at st t\<rbrace>"
  by (wpsimp simp: receive_ipc_preamble_def
               wp: cancel_ipc_st_tcb_at_active hoare_vcg_if_lift2 get_sk_obj_ref_inv
      | wp_once hoare_drop_imps)+

global_interpretation set_tcb_obj_ref: non_reply_op "set_tcb_obj_ref f ref new"
  apply unfold_locales
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (clarsimp simp: reply_at_ppred_def obj_at_def get_tcb_def
              split: option.splits kernel_object.splits)

global_interpretation set_endpoint: non_sc_op "set_endpoint p ep"
  by unfold_locales (clarsimp simp add: sc_at_pred_n_def set_endpoint_obj_at_impossible)

global_interpretation reply_unlink_tcb: non_reply_sc_op "reply_unlink_tcb r"
  apply unfold_locales
  apply (wpsimp simp: reply_unlink_tcb_def
                  wp: get_simple_ko_wp set_reply_reply_tcb_update_reply_sc_reply_at gts_wp)
  by (auto simp: reply_sc_reply_at_def obj_at_def)

lemma reply_unlink_tcb_reply_tcb_reply_at:
  "\<lbrace> \<lambda>s. P (P' None) \<and> (p \<noteq> r \<longrightarrow> P (reply_tcb_reply_at P' p s)) \<rbrace>
    reply_unlink_tcb r
   \<lbrace> \<lambda>rv s. P (reply_tcb_reply_at P' p s) \<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def wp: set_simple_ko_wps get_simple_ko_wp gts_wp)
     (clarsimp simp: reply_tcb_reply_at_def obj_at_def)

lemma reply_remove_reply_tcb_reply_at:
  "\<lbrace> \<lambda>s. P (P' None) \<and> (p \<noteq> r \<longrightarrow> P (reply_tcb_reply_at P' p s)) \<rbrace>
    reply_remove r
   \<lbrace> \<lambda>rv s. P (reply_tcb_reply_at P' p s) \<rbrace>"
  by (wpsimp simp: reply_remove_def
               wp: reply_unlink_tcb_reply_tcb_reply_at get_simple_ko_wp)

lemma get_ep_queue_wp:
  "\<lbrace> \<lambda>s. \<forall>q. ep \<in> {SendEP q, RecvEP q} \<longrightarrow> Q q s \<rbrace> get_ep_queue ep \<lbrace> Q \<rbrace>"
  by (wpsimp simp: get_ep_queue_def)

lemma get_blocking_object_wp:
  "\<lbrace> \<lambda>s. \<forall>ep. (\<exists>r. st = BlockedOnReceive ep r) \<or> (\<exists>d. st = BlockedOnSend ep d) \<longrightarrow> Q ep s \<rbrace>
    get_blocking_object st
   \<lbrace> Q \<rbrace>"
  by (cases st; wpsimp simp: get_blocking_object_def ep_blocked_def)

lemma reply_tcb_reply_at_kheap_update:
  "reply_tcb_reply_at P r (s\<lparr>kheap := kheap s(p \<mapsto> v)\<rparr>) =
    (if p = r then \<exists>r. v = Reply r \<and> P (reply_tcb r) else reply_tcb_reply_at P r s)"
  by (simp add: reply_tcb_reply_at_def obj_at_update)

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
                      reply_cancel_ipc_def reply_remove_tcb_def reply_remove_def
                  wp: get_simple_ko_wp set_simple_ko_wps gts_wp get_ep_queue_wp
                      get_blocking_object_wp reply_unlink_tcb_reply_tcb_reply_at thread_set_wp)
  apply (frule invs_valid_objs, drule invs_sym_refs)
  apply (intro conjI impI allI)
  (* 13 subgoals *)
  apply (all \<open>clarsimp simp: obj_at_update reply_tcb_reply_at_kheap_update pred_tcb_upd_apply
                       cong: conj_cong
                      split: if_splits\<close>)
  apply (all \<open>(intro conjI)?\<close>)
  (* 22 subgoals *)
  apply (all \<open>clarsimp simp: reply_tcb_reply_at_def obj_at_def get_tcb_def
                             is_ep_def is_ntfn_def
                      split: option.splits kernel_object.splits\<close>)
  (* 13 subgoals *)
  apply (all \<open>frule (3) reply_tcb_state_refs\<close>)
  apply (all \<open>clarsimp simp: pred_tcb_at_def obj_at_def
                      dest!: sym[where t="tcb_state t" for t]\<close>)
  (* 2 subgoals *)
   apply (rename_tac s tcb reply' t' r' reply tcb')
   apply (rule_tac V="t' = t" in revcut_rl)
    apply (frule_tac x=t and y=r' and tp=ReplyTCB in sym_refsE
           ; fastforce simp: state_refs_of_def)
   apply (frule_tac x=r and y=t and tp=TCBReply in sym_refsE
          ; fastforce simp: state_refs_of_def get_refs_def2)
  apply (rename_tac s tcb reply' sc' t' sc_obj' r' n' reply tcb')
  apply (rule_tac V="t' = t" in revcut_rl)
   apply (frule_tac x=t and y=r' and tp=ReplyTCB in sym_refsE
          ; fastforce simp: state_refs_of_def)
  by (frule_tac x=r and y=t and tp=TCBReply in sym_refsE
      ; fastforce simp: state_refs_of_def get_refs_def2)

lemma get_notification_default_sp:
  "\<lbrace> P \<rbrace>
    case ptr_opt of None \<Rightarrow> return default_notification | Some p \<Rightarrow> get_notification p
   \<lbrace> \<lambda>rv. P and (case_option (\<lambda>s. rv = default_notification) (ko_at (Notification rv)) ptr_opt) \<rbrace>"
  by (wpsimp wp: get_simple_ko_wp)

lemma sort_queue_ep_rv_wf''[wp]:
  "\<lbrace>P (ep_q_refs_of (RecvEP q))\<rbrace> sort_queue q \<lbrace>\<lambda>rv. P (ep_q_refs_of (RecvEP rv))\<rbrace>"
  "\<lbrace>P (ep_q_refs_of (SendEP q))\<rbrace> sort_queue q \<lbrace>\<lambda>rv. P (ep_q_refs_of (SendEP rv))\<rbrace>"
  "\<lbrace>Q (q = [])\<rbrace> sort_queue q \<lbrace>\<lambda>rv. Q (rv = [])\<rbrace>"
  by (simp add: ep_q_refs_of_def set_empty[symmetric] del: set_empty; rule sort_queue_rv_wf')+

definition receive_ipc_blocked ::
  "bool \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> obj_ref list \<Rightarrow> ('a::state_ext state, unit) nondet_monad"
  where
  "receive_ipc_blocked is_blocking t ep_ptr reply queue \<equiv>
    case is_blocking of True \<Rightarrow> do _ <- set_thread_state t (BlockedOnReceive ep_ptr reply);
                                   _ <- when (\<exists>r. reply = Some r) (set_reply_obj_ref reply_tcb_update (the reply) (Some t));
                                   q <- sort_queue (queue @ [t]);
                                   set_endpoint ep_ptr (RecvEP q)
                                od
                      | False \<Rightarrow> do_nbrecv_failed_transfer t"

definition receive_ipc_idle ::
  "bool \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> ('a::state_ext state, unit) nondet_monad"
  where
  "receive_ipc_idle is_blocking t ep_ptr reply \<equiv>
    case is_blocking of True \<Rightarrow> do _ <- set_thread_state t (BlockedOnReceive ep_ptr reply);
                                   _ <- when (\<exists>r. reply = Some r) (set_reply_obj_ref reply_tcb_update (the reply) (Some t));
                                   set_endpoint ep_ptr (RecvEP [t])
                                od
                      | False \<Rightarrow> do_nbrecv_failed_transfer t"

lemma monadic_rewrite_sort_queue_singleton:
  "monadic_rewrite False True (tcb_at t) (sort_queue [t]) (return [t])"
  proof -
    have rewrite_if:
      "\<And>e s n. (if \<exists>v. e = Some v then s else n) = (case e of None \<Rightarrow> n | Some v \<Rightarrow> s)"
        by fastforce
    show ?thesis
      by (simp add: monadic_rewrite_def sort_queue_def mapM_def sequence_def thread_get_def
                    gets_the_def bind_assoc gets_def get_def get_tcb_def assert_opt_def
                    state_assert_def assert_def rewrite_if return_def fail_def tcb_at_def bind_def
             split: option.splits)
  qed

lemma monadic_rewrite_receive_ipc_idle:
  "monadic_rewrite False True (tcb_at t) (receive_ipc_blocked is_blocking t ep_ptr reply [])
                                         (receive_ipc_idle is_blocking t ep_ptr reply)"
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
    (\<lambda>s. reply = ReplyCap reply_ptr \<and> reply_tcb_reply_at (\<lambda>t. t = None) reply_ptr s
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

lemma pred_tcb_at_ko_atD:
  "pred_tcb_at proj P p s \<Longrightarrow> \<exists>tcb. ko_at (TCB tcb) p s \<and> P (proj (tcb_to_itcb tcb))"
  by (simp add: pred_tcb_at_def2)

lemmas st_tcb_at_ko_atD =
  pred_tcb_at_ko_atD[where proj=itcb_state, simplified]

lemma set_difference_not_P:
  "S - {x \<in> S. P x} = {x \<in> S. \<not>P x}"
  by blast

lemma reply_tcb_reply_at_ReplyTCB_in_state_refs_of:
  "reply_tcb_reply_at P r_ptr s \<Longrightarrow> (t, ReplyTCB) \<in> state_refs_of s r_ptr \<Longrightarrow> P (Some t)"
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def state_refs_of_def get_refs_def
              split: option.splits)

lemma st_tcb_at_TCBReply_in_state_refs_of:
  "st_tcb_at P t s \<Longrightarrow> (r, TCBReply) \<in> state_refs_of s t \<Longrightarrow>
     P (BlockedOnReply (Some r)) \<or> (\<exists>ep. P (BlockedOnReceive ep (Some r)))"
  by (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2 tcb_st_refs_of_def
              split: thread_state.splits if_splits)

global_interpretation set_reply_tcb_obj_ref:
  non_reply_sc_op "set_reply_obj_ref reply_tcb_update ref new"
  by unfold_locales (wpsimp wp: update_sk_obj_ref_wp  simp: reply_sc_reply_at_def obj_at_def)

lemma set_reply_tcb_valid_replies[wp]:
  "set_reply_obj_ref reply_tcb_update x y \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma tcb_st_refs_of_replies_blocked_empty:
  "tcb_st_refs_of st = {} \<Longrightarrow> replies_blocked_of_tcb_st t st = {}"
  by (cases st; fastforce split: if_splits)

lemma receive_ipc_blocked_invs':
  assumes ep: "case ep of IdleEP \<Rightarrow> queue = [] | RecvEP q \<Rightarrow> queue = q | SendEP _ \<Rightarrow> False"
  shows "\<lbrace> receive_ipc_preconds t ep_ptr reply reply_opt ep invs \<rbrace>
          receive_ipc_blocked is_blocking t ep_ptr reply_opt queue
         \<lbrace> \<lambda>rv. invs \<rbrace>"
  proof -
    have ep_valid:
      "\<And>s. invs s \<Longrightarrow> st_tcb_at active t s \<Longrightarrow> ko_at (Endpoint ep) ep_ptr s
            \<Longrightarrow> (\<forall>t \<in> set queue. tcb_at t s) \<and> distinct queue \<and> t \<notin> set queue"
      using ep
      apply (cases ep; clarsimp)
      apply (frule invs_valid_objs, erule valid_objsE, simp add: obj_at_def)
      apply (clarsimp simp add: valid_obj_def valid_ep_def)
      by (fastforce dest!: ep_queued_st_tcb_at[where P="\<lambda>st. \<exists>e p r. st \<in> {BlockedOnSend e p, BlockedOnReceive e r}"]
                     simp: ep_q_refs_of_def invs_valid_objs invs_sym_refs pred_tcb_at_def obj_at_def)+
    have ep_queue:
      "ep_q_refs_of ep = set queue \<times> {EPRecv}"
      using ep by (cases ep; clarsimp simp: ep_q_refs_of_def)
    show ?thesis
      apply (cases reply_opt)
       apply (all \<open>wpsimp wp: valid_irq_node_typ sts_only_idle set_endpoint_invs hoare_vcg_ball_lift
                              sts_valid_replies_simple valid_ioports_lift
                        simp: receive_ipc_blocked_def valid_ep_def do_nbrecv_failed_transfer_def\<close>)
       apply (all \<open>clarsimp simp: ep_valid\<close>)
       apply (all \<open>clarsimp simp: invs_def valid_state_def valid_pspace_def st_tcb_at_tcb_at
                                  valid_tcb_state_def not_idle_thread
                                  ko_at_Endpoint_ep_at reply_tcb_reply_at\<close>)
       apply (all \<open>rule revcut_rl[where V="ep_ptr \<noteq> t"], fastforce simp: obj_at_def pred_tcb_at_def\<close>)
       apply (all \<open>(match premises in \<open>reply = ReplyCap r_ptr\<close> for r_ptr \<Rightarrow>
                     \<open>rule revcut_rl[where V="r_ptr \<notin> {t, ep_ptr}"]\<close>
                   , fastforce simp: obj_at_def reply_tcb_reply_at_def pred_tcb_at_def)?\<close>)
       apply (all \<open>frule obj_at_state_refs_ofD; clarsimp simp: ep_queue\<close>)
       apply (all \<open>drule active_st_tcb_at_state_refs_ofD; drule st_tcb_at_ko_atD\<close>)
       apply (all \<open>clarsimp simp: tcb_non_st_state_refs_of_state_refs_of set_difference_not_P
                            cong: if_cong\<close>)
       apply (all \<open>clarsimp simp: pred_tcb_at_def obj_at_def tcb_st_refs_of_replies_blocked_empty\<close>)
       apply (all \<open>erule delta_sym_refs; fastforce dest: reply_tcb_reply_at_ReplyTCB_in_state_refs_of
                                                  split: if_splits\<close>)
      done
  qed

lemma receive_ipc_idle_invs:
  "\<lbrace> receive_ipc_preconds t ep_ptr reply reply_opt IdleEP invs \<rbrace>
    receive_ipc_idle is_blocking t ep_ptr reply_opt
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

global_interpretation set_sched_context: non_reply_op "set_sched_context ptr sc"
  by unfold_locales (wpsimp simp: set_sched_context_def reply_at_ppred_def obj_at_def
                              wp: set_object_wp get_object_wp)

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

lemma make_fault_msg_ko_at_Endpoint[wp]:
  "make_fault_msg f sender \<lbrace>\<lambda>s. P (ko_at (Endpoint ep) p s)\<rbrace>"
  by (cases f;
      wpsimp simp: tcb_agnostic_pred_def sched_context_update_consumed_def set_sched_context_def
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
   send_ipc True call bdg x can_donate t' epptr
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
    apply (intro conjI, wpsimp+)
   apply (intro conjI, wpsimp+)
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
  apply (wpsimp simp: thread_set_def set_object_def wp: si_blk_makes_simple)
  apply (auto simp: st_tcb_at_def obj_at_def)
  done

lemma hf_makes_simple:
  notes hoare_pre [wp_pre del]
  shows
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t')\<rbrace> handle_fault t ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  apply (simp add: handle_fault_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb])
  apply (wpsimp simp: unless_def handle_no_fault_def send_fault_ipc_def wp: sts_st_tcb_at_cases)
  apply (case_tac "tcb_fault_handler tcb"; simp)
   apply (rule hoare_pre)
    apply wpsimp
   apply clarsimp
  apply (wpsimp wp: si_blk_makes_simple)
  apply (rule hoare_pre)
   apply (wpsimp simp: wp: thread_set_no_change_tcb_state)
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

lemma "(if P then False else Q) \<longleftrightarrow> (\<not>P \<and> Q)"
  by simp

lemma unbind_reply_in_ts_trivial_inv:
  "\<lbrace> P and st_tcb_at (\<lambda>st. \<forall>r ep. st \<notin> {BlockedOnReceive ep r, BlockedOnReply r}) t \<rbrace>
    unbind_reply_in_ts t
   \<lbrace> \<lambda>rv. P \<rbrace>"
  apply (simp add: unbind_reply_in_ts_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule_tac S="\<forall>r ep. st \<notin> {BlockedOnReceive ep r, BlockedOnReply r}" in hoare_gen_asm''
         , clarsimp simp: pred_tcb_at_def obj_at_def)
  by (case_tac st; simp; wpsimp)

lemma unbind_reply_in_ts_inv:
  "\<lbrace>P and st_tcb_at ((=) Inactive) t\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wp unbind_reply_in_ts_trivial_inv) (fastforce elim!: st_tcb_weakenE)

lemma unbind_reply_in_ts_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: unbind_reply_in_ts_def get_thread_state_def thread_get_def)
  apply (fastforce simp: valid_obj_def valid_tcb_def valid_tcb_state_def dest!: get_tcb_SomeD)
  done

lemma unbind_reply_in_ts_tcb_at:
  "\<lbrace>tcb_at t'\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def get_thread_state_def thread_get_def)

lemmas tcb_agnostic_predE' = tcb_agnostic_predE[of "\<lambda>b. b" P for P, rotated]

global_interpretation unbind_reply_in_ts: tcb_op "unbind_reply_in_ts t"
  apply unfold_locales
  apply (wpsimp simp: unbind_reply_in_ts_def get_thread_state_def thread_get_def
                                  set_thread_state_def
                              wp: set_object_wp)
  by (rule_tac f=P in bool_to_bool_cases
      ; intro conjI
      ; clarsimp simp: get_tcb_ko_at obj_at_def tcb_agnostic_predE')

lemma set_reply_tcb_valid_tcb_state:
  "\<lbrace>reply_at reply_ptr'\<rbrace>
   set_reply_obj_ref reply_tcb_update reply_ptr t
   \<lbrace>\<lambda>rv. valid_tcb_state (BlockedOnReply (Some reply_ptr'))\<rbrace>"
  unfolding valid_tcb_state_def by wpsimp

global_interpretation set_reply_tcb:
  non_sc_op "set_reply_obj_ref f reply_ptr t"
  by unfold_locales (wpsimp wp: update_sk_obj_ref_wps simp: sc_at_pred_n_def obj_at_def)

lemma set_sc_replies_bound_sc[wp]:
  "set_sc_obj_ref sc_replies_update sc replies \<lbrace> bound_sc_tcb_at P t \<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def)

lemma reply_unlink_tcb_sym_refs_BlockedOnReceive:
  "\<lbrace>\<lambda>s. (\<exists>tptr epptr. st_tcb_at ((=) (BlockedOnReceive epptr (Some rptr))) tptr s \<and>
                      sym_refs (\<lambda>x. if x = tptr then
                                      {r \<in> state_refs_of s x. snd r = TCBBound \<or>
                                       snd r = TCBSchedContext \<or> snd r = TCBYieldTo
                                       \<or> snd r = TCBReply}
                                    else state_refs_of s x))\<rbrace>
   reply_unlink_tcb rptr \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def get_thread_state_def thread_get_def get_simple_ko_def
                      get_object_def)
  apply safe
     apply (clarsimp simp: st_tcb_at_def obj_at_def get_tcb_def)
    apply (clarsimp simp: st_tcb_at_def obj_at_def get_tcb_def)
   apply (clarsimp simp: st_tcb_at_def obj_at_def)
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = tptr in allE)
   apply (fastforce simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def get_tcb_def
                   split: if_splits thread_state.splits
                   dest!: bspec)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp simp: st_tcb_at_def obj_at_def split: if_splits)
    apply (clarsimp simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def sym_refs_def
                   split: thread_state.splits)
    apply (erule_tac x = tptr in allE)
    apply (fastforce simp: get_refs_def2 state_refs_of_def)
   apply (clarsimp simp: state_refs_of_def)
  apply (clarsimp split: if_splits)
     apply (clarsimp simp: get_refs_def2 st_tcb_at_def obj_at_def state_refs_of_def
                           tcb_st_refs_of_def
                    split: thread_state.splits)
    apply (clarsimp simp: st_tcb_at_def obj_at_def)
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = tptr in allE)
   apply (fastforce simp: st_tcb_at_def obj_at_def state_refs_of_def
                          get_refs_def2 tcb_st_refs_of_def
                   split: if_splits thread_state.splits
                   dest!: bspec)
  apply (clarsimp simp: state_refs_of_def)
  done

lemma reply_unlink_tcb_invs_BlockedOnReceive:
  "\<lbrace>\<lambda>s. (\<exists>tptr epptr. st_tcb_at ((=) (BlockedOnReceive epptr (Some rptr))) tptr s \<and>
                      sym_refs (\<lambda>x. if x = tptr then
                                      {r \<in> state_refs_of s x. snd r = TCBBound \<or>
                                       snd r = TCBSchedContext \<or> snd r = TCBYieldTo
                                       \<or> snd r = TCBReply}
                                    else state_refs_of s x)) \<and>
                      valid_replies s \<and> all_invs_but_sym_refs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   reply_unlink_tcb rptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: reply_unlink_tcb_sym_refs_BlockedOnReceive
                      reply_unlink_tcb_valid_replies_simple
                      valid_ioports_lift)
  apply (clarsimp simp: pred_tcb_at_eq_commute)
  apply (subgoal_tac "rptr \<noteq> tptr")
   apply (rule revcut_rl, erule_tac x=tptr and y=rptr and tp=ReplyTCB in sym_refsE)
    by (auto simp: reply_tcb_reply_at_def pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2)

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
  and reply_tcb_reply_at[wp]: "\<lambda>s. P (reply_tcb_reply_at P' r s)"
  and reply_sc_reply_at[wp]: "\<lambda>s. P (reply_sc_reply_at P' r s)"
  (simp: reply_sc_reply_at_def)

lemma store_word_offs_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: store_word_offs_def do_machine_op_def reply_tcb_reply_at_def)

lemma store_word_offs_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: store_word_offs_def do_machine_op_def reply_sc_reply_at_def)

lemma transfer_caps_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace>
   transfer_caps info caps endpoint receiver recv_buffer
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: transfer_caps_def)

lemma copy_mrs_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> copy_mrs sender sbuf receiver rbuf n \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
    apply (intro conjI)
     apply (wpsimp wp: mapM_wp | fastforce)+
  done

lemma do_normal_transfer_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace>
   do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: do_normal_transfer_def
               wp: transfer_caps_bound_sc copy_mrs_bound_sc)

lemma do_fault_transfer_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> do_fault_transfer badge sender receiver buf \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  apply (wpsimp simp: do_fault_transfer_def)
     apply (case_tac f)
         apply (intro conjI | wpsimp)+
   apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: get_tcb_def)
  done

lemma do_ipc_transfer_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> do_ipc_transfer sender ep badge grant receiver \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def
               wp: do_normal_transfer_bound_sc do_fault_transfer_bound_sc)

lemma set_reply_tcb_rv[wp]:
  "\<lbrace> \<lambda>s. P t \<rbrace> set_reply_obj_ref reply_tcb_update r t \<lbrace> \<lambda>rv s. reply_tcb_reply_at P r s \<rbrace>"
  by (wpsimp wp: update_sk_obj_ref_wp simp: sk_obj_at_pred_def obj_at_def)+

crunches unbind_reply_in_ts
  for bound_sc_tcb_at[wp]: "bound_sc_tcb_at P t"
  and pspace_aligned[wp]: "pspace_aligned"
  and pspace_distinct[wp]: "pspace_distinct"
  and zombies_final[wp]: "zombies_final"
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_mdb[wp]: "valid_mdb"
  and valid_ioc[wp]: "valid_ioc"
  and if_unsafe_then_cap[wp]: "if_unsafe_then_cap"
  and valid_global_refs[wp]: "valid_global_refs"
  and valid_arch_state[wp]: "valid_arch_state"
  and valid_irq_node[wp]: "valid_irq_node"
  and valid_irq_handlers[wp]: "valid_irq_handlers"
  and valid_irq_states[wp]: "valid_irq_states"
  and valid_vspace_objs[wp]: "valid_vspace_objs"
  and valid_machine_state[wp]: "valid_machine_state"
  and valid_arch_caps[wp]: "valid_arch_caps"
  and valid_global_objs[wp]: "valid_global_objs"
  and valid_kernel_mappings[wp]: "valid_kernel_mappings"
  and equal_kernel_mappings[wp]: "equal_kernel_mappings"
  and valid_asid_map[wp]: "valid_asid_map"
  and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
  and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
  and pspace_respects_device_region[wp]: "pspace_respects_device_region"
  and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  and cur_tcb[wp]: "cur_tcb"

lemma unbind_reply_in_ts_st_tcb_at_active[wp]:
  "unbind_reply_in_ts t \<lbrace> st_tcb_at active t' \<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def wp: sts_st_tcb_at_cases gts_wp)
     (fastforce simp add: pred_tcb_at_def obj_at_def)

lemma unbind_reply_in_ts_if_live_then_nonz_cap[wp]:
  "unbind_reply_in_ts t \<lbrace> if_live_then_nonz_cap \<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def wp: gts_wp)
     (auto elim: st_tcb_ex_cap)

lemma unbind_reply_in_ts_state_refs_of[wp]:
  "\<lbrace> \<lambda>s. P ((state_refs_of s)(t := {ref \<in> state_refs_of s t. snd ref \<noteq> TCBReply})) \<rbrace>
    unbind_reply_in_ts t
   \<lbrace> \<lambda>r s. P (state_refs_of s) \<rbrace>"
  apply (wpsimp simp: unbind_reply_in_ts_def fun_upd_def wp: gts_wp)
  apply (case_tac st; clarsimp)
  (* 8 subgoals *)
  apply (all \<open>erule rsubst[of P]\<close>)
  apply (all \<open>rule ext; rule set_eqI; rule iffI\<close>)
  (* 16 subgoals *)
  apply (all \<open>drule pred_tcb_at_eq_state_refs_ofD\<close>)
  apply (all \<open>clarsimp simp: get_refs_def2 split: if_splits\<close>)
  (* 2 subgoals *)
  by blast+

lemma unbind_reply_in_ts_valid_idle[wp]:
  "unbind_reply_in_ts t \<lbrace> valid_idle \<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def wp: gts_wp)
     (fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def)

lemma unbind_reply_in_ts_only_idle[wp]:
  "unbind_reply_in_ts t \<lbrace> only_idle \<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def wp: gts_wp sts_only_idle)

lemma sc_at_pred_n_sc_at:
  "valid_objs s \<Longrightarrow> sc_at_pred_n N proj P sc s \<Longrightarrow> sc_at sc s"
  by (fastforce simp: sc_at_pred_n_def obj_at_def is_sc_obj_def
                elim: valid_objs_valid_sched_context_size)

lemma sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at:
  assumes pre: "\<And>sc_opt. P sc_opt \<longleftrightarrow> sc_opt = Some sc"
               "\<And>t_opt. Q t_opt \<longleftrightarrow> t_opt = Some t"
  assumes sym: "sym_refs (state_refs_of s)"
  shows "bound_sc_tcb_at P t s \<longleftrightarrow> sc_tcb_sc_at Q sc s"
  using sym by (fastforce simp: pred_tcb_at_def sc_tcb_sc_at_def obj_at_def pre
                                sym_refs_def state_refs_of_def get_refs_def2 refs_of_rev
                         split: option.splits)

lemma sc_at_pred_nE:
  assumes "sc_at_pred_n N proj P ref s"
  assumes "\<And>sc n. kheap s ref = Some (SchedContext sc n) \<Longrightarrow> P (proj sc) \<Longrightarrow> N n \<Longrightarrow> R"
  shows R
  using assms by (auto simp: sc_at_pred_n_def obj_at_def)

lemmas sc_replies_sc_atE =
  sc_at_pred_nE[where N=\<top> and proj=sc_replies, simplified]

lemma sc_replies_sc_at_state_refs_of:
  assumes equiv: "\<And>rs. P rs \<longleftrightarrow> rs = replies"
  assumes sc_at: "sc_replies_sc_at P sc s"
  shows "r \<in> set replies \<longleftrightarrow> (r, SCReply) \<in> state_refs_of s sc"
  using sc_at by (auto simp: equiv sc_replies_sc_at_def obj_at_def state_refs_of_def get_refs_def2)

lemma reply_sc_reply_at_ReplySchedContext_in_state_refs_of:
  "reply_sc_reply_at P r_ptr s \<Longrightarrow> (sc, ReplySchedContext) \<in> state_refs_of s r_ptr \<Longrightarrow> P (Some sc)"
  by (clarsimp simp: reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def
              split: option.splits)

lemma receive_ipc_preamble_rv:
  "\<lbrace>st_tcb_at active t and invs\<rbrace> receive_ipc_preamble reply t \<lbrace>receive_ipc_preamble_rv reply\<rbrace>"
  unfolding receive_ipc_preamble_def
  apply (cases reply; clarsimp intro!: hoare_weaken_pre[OF return_wp])
  apply (thin_tac _, rename_tac reply_ptr)
  apply (rule hoare_seq_ext[OF _ get_sk_obj_ref_sp]; simp)
  apply (rename_tac t_opt)
  apply (case_tac t_opt; clarsimp intro!: hoare_weaken_pre[OF return_wp]
                                    simp: reply_tcb_reply_at_None_imp_reply_sc_reply_at_None')
  apply (rename_tac t_ptr)
  apply (rule hoare_seq_ext[OF return_wp], simp)
  apply (rule hoare_when_cases, clarsimp)
   apply (drule_tac x=reply_ptr and y=t and tp=TCBReply in sym_refsE[OF invs_sym_refs]
          ; fastforce simp: reply_at_ppred_def pred_tcb_at_def obj_at_def state_refs_of_def refs_of_rev
                     split: option.splits)
  apply (strengthen reply_tcb_reply_at_None_imp_reply_sc_reply_at_None')
  apply (wpsimp wp: cancel_ipc_reply_at_tcb_in[where tcbs="{}", simplified])
  by (clarsimp simp: reply_tcb_reply_at_def obj_at_def)

lemma do_ipc_transfer_valid_replies[wp]:
  "do_ipc_transfer sender ep badge grant receiver \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_state_refs_lift)

lemma set_reply_sc_valid_replies_already_BlockedOnReply:
  "\<lbrace> \<lambda>s. valid_replies s \<and> r \<in> fst ` replies_blocked s \<rbrace>
    set_reply_obj_ref reply_sc_update r (Some sc)
   \<lbrace> \<lambda>rv. valid_replies \<rbrace>"
  by (wpsimp wp: set_reply_sc_valid_replies) fastforce

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
                               receive_ipc_blocked_def[symmetric] receive_ipc_idle_def[symmetric])
  apply (rename_tac ep_ptr ep_badge ep_rights)
  apply (rule hoare_seq_ext[where B="\<lambda>rv. invs and ?pre and receive_ipc_preamble_rv reply rv", rotated]; simp)
   apply (wpsimp wp: receive_ipc_preamble_invs receive_ipc_preamble_caps_of_state
                     receive_ipc_preamble_st_tcb_at receive_ipc_preamble_rv
               simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state)
  apply (rename_tac reply_opt)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp[simplified pred_conj_comm]])
  apply (rule hoare_seq_ext[OF _ gbn_sp[simplified pred_conj_comm]])
  apply (rule hoare_seq_ext[OF _ get_notification_default_sp])
  apply (rule hoare_weaken_pre)
   apply (rule_tac R="receive_ipc_preconds thread ep_ptr reply reply_opt ep invs" in hoare_vcg_if_split)
    apply (wp complete_signal_invs)
   prefer 2 apply (clarsimp simp: st_tcb_at_tcb_at)
  apply (thin_tac "\<not> (_ \<and> _)", clarsimp)
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
    apply (erule sym_refs_insert_delete'[where t=EPSend]; simp add: st_tcb_at_tcb_non_st_state_refs_of)
   apply (clarsimp simp: sym_refs_def)
   apply (drule_tac x=ep_ptr in spec; clarsimp simp: mk_ep_def split: if_splits;
          erule (1) TCBBlockedSend_in_state_refs_of_unique)
  (* thread_get tcb_fault *)
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  (* if not call and no fault: sender \<rightarrow> Running *)
  apply (rule hoare_if[rotated]
         , wpsimp wp: set_thread_state_invs cong: if_cong
         , fastforce elim: st_tcb_weakenE)
  (* if not grant or no reply: sender \<longrightarrow> Inactive *)
  apply (rule hoare_if[rotated]
         , wpsimp wp: set_thread_state_invs cong: if_cong
         , fastforce elim: st_tcb_weakenE)
  (* otherwise (grant and reply and (call or fault)): reply_push *)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (clarsimp simp: reply_push_def, rename_tac reply_ptr)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ liftM_wp[where P=P and Q="\<lambda>r. P" for P, simplified,
                                          OF get_simple_ko_inv]])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule_tac S="sender_sc = sc_caller \<and> sender \<noteq> thread \<and> sender \<noteq> reply_ptr \<and> thread \<noteq> reply_ptr"
           in hoare_gen_asm'', fastforce simp: sk_obj_at_pred_def pred_tcb_at_def obj_at_def)
  apply (thin_tac "ep_cap = _")
  apply (thin_tac "sender_is_call _ \<or> _")
  apply (thin_tac "sender_can_grant _")
  apply (rule subst[of "do _ <- do _ <- a; _ <- b; c od; d od"
                       "do _ <- a; _ <- b; _ <- c; d od"
                       "\<lambda>c. \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
                    for a b c d P Q]
         , simp add: bind_assoc)
  apply (rule_tac B="\<lambda>_ s. st_tcb_at ((=) (BlockedOnReply (Some reply_ptr))) sender s
                           \<and> bound_sc_tcb_at ((=) sc_callee) thread s
                           \<and> reply_tcb_reply_at (\<lambda>t. t = Some sender) reply_ptr s
                           \<and> reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr s
                           \<and> bound_sc_tcb_at ((=) sc_caller) sender s
                           \<and> st_tcb_at active thread s
                           \<and> ex_nonz_cap_to thread s
                           \<and> ex_nonz_cap_to reply_ptr s
                           \<and> ex_nonz_cap_to sender s
                           \<and> sender \<noteq> idle_thread s
                           \<and> st_tcb_at ((=) (BlockedOnReply (Some reply_ptr))) sender s
                           \<and> invs s"
           in hoare_seq_ext[rotated])
   apply (wpsimp wp: sts_st_tcb_at_cases set_thread_state_bound_sc_tcb_at sts_only_idle
                     sts_valid_replies_simple' unbind_reply_in_ts_trivial_inv valid_ioports_lift
               simp: invs_def valid_state_def valid_pspace_def valid_tcb_state_def
                     st_tcb_at_tcb_at reply_tcb_reply_at
               cong: if_cong)
   apply (apply_conjunct \<open>match conclusion in \<open>st_tcb_at P p s\<close> for P p s
            \<Rightarrow> \<open>fastforce elim!: st_tcb_weakenE simp: \<close>\<close>)+
   apply (erule delta_sym_refs; clarsimp split: if_splits
          ; fastforce dest: reply_tcb_reply_at_ReplyTCB_in_state_refs_of
                            st_tcb_at_TCBReply_in_state_refs_of)
  apply (rule hoare_when_cases; clarsimp split: if_splits)
  apply (rename_tac sc_caller)
  apply (rule hoare_seq_ext[OF _ gbn_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[simplified]])
  apply (rule hoare_seq_ext[where A=P and B="\<lambda>_. P" for P, rotated]
         , wpsimp wp: assert_inv get_simple_ko_inv, fastforce)
  apply (wpsimp wp: sched_context_donate_invs set_reply_sc_valid_replies_already_BlockedOnReply
                    valid_ioports_lift
              simp: invs_def valid_state_def valid_pspace_def
                    st_tcb_at_tcb_at reply_tcb_reply_at sc_at_pred_n_sc_at)
  apply (frule (1) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF eq_commute refl, THEN iffD1])
  apply (rule_tac V="ex_nonz_cap_to sc_caller s \<and> sc_caller \<notin> {reply_ptr, thread, sender}" in revcut_rl
         , fastforce simp: sc_at_pred_n_def pred_tcb_at_def sk_obj_at_pred_def obj_at_def
                           live_def live_sc_def
                     elim: if_live_then_nonz_capD2)
  apply (rule sc_replies_sc_atE
         , assumption
         , erule (1) pspace_valid_objsE
         , clarsimp simp: valid_obj_def valid_sched_context_def list_all_iff in_replies_blockedI)
  apply (apply_conjunct \<open>match conclusion in \<open>reply_ptr \<notin> set (sc_replies sc)\<close> for reply_ptr sc
           \<Rightarrow> \<open>fastforce dest: sc_replies_sc_at_state_refs_of[OF eq_commute, THEN iffD1, THEN sym_refsD]
                               reply_sc_reply_at_ReplySchedContext_in_state_refs_of\<close>\<close>)
  by (erule delta_sym_refs; fastforce simp: image_iff sc_tcb_sc_at_def obj_at_def is_reply
                                            sc_replies_sc_at_state_refs_of[OF eq_commute]
                                      dest: reply_sc_reply_at_ReplySchedContext_in_state_refs_of
                                     split: if_splits)

lemma sched_context_donate_sym_refs_BlockedOnReceive:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
        sym_refs (\<lambda>a. if a = dest
                      then {r \<in> state_refs_of s dest. snd r = TCBBound \<or> snd r = TCBSchedContext
                            \<or> snd r = TCBYieldTo}
                      else state_refs_of s a) \<and>
        sc_tcb_sc_at (\<lambda>t. \<exists>caller. t = Some caller \<and> st_tcb_at active caller s) scptr s \<and>
        st_tcb_at (\<lambda>st. \<exists>epptr. st = BlockedOnReceive epptr None) dest s \<and>
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
  unfolding reply_push_def update_sk_obj_ref_def set_sc_obj_ref_def comp_def
  by (wpsimp wp: get_simple_ko_wp get_tcb_obj_ref_wp hoare_vcg_if_lift hoare_vcg_all_lift
                 sts_st_tcb_at_cases unbind_reply_in_ts_inv
     | wp_once hoare_drop_imp)+

lemma reply_push_invs_helper:
  "\<lbrace> \<lambda>s. invs s
         \<and> reply_at reply_ptr s
         \<and> sc_at sc_ptr s
         \<and> ex_nonz_cap_to reply_ptr s
         \<and> ex_nonz_cap_to callee s
         \<and> ex_nonz_cap_to sc_ptr s
         \<and> reply_sc_reply_at (\<lambda>sc_ptr'. sc_ptr' = None) reply_ptr s
         \<and> reply_ptr \<in> fst ` replies_blocked s \<rbrace>
    when donate (do
      sc_callee <- get_tcb_obj_ref tcb_sched_context callee;
      y <- assert (sc_callee = None);
      sc_replies <- liftM sc_replies (get_sched_context sc_ptr);
      y <- case sc_replies of [] \<Rightarrow> assert True
              | r # x \<Rightarrow> do reply <- get_reply r;
                            assert (reply_sc reply = sc_caller)
                         od;
      y <- set_sc_obj_ref sc_replies_update sc_ptr (reply_ptr # sc_replies);
      y <- set_reply_obj_ref reply_sc_update reply_ptr (Some sc_ptr);
      sched_context_donate sc_ptr callee
    od)
   \<lbrace> \<lambda>rv. invs \<rbrace>"
  supply if_weak_cong[cong del] if_split[split del]
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
  apply (rename_tac sc_replies')
  apply (case_tac sc_replies'; simp)
   apply (wpsimp wp: sched_context_donate_invs)
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: valid_irq_node_typ set_reply_sc_valid_replies_already_BlockedOnReply
                         valid_ioports_lift)
    apply (wpsimp wp: set_sc_replies_bound_sc)
   apply clarsimp
   apply (fastforce simp: invs_def valid_state_def valid_pspace_def
                          reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                          sc_replies_sc_at_def pred_tcb_at_def is_tcb is_reply is_sc_obj_def
                   split: if_splits
                   elim!: delta_sym_refs)
  apply (wpsimp wp: sched_context_donate_invs)
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                     wp: valid_irq_node_typ set_reply_sc_valid_replies_already_BlockedOnReply
                         valid_ioports_lift)
    apply (wpsimp wp: set_sc_replies_bound_sc)
   apply (wpsimp simp: get_simple_ko_def get_object_def)
  apply (clarsimp split: if_splits, intro conjI)
   apply (clarsimp simp: is_reply obj_at_def is_sc_obj_def)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def sc_replies_sc_at_def
                        valid_obj_def valid_sched_context_def
                 elim!: obj_at_valid_objsE)
  apply (case_tac "sc_replies sc"; simp)
  apply (rename_tac hd_rptr tail_rptrs)
  apply (subgoal_tac "reply_ptr \<noteq> hd_rptr \<and> reply_ptr \<notin> set tail_rptrs")
   apply (fastforce simp: reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                          pred_tcb_at_def is_tcb
                   split: if_splits
                   elim!: delta_sym_refs)
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = sc_ptr in allE, erule_tac x = "(reply_ptr, SCReply)" in ballE)
   apply (clarsimp simp: reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2)
  apply (clarsimp simp: state_refs_of_def)
  done

lemma sts_in_replies_blocked:
  "\<lbrace>\<top>\<rbrace> set_thread_state t (BlockedOnReply (Some r)) \<lbrace>\<lambda>rv s. r \<in> fst ` replies_blocked s\<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_strengthen_post)
    apply (rule sts_st_tcb_at'[where P="\<lambda>st. st = BlockedOnReply (Some r)"])
   apply (erule in_replies_blockedI)
  by simp

lemma reply_push_invs:
  "\<lbrace>invs and ex_nonz_cap_to callee and ex_nonz_cap_to caller and ex_nonz_cap_to reply_ptr and
    st_tcb_at active caller and st_tcb_at ((=) Inactive) callee and
    reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ set_reply_tcb_valid_tcb_state
                       unbind_reply_in_ts_inv sts_valid_replies_simple'
                       valid_ioports_lift
            split_del: if_split)
    apply (wpsimp wp: hoare_drop_imp)
   apply clarsimp
   apply (intro conjI)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (intro conjI)
       apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
      apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
     apply (fastforce elim!: st_tcb_weakenE)
    apply (rule delta_sym_refs, assumption)
     apply (clarsimp split: if_splits)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                          tcb_st_refs_of_def reply_tcb_reply_at_def
                   split: if_splits thread_state.splits)
   apply (clarsimp simp: idle_no_ex_cap)
  apply (intro conjI)
   apply (wpsimp wp: reply_push_invs_helper)
        apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                        wp: sts_only_idle valid_irq_node_typ sts_valid_replies_simple'
                            sts_in_replies_blocked valid_ioports_lift)
       apply (wpsimp wp: set_reply_tcb_valid_tcb_state valid_irq_node_typ valid_ioports_lift)
      apply (wpsimp wp: unbind_reply_in_ts_inv)
     apply wpsimp
    apply (wpsimp wp: hoare_drop_imp)
   apply clarsimp
   apply (intro conjI)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (intro conjI)
          apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
         apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
        apply (fastforce elim!: st_tcb_weakenE)
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
   apply (clarsimp simp: pred_tcb_at_def valid_obj_def valid_tcb_def
                  elim!: obj_at_valid_objsE)
   apply (rename_tac tcb')
   apply (case_tac "tcb_sched_context tcb'"; simp)
   apply (clarsimp simp: is_sc_obj_def obj_at_def)
   apply (case_tac ko; simp)
   apply (erule (1) if_live_then_nonz_capD2)
   apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply (clarsimp simp: live_def live_sc_def)
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ no_reply_in_ts_inv])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: sts_only_idle valid_irq_node_typ set_reply_tcb_valid_tcb_state
                      unbind_reply_in_ts_inv sts_valid_replies_simple'
                      valid_ioports_lift
           split_del: if_split)
  apply (intro conjI)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
     apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
    apply (fastforce elim!: st_tcb_weakenE)
   apply (rule delta_sym_refs, assumption)
    apply (clarsimp simp: st_tcb_at_def obj_at_def reply_tcb_reply_at_def split: if_splits)
   apply (clarsimp split: if_splits)
     apply (clarsimp simp: st_tcb_at_def obj_at_def reply_tcb_reply_at_def)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                          tcb_st_refs_of_def
                   split: thread_state.splits)
   apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def state_refs_of_def get_refs_def2)
  apply (clarsimp simp: idle_no_ex_cap)
  done

lemmas reply_push_ex_nonz_cap_to = reply_push_cap_to

lemma reply_push_valid_objs_helper:
  "\<lbrace>\<lambda>s. valid_objs s \<and> reply_at reply_ptr s \<and> sc_at sc_ptr s \<and>
    reply_sc_reply_at (\<lambda>sc_ptr'. sc_ptr' = None) reply_ptr s \<and>
    sym_refs (state_refs_of s)\<rbrace>
   when donate (do
     sc_callee <- get_tcb_obj_ref tcb_sched_context callee;
     y <- assert (sc_callee = None);
     sc_replies <- liftM sc_replies (get_sched_context sc_ptr);
     y <- case sc_replies of [] \<Rightarrow> assert True
             | r # x \<Rightarrow> do reply <- get_reply r;
                           assert (reply_sc reply = sc_caller)
                        od;
     y <- set_sc_obj_ref sc_replies_update sc_ptr (reply_ptr # sc_replies);
     y <- set_reply_obj_ref reply_sc_update reply_ptr (Some sc_ptr);
     sched_context_donate sc_ptr callee
   od)
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: when_def)
  apply (intro conjI)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_sp])
   apply (rule hoare_seq_ext[OF _ assert_sp])
   apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
   apply (rename_tac sc_replies')
   apply (case_tac sc_replies'; simp)
    apply wpsimp
    apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
   apply (wpsimp wp: hoare_drop_imp)
   apply (clarsimp simp: sc_replies_sc_at_def valid_obj_def valid_sched_context_def sym_refs_def
                  elim!: obj_at_valid_objsE)
   apply (erule_tac x = sc_ptr in allE)
   apply (erule_tac x = "(reply_ptr, SCReply)" in ballE)
    apply (clarsimp simp: obj_at_def get_refs_def2 reply_sc_reply_at_def state_refs_of_def)
   apply (case_tac "sc_replies sc"; simp)
   apply (clarsimp simp: state_refs_of_def pred_tcb_at_def obj_at_def is_tcb)
  apply wpsimp
  done

lemma reply_push_valid_objs:
  "\<lbrace>\<lambda>s. valid_objs s \<and> st_tcb_at ((=) Inactive) callee s \<and> tcb_at caller s \<and>
        reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr s \<and> sym_refs (state_refs_of s) \<and>
        st_tcb_at active caller s\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_reply_tcb_valid_tcb_state unbind_reply_in_ts_valid_objs
                     unbind_reply_in_ts_tcb_at)
    apply (wpsimp wp: hoare_drop_imp)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb reply_tcb_reply_at_def is_reply)
  apply (intro conjI)
   apply (wpsimp wp: reply_push_valid_objs_helper)
       apply (wpsimp wp: set_reply_tcb_valid_tcb_state)
      apply (wpsimp wp: unbind_reply_in_ts_inv)
     apply wpsimp
    apply (wpsimp wp: hoare_drop_imp)
   apply (clarsimp, intro conjI)
    apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply is_tcb)
   apply (clarsimp, intro conjI)
     apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
    apply (fastforce simp: pred_tcb_at_def valid_obj_def valid_tcb_def valid_bound_obj_def
                           is_sc_obj_def obj_at_def
                    split: option.splits
                    elim!: obj_at_valid_objsE)
   apply (fastforce simp: obj_at_def state_refs_of_def get_refs_def2 tcb_st_refs_of_def
                          st_tcb_at_def reply_tcb_reply_at_def
                   split: thread_state.splits if_splits
                   elim!: delta_sym_refs)
  apply (wpsimp wp: set_reply_tcb_valid_tcb_state unbind_reply_in_ts_valid_objs
                    unbind_reply_in_ts_tcb_at hoare_drop_imp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb reply_tcb_reply_at_def is_reply)
  done

lemma si_invs'_helper_no_reply:
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> reply_unlink_tcb a \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. st_tcb_at active tptr s \<and>
        st_tcb_at (\<lambda>st. \<exists>epptr. st = BlockedOnReceive epptr None) dest s \<and>
        all_invs_but_sym_refs s \<and>
        valid_replies s \<and>
        sym_refs (\<lambda>x. if x = dest
                      then {r \<in> state_refs_of s dest. snd r = TCBBound \<or>
                            snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                      else state_refs_of s x) \<and>
        sym_refs (state_hyp_refs_of s) \<and> bound_sc_tcb_at bound tptr s \<and> Q s\<rbrace>
   do
     sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     fault <- thread_get tcb_fault tptr;
     y <- if call \<or> (\<exists>y. fault = Some y)
          then return ()
          else when (can_donate \<and> sc_opt = None)
                 (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                     sched_context_donate (the caller_sc_opt) dest
                  od);
     new_sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     test \<leftarrow> case new_sc_opt of None \<Rightarrow> return True
              | Some scp \<Rightarrow> do sufficient <- refill_sufficient scp 0;
                               ready <- refill_ready scp;
                               return (sufficient \<and> ready)
              od;
     y <- assert test;
     y <- set_thread_state dest Running;
     possible_switch_to dest
  od
  \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac "call \<or> (\<exists>y. fault = Some y)"; simp)
   apply (rule hoare_seq_ext[OF _ gbn_inv])
   apply wpsimp
      apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ sts_valid_replies_simple
                       valid_ioports_lift)
     apply (wpsimp wp: assert_inv)+
   apply (apply_conjunct \<open>erule st_tcb_weakenE, fastforce\<close>)
   apply (subgoal_tac "ex_nonz_cap_to dest s")
    apply (clarsimp simp: idle_no_ex_cap)
   apply (fastforce simp: st_tcb_at_def live_def elim!: if_live_then_nonz_capD)

  apply (simp add: when_def bind_assoc)
  apply (intro conjI)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ sts_valid_replies_simple
                       sched_context_donate_sym_refs_BlockedOnReceive
                       valid_ioports_lift hoare_drop_imps)
    apply (wpsimp simp: get_tcb_obj_ref_def thread_get_def)
   apply (clarsimp, intro conjI)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (fastforce simp: live_def elim!: if_live_then_nonz_capD2)
   apply clarsimp
   apply (rename_tac tcb)
   apply (clarsimp cong: conj_cong)
   apply (subgoal_tac "sc_tcb_sc_at (\<lambda>t. t = Some tptr) (the (tcb_sched_context tcb)) s \<and>
                       ex_nonz_cap_to dest s")
    apply (clarsimp, intro conjI)
         apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def sc_tcb_sc_at_def)
         apply (fastforce simp: live_def live_sc_def elim!: if_live_then_nonz_capD2)
        apply (fastforce elim: st_tcb_weakenE)
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
   apply (fastforce simp: st_tcb_at_def live_def elim!: if_live_then_nonz_capD)
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: valid_irq_node_typ sts_only_idle sts_valid_replies_simple
                      valid_ioports_lift hoare_drop_imps)
  apply (apply_conjunct \<open>erule st_tcb_weakenE, fastforce\<close>)
  apply (subgoal_tac "ex_nonz_cap_to dest s")
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
  assumes reply_unlink_tcb_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> reply_unlink_tcb a \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. \<exists>rptr. st_tcb_at active tptr s \<and> st_tcb_at ((=) Inactive) dest s \<and> invs s \<and>
        ex_nonz_cap_to tptr s \<and> ex_nonz_cap_to dest s \<and> reply = Some rptr \<and> ex_nonz_cap_to rptr s \<and>
        reply_sc_reply_at (\<lambda>sc. sc = None) rptr s \<and> bound_sc_tcb_at bound tptr s \<and> Q s\<rbrace>
   do sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then when (cg \<and> (\<exists>y. reply = Some y))
                  (reply_push tptr dest (the reply) can_donate)
           else when (can_donate \<and> sc_opt = None)
                  (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                      sched_context_donate (the caller_sc_opt) dest
                   od);
      new_sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      test \<leftarrow> case new_sc_opt of None \<Rightarrow> return True
              | Some scp \<Rightarrow> do sufficient <- refill_sufficient scp 0;
                               ready <- refill_ready scp;
                               return (sufficient \<and> ready)
                            od;
      y <- assert test;
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac "call \<or> fault \<noteq> None"; clarsimp)
   apply wpsimp
        apply (strengthen invs_valid_objs, clarsimp cong: conj_cong)
        apply (wpsimp wp: sts_invs_minor2_concise)
       apply wpsimp
      apply (wpsimp wp: hoare_drop_imp)
     apply (wpsimp simp: get_tcb_obj_ref_def)
    apply (wpsimp wp: hoare_vcg_conj_lift wp_del: reply_push_st_tcb_at)
     apply (rule_tac Q="\<lambda>_. st_tcb_at ((=) Inactive) dest" in hoare_strengthen_post)
      apply (wpsimp wp: reply_push_st_tcb_at_Inactive)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (wpsimp wp: reply_push_invs)
   apply (rule conjI; clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (frule invs_valid_objs)
   apply (frule invs_valid_global_refs)
   apply (drule (1) idle_no_ex_cap, clarsimp)
  apply wpsimp
       apply (strengthen invs_valid_objs, clarsimp cong: conj_cong)
       apply (wpsimp wp: sts_invs_minor2_concise)
      apply wpsimp
     apply (wpsimp wp: hoare_drop_imp)
    apply (wpsimp simp: get_tcb_obj_ref_def)
   apply (wpsimp wp: hoare_vcg_conj_lift sched_context_donate_invs
      simp: get_tcb_obj_ref_def thread_get_def)
  apply (subgoal_tac "dest \<noteq> idle_thread s")
   apply (clarsimp simp:)
   apply (clarsimp simp: is_tcb pred_tcb_at_def obj_at_def reply_sc_reply_at_def is_sc_obj_def)
   apply (clarsimp simp: get_tcb_rev dest!: get_tcb_SomeD)
   apply (frule invs_valid_objs)
   apply (erule (1) valid_objsE[where x=tptr])
   apply (clarsimp simp: valid_obj_def valid_tcb_def obj_at_def is_sc_obj_def)
   apply (case_tac ko; clarsimp)
   apply (frule invs_iflive)
   apply (erule (1) if_live_then_nonz_capD2)
   apply (frule invs_sym_refs)
   apply (frule invs_valid_objs)
   apply (drule (2) Arch.bound_sc_tcb_bound_sc_at) (* why is this in arch? *)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (rule_tac x="TCB tcb" in exI, clarsimp, simp)
   apply (clarsimp simp: live_def live_sc_def)
  apply clarsimp
  apply (frule invs_valid_objs)
  apply (frule invs_valid_global_refs)
  apply (drule (1) idle_no_ex_cap)
  by simp
  
  lemma not_sk_obj_at_pred:
  "\<not> sk_obj_at_pred C proj' P' p s \<Longrightarrow> sk_obj_at_pred C proj P p s
    \<Longrightarrow> sk_obj_at_pred C proj' (\<lambda>x. \<not> (P' x)) p s"
  by (fastforce simp: sk_obj_at_pred_def obj_at_def)

lemma si_invs'_helper:
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> reply_unlink_tcb a \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. all_invs_but_sym_refs s \<and> Q s \<and> st_tcb_at active tptr s \<and>
        ex_nonz_cap_to tptr s \<and> bound_sc_tcb_at bound tptr s \<and> ep_at epptr s \<and>
        (\<forall>x. (dest, x) \<notin> state_refs_of s epptr) \<and>
        st_tcb_at (\<lambda>st. \<exists>r. st = BlockedOnReceive epptr r) dest s \<and> ex_nonz_cap_to epptr s \<and>
        valid_replies s \<and>
        sym_refs (\<lambda>x. if x = dest
                      then {r \<in> state_refs_of s x. snd r = TCBBound \<or> snd r = TCBSchedContext \<or>
                            snd r = TCBYieldTo \<or> snd r = TCBReply}
                      else state_refs_of s x) \<and>
        sym_refs (state_hyp_refs_of s)\<rbrace>
   do recv_state <- get_thread_state dest;
      reply <- case recv_state of BlockedOnReceive x reply \<Rightarrow>
                         return reply
               | _ \<Rightarrow> fail;
      y \<leftarrow> do_ipc_transfer tptr (Some epptr) ba cg dest;
      y \<leftarrow> maybeM reply_unlink_tcb reply;
      sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then when (cg \<and> (\<exists>y. reply = Some y))
                  (reply_push tptr dest (the reply) can_donate)
           else when (can_donate \<and> sc_opt = None)
                  (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                      sched_context_donate (the caller_sc_opt) dest
                   od);
      new_sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      test \<leftarrow> case new_sc_opt of None \<Rightarrow> return True
              | Some scp \<Rightarrow> do sufficient <- refill_sufficient scp 0;
                               ready <- refill_ready scp;
                               return (sufficient \<and> ready)
                            od;
      y <- assert test;
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  supply if_weak_cong[cong del]
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac recv_state; simp)
  apply (rename_tac r)
  apply (case_tac r, simp)
   apply (wpsimp wp: si_invs'_helper_no_reply wp_del: maybeM_inv)
    apply (wpsimp wp: valid_irq_node_typ do_ipc_transfer_bound_sc)
   apply clarsimp
   apply (intro conjI)
     apply (clarsimp simp: st_tcb_at_def obj_at_def)
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
  apply (wpsimp wp: si_invs'_helper_some_reply wp_del: maybeM_inv)
    apply (rule hoare_vcg_conj_lift)
     apply (wpsimp wp: reply_unlink_tcb_st_tcb_at')
    apply (wpsimp wp: reply_unlink_tcb_invs_BlockedOnReceive
                      reply_unlink_tcb_bound_sc_tcb_at)
   apply (wpsimp wp: hoare_ex_wp valid_irq_node_typ do_ipc_transfer_bound_sc)
  apply clarsimp
  apply (subgoal_tac "reply_tcb_reply_at (\<lambda>b. b = Some dest) rptr s")
   apply (intro conjI)
         apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def st_tcb_at_def)
        apply clarsimp
       apply fastforce
      apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
     apply (clarsimp simp: st_tcb_at_def obj_at_def)
     apply (fastforce simp: live_def elim!: if_live_then_nonz_capD2)
    apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def)
    apply (fastforce simp: live_def live_reply_def elim!: if_live_then_nonz_capD2)
   apply (rule ccontr, drule (1) not_sk_obj_at_pred, frule (1) valid_repliesD[OF _ refl], elim exE)
   apply (clarsimp simp: reply_at_ppred_def pred_tcb_at_def obj_at_def is_ep)
   apply (rule_tac V="rptr \<noteq> dest \<and> t \<noteq> dest" in revcut_rl, fastforce, elim conjE)
   apply (drule_tac x=t and y=rptr and tp=ReplyTCB in sym_refsE; clarsimp simp: state_refs_of_def)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (subgoal_tac "valid_obj dest (TCB tcb) s")
   apply (fastforce simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_reply sym_refs_def
                          reply_tcb_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                   split: if_splits)
  apply fastforce
  done

lemma si_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes possible_switch_to_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]:
    "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes reply_push_Q[wp]: "\<And>a b c d. \<lbrace>Q\<rbrace> reply_push a b c d \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sched_context_donate_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> sched_context_donate a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes reply_unlink_tcb_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> reply_unlink_tcb a \<lbrace>\<lambda>_. Q\<rbrace>"
  shows
  "\<lbrace>invs and Q and st_tcb_at active tptr and ex_nonz_cap_to tptr and bound_sc_tcb_at bound tptr
    and ex_nonz_cap_to epptr\<rbrace>
   send_ipc bl call ba cg can_donate tptr epptr
   \<lbrace>\<lambda>r. invs and Q\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (cases bl, simp_all)[1]
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (wpsimp wp: valid_irq_node_typ valid_ioports_lift)
      apply (simp add: live_def valid_ep_def)
      apply (wp valid_irq_node_typ sts_only_idle sts_typ_ats(1)[simplified ep_at_def2, simplified]
                sts_valid_replies_simple')
     apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at valid_ep_def)
     apply (apply_conjunct \<open>erule st_tcb_weakenE, fastforce\<close>)
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
                    wp: sort_queue_valid_ep_SendEP sts_valid_replies_simple'
                        valid_ioports_lift)
     apply (wpsimp simp: valid_ep_def
                     wp: hoare_vcg_const_Ball_lift sts_only_idle valid_irq_node_typ)
    apply (clarsimp simp: valid_tcb_state_def valid_ep_def)
    apply (intro conjI)
           apply (clarsimp simp: is_ep obj_at_def)
          apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
         apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def elim!: valid_objsE)
        apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def)
       apply (fastforce simp: st_tcb_at_def get_refs_def2 obj_at_def dest!: sym_refs_ko_atD)
      apply (fastforce elim: st_tcb_weakenE)
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
   apply (subgoal_tac "st_tcb_at (\<lambda>st. \<exists>r. st = BlockedOnReceive epptr r) dest s")
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
  assumes reply_unlink_tcb_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> reply_unlink_tcb a \<lbrace>\<lambda>_. Q\<rbrace>"
  notes si_invs''[wp] = si_invs'[where Q=Q]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and bound_sc_tcb_at bound t and
    (\<lambda>_. valid_fault f)\<rbrace>
   handle_fault t f
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>" including no_pre
  apply (cases "valid_fault f"; simp)
  apply (simp add: handle_fault_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_sp])
   apply (wpsimp simp: handle_no_fault_def unless_def)
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                    wp: sts_only_idle valid_irq_node_typ sts_valid_replies_simple')
   apply (simp add: send_fault_ipc_def)
   apply (case_tac "tcb_fault_handler tcb"; simp)
                apply (wpsimp simp: invs_def valid_state_def valid_pspace_def)
                apply (rule hoare_pre, wpsimp, clarsimp)
                apply (fastforce simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                                       tcb_st_refs_of_def idle_no_ex_cap
                                elim!: delta_sym_refs
                                split: if_splits thread_state.splits)
               defer
               apply (intro conjI)
                apply wpsimp
                 apply (rule hoare_strengthen_post)
                  apply (rule si_invs'; wpsimp)
                 apply clarsimp
                apply (rule hoare_pre)
                apply (wpsimp simp: tcb_cap_cases_def wp: thread_set_invs_trivial hoare_vcg_conj_lift)
                  apply auto[8]
                     apply wpsimp
                    apply (rule thread_set_no_change_tcb_state, simp)
                   apply (rule ex_nonz_cap_to_pres)
                   apply (rule thread_set_cte_wp_at_trivial, simp add: tcb_cap_cases_def)
                  apply (rule thread_set_no_change_tcb_sched_context, simp)
                 apply (rule ex_nonz_cap_to_pres)
                 apply (rule thread_set_cte_wp_at_trivial, simp add: tcb_cap_cases_def)
                apply clarsimp
                     apply (simp (no_asm) add: ex_nonz_cap_to_def cte_wp_at_cases2)
                     apply (rule_tac x = t in exI)
                     apply (rule_tac x = "tcb_cnode_index 3" in exI)
                     apply (clarsimp simp: obj_at_def tcb_cnode_map_def)
                    apply wpsimp+
  done

lemmas hf_invs[wp] = hf_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI TrueI,simplified]

crunches maybe_return_sc
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (simp: get_sk_obj_ref_def get_simple_ko_def get_object_def wp: weak_if_wp)

lemma maybe_return_sc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def get_sk_obj_ref_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def get_sk_obj_ref_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def get_sk_obj_ref_def get_simple_ko_def get_object_def
               wp: weak_if_wp)

lemma maybe_return_sc_zombies_final[wp]:
  "\<lbrace>zombies_final\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
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

lemma valid_replies_state_refs_lift:
  assumes "\<And>P. \<lbrace> \<lambda>s. P (state_refs_of s) \<and> Q s \<rbrace> f \<lbrace> \<lambda>rv s. P (state_refs_of s) \<rbrace>"
  shows "\<lbrace> valid_replies_pred P and Q \<rbrace> f \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  by (wpsimp simp: replies_with_sc_def2 replies_blocked_def2 wp: assms)

lemma maybe_return_sc_sym_refs_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_mdb[wp]:
  "\<lbrace>valid_mdb\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> tcb_ptr \<noteq> idle_thread s\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def
                   get_simple_ko_def get_object_def)

lemma maybe_return_sc_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_if_unsafe_then_cap[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_irq_node\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_irq_states\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_machine_state[wp]:
  "\<lbrace>valid_machine_state\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_machine_state\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_global_objs[wp]:
  "\<lbrace>valid_global_objs\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_kernel_mappings[wp]:
  "\<lbrace>valid_kernel_mappings\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_equal_kernel_mappings[wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_asid_map[wp]:
  "\<lbrace>valid_asid_map\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma maybe_return_sc_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: weak_if_wp hoare_drop_imp)

lemma valid_bound_sc_typ_at:
  "\<forall>p. \<lbrace>\<lambda>s. sc_at p s\<rbrace> f \<lbrace>\<lambda>_ s. sc_at p s\<rbrace>
    \<Longrightarrow> \<lbrace>\<lambda>s. valid_bound_sc sc s\<rbrace> f \<lbrace>\<lambda>_ s. valid_bound_sc sc s\<rbrace>"
  apply (clarsimp simp: valid_bound_obj_def split: option.splits)
  apply (wpsimp wp: hoare_vcg_all_lift static_imp_wp)
   defer
   apply assumption
  apply fastforce
  done

lemma sort_queue_ntfn_bound_tcb:
  "\<lbrace>\<lambda>s. ntfn_bound_tcb x = None\<rbrace> sort_queue q
   \<lbrace>\<lambda>rv s. case ntfn_bound_tcb x of None \<Rightarrow> True | Some tcb \<Rightarrow> rv = [tcb]\<rbrace>"
  by (case_tac "ntfn_bound_tcb x = None"; wpsimp)

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
  by (wpsimp simp: set_thread_state_def set_object_def valid_bound_obj_def is_tcb obj_at_def
               split: option.splits)

lemma set_thread_state_valid_bound_sc[wp]:
  "\<lbrace>valid_bound_sc sc\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. valid_bound_sc sc\<rbrace>"
  apply (wpsimp simp: set_thread_state_def valid_bound_obj_def set_object_def
               split: option.splits)
  apply (clarsimp simp: is_sc_obj_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma as_user_bound_sc[wp]:
  "\<lbrace>valid_bound_sc sc\<rbrace> as_user t f \<lbrace>\<lambda>rv. valid_bound_sc sc\<rbrace>"
  apply (wpsimp simp: as_user_def set_object_def valid_bound_obj_def split: option.splits)
  apply (clarsimp simp: is_sc_obj_def obj_at_def get_tcb_SomeD)
  done

global_interpretation maybe_return_sc: non_reply_op "maybe_return_sc ntfn_ptr tcb_ptr"
  by unfold_locales (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps get_sk_obj_ref_wp
                          simp: maybe_return_sc_def)

lemma maybe_return_sc_valid_replies[wp]:
  "maybe_return_sc ntfn_ptr tcb_ptr \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp simp: maybe_return_sc_def wp: hoare_vcg_if_lift2 hoare_drop_imps get_sk_obj_ref_wp)

lemma as_user_valid_replies[wp]:
  "as_user t f \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

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
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: valid_ioports_lift)
      apply (wpsimp simp: valid_ntfn_def live_def live_ntfn_def pred_conj_def
                      wp: sts_only_idle valid_irq_node_typ sts_valid_replies_simple'
                          valid_ioports_lift)
     apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_tcb_state_def
                           ntfn_at_typ obj_at_def st_tcb_at_def is_tcb valid_ntfn_def)
     apply (intro conjI)
             apply (clarsimp split: option.splits)
            apply (clarsimp simp: valid_bound_obj_def is_tcb obj_at_def split: option.splits)
           apply (fastforce simp: valid_obj_def valid_ntfn_def)
          apply fastforce
         apply (fastforce simp: state_refs_of_def get_refs_def2
                         split: if_splits
                         elim!: delta_sym_refs)
        apply fastforce
       apply (fastforce simp: is_tcb obj_at_def)
      apply (fastforce simp: valid_obj_def valid_ntfn_def)
     apply (fastforce dest!: idle_no_ex_cap)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def wp: valid_irq_node_typ)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def valid_ntfn_def
                       live_def live_ntfn_def do_nbrecv_failed_transfer_def
                       valid_tcb_state_def
                   wp: sort_queue_ntfn_bound_tcb sts_only_idle sts_valid_replies_simple'
                       valid_irq_node_typ[where f="as_user t f" for t f]
                       valid_ioports_lift)
   apply (rule conjI, clarsimp simp: is_ntfn obj_at_def)
   apply (rule conjI, clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
   apply (rule obj_at_valid_objsE, assumption+)
   apply (rule conjI, clarsimp simp: valid_obj_def valid_ntfn_def)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def)
   apply (rule conjI,
          fastforce simp: obj_at_def st_tcb_at_def get_refs_def2 dest!: sym_refs_ko_atD bspec)
   apply (apply_conjunct \<open>erule st_tcb_weakenE, fastforce\<close>)
   apply (subgoal_tac "ntfn_bound_tcb notification = None")
    apply (rule conjI, simp)
    apply (rule conjI, rule delta_sym_refs, assumption)
      apply (fastforce simp: state_refs_of_def obj_at_def st_tcb_at_def split: if_splits)
     apply (fastforce simp: state_refs_of_def st_tcb_at_def obj_at_def get_refs_def2
                     split: if_splits)
    apply (rule conjI, clarsimp simp: is_ntfn obj_at_def)
    apply (rule conjI, clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
    apply (fastforce simp: idle_no_ex_cap obj_at_def st_tcb_at_def get_refs_def2
                    dest!: sym_refs_ko_atD bspec)
   apply (fastforce simp: obj_at_def st_tcb_at_def get_refs_def2
                   dest!: sym_refs_ko_atD)
  apply wpsimp
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def wp: valid_ioports_lift)
   apply (wpsimp simp: valid_ntfn_def wp: static_imp_wp valid_irq_node_typ valid_ioports_lift)
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def state_refs_of_def valid_obj_def
                         valid_ntfn_def
                  elim!: obj_at_valid_objsE delta_sym_refs
                  split: if_splits)
  done

lemmas rai_invs[wp] = rai_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

end
