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
imports "./$L4V_ARCH/ArchIpc_AI"
begin

crunch typ_at[wp]: send_ipc "\<lambda>(s::det_ext state). P (typ_at T p s)"
  (wp: hoare_drop_imps mapM_wp_inv maybeM_inv simp: crunch_simps)

lemma si_tcb_at [wp]:
  "\<And>t' call bl w d cd t ep.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      send_ipc call bl w d cd t ep
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma handle_fault_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> handle_fault t f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: handle_fault_def unless_def handle_no_fault_def send_fault_ipc_def)

lemma hf_tcb_at [wp]:
  "\<And>t' t x.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      handle_fault t x
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma sfi_tcb_at [wp]:
  "\<And>t tptr handler_cap fault can_donate.
    \<lbrace>tcb_at t :: det_ext state \<Rightarrow> bool\<rbrace>
      send_fault_ipc tptr handler_cap fault can_donate
    \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (wpsimp simp: send_fault_ipc_def)

lemma reply_push_idle_thread:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: reply_push_def comp_def unbind_reply_in_ts_def no_reply_in_ts_def
               wp: hoare_drop_imp)

lemma receive_ipc_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>
   receive_ipc thread cap is_blocking reply_cap \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  apply (simp add: receive_ipc_def)
  apply (case_tac cap; simp)
  apply (case_tac reply_cap; simp)
   apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
   apply (rename_tac ep)
   apply (rule hoare_seq_ext[OF _ gbn_sp])
   apply (case_tac ntfnptr; simp)
    apply (case_tac ep; simp)
      apply (case_tac is_blocking; simp)
       apply wpsimp
      apply (wpsimp simp: do_nbrecv_failed_transfer_def)
     apply (wpsimp wp: hoare_drop_imp)
    apply (case_tac is_blocking; simp)
     apply (wpsimp simp: sort_queue_def wp: mapM_wp_inv)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def)
   apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
   apply (case_tac "isActive ntfn"; simp)
    apply (simp add: complete_signal_def)
    apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
    apply wpsimp
   apply (case_tac ep; simp)
  apply (wpsimp simp: do_nbrecv_failed_transfer_def)
    apply (wpsimp wp:  hoare_drop_imp)
   apply (wpsimp simp: sort_queue_def do_nbrecv_failed_transfer_def wp: mapM_wp_inv)
  apply wpsimp
        apply (wpsimp simp: complete_signal_def wp: hoare_drop_imp)
       apply (case_tac ep; simp)
         apply (wpsimp simp: sort_queue_def do_nbrecv_failed_transfer_def
                         wp: reply_push_idle_thread hoare_drop_imp mapM_wp_inv)+
  done

crunch cap_to[wp]: receive_ipc "ex_nonz_cap_to p :: det_ext state \<Rightarrow> bool"
  (wp: cap_insert_ex_cap hoare_drop_imps maybeM_inv simp: crunch_simps ignore: set_object)

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
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (rename_tac tptr list s')
   apply (erule_tac x = tptr in ballE)
    apply (rotate_tac -1)
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
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
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (rename_tac tptr list s')
   apply (erule_tac x = tptr in ballE)
    apply (rotate_tac -1)
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
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

lemma sort_queue_invs:
  "\<lbrace>invs\<rbrace> sort_queue q \<lbrace>\<lambda>q'. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wpsimp simp: sort_queue_def wp: mapM_wp_inv)
  done

lemma sort_queue_inv[wp]:
  "\<lbrace>P\<rbrace> sort_queue q \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: sort_queue_def wp: mapM_wp_inv)
  done

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

lemma cancel_ipc_st_tcb_at_active:
  "\<lbrace>\<lambda>s. invs s \<and> st_tcb_at active t' s \<and> t \<noteq> t'\<rbrace>
   cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at active t'\<rbrace>"
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

lemma ri_invs':
  fixes Q t cap is_blocking reply
  notes if_split[split del]
  notes hyp_refs_of_simps[simp del]
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes set_notification_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> complete_signal a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a (s::'a::state_ext state). \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes dit_Q: "\<And>a b c d e. \<lbrace>valid_mdb and valid_objs and Q\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes failed_transfer_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> do_nbrecv_failed_transfer a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sort_queue_Q[wp]: "\<And>q. \<lbrace>Q\<rbrace> sort_queue q \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes cancel_ipc_Q[wp]: "\<And>t. \<lbrace>invs and Q\<rbrace> cancel_ipc t \<lbrace>\<lambda>_. Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>(invs::det_ext state \<Rightarrow> bool) and Q and st_tcb_at active t and ex_nonz_cap_to t
         and cte_wp_at (op = cap.NullCap) (t, tcb_cnode_index 3)
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)\<rbrace>
     receive_ipc t cap is_blocking reply \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  sorry

lemmas ri_invs[wp]
  = ri_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

lemma si_blk_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
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
  apply (case_tac recv_state; simp)
  apply (wpsimp wp: sts_st_tcb_at_cases hoare_drop_imp)
    apply (intro conjI, wpsimp+)
   apply (intro conjI, wpsimp+)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (case_tac "tcb_state tcb"; simp)
  done

lemma sfi_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
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
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace> handle_fault t ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  apply (simp add: handle_fault_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb])
  apply (wpsimp simp: unless_def handle_no_fault_def send_fault_ipc_def wp: sts_st_tcb_at_cases)
  apply (case_tac "tcb_fault_handler tcb"; simp)
   apply wpsimp
  apply (wpsimp wp: si_blk_makes_simple)
  apply (wpsimp simp: thread_set_def set_object_def st_tcb_at_def obj_at_def)
  done

lemma grt_sp:
  "\<lbrace>P\<rbrace> get_reply_tcb reply_ptr \<lbrace>\<lambda>rv. reply_tcb_reply_at (\<lambda>x. x = rv) reply_ptr and P\<rbrace>"
  apply (wpsimp simp: get_simple_ko_def get_object_def)
  apply (auto simp: reply_tcb_reply_at_def obj_at_def)
  done

lemma no_reply_in_ts_inv[wp]:
  "\<lbrace>P\<rbrace> no_reply_in_ts t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: no_reply_in_ts_def get_thread_state_def thread_get_def)

lemma unbind_reply_in_ts_inv:
  "\<lbrace>P and st_tcb_at (op = Inactive) t\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: unbind_reply_in_ts_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp | wpsimp simp: st_tcb_at_def obj_at_def wp: hoare_pre_cont)+
  done

lemma unbind_reply_in_ts_ex_nonz_cap_to:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def get_thread_state_def thread_get_def)

lemma unbind_reply_in_ts_valid_objs:
  "\<lbrace>valid_objs\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: unbind_reply_in_ts_def get_thread_state_def thread_get_def)
  apply (fastforce simp: valid_obj_def valid_tcb_def valid_tcb_state_def dest!: get_tcb_SomeD)
  done

lemma unbind_reply_in_ts_tcb_at:
  "\<lbrace>tcb_at t'\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def get_thread_state_def thread_get_def)

lemma unbind_reply_in_ts_reply_at:
  "\<lbrace>reply_at r\<rbrace> unbind_reply_in_ts t \<lbrace>\<lambda>rv. reply_at r\<rbrace>"
  by (wpsimp simp: unbind_reply_in_ts_def get_thread_state_def thread_get_def)

lemma set_reply_tcb_valid_tcb_state:
  "\<lbrace>reply_at reply_ptr'\<rbrace>
   set_reply_obj_ref reply_tcb_update reply_ptr t
   \<lbrace>\<lambda>rv. valid_tcb_state (BlockedOnReply (Some reply_ptr'))\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_object_def
                   get_simple_ko_def valid_tcb_state_def is_reply obj_at_def)

lemma set_reply_tcb_reply_at:
  "\<lbrace>reply_at reply_ptr'\<rbrace> set_reply_obj_ref reply_tcb_update reply_ptr t \<lbrace>\<lambda>rv. reply_at reply_ptr'\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma set_reply_tcb_sc_at:
  "\<lbrace>sc_at sc_ptr\<rbrace> set_reply_obj_ref reply_tcb_update reply_ptr t \<lbrace>\<lambda>rv. sc_at sc_ptr\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_object_def
                      get_simple_ko_def)
  apply (auto simp: is_sc_obj_def obj_at_def)
  done

lemma set_reply_tcb_reply_sc:
  "\<lbrace>reply_sc_reply_at P reply_ptr'\<rbrace>
   set_reply_obj_ref reply_tcb_update reply_ptr t
   \<lbrace>\<lambda>rv. reply_sc_reply_at P reply_ptr'\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_object_def
                      get_simple_ko_def)
  apply (auto simp: reply_sc_reply_at_def obj_at_def)
  done

lemma set_reply_sc_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> set_reply_obj_ref reply_sc_update r sc \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

lemma set_reply_sc_sc_at:
  "\<lbrace>sc_at sc'\<rbrace> set_reply_obj_ref reply_sc_update r sc \<lbrace>\<lambda>rv. sc_at sc'\<rbrace>"
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_object_def
                      get_simple_ko_def)
  apply (auto simp: is_sc_obj_def obj_at_def)
  done

lemma set_sc_replies_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace>
   set_sc_obj_ref sc_replies_update sc replies
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: set_sc_obj_ref_def)

lemma set_thread_state_reply_sc:
  "\<lbrace>reply_sc_reply_at P reply_ptr\<rbrace>
   set_thread_state caller ts
   \<lbrace>\<lambda>rv. reply_sc_reply_at P reply_ptr\<rbrace>"
  by (wpsimp simp: set_thread_state_def reply_sc_reply_at_def set_object_def obj_at_def get_tcb_def)

lemma reply_unlink_tcb_sym_refs_BlockedOnReceive:
  "\<lbrace>\<lambda>s. (\<exists>tptr epptr. st_tcb_at (op = (BlockedOnReceive epptr (Some rptr))) tptr s \<and>
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
    apply (fastforce simp: get_refs_def2)
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
  "\<lbrace>\<lambda>s. (\<exists>tptr epptr. st_tcb_at (op = (BlockedOnReceive epptr (Some rptr))) tptr s \<and>
                      sym_refs (\<lambda>x. if x = tptr then
                                      {r \<in> state_refs_of s x. snd r = TCBBound \<or>
                                       snd r = TCBSchedContext \<or> snd r = TCBYieldTo
                                       \<or> snd r = TCBReply}
                                    else state_refs_of s x)) \<and>
                      all_invs_but_sym_refs s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   reply_unlink_tcb rptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def
               wp: reply_unlink_tcb_sym_refs_BlockedOnReceive)

lemma reply_unlink_tcb_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> reply_unlink_tcb r \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def set_thread_state_def reply_sc_reply_at_def
                   set_object_def set_simple_ko_def get_object_def get_thread_state_def
                   thread_get_def get_simple_ko_def obj_at_def get_tcb_def)

lemma as_user_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace>
   as_user t f
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: as_user_def set_object_def reply_tcb_reply_at_def obj_at_def get_tcb_def)

lemma as_user_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace>
   as_user t f
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: as_user_def set_object_def reply_sc_reply_at_def obj_at_def get_tcb_def)

lemma set_message_info_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> set_message_info thread info \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: set_message_info_def wp: as_user_reply_tcb)

lemma set_message_info_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> set_message_info thread info \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: set_message_info_def wp: as_user_reply_sc)

lemma update_cdt_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> update_cdt t \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: update_cdt_def set_cdt_def reply_tcb_reply_at_def)

lemma update_cdt_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> update_cdt t \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: update_cdt_def set_cdt_def reply_sc_reply_at_def)

lemma set_original_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> set_original slot v \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: set_original_def reply_tcb_reply_at_def)

lemma set_original_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> set_original slot v \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: set_original_def reply_sc_reply_at_def)

lemma set_cap_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> set_cap cap cslot_ptr \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  apply (wpsimp simp: set_cap_def set_object_def get_object_def)
  apply (auto simp: reply_tcb_reply_at_def obj_at_def)
  done

lemma set_cap_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> set_cap cap cslot_ptr \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  apply (wpsimp simp: set_cap_def set_object_def get_object_def)
  apply (auto simp: reply_sc_reply_at_def obj_at_def)
  done

lemma set_untyped_cap_as_full_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: set_untyped_cap_as_full_def wp: set_cap_reply_tcb)

lemma set_untyped_cap_as_full_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: set_untyped_cap_as_full_def wp: set_cap_reply_sc)

lemma transfer_caps_loop_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace>
   transfer_caps_loop ep rcv_buffer n list slots mi
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  apply (rule transfer_caps_loop_pres)
   apply (wpsimp simp: cap_insert_def wp: set_original_reply_tcb)
             apply (clarsimp simp: reply_tcb_reply_at_def)
            apply (wpsimp wp: update_cdt_reply_tcb)
           apply (wpsimp simp: get_cap_def get_object_def
                           wp: set_cap_reply_tcb set_untyped_cap_as_full_reply_tcb)+
  apply (wpsimp simp: set_extra_badge_def store_word_offs_def do_machine_op_def
                      reply_tcb_reply_at_def)
  done

lemma transfer_caps_loop_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace>
   transfer_caps_loop ep rcv_buffer n list slots mi
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  apply (rule transfer_caps_loop_pres)
   apply (wpsimp simp: cap_insert_def wp: set_original_reply_sc)
             apply (clarsimp simp: reply_sc_reply_at_def)
            apply (wpsimp wp: update_cdt_reply_sc)
           apply (wpsimp simp: get_cap_def get_object_def
                           wp: set_cap_reply_sc set_untyped_cap_as_full_reply_sc)+
  apply (wpsimp simp: set_extra_badge_def store_word_offs_def do_machine_op_def
                      reply_sc_reply_at_def)
  done

lemma store_word_offs_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: store_word_offs_def do_machine_op_def reply_tcb_reply_at_def)

lemma store_word_offs_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: store_word_offs_def do_machine_op_def reply_sc_reply_at_def)

lemma set_mrs_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  apply (wpsimp simp: set_mrs_def)
     apply (intro conjI)
      apply (wpsimp simp: zipWithM_x_mapM wp: mapM_wp store_word_offs_reply_tcb)
      apply fastforce
     apply (wpsimp simp: zipWithM_x_mapM wp: mapM_wp store_word_offs_reply_tcb)
    apply (wpsimp simp: set_object_def)
   apply wpsimp
  apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def get_tcb_def)
  done

lemma set_mrs_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  apply (wpsimp simp: set_mrs_def)
     apply (intro conjI)
      apply (wpsimp simp: zipWithM_x_mapM wp: mapM_wp store_word_offs_reply_sc)
      apply fastforce
     apply (wpsimp simp: zipWithM_x_mapM wp: mapM_wp store_word_offs_reply_sc)
    apply (wpsimp simp: set_object_def)
   apply wpsimp
  apply (clarsimp simp: reply_sc_reply_at_def obj_at_def get_tcb_def)
  done

lemma sched_context_update_consumed_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> sched_context_update_consumed sc_ptr
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def set_sched_context_def set_object_def
                   get_object_def get_sched_context_def reply_tcb_reply_at_def obj_at_def)

lemma sched_context_update_consumed_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> sched_context_update_consumed sc_ptr
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def set_sched_context_def set_object_def
                   get_object_def get_sched_context_def reply_sc_reply_at_def obj_at_def)

lemma transfer_caps_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> transfer_caps info caps endpoint receiver recv_buffer
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: transfer_caps_def wp: transfer_caps_loop_reply_tcb)

lemma transfer_caps_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> transfer_caps info caps endpoint receiver recv_buffer
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: transfer_caps_def wp: transfer_caps_loop_reply_sc)

lemma transfer_caps_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace>
   transfer_caps info caps endpoint receiver recv_buffer
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: transfer_caps_def)

lemma copy_mrs_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
    apply (intro conjI)
     apply (wpsimp wp: mapM_wp store_word_offs_reply_tcb)
     apply fastforce
    apply (wpsimp wp: mapM_wp store_word_offs_reply_tcb)
   apply (wpsimp wp: mapM_wp as_user_reply_tcb)
   apply auto
  done

lemma copy_mrs_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
  apply (intro conjI)
     apply (wpsimp wp: mapM_wp store_word_offs_reply_sc)
     apply fastforce
    apply (wpsimp wp: mapM_wp store_word_offs_reply_sc)
   apply (wpsimp wp: mapM_wp as_user_reply_sc)
   apply auto
  done

lemma copy_mrs_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> copy_mrs sender sbuf receiver rbuf n \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
    apply (intro conjI)
     apply (wpsimp wp: mapM_wp | fastforce)+
  done

lemma do_normal_transfer_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace>
   do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: do_normal_transfer_def
               wp: as_user_reply_tcb set_message_info_reply_tcb transfer_caps_reply_tcb
                   copy_mrs_reply_tcb)

lemma do_normal_transfer_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace>
   do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: do_normal_transfer_def
               wp: as_user_reply_sc set_message_info_reply_sc transfer_caps_reply_sc
                   copy_mrs_reply_sc)

lemma do_normal_transfer_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace>
   do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: do_normal_transfer_def
               wp: transfer_caps_bound_sc copy_mrs_bound_sc)

lemma do_fault_transfer_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace>
   do_fault_transfer badge sender receiver buf
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  apply (wpsimp simp: do_fault_transfer_def
                  wp: as_user_reply_tcb set_message_info_reply_tcb set_mrs_reply_tcb)
     apply (case_tac f)
         apply wpsimp
         apply (intro conjI)
          apply (wpsimp wp: as_user_reply_tcb sched_context_update_consumed_reply_tcb)+
   apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: get_tcb_def)
  done

lemma do_fault_transfer_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace>
   do_fault_transfer badge sender receiver buf
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  apply (wpsimp simp: do_fault_transfer_def
                  wp: as_user_reply_sc set_message_info_reply_sc set_mrs_reply_sc)
     apply (case_tac f)
         apply wpsimp
         apply (intro conjI)
          apply (wpsimp wp: as_user_reply_sc sched_context_update_consumed_reply_sc)+
   apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: get_tcb_def)
  done

lemma do_fault_transfer_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> do_fault_transfer badge sender receiver buf \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  apply (wpsimp simp: do_fault_transfer_def)
     apply (case_tac f)
         apply (intro conjI | wpsimp)+
   apply (wpsimp simp: thread_get_def)
  apply (clarsimp simp: get_tcb_def)
  done

lemma do_ipc_transfer_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def
               wp: do_normal_transfer_reply_tcb do_fault_transfer_reply_tcb)

lemma do_ipc_transfer_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def
               wp: do_normal_transfer_reply_sc do_fault_transfer_reply_sc)

lemma do_ipc_transfer_bound_sc:
  "\<lbrace>bound_sc_tcb_at P t\<rbrace> do_ipc_transfer sender ep badge grant receiver \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def
               wp: do_normal_transfer_bound_sc do_fault_transfer_bound_sc)

lemma sched_context_donate_sym_refs:
  "\<lbrace>\<lambda>s. valid_objs s \<and> sym_refs (state_refs_of s) \<and> tcb_at tcb_ptr s \<and>
        bound_sc_tcb_at (op = None) tcb_ptr s\<rbrace>
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
     apply (clarsimp split: if_splits)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def split: if_splits)
     apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
     apply clarsimp
     apply (erule_tac x = "(tcb_ptr, SCTcb)" in ballE)
      apply (fastforce simp: state_refs_of_def is_tcb get_refs_def2)
     apply (clarsimp simp: get_refs_def2)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def state_refs_of_def get_refs_def2)
   apply (clarsimp, intro conjI)
    apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_tcb)
   apply (clarsimp, intro conjI)
    apply (fastforce simp: sc_tcb_sc_at_def valid_obj_def valid_sched_context_def
                           valid_bound_obj_def is_tcb obj_at_def
                   split: option.splits)
   apply clarsimp
   apply (rule delta_sym_refs, assumption)
    apply (clarsimp split: if_splits)
   apply (clarsimp split: if_splits)
     apply (clarsimp simp: obj_at_def state_refs_of_def get_refs_def2 pred_tcb_at_def)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def state_refs_of_def get_refs_def2)
   apply (intro conjI)
    apply (fastforce simp: sc_tcb_sc_at_def valid_obj_def valid_sched_context_def
                           valid_bound_obj_def is_tcb obj_at_def state_refs_of_def get_refs_def2
                    split: option.splits)
   apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
   apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
   apply (fastforce simp: valid_obj_def valid_sched_context_def valid_bound_obj_def is_tcb
                          obj_at_def get_refs_def2 state_refs_of_def
                   split: option.splits)
  apply wpsimp
  apply (fastforce simp: sc_tcb_sc_at_def pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                  split: if_splits
                  elim!: delta_sym_refs)
  done

lemma sched_context_donate_invs:
  "\<lbrace>\<lambda>s. invs s \<and> tcb_at tcb_ptr s \<and> ex_nonz_cap_to sc_ptr s \<and> ex_nonz_cap_to tcb_ptr s \<and>
    bound_sc_tcb_at (op = None) tcb_ptr s \<and> sc_at sc_ptr s\<rbrace>
   sched_context_donate sc_ptr tcb_ptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: sched_context_donate_sym_refs)
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

lemma sched_context_donate_sym_refs_BlockedOnReceive:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
        sym_refs (\<lambda>a. if a = dest
                      then {r \<in> state_refs_of s dest. snd r = TCBBound \<or> snd r = TCBSchedContext
                            \<or> snd r = TCBYieldTo}
                      else state_refs_of s a) \<and>
        sc_tcb_sc_at (\<lambda>t. \<exists>caller. t = Some caller \<and> st_tcb_at active caller s) scptr s \<and>
        st_tcb_at (\<lambda>st. \<exists>epptr. st = BlockedOnReceive epptr None) dest s \<and>
        bound_sc_tcb_at (op = None) dest s\<rbrace>
   sched_context_donate scptr dest
   \<lbrace>\<lambda>rv s. sym_refs (\<lambda>a. if a = dest
                         then {r \<in> state_refs_of s dest. snd r = TCBBound \<or>
                               snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                         else state_refs_of s a)\<rbrace>"
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

lemma reply_push_st_tcb_at_Inactive:
  "\<lbrace>st_tcb_at (op = Inactive) callee and K (callee \<noteq> caller)\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. st_tcb_at (op = Inactive) callee\<rbrace>"
  by (wpsimp simp: reply_push_def update_sk_obj_ref_def set_sc_obj_ref_def comp_def
               wp: unbind_reply_in_ts_inv sts_st_tcb_at_cases
           wp_del: reply_push_st_tcb_at
      | wp hoare_drop_imp)+

lemma reply_push_invs_helper:
  "\<lbrace>invs and reply_at reply_ptr and sc_at sc_ptr and ex_nonz_cap_to reply_ptr and
    ex_nonz_cap_to callee and
    ex_nonz_cap_to sc_ptr and reply_sc_reply_at (\<lambda>sc_ptr'. sc_ptr' = None) reply_ptr\<rbrace>
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
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: when_def)
  apply (intro conjI)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_sp])
   apply (rule hoare_seq_ext[OF _ assert_sp])
   apply (rule hoare_seq_ext[OF _ gscrpls_sp[unfolded fun_app_def, simplified]])
   apply (case_tac sc_replies; simp)
    apply (wpsimp wp: sched_context_donate_invs)
      apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                      wp: valid_irq_node_typ set_reply_sc_bound_sc set_reply_sc_sc_at)
     apply (wpsimp wp: set_sc_replies_bound_sc)
    apply (fastforce simp: invs_def valid_state_def valid_pspace_def
                           reply_sc_reply_at_def obj_at_def state_refs_of_def get_refs_def2
                           sc_replies_sc_at_def pred_tcb_at_def is_tcb is_reply is_sc_obj_def
                    split: if_splits
                    elim!: delta_sym_refs)
   apply (wpsimp wp: sched_context_donate_invs)
      apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                      wp: valid_irq_node_typ set_reply_sc_bound_sc
                          set_reply_sc_sc_at)
     apply (wpsimp wp: set_sc_replies_bound_sc)
    apply (wpsimp simp: get_simple_ko_def get_object_def split_del: if_split)
   apply (clarsimp, intro conjI)
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
  apply wpsimp
  done

lemma reply_push_invs:
  "\<lbrace>invs and ex_nonz_cap_to callee and ex_nonz_cap_to caller and ex_nonz_cap_to reply_ptr and
    st_tcb_at active caller and st_tcb_at (op = Inactive) callee and
    reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ set_reply_tcb_valid_tcb_state
                       unbind_reply_in_ts_inv
            split_del: if_split)
    apply (wpsimp wp: hoare_drop_imp)
   apply clarsimp
   apply (intro conjI)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def reply_tcb_reply_at_def)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (intro conjI)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
     apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
    apply (rule delta_sym_refs, assumption)
     apply (clarsimp split: if_splits)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                          tcb_st_refs_of_def reply_tcb_reply_at_def
                   split: if_splits thread_state.splits)
   apply (clarsimp simp: idle_no_ex_cap)
  apply (intro conjI)
   apply (wpsimp wp: reply_push_invs_helper)
        apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                        wp: sts_only_idle valid_irq_node_typ set_thread_state_reply_sc)
       apply (wpsimp wp: set_reply_tcb_valid_tcb_state valid_irq_node_typ
                         set_reply_tcb_reply_at set_reply_tcb_sc_at set_reply_tcb_reply_sc)
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
                      unbind_reply_in_ts_inv
           split_del: if_split)
  apply (intro conjI)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def is_reply)
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

lemma reply_push_ex_nonz_cap_to:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: reply_push_def comp_def wp: hoare_drop_imp unbind_reply_in_ts_ex_nonz_cap_to)

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
   apply (case_tac sc_replies; simp)
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
  "\<lbrace>\<lambda>s. valid_objs s \<and> st_tcb_at (op = Inactive) callee s \<and> tcb_at caller s \<and>
        reply_sc_reply_at (\<lambda>sc. sc = None) reply_ptr s \<and> sym_refs (state_refs_of s) \<and>
        st_tcb_at active caller s\<rbrace>
   reply_push caller callee reply_ptr can_donate
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: reply_push_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ grt_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_caller; simp)
   apply (wpsimp wp: set_reply_tcb_valid_tcb_state unbind_reply_in_ts_valid_objs
                     unbind_reply_in_ts_tcb_at unbind_reply_in_ts_reply_at)
    apply (wpsimp wp: hoare_drop_imp)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb reply_tcb_reply_at_def is_reply)
  apply (intro conjI)
   apply (wpsimp wp: reply_push_valid_objs_helper)
        apply (wpsimp wp: set_thread_state_reply_sc)
       apply (wpsimp wp: set_reply_tcb_valid_tcb_state set_reply_tcb_reply_at set_reply_tcb_sc_at
                         set_reply_tcb_reply_sc)
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
                    unbind_reply_in_ts_tcb_at unbind_reply_in_ts_reply_at hoare_drop_imp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb reply_tcb_reply_at_def is_reply)
  done

lemma set_endpoint_reply_tcb:
  "\<lbrace>reply_tcb_reply_at P r\<rbrace> set_endpoint epptr ep \<lbrace>\<lambda>rv. reply_tcb_reply_at P r\<rbrace>"
  by (wpsimp simp: set_simple_ko_def set_object_def get_object_def reply_tcb_reply_at_def
                   obj_at_def partial_inv_def)

lemma set_endpoint_reply_sc:
  "\<lbrace>reply_sc_reply_at P r\<rbrace> set_endpoint epptr ep \<lbrace>\<lambda>rv. reply_sc_reply_at P r\<rbrace>"
  by (wpsimp simp: set_simple_ko_def set_object_def get_object_def reply_sc_reply_at_def
                   obj_at_def partial_inv_def)

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
        st_tcb_at (\<lambda>st. \<exists>epptr. st = BlockedOnReceive epptr None) dest s \<and> reply = None \<and>
        all_invs_but_sym_refs s \<and>
        sym_refs (\<lambda>x. if x = dest
                      then {r \<in> state_refs_of s dest. snd r = TCBBound \<or>
                            snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                      else state_refs_of s x) \<and>
        sym_refs (state_hyp_refs_of s) \<and> bound_sc_tcb_at bound tptr s \<and> Q s\<rbrace>
   do
     sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
     fault <- thread_get tcb_fault tptr;
     y <- if call \<or> (\<exists>y. fault = Some y)
          then when (cg \<and> (\<exists>y. reply = Some y))
                 (reply_push tptr dest (the reply) can_donate)
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
   apply (clarsimp simp: when_def)
   apply (intro conjI)
    apply wpsimp
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ)
   apply (subgoal_tac "ex_nonz_cap_to dest s")
    apply (clarsimp simp: idle_no_ex_cap)
   apply (fastforce simp: st_tcb_at_def live_def elim!: if_live_then_nonz_capD)
  apply (simp add: when_def)
  apply (intro conjI)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                   wp: sts_only_idle valid_irq_node_typ
                       sched_context_donate_sym_refs_BlockedOnReceive)
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
                  wp: valid_irq_node_typ sts_only_idle)
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
  "\<lbrace>\<lambda>s. \<exists>rptr. st_tcb_at active tptr s \<and> st_tcb_at (op = Inactive) dest s \<and> invs s \<and>
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
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (rule hoare_seq_ext[OF _ thread_get_sp])
  apply (case_tac "call \<or> fault \<noteq> None"; simp)
   apply (clarsimp simp: when_def)
   apply (intro conjI)
    apply (wpsimp wp: sts_invs_minor2_concise wp_del: reply_push_st_tcb_at)
     apply (rule hoare_vcg_conj_lift)
      apply (rule hoare_strengthen_post)
       apply (wpsimp wp: reply_push_st_tcb_at_Inactive)
      apply (clarsimp simp: st_tcb_at_def obj_at_def)
     apply (wpsimp wp: reply_push_invs reply_push_ex_nonz_cap_to reply_push_idle_thread
                       reply_push_valid_objs)
    apply (fastforce simp: st_tcb_at_def obj_at_def invs_def valid_state_def valid_pspace_def
                           idle_no_ex_cap is_tcb)
   apply (case_tac cg; simp)
   apply (wpsimp simp: st_tcb_at_def obj_at_def invs_def valid_state_def valid_pspace_def
                       idle_no_ex_cap
                   wp: sts_invs_minor2_concise)
  apply (simp add: when_def)
  apply (intro conjI)
   apply (wpsimp simp: get_tcb_obj_ref_def thread_get_def
                   wp: sts_invs_minor2_concise sched_context_donate_invs)
   apply (rename_tac tcb)
   apply (subgoal_tac "sc_at (the (tcb_sched_context tcb)) s")
    apply (intro conjI)
          apply (clarsimp simp: st_tcb_at_def obj_at_def)
         apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
        apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
        apply (subgoal_tac "obj_at live (the (tcb_sched_context tcb)) s")
         apply (erule (2) if_live_then_nonz_capD)
        apply (clarsimp simp: obj_at_def)
        apply (clarsimp simp: pred_tcb_at_def obj_at_def is_sc_obj_def
                       split: kernel_object.splits)
        apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
        apply (fastforce simp: get_tcb_def get_refs_def2 live_def live_sc_def)
       apply clarsimp
      apply (clarsimp simp: invs_def valid_state_def valid_pspace_def idle_no_ex_cap)
     apply clarsimp
    apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def invs_def valid_state_def
                         valid_pspace_def)
   apply (subgoal_tac "valid_obj tptr (TCB tcb) s")
    apply (clarsimp simp: valid_obj_def valid_tcb_def is_sc_obj_def obj_at_def)
   apply fastforce
  apply (wpsimp wp: sts_invs_minor2_concise)
  apply (clarsimp simp: st_tcb_at_def obj_at_def invs_def valid_state_def valid_pspace_def
                        idle_no_ex_cap)
  done

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
        sym_refs (\<lambda>x. if x = dest
                      then {r \<in> state_refs_of s x. snd r = TCBBound \<or> snd r = TCBSchedContext \<or>
                            snd r = TCBYieldTo \<or> snd r = TCBReply}
                      else state_refs_of s x) \<and>
        sym_refs (state_hyp_refs_of s)\<rbrace>
   do recv_state <- get_thread_state dest;
      reply <- case recv_state of BlockedOnReceive x reply \<Rightarrow>
                      do do_ipc_transfer tptr (Some epptr) ba cg dest;
                         maybeM reply_unlink_tcb reply;
                         return reply
                      od
               | _ \<Rightarrow> fail;
      sc_opt <- get_tcb_obj_ref tcb_sched_context dest;
      fault <- thread_get tcb_fault tptr;
      y <- if call \<or> (\<exists>y. fault = Some y)
           then when (cg \<and> (\<exists>y. reply = Some y))
                  (reply_push tptr dest (the reply) can_donate)
           else when (can_donate \<and> sc_opt = None)
                  (do caller_sc_opt <- get_tcb_obj_ref tcb_sched_context tptr;
                      sched_context_donate (the caller_sc_opt) dest
                   od);
      y <- set_thread_state dest Running;
      possible_switch_to dest
   od
   \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac recv_state; simp)
  apply (rename_tac r)
  apply (case_tac r; simp)
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
    apply (rename_tac reftype)
    apply (subgoal_tac "(x, symreftype reftype) \<in> state_refs_of s dest")
     apply (fastforce simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2)
    apply (erule_tac x = x in allE, fastforce)
   apply (fastforce dest!: bspec)
  apply (rename_tac rptr)
  apply (wpsimp wp: si_invs'_helper_some_reply wp_del: maybeM_inv)
    apply (rule hoare_vcg_conj_lift)
     apply (wpsimp wp: reply_unlink_tcb_st_tcb_at')
    apply (wpsimp wp: reply_unlink_tcb_invs_BlockedOnReceive reply_unlink_tcb_reply_sc
                      reply_unlink_tcb_bound_sc_tcb_at)
   apply (wpsimp wp: do_ipc_transfer_reply_tcb hoare_ex_wp valid_irq_node_typ
                     do_ipc_transfer_reply_sc do_ipc_transfer_bound_sc)
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
  subgoal sorry (* based on the fact that "if a thread has thread_state BlockedOnReceive with an
  associated reply object r, then r has no associated scheduling context", which will be proved
  later on *)
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
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>invs and Q and st_tcb_at active tptr and ex_nonz_cap_to tptr and bound_sc_tcb_at bound tptr
    and ex_nonz_cap_to epptr\<rbrace>
   send_ipc bl call ba cg can_donate tptr epptr
   \<lbrace>\<lambda>r. invs and Q\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (cases bl, simp_all)[1]
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (wpsimp wp: valid_irq_node_typ)
      apply (simp add: live_def valid_ep_def)
      apply (wp valid_irq_node_typ sts_only_idle sts_ep_at_inv[simplified ep_at_def2, simplified])
     apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
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
    apply (wpsimp simp: live_def wp: sort_queue_valid_ep_SendEP)
     apply (wpsimp simp: valid_ep_def
                     wp: hoare_vcg_const_Ball_lift sts_only_idle valid_irq_node_typ)
    apply (clarsimp simp: valid_tcb_state_def)
    apply (intro conjI)
          apply (clarsimp simp: is_ep obj_at_def)
         apply (clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
        apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def elim!: valid_objsE)
       apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def)
      apply (fastforce simp: st_tcb_at_def get_refs_def2 obj_at_def dest!: sym_refs_ko_atD)
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
  apply (wpsimp wp: si_invs'_helper)
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
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  including no_pre
  apply (cases "valid_fault f"; simp)
  apply (simp add: handle_fault_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_sp])
   apply (wpsimp simp: handle_no_fault_def unless_def)
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                    wp: sts_only_idle valid_irq_node_typ)
   apply (simp add: send_fault_ipc_def)
   apply (case_tac "tcb_fault_handler tcb"; simp)
                apply (wpsimp simp: invs_def valid_state_def valid_pspace_def)
                apply (fastforce simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                                       tcb_st_refs_of_def idle_no_ex_cap
                                elim!: delta_sym_refs
                                split: if_splits thread_state.splits)
               defer
               apply (intro conjI)
                apply wpsimp
                 apply (rule hoare_strengthen_post)
                  apply wpsimp
                 apply clarsimp
                apply (wpsimp simp: tcb_cap_cases_def
                                wp: thread_set_invs_trivial thread_set_no_change_tcb_state
                                    ex_nonz_cap_to_pres thread_set_cte_wp_at_trivial
                                    thread_set_no_change_tcb_sched_context)
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
  (simp: get_sk_obj_ref_def get_simple_ko_def get_object_def wp: weak_if_wp)

lemma maybe_return_sc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
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
  by (wpsimp simp: set_thread_state_def set_object_def is_tcb obj_at_def)

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
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (cases cap, simp_all)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rename_tac notification, case_tac "ntfn_obj notification"; simp)
    apply (case_tac is_blocking; simp)
     apply (wpsimp simp: invs_def valid_state_def valid_pspace_def)
      apply (wpsimp simp: valid_ntfn_def live_def live_ntfn_def
                      wp: sts_only_idle valid_irq_node_typ)
     apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_tcb_state_def
                           ntfn_at_typ obj_at_def st_tcb_at_def is_tcb)
     apply (intro conjI)
            apply (clarsimp split: option.splits)
           apply (clarsimp simp: valid_bound_obj_def is_tcb obj_at_def split: option.splits)
          apply (fastforce simp: valid_obj_def valid_ntfn_def)
         apply (fastforce simp: state_refs_of_def get_refs_def2
                         split: if_splits
                         elim!: delta_sym_refs)
        apply fastforce
       apply (fastforce simp: is_tcb obj_at_def)
      apply (fastforce simp: valid_obj_def valid_ntfn_def)
     apply (fastforce dest!: idle_no_ex_cap)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def wp: valid_irq_node_typ)
   apply (wpsimp simp: invs_def valid_state_def valid_pspace_def valid_ntfn_def)
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_strengthen_post)
        apply (wpsimp wp: sort_queue_rv_wf)
       apply clarsimp
      apply (wpsimp simp: live_def live_ntfn_def wp: sort_queue_ntfn_bound_tcb)
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_strengthen_post)
        apply (wpsimp wp: sort_queue_rv_wf)
       apply clarsimp
      apply (wpsimp wp: sort_queue_ntfn_bound_tcb)
     apply (wpsimp wp: sts_only_idle valid_irq_node_typ)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def wp: valid_irq_node_typ)
   apply (intro conjI)
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_tcb_state_def)
    apply (rule conjI, clarsimp simp: is_ntfn obj_at_def)
    apply (rule conjI, clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
    apply (rule obj_at_valid_objsE, assumption+)
    apply (rule conjI, clarsimp simp: valid_obj_def valid_ntfn_def)
    apply (clarsimp simp: valid_obj_def valid_ntfn_def)
    apply (rule conjI,
           fastforce simp: obj_at_def st_tcb_at_def get_refs_def2 dest!: sym_refs_ko_atD bspec)
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
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply wpsimp
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (wpsimp simp: valid_ntfn_def wp: static_imp_wp valid_irq_node_typ)
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def state_refs_of_def valid_obj_def
                         valid_ntfn_def
                  elim!: obj_at_valid_objsE delta_sym_refs
                  split: if_splits)
  done

lemmas rai_invs[wp] = rai_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

end
