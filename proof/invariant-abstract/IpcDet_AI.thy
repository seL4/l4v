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

lemma si_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to ep and ex_nonz_cap_to t\<rbrace>
     send_ipc bl call ba cg can_donate t ep
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  sorry

lemma hf_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace>
                                               do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes thread_set_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> thread_set a b \<lbrace>\<lambda>_.Q\<rbrace>"
  notes si_invs''[wp] = si_invs'[where Q=Q]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and (\<lambda>_. valid_fault f)\<rbrace>
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
               apply wpsimp
              apply (intro conjI)
               apply (wpsimp simp: tcb_cap_cases_def
                               wp: thread_set_invs_trivial thread_set_no_change_tcb_state
                                   ex_nonz_cap_to_pres thread_set_cte_wp_at_trivial)
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
