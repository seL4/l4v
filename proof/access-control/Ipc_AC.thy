(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_AC
imports Finalise_AC "Lib.MonadicRewrite"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

section\<open>Notifications\<close>

subsection\<open>@{term "pas_refined"}\<close>

crunch thread_bound_ntfns[wp]: do_machine_op "\<lambda>s. P (thread_bound_ntfns s)"

crunches deleted_irq_handler, send_signal
  for state_vrefs[wp]: "\<lambda>s. P (state_vrefs (s :: det_ext state))"
  (wp: crunch_wps hoare_unless_wp select_wp dxo_wp_weak simp: crunch_simps)

lemma cancel_ipc_receive_blocked_caps_of_state:
  "\<lbrace>\<lambda>s. P (caps_of_state (s :: det_ext state)) \<and> st_tcb_at receive_blocked t s\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_pre)
  apply (wp gts_wp | wpc | simp)+
     apply (rule hoare_pre_cont)+
  apply (clarsimp simp: st_tcb_def2 receive_blocked_def)
  apply (clarsimp split: thread_state.splits)
  done

lemma send_signal_caps_of_state[wp]:
  "\<lbrace>\<lambda>s :: det_ext state. P (caps_of_state s) \<rbrace> send_signal ntfnptr badge \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (clarsimp simp: send_signal_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp dxo_wp_weak cancel_ipc_receive_blocked_caps_of_state gts_wp static_imp_wp | wpc | simp add: update_waiting_ntfn_def)+
  apply (clarsimp simp: fun_upd_def[symmetric] st_tcb_def2)
  done

crunches deleted_irq_handler, send_signal
  for arch_state[wp]: "\<lambda>s. P (arch_state (s :: det_ext state))"
  (wp: crunch_wps hoare_unless_wp select_wp dxo_wp_weak simp: crunch_simps)

crunch mdb[wp]: blocked_cancel_ipc, update_waiting_ntfn "\<lambda>s. P (cdt (s :: det_ext state))" (wp: crunch_wps hoare_unless_wp select_wp dxo_wp_weak simp: crunch_simps)

lemma cancel_ipc_receive_blocked_mdb:
  "\<lbrace>\<lambda>s. P (cdt (s :: det_ext state)) \<and> st_tcb_at receive_blocked t s\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_pre)
  apply (wp gts_wp | wpc | simp)+
     apply (rule hoare_pre_cont)+
  apply (clarsimp simp: st_tcb_def2 receive_blocked_def)
  apply (clarsimp split: thread_state.splits)
  done

lemma send_signal_mdb[wp]:
  "\<lbrace>\<lambda>s. P (cdt (s :: det_ext state))\<rbrace> send_signal ntfnptr badge \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  apply (clarsimp simp: send_signal_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp dxo_wp_weak gts_wp cancel_ipc_receive_blocked_mdb | wpc | simp)+
  apply (clarsimp simp: st_tcb_def2)
  done

crunches possible_switch_to
  for tcb_domain_map_wellformed[wp]: "tcb_domain_map_wellformed aag"

lemma update_waiting_ntfn_pas_refined:
  "\<lbrace>pas_refined aag and ko_at (Notification ntfn) ntfnptr and K (ntfn_obj ntfn = WaitingNtfn queue)\<rbrace>
     update_waiting_ntfn ntfnptr queue badge val
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  apply (wp set_thread_state_pas_refined set_simple_ko_pas_refined | simp)+
  done

lemma cancel_ipc_receive_blocked_pas_refined:
  "\<lbrace>pas_refined aag and st_tcb_at receive_blocked t\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_pre)
  apply (wp gts_wp | wpc | simp)+
  apply (clarsimp simp: st_tcb_def2 receive_blocked_def)
  done

lemma send_signal_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s\<rbrace> send_signal ntfnptr badge \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: send_signal_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply (wp set_simple_ko_pas_refined update_waiting_ntfn_pas_refined gts_wp set_thread_state_pas_refined
            cancel_ipc_receive_blocked_pas_refined
       | wpc
       | simp)+
  apply clarsimp
  apply (fastforce simp: st_tcb_def2)
  done

lemma receive_signal_pas_refined:
  "\<lbrace>pas_refined aag and K (\<forall>ntfnptr \<in> obj_refs cap. (pasObjectAbs aag thread, Receive, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag)\<rbrace>
     receive_signal thread cap is_blocking
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (cases cap, simp_all)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  by (wp set_simple_ko_pas_refined set_thread_state_pas_refined
       | wpc | simp add: do_nbrecv_failed_transfer_def)+


subsection\<open>integrity\<close>

subsubsection\<open>autarchy\<close>

text\<open>
  For the case when the currently-running thread owns the receiver
  (i.e. receiver last to the notification rendezvous or sender owns
  receiver).
\<close>

lemma st_tcb_at_tcb_states_of_state:
  "(st_tcb_at stf p s) = (\<exists>st. tcb_states_of_state s p = Some st \<and> stf st)"
  unfolding tcb_states_of_state_def st_tcb_def2 by auto

lemma st_tcb_at_tcb_states_of_state_eq:
  "(st_tcb_at ((=) st) p s) = (tcb_states_of_state s p = Some st)"
  unfolding tcb_states_of_state_def st_tcb_def2 by auto

lemma kheap_auth_ipc_buffer_same:
  "kheap st thread = kheap s thread \<Longrightarrow> auth_ipc_buffers st thread = auth_ipc_buffers s thread"
  unfolding auth_ipc_buffers_def get_tcb_def by simp

lemma tcb_ipc_buffer_not_device:
  "\<lbrakk>kheap s thread = Some (TCB tcb);valid_objs s\<rbrakk>
  \<Longrightarrow> \<not> cap_is_device (tcb_ipcframe tcb)"
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def
                 split: cap.split_asm arch_cap.split_asm)
  done

lemma tro_auth_ipc_buffer_idem:
  "\<lbrakk> \<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap st x) (kheap s x);
        pasObjectAbs aag thread \<notin> subjects; valid_objs s \<rbrakk>
   \<Longrightarrow> auth_ipc_buffers st thread = auth_ipc_buffers s thread"
  apply (drule spec [where x = thread])
  by (erule integrity_objE;
      simp add: auth_ipc_buffers_def get_tcb_def;
      fastforce cong: cap.case_cong arch_cap.case_cong if_cong
                simp: case_bool_if
               dest!: tcb_ipc_buffer_not_device split:arch_cap.splits cap.splits
               split: if_splits)


lemma dmo_storeWord_respects_ipc:
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Structures_A.Running) thread and
    K ((\<not> is_subject aag thread \<longrightarrow> st_tcb_at (receive_blocked_on ep) thread st \<and> auth_ipc_buffers st thread = ptr_range buf msg_align_bits) \<and>
      ipc_buffer_has_auth aag thread (Some buf) \<and> p < 2 ^ (msg_align_bits - 2)) \<rbrace>
    do_machine_op (storeWord (buf + of_nat p * of_nat word_size) v)
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (elim conjE)
  apply (cases "is_subject aag thread")
   apply (rule hoare_pre)
   apply (rule dmo_storeWord_respects_Write)
    apply clarsimp
    apply (drule (1) ipc_buffer_has_auth_wordE)
       apply simp
      apply (simp add: msg_align_bits)
     apply (erule mul_word_size_lt_msg_align_bits_ofnat)
    apply simp
   \<comment> \<open>non auth case\<close>
  apply (rule hoare_pre)
  apply (simp add: storeWord_def)
  apply (wp dmo_wp)
  apply clarsimp
  apply (simp add: integrity_def split del: if_split)
  apply (clarsimp split del: if_split)
  apply (case_tac "x \<in> ptr_range (buf + of_nat p * of_nat word_size) 2")
   apply (clarsimp simp add: st_tcb_at_tcb_states_of_state split del: if_split)
   apply (rule trm_ipc [where p' = thread])
      apply simp
     apply assumption
    apply (clarsimp simp: ipc_buffer_has_auth_def)
    apply (erule (1) set_mp [OF ptr_range_subset, rotated -1])
      apply simp
     apply (simp add: msg_align_bits)
    apply (erule mul_word_size_lt_msg_align_bits_ofnat)
   apply simp
  \<comment> \<open>otherwise\<close>
  apply (auto simp: is_aligned_mask [symmetric] intro!: trm_lrefl ptr_range_memI ptr_range_add_memI)
  done

lemma store_word_offs_respects:
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Structures_A.Running) thread and
    K ((\<not> is_subject aag thread \<longrightarrow> st_tcb_at (receive_blocked_on ep) thread st \<and> auth_ipc_buffers st thread = ptr_range buf msg_align_bits) \<and>
      ipc_buffer_has_auth aag thread (Some buf) \<and> p < 2 ^ (msg_align_bits - 2)) \<rbrace>
   store_word_offs buf p v
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: store_word_offs_def)
  apply (rule hoare_pre)
   apply (wp dmo_storeWord_respects_ipc [where thread = thread])
  apply fastforce
  done


lemma ipc_buffer_has_auth_None [simp]:
  "ipc_buffer_has_auth aag receiver None"
  unfolding ipc_buffer_has_auth_def by simp

(* FIXME: MOVE *)
lemma cap_auth_caps_of_state:
  "\<lbrakk> caps_of_state s p = Some cap; pas_refined aag s\<rbrakk>
  \<Longrightarrow> aag_cap_auth aag (pasObjectAbs aag (fst p)) cap"
  unfolding aag_cap_auth_def
  apply (intro conjI)
    apply clarsimp
    apply (drule (2) sta_caps)
    apply (drule auth_graph_map_memI [where x = "pasObjectAbs aag (fst p)", OF _ sym refl])
    apply (rule refl)
    apply (fastforce simp: pas_refined_def)
   apply clarsimp
   apply (drule (2) sta_untyped [THEN pas_refined_mem] )
   apply simp
  apply (drule (1) clas_caps_of_state)
  apply simp
  apply (drule (1) cli_caps_of_state)
  apply simp
  done

lemma lookup_ipc_buffer_has_auth [wp]:
  "\<lbrace>pas_refined aag and valid_objs\<rbrace>
    lookup_ipc_buffer True receiver
   \<lbrace>\<lambda>rv s. ipc_buffer_has_auth aag receiver rv\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: lookup_ipc_buffer_def)
   apply (wp get_cap_wp thread_get_wp'
        | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_auth_def get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (frule (1) caps_of_state_valid_cap)
  apply (rule conjI)
   apply (clarsimp simp: valid_cap_simps cap_aligned_def)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_andI1)
    apply (drule (1) valid_tcb_objs)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def
                   split: if_splits)
   apply (rule order_trans [OF _ pbfs_atleast_pageBits])
   apply (simp add: msg_align_bits pageBits_def)
  apply simp
  apply (drule (1) cap_auth_caps_of_state)
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def vspace_cap_rights_to_auth_def
                        vm_read_write_def is_page_cap_def split: if_split_asm)
  apply (drule bspec)
   apply (erule (3) ipcframe_subset_page)
  apply simp
  done

lemma set_notification_respects:
  "\<lbrace>integrity aag X st and K (aag_has_auth_to aag auth epptr \<and> auth \<in> {Receive, Notify, Reset})\<rbrace>
     set_notification epptr ntfn'
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def partial_inv_def a_type_def)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def tro_ntfn)
  done

lemma receive_signal_integrity_autarch:
  "\<lbrace>integrity aag X st and pas_refined aag and valid_objs
           and K ((\<forall>ntfnptr \<in> obj_refs cap. aag_has_auth_to aag Receive ntfnptr)
                 \<and> is_subject aag thread)\<rbrace>
     receive_signal thread cap is_blocking
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (cases cap, simp_all)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply (wp set_notification_respects[where auth=Receive] set_thread_state_integrity_autarch as_user_integrity_autarch
       | wpc
       | simp add: do_nbrecv_failed_transfer_def)+
  done

subsubsection\<open>Non-autarchy: the sender is running\<close>

lemma send_upd_ctxintegrity:
  "\<lbrakk> direct_send {pasSubject aag} aag ep tcb
      \<or> indirect_send {pasSubject aag} aag (the (tcb_bound_notification tcb)) ep tcb;
     integrity aag X st s; st_tcb_at ((=) Structures_A.thread_state.Running) thread s;
     get_tcb thread st = Some tcb; get_tcb thread s = Some tcb'\<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>kheap :=
                               kheap s(thread \<mapsto> TCB (tcb'\<lparr>tcb_arch :=
                                                           arch_tcb_context_set c' (tcb_arch tcb')
                                                          \<rparr>))
                              \<rparr>)"
 apply (clarsimp simp: integrity_def tcb_states_of_state_preserved st_tcb_def2)
  apply (drule get_tcb_SomeD)+
  apply (drule spec[where x=thread], simp)
  apply (cases "is_subject aag thread")
   apply (rule tro_lrefl, solves\<open>simp\<close>)

  (* slow 5s *)
  by (erule integrity_objE;
      (* eliminate all TCB unrelated cases and simplifies the other *)
      clarsimp;
        (* deal with the orefl case *)
      ( solves\<open>simp add:direct_send_def indirect_send_def\<close>
        (* deal with the other case by applying either the reply, call or send rules and then
           the generic rule *)
      | rule tro_trans_spec,
        (rule tro_tcb_reply'[OF refl refl refl] tro_tcb_call[OF refl refl refl]
              tro_tcb_send[OF refl refl refl];
          blast),
        rule tro_trans_spec,
        (rule tro_tcb_generic'[OF refl refl refl]; simp),
        rule tro_orefl, simp, rule tcb.equality; solves\<open>simp add:arch_tcb_context_set_def\<close>))

lemma set_mrs_respects_in_signalling':
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Structures_A.Running) thread and
    K ((\<not> is_subject aag thread \<longrightarrow> st_tcb_at (receive_blocked_on ep) thread st
        \<and> case_option True (\<lambda>buf'. auth_ipc_buffers st thread = ptr_range buf' msg_align_bits) buf)
        \<and> aag_has_auth_to aag Notify ep \<and> ipc_buffer_has_auth aag thread buf) \<rbrace>
     set_mrs thread buf msgs
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wp gets_the_wp get_wp put_wp
       | wpc
       | simp split del: if_split
                    add: zipWithM_x_mapM_x split_def store_word_offs_def fun_upd_def[symmetric])+
     apply (rule hoare_post_imp [where Q = "\<lambda>rv. st_tcb_at ((=) Structures_A.Running) thread and integrity aag X st"])
      apply simp
     apply (wp mapM_x_wp' dmo_storeWord_respects_ipc [where thread = thread and ep = ep])
     apply (fastforce simp add: set_zip nth_append simp: msg_align_bits msg_max_length_def
                         split: if_split_asm)
    apply wp+
  apply (rule impI)
  apply (subgoal_tac "\<forall>c'. integrity aag X st
          (s\<lparr>kheap := kheap s(thread \<mapsto>
               TCB ((the (get_tcb thread s))\<lparr>tcb_arch :=  arch_tcb_set_registers c' (tcb_arch (the (get_tcb thread s))) \<rparr>))\<rparr>)")
   apply (clarsimp simp: fun_upd_def st_tcb_at_nostate_upd [unfolded fun_upd_def])
  apply (rule allI)
  apply clarsimp
  apply (cases "is_subject aag thread")
   apply (erule (1) integrity_update_autarch)
  apply (clarsimp simp: st_tcb_def2 arch_tcb_set_registers_def)
  apply (rule send_upd_ctxintegrity[OF disjI1], auto simp: st_tcb_def2 direct_send_def)
  done

lemma as_user_set_register_respects:
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Structures_A.Running) thread and
    K ((\<not> is_subject aag thread \<longrightarrow> st_tcb_at (receive_blocked_on ep) thread st) \<and> (aag_has_auth_to aag SyncSend ep \<or> aag_has_auth_to aag Notify ep)) \<rbrace>
   as_user thread (set_register r v)
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: as_user_def split_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: in_monad setRegister_def)
  apply (cases "is_subject aag thread")
   apply (erule (1) integrity_update_autarch [unfolded fun_upd_def])
  apply (clarsimp simp: st_tcb_def2)
  apply (rule send_upd_ctxintegrity [OF disjI1, unfolded fun_upd_def])
      apply (auto simp: direct_send_def st_tcb_def2)
  done

lemma lookup_ipc_buffer_ptr_range:
  "\<lbrace>valid_objs and integrity aag X st\<rbrace>
  lookup_ipc_buffer True thread
  \<lbrace>\<lambda>rv s. \<not> is_subject aag thread \<longrightarrow> (case rv of None \<Rightarrow> True | Some buf' \<Rightarrow> auth_ipc_buffers st thread = ptr_range buf' msg_align_bits) \<rbrace>"
  unfolding lookup_ipc_buffer_def
  apply (rule hoare_pre)
  apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_auth_def get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (clarsimp simp: auth_ipc_buffers_def get_tcb_ko_at [symmetric] integrity_def)
  apply (drule spec [where x = thread])+
  apply (drule get_tcb_SomeD)+
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def case_bool_if
                 split: if_split_asm)
  apply (erule integrity_objE, simp_all add: get_tcb_def vm_read_write_def)
  apply auto
  done

lemma set_thread_state_respects_in_signalling:
  "\<lbrace>integrity aag X st
             and (\<lambda>s. \<not> is_subject aag thread \<longrightarrow> st_tcb_at (receive_blocked_on ntfnptr) thread s)
             and K (aag_has_auth_to aag Notify ntfnptr)\<rbrace>
     set_thread_state thread Structures_A.thread_state.Running
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply wp
  apply (clarsimp)
  apply (cases "is_subject aag thread")
   apply (erule(1) integrity_update_autarch [unfolded fun_upd_def])
  apply (erule integrity_trans)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: integrity_def st_tcb_def2)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (rule tro_tcb_send [OF refl refl])
  apply (rule tcb.equality;simp; rule arch_tcb_context_set_eq[symmetric])
  apply (auto simp: indirect_send_def direct_send_def)
  done

lemma set_notification_obj_at:
  "\<lbrace>obj_at P ptr and K (ptr \<noteq> ntfnptr)\<rbrace>
     set_notification ntfnptr queue
   \<lbrace>\<lambda>rv. obj_at P ptr\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (auto simp: obj_at_def)
  done

lemma set_ntfn_valid_objs_at:
  "\<lbrace>valid_objs and (\<lambda>s. ntfn_at p s \<longrightarrow> valid_ntfn ntfn s)\<rbrace> set_notification p ntfn \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  unfolding set_simple_ko_def
  apply (rule hoare_pre)
  apply (wp set_object_valid_objs get_object_wp)
  apply (clarsimp simp: valid_obj_def obj_at_def is_ntfn partial_inv_def
              split: Structures_A.kernel_object.splits)
  done

lemma drop_Suc0_iff:
  "xs \<noteq> [] \<Longrightarrow> (drop (Suc 0) xs = ys) = (\<exists>x. xs = x # ys)"
  by (auto simp: neq_Nil_conv)

lemma receive_blocked_on_def3:
  "receive_blocked_on ref ts =
     ((\<exists>pl. ts = Structures_A.BlockedOnReceive ref pl)
      \<or> ts = Structures_A.BlockedOnNotification ref)"
  by (cases ts, auto)


lemma integrity_receive_blocked_chain:
  "\<lbrakk> st_tcb_at (receive_blocked_on ep) p s; integrity aag X st s; \<not> is_subject aag p \<rbrakk> \<Longrightarrow> st_tcb_at (receive_blocked_on ep) p st"
  apply (clarsimp simp: integrity_def st_tcb_at_tcb_states_of_state)
  apply (drule (1) tsos_tro [where p = p] )
    apply (fastforce simp: tcb_states_of_state_def)
   apply simp
  apply simp
  done

crunch integrity[wp]: possible_switch_to "integrity aag X st"
  (ignore: tcb_sched_action)

abbreviation
  "integrity_once_ts_upd t ts aag X st s
    == integrity aag X st (s \<lparr> kheap := (kheap s) ( t := Some (TCB ((the (get_tcb t s)) \<lparr>tcb_state := ts\<rparr>)))\<rparr>)"

lemma set_scheduler_action_integrity_once_ts_upd:
  "\<lbrace>integrity_once_ts_upd t ts aag X st\<rbrace>
    set_scheduler_action sa \<lbrace>\<lambda>_. integrity_once_ts_upd t ts aag X st\<rbrace>"
  apply (simp add: set_scheduler_action_def, wp)
  apply clarsimp
  apply (erule rsubst[where P="\<lambda>x. x"])
  apply (rule trans, rule_tac f="\<lambda>x. sa" in eintegrity_sa_update[symmetric])
  apply (rule arg_cong[where f="integrity aag X st"])
  apply (simp add: get_tcb_def)
  done

crunch integrity_once_ts_upd: set_thread_state_ext "integrity_once_ts_upd t ts aag X st"

lemma set_thread_state_integrity_once_ts_upd:
  "\<lbrace>integrity_once_ts_upd t ts aag X st\<rbrace>
    set_thread_state t ts' \<lbrace>\<lambda>_. integrity_once_ts_upd t ts aag X st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp set_thread_state_ext_integrity_once_ts_upd)
  apply (clarsimp simp: fun_upd_def dest!: get_tcb_SomeD)
  apply (simp add: get_tcb_def cong: if_cong)
  done

lemma get_tcb_recv_blocked_implies_receive:
  "\<lbrakk>pas_refined aag s; get_tcb t s = Some tcb; ep_recv_blocked ep (tcb_state tcb) \<rbrakk>
          \<Longrightarrow> (pasObjectAbs aag t, Receive, pasObjectAbs aag ep) \<in> pasPolicy aag"
  apply (erule pas_refined_mem[rotated])
  apply (rule sta_ts)
  apply (simp add: thread_states_def tcb_states_of_state_def)
  apply (case_tac "tcb_state tcb", simp_all)
  done

lemma cancel_ipc_receive_blocked_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and st_tcb_at (receive_blocked) t and
       (sym_refs o state_refs_of) and
       bound_tcb_at (\<lambda>ntfn. ntfn = Some ntfnptr) t and
       K ((pasObjectAbs aag t, Receive, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag \<and>
             (pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag)\<rbrace>
    cancel_ipc t \<lbrace>\<lambda>_. integrity_once_ts_upd t Running aag X st\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_name_pre_state)
  apply (subgoal_tac "case state of BlockedOnReceive x y \<Rightarrow> True | _ \<Rightarrow> False")
   apply (simp add: blocked_cancel_ipc_def bind_assoc set_simple_ko_def set_object_def
                    get_ep_queue_def get_blocking_object_def
             split: thread_state.splits)
   apply (rule hoare_pre)
    apply (wp set_thread_state_integrity_once_ts_upd get_object_wp get_simple_ko_wp
          | wpc)+
   apply (clarsimp simp: st_tcb_at_def2 obj_at_def)
   apply (rename_tac ep payload s tcb ntfn)
   apply (drule_tac t="tcb_state tcb" in sym)
   apply (subgoal_tac "st_tcb_at ((=) (tcb_state tcb)) t s")
    apply (drule(1) sym_refs_st_tcb_atD)
    apply (clarsimp simp: obj_at_def ep_q_refs_of_def fun_upd_def get_tcb_def
                   split: endpoint.splits cong: if_cong)
    apply (intro impI conjI, simp_all)[1]
    apply (erule integrity_trans)
    apply (simp add: integrity_def)
    apply (intro impI conjI allI)
     apply clarsimp
     apply (rule tro_ep_unblock; simp?)
     apply (erule get_tcb_recv_blocked_implies_receive, erule get_tcb_rev; solves\<open>simp\<close>)
    apply (rule_tac ep=ep in tro_tcb_send[OF refl refl];
           fastforce intro!: tcb.equality arch_tcb_context_set_eq[symmetric]
                       simp: indirect_send_def pred_tcb_at_def obj_at_def)
   apply (fastforce simp: indirect_send_def pred_tcb_at_def obj_at_def)
  apply (fastforce simp: pred_tcb_at_def obj_at_def receive_blocked_def)
  done

lemma set_thread_state_integrity':
  "\<lbrace>integrity_once_ts_upd t ts aag X st\<rbrace> set_thread_state t ts \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def)
  by (wpsimp wp: set_object_wp)

lemma as_user_set_register_respects_indirect:
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Structures_A.Running) thread and
    K ((\<not> is_subject aag thread \<longrightarrow> st_tcb_at receive_blocked thread st
           \<and> bound_tcb_at ((=) (Some ntfnptr)) thread st)
        \<and> (aag_has_auth_to aag Notify ntfnptr)) \<rbrace>
   as_user thread (set_register r v)
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: as_user_def split_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: in_monad setRegister_def)
  apply (cases "is_subject aag thread")
   apply (erule (1) integrity_update_autarch [unfolded fun_upd_def])
  apply (clarsimp simp: st_tcb_def2 receive_blocked_def)
  apply (simp split: thread_state.split_asm)
  apply (rule send_upd_ctxintegrity [OF disjI2, unfolded fun_upd_def],
         auto simp: st_tcb_def2 indirect_send_def pred_tcb_def2 dest: sym)
  done

lemma integrity_receive_blocked_chain':
  "\<lbrakk> st_tcb_at receive_blocked p s; integrity aag X st s; \<not> is_subject aag p \<rbrakk> \<Longrightarrow> st_tcb_at receive_blocked p st"
  apply (clarsimp simp: integrity_def st_tcb_at_tcb_states_of_state receive_blocked_def)
  apply (simp split: thread_state.split_asm)
  apply (rename_tac word pl)
  apply (drule_tac ep=word in tsos_tro [where p = p], simp+ )
  done

lemma tba_Some:
  "thread_bound_ntfns s t = Some a \<Longrightarrow> bound_tcb_at ((=) (Some a)) t s"
  by (clarsimp simp: thread_bound_ntfns_def pred_tcb_at_def obj_at_def get_tcb_def
              split: option.splits kernel_object.splits)


lemma tsos_tro':
  "\<lbrakk>\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x);
    thread_bound_ntfns s' p = Some a; pasObjectAbs aag p \<notin> subjects \<rbrakk>
   \<Longrightarrow> thread_bound_ntfns s p = Some a"
  apply (drule_tac x=p in spec)
  apply (erule integrity_objE;
         simp?;
         fastforce simp: thread_bound_ntfns_def get_tcb_def
                         tcb_bound_notification_reset_integrity_def)
  done

lemma integrity_receive_blocked_chain_bound:
  "\<lbrakk>bound_tcb_at ((=) (Some ntfnptr)) p s; integrity aag X st s; \<not> is_subject aag p\<rbrakk>
   \<Longrightarrow> bound_tcb_at ((=) (Some ntfnptr)) p st"
  apply (clarsimp simp: integrity_def)
  apply (drule bound_tcb_at_thread_bound_ntfns)
  apply (drule tsos_tro' [where p = p], simp+ )
  apply (clarsimp simp:tba_Some)
  done

lemma send_signal_respects:
  "\<lbrace>integrity aag X st and pas_refined aag
         and valid_objs
         and sym_refs \<circ> state_refs_of
         and K (aag_has_auth_to aag Notify ntfnptr)\<rbrace>
     send_signal ntfnptr badge
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: send_signal_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_name_pre_state)
  apply (case_tac "ntfn_obj ntfn = IdleNtfn \<and> ntfn_bound_tcb ntfn \<noteq> None")
   \<comment> \<open>ntfn-binding case\<close>
   apply (rule hoare_pre)
    apply (wp set_notification_respects[where auth=Notify]
                 as_user_set_register_respects_indirect[where ntfnptr=ntfnptr]
                 set_thread_state_integrity' sts_st_tcb_at' static_imp_wp
                 cancel_ipc_receive_blocked_respects[where ntfnptr=ntfnptr]
                 gts_wp
               | wpc | simp)+
   apply (clarsimp, rule conjI, clarsimp simp: st_tcb_def2)
   apply (clarsimp simp: receive_blocked_def)
   apply (simp split: thread_state.split_asm)
   apply (clarsimp simp: obj_at_def)
   apply (drule (3) ntfn_bound_tcb_at[where ntfnptr=ntfnptr and P="\<lambda>ntfn. ntfn = Some ntfnptr"], simp+)[1]
   apply (rule conjI)
    apply (drule_tac x=ntfnptr and t=y in bound_tcb_at_implies_receive)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def, simp)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac s=sa in integrity_receive_blocked_chain')
      apply (clarsimp simp add: pred_tcb_at_def obj_at_def receive_blocked_def)
      apply (fastforce split: thread_state.split)
     apply simp+
   apply (rule_tac s=sa in integrity_receive_blocked_chain_bound)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def)
    apply simp+
  apply (rule hoare_pre)
   apply clarsimp
   apply (wpc, clarsimp)
     apply (wp set_notification_respects[where auth=Notify]
               sts_st_tcb_at' as_user_set_register_respects
               set_thread_state_pas_refined set_simple_ko_pas_refined
               set_thread_state_respects_in_signalling [where ntfnptr = ntfnptr]
               set_ntfn_valid_objs_at hoare_vcg_disj_lift static_imp_wp
          | wpc
          | simp add: update_waiting_ntfn_def)+
  apply clarsimp
  apply (subgoal_tac "st_tcb_at (receive_blocked_on ntfnptr) (hd x) sa")
   prefer 2
   apply (rule ntfn_queued_st_tcb_at', assumption)
      apply (fastforce simp: obj_at_def valid_obj_def valid_ntfn_def)
     apply assumption+
   apply simp
  apply simp
  apply (intro impI conjI)
     \<comment> \<open>st_tcb_at receive_blocked st\<close>
   apply (erule (2) integrity_receive_blocked_chain)
  apply clarsimp
  done

section\<open>Sync IPC\<close>

text\<open>

When transferring caps, i.e. when the grant argument is true on the
IPC operations, the currently-running thread owns the receiver. Either
it is the receiver (and ?thesis by well-formedness) or it is the
sender, and that can send arbitrary caps, hence ?thesis by sbta_ipc
etc.

\<close>

subsection\<open>auxiliary\<close>


lemma cap_master_cap_masked_as_full:
  "cap_master_cap (masked_as_full a a) = cap_master_cap a "
  apply(clarsimp simp: cap_master_cap_def split: cap.splits simp: masked_as_full_def)
  done

lemma cap_badge_masked_as_full:
  "(cap_badge (masked_as_full a a), cap_badge a) \<in> capBadge_ordering False"
  apply(case_tac a, simp_all add: masked_as_full_def)
  done



lemma masked_as_full_double:
  "masked_as_full (masked_as_full ab ab) cap' = masked_as_full ab ab"
  apply(case_tac ab, simp_all add: masked_as_full_def)
  done

lemma transfer_caps_loop_pres_dest_aux:
  assumes x: "\<And>cap src dest.
              \<lbrace>\<lambda>s. P s \<and> dest \<in> slots' \<and> src \<in> snd ` caps'
                                   \<and> (valid_objs s \<and> real_cte_at dest s \<and> s \<turnstile> cap \<and> tcb_cap_valid cap dest s
                                   \<and> real_cte_at src s
                                   \<and> cte_wp_at (is_derived (cdt s) src cap) src s \<and> cap \<noteq> cap.NullCap) \<rbrace>
                 cap_insert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n'. n' \<le> N \<Longrightarrow> \<lbrace>P\<rbrace> set_extra_badge buffer b n' \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "n + length caps \<le> N \<Longrightarrow>
                 \<lbrace>\<lambda>s. P s \<and> set slots \<subseteq> slots' \<and> set caps \<subseteq> caps' \<and>
                     (valid_objs s \<and> valid_mdb s \<and> distinct slots \<and>
                     (\<forall>x \<in> set slots. real_cte_at x s) \<and>
                     (\<forall>x \<in> set caps. s \<turnstile> fst x \<and>
                                     cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp \<noteq> fst x \<longrightarrow> cp = masked_as_full (fst x) (fst x)) (snd x) s
                                           \<and> real_cte_at (snd x) s))\<rbrace>
                  transfer_caps_loop ep buffer n caps slots mi
              \<lbrace>\<lambda>rv. P\<rbrace>" (is "?L \<Longrightarrow> ?P n caps slots mi")
proof (induct caps arbitrary: slots n mi)
  case Nil
  thus ?case by (simp, wp, simp)
next
  case (Cons m ms)
  hence nN: "n \<le> N" by simp

  from Cons have "\<And>slots mi. ?P (n + 1) ms slots mi" by clarsimp
  thus ?case
    apply (cases m)
    apply (clarsimp simp add: Let_def split_def whenE_def
                    cong: if_cong list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp eb [OF nN] hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
           | assumption | simp split del: if_split)+

      apply (rule cap_insert_assume_null)
      apply (wp x hoare_vcg_const_Ball_lift cap_insert_cte_wp_at)+
      (* cannot blindly use derive_cap_is_derived_foo here , need to first hoist
         out of the postcondition the conjunct that the return value is derived,
         and solve this using derived_cap_is_derived, and then solve the rest
         using derive_cap_is_derived_foo *)
    apply (rule_tac Q'="\<lambda>r s. S r s \<and> Q r s" for S Q in hoare_post_imp_R)
     apply (rule hoare_vcg_conj_lift_R)
      apply (rule derive_cap_is_derived)
     prefer 2
     apply clarsimp
     apply assumption
    apply(wp derive_cap_is_derived_foo)+
  apply (simp only: tl_drop_1[symmetric])
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        ex_cte_cap_to_cnode_always_appropriate_strg
                        real_cte_tcb_valid caps_of_state_valid
             split del: if_split)
  apply (clarsimp simp: remove_rights_def caps_of_state_valid
                        neq_Nil_conv cte_wp_at_caps_of_state
                        imp_conjR[symmetric] cap_master_cap_masked_as_full
                        cap_badge_masked_as_full
                 split del: if_split)
  apply(intro conjI)
   apply clarsimp
   apply (case_tac "cap = a",clarsimp simp: remove_rights_def)
   apply (clarsimp simp:masked_as_full_def is_cap_simps)
   apply (clarsimp simp: cap_master_cap_simps remove_rights_def split:if_splits)
  apply clarsimp
  apply (intro conjI)
    apply (clarsimp split:if_splits elim!: image_eqI[rotated])
   apply (clarsimp split:if_splits simp: remove_rights_def)
  apply (rule ballI)
  apply (drule(1) bspec)
  apply clarsimp
  apply (intro conjI)
   apply clarsimp
  apply clarsimp
   apply (case_tac "capa = ab",clarsimp simp: masked_as_full_def is_cap_simps split: if_splits)
  apply (clarsimp simp: masked_as_full_double)
  done
qed


(* FIXME: move *)
lemma transfer_caps_loop_pres_dest:
  assumes x: "\<And>cap src dest.
              \<lbrace>\<lambda>s. P s \<and> dest \<in> set slots \<and> src \<in> snd ` set caps
                                   \<and> (valid_objs s \<and> real_cte_at dest s \<and> s \<turnstile> cap \<and> tcb_cap_valid cap dest s
                                   \<and> real_cte_at src s
                                   \<and> cte_wp_at (is_derived (cdt s) src cap) src s \<and> cap \<noteq> cap.NullCap) \<rbrace>
                 cap_insert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n'. n' \<le> n + length caps \<Longrightarrow> \<lbrace>P\<rbrace> set_extra_badge buffer b n' \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s \<and> (valid_objs s \<and> valid_mdb s \<and> distinct slots \<and>
                                 (\<forall>x \<in> set slots. real_cte_at x s) \<and>
                                 (\<forall>x \<in> set caps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp \<noteq> fst x \<longrightarrow> cp = masked_as_full (fst x) (fst x)) (snd x) s
                                           \<and> real_cte_at (snd x) s))\<rbrace>
                  transfer_caps_loop ep buffer n caps slots mi
              \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
  apply (rule transfer_caps_loop_pres_dest_aux [OF x eb])
  apply assumption
  apply simp
  apply simp
  done

subsection\<open>pas_refined\<close>

lemma lookup_slot_for_thread_authorised:
  "\<lbrace>pas_refined aag and K (is_subject aag thread)\<rbrace>
    lookup_slot_for_thread thread cref
   \<lbrace>\<lambda>rv s. is_subject aag (fst (fst rv))\<rbrace>,-"
  unfolding lookup_slot_for_thread_def
  apply wp
  apply (clarsimp simp: owns_thread_owns_cspace)
  done

lemma cnode_cap_all_auth_owns:
  "(\<exists>s. is_cnode_cap cap \<and> (\<forall>x\<in>obj_refs cap.
          \<forall>auth\<in>cap_auth_conferred cap. aag_has_auth_to aag auth x)
            \<and> pas_refined aag s)
          \<longrightarrow> (\<forall>x\<in>obj_refs cap. is_subject aag x)"
  apply (clarsimp simp: is_cap_simps)
  apply (clarsimp simp: cap_auth_conferred_def pas_refined_all_auth_is_owns)
  done

lemma get_receive_slots_authorised:
  "\<lbrace>pas_refined aag and K (\<forall>rbuf. recv_buf = Some rbuf \<longrightarrow> is_subject aag receiver)\<rbrace>
     get_receive_slots receiver recv_buf
  \<lbrace>\<lambda>rv s. \<forall>slot \<in> set rv. is_subject aag (fst slot)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases recv_buf)
   apply (simp, wp, simp)
  apply clarsimp
  apply (wp get_cap_auth_wp[where aag=aag] lookup_slot_for_thread_authorised
       | rule hoare_drop_imps
       | simp add: add: lookup_cap_def split_def)+
   apply (strengthen cnode_cap_all_auth_owns, simp add: aag_cap_auth_def)
   apply (wp hoare_vcg_all_lift_R hoare_drop_imps)+
  apply clarsimp
  apply (fastforce simp: is_cap_simps)
  done

crunch pas_refined[wp]: set_extra_badge "pas_refined aag"

lemma remove_rights_clas [simp]:
  "cap_links_asid_slot aag p (remove_rights R cap) = cap_links_asid_slot aag p cap"
  unfolding cap_links_asid_slot_def remove_rights_def cap_rights_update_def acap_rights_update_def
  by (clarsimp split: cap.splits arch_cap.splits bool.splits)

lemma remove_rights_cap_auth_conferred_subset:
  "x \<in> cap_auth_conferred (remove_rights R cap) \<Longrightarrow> x \<in> cap_auth_conferred cap"
  unfolding remove_rights_def cap_rights_update_def
  apply (clarsimp split: if_split_asm cap.splits arch_cap.splits bool.splits
    simp: cap_auth_conferred_def vspace_cap_rights_to_auth_def acap_rights_update_def
          validate_vm_rights_def vm_read_only_def vm_kernel_only_def)
  apply (erule set_mp [OF cap_rights_to_auth_mono, rotated], clarsimp)+
  apply (auto simp: is_page_cap_def cap_rights_to_auth_def reply_cap_rights_to_auth_def split:if_splits)
  done

lemma remove_rights_cli [simp]:
  "cap_links_irq aag l (remove_rights R cap) = cap_links_irq aag l cap"
  unfolding remove_rights_def cap_rights_update_def
  by (clarsimp split: cap.splits arch_cap.splits bool.splits simp: cap_links_irq_def)

lemma remove_rights_untyped_range [simp]:
  "untyped_range (remove_rights R c) = untyped_range c"
  unfolding remove_rights_def cap_rights_update_def
  by (clarsimp split: cap.splits arch_cap.splits bool.splits simp: )

lemma obj_refs_remove_rights [simp]:
  "obj_refs (remove_rights rs cap) = obj_refs cap"
  unfolding remove_rights_def
  by (cases cap, simp_all add: cap_rights_update_def acap_rights_update_def split: arch_cap.splits bool.splits)

lemma remove_rights_cur_auth:
  "pas_cap_cur_auth aag cap \<Longrightarrow> pas_cap_cur_auth aag (remove_rights R cap)"
  unfolding aag_cap_auth_def
  by (clarsimp dest!: remove_rights_cap_auth_conferred_subset)

(* FIXME MOVE *)
lemmas hoare_gen_asmE2 = hoare_gen_asmE[where P'=\<top>,simplified pred_and_true_var]


lemma derive_cap_is_transferable:
  "\<lbrace>K(is_transferable_cap cap) \<rbrace> derive_cap slot cap \<lbrace>\<lambda>r s. is_transferable_cap r\<rbrace>, -"
  apply (rule hoare_gen_asmE2)
  by (erule is_transferable_capE; wpsimp simp: derive_cap_def)

lemma auth_derived_refl[simp]:
  " auth_derived cap cap"
  by (simp add:auth_derived_def)

lemma derive_cap_auth_derived:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv _. rv \<noteq> NullCap \<longrightarrow> auth_derived rv cap \<rbrace>,-"
  apply (cases cap ; (wpsimp simp:derive_cap_def)?)
  apply (case_tac x12 ;
         simp add:derive_cap_def arch_derive_cap_def;
         wpc?;
         wp?;
         simp add:auth_derived_def cap_auth_conferred_def)
  done

(* FIXME MOVE *)
lemma auth_derived_pas_cur_auth:
  "auth_derived cap cap' \<Longrightarrow> pas_cap_cur_auth aag cap' \<Longrightarrow> pas_cap_cur_auth aag cap"
  by (force simp:aag_cap_auth_def auth_derived_def cap_links_asid_slot_def cap_links_irq_def)

lemma derive_cap_is_derived_foo':
  "\<lbrace>\<lambda>s. \<forall>cap'. (cte_wp_at (\<lambda>capa.
                 cap_master_cap capa = cap_master_cap cap \<and>
                 (cap_badge capa, cap_badge cap) \<in> capBadge_ordering False \<and>
                 cap_asid capa = cap_asid cap \<and> vs_cap_ref capa = vs_cap_ref cap)
      slot s \<and> valid_objs s \<and> cap' \<noteq> NullCap
          \<longrightarrow> cte_at slot s )
            \<and> (s \<turnstile> cap \<longrightarrow> s \<turnstile> cap')
            \<and> (cap' \<noteq> NullCap \<longrightarrow> auth_derived cap' cap \<and> cap \<noteq> NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> IRQControlCap)
          \<longrightarrow> Q cap' s \<rbrace>
      derive_cap slot cap \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp add: validE_R_def validE_def valid_def
                     split: sum.splits)
  apply (frule in_inv_by_hoareD[OF derive_cap_inv], clarsimp)
  apply (erule allE)
  apply (erule impEM)
   apply (frule use_validE_R[OF _ cap_derive_not_null_helper, OF _ _ imp_refl])
    apply (rule derive_cap_inv[THEN valid_validE_R])
    apply (intro conjI)
     apply (clarsimp simp:cte_wp_at_caps_of_state)+
     apply (erule(1) use_validE_R[OF _ derive_cap_valid_cap])
    apply simp
    apply (erule use_validE_R[OF _ derive_cap_auth_derived],simp)
  apply simp
  done

(* FIXME: cleanup *)
lemma transfer_caps_loop_presM_extended:
  fixes P vo em ex buffer slots caps n mi
  assumes x: "\<And>cap src dest.
              \<lbrace>\<lambda>s::('state_ext :: state_ext) state .
                               P s \<and> (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> real_cte_at dest s \<and>
                                             s \<turnstile> cap \<and> Psrc src \<and> Pdest dest \<and> Pcap cap \<and>
                                             tcb_cap_valid cap dest s
                                   \<and> real_cte_at src s
                                   \<and> cte_wp_at (is_derived (cdt s) src cap) src s \<and>
                                                cap \<noteq> cap.NullCap)
                       \<and> (em \<longrightarrow> cte_wp_at ((=) cap.NullCap) dest s)
                       \<and> (ex \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) dest s)\<rbrace>
                 cap_insert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  assumes pcap_auth_derived :
    "\<And>cap cap'. \<lbrakk>auth_derived cap cap'; Pcap cap'\<rbrakk> \<Longrightarrow> Pcap cap"
  shows "\<lbrace>\<lambda>s. P s \<and>
             (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> distinct slots \<and>
                     (\<forall>x \<in> set slots. cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s \<and>
                                             real_cte_at x s \<and> Pdest x) \<and>
                     (\<forall>x \<in> set caps. valid_cap (fst x) s \<and> Psrc (snd x) \<and> Pcap (fst x) \<and>
                                     cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp \<noteq> fst x
                                                     \<longrightarrow> cp = masked_as_full (fst x) (fst x)) (snd x) s
                     \<and> real_cte_at (snd x) s))
             \<and> (ex \<longrightarrow> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s))\<rbrace>
          transfer_caps_loop ep buffer n caps slots mi
        \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (clarsimp simp add: Let_def split_def whenE_def
                      cong: if_cong list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp eb hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift static_imp_wp
           | assumption | simp split del: if_split)+
      apply (rule cap_insert_assume_null)
      apply (wp x hoare_vcg_const_Ball_lift cap_insert_cte_wp_at static_imp_wp)+
    apply (rule hoare_vcg_conj_liftE_R)
     apply (rule derive_cap_is_derived_foo')
    apply (rule_tac Q' ="\<lambda>cap' s. (vo \<longrightarrow> cap'\<noteq> cap.NullCap \<longrightarrow>
                            cte_wp_at (is_derived (cdt s) (aa, b) cap') (aa, b) s)
                            \<and> (cap'\<noteq> cap.NullCap \<longrightarrow> QM s cap')" for QM
                    in hoare_post_imp_R)
     prefer 2
     apply clarsimp
     apply assumption
    apply (rule hoare_vcg_conj_liftE_R)
     apply (rule hoare_vcg_const_imp_lift_R)
     apply (rule derive_cap_is_derived)
    apply (wp derive_cap_is_derived_foo')+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        ex_cte_cap_to_cnode_always_appropriate_strg
                        real_cte_tcb_valid caps_of_state_valid
             split del: if_split)
  apply (clarsimp simp: remove_rights_def caps_of_state_valid
                        neq_Nil_conv cte_wp_at_caps_of_state
                        imp_conjR[symmetric] conj_comms
             split del: if_split)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac "cap = a",clarsimp)
   apply (clarsimp simp:masked_as_full_def is_cap_simps)
   apply (fastforce simp: cap_master_cap_simps split: if_splits)
  apply (clarsimp split del: if_split)
  apply (intro conjI)
     apply (fastforce split: if_split elim!: pcap_auth_derived)
    apply (fastforce)
   apply (clarsimp)
  apply (rule ballI)
  apply (drule(1) bspec)
  apply clarsimp
  apply (intro conjI)
   apply (case_tac "capa = ac",clarsimp+)
  apply (case_tac "capa = ac")
  by (clarsimp simp: masked_as_full_def is_cap_simps split: if_splits)+

lemma transfer_caps_loop_pas_refined:
  "\<lbrace>pas_refined aag and valid_objs and valid_mdb
            and (\<lambda>s. (\<forall>x \<in> set caps. valid_cap (fst x) s \<and>
                                      cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                     \<and> real_cte_at (snd x) s) \<and>
                     (\<forall>x\<in>set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = NullCap) x s))
            and K ((\<forall>slot \<in> set slots. is_subject aag (fst slot)) \<and>
                   (\<forall>x \<in> set caps. is_subject aag (fst (snd x)) \<and>
                   pas_cap_cur_auth aag (fst x)) \<and> distinct slots)\<rbrace>
    transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_pre)
  apply (rule transfer_caps_loop_presM_extended
              [where vo=True and em=True and ex=False and
                     Psrc="\<lambda>slot . is_subject aag (fst slot)" and
                     Pcap="pas_cap_cur_auth aag" and
                     Pdest="\<lambda>slot . is_subject aag (fst slot)"])
  apply (wp cap_insert_pas_refined)
     apply (fastforce simp: cte_wp_at_caps_of_state elim!: is_derived_is_transferable)
    apply (rule set_extra_badge_pas_refined)
   apply (erule(1) auth_derived_pas_cur_auth)
  apply (fastforce elim: cte_wp_at_weakenE)
  done


lemma transfer_caps_pas_refined:
  "\<lbrace>pas_refined aag and valid_objs and valid_mdb
    and (\<lambda>s. (\<forall>x \<in> set caps. valid_cap (fst x) s \<and> valid_cap (fst x) s \<and>
                                      cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                     \<and> real_cte_at (snd x) s))
    and K (is_subject aag receiver \<and> (\<forall>x \<in> set caps. is_subject aag (fst (snd x))) \<and> (\<forall>x \<in> set caps. pas_cap_cur_auth aag (fst x))) \<rbrace>
     transfer_caps info caps endpoint receiver recv_buf
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  unfolding transfer_caps_def
  apply (rule hoare_pre)
  by (wp transfer_caps_loop_pas_refined get_receive_slots_authorised get_recv_slot_inv
         hoare_vcg_const_imp_lift hoare_vcg_all_lift grs_distinct
     | wpc | simp del: get_receive_slots.simps add: ball_conj_distrib)+



crunch pas_refined[wp]: copy_mrs "pas_refined aag"
  (wp: crunch_wps)

lemma lookup_cap_and_slot_authorised:
  "\<lbrace>pas_refined aag and K (is_subject aag thread)\<rbrace>
     lookup_cap_and_slot thread xs
   \<lbrace>\<lambda>rv s. is_subject aag (fst (snd rv))\<rbrace>, -"
  unfolding lookup_cap_and_slot_def
  apply (rule hoare_pre)
   apply (wp lookup_slot_for_thread_authorised
        | simp add: split_def)+
  done

lemma lookup_extra_caps_authorised:
  "\<lbrace>pas_refined aag and K (is_subject aag thread)\<rbrace>
    lookup_extra_caps thread buffer mi
   \<lbrace>\<lambda>rv s. \<forall>cap \<in> set rv. is_subject aag (fst (snd cap))\<rbrace>, -"
  apply (simp add: lookup_extra_caps_def)
  apply (wp mapME_set lookup_cap_and_slot_authorised
       | simp)+
  done

lemma lookup_cap_and_slot_cur_auth:
   "\<lbrace>pas_refined aag and K (is_subject aag thread)\<rbrace>
     lookup_cap_and_slot thread xs
   \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag (fst rv)\<rbrace>, -"
  unfolding lookup_cap_and_slot_def
  apply (rule hoare_pre)
   apply (wp get_cap_auth_wp [where aag = aag] lookup_slot_for_thread_authorised
        | simp add: split_def)+
  done

lemma lookup_extra_caps_auth:
  "\<lbrace>pas_refined aag and K (is_subject aag thread)\<rbrace>
    lookup_extra_caps thread buffer mi
   \<lbrace>\<lambda>rv s. \<forall>cap \<in> set rv. pas_cap_cur_auth aag (fst cap)\<rbrace>, -"
  apply (simp add: lookup_extra_caps_def)
  apply (wp mapME_set lookup_cap_and_slot_cur_auth
       | simp)+
  done

lemma transfer_caps_empty_inv:
  "\<lbrace>P\<rbrace>  transfer_caps mi [] endpoint receiver rbuf \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding transfer_caps_def
  by (wp | wpc | simp) +

lemma lcs_valid':
  "\<lbrace>valid_objs\<rbrace> lookup_cap_and_slot thread xs \<lbrace>\<lambda>x s. s \<turnstile> fst x\<rbrace>, -"
  unfolding lookup_cap_and_slot_def
  apply (rule hoare_pre)
  apply wp
   apply (simp add: split_def)
   apply (wp lookup_slot_for_thread_inv | simp)+
  done

lemma lec_valid_cap':
  "\<lbrace>valid_objs\<rbrace> lookup_extra_caps thread xa mi \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. s \<turnstile> fst x)\<rbrace>, -"
  unfolding lookup_extra_caps_def
  by (wpsimp wp: mapME_set lcs_valid')

(* FIXME: MOVE *)
lemma hoare_conjDR1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> R rv s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by (simp add:validE_def validE_R_def valid_def) blast

lemma hoare_conjDR2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> R rv s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,-"
  by (simp add:validE_def validE_R_def valid_def) blast

lemma do_normal_transfer_pas_refined:
  "\<lbrace>pas_refined aag
        and valid_objs and valid_mdb
        and K (grant \<longrightarrow> is_subject aag sender)
        and K (grant \<longrightarrow> is_subject aag receiver)\<rbrace>
     do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
proof(cases grant)
  case True thus ?thesis
    apply -
    apply (rule hoare_gen_asm)
    apply (simp add: do_normal_transfer_def)
    by (simp
         | wp copy_mrs_pas_refined transfer_caps_pas_refined lec_valid_cap'
           copy_mrs_cte_wp_at
           hoare_vcg_ball_lift
           lookup_extra_caps_srcs[simplified ball_conj_distrib,THEN hoare_conjDR1]
           lookup_extra_caps_srcs[simplified ball_conj_distrib,THEN hoare_conjDR2]
           lookup_extra_caps_authorised lookup_extra_caps_auth lec_valid_cap'
         | wpc | simp add:ball_conj_distrib)+
next
  case False thus ?thesis
    apply (simp add: do_normal_transfer_def)
    by (simp
          | wp copy_mrs_pas_refined transfer_caps_empty_inv
               copy_mrs_cte_wp_at
              hoare_vcg_const_imp_lift hoare_vcg_all_lift
         | wpc)+
qed

crunch pas_refined[wp]: do_fault_transfer "pas_refined aag"

lemma do_ipc_transfer_pas_refined:
  "\<lbrace>pas_refined aag
        and valid_objs and valid_mdb
        and K (grant \<longrightarrow> is_subject aag sender)
        and K (grant \<longrightarrow> is_subject aag receiver)\<rbrace>
     do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: do_ipc_transfer_def)
  apply (wp do_normal_transfer_pas_refined
            hoare_vcg_conj_lift hoare_vcg_all_lift
       | rule hoare_drop_imps
       | wpc)+
  by simp


(* FIXME MOVE*)
lemma cap_insert_pas_refined_transferable:
  "\<lbrace>pas_refined aag and valid_mdb
     and K (is_transferable_cap new_cap
            \<and> aag_cap_auth aag (pasObjectAbs aag (fst dest_slot)) new_cap
            \<and> (pasObjectAbs aag (fst src_slot), DeleteDerived, pasObjectAbs aag (fst dest_slot))
                           \<in> pasPolicy aag) \<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cap_insert_def)
  apply (rule hoare_pre)
  apply (wp set_cap_pas_refined set_cdt_pas_refined update_cdt_pas_refined hoare_vcg_imp_lift
            hoare_weak_lift_imp hoare_vcg_all_lift set_cap_caps_of_state2
            set_untyped_cap_as_full_cdt_is_original_cap get_cap_wp
            tcb_domain_map_wellformed_lift hoare_vcg_disj_lift
            set_untyped_cap_as_full_is_transferable'
        | simp split del: if_split del: split_paired_All fun_upd_apply
        | strengthen update_one_strg)+
  by (fastforce split: if_split_asm
                 simp: cte_wp_at_caps_of_state pas_refined_refl valid_mdb_def2
                       mdb_cte_at_def Option.is_none_def
             simp del: split_paired_All
                 dest: aag_cdt_link_Control aag_cdt_link_DeleteDerived cap_auth_caps_of_state
                intro: aag_wellformed_delete_derived_trans[OF _ _ pas_refined_wellformed])


lemma setup_caller_cap_pas_refined:
  "\<lbrace>pas_refined aag
         and valid_mdb
         and K((grant \<longrightarrow> is_subject aag sender \<and> is_subject aag receiver) \<and>
             (pasObjectAbs aag receiver, Reply, pasObjectAbs aag sender) \<in> pasPolicy aag )\<rbrace>
     setup_caller_cap sender receiver grant
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (rule conjI)
   (* if grant *)
   apply clarsimp
   apply (rule hoare_pre)
    apply (wpsimp wp: cap_insert_pas_refined set_thread_state_pas_refined)
   apply (fastforce simp: aag_cap_auth_def clas_no_asid cli_no_irqs pas_refined_refl)
   (* if not grant *)
  apply clarsimp
  apply (rule hoare_pre)
   apply (wp cap_insert_pas_refined_transferable set_thread_state_pas_refined)
  by (fastforce simp: aag_cap_auth_def cap_links_irq_def cap_links_asid_slot_def
                      cap_auth_conferred_def reply_cap_rights_to_auth_def
               intro: aag_wellformed_delete_derived[OF _ pas_refined_wellformed])

(* FIXME: MOVE *)
lemma sym_ref_endpoint_recvD:
  assumes sym: "sym_refs (state_refs_of s)"
  and ep: "ko_at (Endpoint (RecvEP l)) epptr s"
  and inl: "t \<in> set l"
  shows "\<exists> pl. st_tcb_at ((=) (BlockedOnReceive epptr pl)) t s"
proof -
  have "(t, EPRecv) \<in> state_refs_of s epptr"
    using ep inl by (force simp: state_refs_of_def dest:ko_atD)
  hence "(epptr, TCBBlockedRecv) \<in> state_refs_of s t"
    using sym by (force dest:sym_refsD[rotated])
  thus ?thesis
    by (force simp: st_tcb_at_tcb_states_of_state_eq tcb_states_of_state_def get_tcb_def
                    state_refs_of_def tcb_st_refs_of_def tcb_bound_refs_def ep_q_refs_of_def
                    ntfn_q_refs_of_def ntfn_bound_refs_def
             split: ntfn.splits endpoint.splits thread_state.splits option.splits
                    kernel_object.splits)
qed

lemma pas_refined_ep_recv:
  assumes policy: "pas_refined aag s"
  and invs: "invs s"
  and ep: "ko_at (Endpoint (RecvEP l)) epptr s"
  and inl: "t \<in> set l"
  shows "(pasObjectAbs aag t, Receive, pasObjectAbs aag epptr) \<in> pasPolicy aag"
  apply (insert sym_ref_endpoint_recvD[OF invs_sym_refs[OF invs] ep inl])
  apply clarsimp
  apply (clarsimp simp:st_tcb_at_tcb_states_of_state_eq)
  apply (rule pas_refined_mem[OF _ policy])
  apply (rule sta_ts[of epptr Receive])
  apply (simp add:thread_states_def)
  done

lemma send_ipc_valid_ep_helper:
  "\<lbrakk>invs s ; ko_at (Endpoint (RecvEP (h # t))) epptr s \<rbrakk> \<Longrightarrow>
   valid_ep (case t of [] \<Rightarrow> IdleEP | h' # t'  \<Rightarrow> RecvEP t) s"
  apply (drule invs_valid_objs)
  apply (drule ko_atD)
  apply (erule(1) valid_objsE)
  by (cases t; simp add: valid_obj_def valid_ep_def)

lemmas head_in_set = list.set_intros(1)[of h t for h t]


lemma send_ipc_pas_refined:
  "\<lbrace>pas_refined aag
       and invs
       and K (is_subject aag thread
              \<and> aag_has_auth_to aag SyncSend epptr
              \<and> (can_grant_reply \<longrightarrow> aag_has_auth_to aag Call epptr)
              \<and> (can_grant \<longrightarrow> aag_has_auth_to aag Grant epptr \<and> aag_has_auth_to aag Call epptr))\<rbrace>
     send_ipc block call badge can_grant can_grant_reply thread epptr
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wpc | wp set_thread_state_pas_refined)+
         apply (simp add: hoare_if_r_and split del:if_split)
         apply (wp setup_caller_cap_pas_refined set_thread_state_pas_refined)+
       apply (simp split del:if_split)
       apply (rule_tac Q="\<lambda>rv.  valid_mdb
                            and pas_refined aag and K(
                      (can_grant \<or> can_grant_reply \<longrightarrow>   (reply_can_grant \<longrightarrow> is_subject aag x21) \<and>
                       (pasObjectAbs aag x21, Reply, pasSubject aag) \<in> pasPolicy aag))"
              in hoare_strengthen_post[rotated])
        apply simp
       apply (wp set_thread_state_pas_refined do_ipc_transfer_pas_refined static_imp_wp gts_wp
             | wpc
             | simp add: hoare_if_r_and)+
   apply (wp hoare_vcg_all_lift hoare_imp_lift_something | simp add:st_tcb_at_tcb_states_of_state_eq)+
  subgoal for ep s (* post-wp proof *)
    apply (intro conjI impI; clarsimp;
           frule(2) pas_refined_ep_recv[OF _ _ _ head_in_set])

    subgoal (* can_grant *)
      apply (frule(2) aag_wellformed_grant_Control_to_recv[OF _ _ pas_refined_wellformed])
      apply (frule(2) aag_wellformed_reply[OF _ _ pas_refined_wellformed])
      apply (force elim: send_ipc_valid_ep_helper simp:aag_has_auth_to_Control_eq_owns)
      done
    subgoal (* can_grant_reply and not can_grant*)
      apply (frule(2) aag_wellformed_reply[OF _ _ pas_refined_wellformed])
      apply (frule(1) tcb_states_of_state_to_auth)
      (* Make the blockedOnReceive state point to epptr *)
      apply (frule(1) sym_ref_endpoint_recvD[OF invs_sym_refs _ head_in_set],
             clarsimp simp:st_tcb_at_tcb_states_of_state_eq)
      apply (fastforce elim: send_ipc_valid_ep_helper
                       simp: aag_has_auth_to_Control_eq_owns
                       dest: aag_wellformed_grant_Control_to_recv_by_reply
                               [OF _ _ _ pas_refined_wellformed])
      done
    subgoal (* not can_grant_reply and not can_grant*)
      by (force elim: send_ipc_valid_ep_helper)
    done
  done

lemma set_simple_ko_get_tcb:
  "\<lbrace>\<lambda>s. P (get_tcb p s)\<rbrace> set_simple_ko f ep epptr \<lbrace>\<lambda>_ s. P (get_tcb p s) \<rbrace>"
  unfolding set_simple_ko_def set_object_def
  apply (wp get_object_wp)
  apply (auto simp: partial_inv_def a_type_def get_tcb_def obj_at_def the_equality
                 split: Structures_A.kernel_object.splits option.splits)
  done

lemma get_tcb_is_Some_iff_typ_at:
  "(\<exists>y. get_tcb p s = Some y) = typ_at ATCB p s"
  by (simp add: tcb_at_typ [symmetric] tcb_at_def)

lemma case_list_cons_cong:
  "(case xxs of [] \<Rightarrow> f | x # xs \<Rightarrow> g xxs)
 = (case xxs of [] \<Rightarrow> f | x # xs \<Rightarrow> g (x # xs))"
  by (simp split: list.split)

lemma complete_signal_integrity:
  "\<lbrace>integrity aag X st and pas_refined aag and valid_objs
           and bound_tcb_at ((=) (Some ntfnptr)) thread
           and K (is_subject aag thread)\<rbrace>
     complete_signal ntfnptr thread
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: complete_signal_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply ((wp set_notification_respects[where auth=Receive] set_thread_state_integrity_autarch as_user_integrity_autarch
       | wpc
       | simp)+)[1]
  apply clarsimp
  apply (drule_tac t="pasSubject aag" in sym)
  apply (fastforce intro!: bound_tcb_at_implies_receive)
  done


match_abbreviation (input) receive_ipc_base2
  in concl receive_ipc_def
  select "case_endpoint X Y Z A" (for X Y Z A)

abbreviation (input) receive_ipc_base
where
  "receive_ipc_base aag thread ep epptr rights is_blocking
    \<equiv> receive_ipc_base2 thread is_blocking epptr rights ep"


lemma sym_ref_endpoint_sendD:
  assumes sym: "sym_refs (state_refs_of s)"
  and ep: "ko_at (Endpoint (SendEP l)) epptr s"
  and inl: "t \<in> set l"
  shows "\<exists> pl. st_tcb_at ((=) (BlockedOnSend epptr pl)) t s"
proof -
  have "(t, EPSend) \<in> state_refs_of s epptr"
    using ep inl by (force simp: state_refs_of_def dest:ko_atD)
  hence "(epptr, TCBBlockedSend) \<in> state_refs_of s t"
    using sym by (force dest:sym_refsD[rotated])
  thus ?thesis
    by (force simp: st_tcb_at_tcb_states_of_state_eq tcb_states_of_state_def get_tcb_def
                    state_refs_of_def tcb_st_refs_of_def tcb_bound_refs_def ep_q_refs_of_def
                    ntfn_q_refs_of_def ntfn_bound_refs_def
             split: ntfn.splits endpoint.splits thread_state.splits option.splits
                    kernel_object.splits)
qed

lemma receive_ipc_valid_ep_helper:
  "\<lbrakk> invs s; ko_at (Endpoint (SendEP list)) epptr s \<rbrakk> \<Longrightarrow>
   valid_ep (case tl list of [] \<Rightarrow> IdleEP | a # t \<Rightarrow> SendEP (tl list)) s"
  apply (drule_tac invs_valid_objs)
  apply (drule ko_atD)
  apply (erule(1) valid_objsE)
  apply (cases list, solves \<open>simp add: valid_obj_def valid_ep_def\<close>)
  by (cases "tl list"; clarsimp simp:valid_obj_def valid_ep_def)

lemma receive_ipc_sender_helper:
  "\<lbrakk>pas_refined aag s ; kheap s thread = Some (TCB tcb) ; tcb_state tcb = BlockedOnSend ep pl\<rbrakk>
   \<Longrightarrow> (pasObjectAbs aag thread, SyncSend, pasObjectAbs aag ep) \<in> pasPolicy aag"
  apply (erule pas_refined_mem[rotated])
  apply (rule sta_ts)
  apply (simp add: thread_states_def tcb_states_of_state_def get_tcb_def)
  done

lemma receive_ipc_sender_can_grant_helper:
  "\<lbrakk>invs s; pas_refined aag s ; kheap s thread = Some (TCB tcb) ; tcb_state tcb = BlockedOnSend ep pl;
    sender_can_grant pl ; aag_has_auth_to aag Receive ep\<rbrakk>
   \<Longrightarrow> is_subject aag thread"
  apply (frule pas_refined_mem[rotated,where x = "thread" and auth=Grant])
   apply (rule sta_ts)
   apply (simp add:thread_states_def tcb_states_of_state_def get_tcb_def)
  apply (frule(2) aag_wellformed_grant_Control_to_send[OF _ _ pas_refined_wellformed])
  apply (simp add:aag_has_auth_to_Control_eq_owns)
  done


lemma receive_ipc_base_pas_refined:
  "\<lbrace>pas_refined aag and invs
           and ko_at (Endpoint ep) epptr
           and K (is_subject aag thread
               \<and> (pasSubject aag, Receive, pasObjectAbs aag epptr) \<in> pasPolicy aag \<and>
               (\<forall> auth \<in> cap_rights_to_auth rights True . aag_has_auth_to aag auth epptr))\<rbrace>
    receive_ipc_base aag thread ep epptr rights is_blocking
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  (* FIXME: proof structure *)
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: thread_get_def cong: endpoint.case_cong)
  apply (rule hoare_pre)
   apply (wp set_thread_state_pas_refined get_simple_ko_wp setup_caller_cap_pas_refined
        | wpc | simp add: thread_get_def do_nbrecv_failed_transfer_def split del: if_split)+
        apply (rename_tac list sss data)
        apply (rule_tac Q="\<lambda>rv s. pas_refined aag s \<and> valid_mdb s \<and>
                             (sender_can_grant data \<longrightarrow> is_subject aag (hd list)) \<and>
                             (sender_can_grant_reply data \<longrightarrow>
                             (AllowGrant \<in> rights \<longrightarrow> is_subject aag (hd list)) \<and>
                             (pasSubject aag, Reply, pasObjectAbs aag (hd list)) \<in> pasPolicy aag)"
                     in hoare_strengthen_post[rotated])
         apply (fastforce simp: cap_auth_conferred_def pas_refined_all_auth_is_owns
                                pas_refined_refl)
        apply (wp static_imp_wp do_ipc_transfer_pas_refined set_simple_ko_pas_refined
                  set_thread_state_pas_refined get_simple_ko_wp hoare_vcg_all_lift
                  hoare_vcg_imp_lift [OF set_simple_ko_get_tcb, unfolded disj_not1]
             | wpc
             | simp add: thread_get_def  get_thread_state_def do_nbrecv_failed_transfer_def)+
  apply (clarsimp simp: tcb_at_def [symmetric] tcb_at_st_tcb_at)
  subgoal premises prems for s
  proof -
    have "\<And>P Q R. \<lbrakk> R ; P \<Longrightarrow> R \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q) \<and> (\<not>P \<longrightarrow> R)" by blast
    thus ?thesis
      apply this
      using prems
       apply clarsimp
      subgoal premises prems for list ep' pl
      proof -
        have "sender_can_grant pl \<Longrightarrow> is_subject aag (hd list)"
          using prems
          apply (clarsimp elim!: tcb_atE simp:tcb_at_st_tcb_at[symmetric] get_tcb_def)
          apply (frule(1) sym_ref_endpoint_sendD[OF invs_sym_refs,where t= "hd list"],force)
          apply (clarsimp simp:st_tcb_at_def elim!:obj_atE)
          by (rule receive_ipc_sender_can_grant_helper)
        moreover have
          "sender_can_grant_reply pl \<Longrightarrow>
              (pasSubject aag, Reply, pasObjectAbs aag (hd list)) \<in> pasPolicy aag"
          using prems
          apply (clarsimp elim!: tcb_atE simp:tcb_at_st_tcb_at[symmetric] get_tcb_def)
          apply (frule(1) sym_ref_endpoint_sendD[OF invs_sym_refs,where t= "hd list"],force)
          apply (clarsimp simp:st_tcb_at_def elim!:obj_atE)
          apply (frule pas_refined_mem[rotated,where x = "(hd list)" and auth=Call])
           apply (rule sta_ts)
           apply (simp add:thread_states_def tcb_states_of_state_def get_tcb_def)
          by (erule(2) aag_wellformed_reply[OF _ _ pas_refined_wellformed])
        ultimately show ?thesis
          using prems by (force dest:receive_ipc_valid_ep_helper)
      qed
      apply clarsimp
      using prems
      apply (intro conjI;clarsimp simp add:cap_rights_to_auth_def)
      apply (clarsimp elim!: tcb_atE simp:tcb_at_st_tcb_at[symmetric] get_tcb_def
                             cap_rights_to_auth_def)
      apply (frule_tac t="hd x" in sym_ref_endpoint_sendD[OF invs_sym_refs],assumption,force)
      apply (clarsimp simp:st_tcb_at_def elim!:obj_atE)
      apply (frule_tac x="hd x" in pas_refined_mem[rotated,where auth=Call])
       apply (rule sta_ts)
       apply (simp add:thread_states_def tcb_states_of_state_def get_tcb_def)
      apply (frule aag_wellformed_grant_Control_to_send_by_reply[OF _ _ _ pas_refined_wellformed])
      by (force simp:aag_has_auth_to_Control_eq_owns)+
  qed
  done

lemma complete_signal_pas_refined:
  "\<lbrace>pas_refined aag and bound_tcb_at ((=) (Some ntfnptr)) thread\<rbrace>
     complete_signal ntfnptr thread
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: complete_signal_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply (wp set_simple_ko_pas_refined set_thread_state_pas_refined
       | wpc)+
  apply clarsimp
  done

lemma receive_ipc_pas_refined:
  "\<lbrace>pas_refined aag
         and invs
         and K (is_subject aag thread
              \<and> pas_cap_cur_auth aag ep_cap \<and> AllowRead \<in> cap_rights ep_cap)\<rbrace>
     receive_ipc thread ep_cap is_blocking
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: receive_ipc_def thread_get_def  split: cap.split)
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (case_tac ntfnptr, simp_all)
  (* old receive_ipc stuff *)
   apply (rule hoare_pre)
    apply (wp receive_ipc_base_pas_refined)[1]
   apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
   (* ntfn-binding case *)
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "isActive ntfn", simp_all)
   apply (wp complete_signal_pas_refined, clarsimp)
   (* regular case again *)
  apply (rule hoare_pre, wp receive_ipc_base_pas_refined)
  apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
  done


subsection \<open>@{term "integrity"}\<close>

subsubsection\<open>autarchy\<close>

text\<open>

  For the case when the currently-running thread owns the receiver
  (i.e. receiver last to the IPC rendezvous or sender owns receiver).

\<close>


lemma set_extra_badge_integrity_autarch:
  "\<lbrace>(integrity aag X st and
         K (is_subject aag thread \<and>
            ipc_buffer_has_auth aag thread (Some buf) \<and>
            buffer_cptr_index + n < 2 ^ (msg_align_bits - 2)))\<rbrace>
  set_extra_badge buf badge n
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding set_extra_badge_def
  by (wp store_word_offs_integrity_autarch)

lemma transfer_caps_integrity_autarch:
  "\<lbrace>pas_refined aag
        and integrity aag X st
        and valid_objs and valid_mdb
        and (\<lambda> s. (\<forall>x\<in>set caps.
               s \<turnstile> fst x) \<and>
              (\<forall>x\<in>set caps.
               cte_wp_at
                (\<lambda>cp. fst x \<noteq> NullCap \<longrightarrow>
                      cp = fst x)
                (snd x) s \<and>
               real_cte_at (snd x) s))
        and K (is_subject aag receiver \<and> ipc_buffer_has_auth aag receiver receive_buffer \<and>
               (\<forall>x\<in>set caps. is_subject aag (fst (snd x))) \<and> length caps < 6)\<rbrace>
    transfer_caps mi caps endpoint receiver receive_buffer
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: transfer_caps_def)
  apply (wpc | wp)+
  apply (rule_tac P = "\<forall>x \<in> set dest_slots. is_subject aag (fst x)" in hoare_gen_asm)
  apply (wp transfer_caps_loop_pres_dest cap_insert_integrity_autarch set_extra_badge_integrity_autarch [where aag = aag and thread = receiver]
            get_receive_slots_authorised hoare_vcg_all_lift hoare_vcg_imp_lift
       | simp add: msg_align_bits buffer_cptr_index_def msg_max_length_def cte_wp_at_caps_of_state
       | blast)+
  done

(* FIXME: duplicate somehow *)
lemma load_word_offs_inv[wp]:
  "\<lbrace>P\<rbrace> load_word_offs buf off \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: load_word_offs_def do_machine_op_def split_def)
  apply wp
  apply clarsimp
  apply (drule in_inv_by_hoareD[OF loadWord_inv])
  apply simp
  done

lemma copy_mrs_integrity_autarch:
  "\<lbrace>pas_refined aag and integrity aag X st and K (is_subject aag receiver \<and> ipc_buffer_has_auth aag receiver rbuf \<and> unat n < 2 ^ (msg_align_bits - 2))\<rbrace>
     copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_mrs_def cong: if_cong split del: if_split)
  apply (wp mapM_wp' as_user_integrity_autarch
            store_word_offs_integrity_autarch [where aag = aag and thread = receiver]
       | wpc
       | simp
       | fastforce simp: msg_align_bits split: if_split_asm)+
  done

(* FIXME: Why was the [wp] attribute clobbered by interpretation of the Arch locale? *)
declare as_user_thread_bound_ntfn[wp]

lemma get_mi_valid':
  "\<lbrace>\<top>\<rbrace> get_message_info a \<lbrace>\<lambda>rv s. valid_message_info rv\<rbrace>"
  apply (simp add: get_message_info_def)
  apply (wp, rule hoare_post_imp, rule data_to_message_info_valid)
   apply wp+
  done

lemma lookup_extra_caps_length:
  "\<lbrace>K (valid_message_info mi)\<rbrace> lookup_extra_caps thread buf mi \<lbrace>\<lambda>rv s. length rv < 6\<rbrace>, -"
  unfolding lookup_extra_caps_def
  apply (cases buf, simp_all)
   apply (wp mapME_length | simp add: comp_def  valid_message_info_def msg_max_extra_caps_def word_le_nat_alt)+
  done

lemma get_mi_length:
  "\<lbrace>\<top>\<rbrace> get_message_info sender \<lbrace>\<lambda>rv s. unat (mi_length rv) < 2 ^ (msg_align_bits - 2)\<rbrace>"
  apply (rule hoare_post_imp [OF _ get_mi_valid'])
  apply (clarsimp simp: valid_message_info_def msg_align_bits msg_max_length_def word_le_nat_alt)
  done

lemma do_normal_transfer_send_integrity_autarch:
  notes lec_valid_cap[wp del]
  shows
  "\<lbrace>pas_refined aag
        and integrity aag X st
        and valid_objs and valid_mdb
        and K (is_subject aag receiver \<and>
               ipc_buffer_has_auth aag receiver rbuf \<and>
               (grant \<longrightarrow> is_subject aag sender))\<rbrace>
     do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: do_normal_transfer_def)
  apply (wp as_user_integrity_autarch set_message_info_integrity_autarch transfer_caps_integrity_autarch
            copy_mrs_integrity_autarch
            copy_mrs_tcb copy_mrs_cte_wp_at lookup_extra_caps_authorised
            lookup_extra_caps_length get_mi_length get_mi_valid'
            hoare_vcg_conj_lift hoare_vcg_ball_lift lec_valid_cap' static_imp_wp
       | wpc
       | simp)+
  done

crunch integrity_autarch: setup_caller_cap "integrity aag X st"

lemma do_fault_transfer_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag receiver \<and> ipc_buffer_has_auth aag receiver recv_buf) \<rbrace>
    do_fault_transfer badge sender receiver recv_buf
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: do_fault_transfer_def split_def)
  apply (wp as_user_integrity_autarch set_message_info_integrity_autarch set_mrs_integrity_autarch
            thread_get_wp'
       | wpc | simp)+
  done

lemma do_ipc_transfer_integrity_autarch:
  "\<lbrace>pas_refined aag
        and integrity aag X st
        and valid_objs and valid_mdb
        and K (is_subject aag receiver \<and> (grant \<longrightarrow> is_subject aag sender))\<rbrace>
     do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: do_ipc_transfer_def)
  apply (wp do_normal_transfer_send_integrity_autarch do_fault_transfer_integrity_autarch
            thread_get_wp' lookup_ipc_buffer_has_auth hoare_vcg_all_lift
       | wpc | simp | wp (once) hoare_drop_imps)+
  done

lemma set_thread_state_running_respects:
  "\<lbrace>integrity aag X st
        and (\<lambda>s. \<exists>ep. aag_has_auth_to aag Receive ep
                   \<and> st_tcb_at (send_blocked_on ep) sender s)\<rbrace>
     set_thread_state sender Structures_A.Running
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def st_tcb_at_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (rule_tac new_st=Running in tro_tcb_receive)
  apply (auto simp: tcb_bound_notification_reset_integrity_def)
  done

(* FIXME move *)
lemma set_simple_ko_obj_at:
  "\<lbrace>obj_at P ptr and K (ptr \<noteq> epptr)\<rbrace>
     set_simple_ko f epptr ep
   \<lbrace>\<lambda>rv. obj_at P ptr\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (auto simp: obj_at_def)
  done

(* ep is free here *)
lemma sts_receive_Inactive_respects:
  "\<lbrace>integrity aag X st and st_tcb_at (send_blocked_on ep) thread
    and (\<lambda>s. \<forall>tcb. get_tcb thread s = Some tcb \<longrightarrow> call_blocked ep (tcb_state tcb))
    and K (aag_has_auth_to aag Receive ep)\<rbrace>
    set_thread_state thread Structures_A.thread_state.Inactive
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  apply (drule get_tcb_SomeD)
  apply (rule_tac new_st=Inactive in tro_tcb_receive, simp_all)
  apply (fastforce simp add: st_tcb_at_def obj_at_def)
  done

crunch pred_tcb: do_ipc_transfer "pred_tcb_at proj P t"
  (wp: crunch_wps transfer_caps_loop_pres make_fault_message_inv simp: zipWithM_x_mapM)

lemma set_untyped_cap_as_full_not_untyped:
  "\<lbrace> P and K(\<not> is_untyped_cap cap') \<rbrace>
   set_untyped_cap_as_full cap cap' slot
   \<lbrace> \<lambda>rv. P\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  apply wp
  apply (rule hoare_pre_cont)
   apply wpsimp+
  done


lemma cap_insert_integrity_autarch_not_untyped:
  "\<lbrace>integrity aag X st and
     K (\<not> is_untyped_cap cap \<and> is_subject aag (fst dest_slot))\<rbrace>
   cap_insert cap src_slot dest_slot
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add:cap_insert_def)
  apply (wp set_original_integrity_autarch cap_insert_ext_extended.list_integ_lift
            cap_insert_list_integrity update_cdt_fun_upd_integrity_autarch gets_inv
            set_cap_integrity_autarch set_untyped_cap_as_full_not_untyped assert_inv)
  apply fastforce
  done

(* FIXME MOVE*)
lemma pred_tcb_atE:
  assumes hyp: "pred_tcb_at proj pred t s"
  obtains tcb where "kheap s t = Some (TCB tcb)" and " pred (proj (tcb_to_itcb tcb))"
  using hyp by (fastforce elim:obj_atE simp:pred_tcb_at_def)


lemma set_thread_state_blocked_on_reply_respects:
  "\<lbrace> integrity aag X st and
       st_tcb_at (send_blocked_on ep) thread and
       pred_tcb_at id (\<lambda>itcb. allowed_call_blocked ep (itcb_state itcb)) thread
       and K(aag_has_auth_to aag Receive ep)\<rbrace>
     set_thread_state thread BlockedOnReply
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (erule integrity_trans)
  apply (clarsimp simp:integrity_def dest!:get_tcb_SomeD elim!: pred_tcb_atE)
  apply (rule tro_tcb_receive[where new_st=BlockedOnReply])
  by fastforce+

lemma setup_caller_cap_integrity_recv:
  "\<lbrace>integrity aag X st and valid_mdb
       and st_tcb_at (send_blocked_on ep) sender and
       pred_tcb_at id (\<lambda>itcb. allowed_call_blocked ep (itcb_state itcb)) sender
      and K (aag_has_auth_to aag Receive ep \<and> is_subject aag receiver
             \<and> (grant \<longrightarrow> is_subject aag sender))\<rbrace>
     setup_caller_cap sender receiver grant
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (unfold setup_caller_cap_def)
  apply (wp cap_insert_integrity_autarch_not_untyped set_thread_state_blocked_on_reply_respects)
  by fastforce

lemma pred_tcb_atI:
  "\<lbrakk>kheap s t = Some (TCB tcb) ;pred (proj (tcb_to_itcb tcb))\<rbrakk> \<Longrightarrow> pred_tcb_at proj pred t s"
  by (fastforce simp:pred_tcb_at_def obj_at_def)

(* FIXME MOVE *)
abbreviation
  sender_can_call :: "sender_payload \<Rightarrow> bool"
where
  "sender_can_call pl \<equiv> sender_can_grant pl \<or> sender_can_grant_reply pl"

lemma receive_ipc_base_integrity:
  notes do_nbrecv_failed_transfer_def[simp]
  shows "\<lbrace>pas_refined aag and integrity aag X st and invs
          and ko_at (Endpoint ep) epptr
          and K (is_subject aag receiver
                \<and> (pasSubject aag, Receive, pasObjectAbs aag epptr) \<in> pasPolicy aag
                \<and> (\<forall>auth \<in> cap_rights_to_auth rights True. aag_has_auth_to aag auth epptr))\<rbrace>
          receive_ipc_base aag receiver ep epptr rights is_blocking
         \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: thread_get_def get_thread_state_def cong: endpoint.case_cong)
  apply (rule hoare_pre)
   apply (wp set_endpoinintegrity set_thread_state_running_respects
             setup_caller_cap_integrity_recv[where ep = epptr]
             do_ipc_transfer_integrity_autarch
             set_thread_state_integrity_autarch[where param_a=receiver]
             sts_receive_Inactive_respects[where ep = epptr]
             as_user_integrity_autarch
       | wpc | simp)+
        apply (rename_tac list tcb data)
        apply (rule_tac Q="\<lambda>rv s. integrity aag X st s
                           \<and> valid_mdb s
                           \<and> is_subject aag receiver
                           \<and> (sender_can_call data \<longrightarrow> AllowGrant \<in> rights
                                                   \<longrightarrow> is_subject aag (hd list))
                           \<and> (sender_can_grant data \<longrightarrow> is_subject aag (hd list))
                           \<and> st_tcb_at (send_blocked_on epptr) (hd list) s
                           \<and> st_tcb_at (\<lambda>st. st = BlockedOnSend epptr data) (hd list) s"
                     in hoare_strengthen_post[rotated])
         apply (fastforce simp: st_tcb_at_def obj_at_def get_tcb_rev call_blocked_def
                                allowed_call_blocked_def
                         dest!: get_tcb_SomeD
                         elim: pred_tcb_atI)
        apply (wp do_ipc_transfer_integrity_autarch do_ipc_transfer_pred_tcb set_endpoinintegrity
                  get_simple_ko_wp
                  set_thread_state_integrity_autarch[where param_a=receiver]
                  hoare_vcg_imp_lift [OF set_simple_ko_get_tcb, unfolded disj_not1]
                  hoare_vcg_all_lift as_user_integrity_autarch
              | wpc | simp)+
  apply clarsimp
  apply (subgoal_tac "ep_at epptr s \<and> (\<exists>auth. aag_has_auth_to aag auth epptr
                                    \<and> (auth = Receive \<or> auth = SyncSend \<or> auth = Reset))")
   prefer 2
   apply (fastforce simp: obj_at_def is_ep)
  apply simp
  apply (thin_tac "ep_at epptr s \<and> (\<exists>auth. aag_has_auth_to aag auth epptr
                                 \<and> (auth = Receive \<or> auth = SyncSend \<or> auth = Reset))")
  apply (clarsimp simp: st_tcb_def2 a_type_def)
  apply (frule_tac t="hd x" in sym_ref_endpoint_sendD[OF invs_sym_refs],assumption,force)
  apply (clarsimp simp: get_tcb_def elim!: pred_tcb_atE)
  apply (intro conjI;
         (force elim: receive_ipc_valid_ep_helper receive_ipc_sender_can_grant_helper)?)
  apply (intro impI)
  apply (frule_tac x= "hd x" in pas_refined_mem[rotated,where auth=Call])
   apply (rule sta_ts)
   apply (simp add: thread_states_def tcb_states_of_state_def get_tcb_def)
  apply (simp add: cap_rights_to_auth_def)
  apply (rule aag_has_auth_to_Control_eq_owns[THEN iffD1],assumption)
  apply (erule aag_wellformed_grant_Control_to_send_by_reply[OF _ _ _ pas_refined_wellformed];force)
  done

lemma receive_ipc_integrity_autarch:
  "\<lbrace>pas_refined aag and integrity aag X st and invs
        and K (is_subject aag receiver
            \<and> pas_cap_cur_auth aag cap \<and> AllowRead \<in> cap_rights cap)\<rbrace>
    receive_ipc receiver cap is_blocking
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: receive_ipc_def split: cap.splits)
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (case_tac ntfnptr, simp_all)
  (* old receive case, not bound *)
   apply (rule hoare_pre, wp receive_ipc_base_integrity)
   apply (fastforce simp:aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "isActive ntfn", simp_all)
  (* new ntfn-binding case *)
   apply (rule hoare_pre, wp complete_signal_integrity, clarsimp)
   (* old receive case, bound ntfn not active *)
  apply (rule hoare_pre, wp receive_ipc_base_integrity)
  apply (fastforce simp:aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
  done

subsubsection\<open>Non-autarchy: the sender is running\<close>

text\<open>

  If the sender is running (i.e. last to the IPC rendezvous) then we
  need this auxiliary machinery to show that the sequence of TCB
  updates ends up in the tcb_send, tcb_call or tcb_reply case of @{term integrity_obj}.

  This machinery is used for both send_ipc and do_reply_transfer

  The sender can update an IPC receiver's context as much as it likes,
  provided it eventually changes the thread state to Running.

\<close>

datatype tcb_respects_state = TRContext | TRFinal | TRFinalOrCall | TRReplyContext

inductive
  tcb_in_ipc for aag tst l' epptr ko ko'
where
  tii_lrefl: "\<lbrakk> l' = pasSubject aag \<rbrakk> \<Longrightarrow> tcb_in_ipc aag tst l' epptr ko ko'"
| tii_context: "\<lbrakk> ko  = Some (TCB tcb);
                  ko' = Some (TCB tcb');
                  can_receive_ipc (tcb_state tcb);
                  \<exists>ctxt'. tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb)\<rparr>;
                  tst = TRContext\<rbrakk>
        \<Longrightarrow> tcb_in_ipc aag tst l' epptr ko ko'"
| tii_final: "\<lbrakk> ko  = Some (TCB tcb);
                ko' = Some (TCB tcb');
                receive_blocked_on epptr (tcb_state tcb);
                \<exists>ctxt'. tcb' = tcb \<lparr> tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb)
                                   , tcb_state := Structures_A.Running\<rparr>;
                aag_has_auth_to aag SyncSend epptr;
                tst = TRFinal \<or> tst = TRFinalOrCall\<rbrakk>
         \<Longrightarrow> tcb_in_ipc aag tst l' epptr ko ko'"
| tii_call:  "\<lbrakk> ko  = Some (TCB tcb);
                ko' = Some (TCB tcb');
                ep_recv_blocked epptr (tcb_state tcb);
                \<exists>ctxt'. tcb' = tcb \<lparr> tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                                     tcb_state := Structures_A.Running,
                                     tcb_caller := ReplyCap caller False R\<rparr>;
                is_subject aag caller;
                aag_has_auth_to aag Call epptr;
                tst = TRFinal\<rbrakk>
         \<Longrightarrow> tcb_in_ipc aag tst l' epptr ko ko'"
| tii_reply:  "\<lbrakk> ko  = Some (TCB tcb);
                ko' = Some (TCB tcb');
                \<exists>ctxt'. tcb' = tcb \<lparr> tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                                     tcb_fault := None,
                                     tcb_state := Structures_A.Running\<rparr>;
                (pasSubject aag, Reply, l') \<in> pasPolicy aag;
                tcb_state tcb = BlockedOnReply;
                tst = TRFinal\<rbrakk>
         \<Longrightarrow> tcb_in_ipc aag tst l' epptr ko ko'"

lemmas tii_subject[simp] = tii_lrefl [OF refl]

definition integrity_tcb_in_ipc
  :: "'a PAS \<Rightarrow> obj_ref set \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> tcb_respects_state \<Rightarrow>
      det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "integrity_tcb_in_ipc aag X thread epptr tst st \<equiv> \<lambda>s.
     \<not> is_subject aag thread \<and> pas_refined aag st \<and>
     (integrity aag X st (s\<lparr>kheap := (kheap s)(thread := kheap st thread),
                            machine_state :=
                               (machine_state s)\<lparr>underlying_memory :=
                                    (\<lambda>p. if p \<in> auth_ipc_buffers st thread then
                                         underlying_memory (machine_state st) p
                                         else underlying_memory (machine_state s) p) \<rparr>\<rparr>)
   \<and> (tcb_in_ipc aag tst (pasObjectAbs aag thread) epptr (kheap st thread) (kheap s thread)))"

lemma tcb_context_no_change:
  "\<exists>ctxt. tcb = tcb\<lparr> tcb_arch :=  arch_tcb_context_set ctxt (tcb_arch tcb)\<rparr>"
  apply (cases tcb, clarsimp)
  apply (case_tac tcb_arch)
  apply (auto simp: arch_tcb_context_set_def)
  done

lemma auth_ipc_buffers_mem_Write:
  "\<lbrakk> x \<in> auth_ipc_buffers s thread; pas_refined aag s; valid_objs s; is_subject aag thread \<rbrakk>
  \<Longrightarrow> aag_has_auth_to aag Write x"
  apply (clarsimp simp add: auth_ipc_buffers_member_def)
  apply (drule (1) cap_cur_auth_caps_of_state)
   apply simp
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def
                        vspace_cap_rights_to_auth_def vm_read_write_def
                        is_page_cap_def
                 split: if_split_asm)
  apply (auto dest: ipcframe_subset_page)
  done


lemma integrity_tcb_in_ipc_final:
  "\<lbrakk> integrity_tcb_in_ipc aag X thread epptr TRFinal st s \<rbrakk> \<Longrightarrow> integrity aag X st s"
  unfolding integrity_tcb_in_ipc_def
  apply clarsimp
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  apply (rule conjI)
   apply (erule tcb_in_ipc.cases; simp)
     apply (fastforce intro!: tro_tcb_send simp: direct_send_def)
    apply (fastforce intro!: tro_tcb_call  simp: direct_call_def)
    apply clarsimp
   apply (fastforce intro!: tro_tcb_reply tcb.equality simp: direct_reply_def)
    \<comment> \<open>rm\<close>
  apply clarsimp
  apply (cases "is_subject aag thread")
   apply (rule trm_write)
   apply (solves\<open>simp\<close>)
  \<comment> \<open>doesn't own\<close>
  apply (erule tcb_in_ipc.cases, simp_all)[1]
    apply clarsimp
    apply (rule trm_ipc [where p' = thread])
       apply (simp add: tcb_states_of_state_def get_tcb_def)
      apply (simp add: tcb_states_of_state_def get_tcb_def)
     apply (simp add: auth_ipc_buffers_def get_tcb_def
      split: option.split_asm cap.split_asm arch_cap.split_asm if_split_asm  split del: if_split)
    apply simp
   apply clarsimp
   apply (rule trm_ipc [where p' = thread])
      apply (simp add: tcb_states_of_state_def get_tcb_def split:thread_state.splits)
     apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (simp add: auth_ipc_buffers_def get_tcb_def
      split: option.split_asm cap.split_asm arch_cap.split_asm if_split_asm  split del: if_split)
   apply simp
  apply clarsimp
  apply (rule trm_ipc [where p' = thread])
     apply (simp add: tcb_states_of_state_def get_tcb_def split:thread_state.splits)
    apply (simp add: tcb_states_of_state_def get_tcb_def)
   apply (simp add: auth_ipc_buffers_def get_tcb_def
     split: option.split_asm cap.split_asm arch_cap.split_asm if_split_asm  split del: if_split)
  apply simp
  done

lemma update_tcb_context_in_ipc:
  "\<lbrakk> integrity_tcb_in_ipc aag X thread epptr TRContext st s;
     get_tcb thread s = Some tcb;
     tcb' = tcb\<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb)\<rparr>\<rbrakk>
     \<Longrightarrow> integrity_tcb_in_ipc aag X thread epptr TRContext st
                              (s\<lparr>kheap := (kheap s)(thread \<mapsto> TCB tcb')\<rparr>)"
  unfolding integrity_tcb_in_ipc_def
  apply (elim conjE)
  apply (intro conjI)
    apply assumption+
   apply (erule integrity_trans)
   apply (simp cong: if_cong)
  apply clarsimp
  apply (erule tcb_in_ipc.cases, simp_all)
   apply (auto intro!: tii_context[OF refl refl] tii_lrefl[OF refl]  tcb_context_no_change
                dest!: get_tcb_SomeD simp: arch_tcb_context_set_def)
  done


lemma update_tcb_state_in_ipc:
  "\<lbrakk> integrity_tcb_in_ipc aag X thread epptr TRContext st s;
      receive_blocked_on epptr (tcb_state tcb); aag_has_auth_to aag SyncSend epptr;
     get_tcb thread s = Some tcb; tcb' = tcb\<lparr>tcb_state := Structures_A.thread_state.Running\<rparr> \<rbrakk>
     \<Longrightarrow> integrity_tcb_in_ipc aag X thread epptr TRFinalOrCall st
                              (s\<lparr>kheap := (kheap s)(thread \<mapsto> TCB tcb')\<rparr>)"
  unfolding integrity_tcb_in_ipc_def
  apply (elim conjE)
  apply (intro conjI)
     apply assumption+
   apply (erule integrity_trans)
   apply (simp cong: if_cong)
  apply clarsimp
  apply (erule tcb_in_ipc.cases, simp_all)
  apply (drule get_tcb_SomeD)
  apply (rule tii_final[OF refl refl])
     apply (solves\<open>clarsimp\<close>)
    apply (elim exE, intro exI tcb.equality; solves \<open>simp\<close>)
   apply fastforce
  apply fastforce
  done

lemma as_user_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X thread epptr TRContext st\<rbrace>
     as_user thread m
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X thread epptr TRContext st\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def)
  apply (wp gets_the_wp get_wp put_wp mapM_x_wp'
       | wpc
       | simp split del: if_split add: zipWithM_x_mapM_x split_def store_word_offs_def)+
  apply (clarsimp simp: st_tcb_def2 tcb_at_def fun_upd_def[symmetric])
  apply (auto elim: update_tcb_context_in_ipc)
  done

lemma set_message_info_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X thread epptr TRContext st\<rbrace>
     set_message_info thread m
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X thread epptr TRContext st\<rbrace>"
  unfolding set_message_info_def
  by (wp as_user_respects_in_ipc)

lemma mul_add_word_size_lt_msg_align_bits_ofnat:
  "\<lbrakk> p < 2 ^ (msg_align_bits - 2); k < 4 \<rbrakk>
   \<Longrightarrow> of_nat p * of_nat word_size + k < (2 :: obj_ref) ^ msg_align_bits"
  unfolding word_size_def
  apply simp
  apply (rule is_aligned_add_less_t2n[where n=2])
     apply (simp_all add: msg_align_bits word_bits_conv
                          is_aligned_word_size_2[simplified word_size_def, simplified])
  apply (erule word_less_power_trans_ofnat [where k = 2 and m=9, simplified], simp)
  done

lemmas ptr_range_off_off_mems =
    ptr_range_add_memI [OF _ mul_word_size_lt_msg_align_bits_ofnat]
    ptr_range_add_memI [OF _ mul_add_word_size_lt_msg_align_bits_ofnat,
                        simplified add.assoc [symmetric]]

lemma store_word_offs_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and
     K ((\<not> is_subject aag receiver \<longrightarrow> auth_ipc_buffers st receiver = ptr_range buf msg_align_bits)
        \<and> is_aligned buf msg_align_bits \<and> r < 2 ^ (msg_align_bits - 2))\<rbrace>
    store_word_offs buf r v
  \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: store_word_offs_def storeWord_def pred_conj_def)
  apply (rule hoare_pre)
  apply (wp dmo_wp)
  apply (unfold integrity_tcb_in_ipc_def)
  apply (elim conjE)
  apply (intro impI conjI)
    apply assumption+
   apply (erule integrity_trans)
   apply (clarsimp simp:  ptr_range_off_off_mems integrity_def is_aligned_mask [symmetric]
     cong: imp_cong )
 apply simp
 done

crunch respects_in_ipc: set_extra_badge "integrity_tcb_in_ipc aag X receiver epptr TRContext st"
  (wp: store_word_offs_respects_in_ipc)

lemma set_object_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st
          and K (is_subject aag ptr)\<rbrace>
     set_object ptr obj
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (simp add: integrity_tcb_in_ipc_def)
  apply (rule hoare_pre, wp)
   apply (wpsimp wp: set_object_wp)
  apply (simp only: pred_conj_def)
  apply (elim conjE)
  apply (intro conjI ; (solves \<open>simp\<close>)?)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  done

lemma set_cap_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st
          and K (is_subject aag (fst ptr))\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wp set_object_respects_in_ipc_autarch get_object_wp
       | wpc)+
  apply simp
  done

lemma set_original_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st
          and K (is_subject aag (fst slot))\<rbrace>
     set_original slot orig
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (wp set_original_wp)
  apply (clarsimp simp: integrity_tcb_in_ipc_def)
  apply (simp add: integrity_def
                   tcb_states_of_state_def get_tcb_def map_option_def
                 split del: if_split cong: if_cong)
  by (fastforce intro :integrity_cdt_direct)

lemma update_cdt_fun_upd_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
           and K (is_subject aag (fst slot))\<rbrace>
      update_cdt (\<lambda>cdt. cdt (slot := v cdt))
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (clarsimp simp: integrity_tcb_in_ipc_def integrity_def
                        tcb_states_of_state_def get_tcb_def
             split del: if_split cong: if_cong)
  by (fastforce intro :integrity_cdt_direct)

lemma set_untyped_cap_as_full_integrity_tcb_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and
    K (is_subject aag (fst src_slot))\<rbrace>
   set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>ya. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply(rule hoare_pre)
  apply(clarsimp simp: set_untyped_cap_as_full_def)
  apply(intro conjI impI)
  apply (wp set_cap_respects_in_ipc_autarch | simp)+
  done


lemma cap_insert_ext_integrity_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st and K(is_subject aag (fst src_slot))
        and K(is_subject aag (fst dest_slot))\<rbrace>
      cap_insert_ext src_parent src_slot dest_slot src_p dest_p
   \<lbrace>\<lambda>yd. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: integrity_tcb_in_ipc_def split del: if_split)
  apply (unfold integrity_def)
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (rule hoare_lift_Pf[where f="ekheap"])
   apply (clarsimp simp: integrity_tcb_in_ipc_def integrity_def
                         tcb_states_of_state_def get_tcb_def
              split del: if_split cong: if_cong)
   including no_pre
   apply wp
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: list_integ_def del: split_paired_All)
    apply (fold list_integ_def)
    apply (wp cap_insert_list_integrity | simp | force)+
  done

lemma cap_inserintegrity_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
         and K (is_subject aag (fst dest_slot) \<and> is_subject aag (fst src_slot))\<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cap_insert_def cong: if_cong)
  apply (rule hoare_pre)
   apply (wp set_original_respects_in_ipc_autarch
             set_untyped_cap_as_full_integrity_tcb_in_ipc_autarch
             update_cdt_fun_upd_respects_in_ipc_autarch
             set_cap_respects_in_ipc_autarch get_cap_wp
             cap_insert_ext_integrity_in_ipc_autarch
              | simp split del: if_split)+
  done

lemma transfer_caps_loop_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
         and valid_objs and valid_mdb
         and (\<lambda>s. (\<forall>slot \<in> set slots. real_cte_at slot s)
                \<and> (\<forall>x \<in> set caps. s \<turnstile> fst x
                                \<and> cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                                \<and> real_cte_at (snd x) s))
         and K ((\<forall>cap \<in> set caps. is_subject aag (fst (snd cap)))
              \<and> (\<forall>slot \<in> set slots. is_subject aag (fst slot))
              \<and> (\<not> is_subject aag receiver \<longrightarrow>
                           auth_ipc_buffers st receiver = ptr_range buffer msg_align_bits)
              \<and> is_aligned buffer msg_align_bits
              \<and> n + length caps < 6 \<and> distinct slots)\<rbrace>
     transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp transfer_caps_loop_pres_dest cap_inserintegrity_in_ipc_autarch
            set_extra_badge_respects_in_ipc
       | simp
       | simp add: msg_align_bits buffer_cptr_index_def msg_max_length_def
       | blast)+
  apply (auto simp: cte_wp_at_caps_of_state)
  done

lemma transfer_caps_respects_in_ipc:
  "\<lbrace>pas_refined aag
         and integrity_tcb_in_ipc aag X receiver epptr TRContext st
         and valid_objs and valid_mdb
         and tcb_at receiver
         and (\<lambda>s. (\<forall>x \<in> set caps. s \<turnstile> fst x)
                \<and> (\<forall>x \<in> set caps. cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                                \<and> real_cte_at (snd x) s))
         and K ((\<not> null caps \<longrightarrow> is_subject aag receiver)
              \<and> (\<forall>cap \<in> set caps. is_subject aag (fst (snd cap)))
              \<and> (\<not> is_subject aag receiver \<longrightarrow>
                      case_option True (\<lambda>buf'. auth_ipc_buffers st receiver
                                             = ptr_range buf' msg_align_bits) recv_buf)
              \<and> (case_option True (\<lambda>buf'. is_aligned buf' msg_align_bits) recv_buf)
              \<and> length caps < 6)\<rbrace>
     transfer_caps mi caps endpoint receiver recv_buf
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases recv_buf)
   apply (simp add: transfer_caps_def, wp, simp)
  apply (cases caps)
   apply (simp add: transfer_caps_def del: get_receive_slots.simps, wp, simp)
  apply (simp add: transfer_caps_def del: get_receive_slots.simps)
  apply (wp transfer_caps_loop_respects_in_ipc_autarch
            get_receive_slots_authorised
            hoare_vcg_all_lift
       | wpc
       | rule hoare_drop_imps
       | simp add: null_def del: get_receive_slots.simps)+
  done

lemma copy_mrs_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
        and K ((\<not> is_subject aag receiver \<longrightarrow>
                      case_option True (\<lambda>buf'. auth_ipc_buffers st receiver
                                             = ptr_range buf' msg_align_bits) rbuf)
              \<and> (case_option True (\<lambda>buf'. is_aligned buf' msg_align_bits) rbuf)
              \<and> unat n < 2 ^ (msg_align_bits - 2))\<rbrace>
     copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  unfolding copy_mrs_def
  apply (rule hoare_gen_asm)
  apply (wp as_user_respects_in_ipc store_word_offs_respects_in_ipc
            mapM_wp'
            hoare_vcg_const_imp_lift hoare_vcg_all_lift
       | wpc
       | fastforce split: if_split_asm)+
  done

lemma do_normal_transfer_respects_in_ipc:
  notes lec_valid_cap[wp del]
  shows
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
         and pas_refined aag
         and valid_objs and valid_mdb
         and st_tcb_at can_receive_ipc receiver
         and (\<lambda>s. grant \<longrightarrow> is_subject aag sender
                         \<and> is_subject aag receiver)
         and K ((\<not> is_subject aag receiver \<longrightarrow>
                      (case recv_buf of None \<Rightarrow> True
                                      | Some buf' \<Rightarrow> auth_ipc_buffers st receiver
                                                   = ptr_range buf' msg_align_bits)) \<and>
                (case recv_buf of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits))\<rbrace>
     do_normal_transfer sender sbuf epopt badge grant receiver recv_buf
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: do_normal_transfer_def)
  apply (wp as_user_respects_in_ipc set_message_info_respects_in_ipc
            transfer_caps_respects_in_ipc copy_mrs_respects_in_ipc get_mi_valid'
            lookup_extra_caps_authorised lookup_extra_caps_length get_mi_length
            hoare_vcg_const_Ball_lift hoare_vcg_conj_lift_R hoare_vcg_const_imp_lift
            lec_valid_cap'
       | rule hoare_drop_imps
       | simp)+
  apply (auto simp: null_def intro: st_tcb_at_tcb_at)
  done

lemma set_mrs_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and
    K ((\<not> is_subject aag receiver \<longrightarrow> (case recv_buf of None \<Rightarrow> True | Some buf' \<Rightarrow> auth_ipc_buffers st receiver = ptr_range buf' msg_align_bits)) \<and>
       (case recv_buf of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits))\<rbrace>
     set_mrs receiver recv_buf msgs
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  unfolding set_mrs_def set_object_def get_object_def
  apply (rule hoare_gen_asm)
  apply (wp mapM_x_wp' store_word_offs_respects_in_ipc
       | wpc
       | simp split del: if_split add: zipWithM_x_mapM_x split_def)+
   apply (clarsimp simp add: set_zip nth_append simp: msg_align_bits msg_max_length_def
                   split: if_split_asm)
   apply (simp add: msg_registers_def msgRegisters_def upto_enum_def fromEnum_def enum_register)
   apply arith
   apply simp
   apply wp+
  apply (clarsimp simp: arch_tcb_set_registers_def)
  by (rule update_tcb_context_in_ipc [unfolded fun_upd_def]; fastforce)

lemma do_fault_transfer_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and
    K ((\<not> is_subject aag receiver \<longrightarrow> (case recv_buf of None \<Rightarrow> True | Some buf' \<Rightarrow> auth_ipc_buffers st receiver = ptr_range buf' msg_align_bits)) \<and>
       (case recv_buf of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits))\<rbrace>
    do_fault_transfer badge sender receiver recv_buf
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: do_fault_transfer_def split_def)
  apply (wp as_user_respects_in_ipc set_message_info_respects_in_ipc set_mrs_respects_in_ipc
       | wpc
       | simp
       | rule hoare_drop_imps)+
  done

lemma lookup_ipc_buffer_ptr_range_in_ipc:
  "\<lbrace>valid_objs and integrity_tcb_in_ipc aag X thread epptr tst st\<rbrace>
  lookup_ipc_buffer True thread
  \<lbrace>\<lambda>rv s. \<not> is_subject aag thread \<longrightarrow>
         (case rv of None \<Rightarrow> True
                   | Some buf' \<Rightarrow> auth_ipc_buffers st thread = ptr_range buf' msg_align_bits) \<rbrace>"
  unfolding lookup_ipc_buffer_def
  apply (rule hoare_pre)
  apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_auth_def get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (clarsimp simp: auth_ipc_buffers_def get_tcb_ko_at [symmetric] integrity_tcb_in_ipc_def)
  apply (drule get_tcb_SomeD)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def case_bool_if
                 split: if_split_asm)
  apply (erule tcb_in_ipc.cases; clarsimp simp: get_tcb_def vm_read_write_def)
  done

lemma lookup_ipc_buffer_aligned:
  "\<lbrace>valid_objs\<rbrace>
  lookup_ipc_buffer True thread
  \<lbrace>\<lambda>rv s. (case rv of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits) \<rbrace>"
  unfolding lookup_ipc_buffer_def
  apply (rule hoare_pre)
   apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (frule (1) caps_of_state_valid_cap)
  apply (clarsimp simp: valid_cap_simps cap_aligned_def)
  apply (erule aligned_add_aligned)
    apply (rule is_aligned_andI1)
    apply (drule (1) valid_tcb_objs)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def
                   split: if_splits)
  apply (rule order_trans [OF _ pbfs_atleast_pageBits])
  apply (simp add: msg_align_bits pageBits_def)
  done

lemma do_ipc_transfer_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
         and pas_refined aag
         and valid_objs and valid_mdb
         and st_tcb_at can_receive_ipc receiver
         and (\<lambda>s. grant \<longrightarrow> is_subject aag sender
                         \<and> is_subject aag receiver)
         \<rbrace>
     do_ipc_transfer sender epopt badge grant receiver
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: do_ipc_transfer_def)
  apply (wp do_normal_transfer_respects_in_ipc do_fault_transfer_respects_in_ipc
            lookup_ipc_buffer_ptr_range_in_ipc lookup_ipc_buffer_aligned
            hoare_vcg_conj_lift
       | wpc
       | simp
       | rule hoare_drop_imps)+
  apply (auto intro: st_tcb_at_tcb_at)
  done


lemma sts_ext_running_noop:
  "\<lbrace>P and st_tcb_at (runnable) receiver\<rbrace> set_thread_state_ext receiver \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: set_thread_state_ext_def get_thread_state_def thread_get_def
        | wp set_scheduler_action_wp)+
  apply (clarsimp simp add: st_tcb_at_def obj_at_def get_tcb_def)
  done

lemma set_thread_state_running_respects_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st and st_tcb_at(receive_blocked_on epptr) receiver and K(aag_has_auth_to aag SyncSend epptr)\<rbrace>
     set_thread_state receiver Structures_A.thread_state.Running
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRFinalOrCall st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp sts_ext_running_noop)
  apply (auto simp: st_tcb_at_def obj_at_def get_tcb_def
                    get_tcb_rev update_tcb_state_in_ipc
              cong: if_cong
              elim: update_tcb_state_in_ipc[unfolded fun_upd_def])
  done

lemma set_endpoinintegrity_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
          and K (aag_has_auth_to aag SyncSend epptr)\<rbrace>
    set_endpoint epptr ep'
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRContext st\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: Structures_A.kernel_object.splits
                  simp: obj_at_def is_tcb is_ep integrity_tcb_in_ipc_def
                        partial_inv_def a_type_def)
  apply (intro impI conjI)
    apply (erule integrity_trans)
    apply (clarsimp simp: integrity_def)
   apply clarsimp
   apply (erule tcb_in_ipc.cases, simp_all)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  apply (fastforce intro: tro_ep)
  done

(* FIXME: move *)
lemma valid_ep_recv_dequeue:
  "\<lbrakk> ko_at (Endpoint (Structures_A.endpoint.RecvEP (t # ts))) epptr s;
     valid_objs s; sym_refs (state_refs_of s) \<rbrakk>
     \<Longrightarrow> valid_ep (case ts of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                            | b # bs \<Rightarrow> Structures_A.endpoint.RecvEP ts) s"
  unfolding valid_objs_def valid_obj_def valid_ep_def obj_at_def
  apply (drule bspec)
  apply (auto split: list.splits)
  done

lemma integrity_tcb_in_ipc_refl:
  "\<lbrakk> st_tcb_at can_receive_ipc receiver s; \<not> is_subject aag receiver; pas_refined aag s\<rbrakk>
  \<Longrightarrow> integrity_tcb_in_ipc aag X receiver epptr TRContext s s"
  unfolding integrity_tcb_in_ipc_def
  apply (clarsimp simp: st_tcb_def2)
  apply (rule tii_context [OF get_tcb_SomeD get_tcb_SomeD], assumption+)
    apply (rule tcb_context_no_change)
   apply simp
  done

(* stronger *)
(* MOVE *)
lemma ep_queued_st_tcb_at'':
  "\<And>P. \<lbrakk>ko_at (Endpoint ep) ptr s; (t, rt) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>pl pl'. (rt = EPSend \<and> P (Structures_A.BlockedOnSend ptr pl)) \<or>
                  (rt = EPRecv \<and> P (Structures_A.BlockedOnReceive ptr pl')) \<rbrakk>
    \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac ep, simp_all)
  apply (frule (1) sym_refs_ko_atD, fastforce simp: st_tcb_at_def obj_at_def refs_of_rev)+
  done

subsubsection \<open>Inserting the reply cap\<close>

lemma integrity_tcb_in_ipc_no_call:
  "integrity_tcb_in_ipc aag X receiver epptr TRFinalOrCall st s
   \<Longrightarrow> integrity_tcb_in_ipc aag X receiver epptr TRFinal st s"
  unfolding integrity_tcb_in_ipc_def tcb_in_ipc.simps by clarsimp

lemma set_original_respects_in_ipc_reply:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st
          and K(st_tcb_at (\<lambda>st. direct_call {pasSubject aag} aag epptr st) receiver st)\<rbrace>
     set_original (receiver, tcb_cnode_index 3) orig
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (wp set_original_wp)
  apply (clarsimp simp: integrity_tcb_in_ipc_def)
  apply (simp add: integrity_def tcb_states_of_state_def get_tcb_def
              split del: if_split cong: if_cong)
  apply (fold get_tcb_def tcb_states_of_state_def)
  apply (clarsimp simp:st_tcb_at_tcb_states_of_state)
  apply (rule integrity_cdt_change_allowed)
  apply (rule cca_reply; force)
  done

lemma cap_insert_ext_integrity_in_ipc_reply:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st
       and K(is_subject aag (fst src_slot)
           \<and> st_tcb_at (\<lambda>st. direct_call {pasSubject aag} aag epptr st) receiver st)\<rbrace>
    cap_insert_ext src_parent src_slot (receiver, tcb_cnode_index 3) src_p dest_p
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: integrity_tcb_in_ipc_def split del: if_split)
  apply (unfold integrity_def)
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (clarsimp simp: integrity_tcb_in_ipc_def integrity_def
                        tcb_states_of_state_def get_tcb_def
             split del: if_split cong: if_cong)
  apply wp
   apply (simp add: list_integ_def del: split_paired_All)
   apply (fold list_integ_def get_tcb_def tcb_states_of_state_def)
   apply (wp cap_insert_list_integrity)
   apply simp
   apply (simp add: list_integ_def del: split_paired_All)
   apply (fold list_integ_def get_tcb_def tcb_states_of_state_def)
   apply (clarsimp simp: st_tcb_at_tcb_states_of_state)
   apply (rule cca_reply; force)
  done

lemma update_cdt_wp:
  "\<lbrace>\<lambda>s.  P (s\<lparr> cdt := f (cdt s) \<rparr>)\<rbrace>
     update_cdt f
   \<lbrace>\<lambda>_. P \<rbrace>"
  by (wpsimp simp: update_cdt_def set_cdt_def)

lemma update_cdt_reply_in_ipc:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st
       and K(st_tcb_at (\<lambda>st. direct_call {pasSubject aag} aag epptr st) receiver st)\<rbrace>
    update_cdt (\<lambda>cdt. cdt ((receiver, tcb_cnode_index 3) := val cdt))
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (wp update_cdt_wp)
  apply (clarsimp simp: integrity_tcb_in_ipc_def)
  apply (simp add: integrity_def tcb_states_of_state_def get_tcb_def
              split del: if_split cong: if_cong)
  apply (fold get_tcb_def tcb_states_of_state_def)
  apply (clarsimp simp:st_tcb_at_tcb_states_of_state)
  apply (rule integrity_cdt_change_allowed)
  apply (rule cca_reply; force)
  done

(* FIXME: move to NondetMonad *)
lemma spec_valid_direct:
  "\<lbrakk> P s \<Longrightarrow> s \<turnstile> \<lbrace> \<top> \<rbrace> f \<lbrace> Q \<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace> Q \<rbrace>"
  by (simp add: spec_valid_def valid_def)

lemma set_cap_respects_in_ipc_reply:
   "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRFinalOrCall st
     and K(st_tcb_at (\<lambda>st. direct_call {pasSubject aag} aag epptr st) receiver st
           \<and> is_subject aag caller)\<rbrace>
      set_cap (ReplyCap caller False R) (receiver, tcb_cnode_index 3)
    \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRFinal st\<rbrace>"
  unfolding set_cap_def
  apply simp
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  including no_pre
  apply (wp set_object_wp)
  apply (rule use_spec')
  apply (rule spec_valid_direct)
  apply (clarsimp simp:tcb_at_def get_tcb_def dest!:ko_atD split:kernel_object.splits)
  apply (simp add: spec_valid_def valid_def return_def)
  unfolding integrity_tcb_in_ipc_def
  apply (clarsimp simp:st_tcb_at_tcb_states_of_state )
  apply (clarsimp simp:tcb_states_of_state_def direct_call_def dest!:get_tcb_SomeD)
  by (erule tcb_in_ipc.cases; (force intro:tii_call))


lemma cap_insert_reply_cap_respects_in_ipc:
  "\<lbrace> integrity_tcb_in_ipc aag X receiver epptr TRFinalOrCall st and
    K (st_tcb_at (direct_call {pasSubject aag} aag epptr) receiver st \<and>
       is_subject aag caller \<and> is_subject aag (fst master_slot))\<rbrace>
    cap_insert
          (ReplyCap caller False R)
          master_slot (receiver, tcb_cnode_index 3)
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr TRFinal st\<rbrace>"
  unfolding cap_insert_def
  apply (rule hoare_pre)
  apply (wp add:set_original_respects_in_ipc_reply)
  apply simp
  apply (wp cap_insert_ext_integrity_in_ipc_reply update_cdt_reply_in_ipc
            set_cap_respects_in_ipc_reply set_untyped_cap_as_full_not_untyped get_cap_wp)+
  by fastforce

lemma set_scheduler_action_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>
    set_scheduler_action action
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
   unfolding set_scheduler_action_def
   by (wpsimp simp: integrity_tcb_in_ipc_def integrity_def tcb_states_of_state_def get_tcb_def)

lemma exists_cons_append:
  "\<exists>xs. xs @ ys = zs \<Longrightarrow> \<exists>xs. xs @ ys = z # zs"
  by auto

lemma tcb_sched_action_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>
      tcb_sched_action tcb_sched_enqueue target
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_tcb_in_ipc_def tcb_states_of_state_def get_tcb_def
                        integrity_ready_queues_def pas_refined_def tcb_domain_map_wellformed_aux_def
                        tcb_at_def get_etcb_def tcb_sched_enqueue_def etcb_at_def
                 split: option.splits)
  apply (fastforce intro: exists_cons_append)
  done


crunches possible_switch_to, set_thread_state for respects_in_ipc_autarch: "integrity_tcb_in_ipc aag X receiver epptr ctxt st"
  (wp: tcb_sched_action_respects_in_ipc_autarch ignore:tcb_sched_action )

lemma setup_caller_cap_respects_in_ipc_reply:
  "\<lbrace> integrity_tcb_in_ipc aag X receiver epptr TRFinalOrCall st
      and K (is_subject aag sender \<and> st_tcb_at (direct_call {pasSubject aag} aag epptr) receiver st) \<rbrace>
   setup_caller_cap sender receiver grant
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr TRFinal st \<rbrace>"
  unfolding setup_caller_cap_def
  by (wpsimp wp: cap_insert_reply_cap_respects_in_ipc set_thread_state_respects_in_ipc_autarch)


lemma send_ipc_integrity_autarch:
  "\<lbrace>integrity aag X st and pas_refined aag
          and invs
          and is_subject aag \<circ> cur_thread
          and obj_at (\<lambda>ep. can_grant \<longrightarrow> (\<forall>r \<in> refs_of ep. snd r = EPRecv \<longrightarrow> is_subject aag (fst r))) epptr
          and K (is_subject aag sender \<and> aag_has_auth_to aag SyncSend epptr \<and>
                (can_grant_reply \<longrightarrow> aag_has_auth_to aag Call epptr))\<rbrace>
     send_ipc block call badge can_grant can_grant_reply sender epptr
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac ep)
    \<comment> \<open>IdleEP\<close>
    apply simp
    apply (rule hoare_pre)
     apply (wp set_endpoinintegrity  set_thread_state_integrity_autarch
                 | wpc | simp)+
    apply (fastforce simp: obj_at_def is_ep) \<comment> \<open>ep_at and has_auth\<close>
   \<comment> \<open>SendEP\<close>
   apply simp
   apply (rule hoare_pre)
    apply (wp set_endpoinintegrity  set_thread_state_integrity_autarch
               | wpc | simp)+
   apply (fastforce simp: obj_at_def is_ep) \<comment> \<open>ep_at and has_auth\<close>
  \<comment> \<open>WaitingEP\<close>
  apply (rename_tac list)
  apply simp
  apply (case_tac "is_subject aag (hd list)") \<comment> \<open>autarch or not on receiver side\<close>
   apply clarsimp
   apply (rule hoare_pre)
    apply (wp setup_caller_cap_integrity_autarch set_thread_state_integrity_autarch thread_get_wp'
                  | wpc)+
          apply (rule_tac Q="\<lambda>rv s. integrity aag X st s\<and> (can_grant \<longrightarrow> is_subject aag (hd list))"
                       in hoare_strengthen_post[rotated])
          apply simp+
          apply (wp set_thread_state_integrity_autarch thread_get_wp'
                    do_ipc_transfer_integrity_autarch
                    hoare_vcg_all_lift hoare_drop_imps set_endpoinintegrity
                   | wpc | simp add: get_thread_state_def split del: if_split
                                del: hoare_True_E_R)+
   apply (fastforce simp: a_type_def obj_at_def is_ep elim: send_ipc_valid_ep_helper)
  \<comment> \<open>we don't own head of queue\<close>
  apply clarsimp
  apply (rule use_spec') \<comment> \<open>Name initial state\<close>
  apply (simp add: spec_valid_def) \<comment> \<open>no imp rule?\<close>
  apply (rule hoare_pre)
   apply (wpc, wp)
   apply (rename_tac list s receiver queue)
   apply (rule_tac Q =  "\<lambda>_ s'. integrity aag X st s \<and>
                         integrity_tcb_in_ipc aag X receiver epptr TRFinal s s'" in hoare_post_imp)
    apply (fastforce dest!: integrity_tcb_in_ipc_final elim!: integrity_trans)
   apply (wp setup_caller_cap_respects_in_ipc_reply
             set_thread_state_respects_in_ipc_autarch[where param_b = Inactive]
             hoare_vcg_if_lift static_imp_wp possible_switch_to_respects_in_ipc_autarch
             set_thread_state_running_respects_in_ipc do_ipc_transfer_respects_in_ipc thread_get_inv
             set_endpoinintegrity_in_ipc
          | wpc
          | strengthen integrity_tcb_in_ipc_no_call
          | wp hoare_drop_imps
          | simp add:get_thread_state_def)+

  apply (clarsimp intro:integrity_tcb_in_ipc_refl)
  apply (frule_tac t=x in sym_ref_endpoint_recvD[OF invs_sym_refs],assumption,simp)
  apply (clarsimp simp:st_tcb_at_tcb_states_of_state_eq st_tcb_at_tcb_states_of_state direct_call_def)
  apply (subgoal_tac "\<not> can_grant")
   apply (force intro!: integrity_tcb_in_ipc_refl
                  simp: st_tcb_at_tcb_states_of_state
                  elim: send_ipc_valid_ep_helper)
  apply (force elim:obj_at_ko_atE)
  done

section\<open>Faults\<close>

(* FIXME: move *)
lemma valid_tcb_fault_update:
  "\<lbrakk> valid_tcb p t s; valid_fault fault \<rbrakk> \<Longrightarrow> valid_tcb p (t\<lparr>tcb_fault := Some fault\<rparr>) s"
  by (simp add: valid_tcb_def ran_tcb_cap_cases)

lemma thread_set_fault_pas_refined:
  "\<lbrace>pas_refined aag\<rbrace>
     thread_set (tcb_fault_update (\<lambda>_. Some fault)) thread
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (wp send_ipc_pas_refined thread_set_pas_refined
            thread_set_refs_trivial thread_set_obj_at_impossible
       | simp)+
  done

lemma owns_ep_owns_receivers':
  "\<lbrakk> (\<forall>auth. aag_has_auth_to aag auth epptr); pas_refined aag s; valid_objs s;
     sym_refs (state_refs_of s); ko_at (Endpoint ep) epptr s; (t, EPRecv) \<in> ep_q_refs_of ep\<rbrakk>
  \<Longrightarrow> is_subject aag t"
  apply (drule (1) ep_rcv_queued_st_tcb_at [where P = "receive_blocked_on epptr"])
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply (rule refl)
  apply (drule st_tcb_at_to_thread_states)
  apply (clarsimp simp: receive_blocked_on_def2)
  apply (drule spec [where x = Grant])
  apply (frule aag_wellformed_grant_Control_to_recv [OF _ _ pas_refined_wellformed])
    apply (rule pas_refined_mem [OF sta_ts])
     apply fastforce
    apply assumption
   apply assumption
  apply (erule (1) aag_Control_into_owns)
  done

lemma send_fault_ipc_pas_refined:
  "\<lbrace>pas_refined aag
         and invs
         and is_subject aag \<circ> cur_thread
         and K (valid_fault fault)
         and K (is_subject aag thread)\<rbrace>
     send_fault_ipc thread fault
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: send_fault_ipc_def Let_def lookup_cap_def split_def)
  apply (wp send_ipc_pas_refined thread_set_fault_pas_refined thread_set_tcb_fault_set_invs
            thread_set_refs_trivial thread_set_obj_at_impossible
            get_cap_wp thread_set_valid_objs''
            hoare_vcg_conj_lift hoare_vcg_ex_lift hoare_vcg_all_lift
       | wpc
       | rule hoare_drop_imps
       | simp add: split_def split del: if_split)+
    apply (rule_tac Q'="\<lambda>rv s. pas_refined aag s
                            \<and> is_subject aag (cur_thread s)
                            \<and> invs s
                            \<and> valid_fault fault
                            \<and> is_subject aag (fst (fst rv))"
                 in hoare_post_imp_R[rotated])
     apply (fastforce dest!: cap_auth_caps_of_state
                       simp: invs_valid_objs invs_sym_refs cte_wp_at_caps_of_state aag_cap_auth_def
                             cap_auth_conferred_def cap_rights_to_auth_def AllowSend_def)
    apply (wp get_cap_auth_wp[where aag=aag] lookup_slot_for_thread_authorised
          | simp add: lookup_cap_def split_def)+
  done

lemma handle_fault_pas_refined:
  "\<lbrace>pas_refined aag
          and invs
          and is_subject aag \<circ> cur_thread
          and K (valid_fault fault)
          and K (is_subject aag thread)\<rbrace>
     handle_fault thread fault
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: handle_fault_def)
  apply (wp set_thread_state_pas_refined send_fault_ipc_pas_refined
        | simp add: handle_double_fault_def)+
  done



lemma thread_set_tcb_fault_update_valid_mdb:
  "\<lbrace>valid_mdb\<rbrace>
     thread_set (tcb_fault_update (\<lambda>_. Some fault)) thread
          \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  apply(rule thread_set_mdb)
  apply(clarsimp simp: tcb_cap_cases_def)
  apply auto
  done


(* FIXME: MOVE *)
lemma obj_at_conj_distrib:
  "obj_at (\<lambda>ko. P ko \<and> Q ko) p s = (obj_at (\<lambda>ko. P ko) p s \<and> obj_at (\<lambda>ko. Q ko) p s)"
  by (auto simp: obj_at_def)

lemma send_fault_ipc_integrity_autarch:
  "\<lbrace>pas_refined aag
          and invs
          and integrity aag X st
          and is_subject aag \<circ> cur_thread
          and K (valid_fault fault)
          and K (is_subject aag thread)\<rbrace>
     send_fault_ipc thread fault
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: send_fault_ipc_def Let_def)
  apply (wp send_ipc_integrity_autarch
            thread_set_integrity_autarch thread_set_fault_pas_refined
            thread_set_valid_objs'' thread_set_refs_trivial
            thread_set_tcb_fault_update_valid_mdb
            thread_set_tcb_fault_set_invs
        | wpc
        | simp add: is_obj_defs)+
  (* 14 subgoals *)
  apply (rename_tac word1 word2 set)
  apply (rule_tac R="\<lambda>rv s. ep_at word1 s" in hoare_post_add)
  apply (simp only: obj_at_conj_distrib[symmetric] flip: conj_assoc)
  apply (wp thread_set_obj_at_impossible thread_set_tcb_fault_set_invs
            get_cap_auth_wp[where aag=aag]
        | simp add: lookup_cap_def is_obj_defs split_def)+
  (* down to 3 : normal indentation *)
    apply (rule_tac Q'="\<lambda>rv s. integrity aag X st s \<and> pas_refined aag s
                          \<and> invs s
                          \<and> valid_fault fault
                          \<and> is_subject aag (cur_thread s)
                          \<and> is_subject aag (fst (fst rv))"
               in hoare_post_imp_R[rotated])
     apply (clarsimp simp: invs_valid_objs invs_sym_refs cte_wp_at_caps_of_state obj_at_def)

     apply (frule(1) caps_of_state_valid)
     apply (clarsimp simp: valid_cap_def  is_ep aag_cap_auth_def cap_auth_conferred_def
                           cap_rights_to_auth_def AllowSend_def
                    elim!: obj_atE)

     apply (intro conjI ; fastforce ?)
     apply (clarsimp simp:ep_q_refs_of_def split:endpoint.splits)
     apply (frule(1) pas_refined_ep_recv, simp add:obj_at_def,assumption)
     apply (frule(1) aag_wellformed_grant_Control_to_recv[OF _ _ pas_refined_wellformed,rotated],
            blast)
     apply (simp add:aag_has_auth_to_Control_eq_owns)

    apply (wp lookup_slot_for_thread_authorised)+
  apply simp
  done

lemma handle_fault_integrity_autarch:
  "\<lbrace>pas_refined aag
         and integrity aag X st
         and is_subject aag \<circ> cur_thread
         and invs
         and K (valid_fault fault)
         and K (is_subject aag thread)\<rbrace>
     handle_fault thread fault
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: handle_fault_def)
  apply (wp set_thread_state_integrity_autarch send_fault_ipc_integrity_autarch
       | simp add: handle_double_fault_def)+
  done

section\<open>Replies\<close>

crunch pas_refined[wp]: handle_fault_reply "pas_refined aag"

lemma handle_fault_reply_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
     handle_fault_reply fault thread x y
    \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (cases fault, simp_all)
  apply (wp as_user_integrity_autarch
        | simp add: handle_arch_fault_reply_def arch_get_sanitise_register_info_def)+
  done

lemma tcb_st_to_auth_Restart_Inactive [simp]:
  "tcb_st_to_auth (if P then Restart else Inactive) = {}"
  by simp


lemma do_reply_transfer_pas_refined:
  "\<lbrace>pas_refined aag
         and invs and K (is_subject aag sender)
         and K ((grant \<longrightarrow> is_subject aag receiver) \<and> is_subject aag (fst slot))\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (rule hoare_pre)
  apply (wp set_thread_state_pas_refined do_ipc_transfer_pas_refined
            thread_set_pas_refined K_valid
       | wpc
       | simp add: thread_get_def split del: if_split)+
  (* otherwise simp does too much *)
  apply (rule hoare_strengthen_post, rule gts_inv)
   apply (rule impI)
   apply assumption
  apply auto
  done

lemma update_tcb_state_in_ipc_reply:
  "\<lbrakk> integrity_tcb_in_ipc aag X thread epptr TRContext st s;
     tcb_state tcb = BlockedOnReply; aag_has_auth_to aag Reply thread; tcb_fault tcb = None;
     get_tcb thread s = Some tcb; tcb' = tcb\<lparr>tcb_state := Structures_A.thread_state.Running\<rparr>
   \<rbrakk> \<Longrightarrow>
   integrity_tcb_in_ipc aag X thread epptr TRFinal st
                        (s \<lparr> kheap := (kheap s)(thread \<mapsto> TCB tcb') \<rparr>)"
  unfolding integrity_tcb_in_ipc_def
  apply (elim conjE)
  apply (intro conjI)
    apply assumption+
   apply (erule integrity_trans)
   apply (simp cong: if_cong)
  apply clarsimp
  apply (erule tcb_in_ipc.cases, simp_all)
  apply (drule get_tcb_SomeD)
  apply (rule tii_reply[OF refl refl])
     apply (elim exE, intro exI tcb.equality; solves \<open>simp\<close>)
    apply auto
  done


abbreviation "fault_tcb_at \<equiv> pred_tcb_at itcb_fault"

lemma fault_tcb_atI:
  "\<lbrakk>kheap s ptr = Some (TCB tcb); P (tcb_fault tcb) \<rbrakk> \<Longrightarrow> fault_tcb_at P ptr s"
  by (fastforce simp:pred_tcb_at_def obj_at_def)

lemma fault_tcb_atE:
  assumes hyp:"fault_tcb_at P ptr s"
  obtains tcb where "kheap s ptr = Some (TCB tcb)" and "P (tcb_fault tcb)"
  using hyp by (fastforce simp:pred_tcb_at_def elim: obj_atE)

lemma set_thread_state_running_respects_in_ipc_reply:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr TRContext st
      and st_tcb_at awaiting_reply receiver
      and fault_tcb_at ((=) None) receiver
      and K (aag_has_auth_to aag Reply receiver)\<rbrace>
     set_thread_state receiver Structures_A.thread_state.Running
   \<lbrace>\<lambda>rv. integrity_tcb_in_ipc aag X receiver epptr TRFinal st\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp sts_ext_running_noop)
  apply (auto simp: st_tcb_at_def obj_at_def get_tcb_def
              cong: if_cong
              elim!: fault_tcb_atE elim: update_tcb_state_in_ipc_reply[unfolded fun_upd_def])
  done

end

context is_extended begin

interpretation Arch . (*FIXME: arch_split*)

lemma list_integ_lift_in_ipc:
  assumes li:
   "\<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
       f
    \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag}  (cdt st) (tcb_states_of_state st)) st\<rbrace>"
  assumes ekh: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  assumes rq: "\<And>P. \<lbrace> \<lambda>s. P (ready_queues s) \<rbrace> f \<lbrace> \<lambda>rv s. P (ready_queues s) \<rbrace>"
  shows "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st and Q\<rbrace> f \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (unfold integrity_tcb_in_ipc_def integrity_def[abs_def])
  apply (simp del:split_paired_All)
  apply (rule hoare_pre)
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (rule hoare_lift_Pf2[where f="ekheap"])
    apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (wp li[simplified tcb_states_of_state_def get_tcb_def] ekh rq)+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

end

context begin interpretation Arch . (*FIXME: arch_split*)

lemma fast_finalise_reply_respects_in_ipc_autarch:
  "\<lbrace> integrity_tcb_in_ipc aag X receiver epptr ctxt st  and K (is_reply_cap cap) \<rbrace>
     fast_finalise cap final
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st \<rbrace>"
  by (rule hoare_gen_asm) (fastforce simp: is_cap_simps)

lemma empty_slot_list_integrity':
  notes split_paired_All[simp del]
  shows
  "\<lbrace>list_integ P st and (\<lambda>s . cdt_list s slot = []) and K(P slot)\<rbrace> empty_slot_ext slot slot_p \<lbrace>\<lambda>_. list_integ P st\<rbrace>"
  apply (simp add: empty_slot_ext_def split del: if_split)
  apply (wp update_cdt_list_wp)
  apply (intro impI conjI allI | simp add: list_filter_replace_list list_filter_remove split: option.splits | elim conjE  | simp add: list_integ_def)+
  done


lemma tcb_state_of_states_cdt_update_behind_kheap[simp]:
  "tcb_states_of_state (kheap_update g (cdt_update f s)) = tcb_states_of_state (kheap_update g s)"
  by (simp add:tcb_states_of_state_def get_tcb_def)

lemma set_cdt_empty_slot_respects_in_ipc_autarch:
  "\<lbrace> integrity_tcb_in_ipc aag X receiver epptr ctxt st and (\<lambda>s. m =cdt s)
     and (\<lambda>s. descendants_of slot m = {}) and K(is_subject aag (fst slot))\<rbrace>
      set_cdt ((\<lambda>p. if m p = Some slot then m slot else m p)(slot := None))
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st \<rbrace>"
  unfolding set_cdt_def
  apply wp
  apply (simp add: integrity_tcb_in_ipc_def integrity_def)
  apply (force simp:no_children_empty_desc[symmetric])
  done

lemma reply_cap_no_children':
  "\<lbrakk> valid_mdb s; caps_of_state s p = Some (ReplyCap t False r) \<rbrakk> \<Longrightarrow> \<forall>p' .cdt s p' \<noteq> Some p"
  using reply_cap_no_children ..

lemma valid_list_empty:
  "\<lbrakk> valid_list_2 list m; descendants_of slot m = {}\<rbrakk> \<Longrightarrow> list slot = []"
  unfolding valid_list_2_def
  apply (drule no_children_empty_desc[THEN iffD2])
  apply (rule classical)
  by (fastforce simp del:split_paired_All split_paired_Ex simp add:neq_Nil_conv)


lemma empty_slot_respects_in_ipc_autarch:
  "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st and valid_mdb and valid_list
    and cte_wp_at is_reply_cap slot and K (is_subject aag (fst slot))\<rbrace>
     empty_slot slot NullCap
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  unfolding empty_slot_def apply simp
  apply (wp add: set_cap_respects_in_ipc_autarch set_original_respects_in_ipc_autarch)
       apply (wp empty_slot_extended.list_integ_lift_in_ipc empty_slot_list_integrity')
          apply simp
         apply wp+
      apply (wp set_cdt_empty_slot_respects_in_ipc_autarch)
      apply (simp add: set_cdt_def)
      apply wp
     apply wp
    apply wp
   apply (wp get_cap_wp)
  apply (clarsimp simp: integrity_tcb_in_ipc_def cte_wp_at_caps_of_state is_cap_simps)
  apply (drule(1) reply_cap_no_children')
  by (force dest: valid_list_empty simp: no_children_empty_desc simp del: split_paired_All)

lemma cte_delete_one_respects_in_ipc_autharch:
  "\<lbrace> integrity_tcb_in_ipc aag X receiver epptr ctxt st and valid_mdb and valid_list and
       cte_wp_at is_reply_cap slot and K (is_subject aag (fst slot)) \<rbrace>
     cap_delete_one slot
   \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st \<rbrace>"
  unfolding cap_delete_one_def
  apply (wp empty_slot_respects_in_ipc_autarch
            fast_finalise_reply_respects_in_ipc_autarch get_cap_wp)
  by (fastforce simp:cte_wp_at_caps_of_state is_cap_simps)



text \<open>The special case of fault reply need a different machinery than *_in_ipc stuff because,
        there is no @{term underlying_memory} modification\<close>

datatype tcb_respects_fault_state = TRFContext | TRFRemoveFault | TRFFinal

inductive tcb_in_fault_reply for aag tst l' ko ko'
where
  tifr_lrefl: "\<lbrakk> l' = pasSubject aag \<rbrakk> \<Longrightarrow> tcb_in_fault_reply aag tst l' ko ko'"
| tifr_context: "\<lbrakk> ko  = Some (TCB tcb);
                  ko' = Some (TCB tcb');
                  \<exists>ctxt'. tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb)\<rparr>;
                  (pasSubject aag, Reply, l') \<in> pasPolicy aag;
                  tcb_state tcb = BlockedOnReply;
                  tcb_fault tcb = Some fault;
                  tst = TRFContext\<rbrakk>
        \<Longrightarrow> tcb_in_fault_reply aag tst l' ko ko'"
| tifr_remove_fault: "\<lbrakk> ko  = Some (TCB tcb);
                   ko' = Some (TCB tcb');
                   \<exists>ctxt'. tcb' = tcb \<lparr> tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb)
                                   , tcb_fault := None\<rparr>;
                   (pasSubject aag, Reply, l') \<in> pasPolicy aag;
                   tcb_state tcb = BlockedOnReply;
                   tcb_fault tcb = Some fault;
                   tst = TRFRemoveFault\<rbrakk>
         \<Longrightarrow> tcb_in_fault_reply aag tst l' ko ko'"
| tifr_reply:  "\<lbrakk> ko  = Some (TCB tcb);
                ko' = Some (TCB tcb');
                \<exists>ctxt'. tcb' = tcb \<lparr> tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                                     tcb_fault := None,
                                     tcb_state := new_st\<rparr>;
                new_st = Structures_A.Restart \<or> new_st = Structures_A.Inactive;
                (pasSubject aag, Reply, l') \<in> pasPolicy aag;
                tcb_state tcb = BlockedOnReply;
                tcb_fault tcb = Some fault;
                tst = TRFFinal\<rbrakk>
         \<Longrightarrow> tcb_in_fault_reply aag tst l' ko ko'"

definition integrity_tcb_in_fault_reply ::
  "'a PAS \<Rightarrow> obj_ref set \<Rightarrow> obj_ref \<Rightarrow> tcb_respects_fault_state \<Rightarrow> det_ext state
    \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "integrity_tcb_in_fault_reply aag X thread tst st \<equiv> \<lambda>s.
     \<not> is_subject aag thread \<and> pas_refined aag st \<and> \<comment> \<open>more or less convenience\<close>
     (integrity aag X st (s\<lparr>kheap := (kheap s)(thread := kheap st thread)\<rparr>)
   \<and> (tcb_in_fault_reply aag tst (pasObjectAbs aag thread) (kheap st thread) (kheap s thread)))"

lemma integrity_tcb_in_fault_reply_final:
  "\<lbrakk> integrity_tcb_in_fault_reply aag X thread TRFFinal st s \<rbrakk> \<Longrightarrow> integrity aag X st s"
  unfolding integrity_tcb_in_fault_reply_def
  apply clarsimp
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  apply (erule tcb_in_fault_reply.cases; clarsimp)
  apply (fastforce intro!:tcb.equality tro_tcb_reply)
  done

lemma set_scheduler_action_respects_in_fault_reply:
  "\<lbrace>integrity_tcb_in_fault_reply aag X receiver ctxt st\<rbrace>
    set_scheduler_action action
   \<lbrace>\<lambda>_. integrity_tcb_in_fault_reply aag X receiver ctxt st\<rbrace>"
  unfolding set_scheduler_action_def
  by (wpsimp simp: integrity_tcb_in_fault_reply_def integrity_def
                   tcb_states_of_state_def get_tcb_def)

crunches set_thread_state_ext
  for respects_in_fault_reply:"integrity_tcb_in_fault_reply aag X receiver ctxt st"

lemma as_user_respects_in_fault_reply:
  "\<lbrace>integrity_tcb_in_fault_reply aag X thread TRFContext st\<rbrace>
     as_user thread m
   \<lbrace>\<lambda>rv. integrity_tcb_in_fault_reply aag X thread TRFContext st\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: integrity_tcb_in_fault_reply_def)
  apply (erule tcb_in_fault_reply.cases; clarsimp dest!: get_tcb_SomeD)
  apply (rule tifr_context[OF refl refl])
      apply (intro exI tcb.equality; simp add: arch_tcb_context_set_def)
  by fastforce+

lemma handle_fault_reply_respects_in_fault_reply:
  "\<lbrace>integrity_tcb_in_fault_reply aag X thread TRFContext st\<rbrace>
   handle_fault_reply f thread label mrs
   \<lbrace>\<lambda>_. integrity_tcb_in_fault_reply aag X thread TRFContext st\<rbrace>"
  by (cases f;
      wpsimp simp: handle_arch_fault_reply_def arch_get_sanitise_register_info_def
               wp: as_user_respects_in_fault_reply)

lemma thread_set_no_fault_respects_in_fault_reply:
  "\<lbrace>integrity_tcb_in_fault_reply aag X thread TRFContext st\<rbrace>
   thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) thread
   \<lbrace>\<lambda>_. integrity_tcb_in_fault_reply aag X thread TRFRemoveFault st\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_thread_state_ext_respects_in_fault_reply set_object_wp)
  apply (clarsimp simp: integrity_tcb_in_fault_reply_def)
  apply (erule tcb_in_fault_reply.cases; clarsimp dest!: get_tcb_SomeD)
  apply (rule tifr_remove_fault[OF refl refl])
      apply (intro exI tcb.equality ; simp add: arch_tcb_context_set_def)
  by fastforce+

lemma set_thread_state_respects_in_fault_reply:
  "tst = Restart \<or> tst = Inactive \<Longrightarrow>
   \<lbrace>integrity_tcb_in_fault_reply aag X thread TRFRemoveFault st\<rbrace>
   set_thread_state thread tst
   \<lbrace>\<lambda>_. integrity_tcb_in_fault_reply aag X thread TRFFinal st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp set_thread_state_ext_respects_in_fault_reply set_object_wp)
  apply (clarsimp simp: integrity_tcb_in_fault_reply_def)
  apply (erule tcb_in_fault_reply.cases; clarsimp dest!: get_tcb_SomeD)
  apply (rule tifr_reply[OF refl refl])
       apply (intro exI tcb.equality; simp add: arch_tcb_context_set_def)
  by fastforce+

lemma integrity_tcb_in_fault_reply_refl:
  "\<lbrakk> st_tcb_at awaiting_reply receiver s; fault_tcb_at (flip (\<noteq>) None) receiver s;
     aag_has_auth_to aag Reply receiver;
     \<not> is_subject aag receiver; pas_refined aag s \<rbrakk>
  \<Longrightarrow> integrity_tcb_in_fault_reply aag X receiver TRFContext s s"
  unfolding integrity_tcb_in_fault_reply_def
  apply (clarsimp elim!: pred_tcb_atE)
  apply (rule tifr_context[OF refl refl])
      apply (rule tcb_context_no_change)
     apply fastforce+
  done

lemma emptyable_not_master:
  "\<lbrakk> valid_objs s; caps_of_state s slot = Some cap; \<not> is_master_reply_cap cap\<rbrakk>
   \<Longrightarrow> emptyable slot s"
  apply (rule emptyable_cte_wp_atD[rotated 2])
    apply (intro allI impI, assumption)
   by (fastforce simp:is_cap_simps cte_wp_at_caps_of_state)+

lemma do_reply_transfer_respects:
  "\<lbrace>pas_refined aag
        and integrity aag X st
        and einvs \<comment> \<open>cap_delete_one\<close>
        and tcb_at sender
        and cte_wp_at (is_reply_cap_to receiver) slot
        and K (is_subject aag sender)
        and K (aag_has_auth_to aag Reply receiver)
        and K (is_subject aag (fst slot) \<and> (grant \<longrightarrow> is_subject aag receiver))\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: do_reply_transfer_def thread_get_def get_thread_state_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_sp];force?)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_sp];force?)
  apply wpc
    \<comment> \<open>No fault case\<close>
    apply (rule hoare_vcg_if_split[where P= "is_subject aag receiver" and f=f and g=f for f,
                                   simplified if_cancel])
     \<comment> \<open>receiver is a subject\<close>
     apply ((wp set_thread_state_integrity_autarch thread_set_integrity_autarch
                handle_fault_reply_respects do_ipc_transfer_integrity_autarch
                do_ipc_transfer_pas_refined
             | simp
             | intro conjI impI)+)[1]
    \<comment> \<open>receiver is not a subject\<close>
    apply (rule use_spec') \<comment> \<open>Name initial state\<close>
    apply (simp add: spec_valid_def) \<comment> \<open>no imp rule?\<close>

    apply (rule_tac Q =  "\<lambda>_ s'. integrity aag X st s \<and>
                         integrity_tcb_in_ipc aag X receiver _ TRFinal s s'" in hoare_post_imp)
     apply (fastforce dest!: integrity_tcb_in_ipc_final elim!: integrity_trans)
    apply ((wp possible_switch_to_respects_in_ipc_autarch
               set_thread_state_running_respects_in_ipc_reply
               cte_delete_one_respects_in_ipc_autharch cap_delete_one_reply_st_tcb_at
               do_ipc_transfer_pred_tcb do_ipc_transfer_respects_in_ipc
               do_ipc_transfer_non_null_cte_wp_at2
           | simp add: is_cap_simps is_reply_cap_to_def
           | clarsimp)+)[1]
   \<comment> \<open>fault case\<close>
   apply (rule hoare_vcg_if_split[where P= "is_subject aag receiver" and f=f and g=f for f,
                                  simplified if_cancel])
    \<comment> \<open>receiver is a subject\<close>
    apply ((wp set_thread_state_integrity_autarch thread_set_integrity_autarch
               handle_fault_reply_respects
           | simp
           | intro conjI impI)+)[1]
    \<comment> \<open>receiver is not a subject\<close>
   apply (rule hoare_seq_ext, simp)
    apply (rule use_spec') \<comment> \<open>Name initial state\<close>
    apply (simp add: spec_valid_def) \<comment> \<open>no imp rule?\<close>
    apply wp
          apply (rule_tac Q = "\<lambda>_ s'. integrity aag X st s \<and>
                                      integrity_tcb_in_fault_reply aag X receiver TRFFinal s s'"
                       in hoare_post_imp)
     apply (fastforce dest!: integrity_tcb_in_fault_reply_final elim!: integrity_trans)
   apply (wp set_thread_state_respects_in_fault_reply
             thread_set_no_fault_respects_in_fault_reply
             handle_fault_reply_respects_in_fault_reply
         | simp)+
   apply force
   apply (strengthen integrity_tcb_in_fault_reply_refl)+
   apply (wp cap_delete_one_reply_st_tcb_at)

  \<comment> \<open>the end\<close>
  by (force simp: st_tcb_at_tcb_states_of_state cte_wp_at_caps_of_state is_cap_simps
                  is_reply_cap_to_def
           dest!: tcb_states_of_state_kheapD get_tcb_SomeD tcb_atD ko_atD
           intro: tcb_atI fault_tcb_atI emptyable_not_master
          intro!: integrity_tcb_in_ipc_refl tcb_states_of_state_kheapI
           elim!: fault_tcb_atE)


lemma reply_from_kernel_integrity_autarch:
  "\<lbrace>integrity aag X st and pas_refined aag and valid_objs and K (is_subject aag thread)\<rbrace>
    reply_from_kernel thread x
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: reply_from_kernel_def split_def)
  apply (wp set_message_info_integrity_autarch set_mrs_integrity_autarch as_user_integrity_autarch | simp)+
  done

end

end
