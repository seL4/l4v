(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_AC
imports Arch_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

text \<open>
NB: the @{term is_subject} assumption is not appropriate for some of
    the scheduler lemmas. This is because a scheduler domain may have
    threads from multiple labels, hence the thread being acted upon
    might not be in the same label as the current subject.

    In some of the scheduling lemmas, we replace the @{term is_subject}
    assumption with a statement that the scheduled thread is in one of
    the current subject's domains.
\<close>

lemma tcb_sched_action_dequeue_integrity':
  "\<lbrace>integrity aag X st and pas_refined aag and
    (\<lambda>s. pasSubject aag \<in> pasDomainAbs aag (tcb_domain (the (ekheap s thread))))\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def pas_refined_def
                        tcb_domain_map_wellformed_aux_def etcb_at_def get_etcb_def
                  split: option.splits)
  done

lemma tcb_sched_action_dequeue_integrity[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and K (is_subject aag thread)\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def pas_refined_def
                        tcb_domain_map_wellformed_aux_def etcb_at_def get_etcb_def
             split: option.splits)
  apply (erule_tac x="(thread, tcb_domain (the (ekheap s thread)))" in ballE)
  apply (auto intro: domtcbs)
  done

lemma tcb_sched_action_enqueue_integrity[wp]:
  "\<lbrace>integrity aag X st\<rbrace>
    tcb_sched_action tcb_sched_enqueue thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def pas_refined_def
                        tcb_domain_map_wellformed_aux_def tcb_at_def get_etcb_def
                        tcb_sched_enqueue_def etcb_at_def
             split: option.splits)
  apply (metis append.simps(2))
  done

text \<open>See comment for @{thm tcb_sched_action_dequeue_integrity'}\<close>
lemma tcb_sched_action_append_integrity':
  "\<lbrace>integrity aag X st and
    (\<lambda>s. pasSubject aag \<in> pasDomainAbs aag (tcb_domain (the (ekheap s thread))))\<rbrace>
    tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def etcb_at_def
                 split: option.splits)
  done

lemma tcb_sched_action_append_integrity[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and K (is_subject aag thread)\<rbrace>
    tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def pas_refined_def
                        tcb_domain_map_wellformed_aux_def etcb_at_def get_etcb_def
                 split: option.splits)
  apply (erule_tac x="(thread, tcb_domain (the (ekheap s thread)))" in ballE)
  apply (auto intro: domtcbs)
  done

lemma tcb_sched_action_append_integrity_pasMayEditReadyQueues:
  "\<lbrace>integrity aag X st and pas_refined aag and K (pasMayEditReadyQueues aag)\<rbrace>
    tcb_sched_action tcb_sched_append thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def split: option.splits)
  done

lemma reschedule_required_integrity[wp]:
  "\<lbrace>integrity aag X st\<rbrace> reschedule_required \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: integrity_def reschedule_required_def)
  apply (wp | wpc)+
  apply simp
  done

lemma cancel_badged_sends_respects[wp]:
  "\<lbrace>integrity aag X st and einvs
           and valid_objs and (sym_refs \<circ> state_refs_of)
           and K (aag_has_auth_to aag Reset epptr)\<rbrace>
    cancel_badged_sends epptr badge
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cancel_badged_sends_def filterM_mapM
             cong: Structures_A.endpoint.case_cong)
  apply (wp set_endpoinintegrity | wpc | simp)+
     apply (rule mapM_mapM_x_valid[THEN iffD1])
     apply (simp add: exI[where x=Reset])
     apply (rule mapM_x_inv_wp2[where Q="P" and I="P" and
               V = "\<lambda>q s. distinct q \<and> (\<forall>x \<in> set q. st_tcb_at (blocked_on epptr) x s)"
               for P] )
      apply simp
     apply (simp add: bind_assoc)
     apply (rule hoare_seq_ext[OF _ gts_sp])
     apply (rule hoare_pre)
      apply (wp sts_respects_restart_ep hoare_vcg_const_Ball_lift sts_st_tcb_at_neq)
     apply clarsimp
     apply fastforce
    apply (wp set_endpoinintegrity hoare_vcg_const_Ball_lift get_simple_ko_wp)+
  apply clarsimp
  apply (frule(1) sym_refs_ko_atD)
  apply (frule ko_at_state_refs_ofD)
  apply (rule obj_at_valid_objsE, assumption, assumption)
  apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_def2)
  apply (clarsimp simp: obj_at_def is_ep valid_obj_def valid_ep_def)
  apply auto
  done

lemma cancel_all_ipc_respects [wp]:
  "\<lbrace>integrity aag X st
           and valid_objs and (sym_refs \<circ> state_refs_of)
           and K (\<exists>auth. aag_has_auth_to aag Reset epptr)\<rbrace>
    cancel_all_ipc epptr
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: cancel_all_ipc_def get_ep_queue_def cong: Structures_A.endpoint.case_cong)
  apply (wp mapM_x_inv_wp2[
                  where I = "integrity aag X st"
                    and V = "\<lambda>q s. distinct q \<and> (\<forall>x \<in> set q. st_tcb_at (blocked_on epptr) x s)"]
            sts_respects_restart_ep sts_st_tcb_at_neq hoare_vcg_ball_lift set_endpoinintegrity
            get_simple_ko_wp
        | wpc
        | clarsimp
        | blast)+
  apply (frule ko_at_state_refs_ofD)
  apply (rule obj_at_valid_objsE, assumption, assumption)
  apply (rename_tac ep ko)
  apply (subgoal_tac "\<forall>x \<in> ep_q_refs_of ep. st_tcb_at (blocked_on epptr) (fst x) s")
   apply (fastforce simp: valid_obj_def valid_ep_def obj_at_def is_ep_def
                   split: Structures_A.endpoint.splits)
  apply clarsimp
  apply (erule (1) ep_queued_st_tcb_at')
    apply simp_all
  done

crunch pas_refined[wp]: blocked_cancel_ipc, cancel_signal "pas_refined aag"

(* FIXME move to AInvs *)
lemma tcb_sched_action_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> tcb_sched_action p1 p2 \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
apply (simp add: tcb_sched_action_def)
apply wp
apply (simp add: etcb_at_def)
done

(* FIXME move to CNode *)
lemma scheduler_action_update_pas_refined[simp]:
  "pas_refined aag (scheduler_action_update (\<lambda>_. param_a) s) = pas_refined aag s"
by (simp add: pas_refined_def)

(* FIXME move to CNode *)
lemma tcb_sched_action_tcb_domain_map_wellformed[wp]:
  "\<lbrace>tcb_domain_map_wellformed aag\<rbrace> tcb_sched_action p1 p2 \<lbrace>\<lambda>_. tcb_domain_map_wellformed aag\<rbrace>"
by (wp tcb_domain_map_wellformed_lift)

lemma gbn_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> get_bound_notification t \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wp get_bound_notification_inv)

lemma set_bound_notification_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> set_bound_notification t st \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wp set_scheduler_action_wp | simp)+
  done

lemma sbn_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> set_bound_notification t ntfn \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: get_tcb_def thread_states_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma sbn_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_bound_notification t st \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def
                 elim!: rsubst[where P=P, OF _ ext]
                 dest!: get_tcb_SomeD)
  done

lemma sbn_pas_refined[wp]:
  "\<lbrace>pas_refined aag and
       K(case ntfn of None \<Rightarrow> True
                    | Some ntfn' \<Rightarrow> \<forall>auth \<in> {Receive, Reset}.
                         (pasObjectAbs aag t, auth, pasObjectAbs aag ntfn') \<in> pasPolicy aag )\<rbrace>
      set_bound_notification t ntfn
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply (clarsimp dest!: auth_graph_map_memD)
  apply (erule state_bits_to_policy.cases)
  apply (auto intro: state_bits_to_policy.intros auth_graph_map_memI
              split: if_split_asm)
  done

lemma unbind_notification_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> unbind_notification t \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (clarsimp simp: unbind_notification_def)
  apply (wp set_simple_ko_pas_refined | wpc | simp)+
  done

lemma unbind_maybe_notification_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> unbind_maybe_notification a \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (clarsimp simp: unbind_maybe_notification_def)
  apply (wp set_simple_ko_pas_refined | wpc | simp)+
  done

crunch tcb_domain_map_wellformed[wp]: reschedule_required "tcb_domain_map_wellformed aag"


crunch pas_refined[wp]: fast_finalise "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_mdb[wp]: fast_finalise "valid_mdb :: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_objs[wp]: fast_finalise "valid_objs :: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

crunch pas_refined_transferable[wp_transferable]: cap_delete_one "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

crunch pas_refined[wp, wp_not_transferable]: cap_delete_one, set_vm_root "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

(* FIXME MOVE next to thread_set_tcb_fault_set_invs in DetSchedSchedule *)
lemma thread_set_tcb_fault_reset_invs:
  "\<lbrace>invs\<rbrace>
     thread_set (tcb_fault_update (\<lambda>_. None)) t
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (rule thread_set_invs_trivial) (clarsimp simp: ran_tcb_cap_cases)+

(* FIXME MOVE next to IpcCancel_AI.reply_cap_descends_from_master *)
lemma reply_cap_descends_from_master0:
  "\<lbrakk> invs s; tcb_at t s \<rbrakk> \<Longrightarrow>
   \<forall>sl\<in>descendants_of (t, tcb_cnode_index 2) (cdt s).
      \<exists> R. caps_of_state s sl = Some (cap.ReplyCap t False R)"
  apply (subgoal_tac "cte_wp_at (\<lambda>c. (is_master_reply_cap c \<and> obj_ref_of c = t)
                                     \<or> c = cap.NullCap)
                                (t, tcb_cnode_index 2) s")
   apply (clarsimp simp: invs_def valid_state_def valid_mdb_def2 is_cap_simps
                         valid_reply_caps_def cte_wp_at_caps_of_state)
   apply (erule disjE)
    apply (unfold reply_mdb_def reply_masters_mdb_def)[1]
    apply (elim conjE)
    apply (erule_tac x="(t, tcb_cnode_index 2)" in allE)
    apply (erule_tac x=t in allE)+
    apply (fastforce simp: unique_reply_caps_def is_cap_simps)
   apply (fastforce dest: mdb_cte_at_Null_descendants)
  apply (clarsimp simp: tcb_cap_wp_at invs_valid_objs
                        tcb_cap_cases_def is_cap_simps)
  done


lemma reply_cancel_ipc_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and tcb_at t and K (is_subject aag t)\<rbrace>
     reply_cancel_ipc t
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: reply_cancel_ipc_def)
  apply (wp add: select_wp wp_transferable del: wp_not_transferable)
   apply (rule hoare_strengthen_post[where Q="\<lambda>_.invs and tcb_at t and pas_refined aag"])
    apply (wpsimp wp: hoare_wp_combs thread_set_tcb_fault_reset_invs thread_set_pas_refined)+
   apply (frule(1) reply_cap_descends_from_master0)
   apply (fastforce simp: cte_wp_at_caps_of_state intro:it_Reply)
  by fastforce

lemma deleting_irq_handler_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and K (is_subject_irq aag irq)\<rbrace>
      deleting_irq_handler irq
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: deleting_irq_handler_def get_irq_slot_def)
  apply wp
  apply (clarsimp simp: pas_refined_def irq_map_wellformed_aux_def)
  done

crunch pas_refined[wp]: "suspend", arch_finalise_cap,prepare_thread_delete "pas_refined aag"

lemma finalise_cap_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and valid_cap cap and K (pas_cap_cur_auth aag cap)\<rbrace>
     finalise_cap cap fin
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases cap; simp only: finalise_cap.simps)
  (* 12 subgoals *)
  apply (wp unbind_notification_invs
        | clarsimp simp: aag_cap_auth_def cap_auth_conferred_def valid_cap_simps
                         cap_links_irq_def pas_refined_Control[symmetric])+
  done

lemma cancel_all_signals_respects [wp]:
  "\<lbrace>integrity aag X st
           and valid_objs and (sym_refs \<circ> state_refs_of)
           and K (aag_has_auth_to aag Reset epptr)\<rbrace>
    cancel_all_signals epptr
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp add: cancel_all_signals_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp], rule hoare_pre)
   apply (wp mapM_x_inv_wp2[
              where I = "integrity aag X st"
                and V = "\<lambda>q s. distinct q \<and> (\<forall>x \<in> set q. st_tcb_at (blocked_on epptr) x s)"]
            sts_respects_restart_ep sts_st_tcb_at_neq hoare_vcg_ball_lift set_ntfn_respects
        | wpc
        | clarsimp
        | blast)+
  apply (frule sym_refs_ko_atD, clarsimp+)
  apply (rule obj_at_valid_objsE, assumption, assumption)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def st_tcb_at_refs_of_rev st_tcb_def2
                 split: option.splits)
  apply fastforce+
  done

lemma gbn_respects[wp]:
  "\<lbrace>integrity aag X st\<rbrace> get_bound_notification t \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wp get_bound_notification_inv)

lemma sbn_unbind_respects[wp]:
  "\<lbrace>integrity aag X st and
       (\<lambda>s. (\<exists>ntfn. bound_tcb_at (\<lambda>a. a = Some ntfn) t s \<and>
           (pasSubject aag, Reset, pasObjectAbs aag ntfn) \<in> pasPolicy aag))\<rbrace>
     set_bound_notification t None
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def pred_tcb_at_def)
  apply (rule tro_tcb_unbind)
     apply (fastforce dest!: get_tcb_SomeD)
    apply (fastforce dest!: get_tcb_SomeD)
   apply simp
  apply (simp add: tcb_bound_notification_reset_integrity_def)
  done

lemma bound_tcb_at_thread_bound_ntfns:
  "bound_tcb_at ((=) ntfn) t s \<Longrightarrow> thread_bound_ntfns s t = ntfn"
  by (clarsimp simp: thread_bound_ntfns_def pred_tcb_at_def obj_at_def get_tcb_def
              split: option.splits)


lemma bound_tcb_at_implies_receive:
  "\<lbrakk>pas_refined aag s; bound_tcb_at ((=) (Some x)) t s\<rbrakk>
          \<Longrightarrow> (pasObjectAbs aag t, Receive, pasObjectAbs aag x) \<in> pasPolicy aag"
  by (fastforce dest!: bound_tcb_at_thread_bound_ntfns sta_bas pas_refined_mem)

lemma bound_tcb_at_implies_reset:
  "\<lbrakk>pas_refined aag s; bound_tcb_at ((=) (Some x)) t s\<rbrakk>
          \<Longrightarrow> (pasObjectAbs aag t, Reset, pasObjectAbs aag x) \<in> pasPolicy aag"
  by (fastforce dest!: bound_tcb_at_thread_bound_ntfns sta_bas pas_refined_mem)

lemma unbind_notification_bound_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and (\<lambda>s. bound_tcb_at (\<lambda>a. a = Some ntfn) t s \<and>
     (pasSubject aag, Reset, pasObjectAbs aag ntfn) \<in> pasPolicy aag)\<rbrace>
      unbind_notification t
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (clarsimp simp: unbind_notification_def)
  apply (wp set_ntfn_respects hoare_vcg_imp_lift hoare_vcg_ex_lift gbn_wp
        | wpc
        | simp)+
   apply clarsimp
   apply (fastforce simp: pred_tcb_at_def obj_at_def)+
  done

lemma unbind_notification_noop_respects:
  "\<lbrace>integrity aag X st and bound_tcb_at (\<lambda>a. a = None) t\<rbrace>
      unbind_notification t
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (clarsimp simp: unbind_notification_def)
  apply (wp set_ntfn_respects hoare_vcg_ex_lift gbn_wp | wpc | simp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma unbind_notification_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and
      bound_tcb_at (\<lambda>a. case a of
        None \<Rightarrow> True |
        Some ntfn \<Rightarrow> (pasSubject aag, Reset, pasObjectAbs aag ntfn) \<in> pasPolicy aag) t\<rbrace>
     unbind_notification t \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (clarsimp simp: unbind_notification_def)
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (rule hoare_pre)
  apply (wp set_ntfn_respects hoare_vcg_ex_lift gbn_wp | wpc | simp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def split: option.splits)
  apply blast
  done

lemma unbind_maybe_notification_respects:
  "\<lbrace>integrity aag X st and invs and pas_refined aag and
      obj_at (\<lambda>ko. \<exists>ntfn. ko = (Notification ntfn) \<and>
        (case (ntfn_bound_tcb ntfn) of
          None \<Rightarrow> True |
          Some t \<Rightarrow> (pasSubject aag, Reset, pasObjectAbs aag a) \<in> pasPolicy aag)) a \<rbrace>
     unbind_maybe_notification a \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (clarsimp simp: unbind_maybe_notification_def)
  apply (rule hoare_pre)
   apply (wp set_ntfn_respects get_simple_ko_wp hoare_vcg_ex_lift gbn_wp | wpc | simp)+
  apply clarsimp
  apply (frule_tac P="\<lambda>ntfn. ntfn = Some a"
                in ntfn_bound_tcb_at[OF invs_sym_refs invs_valid_objs], (simp add: obj_at_def)+)
  apply (auto simp: pred_tcb_at_def obj_at_def split: option.splits)
  done

lemma fast_finalise_respects[wp]:
  "\<lbrace>integrity aag X st and invs and pas_refined aag and valid_cap cap and
     K (pas_cap_cur_auth aag cap)\<rbrace>
      fast_finalise cap fin
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (cases cap; simp)
     apply (wp unbind_maybe_notification_valid_objs get_simple_ko_wp
               unbind_maybe_notification_respects
           | wpc
           | simp add: cap_auth_conferred_def cap_rights_to_auth_def aag_cap_auth_def when_def
                split: if_split_asm
           | fastforce)+
      apply (clarsimp simp: obj_at_def valid_cap_def is_ntfn invs_def valid_state_def
                            valid_pspace_def
                     split: option.splits)+
  apply (wp, simp)
  done

lemma cap_delete_one_respects[wp,wp_not_transferable]:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and K (is_subject aag (fst slot))\<rbrace>
     cap_delete_one slot
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def bind_assoc)
  apply (wp hoare_drop_imps get_cap_auth_wp [where aag = aag]
        | simp)+
  apply (fastforce simp: caps_of_state_valid)
  done

lemma fast_finalise_is_transferable[wp_transferable]:
  "\<lbrace> P and K(is_transferable (Some cap)) \<rbrace>
     fast_finalise cap final
   \<lbrace>\<lambda>_. P \<rbrace>"
  by (rule hoare_gen_asm) (erule is_transferable.cases; simp)

lemma cap_delete_one_respects_transferable[wp_transferable]:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and
    cte_wp_at(\<lambda>c. is_transferable (Some c)) slot and cdt_change_allowed' aag slot\<rbrace>
      cap_delete_one slot
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def bind_assoc)
  apply (wp add: hoare_drop_imps get_cap_wp wp_transferable del:wp_not_transferable
        | simp)+
  apply (fastforce simp: caps_of_state_valid cte_wp_at_caps_of_state)
  done

lemma thread_set_tcb_state_trivial:
  "(\<And> tcb. tcb_state (f tcb) = tcb_state tcb) \<Longrightarrow>
   \<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace> thread_set f t \<lbrace>\<lambda>_ s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  by (auto simp: tcb_states_of_state_def get_tcb_def)


lemma reply_cancel_ipc_respects[wp]:
  "\<lbrace>integrity aag X st and einvs and tcb_at t and
        K (is_subject aag t) and
        pas_refined aag\<rbrace>
     reply_cancel_ipc t
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply (rule hoare_pre)
   apply (wp add: select_wp wp_transferable del:wp_not_transferable)
   apply simp
   apply (rule hoare_lift_Pf2[where f="cdt"])
    apply (wpsimp wp: hoare_vcg_const_Ball_lift thread_set_integrity_autarch
                      thread_set_invs_trivial[OF ball_tcb_cap_casesI] thread_set_tcb_state_trivial
                      thread_set_not_state_valid_sched static_imp_wp thread_set_cte_wp_at_trivial
                      thread_set_pas_refined
                simp: ran_tcb_cap_cases)+
  apply (rule conjI)
   apply (fastforce simp: cte_wp_at_caps_of_state intro:is_transferable.intros
                   dest!: reply_cap_descends_from_master0)
  apply (rule cdt_change_allowed_all_children
                [where aag=aag, THEN all_children_descendants_of])
   by fastforce+

lemma cancel_signal_respects[wp]:
  "\<lbrace>integrity aag X st and K (is_subject aag t \<and>
        (\<exists>auth. aag_has_auth_to aag auth ntfnptr \<and> (auth = Receive \<or> auth = Notify)))\<rbrace>
     cancel_signal t ntfnptr
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp set_thread_state_integrity_autarch set_ntfn_respects
             | wpc | fastforce)+
  done

lemma cancel_ipc_respects[wp]:
  "\<lbrace>integrity aag X st and einvs and tcb_at t and
    K (is_subject aag t) and pas_refined aag\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_pre)
   apply (wp set_thread_state_integrity_autarch set_endpoinintegrity get_simple_ko_wp
         | wpc
         | simp(no_asm) add: blocked_cancel_ipc_def get_ep_queue_def get_blocking_object_def)+
  apply clarsimp
  apply (frule st_tcb_at_to_thread_states, clarsimp+)
  apply (fastforce simp: obj_at_def is_ep_def dest: pas_refined_mem[OF sta_ts_mem])
  done

lemma update_restart_pc_integrity_autarch[wp]:
  "\<lbrace>integrity aag X st and K (is_subject aag t)\<rbrace> update_restart_pc t
                                      \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def)
  unfolding update_restart_pc_def
  apply (wp as_user_integrity_autarch)
  apply simp
  done

lemma suspend_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and tcb_at t and
    K (is_subject aag t)\<rbrace>
    suspend t \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: suspend_def)
  apply (wp set_thread_state_integrity_autarch set_thread_state_pas_refined)
    apply (rule hoare_conjI)
     apply (wp hoare_drop_imps)+
    apply wpsimp+
  done

lemma finalise_is_fast_finalise:
  "can_fast_finalise cap \<Longrightarrow>
    finalise_cap cap fin = do fast_finalise cap fin; return (cap.NullCap, cap.NullCap) od"
  by (cases cap, simp_all add: can_fast_finalise_def liftM_def)

lemma get_irq_slot_owns [wp]:
  "\<lbrace>pas_refined aag and K (is_subject_irq aag irq)\<rbrace>
      get_irq_slot irq
   \<lbrace>\<lambda>rv _. is_subject aag (fst rv)\<rbrace>"
  unfolding get_irq_slot_def
  apply wp
  apply (rule pas_refined_Control [symmetric])
  apply (clarsimp simp: pas_refined_def irq_map_wellformed_aux_def aag_wellformed_refl)
  apply fastforce
  done

lemma pas_refined_Control_into_is_subject_asid:
  "\<lbrakk>pas_refined aag s; (pasSubject aag, Control, pasASIDAbs aag asid) \<in> pasPolicy aag\<rbrakk> \<Longrightarrow>
  is_subject_asid aag asid"
  apply(drule (1) pas_refined_Control)
  apply(blast intro: sym)
  done

lemma arch_finalise_cap_respects[wp]:
  "\<lbrace>integrity aag X st and invs and pas_refined aag
             and valid_cap (cap.ArchObjectCap cap)
             and K (pas_cap_cur_auth aag (cap.ArchObjectCap cap))\<rbrace>
       arch_finalise_cap cap final \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp unmap_page_respects unmap_page_table_respects delete_asid_respects
              | wpc | simp)+
  apply clarsimp
  apply (auto simp: cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                    aag_cap_auth_def pas_refined_all_auth_is_owns valid_cap_simps
                    cap_links_asid_slot_def label_owns_asid_slot_def
             dest!: pas_refined_Control intro: pas_refined_Control_into_is_subject_asid)
  done

crunch respects[wp]: prepare_thread_delete "integrity aag X st"

lemma finalise_cap_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and valid_cap cap
    and K (pas_cap_cur_auth aag cap)\<rbrace>
       finalise_cap cap final \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (cases cap; simp; safe?;
     (solves \<open>(wp | simp add: if_apply_def2 split del: if_split
                  | clarsimp simp: cap_auth_conferred_def cap_rights_to_auth_def is_cap_simps
                                   pas_refined_all_auth_is_owns aag_cap_auth_def
                                   deleting_irq_handler_def cap_links_irq_def invs_valid_objs
                        split del: if_split
                            elim!: pas_refined_Control [symmetric])+\<close>)?
  )

   (*NTFN Cap*)
   apply ((wp unbind_maybe_notification_valid_objs get_simple_ko_wp
              unbind_maybe_notification_respects
          | wpc
          | simp add: cap_auth_conferred_def cap_rights_to_auth_def aag_cap_auth_def
               split: if_split_asm
          | fastforce)+;
          clarsimp simp: obj_at_def valid_cap_def is_ntfn invs_def
                         valid_state_def valid_pspace_def
                  split: option.splits)
  (* tcb cap *)
  apply (wp unbind_notification_respects unbind_notification_invs
          | clarsimp simp: cap_auth_conferred_def cap_rights_to_auth_def aag_cap_auth_def
                           unbind_maybe_notification_def
                    elim!: pas_refined_Control[symmetric]
          | simp add: if_apply_def2 split del: if_split )+
  apply (clarsimp simp: valid_cap_def pred_tcb_at_def obj_at_def is_tcb
                 dest!: tcb_at_ko_at)
  apply (clarsimp split: option.splits elim!: pas_refined_Control[symmetric])
  apply (frule pas_refined_Control, simp+)
  apply (fastforce dest: bound_tcb_at_implies_reset
               simp add: pred_tcb_at_def obj_at_def)
  done

lemma finalise_cap_auth:
  "\<lbrace>(\<lambda>s. final \<longrightarrow> is_final_cap' cap s \<and> cte_wp_at ((=) cap) slot s)
             and K (pas_cap_cur_auth aag cap)\<rbrace>
      finalise_cap cap final
   \<lbrace>\<lambda>rv s. \<forall>x\<in>obj_refs (fst rv). \<forall>a \<in> cap_auth_conferred (fst rv).
                                         (pasSubject aag, a, pasObjectAbs aag x) \<in> pasPolicy aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post, rule finalise_cap_cases)
  apply (elim disjE, clarsimp+)
  apply (clarsimp simp: is_cap_simps cap_auth_conferred_def aag_cap_auth_def)
  apply (simp add: fst_cte_ptrs_def split: cap.split_asm)
  done

lemma aag_cap_auth_Zombie:
  "pas_refined aag s \<Longrightarrow> pas_cap_cur_auth aag (cap.Zombie word a b) = is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def pas_refined_all_auth_is_owns)

lemma aag_cap_auth_CNode:
  "pas_refined aag s \<Longrightarrow> pas_cap_cur_auth aag (cap.CNodeCap word a b) = is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def pas_refined_all_auth_is_owns)

lemma aag_cap_auth_Thread:
  "pas_refined aag s \<Longrightarrow> pas_cap_cur_auth aag (cap.ThreadCap word) = is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def pas_refined_all_auth_is_owns)

lemma finalise_cap_auth':
  "\<lbrace>pas_refined aag and K (pas_cap_cur_auth aag cap)\<rbrace>
      finalise_cap cap final
   \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag (fst rv)\<rbrace>"
  including no_pre
  apply (rule hoare_gen_asm)
  apply (cases cap, simp_all add: arch_finalise_cap_def split del: if_split)
  apply (wp
    | simp add: comp_def hoare_post_taut [where P = \<top>] split del: if_split
    | fastforce simp:  aag_cap_auth_Zombie aag_cap_auth_CNode aag_cap_auth_Thread
    )+
  apply (rule hoare_pre)
  apply (wp | simp)+
  apply (rule hoare_pre)
  apply (wp | wpc
    | simp add: comp_def hoare_post_taut [where P = \<top>] split del: if_split)+
  done

lemma finalise_cap_obj_refs:
  "\<lbrace>\<lambda>s. \<forall>x \<in> obj_refs cap. P x\<rbrace> finalise_cap cap slot \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs (fst rv). P x\<rbrace>"
  apply (cases cap)
             apply (wpsimp simp: arch_finalise_cap_def o_def|rule conjI)+
  done

lemma zombie_ptr_emptyable:
  "\<lbrakk> caps_of_state s cref = Some (cap.Zombie ptr zbits n); invs s \<rbrakk>
     \<Longrightarrow> emptyable (ptr, cref_half) s"
  apply (clarsimp simp: emptyable_def tcb_at_def st_tcb_def2)
  apply (rule ccontr)
  apply (clarsimp simp: get_tcb_ko_at)
  apply (drule if_live_then_nonz_capD[rotated])
    apply (auto simp: live_def hyp_live_def)[2]
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state
                        zobj_refs_to_obj_refs)
  apply (drule(2) zombies_final_helperE, clarsimp, simp+)
  apply (simp add: is_cap_simps)
  done

lemma finalise_cap_makes_halted:
  "\<lbrace>invs and valid_cap cap and (\<lambda>s. ex = is_final_cap' cap s)
         and cte_wp_at ((=) cap) slot\<rbrace>
    finalise_cap cap ex
   \<lbrace>\<lambda>rv s. \<forall>t \<in> obj_refs (fst rv). halted_if_tcb t s\<rbrace>"
  apply (case_tac cap, simp_all)
            apply (wp unbind_notification_valid_objs
                 | clarsimp simp: o_def valid_cap_def cap_table_at_typ
                                  is_tcb obj_at_def
                 | clarsimp simp: halted_if_tcb_def
                           split: option.split
                 | intro impI conjI
                 | rule hoare_drop_imp)+
   apply (fastforce simp: st_tcb_at_def obj_at_def is_tcb live_def
                  dest!: final_zombie_not_live)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all add: arch_finalise_cap_def)
      apply (wp
           | clarsimp simp: valid_cap_def split: option.split bool.split
           | intro impI conjI)+
  done


lemma aag_Control_into_owns_irq:
  "\<lbrakk>(pasSubject aag, Control, pasIRQAbs aag irq) \<in> pasPolicy aag; pas_refined aag s\<rbrakk>
    \<Longrightarrow> is_subject_irq aag irq"
  apply (drule (1) pas_refined_Control)
  apply simp
  done

lemma owns_slot_owns_irq:
  "\<lbrakk>is_subject aag (fst slot); caps_of_state s slot = Some rv;
    pas_refined aag s; cap_irq_opt rv = Some irq\<rbrakk>
    \<Longrightarrow> is_subject_irq aag irq"
  apply(rule aag_Control_into_owns_irq[rotated], assumption)
  apply(drule (1) cli_caps_of_state)
  apply(clarsimp simp: cap_links_irq_def cap_irq_opt_def split: cap.splits)
  done

lemma replaceable_zombie_not_transferable:
  "replaceable s slot (Zombie ref sz n) cap \<Longrightarrow> \<not> is_transferable (Some cap)"
  by (intro notI) (erule is_transferable.cases; simp add:replaceable_def)


lemma rec_del_respects'_pre':
  "s \<turnstile> \<lbrace>(\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag
                  and einvs and simple_sched_action and valid_rec_del_call call
                  and emptyable (slot_rdcall call)
                  and (\<lambda>s. \<not> exposed_rdcall call \<longrightarrow>
                                  ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall call) s)
                  and K (is_subject aag (fst (slot_rdcall call)))
                  and K (case call of ReduceZombieCall cap sl _ \<Rightarrow>
                                          \<forall>x \<in> obj_refs cap. is_subject aag x
                                    | _ \<Rightarrow> True)\<rbrace>
     rec_del call
   \<lbrace>\<lambda>rv. (\<lambda>s. trp \<longrightarrow> (case call of FinaliseSlotCall sl _ \<Rightarrow>
                                          (cleanup_info_wf (snd rv) aag)
                                  | _ \<Rightarrow> True) \<and> integrity aag X st s)
                  and pas_refined aag\<rbrace>,
   \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
proof (induct arbitrary: st rule: rec_del.induct, simp_all only: rec_del_fails)
  case (1 slot exposed s)
  show ?case
    apply (rule hoare_spec_gen_asm)+
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (rule hoare_pre_spec_validE)
     apply (rule split_spec_bindE)
      apply (wp static_imp_wp)
     apply (rule spec_strengthen_postE)
      apply (rule spec_valid_conj_liftE1)
       apply (rule valid_validE_R, rule rec_del_valid_list, rule preemption_point_inv';
              solves\<open>simp\<close>)
      apply (rule spec_valid_conj_liftE1)
       apply (rule valid_validE_R, rule rec_del_invs)
      apply (rule "1.hyps"[simplified rec_del_call.simps slot_rdcall.simps])
     apply auto
  done

next
  case (2 slot exposed s)
  show ?case
    apply (rule hoare_spec_gen_asm)+
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (rule hoare_pre_spec_validE)
     apply (wp set_cap_integrity_autarch set_cap_pas_refined_not_transferable "2.hyps" static_imp_wp)
          apply ((wp preemption_point_inv'
                 | simp add: integrity_subjects_def pas_refined_def)+)[1]
         apply (simp(no_asm))
         apply (rule spec_strengthen_postE)
          apply (rule spec_valid_conj_liftE1, rule valid_validE_R, rule rec_del_invs)
          apply (rule spec_valid_conj_liftE1, rule reduce_zombie_cap_to)
          apply (rule spec_valid_conj_liftE1, rule rec_del_emptyable)
          apply (rule spec_valid_conj_liftE1, rule valid_validE_R, rule rec_del_valid_sched')
          apply (rule spec_valid_conj_liftE1, rule valid_validE_R, rule rec_del_valid_list,
                 rule preemption_point_inv')
            apply simp
           apply simp
          apply (rule "2.hyps", assumption+)
         apply simp
        apply (simp add: conj_comms)
        apply (wp set_cap_integrity_autarch  set_cap_pas_refined_not_transferable replace_cap_invs
                  final_cap_same_objrefs set_cap_cte_cap_wp_to
                  set_cap_cte_wp_at hoare_vcg_const_Ball_lift static_imp_wp
                       | rule finalise_cap_not_reply_master
                       | simp add: in_monad)+
       apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>fin s. einvs s \<and> simple_sched_action s \<and> replaceable s slot (fst fin) rv
                                  \<and> cte_wp_at ((=) rv) slot s \<and> s \<turnstile> (fst fin)
                                  \<and> ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s
                                  \<and> emptyable slot s
                                  \<and> (\<forall>t\<in>obj_refs (fst fin). halted_if_tcb t s)
                                  \<and> pas_refined aag s \<and> (trp \<longrightarrow> integrity aag X st s)
                                  \<and> pas_cap_cur_auth aag (fst fin)"
                   in hoare_vcg_conj_lift)
         apply (wp finalise_cap_invs[where slot=slot]
                   finalise_cap_replaceable[where sl=slot]
                   finalise_cap_makes_halted[where slot=slot]
                   finalise_cap_auth' static_imp_wp)[1]
        apply (rule finalise_cap_cases[where slot=slot])
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply (erule disjE)
        apply (clarsimp split: cap.split_asm)
        apply(fastforce intro: owns_slot_owns_irq)
       apply (clarsimp simp: is_cap_simps cap_auth_conferred_def clas_no_asid aag_cap_auth_def
                             pas_refined_all_auth_is_owns cli_no_irqs)
       apply (drule appropriate_Zombie[symmetric, THEN trans, symmetric])
       apply (clarsimp simp: gen_obj_refs_eq)
       apply (erule_tac s = "{r}" in subst)
       subgoal by (simp add:replaceable_zombie_not_transferable)
      apply (simp add: is_final_cap_def)
      apply (wp get_cap_auth_wp [where aag = aag])+
    apply (clarsimp simp: pas_refined_wellformed cte_wp_at_caps_of_state conj_comms)
    apply (frule (1) caps_of_state_valid)
    apply (frule if_unsafe_then_capD [OF caps_of_state_cteD], clarsimp+)
    apply auto
    done
next
  case (3 ptr bits n slot s)
  show ?case
    apply (simp add: spec_validE_def)
    apply (wp static_imp_wp)
    apply clarsimp
    done

next
  case (4 ptr bits n slot s)
  show ?case
    apply (rule hoare_spec_gen_asm)+
    apply (subst rec_del.simps)
    apply (rule hoare_pre_spec_validE)
     apply (rule split_spec_bindE)
      apply (rule split_spec_bindE[rotated])
       apply (rule "4.hyps", assumption+)
      apply (wp set_cap_integrity_autarch set_cap_pas_refined_not_transferable get_cap_wp
                static_imp_wp
            | simp)+
      apply (clarsimp simp: cte_wp_at_caps_of_state clas_no_asid cli_no_irqs aag_cap_auth_def)
      apply (drule_tac auth=auth in sta_caps, simp+)
       apply (simp add: cap_auth_conferred_def aag_cap_auth_def)
      apply (drule(1) pas_refined_mem)
      apply (simp add: cap_auth_conferred_def is_cap_simps)
     apply (wp | simp)+
    apply (clarsimp simp add: zombie_is_cap_toE)
    apply (clarsimp simp: cte_wp_at_caps_of_state zombie_ptr_emptyable)
    done
qed

lemma rec_del_respects'_pre:
  "s \<turnstile> \<lbrace>(\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag
                  and einvs and simple_sched_action and valid_rec_del_call call
                  and emptyable (slot_rdcall call)
                  and (\<lambda>s. \<not> exposed_rdcall call \<longrightarrow>
                                   ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall call) s)
                  and K (is_subject aag (fst (slot_rdcall call)))
                  and K (case call of ReduceZombieCall cap sl _ \<Rightarrow>
                                         \<forall>x \<in> obj_refs cap. is_subject aag x
                                    | _ \<Rightarrow> True)\<rbrace>
     rec_del call
   \<lbrace>\<lambda>rv. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>,
   \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
  apply (rule spec_strengthen_postE[OF rec_del_respects'_pre'])
  by simp

lemmas rec_del_respects'' = rec_del_respects'_pre[THEN use_spec(2), THEN validE_valid]
lemmas rec_del_respects
    = rec_del_respects''[of True, THEN hoare_conjD1, simplified]
      rec_del_respects''[of False, THEN hoare_conjD2, simplified]

lemma finalise_cap_transferable:
  "\<lbrace>P and K(is_transferable_cap cap)\<rbrace> finalise_cap cap final \<lbrace>\<lambda>rv s . rv =(NullCap, NullCap) \<and> P s\<rbrace>"
  by (rule hoare_gen_asm) (erule is_transferable_capE; wpsimp+)


lemma rec_del_Finalise_transferable:
  "\<lbrace>(\<lambda>s. is_transferable (caps_of_state s slot)) and P\<rbrace>
     rec_del (FinaliseSlotCall slot exposed)
   \<lbrace>\<lambda>rv. K(rv = (True,NullCap)) and  P \<rbrace>, \<lbrace>\<lambda>_.P\<rbrace>"
  apply (subst rec_del.simps[abs_def])
  apply (wp hoare_K_bind | wpc )+
        apply ((simp only: validE_R_def validE_E_def)?, rule hoare_FalseE)
       apply ((simp only: validE_R_def validE_E_def)?, rule hoare_FalseE)
      apply ((simp only: validE_R_def validE_E_def)?, rule hoare_FalseE)
     apply (wp without_preemption_wp)
     apply (rule hoare_post_imp[of "\<lambda>rv s. rv = (NullCap,NullCap) \<and> P s" for P])
      apply (clarsimp; assumption)
     apply (wp finalise_cap_transferable without_preemption_wp get_cap_wp)+
  by (fastforce simp:cte_wp_at_caps_of_state)

lemma rec_del_respects_CTEDelete_transferable':
  "\<lbrace>(\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag
                  and einvs and simple_sched_action and emptyable slot
                  and (\<lambda>s. \<not> exposed \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s)
                  and cdt_change_allowed' aag slot\<rbrace>
     rec_del (CTEDeleteCall slot exposed)
   \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>,
   \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
  apply (cases "is_subject aag (fst slot)")
   apply (wp rec_del_respects'')
   apply (solves \<open>simp\<close>)
  apply (subst rec_del.simps[abs_def])
  apply (wp add: hoare_K_bind without_preemption_wp static_imp_wp wp_transferable
                 rec_del_Finalise_transferable
            del: wp_not_transferable
        | wpc)+
    apply (rule hoare_post_impErr,rule rec_del_Finalise_transferable)
     apply simp apply (elim conjE) apply simp apply simp
   apply (wp add: hoare_K_bind without_preemption_wp static_imp_wp wp_transferable
                  rec_del_Finalise_transferable
             del: wp_not_transferable
         | wpc)+
   apply (rule hoare_post_impErr,rule rec_del_Finalise_transferable)
    apply simp apply (elim conjE) apply simp apply simp
  apply (clarsimp)
  apply (frule(3) cca_to_transferable_or_subject[OF invs_valid_objs invs_mdb])
  by (safe; simp)

lemmas rec_del_respects_CTEDelete_transferable =
  rec_del_respects_CTEDelete_transferable'[of True,THEN validE_valid,THEN hoare_conjD1,simplified]
  rec_del_respects_CTEDelete_transferable'[of False,THEN validE_valid,THEN hoare_conjD2,simplified]



(* TODO section change *)


(* FIXME: CLAG *)
lemmas dmo_valid_cap[wp] = valid_cap_typ [OF do_machine_op_obj_at]

lemma integrity_eupdate_autarch:
  "\<lbrakk> integrity aag X st s; is_subject aag ptr \<rbrakk>
    \<Longrightarrow> integrity aag X st (s\<lparr>ekheap := ekheap s(ptr \<mapsto> obj)\<rparr>)"
  unfolding integrity_subjects_def by auto

lemma set_eobject_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag ptr)\<rbrace>
     set_eobject ptr obj
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_eobject_def)
  apply wp
  apply (rule integrity_eupdate_autarch, simp_all)
  done

crunch pas_refined[wp]: cancel_badged_sends "pas_refined aag"
  (wp: crunch_wps simp: filterM_mapM crunch_simps ignore: filterM)

lemma rsubst':
  "\<lbrakk>P s s'; s=t; s'=t'\<rbrakk> \<Longrightarrow> P t t'"
  by auto

lemma thread_set_pas_refined_triv_idleT:
  assumes cps: "\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb"
       and st: "\<And>tcb. P (tcb_state tcb) \<longrightarrow> tcb_state (f tcb) = tcb_state tcb"
       and ba: "\<And>tcb. Q (tcb_bound_notification tcb) \<longrightarrow>
                             tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  shows
    "\<lbrace>pas_refined aag and idle_tcb_at (\<lambda>(st, ntfn, arch). P st \<and> Q ntfn \<and> R arch) t\<rbrace>
        thread_set f t
     \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wps thread_set_caps_of_state_trivial[OF cps])
   apply (simp add: thread_set_def)
   apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_def2 fun_upd_def[symmetric]
                   del: subsetI)
  apply (erule_tac P="\<lambda> ts ba. auth_graph_map a (state_bits_to_policy cps ts ba cd vr) \<subseteq> ag"
               for a cps cd vr ag in rsubst')
   apply (drule get_tcb_SomeD)
   apply (rule ext, clarsimp simp add: thread_states_def get_tcb_def st tcb_states_of_state_def)
  apply (drule get_tcb_SomeD)
  apply (rule ext, clarsimp simp: thread_bound_ntfns_def get_tcb_def ba)
  done

lemma copy_global_mappings_pas_refined2:
  "\<lbrace>invs and pas_refined aag and K (is_aligned pd pd_bits)\<rbrace>
      copy_global_mappings pd
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm, wp copy_global_mappings_pas_refined)
  apply (auto simp: invs_def valid_state_def valid_pspace_def)
  done

lemma pas_refined_set_asid_table_empty_strg:
  "pas_refined aag s \<and> is_subject aag pool
   \<and> (\<forall> asid. asid \<noteq> 0 \<and> asid_high_bits_of asid = base \<longrightarrow> is_subject_asid aag asid)
   \<and> ko_at (ArchObj (arch_kernel_obj.ASIDPool Map.empty)) pool s
   \<longrightarrow> pas_refined aag (s\<lparr>arch_state :=
                          arch_state s \<lparr>arm_asid_table :=
                                        (arm_asid_table (arch_state s))(base \<mapsto> pool)\<rparr>\<rparr>)"
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (erule state_asids_to_policy_aux.cases)
    apply(simp_all split: if_split_asm)
      prefer 2
      apply (clarsimp simp: state_vrefs_def obj_at_def vs_refs_no_global_pts_def)
     apply (auto intro: state_asids_to_policy_aux.intros auth_graph_map_memI[OF sbta_vref]
                intro!: pas_refined_refl[simplified pas_refined_def state_objs_to_policy_def])[3]
  apply(rule pas_refined_asid_mem)
   apply(drule_tac t="pasSubject aag" in sym)
   apply(simp, rule sata_asidpool)
    apply simp
   apply assumption
  apply(simp add: pas_refined_def state_objs_to_policy_def)
  done

lemma set_asid_pool_ko_at[wp]:
  "\<lbrace>\<top>\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>rv. ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr\<rbrace>"
  by (wpsimp simp: obj_at_def set_asid_pool_def set_object_def)

(* The contents of the delete_access_control locale *)



lemma cap_delete_respects:
  "\<lbrace>integrity aag X st and cdt_change_allowed' aag slot and pas_refined aag
            and einvs and simple_sched_action and emptyable slot\<rbrace>
       cap_delete slot
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  by (simp add: cap_delete_def) (wpsimp wp: rec_del_respects_CTEDelete_transferable)

lemma cap_delete_respects':
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))
            and pas_refined aag
            and einvs and simple_sched_action and emptyable slot\<rbrace>
       cap_delete slot
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  by (wp cap_delete_respects) fastforce

lemma cap_delete_pas_refined:
  "\<lbrace>cdt_change_allowed' aag slot and pas_refined aag and einvs and simple_sched_action
          and emptyable slot\<rbrace>
       cap_delete slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  by (simp add: cap_delete_def) (wpsimp wp: rec_del_respects_CTEDelete_transferable)

lemma cap_delete_pas_refined':
  "\<lbrace>pas_refined aag and einvs and simple_sched_action and emptyable slot
          and K(is_subject aag (fst slot))\<rbrace>
       cap_delete slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  by (wp cap_delete_pas_refined) fastforce

lemma cap_revoke_respects':
  "s \<turnstile> \<lbrace> (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and K (is_subject aag (fst slot))
         and pas_refined aag and einvs and simple_sched_action\<rbrace>
       (cap_revoke slot)
   \<lbrace>\<lambda>rv. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>,
   \<lbrace>\<lambda>rv. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
proof (induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (subst cap_revoke.simps)

    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps")
            apply ((wp preemption_point_inv' | simp add: integrity_subjects_def pas_refined_def)+)[1]
           apply (wp select_ext_weak_wp cap_delete_respects cap_delete_pas_refined
                 | simp split del: if_split | wp (once) hoare_vcg_const_imp_lift hoare_drop_imps)+
    by (auto simp: emptyable_def descendants_of_def
             dest: reply_slot_not_descendant
            intro: cca_owned)
qed

lemmas cap_revoke_respects[wp]
    = cap_revoke_respects'[of _ True, THEN use_spec(2), THEN validE_valid,
                           THEN hoare_conjD1, simplified]

lemmas cap_revoke_pas_refined[wp]
    = cap_revoke_respects'[of _ False, THEN use_spec(2), THEN validE_valid,
                           THEN hoare_conjD2, simplified]

(* MOVE *)
lemma empty_slot_cte_wp_at:
  "\<lbrace>\<lambda>s. (p = slot \<longrightarrow> P cap.NullCap) \<and> (p \<noteq> slot \<longrightarrow> cte_wp_at P p s)\<rbrace>
      empty_slot slot free_irq
   \<lbrace>\<lambda>_ s. cte_wp_at P p s\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp empty_slot_caps_of_state)
  apply (simp add: cte_wp_at_caps_of_state)
  done

lemma valid_specE_validE:
  "s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s'. s = s' \<and> P s'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>R\<rbrace>"
  unfolding spec_validE_def
  apply (erule hoare_pre)
  apply simp
  done

lemma deleting_irq_handler_caps_of_state_nullinv:
  "\<lbrace>\<lambda>s. \<forall>p. P (caps_of_state s(p \<mapsto> cap.NullCap))\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  unfolding deleting_irq_handler_def
  including no_pre
  apply (wp cap_delete_one_caps_of_state hoare_drop_imps)
  apply (rule hoare_post_imp [OF _ get_irq_slot_inv])
  apply fastforce
  done

lemma finalise_cap_caps_of_state_nullinv:
  "\<lbrace>\<lambda>s. P (caps_of_state s) \<and> (\<forall>p. P (caps_of_state s(p \<mapsto> cap.NullCap)))\<rbrace>
     finalise_cap cap final
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (cases cap;
      wpsimp wp: suspend_caps_of_state unbind_notification_caps_of_state
                 unbind_notification_cte_wp_at
                 hoare_vcg_all_lift hoare_drop_imps
                 deleting_irq_handler_caps_of_state_nullinv
           simp: fun_upd_def[symmetric] if_apply_def2 split_del: if_split)

lemma finalise_cap_cte_wp_at_nullinv:
  "\<lbrace>\<lambda>s. P cap.NullCap \<and> cte_wp_at P p s\<rbrace>
     finalise_cap cap final
   \<lbrace>\<lambda>rv s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp finalise_cap_caps_of_state_nullinv)
  apply simp
  done

lemma finalise_cap_fst_ret:
  "\<lbrace>\<lambda>s. P cap.NullCap \<and> (\<forall>a b c. P (cap.Zombie a b c)) \<rbrace>
     finalise_cap cap is_final
   \<lbrace>\<lambda>rv s. P (fst rv)\<rbrace>"
  including no_pre
  apply (cases cap, simp_all add: arch_finalise_cap_def split del: if_split)
  apply (wp | simp add: comp_def split del: if_split | fastforce)+
  apply (rule hoare_pre)
  apply (wp | simp | (rule hoare_pre, wpc))+
  done

lemma rec_del_preserves_cte_zombie_null:
  assumes P_Null: "P (NullCap)"
  assumes P_Zombie: "\<And>word x y. P (Zombie word x y)"
  shows "s \<turnstile> \<lbrace>\<lambda>s. ((slot_rdcall call \<noteq> p \<or> exposed_rdcall call)
                         \<longrightarrow> cte_wp_at P p s)
                    \<and> (case call of ReduceZombieCall remove slot _
                        \<Rightarrow> cte_wp_at ((=) remove) slot s | _ \<Rightarrow> True)\<rbrace>
              rec_del call
             \<lbrace>\<lambda>_ s. (slot_rdcall call \<noteq> p \<or> exposed_rdcall call)
                         \<longrightarrow> cte_wp_at P p s\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
proof (induct rule: rec_del.induct, simp_all only: rec_del_fails)
  case (1 slot exposed s)

  show ?case
    apply (insert P_Null)
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (wp static_imp_wp | simp)+
    apply (wp empty_slot_cte_wp_at)[1]
    apply (rule spec_strengthen_postE)
    apply (rule hoare_pre_spec_validE)
    apply (rule "1.hyps")
    apply simp
    apply clarsimp
    done
next
  case (2 slot exposed s)

  show ?case
    apply (insert P_Null)
    apply (subst rec_del.simps)
    apply (simp only: split_def without_preemption_def
                      rec_del_call.simps)
    apply (wp static_imp_wp)
    apply (wp set_cap_cte_wp_at')[1]
    apply (wp "2.hyps"[simplified without_preemption_def rec_del_call.simps])
         apply ((wp preemption_point_inv | simp)+)[1]
        apply simp
        apply (rule "2.hyps"[simplified exposed_rdcall.simps slot_rdcall.simps
                                        simp_thms disj_not1], simp_all)[1]
       apply (simp add: cte_wp_at_caps_of_state)
       apply wp+
      apply (rule_tac Q = "\<lambda>rv' s. (slot \<noteq> p \<or> exposed \<longrightarrow> cte_wp_at P p s) \<and> P (fst rv')
                             \<and> cte_at slot s" in hoare_post_imp)
       apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (wp static_imp_wp set_cap_cte_wp_at' finalise_cap_cte_wp_at_nullinv finalise_cap_fst_ret get_cap_wp
         | simp add: is_final_cap_def)+
    apply (clarsimp simp add: P_Zombie is_cap_simps cte_wp_at_caps_of_state)+
    done
next
  case 3
  show ?case
    apply (simp add: cte_wp_at_caps_of_state)
    apply wp+
    apply clarsimp
    apply (simp add: P_Zombie is_cap_simps)
    done
next
  case (4 ptr bits n slot s)
  show ?case
    apply (subst rec_del.simps)
    apply wp
        apply (simp add: cte_wp_at_caps_of_state)
        apply wp+
      apply simp
      apply (wp get_cap_wp)[1]
     apply (rule spec_strengthen_postE)
      apply (rule spec_valid_conj_liftE1)
       apply (rule rec_del_delete_cases)
      apply (rule "4.hyps", assumption+)
     apply simp
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (auto simp: is_cap_simps P_Zombie P_Null)[1]
    apply wp+
    apply (clarsimp simp: cte_wp_at_caps_of_state P_Zombie is_cap_simps)
    done
qed

lemma nullcap_not_pg_cap:
  "is_pg_cap NullCap \<longrightarrow> has_cancel_send_rights NullCap"
  by (clarsimp simp: is_pg_cap_def)

lemma zombie_not_pg_cap:
  "is_pg_cap (Zombie word x y) \<longrightarrow> has_cancel_send_rights (Zombie word x y)"
  by (clarsimp simp: is_pg_cap_def)

lemmas rec_del_has_cancel_send_rights' =
           rec_del_preserves_cte_zombie_null[where P="\<lambda>cap. is_pg_cap cap
                                                        \<longrightarrow> has_cancel_send_rights cap",
                                             OF nullcap_not_pg_cap zombie_not_pg_cap]

lemma rec_del_preserves_cte_zombie_null_insts:
  assumes P_Null: "P (NullCap)"
  assumes P_Zombie: "\<And>word x y. P (Zombie word x y)"
  shows "\<lbrace>cte_wp_at P p\<rbrace> rec_del (FinaliseSlotCall slot True) \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>,-"
        "\<lbrace>cte_wp_at P p\<rbrace> cap_delete slot \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>,-"
  apply (simp add: validE_R_def P_Null P_Zombie cap_delete_def
        | rule use_spec spec_strengthen_postE[OF hoare_pre_spec_validE
                            [OF rec_del_preserves_cte_zombie_null[where P=P]]]
        | wp)+
done

lemmas rec_del_has_cancel_send_rights_insts =
           rec_del_preserves_cte_zombie_null_insts[where P="\<lambda>cap. is_pg_cap cap
                                                              \<longrightarrow> has_cancel_send_rights cap",
                                                   OF nullcap_not_pg_cap zombie_not_pg_cap]

lemma cap_revoke_preserves_cte_zombie_null:
  fixes p
  assumes Q_Null: "Q (NullCap)"
  assumes Q_Zombie: "\<And>word x y. Q (Zombie word x y)"
  defines "P \<equiv> cte_wp_at (\<lambda>cap. Q cap) p"
  shows "s \<turnstile> \<lbrace>P\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. \<top>\<rbrace>"
proof (induct rule: cap_revoke.induct)
  case (1 slot)
  show ?case
    apply (subst cap_revoke.simps)
    apply (unfold P_def)
     apply (wp "1.hyps"[unfolded P_def], simp+)
           apply (wp preemption_point_inv hoare_drop_imps select_wp
                     rec_del_preserves_cte_zombie_null_insts[where P=Q]
                  | simp add: Q_Null Q_Zombie)+
    done
qed

lemmas cap_revoke_has_cancel_send_rights' =
                  cap_revoke_preserves_cte_zombie_null[where Q="\<lambda>cap. is_pg_cap cap
                                                                  \<longrightarrow> has_cancel_send_rights cap",
                                                       OF nullcap_not_pg_cap zombie_not_pg_cap]

lemmas cap_revoke_has_cancel_send_rights
    = cap_revoke_has_cancel_send_rights'[THEN use_spec(2), folded validE_R_def]

lemma invoke_cnode_respects:
  "\<lbrace>integrity aag X st and authorised_cnode_inv aag ci
          and (\<lambda>s. is_subject aag (cur_thread s)) and pas_refined aag
          and einvs and simple_sched_action and valid_cnode_inv ci
          and cnode_inv_auth_derivations ci\<rbrace>
     invoke_cnode ci \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: invoke_cnode_def authorised_cnode_inv_def
            split: Invocations_A.cnode_invocation.split,
         safe)
  apply (wp get_cap_wp cap_insert_integrity_autarch
            cap_revoke_respects cap_delete_respects
            | wpc | simp add: real_cte_emptyable_strg is_transferable_weak_derived
            | clarsimp simp: cte_wp_at_caps_of_state invs_valid_objs invs_sym_refs
                             cnode_inv_auth_derivations_def
            | drule(2) auth_derived_caps_of_state_impls
            | rule hoare_pre | rule cca_direct)+
  apply (auto simp: cap_auth_conferred_def cap_rights_to_auth_def aag_cap_auth_def)
  done

lemma set_cap_cte_wp_at_separation:
  "\<lbrace> cte_wp_at P slot and K(slot \<noteq> slot') \<rbrace>
     set_cap cap slot'
   \<lbrace>\<lambda>_. cte_wp_at P slot \<rbrace>"
  by (wpsimp simp: cte_wp_at_caps_of_state[abs_def])

(* FIXME MOVE*)
lemma cap_move_cte_wp_at_separation:
  "\<lbrace> cte_wp_at P slot and K(slot \<noteq> src \<and> slot \<noteq> dest) \<rbrace>
     cap_move cap src dest
   \<lbrace>\<lambda>_. cte_wp_at P slot \<rbrace>"
  by (wpsimp wp: dxo_wp_weak set_cdt_cte_wp_at set_cap_cte_wp_at_separation
           simp: cap_move_def cte_wp_at_caps_of_state)

(* FIXME MOVE *)
lemma cap_move_empty_src_slot:
  "\<lbrace> K(src \<noteq> dest) \<rbrace>
     cap_move cap src dest
   \<lbrace>\<lambda>_. cte_wp_at ((=) NullCap) src \<rbrace>"
  apply (simp add:cap_move_def)
  apply (wp dxo_wp_weak set_cdt_cte_wp_at set_cap_cte_wp_at_separation)
         apply simp
        apply (wp dxo_wp_weak set_cdt_cte_wp_at set_cap_sets_wp)+
  apply simp
  done

lemma is_derived_is_transferable:
  "\<lbrakk> is_derived m slot child_cap parent_cap; is_transferable_cap parent_cap \<rbrakk> \<Longrightarrow>
   is_transferable_cap child_cap"
  apply (erule is_transferable_capE)
  apply simp
  apply (simp add:is_derived_def is_cap_simps)
  done

lemma invoke_cnode_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and einvs and simple_sched_action
          and valid_cnode_inv ci and (\<lambda>s. is_subject aag (cur_thread s))
          and cnode_inv_auth_derivations ci and authorised_cnode_inv aag ci\<rbrace>
     invoke_cnode ci
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp add:cap_insert_pas_refined cap_delete_pas_refined cap_revoke_pas_refined
             get_cap_wp cap_move_empty_src_slot
             | wpc
             | simp split del: if_split
             | wp (once) cap_move_cte_wp_at_separation)+
  by (cases ci;
      simp add: authorised_cnode_inv_def
                cnode_inv_auth_derivations_def integrity_def;
      (clarsimp simp: cte_wp_at_caps_of_state pas_refined_refl cap_links_irq_def
                      real_cte_emptyable_strg
      | drule auth_derived_caps_of_state_impls
      | fastforce intro: cap_cur_auth_caps_of_state dest: is_derived_is_transferable)+)

end

end
