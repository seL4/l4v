(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Syscall_AC
imports
  Ipc_AC
  Tcb_AC
  Interrupt_AC
  DomainSepInv
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  authorised_invocation :: "'a PAS \<Rightarrow> Invocations_A.invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "authorised_invocation aag i \<equiv> \<lambda>s. case i of
     Invocations_A.InvokeUntyped i' \<Rightarrow> valid_untyped_inv i' s \<and> (authorised_untyped_inv aag i') \<and> ct_active s
   | Invocations_A.InvokeEndpoint epptr badge can_grant can_grant_reply \<Rightarrow>
               \<exists>ep. ko_at (Endpoint ep) epptr s \<and>
                    (can_grant \<longrightarrow>  (\<forall>r \<in> ep_q_refs_of ep. snd r = EPRecv \<longrightarrow> is_subject aag (fst r))
                                  \<and> aag_has_auth_to aag Grant epptr \<and> aag_has_auth_to aag Call epptr) \<and>
                    (can_grant_reply \<longrightarrow> aag_has_auth_to aag Call epptr)
             \<and> aag_has_auth_to aag SyncSend epptr
   | Invocations_A.InvokeNotification ep badge \<Rightarrow> aag_has_auth_to aag Notify ep
   | Invocations_A.InvokeReply thread slot grant \<Rightarrow>
       (grant \<longrightarrow> is_subject aag thread) \<and> is_subject aag (fst slot) \<and> aag_has_auth_to aag Reply thread
   | Invocations_A.InvokeTCB i' \<Rightarrow> Tcb_AI.tcb_inv_wf i' s \<and> authorised_tcb_inv aag i'
   | Invocations_A.InvokeDomain thread slot \<Rightarrow> False
   | Invocations_A.InvokeCNode i' \<Rightarrow> authorised_cnode_inv aag i' s \<and> is_subject aag (cur_thread s)
           \<and> cnode_inv_auth_derivations i' s
   | Invocations_A.InvokeIRQControl i' \<Rightarrow> authorised_irq_ctl_inv aag i'
   | Invocations_A.InvokeIRQHandler i' \<Rightarrow> authorised_irq_hdl_inv aag i'
   | Invocations_A.InvokeArchObject i' \<Rightarrow> valid_arch_inv i' s \<and> authorised_arch_inv aag i' \<and> ct_active s"

lemma perform_invocation_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag
          and einvs and simple_sched_action and valid_invocation oper
          and is_subject aag \<circ> cur_thread
          and authorised_invocation aag oper\<rbrace>
    perform_invocation blocking calling oper
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (cases oper, simp_all)
  apply (simp add: authorised_invocation_def validE_R_def[symmetric] invs_valid_objs
       | wp invoke_untyped_pas_refined send_ipc_pas_refined send_signal_pas_refined
            do_reply_transfer_pas_refined invoke_tcb_pas_refined invoke_cnode_pas_refined
            invoke_irq_control_pas_refined invoke_irq_handler_pas_refined
            invoke_arch_pas_refined decode_cnode_invocation_auth_derived
       | fastforce)+
  done

lemma ntfn_gives_obj_at:
  "invs s \<Longrightarrow>
   (\<exists>ntfn. ko_at (Notification ntfn) ntfnptr s
           \<and> (\<forall>x\<in>ntfn_q_refs_of (ntfn_obj ntfn).
                  (\<lambda>(t, rt). obj_at (\<lambda>tcb. ko_at tcb t s) t s) x)) = ntfn_at ntfnptr s"
  apply (rule iffI)
   apply (clarsimp simp: obj_at_def is_ntfn)
  apply (clarsimp simp: obj_at_def is_ntfn)
  apply (drule (1) ntfn_queued_st_tcb_at [where P = \<top>, unfolded obj_at_def, simplified])
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: st_tcb_def2 dest!: get_tcb_SomeD)
  done

(* ((=) st) -- too strong, the thread state of the calling thread changes. *)
lemma perform_invocation_respects:
  "\<lbrace>pas_refined aag and integrity aag X st
          and einvs and simple_sched_action and valid_invocation oper
          and authorised_invocation aag oper
          and is_subject aag \<circ> cur_thread
          and (\<lambda>s. \<forall>p ko. kheap s p = Some ko \<longrightarrow> \<not> (is_tcb ko \<and> p = cur_thread st)  \<longrightarrow> kheap st p = Some ko)
          \<rbrace>
    perform_invocation blocking calling oper
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  supply [wp] = invoke_untyped_integrity send_ipc_integrity_autarch send_signal_respects
                do_reply_transfer_respects invoke_tcb_respects invoke_cnode_respects
                invoke_arch_respects invoke_irq_control_respects invoke_irq_handler_respects
  supply [simp] = authorised_invocation_def
  proof (cases oper)
  case InvokeEndpoint
    show ?thesis
      unfolding InvokeEndpoint
      apply (rule hoare_pre)
      apply wpsimp
      apply (fastforce simp: obj_at_def is_tcb split: if_split_asm)
      done
  next
  case InvokeNotification
    show ?thesis
      unfolding InvokeNotification
      apply (rule hoare_pre)
      apply wpsimp
      apply fastforce
      done
  next
  case InvokeReply
    show ?thesis
      unfolding InvokeReply
      apply (rule hoare_pre)
      apply wpsimp
      apply clarsimp
      apply (fastforce simp: is_reply_cap_to_def cur_tcb_def dest!: invs_cur)
      done
  qed (simp, rule hoare_pre, wpsimp, fastforce)+

declare AllowSend_def[simp] AllowRecv_def[simp]

lemma hoare_conjunct1_R:
  "\<lbrace> P \<rbrace> f \<lbrace> \<lambda> r s. Q r s \<and> Q' r s\<rbrace>,- \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,-"
  apply(auto intro: hoare_post_imp_R)
  done

lemma hoare_conjunct2_R:
  "\<lbrace> P \<rbrace> f \<lbrace> \<lambda> r s. Q r s \<and> Q' r s\<rbrace>,- \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q' \<rbrace>,-"
  apply(auto intro: hoare_post_imp_R)
  done

lemma decode_invocation_authorised:
  "\<lbrace>pas_refined aag and valid_cap cap and invs and ct_active and cte_wp_at ((=) cap) slot
           and ex_cte_cap_to slot
           and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_to r s)
           and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))
           and (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. real_cte_at (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to is_cnode_cap (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at (interrupt_derived (fst x)) (snd x) s)
           and (is_subject aag \<circ> cur_thread) and
              K (is_subject aag (fst slot) \<and> pas_cap_cur_auth aag cap
                \<and> (\<forall>slot \<in> set excaps. is_subject aag (fst (snd slot)))
                \<and> (\<forall>slot \<in> set excaps. pas_cap_cur_auth aag (fst slot)))
           and domain_sep_inv (pasMaySendIrqs aag) st'\<rbrace>
    decode_invocation info_label args ptr slot cap excaps
   \<lbrace>\<lambda>rv. authorised_invocation aag rv\<rbrace>, -"
  unfolding decode_invocation_def
  apply (rule hoare_pre)
   apply (wp decode_untyped_invocation_authorised
              decode_cnode_invocation_auth_derived
              decode_cnode_inv_authorised
              decode_tcb_invocation_authorised decode_tcb_inv_wf
              decode_arch_invocation_authorised
              | strengthen cnode_eq_strg
              | wpc | simp add: comp_def authorised_invocation_def decode_invocation_def
                        split del: if_split del: hoare_True_E_R
              | wp (once) hoare_FalseE_R)+

  apply (clarsimp simp: aag_has_Control_iff_owns split_def aag_cap_auth_def)
  apply (cases cap, simp_all)
          apply (fastforce simp: cte_wp_at_caps_of_state)
         apply (clarsimp simp: valid_cap_def obj_at_def is_ep cap_auth_conferred_def
                               cap_rights_to_auth_def ball_Un)
         apply (fastforce simp: valid_cap_def cap_auth_conferred_def cap_rights_to_auth_def
                                obj_at_def is_ep
                        intro!: owns_ep_owns_receivers)
        apply (fastforce simp: cap_auth_conferred_def cap_rights_to_auth_def)
       apply (clarsimp simp: cap_auth_conferred_def cap_rights_to_auth_def
                             pas_refined_Control[symmetric] reply_cap_rights_to_auth_def)

      apply ((clarsimp simp: valid_cap_def is_cap_simps pas_refined_all_auth_is_owns
                            ex_cte_cap_wp_to_weakenE[OF _ TrueI]
                            cap_auth_conferred_def cap_rights_to_auth_def
               | rule conjI | (subst split_paired_Ex[symmetric], erule exI)
               | erule cte_wp_at_weakenE
               | drule(1) bspec
               | erule eq_no_cap_to_obj_with_diff_ref)+)[1]
     apply (simp only: domain_sep_inv_def)
    apply (rule impI, erule subst, rule pas_refined_sita_mem [OF sita_controlled],
           auto simp: cte_wp_at_caps_of_state)[1]

   apply (clarsimp simp add: cap_links_irq_def )
   apply (drule (1) pas_refined_Control, simp)

  apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def)
  apply (fastforce dest!: pas_refined_Control)
  done

lemma in_extended: "(u,a) \<in> fst (do_extended_op f s) \<Longrightarrow> \<exists>e. a = (trans_state (\<lambda>_. e) s)"
   apply (clarsimp simp add: do_extended_op_def bind_def gets_def return_def get_def
                   mk_ef_def modify_def select_f_def put_def trans_state_update')
   apply force
   done

lemma set_thread_state_authorised[wp]:
  "\<lbrace>authorised_invocation aag i and (\<lambda>s. thread = cur_thread s) and valid_objs\<rbrace>
     set_thread_state thread Structures_A.thread_state.Restart
   \<lbrace>\<lambda>rv. authorised_invocation aag i\<rbrace>"
  apply (cases i)
           apply (simp_all add: authorised_invocation_def)
          apply (wp sts_valid_untyped_inv ct_in_state_set
                    hoare_vcg_ex_lift sts_obj_at_impossible
                  | simp)+
     apply (rename_tac cnode_invocation)
     apply (case_tac cnode_invocation,
            simp_all add: cnode_inv_auth_derivations_def authorised_cnode_inv_def)[1]
           apply (wp set_thread_state_cte_wp_at | simp)+
  apply (rename_tac arch_invocation)
  apply (case_tac arch_invocation, simp_all add: valid_arch_inv_def)[1]
      apply (rename_tac page_table_invocation)
      apply (case_tac page_table_invocation, simp_all add: valid_pti_def)[1]
       apply (wp sts_typ_ats sts_obj_at_impossible ct_in_state_set
                 hoare_vcg_ex_lift hoare_vcg_conj_lift
               | simp add: valid_pdi_def)+
     apply (rename_tac asid_control_invocation)
     apply (case_tac asid_control_invocation, simp_all add: valid_aci_def)
    apply (wp ct_in_state_set | simp)+
  apply (rename_tac asid_pool_invocation)
  apply (case_tac asid_pool_invocation; simp add: valid_apinv_def)
  apply (wp sts_obj_at_impossible ct_in_state_set
            hoare_vcg_ex_lift
          | simp)+
  done

lemma sts_first_restart:
  "\<lbrace>(=) st and (\<lambda>s. thread = cur_thread s)\<rbrace>
     set_thread_state thread Structures_A.thread_state.Restart
   \<lbrace>\<lambda>rv s. \<forall>p ko. kheap s p = Some ko \<longrightarrow>
           (is_tcb ko \<longrightarrow> p \<noteq> cur_thread st) \<longrightarrow> kheap st p = Some ko\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp wp: set_object_wp dxo_wp_weak simp: is_tcb)

lemma lcs_reply_owns:
  "\<lbrace>pas_refined aag and K (is_subject aag thread)\<rbrace>
    lookup_cap_and_slot thread ptr
   \<lbrace>\<lambda>rv s. \<forall>ep. (\<exists>m R. fst rv = cap.ReplyCap ep m R \<and> AllowGrant \<in> R) \<longrightarrow> is_subject aag ep\<rbrace>, -"
  apply (rule hoare_post_imp_R)
   apply (rule hoare_pre)
    apply (rule hoare_vcg_conj_lift_R [where S = "K (pas_refined aag)"])
     apply (rule lookup_cap_and_slot_cur_auth)
    apply (simp | wp lookup_cap_and_slot_inv)+
  apply (force simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
               dest: aag_Control_into_owns)
  done

crunch pas_refined[wp]: reply_from_kernel "pas_refined aag"
  (simp: split_def)

lemma lookup_cap_and_slot_valid_fault3:
  "\<lbrace>valid_objs\<rbrace> lookup_cap_and_slot thread cptr
   -,
   \<lbrace>\<lambda>ft s. valid_fault (ExceptionTypes_A.CapFault (of_bl cptr) rp ft)\<rbrace>"
  apply (unfold validE_E_def)
  apply (rule hoare_post_impErr)
    apply (rule lookup_cap_and_slot_valid_fault)
   apply auto
  done

definition guarded_pas_domain
where
  "guarded_pas_domain aag \<equiv>
     \<lambda>s. cur_thread s \<noteq> idle_thread s \<longrightarrow>
         pasObjectAbs aag (cur_thread s) \<in> pasDomainAbs aag (cur_domain s)"


lemma guarded_pas_domain_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_domain s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>guarded_pas_domain aag\<rbrace> f \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  apply (simp add: guarded_pas_domain_def)
  apply (rule hoare_pre)
  apply (wps a b c)
  apply wp
  apply simp
  done

lemma guarded_to_cur_domain:
  "\<lbrakk>invs s; ct_in_state x s; \<not> x IdleThreadState; guarded_pas_domain aag s;
    is_subject aag (cur_thread s)\<rbrakk>
   \<Longrightarrow> pas_cur_domain aag s"
  by (auto simp: invs_def valid_state_def valid_idle_def pred_tcb_at_def obj_at_def
                 ct_in_state_def guarded_pas_domain_def)


lemma handle_invocation_pas_refined:
  shows "\<lbrace>pas_refined aag and guarded_pas_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'
          and einvs and ct_active and schact_is_rct
          and is_subject aag \<circ> cur_thread\<rbrace>
     handle_invocation calling blocking
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: handle_invocation_def split_def)
  apply (cases blocking, simp)
   apply (rule hoare_pre)
    by (((wp syscall_valid without_preemption_wp
              handle_fault_pas_refined set_thread_state_pas_refined
              set_thread_state_runnable_valid_sched
              perform_invocation_pas_refined
              hoare_vcg_conj_lift hoare_vcg_all_lift
         | wpc
         | rule hoare_drop_imps
         | simp add: if_apply_def2 conj_comms split del: if_split
               del: hoare_True_E_R)+),
        ((wp lookup_extra_caps_auth lookup_extra_caps_authorised
              decode_invocation_authorised
              lookup_cap_and_slot_authorised
              lookup_cap_and_slot_cur_auth
              as_user_pas_refined
              lookup_cap_and_slot_valid_fault3
         | simp add: comp_def runnable_eq_active)+),
         (auto intro: guarded_to_cur_domain
               simp: ct_in_state_def st_tcb_at_def live_def hyp_live_def
               intro: if_live_then_nonz_capD)[1])+

lemma handle_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and guarded_pas_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'
          and einvs and ct_active and schact_is_rct
          and is_subject aag \<circ> cur_thread
          and ((=) st)\<rbrace>
     handle_invocation calling blocking
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: handle_invocation_def split_def)
  apply (wp syscall_valid without_preemption_wp handle_fault_integrity_autarch
            reply_from_kernel_integrity_autarch
            set_thread_state_integrity_autarch
            hoare_vcg_conj_lift
            hoare_vcg_all_lift_R hoare_vcg_all_lift
         | rule hoare_drop_imps
         | wpc
         | simp add: if_apply_def2
                split del: if_split)+
         apply (simp add: conj_comms pred_conj_def comp_def if_apply_def2 split del: if_split
               | wp perform_invocation_respects set_thread_state_pas_refined
                  set_thread_state_authorised
                  set_thread_state_runnable_valid_sched
                  set_thread_state_integrity_autarch
                  sts_first_restart
                  decode_invocation_authorised
                  lookup_extra_caps_auth lookup_extra_caps_authorised
                  set_thread_state_integrity_autarch
                  lookup_cap_and_slot_cur_auth lookup_cap_and_slot_authorised
                  hoare_vcg_const_imp_lift perform_invocation_pas_refined
                  set_thread_state_ct_st      hoare_vcg_const_imp_lift_R
                  lookup_cap_and_slot_valid_fault3
               | (rule valid_validE, strengthen invs_vobjs_strgs))+
  by (fastforce intro: st_tcb_ex_cap' guarded_to_cur_domain
                 simp: ct_in_state_def runnable_eq_active)

crunch pas_refined[wp]: delete_caller_cap "pas_refined aag"

lemma invs_sym_refs_strg:
  "invs s \<longrightarrow> sym_refs (state_refs_of s)" by clarsimp

lemma handle_recv_pas_refined:
  "\<lbrace>pas_refined aag and invs and is_subject aag \<circ> cur_thread\<rbrace>
     handle_recv is_blocking
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: handle_recv_def Let_def lookup_cap_def split_def)
  apply (wp handle_fault_pas_refined receive_ipc_pas_refined receive_signal_pas_refined
            get_cap_auth_wp [where aag=aag] lookup_slot_for_cnode_op_authorised
            lookup_slot_for_thread_authorised lookup_slot_for_thread_cap_fault
            hoare_vcg_all_lift_R get_simple_ko_wp
       | wpc | simp
       | (rule_tac Q="\<lambda>rv s. invs s \<and> is_subject aag thread
                             \<and> (pasSubject aag, Receive, pasObjectAbs aag thread) \<in> pasPolicy aag"
                in hoare_strengthen_post,
          wp, clarsimp simp: invs_valid_objs invs_sym_refs))+
     apply (rule_tac Q' = "\<lambda>rv s. pas_refined aag s \<and> invs s \<and> tcb_at thread s
                                   \<and> cur_thread s = thread \<and> is_subject aag (cur_thread s)
                                   \<and> is_subject aag thread" in hoare_post_imp_R [rotated])
      apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def
                             cap_rights_to_auth_def valid_fault_def)
     apply (wp user_getreg_inv | strengthen invs_vobjs_strgs invs_sym_refs_strg | simp)+
  apply clarsimp
  done

crunch respects[wp]: delete_caller_cap "integrity aag X st"

lemma invs_mdb_strgs: "invs s \<longrightarrow> valid_mdb s"
  by auto

lemma handle_recv_integrity:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and is_subject aag \<circ> cur_thread
      and K(valid_mdb st \<and> valid_objs st)\<rbrace>
     handle_recv is_blocking
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: handle_recv_def Let_def lookup_cap_def split_def)
  apply (wp handle_fault_integrity_autarch receive_ipc_integrity_autarch
            receive_signal_integrity_autarch lookup_slot_for_thread_authorised
            lookup_slot_for_thread_cap_fault get_cap_auth_wp [where aag=aag] get_simple_ko_wp
        | wpc
        | simp
        | rule_tac Q="\<lambda>rv s. invs s \<and> is_subject aag thread
                           \<and> (pasSubject aag, Receive, pasObjectAbs aag thread) \<in> pasPolicy aag"
                in hoare_strengthen_post, wp, clarsimp simp: invs_valid_objs invs_sym_refs)+
     apply (rule_tac Q' = "\<lambda>rv s. pas_refined aag s \<and> einvs s \<and> is_subject aag (cur_thread s)
                         \<and> tcb_at thread s \<and> cur_thread s = thread
            \<and> is_subject aag thread \<and> integrity aag X st s" in hoare_post_imp_R [rotated])
      apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def
                             cap_rights_to_auth_def valid_fault_def)
     apply (wp user_getreg_inv
           | strengthen invs_vobjs_strgs invs_sym_refs_strg invs_mdb_strgs
           | simp)+
  apply clarsimp
  done

lemma handle_reply_pas_refined[wp]:
  "\<lbrace> pas_refined aag and invs and is_subject aag \<circ> cur_thread\<rbrace>
     handle_reply
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  unfolding handle_reply_def
  apply (rule hoare_pre)
   apply (wp do_reply_transfer_pas_refined get_cap_auth_wp [where aag = aag]| wpc)+
  by (force simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
           intro: aag_Control_into_owns)

lemma handle_reply_respects:
  "\<lbrace>integrity aag X st and pas_refined aag
          and einvs
          and is_subject aag \<circ> cur_thread\<rbrace>
     handle_reply
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  unfolding handle_reply_def
  apply (rule hoare_pre)
  apply (wp do_reply_transfer_respects get_cap_auth_wp [where aag = aag]| wpc)+
  apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                         cur_tcb_def cte_wp_at_caps_of_state is_reply_cap_to_def
                  intro: aag_Control_into_owns
                   dest: invs_cur)
  done

lemma ethread_set_time_slice_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
     ethread_set (tcb_time_slice_update f) thread
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(a, b)" in ballE)
   apply force
  apply (erule notE)
  apply (erule domains_of_state_aux.cases, simp add: get_etcb_def split: if_split_asm)
   apply (force intro: domtcbs)+
  done

lemma thread_set_time_slice_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
     thread_set_time_slice tptr time
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: thread_set_time_slice_def | wp)+
  done

lemma dec_domain_time_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
     dec_domain_time
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: dec_domain_time_def | wp)+
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  done

crunch pas_refined[wp]: timer_tick "pas_refined aag"
  (wp_del: timer_tick_extended.pas_refined_tcb_domain_map_wellformed)

lemma handle_interrupt_pas_refined:
  "\<lbrace>pas_refined aag\<rbrace>
     handle_interrupt irq
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: handle_interrupt_def)
  apply (rule conjI; rule impI;rule hoare_pre)
  apply (wp send_signal_pas_refined get_cap_wp
       | wpc
       | simp add: get_irq_slot_def get_irq_state_def handle_reserved_irq_def)+
  done

lemma dec_domain_time_integrity[wp]:
  "\<lbrace>integrity aag X st\<rbrace>
        dec_domain_time
       \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: dec_domain_time_def | wp)+
  apply (clarsimp simp: integrity_subjects_def)
  done

lemma timer_tick_integrity[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))\<rbrace>
        timer_tick
       \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: timer_tick_def)
  apply (wp ethread_set_integrity_autarch gts_wp
           | wpc | simp add: thread_set_time_slice_def split del: if_split)+
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
  done

lemma handle_interrupt_integrity_autarch:
  "\<lbrace>integrity aag X st and pas_refined aag
          and invs and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))
          and K (is_subject_irq aag irq)\<rbrace>
     handle_interrupt irq
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: handle_interrupt_def  cong: irq_state.case_cong maskInterrupt_def
                   ackInterrupt_def resetTimer_def )
  apply (rule conjI; rule impI; rule hoare_pre)
  apply (wp (once) send_signal_respects get_cap_auth_wp [where aag = aag] dmo_mol_respects
       | simp add: get_irq_slot_def get_irq_state_def ackInterrupt_def resetTimer_def
                   handle_reserved_irq_def
       | wp dmo_no_mem_respects
       | wpc)+
  apply (fastforce simp: is_cap_simps aag_cap_auth_def cap_auth_conferred_def
                         cap_rights_to_auth_def)
  done

lemma hacky_ipc_Send:
  "\<lbrakk> (pasObjectAbs aag (interrupt_irq_node s irq), Notify, pasObjectAbs aag p) \<in> pasPolicy aag;
     pas_refined aag s; pasMaySendIrqs aag \<rbrakk>
   \<Longrightarrow> aag_has_auth_to aag Notify p"
  unfolding pas_refined_def
  apply (clarsimp simp: policy_wellformed_def irq_map_wellformed_aux_def)
  apply (drule spec [where x = "pasIRQAbs aag irq"], drule spec [where x = "pasObjectAbs aag p"],
         erule mp)
  apply simp
  done


lemma handle_interrupt_integrity:
  "\<lbrace>integrity aag X st and pas_refined aag and invs
       and (\<lambda>s. pasMaySendIrqs aag \<or> interrupt_states s irq \<noteq> IRQSignal)
       and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))\<rbrace>
     handle_interrupt irq
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: handle_interrupt_def maskInterrupt_def ackInterrupt_def resetTimer_def
             cong: irq_state.case_cong bind_cong)
  apply (rule conjI; rule impI; rule hoare_pre)
  apply (wp (once) send_signal_respects get_cap_wp dmo_mol_respects dmo_no_mem_respects
       | wpc
       | simp add: get_irq_slot_def get_irq_state_def ackInterrupt_def resetTimer_def
                   handle_reserved_irq_def)+
  apply clarsimp
  apply (rule conjI, fastforce)+ \<comment> \<open>valid_objs etc.\<close>
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule_tac s = s in hacky_ipc_Send [where irq = irq])
   apply (drule (1) cap_auth_caps_of_state)
   apply (clarsimp simp: aag_cap_auth_def is_cap_simps cap_auth_conferred_def
                         cap_rights_to_auth_def split: if_split_asm)
  apply assumption+
  done

lemma handle_vm_fault_integrity:
  "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
    handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (cases vmfault_type, simp_all)
  apply (rule hoare_pre)
  apply (wp as_user_integrity_autarch dmo_wp | simp add: getDFSR_def getFAR_def getIFSR_def)+
  done

lemma handle_vm_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
    handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (cases vmfault_type, simp_all)
  apply (wp | simp)+
  done

crunch pas_refined[wp]: handle_hypervisor_fault "pas_refined aag"
crunch cur_thread[wp]: handle_hypervisor_fault "\<lambda>s. P (cur_thread s)"
crunch integrity[wp]: handle_hypervisor_fault "integrity aag X st"

lemma handle_vm_cur_thread [wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>
    handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  apply (cases vmfault_type, simp_all)
  apply (wp | simp)+
  done

lemma handle_vm_state_refs_of [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
    handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (cases vmfault_type, simp_all)
  apply (wp | simp)+
  done

lemma handle_yield_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
    handle_yield
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  by (simp add: handle_yield_def | wp)+



lemma handle_event_pas_refined:
  "\<lbrace>pas_refined aag and guarded_pas_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'
          and einvs and schact_is_rct
          and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> is_subject aag (cur_thread s))
          and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) \<rbrace>
    handle_event ev
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (case_tac ev; simp)
      apply (rename_tac syscall)
      apply (case_tac syscall; simp add: handle_send_def handle_call_def)
            apply ((wp handle_invocation_pas_refined handle_recv_pas_refined
                       handle_fault_pas_refined
                     | simp | clarsimp)+)
     apply (fastforce simp: valid_fault_def)
    apply (wp handle_fault_pas_refined
            | simp)+
    apply (fastforce simp: valid_fault_def)
   apply (wp handle_interrupt_pas_refined handle_fault_pas_refined
             hoare_vcg_conj_lift hoare_vcg_all_lift
           | wpc
           | rule hoare_drop_imps
           | strengthen invs_vobjs_strgs
           | simp)+
  done

lemma valid_fault_Unknown [simp]:
  "valid_fault (UnknownSyscallException x)"
  by (simp add: valid_fault_def)

lemma valid_fault_User [simp]:
  "valid_fault (UserException word1 word2)"
  by (simp add: valid_fault_def)


declare hy_inv[wp del]

lemma handle_yield_integrity[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and is_subject aag \<circ> cur_thread\<rbrace>
    handle_yield
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  by (simp add: handle_yield_def | wp)+

lemma ct_in_state_machine_state_update[simp]: "ct_in_state s (st\<lparr>machine_state := x\<rparr>) = ct_in_state s st"
  apply (simp add: ct_in_state_def)
  done


lemma handle_event_integrity:
  "\<lbrace>integrity aag X st and pas_refined aag and guarded_pas_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'
          and einvs and schact_is_rct
          and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s)) and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and ((=) st)\<rbrace>
    handle_event ev
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (case_tac "ev \<noteq> Interrupt")
  apply (case_tac ev; simp)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all add: handle_send_def handle_call_def)
      apply (wp handle_recv_integrity handle_invocation_respects
                handle_reply_respects handle_fault_integrity_autarch
                handle_interrupt_integrity handle_vm_fault_integrity
                handle_reply_pas_refined handle_vm_fault_valid_fault
                handle_reply_valid_sched
                hoare_vcg_conj_lift hoare_vcg_all_lift alternative_wp select_wp
           | rule dmo_wp
           | wpc
           | simp add: getActiveIRQ_def domain_sep_inv_def
           | clarsimp
           | rule conjI hoare_vcg_E_elim
           | strengthen invs_vobjs_strgs invs_mdb_strgs
           | fastforce)+
   done

lemma set_thread_state_restart_to_running_respects:
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Structures_A.Restart) thread
          and K (pasMayActivate aag)\<rbrace>
              do pc \<leftarrow> as_user thread getRestartPC;
                 as_user thread $ setNextPC pc;
                 set_thread_state thread Structures_A.thread_state.Running
              od
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def as_user_def split_def setNextPC_def
                   getRestartPC_def setRegister_def bind_assoc getRegister_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: in_monad fun_upd_def[symmetric] cong: if_cong)
  apply (cases "is_subject aag thread")
   apply (cut_tac aag=aag in integrity_update_autarch, simp+)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def st_tcb_at_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (rule_tac tro_tcb_activate[OF refl refl])
    apply (simp add: tcb_bound_notification_reset_integrity_def ctxt_IP_update_def)+
  done

lemma activate_thread_respects:
  "\<lbrace>integrity aag X st and K (pasMayActivate aag)\<rbrace>
    activate_thread
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: activate_thread_def arch_activate_idle_thread_def)
  apply (rule hoare_pre)
  apply (wp set_thread_state_restart_to_running_respects thread_get_wp'
    | wpc | simp add: arch_activate_idle_thread_def get_thread_state_def)+
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  done

lemma activate_thread_integrity:
  "\<lbrace>integrity aag X st and (\<lambda>s. cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject aag (cur_thread s)) and valid_idle\<rbrace>
    activate_thread
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: activate_thread_def arch_activate_idle_thread_def)
  apply (rule hoare_pre)
  apply (wp gts_wp set_thread_state_integrity_autarch as_user_integrity_autarch | wpc |  simp add: arch_activate_idle_thread_def)+
  apply(clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma activate_thread_pas_refined:
  "\<lbrace> pas_refined aag \<rbrace>
    activate_thread
   \<lbrace>\<lambda>rv. pas_refined aag \<rbrace>"
  unfolding activate_thread_def arch_activate_idle_thread_def
            get_thread_state_def thread_get_def
  apply (rule hoare_pre)
  apply (wp set_thread_state_pas_refined hoare_drop_imps
             | wpc | simp)+
  done

lemma integrity_exclusive_state [iff]:
  "integrity aag X st (s\<lparr>machine_state := machine_state s \<lparr>exclusive_state := es \<rparr>\<rparr>)
   = integrity aag X st s"
  unfolding integrity_def
  by simp

lemma dmo_clearExMonitor_respects_globals[wp]:
  "\<lbrace>integrity aag X st\<rbrace>
    do_machine_op clearExMonitor
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: clearExMonitor_def | wp dmo_wp)+
  done

lemma integrity_cur_thread [iff]:
  "integrity aag X st (s\<lparr>cur_thread := v\<rparr>) = integrity aag X st s"
  unfolding integrity_def by simp

lemma tcb_sched_action_dequeue_integrity_pasMayEditReadyQueues:
  "\<lbrace>integrity aag X st and pas_refined aag and K (pasMayEditReadyQueues aag)\<rbrace>
    tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def pas_refined_def tcb_domain_map_wellformed_aux_def etcb_at_def get_etcb_def
                  split: option.splits)
  done

lemma as_user_set_register_respects_indirect:
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Structures_A.Running) thread and
    K ((\<not> is_subject aag thread \<longrightarrow> st_tcb_at receive_blocked thread st
           \<and> bound_tcb_at ((=) (Some ntfnptr)) thread st)
        \<and> (aag_has_auth_to aag Notify ntfnptr)) \<rbrace>
   as_user thread (setRegister r v)
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

lemma switch_to_thread_respects_pasMayEditReadyQueues:
  notes tcb_sched_action_dequeue_integrity[wp del]
  shows
  "\<lbrace>integrity aag X st and pas_refined aag
    and K (pasMayEditReadyQueues aag)\<rbrace>
  switch_to_thread t
  \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  unfolding switch_to_thread_def arch_switch_to_thread_def
  apply (simp add: spec_valid_def)
  apply (wp tcb_sched_action_dequeue_integrity_pasMayEditReadyQueues
                | simp add: clearExMonitor_def)+
  done

lemma switch_to_thread_respects:
  "\<lbrace>integrity aag X st and pas_refined aag
    and K (is_subject aag t) \<rbrace>
  switch_to_thread t
  \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  unfolding switch_to_thread_def arch_switch_to_thread_def
  apply (simp add: spec_valid_def)
  apply (wp | simp add: clearExMonitor_def)+
  done

text \<open>
Variants of scheduling lemmas without is_subject assumption.
See comment for @{thm tcb_sched_action_dequeue_integrity'}
\<close>
lemma switch_to_thread_respects':
  "\<lbrace>integrity aag X st and pas_refined aag
    and (\<lambda>s. pasSubject aag \<in> pasDomainAbs aag (tcb_domain (the (ekheap s t)))) \<rbrace>
  switch_to_thread t
  \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  unfolding switch_to_thread_def arch_switch_to_thread_def
  apply (simp add: spec_valid_def)
  apply (wp tcb_sched_action_dequeue_integrity'
        | simp add: clearExMonitor_def)+
  done

lemma switch_to_idle_thread_respects:
  "\<lbrace>integrity aag X st\<rbrace>
    switch_to_idle_thread
  \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  unfolding switch_to_idle_thread_def arch_switch_to_idle_thread_def
  by (wp | simp)+

lemma choose_thread_respects_pasMayEditReadyQueues:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and valid_queues and K (pasMayEditReadyQueues aag ) \<rbrace>
  choose_thread
  \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  by (simp add: choose_thread_def guarded_switch_to_def
      | wp switch_to_thread_respects_pasMayEditReadyQueues switch_to_idle_thread_respects gts_wp)+

text \<open>integrity for @{const choose_thread} without @{const pasMayEditReadyQueues}\<close>
lemma choose_thread_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and pas_cur_domain aag and einvs and valid_queues\<rbrace>
   choose_thread
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: choose_thread_def guarded_switch_to_def
        | wp switch_to_thread_respects' switch_to_idle_thread_respects gts_wp)+
  apply (clarsimp simp: pas_refined_def)
  apply (clarsimp simp: tcb_domain_map_wellformed_aux_def)
  apply (clarsimp simp: valid_queues_def is_etcb_at_def)
  apply (erule_tac x="cur_domain s" in allE)
  apply (erule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in allE)
  apply clarsimp
  apply (erule_tac x="hd (max_non_empty_queue (ready_queues s (cur_domain s)))" in ballE)
   apply (clarsimp simp: etcb_at_def)
  (* thread we're switching to is in cur_domain *)
  apply (rule_tac s = "cur_domain s" in subst)
  apply (clarsimp simp: max_non_empty_queue_def)
   apply (frule tcb_at_ekheap_dom[OF st_tcb_at_tcb_at])
    apply (simp add: valid_sched_def)
   apply (clarsimp simp: max_non_empty_queue_def)
   apply (metis (mono_tags, lifting) setcomp_Max_has_prop hd_in_set)
  (* pas_cur_domain *)
  apply assumption
  done

lemma guarded_switch_to_respects:
  "\<lbrace> integrity aag X st
     and pas_refined aag and (\<lambda>s. is_subject aag x)\<rbrace>
   guarded_switch_to x
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
   apply (simp add: guarded_switch_to_def)
   apply (simp add: choose_thread_def guarded_switch_to_def
               | wp switch_to_thread_respects switch_to_idle_thread_respects gts_wp)+
   done

lemma next_domain_integrity [wp]:
  "\<lbrace>integrity aag X st\<rbrace>
  next_domain
  \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: next_domain_def thread_set_domain_def ethread_set_def set_eobject_def Let_def | wp)+
  apply (clarsimp simp: get_etcb_def integrity_subjects_def lfp_def)
  done

lemma next_domain_tcb_domain_map_wellformed [wp]:
  "\<lbrace>tcb_domain_map_wellformed aag\<rbrace>
  next_domain
  \<lbrace>\<lambda>rv. tcb_domain_map_wellformed aag\<rbrace>"
  by (simp add: next_domain_def thread_set_domain_def ethread_set_def set_eobject_def Let_def | wp)+


lemma valid_blocked_2_valid_blocked_except[simp]:
  "valid_blocked_2 queues kh sa ct \<Longrightarrow> valid_blocked_except_2 t queues kh sa ct"
  by (clarsimp simp: valid_blocked_def valid_blocked_except_def)

(* clagged from Schedule_R *)
lemma next_domain_valid_sched:
  "\<lbrace> valid_sched and (\<lambda>s. scheduler_action s  = choose_new_thread)\<rbrace> next_domain \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: next_domain_def Let_def)
  apply (wp, simp add: valid_sched_def valid_sched_action_2_def ct_not_in_q_2_def)
  apply (simp add:valid_blocked_2_def)
  done

text \<open>
We need to use the domain of t instead of @{term "is_subject aag t"}
because t's domain may contain multiple labels. See the comment for
@{thm tcb_sched_action_dequeue_integrity'}
\<close>
lemma valid_sched_action_switch_subject_thread:
   "\<lbrakk> scheduler_action s = switch_thread t ; valid_sched_action s ;
      valid_etcbs s ; pas_refined aag s ; pas_cur_domain aag s \<rbrakk>
    \<Longrightarrow> pasObjectAbs aag t \<in> pasDomainAbs aag (tcb_domain (the (ekheap s t))) \<and>
        pasSubject aag \<in> pasDomainAbs aag (tcb_domain (the (ekheap s t)))"
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_2_def
                        switch_in_cur_domain_2_def in_cur_domain_2_def valid_etcbs_def
                        etcb_at_def st_tcb_at_def obj_at_def is_etcb_at_def)
  apply (rule conjI)
   apply (force simp: pas_refined_def tcb_domain_map_wellformed_aux_def
                intro: domtcbs)
  apply force
  done


lemma schedule_choose_new_thread_integrity:
  "\<lbrace> invs and valid_sched and valid_list and integrity aag X st and pas_refined aag
     and K (pasMayEditReadyQueues aag)
     and (\<lambda>s. scheduler_action s = choose_new_thread) \<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by (wpsimp wp: choose_thread_respects_pasMayEditReadyQueues
                 next_domain_valid_sched next_domain_valid_queues
           simp: schedule_choose_new_thread_def valid_sched_def)

lemma schedule_integrity:
  "\<lbrace>einvs and integrity aag X st and pas_refined aag and pas_cur_domain aag
          and (\<lambda>s. domain_time s \<noteq> 0) \<rbrace>
      schedule
    \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: schedule_def)
  apply (rule hoare_pre)
  supply ethread_get_wp[wp del]
  apply (wp|wpc|simp only: schedule_choose_new_thread_def)+
  apply (wpsimp wp: alternative_wp switch_to_thread_respects' select_wp switch_to_idle_thread_respects
                 guarded_switch_to_lift choose_thread_respects gts_wp hoare_drop_imps
                 set_scheduler_action_cnt_valid_sched append_thread_queued enqueue_thread_queued
                 tcb_sched_action_enqueue_valid_blocked_except
                 tcb_sched_action_append_integrity'
            wp_del: ethread_get_wp
    | wpc
    | simp add: allActiveTCBs_def schedule_choose_new_thread_def
    | rule hoare_pre_cont[where a=next_domain])+
  apply (auto simp: obj_at_def st_tcb_at_def not_cur_thread_2_def valid_sched_def
              valid_sched_action_def weak_valid_sched_action_def
              valid_sched_action_switch_subject_thread schedule_choose_new_thread_def)
  done

lemma  valid_sched_valid_sched_action:
  "valid_sched s \<Longrightarrow> valid_sched_action s"
  by (simp add: valid_sched_def)

lemma schedule_integrity_pasMayEditReadyQueues:
  "\<lbrace>einvs and integrity aag X st and pas_refined aag and guarded_pas_domain aag
          and K (pasMayEditReadyQueues aag) \<rbrace>
     schedule
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  supply ethread_get_wp[wp del]
  supply schedule_choose_new_thread_integrity[wp]
  supply if_split[split del]
  apply (simp add: schedule_def wrap_is_highest_prio_def[symmetric])
  apply (wp, wpc)
        (* resume current thread *)
        apply wp
       prefer 2
       (* choose thread *)
       apply wp
      (* switch_to *)
      apply (wpsimp wp: set_scheduler_action_cnt_valid_sched enqueue_thread_queued append_thread_queued
                        tcb_sched_action_append_integrity_pasMayEditReadyQueues
                        guarded_switch_to_lift switch_to_thread_respects_pasMayEditReadyQueues)+
            (* is_highest_prio *)
            apply (simp add: wrap_is_highest_prio_def)
            apply ((wp (once) hoare_drop_imp)+)[1]
           apply (wpsimp wp: tcb_sched_action_enqueue_valid_blocked_except hoare_vcg_imp_lift' gts_wp)+
  apply (clarsimp simp: if_apply_def2 cong: imp_cong conj_cong)

  apply (safe ; ((solves \<open>clarsimp simp: valid_sched_def not_cur_thread_def valid_sched_action_def
                                         weak_valid_sched_action_def\<close>
                )?))
   apply (clarsimp simp: obj_at_def pred_tcb_at_def)+
  done

lemma pas_refined_cur_thread [iff]:
  "pas_refined aag (s\<lparr>cur_thread := v\<rparr>) = pas_refined aag s"
  unfolding pas_refined_def
  by (simp add:  state_objs_to_policy_def)

lemma switch_to_thread_pas_refined:
  "\<lbrace>pas_refined aag\<rbrace>
    switch_to_thread t
  \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  unfolding switch_to_thread_def arch_switch_to_thread_def
  by (wp do_machine_op_pas_refined | simp)+

lemma switch_to_idle_thread_pas_refined:
  "\<lbrace>pas_refined aag\<rbrace>
    switch_to_idle_thread
  \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  unfolding switch_to_idle_thread_def arch_switch_to_idle_thread_def
  by (wp do_machine_op_pas_refined | simp)+

crunch pas_refined[wp]: choose_thread "pas_refined aag" (wp: switch_to_thread_pas_refined switch_to_idle_thread_pas_refined crunch_wps)

lemma schedule_pas_refined:
  "\<lbrace>pas_refined aag\<rbrace>
  schedule
  \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: schedule_def allActiveTCBs_def)
  apply (wp add: alternative_wp guarded_switch_to_lift switch_to_thread_pas_refined select_wp
                  switch_to_idle_thread_pas_refined gts_wp
                  guarded_switch_to_lift switch_to_thread_respects_pasMayEditReadyQueues
                  choose_thread_respects_pasMayEditReadyQueues
                  next_domain_valid_sched next_domain_valid_queues gts_wp hoare_drop_imps
                  set_scheduler_action_cnt_valid_sched enqueue_thread_queued
                  tcb_sched_action_enqueue_valid_blocked_except
             del: ethread_get_wp
         | wpc | simp add: schedule_choose_new_thread_def)+
  done

lemma handle_interrupt_arch_state [wp]:
  "\<lbrace>\<lambda>s :: det_ext state. P (arch_state s)\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  unfolding handle_interrupt_def
  apply (rule hoare_if)
  apply (rule hoare_pre)
  apply clarsimp
  apply (wp get_cap_inv dxo_wp_weak send_signal_arch_state
        | wpc
        | simp add: get_irq_state_def handle_reserved_irq_def)+
  done

lemmas sequence_x_mapM_x = mapM_x_def [symmetric]

crunch arch_state [wp]: invoke_untyped "\<lambda>s. P (arch_state s)"
   (wp: crunch_wps without_preemption_wp syscall_valid do_machine_op_arch hoare_unless_wp
        preemption_point_inv mapME_x_inv_wp
     simp: crunch_simps sequence_x_mapM_x
     ignore: do_machine_op freeMemory clearMemory)

end

crunch_ignore (add:
  cap_swap_ext cap_move_ext cap_insert_ext empty_slot_ext create_cap_ext tcb_sched_action ethread_set
  reschedule_required set_thread_state_ext possible_switch_to next_domain
  set_domain
  timer_tick set_priority retype_region_ext)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma zet_zip_contrapos:
  "fst t \<notin> set xs  \<Longrightarrow> t \<notin> set (zip xs ys)"
  apply (rule ccontr)
  apply (simp add: set_zip_helper)
  done

lemma ct_active_update[simp]:
  "ct_active (s\<lparr>cdt := b\<rparr>) = ct_active s"
  "ct_active (s\<lparr>is_original_cap := ic\<rparr>) = ct_active s"
  "ct_active (s\<lparr>interrupt_states := st\<rparr>) = ct_active s"
  "ct_active (s\<lparr>arch_state := as\<rparr>) = ct_active s"
  by (auto simp: st_tcb_at_def ct_in_state_def)

lemma set_cap_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    set_cap ptr c
   \<lbrace>\<lambda>_. ct_active \<rbrace>"
  apply (rule hoare_pre)
  apply (wp select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state
          | simp add: crunch_simps ct_in_state_def | wps)+
  done

lemma do_extended_op_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    do_extended_op ch
   \<lbrace>\<lambda>_. ct_active \<rbrace>"
  apply (rule hoare_pre)
  apply (wp | simp add: crunch_simps ct_in_state_def do_extended_op_def | wps)+
  apply (auto simp: st_tcb_at_def obj_at_def)
  done

crunch ct_active [wp]: set_original "ct_active"
  ( wp: crunch_wps
    simp: crunch_simps ct_in_state_def)

crunch ct_active [wp]: set_cdt "ct_active"
  ( wp: crunch_wps
    simp: crunch_simps ct_in_state_def)

lemma cap_swap_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    cap_swap a b c d
   \<lbrace>\<lambda>_. ct_active \<rbrace>"
  by (wp | simp add: cap_swap_def | wps)+

lemma unbind_maybe_notification_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    unbind_maybe_notification ptr
   \<lbrace>\<lambda>_. ct_active \<rbrace>"
  apply (rule hoare_pre)
  apply (wp | wps | simp add: unbind_maybe_notification_def ct_in_state_def | wpc)+
  done

lemma unbind_notification_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    unbind_notification ptr
   \<lbrace>\<lambda>_. ct_active \<rbrace>"
  apply (rule hoare_pre)
  apply (wp | wps | simp add: unbind_notification_def ct_in_state_def | wpc)+
  done

lemma sts_Restart_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> set_thread_state xa Restart \<lbrace>\<lambda>xb. ct_active\<rbrace>"
  apply (wp set_object_wp | simp add: set_thread_state_def)+
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
  done

lemma cancel_all_ipc_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
    cancel_all_ipc ptr
   \<lbrace>\<lambda>_. ct_active \<rbrace>"
  apply (wp mapM_x_wp set_simple_ko_ct_active | wps | simp add: cancel_all_ipc_def | wpc)+
       apply force
      apply (wp mapM_x_wp set_simple_ko_ct_active)+
      apply force
     apply (wp set_simple_ko_ct_active hoare_drop_imps hoare_vcg_conj_lift hoare_vcg_all_lift)+
  apply simp
  done

crunch ct_active [wp]: cap_swap_for_delete "ct_active"
  ( wp: crunch_wps filterM_preserved hoare_unless_wp
    simp: crunch_simps ignore: do_extended_op)

crunch ct_active [wp]: post_cap_deletion, empty_slot "ct_active"
  ( wp: crunch_wps filterM_preserved hoare_unless_wp
    simp: crunch_simps ignore: do_extended_op)

crunch cur_thread[wp]: cap_swap_for_delete,finalise_cap "\<lambda>s. P (cur_thread s)" (wp: select_wp dxo_wp_weak crunch_wps simp: crunch_simps )

lemma irq_state_indepenedent_cur_thread[simp]: "irq_state_independent_A (\<lambda>s. P (cur_thread s))"
  by (simp add: irq_state_independent_def)

lemma rec_del_cur_thread[wp]:"\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> rec_del a \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  apply (rule rec_del_preservation)
  apply (wp preemption_point_inv|simp)+
  done

crunch cur_thread[wp]: cap_delete,cap_move "\<lambda>s. P (cur_thread s)" (wp: cap_revoke_preservation2 mapM_wp mapM_x_wp crunch_wps dxo_wp_weak simp: filterM_mapM unless_def ignore: without_preemption filterM)

lemma cap_revoke_cur_thread[wp]: "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> cap_revoke a \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  apply (rule cap_revoke_preservation2)
  apply (wp preemption_point_inv|simp)+
  done

crunch cur_thread[wp]: cancel_badged_sends "\<lambda>s. P (cur_thread s)" (wp: crunch_wps mapM_wp mapM_x_wp dxo_wp_weak simp: filterM_mapM unless_def ignore: without_preemption filterM)

lemma invoke_cnode_cur_thread[wp]: "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> invoke_cnode a \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
  apply (wp hoare_drop_imps hoare_vcg_all_lift | wpc | simp split del: if_split)+
  done

crunch cur_thread[wp]: handle_event "\<lambda>s. P (cur_thread s)"
  (wp: syscall_valid crunch_wps check_cap_inv dxo_wp_weak
   simp: crunch_simps filterM_mapM
   ignore: syscall)

crunches ethread_set, timer_tick, possible_switch_to, handle_interrupt
  for pas_cur_domain[wp]: "pas_cur_domain pas"
  (wp: crunch_wps simp: crunch_simps ignore_del: ethread_set timer_tick possible_switch_to)

lemma dxo_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s) \<rbrace> do_extended_op f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (clarsimp simp: valid_def dest!: in_dxo_idle_threadD)

crunch idle_thread[wp]: throwError "\<lambda>s. P (idle_thread s)"

lemma preemption_point_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s) \<rbrace> preemption_point \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  apply (clarsimp simp: preemption_point_def)
  by (wpsimp wp: OR_choiceE_weak_wp simp: irq_state_independent_def)

(* following idle_thread and cur_domain proofs clagged from infoflow/PasUpdates.thy *)
crunch idle_thread'[wp]: cap_delete "\<lambda>s. P (idle_thread s)"

lemma cap_revoke_idle_thread[wp]:"\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> cap_revoke a \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  by (rule cap_revoke_preservation2; wp)

lemma invoke_cnode_idle_thread[wp]: "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> invoke_cnode a \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
    apply (wp hoare_drop_imps hoare_vcg_all_lift | wpc | simp split del: if_split)+
  done

crunch idle_thread[wp]: handle_event "\<lambda>s::det_state. P (idle_thread s)"
  (wp: syscall_valid crunch_wps
   simp: crunch_simps check_cap_at_def
   ignore: check_cap_at syscall)

crunch cur_domain[wp]:
  transfer_caps_loop, ethread_set, possible_switch_to, thread_set_priority, set_priority,
  set_domain, invoke_domain, cap_move_ext, timer_tick,
  cap_move, cancel_badged_sends, possible_switch_to
  "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps simp: crunch_simps filterM_mapM rule: transfer_caps_loop_pres
   ignore_del: ethread_set set_priority set_domain cap_move_ext timer_tick possible_switch_to)

lemma invoke_cnode_cur_domain[wp]: "\<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> invoke_cnode a \<lbrace>\<lambda>r s. P (cur_domain s)\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps hoare_vcg_all_lift | wpc | simp split del: if_split)+
  done

crunch cur_domain[wp]: handle_event "\<lambda>s. P (cur_domain s)"
  (wp: syscall_valid crunch_wps check_cap_inv
   simp: crunch_simps
   ignore: check_cap_at syscall)

lemma handle_event_guarded_pas_domain[wp]:
  "\<lbrace>guarded_pas_domain aag\<rbrace> handle_event e \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  by (wp guarded_pas_domain_lift)

lemma handle_interrupt_guarded_pas_domain[wp]:
  "\<lbrace>guarded_pas_domain aag\<rbrace> handle_interrupt blah \<lbrace>\<lambda>_. guarded_pas_domain aag\<rbrace>"
  by (wp guarded_pas_domain_lift)

lemma call_kernel_integrity':
  "st \<turnstile> \<lbrace>einvs and pas_refined aag and is_subject aag \<circ> cur_thread and schact_is_rct and guarded_pas_domain aag
                    and domain_sep_inv (pasMaySendIrqs aag) st'
                    and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and (ct_active or ct_idle)
                    and K (pasMayActivate aag \<and> pasMayEditReadyQueues aag)\<rbrace>
               call_kernel ev
             \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: call_kernel_def getActiveIRQ_def )
  apply (simp only: spec_valid_def)
  apply (wp activate_thread_respects schedule_integrity_pasMayEditReadyQueues
            handle_interrupt_integrity
            dmo_wp alternative_wp select_wp handle_interrupt_pas_refined
         | simp )+
   apply (rule hoare_post_impErr,
          rule_tac Q = "integrity aag X st and pas_refined aag and einvs and guarded_pas_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'
                        and is_subject aag \<circ> cur_thread
                        and (\<lambda>_. pasMayActivate aag \<and> pasMayEditReadyQueues aag)" in valid_validE)
     apply (wp handle_event_integrity he_invs handle_event_pas_refined
              handle_event_cur_thread handle_event_cur_domain
              handle_event_domain_sep_inv handle_event_valid_sched | simp)+
    apply(fastforce simp: domain_sep_inv_def guarded_pas_domain_def)+
  done

lemma call_kernel_integrity:
  "\<lbrace>pas_refined pas and einvs
    and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and (ct_active or ct_idle)
    and domain_sep_inv (pasMaySendIrqs pas) st'
    and schact_is_rct and guarded_pas_domain pas
    and is_subject pas o cur_thread and K (pasMayActivate pas \<and> pasMayEditReadyQueues pas) and (\<lambda>s. s = st)\<rbrace>
   call_kernel ev
   \<lbrace>\<lambda>_. integrity pas X st\<rbrace>"
  using call_kernel_integrity' [of st pas st' ev X]
  apply (simp add: spec_valid_def)
  apply (erule hoare_chain)
   apply clarsimp
  apply assumption
  done

lemma call_kernel_pas_refined:
  "\<lbrace>einvs and pas_refined aag and is_subject aag \<circ> cur_thread and guarded_pas_domain aag
    and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and (ct_active or ct_idle)
    and schact_is_rct and pas_cur_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'\<rbrace>
  call_kernel ev
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: call_kernel_def getActiveIRQ_def)
  apply (wp activate_thread_pas_refined schedule_pas_refined handle_interrupt_pas_refined
            do_machine_op_pas_refined dmo_wp alternative_wp select_wp)
   apply simp
   apply (rule hoare_post_impErr [OF valid_validE [where Q = "pas_refined aag and invs"]])
     apply (wp he_invs handle_event_pas_refined)
    apply auto
  done

end

end
