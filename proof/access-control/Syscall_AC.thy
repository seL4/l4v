(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Syscall_AC
imports
  ArchIpc_AC
  ArchTcb_AC
  ArchInterrupt_AC
  ArchDomainSepInv
begin

definition authorised_invocation ::
  "'a PAS \<Rightarrow> invocation \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool" where
  "authorised_invocation aag i \<equiv> \<lambda>s. case i of
     InvokeUntyped i' \<Rightarrow> valid_untyped_inv i' s \<and> (authorised_untyped_inv aag i') \<and> ct_active s
   | InvokeEndpoint epptr badge can_grant can_grant_reply \<Rightarrow>
       \<exists>ep. ko_at (Endpoint ep) epptr s \<and>
            (can_grant \<longrightarrow>  (\<forall>r \<in> ep_q_refs_of ep. snd r = EPRecv \<longrightarrow> is_subject aag (fst r)) \<and>
                            aag_has_auth_to aag Grant epptr \<and> aag_has_auth_to aag Call epptr) \<and>
            (can_grant_reply \<longrightarrow> aag_has_auth_to aag Call epptr) \<and>
            aag_has_auth_to aag SyncSend epptr
   | InvokeNotification ep badge \<Rightarrow> aag_has_auth_to aag Notify ep
   | InvokeReply thread slot grant \<Rightarrow>
       (grant \<longrightarrow> is_subject aag thread) \<and> is_subject aag (fst slot)
                                         \<and> aag_has_auth_to aag Reply thread
   | InvokeTCB i' \<Rightarrow> tcb_inv_wf i' s \<and> authorised_tcb_inv aag i'
   | InvokeDomain thread slot \<Rightarrow> False
   | InvokeCNode i' \<Rightarrow> authorised_cnode_inv aag i' s \<and> is_subject aag (cur_thread s)
                                                     \<and> cnode_inv_auth_derivations i' s
   | InvokeIRQControl i' \<Rightarrow> authorised_irq_ctl_inv aag i'
   | InvokeIRQHandler i' \<Rightarrow> authorised_irq_hdl_inv aag i'
   | InvokeArchObject i' \<Rightarrow> valid_arch_inv i' s \<and> authorised_arch_inv aag i' s \<and> ct_active s"

lemma perform_invocation_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and einvs and simple_sched_action
                    and valid_invocation oper and is_subject aag \<circ> cur_thread
                    and authorised_invocation aag oper\<rbrace>
   perform_invocation blocking calling oper
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (cases oper, simp_all)
           apply (simp add: authorised_invocation_def validE_R_def[symmetric] invs_valid_objs
                  | wp invoke_untyped_pas_refined send_ipc_pas_refined send_signal_pas_refined
                       do_reply_transfer_pas_refined invoke_tcb_pas_refined invoke_cnode_pas_refined
                       invoke_irq_control_pas_refined invoke_irq_handler_pas_refined
                       invoke_arch_pas_refined decode_cnode_invocation_auth_derived
                  | fastforce)+
  done

lemma ntfn_gives_obj_at:
  "invs s
   \<Longrightarrow> (\<exists>ntfn. ko_at (Notification ntfn) ntfnptr s
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
  "\<lbrace>pas_refined aag and integrity aag X st and einvs and simple_sched_action
                    and valid_invocation oper and authorised_invocation aag oper
                    and is_subject aag \<circ> cur_thread
                    and (\<lambda>s. \<forall>p ko. kheap s p = Some ko
                                    \<longrightarrow> \<not> (is_tcb ko \<and> p = cur_thread st)  \<longrightarrow> kheap st p = Some ko)\<rbrace>
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

(* FIXME AC: the RISCV variant of arch_decode_inv_wf assumes "real_cte_at slot" whereas the
             ARM variant does not. Just going to assume "real_cte_at slot" here for now, but
             we might want to avoid requalifying this lemma. *)
lemma decode_invocation_authorised:
  "\<lbrace>pas_refined aag and valid_cap cap and invs and ct_active and (is_subject aag \<circ> cur_thread) and
    cte_wp_at ((=) cap) slot and ex_cte_cap_to slot and domain_sep_inv (pasMaySendIrqs aag) st' and
    real_cte_at slot and
    (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s) and
    (\<lambda>s. \<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_to r s) and
    (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s) and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x)) and
    (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s) and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. real_cte_at (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to is_cnode_cap (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at (interrupt_derived (fst x)) (snd x) s) and
    K (is_subject aag (fst slot) \<and> pas_cap_cur_auth aag cap \<and>
       (\<forall>slot \<in> set excaps. is_subject aag (fst (snd slot))) \<and>
       (\<forall>slot \<in> set excaps. pas_cap_cur_auth aag (fst slot)))\<rbrace>
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
          sorry (* XXX: broken by touched_addresses. -robs
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
*)

lemma in_extended: "(u,a) \<in> fst (do_extended_op f s) \<Longrightarrow> \<exists>e. a = (trans_state (\<lambda>_. e) s)"
  by (fastforce simp: do_extended_op_def bind_def gets_def return_def get_def
                      mk_ef_def modify_def select_f_def put_def trans_state_update')

lemma set_scheduler_action_authorised_arch_inv[wp]:
  "set_scheduler_action act \<lbrace>authorised_arch_inv aag i\<rbrace>"
  unfolding set_scheduler_action_def
  by wpsimp

lemma set_thread_state_authorised[wp]:
  "\<lbrace>authorised_invocation aag i and (\<lambda>s. thread = cur_thread s) and valid_objs\<rbrace>
   set_thread_state thread Restart
   \<lbrace>\<lambda>_. authorised_invocation aag i\<rbrace>"
  apply (cases i; simp add: authorised_invocation_def)
          apply (wpsimp wp: sts_valid_untyped_inv ct_in_state_set
                            hoare_vcg_ex_lift sts_obj_at_impossible)+
     apply (rename_tac cnode_invocation)
     apply (case_tac cnode_invocation;
            simp add: cnode_inv_auth_derivations_def authorised_cnode_inv_def)[1]
           apply (wp set_thread_state_cte_wp_at | simp)+
  apply (rename_tac arch_invocation)
  apply (wpsimp wp: sts_valid_arch_inv ct_in_state_set)
  done

lemma sts_first_restart:
  "\<lbrace>(=) st and (\<lambda>s. thread = cur_thread s)\<rbrace>
   set_thread_state thread Structures_A.thread_state.Restart
   \<lbrace>\<lambda>rv s. \<forall>p ko. kheap s p = Some ko \<longrightarrow>
           (is_tcb ko \<longrightarrow> p \<noteq> cur_thread st) \<longrightarrow> kheap st p = Some ko\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp wp: set_object_wp dxo_wp_weak touch_object_wp' simp: is_tcb)

lemma lcs_reply_owns:
  "\<lbrace>pas_refined aag and K (is_subject aag thread)\<rbrace>
   lookup_cap_and_slot thread ptr
   \<lbrace>\<lambda>rv _. \<forall>ep. (\<exists>m R. fst rv = ReplyCap ep m R \<and> AllowGrant \<in> R) \<longrightarrow> is_subject aag ep\<rbrace>, -"
  apply (rule hoare_post_imp_R)
   apply (rule hoare_pre)
    apply (rule hoare_vcg_conj_lift_R [where S = "K (pas_refined aag)"])
     apply (rule lookup_cap_and_slot_cur_auth)
    sorry (* XXX: broken by touched_addresses. -robs
    apply (simp | wp lookup_cap_and_slot_inv)+
  apply (force simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
               dest: aag_Control_into_owns)
  done
*)

crunch pas_refined[wp]: reply_from_kernel "pas_refined aag"
  (simp: split_def)

lemma lookup_cap_and_slot_valid_fault3:
  "\<lbrace>valid_objs\<rbrace>
   lookup_cap_and_slot thread cptr
   -, \<lbrace>\<lambda>ft _. valid_fault (CapFault (of_bl cptr) rp ft)\<rbrace>"
  apply (unfold validE_E_def)
  apply (rule hoare_post_impErr)
    apply (rule lookup_cap_and_slot_valid_fault)
   apply auto
  done

definition guarded_pas_domain where
  "guarded_pas_domain aag \<equiv>
   \<lambda>s. cur_thread s \<noteq> idle_thread s
       \<longrightarrow> pasObjectAbs aag (cur_thread s) \<in> pasDomainAbs aag (cur_domain s)"

locale gpd_wps' =
  fixes f :: "(det_ext state, 'z) nondet_monad"
  assumes idle_thread[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>"
  and cur_thread[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"

locale gpd_wps = gpd_wps' +
  assumes cur_domain[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"

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
  "\<lbrakk> invs s; ct_in_state x s; \<not> x IdleThreadState;
     guarded_pas_domain aag s; is_subject aag (cur_thread s) \<rbrakk>
     \<Longrightarrow> pas_cur_domain aag s"
  by (auto simp: invs_def valid_state_def valid_idle_def pred_tcb_at_def
                 obj_at_def ct_in_state_def guarded_pas_domain_def)

lemma sts_ct_in_state:
  "\<lbrace>\<lambda>s. t = cur_thread s \<and> P ts\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. ct_in_state P\<rbrace>"
  unfolding ct_in_state_def
  apply (rule hoare_pre)
   apply wps
   apply (wpsimp wp: sts_st_tcb_at'')
  apply clarsimp
  done

lemma handle_invocation_pas_refined:
  "\<lbrace>pas_refined aag and guarded_pas_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'
                    and einvs and ct_active and schact_is_rct and is_subject aag \<circ> cur_thread\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: handle_invocation_def split_def)
  apply (cases blocking, simp)
  (* slow ~30s *)
  sorry (* XXX: broken by touched_addresses. -robs
  by ((wp syscall_valid without_preemption_wp handle_fault_pas_refined
             set_thread_state_pas_refined set_thread_state_runnable_valid_sched
             perform_invocation_pas_refined hoare_vcg_conj_lift hoare_vcg_all_lift
             rfk_invs sts_st_tcb_at'' sts_ct_in_state
       | strengthen invs_psp_aligned invs_vspace_objs invs_arch_state
       | wpc
       | rule hoare_drop_imps
       | simp add: if_apply_def2 conj_comms split del: if_split
              del: hoare_True_E_R)+,
      (wp lookup_extra_caps_auth lookup_extra_caps_authorised decode_invocation_authorised
          lookup_cap_and_slot_authorised lookup_cap_and_slot_cur_auth as_user_pas_refined
          lookup_cap_and_slot_valid_fault3 hoare_vcg_const_imp_lift_R
       | simp add: comp_def runnable_eq_active split del: if_split)+,
       fastforce intro: guarded_to_cur_domain if_live_then_nonz_capD
                  simp: ct_in_state_def st_tcb_at_def live_def)+
*)


lemma handle_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and guarded_pas_domain aag
                       and domain_sep_inv (pasMaySendIrqs aag) st'
                       and einvs and ct_active and schact_is_rct
                       and is_subject aag \<circ> cur_thread and ((=) st)\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: handle_invocation_def split_def)
  apply (wp syscall_valid without_preemption_wp handle_fault_integrity_autarch
            touch_object_wp'
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
                   set_thread_state_ct_st hoare_vcg_const_imp_lift_R
                   lookup_cap_and_slot_valid_fault3
                | (rule valid_validE, strengthen invs_vobjs_strgs))+
  sorry (* XXX: broken by touched_addresses. -robs
  by (fastforce intro: st_tcb_ex_cap' guarded_to_cur_domain
                 simp: ct_in_state_def runnable_eq_active)
*)

crunch pas_refined[wp]: delete_caller_cap "pas_refined aag"

lemma handle_recv_pas_refined:
  "\<lbrace>pas_refined aag and invs and is_subject aag \<circ> cur_thread\<rbrace>
     handle_recv is_blocking
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: handle_recv_def Let_def lookup_cap_def split_def)
  apply (wp handle_fault_pas_refined receive_ipc_pas_refined receive_signal_pas_refined
            get_cap_auth_wp [where aag=aag] lookup_slot_for_cnode_op_authorised
            lookup_slot_for_thread_authorised lookup_slot_for_thread_cap_fault
            hoare_vcg_all_lift_R get_simple_ko_wp
         | wpc | simp
         | (rule_tac Q="\<lambda>rv s. invs s \<and> is_subject aag thread \<and> aag_has_auth_to aag Receive thread"
                  in hoare_strengthen_post,
            wp, clarsimp simp: invs_valid_objs invs_sym_refs))+
     sorry (* XXX: broken by touched_addresses. -robs
     apply (rule_tac Q'="\<lambda>rv s. pas_refined aag s \<and> invs s \<and> tcb_at thread s
                              \<and> cur_thread s = thread \<and> is_subject aag (cur_thread s)
                              \<and> is_subject aag thread" in hoare_post_imp_R [rotated])
      apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def
                             cap_rights_to_auth_def valid_fault_def)
     apply (wp user_getreg_inv | strengthen invs_vobjs_strgs | simp)+
  apply clarsimp
  done
*)

crunch respects[wp]: delete_caller_cap "integrity aag X st"

lemma handle_recv_integrity:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and is_subject aag \<circ> cur_thread
                       and K (valid_mdb st \<and> valid_objs st)\<rbrace>
   handle_recv is_blocking
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: handle_recv_def Let_def lookup_cap_def split_def)
  sorry (* XXX: broken by touched_addresses. -robs
  apply (wp handle_fault_integrity_autarch receive_ipc_integrity_autarch
            receive_signal_integrity_autarch lookup_slot_for_thread_authorised
            lookup_slot_for_thread_cap_fault get_cap_auth_wp [where aag=aag] get_simple_ko_wp
         | wpc
         | simp
         | rule_tac Q="\<lambda>rv s. invs s \<and> is_subject aag thread \<and> aag_has_auth_to aag Receive thread"
                 in hoare_strengthen_post, wp, clarsimp simp: invs_valid_objs invs_sym_refs)+
     apply (rule_tac Q'="\<lambda>rv s. pas_refined aag s \<and> einvs s \<and> is_subject aag (cur_thread s)
                              \<and> tcb_at thread s \<and> cur_thread s = thread \<and> is_subject aag thread
                              \<and> integrity aag X st s" in hoare_post_imp_R [rotated])
      apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def
                             cap_rights_to_auth_def valid_fault_def)
     apply wpsimp+
  apply fastforce
  done
*)

lemma handle_reply_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and is_subject aag \<circ> cur_thread\<rbrace>
   handle_reply
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding handle_reply_def
  apply (rule hoare_pre)
   apply (wp do_reply_transfer_pas_refined touch_object_wp' get_cap_auth_wp [where aag = aag] | wpc)+
  by (force simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
           intro: aag_Control_into_owns)

lemma handle_reply_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and is_subject aag \<circ> cur_thread\<rbrace>
   handle_reply
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding handle_reply_def
  apply (rule hoare_pre)
  apply (wp do_reply_transfer_respects touch_object_wp' get_cap_auth_wp [where aag = aag]| wpc)+
  apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                         cur_tcb_def cte_wp_at_caps_of_state is_reply_cap_to_def
                  intro: aag_Control_into_owns
                   dest: invs_cur)
  done

lemma ethread_set_time_slice_pas_refined[wp]:
  "ethread_set (tcb_time_slice_update f) thread \<lbrace>pas_refined aag\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(a, b)" in ballE)
   apply force
  apply (erule notE)
  apply (erule domains_of_state_aux.cases, simp add: get_etcb_def split: if_split_asm)
   apply (force intro: domtcbs)+
  done

lemma thread_set_time_slice_pas_refined[wp]:
  "thread_set_time_slice tptr time \<lbrace>pas_refined aag\<rbrace>"
  by (simp add: thread_set_time_slice_def | wp)+

lemma dec_domain_time_pas_refined[wp]:
  "dec_domain_time \<lbrace>pas_refined aag\<rbrace>"
  apply (simp add: dec_domain_time_def | wp)+
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  done

crunch pas_refined[wp]: timer_tick "pas_refined aag"
  (wp_del: timer_tick_extended.pas_refined_tcb_domain_map_wellformed wp: touch_object_wp')


locale Syscall_AC_wps =
  fixes f :: "(det_ext state, 'z) nondet_monad"
  and aag :: "'a PAS"
  assumes respects[wp]: "f \<lbrace>integrity aag X st\<rbrace>"
  and pas_refined[wp]: "f \<lbrace>pas_refined aag\<rbrace>"


locale Syscall_AC_1 =
  fixes aag :: "'a PAS"
  assumes invs_irq_state_update[simp]:
    "invs ((s :: det_ext state)\<lparr>machine_state := irq_state_update f s'\<rparr>) =
     invs (s\<lparr>machine_state := s'\<rparr>)"
  and prepare_thread_delete_Syscall_AC_wps''[simp]:
    "gpd_wps' (prepare_thread_delete p)"
  and arch_finalise_cap_Syscall_AC_wps''[simp]:
    "gpd_wps' (arch_finalise_cap acap final)"
  and cap_move_Syscall_AC_wps''[simp]:
    "gpd_wps' (cap_move new_cap src_slot dest_slot)"
  and cancel_badged_sends_Syscall_AC_wps''[simp]:
    "gpd_wps' (cancel_badged_sends epptr badge)"
  and arch_post_modify_registers_Syscall_AC_wps[simp]:
    "gpd_wps (arch_post_modify_registers cur t)"
  and arch_perform_invocation_Syscall_AC_wps[simp]:
    "gpd_wps (arch_perform_invocation ai)"
  and arch_invoke_irq_control_Syscall_AC_wps[simp]:
    "gpd_wps (arch_invoke_irq_control ivk)"
  and arch_invoke_irq_handler_Syscall_AC_wps[simp]:
    "gpd_wps (arch_invoke_irq_handler ihi)"
  and arch_mask_irq_signal_Syscall_AC_wps[simp]:
    "gpd_wps (arch_mask_irq_signal irq)"
  and arch_mask_interrupts_Syscall_AC_wps[simp]:
    "gpd_wps (arch_mask_interrupts m irqs)"
  and arch_switch_domain_kernel_Syscall_AC_wps[simp]:
    "gpd_wps (arch_switch_domain_kernel nextdom)"
  and arch_domainswitch_flush_Syscall_AC_wps[simp]:
    "gpd_wps (arch_domainswitch_flush)"
  and handle_reserved_irq_Syscall_AC_wps[simp]:
    "gpd_wps (handle_reserved_irq irq)"
  and handle_arch_fault_reply_Syscall_AC_wps[simp]:
    "gpd_wps (handle_arch_fault_reply vmf thread x y)"
  and handle_hypervisor_fault_Syscall_AC_wps[simp]:
    "gpd_wps (handle_hypervisor_fault t hf_t)"
  and handle_vm_fault_Syscall_AC_wps[simp]:
    "gpd_wps (handle_vm_fault t vmf_t)"
  and arch_switch_to_thread_Syscall_AC_wps'[simp]:
    "Syscall_AC_wps (arch_switch_to_thread t) aag"
  and arch_switch_to_idle_thread_respects[simp]:
    "Syscall_AC_wps (arch_switch_to_idle_thread) aag"
  and arch_activate_idle_thread_respects[simp]:
    "Syscall_AC_wps (arch_activate_idle_thread t) aag"
  and arch_mask_irq_signal_integrity[simp]:
    "Syscall_AC_wps (arch_mask_irq_signal irq) aag"
  and arch_mask_interrupts_integrity[simp]:
    "Syscall_AC_wps (arch_mask_interrupts m irqs) aag"
  and arch_switch_domain_kernel_integrity[simp]:
    "Syscall_AC_wps (arch_switch_domain_kernel newdom) aag"
  and arch_domainswitch_flush_integrity[simp]:
    "Syscall_AC_wps arch_domainswitch_flush aag"
  and handle_reserved_irq_integrity[simp]:
    "Syscall_AC_wps (handle_reserved_irq irq) aag"
  and handle_hypervisor_fault_integrity[simp]:
    "Syscall_AC_wps (handle_hypervisor_fault t hf_t) aag"
  and arch_switch_to_idle_thread_pas_refined[wp]:
    "arch_switch_to_idle_thread \<lbrace>pas_refined aag\<rbrace>"
  and arch_activate_idle_thread_pas_refined[wp]:
    "arch_activate_idle_thread t \<lbrace>pas_refined aag\<rbrace>"
  and arch_mask_irq_signal_pas_refined[wp]:
    "arch_mask_irq_signal irq \<lbrace>pas_refined aag\<rbrace>"
  and arch_mask_interrupts_pas_refined[wp]:
    "arch_mask_interrupts m irqset \<lbrace>\<lambda>s :: det_ext state. pas_refined aag s\<rbrace>"
  and arch_switch_domain_kernel_pas_refined[wp]:
    "arch_switch_domain_kernel newdom \<lbrace>\<lambda>s :: det_ext state. pas_refined aag s\<rbrace>"
  and arch_domainswitch_flush_pas_refined[wp]:
    "arch_domainswitch_flush \<lbrace>\<lambda>s :: det_ext state. pas_refined aag s\<rbrace>"
  and handle_reserved_irq_pas_refined[wp]:
    "handle_reserved_irq irq \<lbrace>pas_refined aag\<rbrace>"
  and handle_hypervisor_fault_pas_refined[wp]:
    "handle_hypervisor_fault t hf_t \<lbrace>pas_refined aag\<rbrace>"
  and handle_vm_fault_integrity:
    "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
     handle_vm_fault thread vmfault_type
     \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  and handle_vm_fault_pas_refined[wp]:
    "handle_vm_fault t vmf_t \<lbrace>pas_refined aag\<rbrace>"
  and arch_mask_irq_signal_pas_cur_domain:
    "arch_mask_irq_signal irq \<lbrace>pas_cur_domain aag\<rbrace>"
  and handle_reserved_irq_pas_cur_domain:
    "handle_reserved_irq irq \<lbrace>pas_cur_domain aag\<rbrace>"
  and ackInterrupt_underlying_memory_inv[wp]:
    "\<And>P. ackInterrupt irq \<lbrace>\<lambda>s. P (underlying_memory s)\<rbrace>"
  and resetTimer_underlying_memory_inv[wp]:
    "\<And>P. resetTimer \<lbrace>\<lambda>s. P (underlying_memory s)\<rbrace>"
  and arch_post_cap_deletion_ct_active[wp]:
    "arch_post_cap_deletion acap \<lbrace>\<lambda>s :: det_ext state. ct_active s\<rbrace>"
  and arch_mask_irq_signal_arch_state[wp]:
    "\<And>P. arch_mask_irq_signal irq \<lbrace>\<lambda>s :: det_ext state. P (arch_state s)\<rbrace>"
  and handle_reserved_irq_arch_state[wp]:
    "\<And>P. handle_reserved_irq irq \<lbrace>\<lambda>s :: det_ext state. P (arch_state s)\<rbrace>"
  and init_arch_objects_arch_state[wp]:
    "\<And>P. init_arch_objects new_type ptr n sz refs \<lbrace>\<lambda>s :: det_ext state. P (arch_state s)\<rbrace>"
  and getActiveIRQ_inv:
    "\<And>P. \<forall>f s. P s \<longrightarrow> P (irq_state_update f s)
          \<Longrightarrow> \<lbrace>P\<rbrace> getActiveIRQ in_kernel \<lbrace>\<lambda>rv. P\<rbrace>"
  and getActiveIRQ_rv_None:
    "\<lbrace>\<top>\<rbrace> getActiveIRQ True \<lbrace>\<lambda>rv ms. (rv \<noteq> None \<longrightarrow> the rv \<notin> non_kernel_IRQs)\<rbrace>"
  and set_thread_state_restart_to_running_respects:
    "\<lbrace>integrity aag X st and st_tcb_at ((=) Restart) thread and K (pasMayActivate aag)\<rbrace>
     do pc \<leftarrow> as_user thread getRestartPC;
              as_user thread $ setNextPC pc;
              set_thread_state thread Structures_A.thread_state.Running
     od
     \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"


sublocale Syscall_AC_1 \<subseteq> prepare_thread_delete: gpd_wps' "prepare_thread_delete p"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_finalise_cap: gpd_wps' "arch_finalise_cap acap final"
  by simp
sublocale Syscall_AC_1 \<subseteq> cap_move: gpd_wps' "cap_move new_cap src_slot dest_slot"
  by simp
sublocale Syscall_AC_1 \<subseteq> cancel_badged_sends: gpd_wps' "cancel_badged_sends epptr badge"
  by simp

sublocale Syscall_AC_1 \<subseteq> arch_post_modify_registers: gpd_wps "arch_post_modify_registers cur t"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_perform_invocation: gpd_wps "arch_perform_invocation ai"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_invoke_irq_control: gpd_wps "arch_invoke_irq_control ivk"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_invoke_irq_handler: gpd_wps "arch_invoke_irq_handler ihi"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_mask_irq_signal: gpd_wps "arch_mask_irq_signal irq"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_mask_interrupts: gpd_wps "arch_mask_interrupts m irqs"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_switch_domain_kernel: gpd_wps "arch_switch_domain_kernel nextdom"
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_domainswitch_flush: gpd_wps "arch_domainswitch_flush"
  by simp
sublocale Syscall_AC_1 \<subseteq> handle_reserved_irq: gpd_wps "handle_reserved_irq irq"
  by simp
sublocale Syscall_AC_1 \<subseteq> handle_arch_fault_reply: gpd_wps "handle_arch_fault_reply vmf thread x y"
  by simp
sublocale Syscall_AC_1 \<subseteq> handle_hypervisor_fault: gpd_wps "handle_hypervisor_fault t hf_t"
  by simp
sublocale Syscall_AC_1 \<subseteq> handle_vm_fault: gpd_wps "handle_vm_fault t vmf_t"
  by simp

sublocale Syscall_AC_1 \<subseteq> arch_switch_to_thread: Syscall_AC_wps "arch_switch_to_thread t" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_switch_to_idle_thread: Syscall_AC_wps "arch_switch_to_idle_thread" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_activate_idle_thread: Syscall_AC_wps "arch_activate_idle_thread t" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_mask_irq_signal: Syscall_AC_wps "arch_mask_irq_signal irq" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_mask_interrupts: Syscall_AC_wps "arch_mask_interrupts m irqs" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_switch_domain_kernel: Syscall_AC_wps "arch_switch_domain_kernel nextdom" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> arch_domainswitch_flush: Syscall_AC_wps "arch_domainswitch_flush" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> handle_reserved_irq: Syscall_AC_wps "handle_reserved_irq irq" aag
  by simp
sublocale Syscall_AC_1 \<subseteq> handle_hypervisor_fault: Syscall_AC_wps "handle_hypervisor_fault t hf_t" aag
  by simp


context Syscall_AC_1 begin

lemma handle_interrupt_pas_refined:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state\<rbrace>
    handle_interrupt irq \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: handle_interrupt_def)
  apply (rule conjI; rule impI;rule hoare_pre)
  apply (wp send_signal_pas_refined get_cap_wp touch_object_wp'
         | wpc
         | simp add: get_irq_slot_def get_irq_state_def )+
  done

lemma dec_domain_time_integrity[wp]:
  "dec_domain_time \<lbrace>integrity aag X st\<rbrace>"
  apply (simp add: dec_domain_time_def | wp)+
  apply (clarsimp simp: integrity_subjects_def)
  done

lemma timer_tick_integrity[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))\<rbrace>
   timer_tick
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: timer_tick_def)
  apply (wp ethread_set_integrity_autarch gts_wp touch_object_wp'
         | wpc | simp add: thread_set_time_slice_def split del: if_split)+
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
  done

lemma handle_interrupt_integrity_autarch:
  "\<lbrace>integrity aag X st and pas_refined aag and invs
                       and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))
                       and K (is_subject_irq aag irq)\<rbrace>
   handle_interrupt irq
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: handle_interrupt_def  cong: irq_state.case_cong)
  apply (rule conjI; rule impI; rule hoare_pre)
     apply (wp (once) send_signal_respects get_cap_auth_wp [where aag = aag] dmo_mol_respects
                      ackInterrupt_device_state_inv resetTimer_device_state_inv
            | simp add: get_irq_slot_def get_irq_state_def
            | wp dmo_no_mem_respects touch_object_wp'
            | wpc)+
  apply (fastforce simp: is_cap_simps aag_cap_auth_def cap_auth_conferred_def
                         invs_sym_refs invs_valid_objs2 pas_refined_is_subject_irqD
                         cap_rights_to_auth_def)
  done

lemma hacky_ipc_Send:
  "\<lbrakk> abs_has_auth_to aag Notify (interrupt_irq_node s irq) p;
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
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: handle_interrupt_def
             cong: irq_state.case_cong bind_cong)
  apply (rule conjI; rule impI; rule hoare_pre)
     apply (wp (once) send_signal_respects get_cap_wp dmo_mol_respects dmo_no_mem_respects
                      ackInterrupt_device_state_inv resetTimer_device_state_inv
            | wp touch_object_wp'
            | wpc
            | simp add: get_irq_slot_def get_irq_state_def)+
  apply clarsimp
  apply (rule conjI, fastforce)+ \<comment> \<open>valid_objs etc.\<close>
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule_tac s = s in hacky_ipc_Send [where irq = irq])
   apply (drule (1) cap_auth_caps_of_state)
   apply (clarsimp simp: aag_cap_auth_def is_cap_simps cap_auth_conferred_def
                         cap_rights_to_auth_def split: if_split_asm)
  apply assumption+
  done

lemma handle_yield_pas_refined[wp]:
  "handle_yield \<lbrace>pas_refined aag\<rbrace>"
  by (simp add: handle_yield_def | wp)+

lemma handle_event_pas_refined:
  "\<lbrace>pas_refined aag and guarded_pas_domain aag and domain_sep_inv (pasMaySendIrqs aag) st'
                    and einvs and schact_is_rct
                    and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> is_subject aag (cur_thread s))
                    and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) \<rbrace>
   handle_event ev
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (case_tac ev; simp)
      apply (rename_tac syscall)
      apply (case_tac syscall; simp add: handle_send_def handle_call_def)
            apply ((wp handle_invocation_pas_refined handle_recv_pas_refined
                       handle_fault_pas_refined
                    | simp | clarsimp)+)
     apply (fastforce simp: valid_fault_def)
    apply (wp handle_fault_pas_refined | simp)+
    apply (fastforce simp: valid_fault_def)
   apply (wp handle_interrupt_pas_refined handle_fault_pas_refined
             hoare_vcg_conj_lift hoare_vcg_all_lift
          | wpc
          | rule hoare_drop_imps
          | strengthen invs_vobjs_strgs invs_psp_aligned invs_vspace_objs invs_arch_state
          | simp)+
  done

lemma valid_fault_Unknown[simp]:
  "valid_fault (UnknownSyscallException x)"
  by (simp add: valid_fault_def)

lemma valid_fault_User[simp]:
  "valid_fault (UserException word1 word2)"
  by (simp add: valid_fault_def)

declare hy_inv[wp del]

lemma handle_yield_integrity[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and is_subject aag \<circ> cur_thread\<rbrace>
   handle_yield
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (simp add: handle_yield_def | wp)+

lemma ct_in_state_machine_state_update[simp]:
  "ct_in_state s (st\<lparr>machine_state := x\<rparr>) = ct_in_state s st"
  by (simp add: ct_in_state_def)

lemma handle_event_integrity:
  "\<lbrace>integrity aag X st and pas_refined aag and guarded_pas_domain aag
                       and domain_sep_inv (pasMaySendIrqs aag) st'
                       and einvs and schact_is_rct
                       and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))
                       and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and ((=) st)\<rbrace>
   handle_event ev
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (cases ev; simp)
       apply (unfold handle_send_def handle_call_def)
  sorry (* FIXME: broken by touched-addrs -robs
  by (wpsimp wp: handle_recv_integrity handle_invocation_respects
                  handle_reply_respects handle_fault_integrity_autarch
                  handle_interrupt_integrity handle_vm_fault_integrity
                  handle_reply_pas_refined handle_vm_fault_valid_fault
                  handle_reply_valid_sched alternative_wp select_wp
                  hoare_vcg_conj_lift hoare_vcg_all_lift hoare_drop_imps
            simp: domain_sep_inv_def
      | rule dmo_wp hoare_vcg_E_elim
      | fastforce
      | (rule hoare_vcg_conj_lift)?, wpsimp wp: getActiveIRQ_inv)+
*)

lemma activate_thread_respects:
  "\<lbrace>integrity aag X st and K (pasMayActivate aag)\<rbrace>
   activate_thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: activate_thread_def get_thread_state_def)
  apply (wpsimp wp: set_thread_state_restart_to_running_respects thread_get_wp'
    touch_object_wp' set_thread_state_integrity_autarch as_user_integrity_autarch)
  apply (clarsimp simp: st_tcb_at_def obj_at_def integrity_subjects_def)
  sorry (* FIXME: broken by touched-addrs -robs
  done
*)

lemma activate_thread_integrity:
  "\<lbrace>integrity aag X st and valid_idle and
    (\<lambda>s. cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject aag (cur_thread s))\<rbrace>
   activate_thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: activate_thread_def )
  apply (rule hoare_pre)
  apply (wpsimp wp: gts_wp set_thread_state_integrity_autarch as_user_integrity_autarch
    touch_object_wp')+
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma activate_thread_pas_refined:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state\<rbrace>
   activate_thread
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding activate_thread_def get_thread_state_def thread_get_def
  apply (wpsimp wp: set_thread_state_pas_refined hoare_drop_imps touch_object_wp')
  done

lemma integrity_cur_thread[iff]:
  "integrity aag X st (s\<lparr>cur_thread := v\<rparr>) = integrity aag X st s"
  unfolding integrity_def by simp

lemma tcb_sched_action_dequeue_integrity_pasMayEditReadyQueues:
  "\<lbrace>integrity aag X st and pas_refined aag and K (pasMayEditReadyQueues aag)\<rbrace>
   tcb_sched_action tcb_sched_dequeue thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp: integrity_def integrity_ready_queues_def pas_refined_def
                        tcb_domain_map_wellformed_aux_def etcb_at_def get_etcb_def
                 split: option.splits)
  done

lemma switch_to_thread_respects_pasMayEditReadyQueues:
  "\<lbrace>integrity aag X st and pas_refined aag and K (pasMayEditReadyQueues aag)\<rbrace>
   switch_to_thread t
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding switch_to_thread_def
  apply (simp add: spec_valid_def)
  apply (wpsimp wp: tcb_sched_action_dequeue_integrity_pasMayEditReadyQueues touch_object_wp')
  done

lemma switch_to_thread_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and K (is_subject aag t) \<rbrace>
   switch_to_thread t
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding switch_to_thread_def
  apply (simp add: spec_valid_def)
  apply (wpsimp wp:touch_object_wp')
  done

text \<open>
Variants of scheduling lemmas without is_subject assumption.
See comment for @{thm tcb_sched_action_dequeue_integrity'}
\<close>
lemma switch_to_thread_respects':
  "\<lbrace>integrity aag X st and pas_refined aag
                       and (\<lambda>s. pasSubject aag \<in> pasDomainAbs aag (tcb_domain (the (ekheap s t))))\<rbrace>
   switch_to_thread t
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding switch_to_thread_def
  apply (simp add: spec_valid_def)
  apply (wpsimp wp: tcb_sched_action_dequeue_integrity' touch_object_wp')
  done

lemma switch_to_idle_thread_respects:
  "switch_to_idle_thread \<lbrace>integrity aag X st\<rbrace>"
  unfolding switch_to_idle_thread_def by wpsimp

lemma choose_thread_respects_pasMayEditReadyQueues:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and valid_queues
                       and K (pasMayEditReadyQueues aag)\<rbrace>
   choose_thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (simp add: choose_thread_def guarded_switch_to_def
      | wp switch_to_thread_respects_pasMayEditReadyQueues switch_to_idle_thread_respects gts_wp
           touch_object_wp')+

text \<open>integrity for @{const choose_thread} without @{const pasMayEditReadyQueues}\<close>
lemma choose_thread_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and pas_cur_domain aag and einvs and valid_queues\<rbrace>
   choose_thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: choose_thread_def guarded_switch_to_def
         | wp switch_to_thread_respects' switch_to_idle_thread_respects gts_wp touch_object_wp')+
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
  "\<lbrace>integrity aag X st and pas_refined aag and (\<lambda>s. is_subject aag x)\<rbrace>
   guarded_switch_to x
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
   by (wpsimp simp: guarded_switch_to_def choose_thread_def
                wp: switch_to_thread_respects switch_to_idle_thread_respects gts_wp touch_object_wp')

lemma next_domain_tcb_domain_map_wellformed[wp]:
  "next_domain \<lbrace>tcb_domain_map_wellformed aag\<rbrace>"
  by (wpsimp simp: next_domain_def thread_set_domain_def ethread_set_def set_eobject_def Let_def)

lemma valid_blocked_2_valid_blocked_except[simp]:
  "valid_blocked_2 queues kh sa ct \<Longrightarrow> valid_blocked_except_2 t queues kh sa ct"
  by (clarsimp simp: valid_blocked_def valid_blocked_except_def)

(* clagged from Schedule_R *)
lemma next_domain_valid_sched:
  "\<lbrace>valid_sched and (\<lambda>s. scheduler_action s = choose_new_thread)\<rbrace> next_domain \<lbrace>\<lambda>_. valid_sched\<rbrace>"
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
   "\<lbrakk> scheduler_action s = switch_thread t; valid_sched_action s;
      valid_etcbs s; pas_refined aag s; pas_cur_domain aag s \<rbrakk>
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

lemma next_domain_integrity[wp]:
  "next_domain \<lbrace>integrity aag X st\<rbrace>"
  apply (wpsimp simp: next_domain_def thread_set_domain_def ethread_set_def set_eobject_def Let_def)
  apply (clarsimp simp: get_etcb_def integrity_subjects_def lfp_def)
  done

lemma pas_refined_cur_thread[iff]:
  "pas_refined aag (s\<lparr>cur_thread := v\<rparr>) = pas_refined aag s"
  unfolding pas_refined_def
  by (simp add: state_objs_to_policy_def)

lemma switch_to_thread_pas_refined:
  "switch_to_thread t \<lbrace>pas_refined aag\<rbrace>"
  unfolding switch_to_thread_def
  by (wpsimp wp: do_machine_op_pas_refined touch_object_wp')

lemma switch_to_idle_thread_pas_refined:
  "switch_to_idle_thread \<lbrace>pas_refined aag\<rbrace>"
  unfolding switch_to_idle_thread_def
  by (wpsimp wp: do_machine_op_pas_refined)

(* FIXME: Prove these in AInvs, not here. -robs *)
lemma arch_mask_interrupts_invs[wp]:
  "arch_mask_interrupts m irqs \<lbrace>invs\<rbrace>"
  sorry (* FIXME: Made necessary by experimental-tpspec. -robs *)

lemma arch_switch_domain_kernel_invs[wp]:
  "arch_switch_domain_kernel newdom \<lbrace>invs\<rbrace>"
  sorry (* FIXME: Made necessary by experimental-tpspec. -robs *)

lemma arch_domainswitch_flush_invs[wp]:
  "arch_domainswitch_flush \<lbrace>invs\<rbrace>"
  sorry (* FIXME: Made necessary by experimental-tpspec. -robs *)

(* FIXME: Prove these in AInvs (probably ArchDetSchedSchedule_AI), not here. -robs *)
lemma arch_mask_interrupts_valid_sched[wp]:
  "arch_mask_interrupts m irqs \<lbrace>valid_sched\<rbrace>"
  sorry (* FIXME: Made necessary by experimental-tpspec. -robs *)

lemma arch_switch_domain_kernel_valid_sched[wp]:
  "arch_switch_domain_kernel newdom \<lbrace>valid_sched\<rbrace>"
  sorry (* FIXME: Made necessary by experimental-tpspec. -robs *)

lemma arch_domainswitch_flush_valid_sched[wp]:
  "arch_domainswitch_flush \<lbrace>valid_sched\<rbrace>"
  sorry (* FIXME: Made necessary by experimental-tpspec. -robs *)

lemma schedule_choose_new_thread_integrity:
  "\<lbrace>invs and valid_sched and valid_list and integrity aag X st and pas_refined aag
         and K (pasMayEditReadyQueues aag)
         and (\<lambda>s. scheduler_action s = choose_new_thread)\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding schedule_choose_new_thread_def
  sorry (* FIXME: Broken by experimental-tpspec. -robs
  by (wpsimp wp: choose_thread_respects_pasMayEditReadyQueues
                 next_domain_valid_sched next_domain_valid_queues
           simp: schedule_choose_new_thread_def valid_sched_def)
*)

lemma schedule_integrity:
  "\<lbrace>einvs and integrity aag X st and pas_refined aag and pas_cur_domain aag
          and (\<lambda>s. domain_time s \<noteq> 0) \<rbrace>
   schedule
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: schedule_def)
  sorry (* FIXME: Broken by both touched_addresses *and* experimental-tpspec. -robs
  apply (wpsimp wp: alternative_wp switch_to_thread_respects' select_wp guarded_switch_to_lift
                    switch_to_idle_thread_respects choose_thread_respects gts_wp hoare_drop_imps
                    set_scheduler_action_cnt_valid_sched append_thread_queued enqueue_thread_queued
                    tcb_sched_action_enqueue_valid_blocked_except tcb_sched_action_append_integrity'
         | simp add: allActiveTCBs_def schedule_choose_new_thread_def
         | rule hoare_pre_cont[where a=next_domain])+
  apply (auto simp: obj_at_def st_tcb_at_def not_cur_thread_2_def valid_sched_def
                    valid_sched_action_def weak_valid_sched_action_def
                    valid_sched_action_switch_subject_thread)
  done
*)

lemma  valid_sched_valid_sched_action:
  "valid_sched s \<Longrightarrow> valid_sched_action s"
  by (simp add: valid_sched_def)

lemma schedule_integrity_pasMayEditReadyQueues:
  "\<lbrace>einvs and integrity aag X st and pas_refined aag
          and guarded_pas_domain aag and K (pasMayEditReadyQueues aag)\<rbrace>
   schedule
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
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
      apply (wpsimp wp: set_scheduler_action_cnt_valid_sched enqueue_thread_queued
                        append_thread_queued tcb_sched_action_append_integrity_pasMayEditReadyQueues
                        guarded_switch_to_lift switch_to_thread_respects_pasMayEditReadyQueues)+
             sorry (* FIXME: broken by touched-addrs -robs
            (* is_highest_prio *)
            apply (simp add: wrap_is_highest_prio_def)
            apply ((wp (once) hoare_drop_imp)+)[1]
           apply (wpsimp wp: tcb_sched_action_enqueue_valid_blocked_except hoare_vcg_imp_lift' gts_wp)+
  apply (clarsimp simp: if_apply_def2 cong: imp_cong conj_cong)
  apply (safe; ((solves \<open>clarsimp simp: valid_sched_def not_cur_thread_def
                                        valid_sched_action_def weak_valid_sched_action_def\<close>)?))
   apply (clarsimp simp: obj_at_def pred_tcb_at_def)+
  done
*)

crunch pas_refined[wp]: choose_thread "pas_refined aag"
  (wp: switch_to_thread_pas_refined switch_to_idle_thread_pas_refined crunch_wps)

lemma schedule_pas_refined:
  "schedule \<lbrace>pas_refined aag\<rbrace>"
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
               sorry (* FIXME: broken by touched-addrs -robs
  done
*)

lemmas sequence_x_mapM_x = mapM_x_def [symmetric]

crunch arch_state [wp]: invoke_untyped "\<lambda>s :: det_ext state. P (arch_state s)"
  (wp: crunch_wps preemption_point_inv mapME_x_inv_wp simp: crunch_simps sequence_x_mapM_x)

crunch_ignore (add: cap_swap_ext cap_move_ext cap_insert_ext create_cap_ext set_thread_state_ext
                    empty_slot_ext retype_region_ext set_priority ethread_set tcb_sched_action
                    reschedule_required possible_switch_to next_domain set_domain timer_tick)

lemma zet_zip_contrapos:
  "fst t \<notin> set xs  \<Longrightarrow> t \<notin> set (zip xs ys)"
  by (auto simp: set_zip_helper)

lemma ct_active_update[simp]:
  "ct_active (s\<lparr>cdt := b\<rparr>) = ct_active s"
  "ct_active (s\<lparr>is_original_cap := ic\<rparr>) = ct_active s"
  "ct_active (s\<lparr>interrupt_states := st\<rparr>) = ct_active s"
  "ct_active (s\<lparr>arch_state := as\<rparr>) = ct_active s"
  by (auto simp: st_tcb_at_def ct_in_state_def)

lemma set_cap_ct_active[wp]:
  "set_cap ptr c \<lbrace>ct_active \<rbrace>"
  apply (rule hoare_pre)
  apply (wps | wpsimp wp: select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state
                    simp: crunch_simps ct_in_state_def)+
  done

lemma do_extended_op_ct_active[wp]:
  "do_extended_op ch \<lbrace>ct_active \<rbrace>"
  apply (rule hoare_pre)
  apply (wp | simp add: crunch_simps ct_in_state_def do_extended_op_def | wps)+
  apply (auto simp: st_tcb_at_def obj_at_def)
  done

crunches set_original, set_cdt
  for ct_active [wp]: "ct_active"
  (wp: crunch_wps simp: crunch_simps ct_in_state_def)

lemma ct_active_ta_agnostic: "ta_agnostic ct_active"
  unfolding ta_agnostic_def ct_in_state_def
  by force

lemma ct_active_ms_ta_independent[intro!, simp]:
  "ct_active (ms_ta_update taf s) = ct_active s"
  using ct_active_ta_agnostic
  by (simp add: ct_in_state_def)

lemma cap_swap_ct_active[wp]:
  "cap_swap a b c d \<lbrace>ct_active\<rbrace>"
  by (wp touch_objects_wp | simp add: cap_swap_def | wps)+

lemma unbind_maybe_notification_ct_active[wp]:
  "unbind_maybe_notification ptr \<lbrace>ct_active\<rbrace>"
  by (wps | wpsimp simp: unbind_maybe_notification_def ct_in_state_def)+

lemma unbind_notification_ct_active[wp]:
  "unbind_notification ptr \<lbrace>ct_active\<rbrace>"
  by (wps | wpsimp simp: unbind_notification_def ct_in_state_def)+

lemma sts_Restart_ct_active[wp]:
  "set_thread_state xa Restart \<lbrace>ct_active\<rbrace>"
  apply (wp set_object_wp touch_object_wp' | simp add: set_thread_state_def)+
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
  done

lemma cancel_all_ipc_ct_active[wp]:
  "cancel_all_ipc ptr \<lbrace>ct_active\<rbrace>"
  apply (wp mapM_x_wp set_simple_ko_ct_active | wps | simp add: cancel_all_ipc_def | wpc)+
       apply force
      apply (wp mapM_x_wp set_simple_ko_ct_active)+
      apply force
     apply (wp set_simple_ko_ct_active hoare_drop_imps hoare_vcg_conj_lift hoare_vcg_all_lift
       touch_object_wp')+
  apply simp
  done

crunch ct_active[wp]: cap_swap_for_delete "ct_active"
  (wp: crunch_wps filterM_preserved hoare_unless_wp simp: crunch_simps ignore: do_extended_op)

crunch ct_active[wp]: post_cap_deletion, empty_slot "\<lambda>s :: det_ext state. ct_active s"
  (simp: crunch_simps empty_slot_ext_def ignore: do_extended_op
     wp: crunch_wps filterM_preserved hoare_unless_wp)

crunch cur_thread[wp]: cap_swap_for_delete, finalise_cap "\<lambda>s :: det_ext state. P (cur_thread s)"
  (wp: select_wp dxo_wp_weak crunch_wps simp: crunch_simps)

lemma rec_del_cur_thread[wp]:
  "rec_del a \<lbrace>\<lambda>s :: det_ext state. P (cur_thread s)\<rbrace>"
  apply (rule rec_del_preservation)
  apply (wp preemption_point_inv|simp)+
  done

crunch cur_thread[wp]: cap_delete, cap_move "\<lambda>s :: det_ext state. P (cur_thread s)"

lemma cap_revoke_cur_thread[wp]:
  "cap_revoke a \<lbrace>\<lambda>s :: det_ext state. P (cur_thread s)\<rbrace>"
  apply (rule cap_revoke_preservation2)
  apply (wp preemption_point_inv|simp)+
  done

crunch cur_thread[wp]: cancel_badged_sends "\<lambda>s. P (cur_thread s)"
  (wp: mapM_wp dxo_wp_weak simp: filterM_mapM)

lemma invoke_cnode_cur_thread[wp]:
 "invoke_cnode a \<lbrace>\<lambda>s :: det_ext state. P (cur_thread s)\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
  apply (wp hoare_drop_imps hoare_vcg_all_lift | wpc | simp split del: if_split)+
  done

crunch cur_thread[wp]: handle_event "\<lambda>s :: det_ext state. P (cur_thread s)"
  (wp: syscall_valid crunch_wps check_cap_inv dxo_wp_weak
   simp: crunch_simps ignore: syscall)

crunches ethread_set, timer_tick, possible_switch_to, handle_interrupt
  for pas_cur_domain[wp]: "pas_cur_domain aag"
  (wp: crunch_wps simp: crunch_simps ignore_del: ethread_set timer_tick possible_switch_to)

lemma dxo_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s) \<rbrace> do_extended_op f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (clarsimp simp: valid_def dest!: in_dxo_idle_threadD)

crunch idle_thread[wp]: throwError "\<lambda>s. P (idle_thread s)"

lemma preemption_point_idle_thread[wp]:
  "preemption_point \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>"
  by (wpsimp wp: OR_choiceE_weak_wp simp: preemption_point_def)

lemma cap_revoke_idle_thread[wp]:
  "cap_revoke a \<lbrace>\<lambda>s :: det_ext state. P (idle_thread s)\<rbrace>"
  by (rule cap_revoke_preservation2; wp)

lemma invoke_cnode_idle_thread[wp]:
  "invoke_cnode a \<lbrace>\<lambda>s :: det_ext state. P (idle_thread s)\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps hoare_vcg_all_lift | wpc | simp split del: if_split)+
  done

crunch idle_thread[wp]: handle_event "\<lambda>s :: det_state. P (idle_thread s)"
  (wp: syscall_valid crunch_wps simp: check_cap_at_def ignore: check_cap_at syscall)

crunch cur_domain[wp]:
  transfer_caps_loop, ethread_set, possible_switch_to, thread_set_priority,
  set_priority, set_domain, invoke_domain, cap_move_ext, timer_tick,
  cap_move, cancel_badged_sends, possible_switch_to
  "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps simp: filterM_mapM rule: transfer_caps_loop_pres
   ignore_del: ethread_set set_priority set_domain cap_move_ext timer_tick possible_switch_to)

lemma invoke_cnode_cur_domain[wp]:
 "invoke_cnode a \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps hoare_vcg_all_lift | wpc | simp split del: if_split)+
  done

(* XXX: broken by touched_addresses. -robs
crunch cur_domain[wp]: handle_event "\<lambda>s. P (cur_domain s)"
  (wp: syscall_valid crunch_wps check_cap_inv
   simp: crunch_simps
   ignore: check_cap_at syscall)

lemma handle_event_guarded_pas_domain[wp]:
  "handle_event e \<lbrace>guarded_pas_domain aag\<rbrace>"
  by (wpsimp wp: guarded_pas_domain_lift)

lemma handle_interrupt_guarded_pas_domain[wp]:
  "handle_interrupt blah \<lbrace>guarded_pas_domain aag\<rbrace>"
  by (wpsimp wp: guarded_pas_domain_lift)
*)

lemma integrity_irq_state_independent[simp]:
  "integrity_subjects subjects aag activate X st (s\<lparr>machine_state := irq_state_update f ms\<rparr>) =
   integrity_subjects subjects aag activate X st (s\<lparr>machine_state := ms\<rparr>)"
  by (clarsimp simp: integrity_def)

lemma guarded_pas_domain_machine_state_update[simp]:
  "guarded_pas_domain aag (machine_state_update f s) = guarded_pas_domain aag s"
  by (simp add: guarded_pas_domain_def)

lemma call_kernel_integrity':
  "st \<turnstile> \<lbrace>einvs and pas_refined aag and is_subject aag \<circ> cur_thread and schact_is_rct and guarded_pas_domain aag
               and domain_sep_inv (pasMaySendIrqs aag) st'
               and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and (ct_active or ct_idle)
               and K (pasMayActivate aag \<and> pasMayEditReadyQueues aag)\<rbrace>
        call_kernel ev
        \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (simp only: spec_valid_def)
  apply (wpsimp wp: activate_thread_respects schedule_integrity_pasMayEditReadyQueues
                    handle_interrupt_integrity dmo_wp alternative_wp
                    select_wp handle_interrupt_pas_refined)
    sorry (* XXX: broken by touched_addresses. -robs
    apply (clarsimp simp: if_fun_split)
    apply (rule_tac Q="\<lambda>rv ms. (rv \<noteq> None \<longrightarrow> the rv \<notin> non_kernel_IRQs) \<and>
                                R True (domain_sep_inv (pasMaySendIrqs aag) st' s) rv ms"
                and R="\<lambda>rv ms. R (the rv \<in> non_kernel_IRQs \<longrightarrow> scheduler_act_sane s \<and> ct_not_queued s)
                                 (pasMaySendIrqs aag \<or> interrupt_states s (the rv) \<noteq> IRQSignal) rv ms"
                for R in hoare_strengthen_post[rotated], fastforce simp: domain_sep_inv_def)
    apply (wpsimp wp: getActiveIRQ_rv_None hoare_drop_imps getActiveIRQ_inv)
   apply (rule hoare_post_impErr,
      rule_tac Q="integrity aag X st and pas_refined aag and einvs and guarded_pas_domain aag
                                     and domain_sep_inv (pasMaySendIrqs aag) st'
                                     and is_subject aag \<circ> cur_thread
                                     and K (pasMayActivate aag \<and> pasMayEditReadyQueues aag)"
            in valid_validE)
     apply (wpsimp wp: handle_event_integrity he_invs handle_event_pas_refined
                       handle_event_cur_thread handle_event_cur_domain
                       handle_event_domain_sep_inv handle_event_valid_sched)+
    apply (fastforce simp: domain_sep_inv_def guarded_pas_domain_def)+
  done
*)

lemma call_kernel_integrity:
  "\<lbrace>pas_refined aag and einvs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s) and (ct_active or ct_idle)
                    and domain_sep_inv (pasMaySendIrqs aag) st' and schact_is_rct
                    and guarded_pas_domain aag and is_subject aag o cur_thread
                    and K (pasMayActivate aag \<and> pasMayEditReadyQueues aag) and (\<lambda>s. s = st)\<rbrace>
   call_kernel ev
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  using call_kernel_integrity' [of st st' ev X]
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
  apply (simp add: call_kernel_def )
  apply (wp activate_thread_pas_refined schedule_pas_refined handle_interrupt_pas_refined
            do_machine_op_pas_refined dmo_wp alternative_wp select_wp hoare_drop_imps getActiveIRQ_inv
         | simp add: if_fun_split
         | strengthen invs_psp_aligned invs_vspace_objs invs_arch_state)+
   apply (wp he_invs handle_event_pas_refined)
  apply auto
  done

end

end
