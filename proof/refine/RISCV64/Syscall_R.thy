(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Refinement for handleEvent and syscalls
*)

theory Syscall_R
imports Tcb_R Arch_R Interrupt_R SchedContextInv_R
begin

context begin interpretation Arch . (*FIXME: arch-split*)

(*
syscall has 5 sections: m_fault h_fault m_error h_error m_finalise

run m_fault (faultable code) \<rightarrow> r_fault
  failure, i.e. Inr somefault \<rightarrow> \<lambda>somefault. h_fault; done

success, i.e. Inl a
  \<rightarrow> run \<lambda>a. m_error a (errable code) \<rightarrow> r_error
       failure, i.e. Inr someerror \<rightarrow> \<lambda>someerror. h_error e; done
       success, i.e. Inl b \<rightarrow> \<lambda>b. m_finalise b

One can clearly see this is simulating some kind of monadic Maybe sequence
trying to identify all possible errors before actually performing the syscall.
*)

lemma syscall_corres:
  assumes corres:
    "corres (fr \<oplus> r_flt_rel) P P' m_flt m_flt'"
    "\<And>flt flt'. flt' = fault_map flt \<Longrightarrow>
        corres r (P_flt flt) (P'_flt flt') (h_flt flt) (h_flt' flt')"
    "\<And>rv rv'. r_flt_rel rv rv' \<Longrightarrow>
        corres (ser \<oplus> r_err_rel rv rv')
               (P_no_flt rv) (P'_no_flt rv')
               (m_err rv) (m_err' rv')"
    "\<And>rv rv' err err'. \<lbrakk>r_flt_rel rv rv'; err' = syscall_error_map err \<rbrakk>
     \<Longrightarrow> corres r (P_err rv err)
            (P'_err rv' err') (h_err err) (h_err' err')"
    "\<And>rvf rvf' rve rve'. \<lbrakk>r_flt_rel rvf rvf'; r_err_rel rvf rvf' rve rve'\<rbrakk>
     \<Longrightarrow> corres (dc \<oplus> r)
           (P_no_err rvf rve) (P'_no_err rvf' rve')
           (m_fin rve) (m_fin' rve')"

  assumes wp:
    "\<And>rv.  \<lbrace>Q_no_flt rv\<rbrace>   m_err rv   \<lbrace>P_no_err rv\<rbrace>,  \<lbrace>P_err rv\<rbrace>"
    "\<And>rv'. \<lbrace>Q'_no_flt rv'\<rbrace> m_err' rv' \<lbrace>P'_no_err rv'\<rbrace>,\<lbrace>P'_err rv'\<rbrace>"
    "\<lbrace>Q\<rbrace> m_flt \<lbrace>\<lambda>rv. P_no_flt rv and Q_no_flt rv\<rbrace>, \<lbrace>P_flt\<rbrace>"
    "\<lbrace>Q'\<rbrace> m_flt' \<lbrace>\<lambda>rv. P'_no_flt rv and Q'_no_flt rv\<rbrace>, \<lbrace>P'_flt\<rbrace>"

  shows "corres (dc \<oplus> r) (P and Q) (P' and Q')
           (Syscall_A.syscall m_flt  h_flt m_err h_err m_fin)
           (Syscall_H.syscall m_flt' h_flt' m_err' h_err' m_fin')"
  apply (simp add: Syscall_A.syscall_def Syscall_H.syscall_def liftE_bindE)
  apply (rule corres_split_bind_case_sum)
      apply (rule corres_split_bind_case_sum | rule corres | rule wp | simp add: liftE_bindE)+
  done

lemma syscall_valid':
  assumes x:
             "\<And>ft. \<lbrace>P_flt ft\<rbrace> h_flt ft \<lbrace>Q\<rbrace>"
             "\<And>err. \<lbrace>P_err err\<rbrace> h_err err \<lbrace>Q\<rbrace>"
             "\<And>rv. \<lbrace>P_no_err rv\<rbrace> m_fin rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
             "\<And>rv. \<lbrace>P_no_flt rv\<rbrace> m_err rv \<lbrace>P_no_err\<rbrace>, \<lbrace>P_err\<rbrace>"
             "\<lbrace>P\<rbrace> m_flt \<lbrace>P_no_flt\<rbrace>, \<lbrace>P_flt\<rbrace>"
  shows "\<lbrace>P\<rbrace> Syscall_H.syscall m_flt h_flt m_err h_err m_fin \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (simp add: Syscall_H.syscall_def liftE_bindE
             cong: sum.case_cong)
  apply (rule hoare_split_bind_case_sumE)
    apply (wp x)[1]
   apply (rule hoare_split_bind_case_sumE)
     apply (wp x|simp)+
  done


text \<open>Completing the relationship between abstract/haskell invocations\<close>

primrec
  inv_relation :: "Invocations_A.invocation \<Rightarrow> Invocations_H.invocation \<Rightarrow> bool"
where
  "inv_relation (Invocations_A.InvokeUntyped i) x =
     (\<exists>i'. untypinv_relation i i' \<and> x = InvokeUntyped i')"
| "inv_relation (Invocations_A.InvokeEndpoint w w2 b c) x =
     (x = InvokeEndpoint w w2 b c)"
| "inv_relation (Invocations_A.InvokeNotification w w2) x =
     (x = InvokeNotification w w2)"
| "inv_relation (Invocations_A.InvokeReply w grant) x =
     (x = InvokeReply w grant)"
| "inv_relation (Invocations_A.InvokeTCB i) x =
     (\<exists>i'. tcbinv_relation i i' \<and> x = InvokeTCB i')"
| "inv_relation (Invocations_A.InvokeDomain tptr domain) x =
     (x = InvokeDomain tptr domain)"
| "inv_relation (Invocations_A.InvokeSchedContext sc_inv) x =
     (\<exists>sc_inv'. sc_inv_rel sc_inv sc_inv' \<and> x = InvokeSchedContext sc_inv')"
| "inv_relation (Invocations_A.InvokeSchedControl sc_control_inv) x =
     (\<exists>sc_inv'. sc_ctrl_inv_rel sc_control_inv sc_inv' \<and> x = InvokeSchedControl sc_inv')"
| "inv_relation (Invocations_A.InvokeIRQControl i) x =
     (\<exists>i'. irq_control_inv_relation i i' \<and> x = InvokeIRQControl i')"
| "inv_relation (Invocations_A.InvokeIRQHandler i) x =
     (\<exists>i'. irq_handler_inv_relation i i' \<and> x = InvokeIRQHandler i')"
| "inv_relation (Invocations_A.InvokeCNode i) x =
     (\<exists>i'. cnodeinv_relation i i' \<and> x = InvokeCNode i')"
| "inv_relation (Invocations_A.InvokeArchObject i) x =
     (\<exists>i'. archinv_relation i i' \<and> x = InvokeArchObject i')"

(* In order to assert conditions that must hold for the appropriate
   handleInvocation and handle_invocation calls to succeed, we must have
   some notion of what a valid invocation is.
   This function defines that.
   For example, a InvokeEndpoint requires an endpoint at its first
   constructor argument. *)

primrec
  valid_invocation' :: "Invocations_H.invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_invocation' (InvokeUntyped i) = valid_untyped_inv' i"
| "valid_invocation' (InvokeEndpoint w w2 b c) = (ep_at' w and ex_nonz_cap_to' w)"
| "valid_invocation' (InvokeNotification w w2) = (ntfn_at' w and ex_nonz_cap_to' w)"
| "valid_invocation' (InvokeTCB i) = tcb_inv_wf' i"
| "valid_invocation' (InvokeDomain thread domain) = (tcb_at' thread  and K (domain \<le> maxDomain))"
| "valid_invocation' (InvokeSchedContext i) = valid_sc_inv' i"
| "valid_invocation' (InvokeSchedControl i) = valid_sc_ctrl_inv' i"
| "valid_invocation' (InvokeReply reply grant) = reply_at' reply"
| "valid_invocation' (InvokeIRQControl i) = irq_control_inv_valid' i"
| "valid_invocation' (InvokeIRQHandler i) = irq_handler_inv_valid' i"
| "valid_invocation' (InvokeCNode i) = valid_cnode_inv' i"
| "valid_invocation' (InvokeArchObject i) = valid_arch_inv' i"


(* FIXME: move *)
lemma decodeDomainInvocation_corres:
  shows "\<lbrakk> list_all2 cap_relation (map fst cs) (map fst cs');
           list_all2 (\<lambda>p pa. snd pa = cte_map (snd p)) cs cs' \<rbrakk> \<Longrightarrow>
        corres (ser \<oplus> ((\<lambda>x. inv_relation x \<circ> uncurry Invocations_H.invocation.InvokeDomain) \<circ> (\<lambda>(x,y). Invocations_A.invocation.InvokeDomain x y))) \<top> \<top>
          (decode_domain_invocation label args cs)
          (decodeDomainInvocation label args cs')"
  apply (simp add: decode_domain_invocation_def decodeDomainInvocation_def)
  apply (rule whenE_throwError_corres_initial)
    apply (simp+)[2]
  apply (case_tac "args", simp_all)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>domain domain'. domain = domain'" and R="\<lambda>_. \<top>" and R'="\<lambda>_. \<top>"
            in corres_splitEE)     apply (rule whenE_throwError_corres)
         apply (simp+)[2]
       apply (rule corres_returnOkTT)
       apply simp
      apply (rule whenE_throwError_corres_initial)
        apply simp
       apply (case_tac "cs")
        apply ((case_tac "cs'", ((simp add: null_def)+)[2])+)[2]
      apply (subgoal_tac "cap_relation (fst (hd cs)) (fst (hd cs'))")
       apply (case_tac "fst (hd cs)")
                  apply (case_tac "fst (hd cs')", simp+, rule corres_returnOkTT)
            apply (simp add: inv_relation_def o_def uncurry_def)
           apply (case_tac "fst (hd cs')", fastforce+)
      apply (case_tac "cs")
       apply (case_tac "cs'", ((simp add: list_all2_map2 list_all2_map1)+)[2])
      apply (case_tac "cs'", ((simp add: list_all2_map2 list_all2_map1)+)[2])
     apply (wp | simp)+
  done

lemma decodeInvocation_corres:
  "\<lbrakk>cptr = to_bl cptr'; mi' = message_info_map mi;
    slot' = cte_map slot; cap_relation cap cap';
    args = args'; list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>p pa. snd pa = cte_map (snd p)) excaps excaps' \<rbrakk>
    \<Longrightarrow>
    corres (ser \<oplus> inv_relation)
           (invs and valid_sched and valid_list
                 and valid_cap cap and cte_at slot and cte_wp_at ((=) cap) slot
                 and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s)
                 and case_option \<top> in_user_frame buffer
                 and (\<lambda>s. length args < 2 ^ word_bits))
           (invs' and valid_cap' cap' and cte_at' slot'
            and (\<lambda>s. \<forall>x\<in>set excaps'. s \<turnstile>' fst x \<and> cte_at' (snd x) s)
            and case_option \<top> valid_ipc_buffer_ptr' buffer)
      (decode_invocation first_phase (mi_label mi) args cptr slot cap excaps buffer)
      (RetypeDecls_H.decodeInvocation (msgLabel mi') args' cptr' slot' cap' excaps' first_phase buffer)"
  apply (rule corres_gen_asm)
  apply (unfold decode_invocation_def decodeInvocation_def)
  apply (case_tac cap, simp_all only: cap.simps)
   \<comment> \<open>dammit, simp_all messes things up, must handle cases manually\<close>
             \<comment> \<open>Null\<close>
               apply (simp add: isCap_defs)
              \<comment> \<open>Untyped\<close>
              apply (simp add: isCap_defs Let_def o_def split del: if_split)
            apply (rule corres_guard_imp, rule decodeUntypedInvocation_corres)
                apply ((clarsimp simp:cte_wp_at_caps_of_state)+)[3]
             \<comment> \<open>(Async)Endpoint\<close>
             apply (simp add: isCap_defs returnOk_def)
            apply (simp add: isCap_defs)
            apply (clarsimp simp: returnOk_def neq_Nil_conv)
           \<comment> \<open>ReplyCap\<close>
           apply (simp add: isCap_defs Let_def returnOk_def)
          \<comment> \<open>CNodeCap\<close>
          apply (rename_tac word nat list)
          apply (simp add: isCap_defs Let_def CanModify_def
                      split del: if_split cong: if_cong)
          apply (clarsimp simp add: o_def)
          apply (rule corres_guard_imp)
            apply (rule_tac F="length list \<le> 64" in corres_gen_asm)
          apply (rule decodeCNodeInvocation_corres, simp+)
           apply (simp add: valid_cap_def word_bits_def)
          apply simp
         \<comment> \<open>ThreadCap\<close>
         apply (simp add: isCap_defs Let_def CanModify_def
                     split del: if_split cong: if_cong)
         apply (clarsimp simp add: o_def)
         apply (rule corres_guard_imp)
         apply (rule decodeTCBInvocation_corres, rule refl,
                  simp_all add: valid_cap_def valid_cap'_def)[3]
         apply (simp add: split_def)
         apply (rule list_all2_conj)
          apply (simp add: list_all2_map2 list_all2_map1)
         apply assumption
        \<comment> \<open>DomainCap\<close>
        apply (clarsimp simp: isCap_defs)
        apply (rule corres_guard_imp)
          apply (rule decodeDomainInvocation_corres)
           apply (simp+)[4]
       \<comment> \<open>SchedContextCap\<close>
       apply (clarsimp simp: isCap_defs o_def)
       apply (rule corres_guard_imp, erule decode_sc_inv_corres; clarsimp simp: valid_cap_def)
      \<comment> \<open>SchedControlCap\<close>
      apply (clarsimp simp: isCap_defs o_def)
      apply (rule corres_guard_imp, rule decode_sc_ctrl_inv_corres; clarsimp)
     \<comment> \<open>IRQControl\<close>
     apply (simp add: isCap_defs o_def)
     apply (rule corres_guard_imp, rule decodeIRQControlInvocation_corres, simp+)[1]
    \<comment> \<open>IRQHandler\<close>
    apply (simp add: isCap_defs o_def)
    apply (rule corres_guard_imp, rule decodeIRQHandlerInvocation_corres, simp+)[1]
   \<comment> \<open>Zombie\<close>
   apply (simp add: isCap_defs)
  \<comment> \<open>Arch\<close>
  apply (clarsimp simp only: cap_relation.simps)
  apply (clarsimp simp add: isCap_defs Let_def o_def)
  apply (rule corres_guard_imp [OF arch_decodeInvocation_corres])
      apply (simp_all add: list_all2_map2 list_all2_map1)+
  done

lemma hinv_corres_assist:
  "\<lbrakk> info' = message_info_map info \<rbrakk>
       \<Longrightarrow> corres (fr \<oplus> (\<lambda>(p, cap, extracaps, buffer) (p', capa, extracapsa, buffera).
        p' = cte_map p \<and> cap_relation cap capa \<and> buffer = buffera \<and>
        list_all2
         (\<lambda>x y. cap_relation (fst x) (fst y) \<and> snd y = cte_map (snd x))
         extracaps extracapsa))

           (invs and tcb_at thread and (\<lambda>_. valid_message_info info))
           (invs' and tcb_at' thread)
           (doE (cap, slot) \<leftarrow>
                cap_fault_on_failure cptr' False
                 (lookup_cap_and_slot thread (to_bl cptr'));
                do
                   buffer \<leftarrow> lookup_ipc_buffer False thread;
                   doE extracaps \<leftarrow> lookup_extra_caps thread buffer info;
                       returnOk (slot, cap, extracaps, buffer)
                   odE
                od
            odE)
           (doE (cap, slot) \<leftarrow> capFaultOnFailure cptr' False (lookupCapAndSlot thread cptr');
               do buffer \<leftarrow> VSpace_H.lookupIPCBuffer False thread;
                  doE extracaps \<leftarrow> lookupExtraCaps thread buffer info';
                      returnOk (slot, cap, extracaps, buffer)
                  odE
               od
            odE)"
  apply (clarsimp simp add: split_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF corres_cap_fault])
       \<comment> \<open>switched over to argument of corres_cap_fault\<close>
       apply (rule lookupCapAndSlot_corres, simp)
      apply (rule corres_split[OF lookupIPCBuffer_corres])
        apply (rule corres_splitEE)
           apply (rule lookupExtraCaps_corres; simp)
          apply (rule corres_returnOkTT)
          apply (wp | simp)+
   apply auto
  done

lemma msg_from_syserr_map[simp]:
  "msgFromSyscallError (syscall_error_map err) = msg_from_syscall_error err"
  apply (simp add: msgFromSyscallError_def)
  apply (case_tac err,clarsimp+)
  done

lemma threadSet_tcbDomain_update_ct_not_inQ:
  "\<lbrace>ct_not_inQ \<rbrace> threadSet (tcbDomain_update (\<lambda>_. domain)) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: threadSet_def ct_not_inQ_def)
  apply (wp)
    apply (rule hoare_convert_imp [OF setObject_nosch])
     apply simp
     apply (rule updateObject_default_inv)
    apply (wps setObject_ct_inv)
    apply (wp setObject_tcb_strongest getObject_tcb_wp)+
  apply (case_tac "t = ksCurThread s")
   apply (clarsimp simp: obj_at'_def)+
  done

(* FIXME: move *)
lemma setObject_F_ct_activatable':
  "\<lbrakk>\<And>tcb f. tcbState (F f tcb) = tcbState tcb \<rbrakk> \<Longrightarrow>  \<lbrace>ct_in_state' activatable' and obj_at' ((=) tcb) t\<rbrace>
    setObject t (F f tcb)
   \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def)
  apply (rule hoare_pre)
   apply (wps setObject_ct_inv)
   apply (wp setObject_tcb_strongest)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas setObject_tcbDomain_update_ct_activatable'[wp] = setObject_F_ct_activatable'[where F="tcbDomain_update", simplified]

(* FIXME: move *)
lemma setObject_F_st_tcb_at':
  "\<lbrakk>\<And>tcb f. tcbState (F f tcb) = tcbState tcb \<rbrakk> \<Longrightarrow> \<lbrace>st_tcb_at' P t' and obj_at' ((=) tcb) t\<rbrace>
    setObject t (F f tcb)
   \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: st_tcb_at'_def)
  apply (rule hoare_pre)
  apply (wp setObject_tcb_strongest)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas setObject_tcbDomain_update_st_tcb_at'[wp] = setObject_F_st_tcb_at'[where F="tcbDomain_update", simplified]

lemma threadSet_tcbDomain_update_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not t s\<rbrace>
    threadSet (tcbDomain_update (\<lambda>_. domain)) t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: sch_act_wf_cases split: scheduler_action.split)
  apply (wp hoare_vcg_conj_lift)
    apply (simp add: threadSet_def)
    apply wp
     apply (wps set_tcb'.ksSchedulerAction)
     apply (wp hoare_weak_lift_imp getObject_tcb_wp hoare_vcg_all_lift)+
   apply (rename_tac word)
   apply (rule_tac Q'="\<lambda>_ s. ksSchedulerAction s = SwitchToThread word \<longrightarrow>
                            st_tcb_at' runnable' word s \<and> tcb_in_cur_domain' word s \<and> word \<noteq> t"
                   in hoare_strengthen_post)
    apply (wp hoare_vcg_all_lift hoare_vcg_conj_lift hoare_vcg_imp_lift)+
     apply (simp add: threadSet_def)
     apply (wp getObject_tcb_wp threadSet_tcbDomain_triv')+
   apply (auto simp: obj_at'_def)
  done

lemma tcb_sched_action_schedulable_bool[wp]:
  "tcb_sched_action f t \<lbrace>\<lambda>s. P (schedulable t' s)\<rbrace>"
  apply (wpsimp simp: tcb_sched_action_def thread_get_def wp: set_tcb_queue_wp)
  by (fastforce simp: schedulable_def)

lemma schedulable'_ksReadyQueuesL2Bitmap_update[simp]:
  "schedulable' t (ksReadyQueuesL2Bitmap_update f s) = schedulable' t s"
  by (simp add: schedulable'_def bitmap_fun_defs pred_map_simps opt_map_def active_sc_tcb_at'_def)

lemma schedulable'_ksReadyQueuesL1Bitmap_update[simp]:
  "schedulable' t (ksReadyQueuesL1Bitmap_update f s) = schedulable' t s"
  by (simp add: schedulable'_def bitmap_fun_defs pred_map_simps opt_map_def active_sc_tcb_at'_def)

lemma schedulable'_ksReadyQueues_update[simp]:
  "schedulable' t (ksReadyQueues_update f s) = schedulable' t s"
  by (simp add: schedulable'_def bitmap_fun_defs pred_map_simps opt_map_def active_sc_tcb_at'_def)

crunch removeFromBitmap
  for schedulable'[wp]: "\<lambda>s. P (schedulable' tcbPtr s)"

lemma tcbSchedDequeue_schedulable'[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>\<lambda>s. P (schedulable' tcbPtr' s)\<rbrace>"
  unfolding tcbSchedDequeue_def tcbQueueRemove_def setQueue_def
  by (wpsimp wp: threadSet_schedulable'_fields_inv getTCB_wp threadGet_wp hoare_drop_imps)

lemma setDomain_corres:
  "corres dc
     (valid_tcbs and pspace_aligned and pspace_distinct and weak_valid_sched_action
      and in_correct_ready_q and ready_qs_distinct and ready_or_release
      and active_scs_valid and tcb_at tptr)
     (invs' and (\<lambda>_. new_dom \<le> maxDomain))
     (set_domain tptr new_dom)
     (setDomain tptr new_dom)"
  supply comp_apply[simp del]
  apply (rule corres_gen_asm2)
  apply (simp add: set_domain_def setDomain_def thread_set_domain_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split[OF tcbSchedDequeue_corres], simp)
        apply (rule corres_split[OF threadSet_not_queued_corres];
               simp add: tcb_relation_def tcb_cap_cases_def tcb_cte_cases_def cteSizeBits_def)
          apply (rule corres_split[OF getSchedulable_corres])
            apply (rule corres_split[OF corres_when[OF _ tcbSchedEnqueue_corres]], simp, simp)
              apply (rule corres_when[OF _ rescheduleRequired_corres], simp)
             apply (wpsimp wp: hoare_vcg_const_imp_lift)
            apply (wpsimp wp: hoare_vcg_const_imp_lift tcbSchedEnqueue_valid_tcbs')
           apply wpsimp
          apply (wpsimp wp: getSchedulable_wp)
         apply (wpsimp wp: hoare_vcg_imp_lift' thread_set_valid_tcbs
                           thread_set_weak_valid_sched_action
                           thread_set_in_correct_ready_q_not_queued
                           thread_set_no_change_tcb_state thread_set_schedulable)
        apply (wpsimp wp: hoare_vcg_imp_lift' threadSet_valid_tcbs'
                          threadSet_sched_pointers threadSet_valid_sched_pointers
                          threadSet_schedulable'_fields_inv)
       apply (wpsimp wp: hoare_vcg_imp_lift' tcb_dequeue_not_queued')
      apply wpsimp
      apply (clarsimp cong: conj_cong)
      apply (rule hoare_vcg_conj_lift, strengthen valid_tcb'_tcbDomain_update, wpsimp)
      apply (wpsimp wp: hoare_vcg_imp_lift')
     apply wpsimp+
   apply (clarsimp simp: schedulable_def2)
  apply fastforce
  done

lemma performInvocation_corres:
  "\<lbrakk> inv_relation i i'; call \<longrightarrow> block \<rbrakk> \<Longrightarrow>
   corres (dc \<oplus> (=))
     (einvs and valid_machine_time and valid_invocation i
            and schact_is_rct
            and current_time_bounded
            and ct_active
            and ct_released
            and ct_not_in_release_q
            and (\<lambda>s. (\<exists>w w2 b c. i = Invocations_A.InvokeEndpoint w w2 b c) \<longrightarrow> st_tcb_at simple (cur_thread s) s)
            and cur_sc_active and current_time_bounded and consumed_time_bounded
            and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
            and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s))
     (invs' and sch_act_simple and valid_invocation' i' and ct_active')
     (perform_invocation block call can_donate i) (performInvocation block call can_donate i')"
  apply (simp add: performInvocation_def)
  apply add_sym_refs
  apply (case_tac i)

             apply (clarsimp simp: o_def liftE_bindE)
             apply (rule corres_stateAssertE_add_assertion)
             apply (rule corres_guard_imp)
                apply (rule corres_split_norE)
                   apply (rule corres_rel_imp, rule inv_untyped_corres)
                    apply simp
                   apply (case_tac x, simp_all)[1]
                  apply (rule corres_returnOkTT)
                  apply simp
                 apply wpsimp+

            apply (rule corres_guard_imp)
              apply (rule corres_split[OF getCurThread_corres])
                apply simp
                apply (rule corres_split[OF sendIPC_corres])
                   apply simp
                  apply (rule corres_trivial)
                  apply simp
                 apply wp+
             apply (clarsimp simp: invs_def valid_sched_def valid_state_def valid_pspace_def
                                   fault_tcbs_valid_states_to_except_set schact_is_rct_sane
                                   ct_in_state_def released_sc_tcb_at_def active_sc_tcb_at_def2)

             apply (intro conjI)
                apply fastforce
               apply fastforce
              apply (fastforce elim!: st_tcb_ex_cap)
             apply (clarsimp simp: pred_tcb_at_def obj_at_def)
            apply simp
           apply (rule corres_guard_imp)
             apply (simp add: liftE_bindE)
             apply (rule corres_split[OF sendSignal_corres])
               apply (rule corres_trivial)
               apply (simp add: returnOk_def)
              apply wpsimp+
          apply (rule corres_guard_imp)
            apply (rule corres_split_eqr[OF getCurThread_corres])
              apply (rule corres_split_nor[OF doReplyTransfer_corres])
                apply (rule corres_trivial, simp)
               apply wp+
           apply (clarsimp simp: tcb_at_invs)
          apply simp
         apply (clarsimp simp: liftME_def)
         apply (rule corres_guard_imp)
           apply (erule invokeTCB_corres)
          apply (fastforce simp: current_time_bounded_def)+
        \<comment> \<open>domain cap\<close>
        apply (clarsimp simp: invoke_domain_def)
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF setDomain_corres])
            apply (rule corres_trivial, simp)
           apply (wp)+
         apply ((clarsimp | fastforce dest: valid_sched_valid_ready_qs)+)[3]
       \<comment> \<open>SchedContext\<close>
       apply (rule corres_guard_imp)
         apply (rule corres_splitEE)
            apply (simp)
            apply (erule invokeSchedContext_corres)
           apply (rule corres_trivial, simp add: returnOk_def)
          apply (wpsimp+)[4]
      \<comment> \<open>SchedControl\<close>
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE)
           apply (simp)
           apply (erule invokeSchedControlConfigureFlags_corres)
          apply (rule corres_trivial, simp add: returnOk_def comp_apply)
         apply (wpsimp+)[4]
     \<comment> \<open>CNodes\<close>
     apply clarsimp
     apply (rule corres_stateAssertE_add_assertion)
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE[OF invokeCNode_corres])
           apply assumption
          apply (rule corres_trivial, simp add: returnOk_def)
         apply wp+
       apply (clarsimp+)[2]
     apply (clarsimp simp: sym_refs_asrt_def)
    apply (clarsimp simp: liftME_def[symmetric] o_def dc_def[symmetric])
    apply (rule corres_guard_imp, rule performIRQControl_corres; fastforce)
   apply (clarsimp simp: liftME_def[symmetric] o_def dc_def[symmetric])
   apply (rule corres_guard_imp, rule invokeIRQHandler_corres; fastforce)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule arch_performInvocation_corres, assumption)
   apply (clarsimp+)[2]
  done

crunch sendSignal, setDomain
  for tcb_at'[wp]: "tcb_at' t"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T t s)"
  (simp: crunch_simps wp: crunch_wps)

crunch restart, bindNotification, performTransfer, invokeTCB, doReplyTransfer,
         performIRQControl, InterruptDecls_H.invokeIRQHandler, sendIPC,
         invokeSchedContext, invokeSchedControlConfigureFlags, handleFault
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (simp: crunch_simps
   wp: crunch_wps checkCap_inv hoare_vcg_all_lift
   ignore: checkCapAt)

end

global_interpretation invokeTCB: typ_at_all_props' "invokeTCB i"
  by typ_at_props'
global_interpretation doReplyTransfer: typ_at_all_props' "doReplyTransfer s r g"
  by typ_at_props'
global_interpretation performIRQControl: typ_at_all_props' "performIRQControl i"
  by typ_at_props'
sublocale Arch < arch_invokeIRQHandler: typ_at_all_props' "invokeIRQHandler i"
  by typ_at_props'
global_interpretation invokeIRQHandler: typ_at_all_props' "InterruptDecls_H.invokeIRQHandler i"
  by typ_at_props'
global_interpretation sendIPC: typ_at_all_props' "sendIPC bl call bdg cg cgr cd t' ep"
  by typ_at_props'
global_interpretation invokeSchedContext: typ_at_all_props' "invokeSchedContext i"
  by typ_at_props'
global_interpretation invokeSchedControlConfigureFlags: typ_at_all_props' "invokeSchedControlConfigureFlags i"
  by typ_at_props'
global_interpretation handleFault: typ_at_all_props' "handleFault t ex"
  by typ_at_props'

lemma pinv_tcb'[wp]:
  "\<lbrace>invs' and st_tcb_at' active' tptr
          and valid_invocation' i and ct_active'\<rbrace>
     RetypeDecls_H.performInvocation block call can_donate i
   \<lbrace>\<lambda>rv. tcb_at' tptr\<rbrace>"
  unfolding performInvocation_def
  by (cases i; simp; wpsimp wp: invokeArch_tcb_at' simp: stateAssertE_def sym_refs_asrt_def)

lemma sts_mcpriority_tcb_at'[wp]:
  "\<lbrace>mcpriority_tcb_at' P t\<rbrace>
    setThreadState st t'
   \<lbrace>\<lambda>_. mcpriority_tcb_at' P t\<rbrace>"
  apply (cases "t = t'",
         simp_all add: setThreadState_def
                  split del: if_split)
   apply ((wp threadSet_pred_tcb_at_state | simp)+)[1]
   apply (wp threadSet_obj_at'_really_strongest
               | simp add: pred_tcb_at'_def)+
  done

crunch setThreadState
  for valid_ipc_buffer_ptr'[wp]: "valid_ipc_buffer_ptr' buf"

context begin interpretation Arch . (*FIXME: arch-split*)

lemma sts_valid_inv'[wp]:
  "setThreadState st t \<lbrace>valid_invocation' i\<rbrace>"
  supply opt_mapE[elim!]
  apply (case_tac i; simp)
             apply (wpsimp wp: sts_valid_untyped_inv')
            apply (wpsimp+)[4]
        \<comment>\<open>start InvokeTCB\<close>
        apply (rename_tac tcbinvocation)
        apply (case_tac tcbinvocation; simp)
              apply (wpsimp wp: hoare_case_option_wp2 hoare_case_option_wp sts_mcpriority_tcb_at'
                     | clarsimp split: option.splits)+
        \<comment>\<open>end InvokeTCB\<close>
       \<comment>\<open>start InvokeSchedContext\<close>
       apply (rename_tac schedcontextinvocation)
       apply (case_tac schedcontextinvocation; simp)
           apply (wpsimp wp: hoare_case_option_wp split: option.splits)
          apply (rename_tac bindCap, case_tac bindCap; wpsimp)
         apply (rename_tac bindCap, case_tac bindCap; wpsimp)
        apply wpsimp
       apply ((wpsimp wp: hoare_case_option_wp split: option.splits | wps)+)[1]
       \<comment>\<open>end InvokeSchedContext\<close>
      apply (rename_tac schedcontrolinvocation)
      apply (case_tac schedcontrolinvocation; wpsimp wp: hoare_vcg_ex_lift)
     apply (rename_tac cnode_invocation)
     apply (case_tac cnode_invocation; wpsimp simp: cte_wp_at_ctes_of split: option.splits)
    apply (rename_tac irqcontrol_invocation)
    apply (case_tac irqcontrol_invocation; simp)
     apply (rename_tac arch_irqhandler_issue)
     apply (case_tac arch_irqhandler_issue; wpsimp simp: irq_issued'_def)
    apply (wpsimp simp: irq_issued'_def)
   apply (rename_tac irqhandler_invocation)
   apply (case_tac irqhandler_invocation; wpsimp wp: hoare_vcg_ex_lift simp: comp_def)
  apply (wpsimp wp: sts_valid_arch_inv')
  done

crunch decodeDomainInvocation, decodeSchedContextInvocation, decodeSchedControlInvocation
  for inv[wp]: P
  (wp: crunch_wps simp: crunch_simps)

lemma arch_cap_exhausted:
  "\<lbrakk>\<not> isFrameCap param_e; \<not> isPageTableCap param_e; \<not> isASIDControlCap param_e; \<not> isASIDPoolCap param_e\<rbrakk>
    \<Longrightarrow> undefined \<lbrace>P\<rbrace>"
  by (cases param_e; simp add: isCap_simps)

crunch decodeInvocation
  for inv[wp]: P
  (simp: crunch_simps wp: crunch_wps arch_cap_exhausted mapME_x_inv_wp getASID_wp)

(* FIXME: move to TCB *)
lemma dec_dom_inv_wf[wp]:
  "\<lbrace>invs' and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile>' fst x)\<rbrace>
  decodeDomainInvocation label args excaps
  \<lbrace>\<lambda>x s. tcb_at' (fst x) s \<and> snd x \<le> maxDomain\<rbrace>, -"
  apply (simp add:decodeDomainInvocation_def)
  apply (wp whenE_throwError_wp | wpc |simp)+
  apply clarsimp
  apply (drule_tac x = "hd excaps" in bspec)
   apply (rule hd_in_set)
   apply (simp add:null_def)
  apply (simp add:valid_cap'_def)
  apply (simp add:not_le)
  apply (simp del: Word.of_nat_unat flip: ucast_nat_def)
  apply (rule word_of_nat_le)
  apply (simp add: le_maxDomain_eq_less_numDomains)
  done

lemma decode_inv_wf'[wp]:
  "\<lbrace>valid_cap' cap and invs' and sch_act_simple
          and cte_wp_at' ((=) cap \<circ> cteCap) slot and real_cte_at' slot
          and (\<lambda>s. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
          and case_option \<top> valid_ipc_buffer_ptr' buffer
          and (\<lambda>s. \<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
          and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs' (fst cap) (irq_node' s). ex_cte_cap_to' r s)
          and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>zobj_refs' (fst cap). ex_nonz_cap_to' r s)
          and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile>' fst x)
          and (\<lambda>s. \<forall>x \<in> set excaps. real_cte_at' (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to' isCNodeCap (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' (badge_derived' (fst x) \<circ> cteCap) (snd x) s)\<rbrace>
     decodeInvocation label args cap_index slot cap excaps first_phase buffer
   \<lbrace>valid_invocation'\<rbrace>,-"
  apply (case_tac cap,
         simp_all add: decodeInvocation_def Let_def isCap_defs uncurry_def split_def
            split del: if_split
                 cong: if_cong)
             apply ((rule hoare_pre,
                     ((wpsimp wp: decodeTCBInv_wf decodeSchedControlInvocation_wf
                                  decodeSchedContextInvocation_wf
                              simp: o_def)+)[1],
                     clarsimp simp: valid_cap'_def cte_wp_at_ctes_of)
                    | intro exI conjI | simp | drule sym)+
  done

lemma ct_active_imp_simple'[elim!]:
  "ct_active' s \<Longrightarrow> st_tcb_at' simple' (ksCurThread s) s"
  by (clarsimp simp: ct_in_state'_def
              elim!: pred_tcb'_weakenE)

lemma ct_running_imp_simple'[elim!]:
  "ct_running' s \<Longrightarrow> st_tcb_at' simple' (ksCurThread s) s"
  by (clarsimp simp: ct_in_state'_def
              elim!: pred_tcb'_weakenE)

lemma active_ex_cap'[elim]:
  "\<lbrakk> ct_active' s; if_live_then_nonz_cap' s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to' (ksCurThread s) s"
  by (fastforce simp: ct_in_state'_def elim!: st_tcb_ex_cap'')

crunch handleFaultReply
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"

crunch handleFaultReply
 for sch_act_simple[wp]: sch_act_simple
  (wp: crunch_wps)

lemma transferCaps_non_null_cte_wp_at':
  assumes PUC: "\<And>cap. P cap \<Longrightarrow> \<not> isUntypedCap cap"
  shows "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte) \<and> cteCap cte \<noteq> capability.NullCap) ptr\<rbrace>
     transferCaps info caps ep rcvr rcvBuf
   \<lbrace>\<lambda>_. cte_wp_at' (\<lambda>cte. P (cteCap cte) \<and> cteCap cte \<noteq> capability.NullCap) ptr\<rbrace>"
proof -
  have CTEF: "\<And>P p s. \<lbrakk> cte_wp_at' P p s; \<And>cte. P cte \<Longrightarrow> False \<rbrakk> \<Longrightarrow> False"
    by (erule cte_wp_atE', auto)
  show ?thesis
    unfolding transferCaps_def
    apply (wp | wpc)+
        apply (rule transferCapsToSlots_pres2)
         apply (rule hoare_weaken_pre [OF cteInsert_weak_cte_wp_at3])
         apply (rule PUC,simp)
         apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (wp hoare_vcg_all_lift hoare_weak_lift_imp | simp add:ball_conj_distrib)+
    done
qed

lemma copyMRs_cte_wp_at'[wp]:
  "\<lbrace>cte_wp_at' P ptr\<rbrace> copyMRs sender sendBuf receiver recvBuf n \<lbrace>\<lambda>_. cte_wp_at' P ptr\<rbrace>"
  unfolding copyMRs_def
  apply (wp mapM_wp | wpc | simp add: split_def | rule equalityD1)+
  done

lemma doNormalTransfer_non_null_cte_wp_at':
  assumes PUC: "\<And>cap. P cap \<Longrightarrow> \<not> isUntypedCap cap"
  shows
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte) \<and> cteCap cte \<noteq> capability.NullCap) ptr\<rbrace>
   doNormalTransfer st send_buffer ep b gr rt recv_buffer
   \<lbrace>\<lambda>_. cte_wp_at' (\<lambda>cte. P (cteCap cte) \<and> cteCap cte \<noteq> capability.NullCap) ptr\<rbrace>"
  unfolding doNormalTransfer_def
  apply (wp transferCaps_non_null_cte_wp_at' | simp add:PUC)+
  done

crunch doFaultTransfer, setMRs
  for cte_wp_at'[wp]: "cte_wp_at' P ptr"
  (wp: crunch_wps simp: zipWithM_x_mapM)

lemma doIPCTransfer_non_null_cte_wp_at':
  assumes PUC: "\<And>cap. P cap \<Longrightarrow> \<not> isUntypedCap cap"
  shows
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte) \<and> cteCap cte \<noteq> capability.NullCap) ptr\<rbrace>
   doIPCTransfer sender endpoint badge grant receiver
   \<lbrace>\<lambda>_. cte_wp_at' (\<lambda>cte. P (cteCap cte) \<and> cteCap cte \<noteq> capability.NullCap) ptr\<rbrace>"
  unfolding doIPCTransfer_def
  apply (wp doNormalTransfer_non_null_cte_wp_at' hoare_drop_imp hoare_allI | wpc | clarsimp simp:PUC)+
  done

lemma doIPCTransfer_non_null_cte_wp_at2':
  fixes P
  assumes PNN: "\<And>cte. P (cteCap cte) \<Longrightarrow> cteCap cte \<noteq> capability.NullCap"
   and    PUC: "\<And>cap. P cap \<Longrightarrow> \<not> isUntypedCap cap"
  shows "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) ptr\<rbrace>
         doIPCTransfer sender endpoint badge grant receiver
         \<lbrace>\<lambda>_. cte_wp_at' (\<lambda>cte. P (cteCap cte)) ptr\<rbrace>"
  proof -
    have PimpQ: "\<And>P Q ptr s. \<lbrakk> cte_wp_at' (\<lambda>cte. P (cteCap cte)) ptr s;
                               \<And>cte. P (cteCap cte) \<Longrightarrow> Q (cteCap cte) \<rbrakk>
                             \<Longrightarrow> cte_wp_at' (\<lambda>cte. P (cteCap cte) \<and> Q (cteCap cte)) ptr s"
      by (erule cte_wp_at_weakenE', clarsimp)
    show ?thesis
      apply (rule hoare_chain [OF doIPCTransfer_non_null_cte_wp_at'])
       apply (erule PUC)
       apply (erule PimpQ)
       apply (drule PNN, clarsimp)
      apply (erule cte_wp_at_weakenE')
      apply (clarsimp)
      done
  qed

lemma st_tcb_at'_eqD:
  "\<lbrakk> st_tcb_at' (\<lambda>s. s = st) t s; st_tcb_at' (\<lambda>s. s = st') t s \<rbrakk> \<Longrightarrow> st = st'"
  by (clarsimp simp add: pred_tcb_at'_def obj_at'_def)

lemma isReply_awaiting_reply':
  "isReply st = awaiting_reply' st"
  by (case_tac st, (clarsimp simp add: isReply_def isBlockedOnReply_def)+)

lemma handleTimeout_invs':
  "\<lbrace>invs' and st_tcb_at' active' tptr and sch_act_not tptr and ex_nonz_cap_to' tptr\<rbrace>
   handleTimeout tptr timeout
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: handleTimeout_def)
  apply wpsimp
      apply (rename_tac tcb)
      apply (rule_tac Q'="\<lambda>_. invs'"
                  and E'="\<lambda>_. invs' and valid_idle' and st_tcb_at' active' tptr and sch_act_not tptr
                             and (\<lambda>s. False \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> None) tptr s)
                             and ex_nonz_cap_to' tptr
                             and (\<lambda>s. \<exists>n\<in>dom tcb_cte_cases. cte_wp_at' (\<lambda>cte. cteCap cte
                                                                               = cteCap (tcbTimeoutHandler tcb))
                                                                        (tptr + n) s)"
                   in hoare_strengthen_postE)
        apply (rule sfi_invs_plus')
       apply (wpsimp wp: getTCB_wp
                   simp: isValidTimeoutHandler_def)+
  apply (clarsimp simp: cte_wp_at'_obj_at' tcb_cte_cases_def obj_at'_def valid_idle'_asrt_def)
  done

crunch isValidTimeoutHandler
  for inv[wp]: P

crunch ifCondRefillUnblockCheck
  for sch_act_simple[wp]: sch_act_simple
  (simp: crunch_simps sch_act_simple_def)

lemma ifConfRefillUnblockCheck_ko_at'_tcb[wp]:
  "ifCondRefillUnblockCheck scOpt act ast \<lbrace>\<lambda>s. P (ko_at' (ko :: tcb) tcbPtr s)\<rbrace>"
  unfolding ifCondRefillUnblockCheck_def refillUnblockCheck_def refillHeadOverlappingLoop_def
            mergeOverlappingRefills_def updateRefillHd_def updateSchedContext_def refillPopHead_def
  by (wpsimp wp: whileLoop_valid_inv hoare_drop_imps getRefillNext_wp isRoundRobin_wp)

lemma doReplyTransfer_invs'[wp]:
  "\<lbrace>invs' and tcb_at' sender and reply_at' replyPtr and sch_act_simple\<rbrace>
   doReplyTransfer sender replyPtr grant
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding doReplyTransfer_def
  apply (wpsimp wp: handleTimeout_invs' postpone_invs' isValidTimeoutHandler_inv hoare_drop_imps)
           apply (wpsimp wp: threadGet_wp)
          apply wpsimp
         apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> sch_act_not x2 s \<and> ex_nonz_cap_to' x2 s"
                      in hoare_post_imp)
          apply (fastforce simp: runnable_eq_active' obj_at_simps st_tcb_at'_def)
         apply (wpsimp wp: setThreadState_Running_invs')
              apply (intro conjI)
               apply (wpsimp wp: setThreadState_Restart_invs')
              apply (wpsimp wp: sts_invs' sts_st_tcb_at'_cases)
             apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) xa s
                                      \<and> sch_act_not xa s \<and> ex_nonz_cap_to' xa s"
                          in hoare_post_imp)
              apply (clarsimp simp: obj_at_simps st_tcb_at'_def is_BlockedOnReply_def)
              apply metis
             apply (wpsimp wp: threadSet_fault_invs' threadSet_st_tcb_at2)+
       apply (wpsimp wp: replyRemove_invs' gts_wp' hoare_drop_imps)+
  by (fastforce intro: st_tcb_ex_cap''
                 simp: isReply_def split: thread_state.splits)

lemma ct_active_runnable' [simp]:
  "ct_active' s \<Longrightarrow> ct_in_state' runnable' s"
  by (fastforce simp: ct_in_state'_def elim!: pred_tcb'_weakenE)

crunch tcbSchedEnqueue
  for valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  (wp: valid_irq_node_lift )

lemma tcbSchedEnqueue_valid_action:
  "\<lbrace>\<lambda>s. \<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s\<rbrace>
  tcbSchedEnqueue ptr
  \<lbrace>\<lambda>rv s. \<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s\<rbrace>"
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply clarsimp
  done

lemma threadSet_tcbDomain_update_invs':
  "\<lbrace>invs' and  obj_at' (Not \<circ> tcbQueued) t and K (ds \<le> maxDomain) \<rbrace>
   threadSet (tcbDomain_update (\<lambda>_. ds)) t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply comp_apply[simp del]
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (clarsimp simp: invs'_def)
  apply (wp threadSet_valid_pspace'T_P)
  apply (simp add: tcb_cte_cases_def)+
   apply (wp valid_irq_node_lift valid_irq_handlers_lift'' threadSet_ctes_ofT
             threadSet_valid_dom_schedule' threadSet_iflive'T threadSet_ifunsafe'T
             untyped_ranges_zero_lift threadSet_valid_sched_pointers
             sym_heap_sched_pointers_lift threadSet_tcbSchedNexts_of threadSet_tcbSchedPrevs_of
          | simp add: tcb_cte_cases_def cteSizeBits_def cteCaps_of_def o_def invs'_def
          | intro allI)+
  apply (fastforce simp: obj_at'_def opt_map_def)
  done

lemma threadSet_not_curthread_ct_domain:
  "\<lbrace>\<lambda>s. ptr \<noteq> ksCurThread s \<and> ct_idle_or_in_cur_domain' s\<rbrace> threadSet f ptr \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add:ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (wp hoare_vcg_imp_lift hoare_vcg_disj_lift | wps)+
  apply clarsimp
  done

lemma schedContextBindNtfn_invs':
  "\<lbrace>invs' and ex_nonz_cap_to' scPtr and ex_nonz_cap_to' ntfnPtr\<rbrace>
   schedContextBindNtfn scPtr ntfnPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: schedContextBindNtfn_def updateSchedContext_def)
  apply (wpsimp wp: setSchedContext_invs' setNotification_invs' hoare_vcg_imp_lift'
                    hoare_vcg_all_lift getNotification_wp)
  apply (rule conjI)
   apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn'
                    simp: valid_ntfn'_def
                   split: ntfn.splits)
  apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps
                         refillSize_def)
  done

lemma contextYieldToUpdateQueues_invs'_helper:
   "\<lbrace>\<lambda>s. invs' s \<and> sc_at' scPtr s \<and> valid_sched_context' sc s \<and> valid_sched_context_size' sc
         \<and> ex_nonz_cap_to' scPtr s \<and> ex_nonz_cap_to' ctPtr s \<and> tcb_at' ctPtr s\<rbrace>
    do y \<leftarrow> threadSet (tcbYieldTo_update (\<lambda>_. Some scPtr)) ctPtr;
       setSchedContext scPtr (scYieldFrom_update (\<lambda>_. Some ctPtr) sc)
    od
    \<lbrace>\<lambda>_. invs'\<rbrace>"
   apply (clarsimp simp: invs'_def valid_pspace'_def valid_dom_schedule'_def)
   apply (wp threadSet_valid_objs' threadSet_mdb' threadSet_iflive' threadSet_cap_to
             threadSet_ifunsafe'T threadSet_ctes_ofT threadSet_valid_sched_pointers
             sym_heap_sched_pointers_lift threadSet_tcbSchedNexts_of threadSet_tcbSchedPrevs_of
             untyped_ranges_zero_lift valid_irq_node_lift valid_irq_handlers_lift''
             hoare_vcg_const_imp_lift hoare_vcg_imp_lift' threadSet_valid_replies'
          | clarsimp simp: tcb_cte_cases_def cteSizeBits_def cteCaps_of_def)+
  by (fastforce simp: obj_at_simps valid_tcb'_def tcb_cte_cases_def cteSizeBits_def comp_def
                      valid_sched_context'_def valid_sched_context_size'_def inQ_def refillSize_def)

crunch schedContextResume
  for bound_scTCB[wp]: "obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr"
  (wp: crunch_wps simp: crunch_simps)

lemma schedContextCancelYieldTo_bound_scTCB[wp]:
  "schedContextCancelYieldTo tptr \<lbrace>obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr\<rbrace>"
  apply (clarsimp simp: schedContextCancelYieldTo_def)
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (rule hoare_when_cases, simp)
  apply (wpsimp wp: set_sc'.obj_at' simp: updateSchedContext_def)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: if_split)
  done

lemma schedContextUpdateConsumed_bound_scTCB[wp]:
  "schedContextUpdateConsumed tptr \<lbrace>obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr\<rbrace>"
  apply (clarsimp simp: schedContextUpdateConsumed_def)
  apply (wpsimp wp: set_sc'.obj_at' simp: updateSchedContext_def)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def split: if_split)
  done

crunch schedContextCompleteYieldTo
  for bound_scTCB[wp]: "obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr"

lemma contextYieldToUpdateQueues_invs':
  "\<lbrace>invs' and (\<lambda>s. obj_at' (\<lambda>a. \<exists>y. scTCB a = Some y) scPtr s) and ct_active'
    and ex_nonz_cap_to' scPtr and cur_tcb'\<rbrace>
   contextYieldToUpdateQueues scPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: contextYieldToUpdateQueues_def)
  apply (rule bind_wp[OF _ get_sc_sp'], rename_tac sc)
  apply (rule bind_wp[OF _ getSchedulable_sp])
  apply (rule hoare_if; (solves wpsimp)?)
  apply (rule bind_wp[OF _ getCurThread_sp], rename_tac ctPtr)
  apply (rule bind_wp_fwd_skip, solves wpsimp)+
  apply (rule hoare_if)
   apply wpsimp
  apply clarsimp
  apply (subst bind_assoc[symmetric])
  apply (rule_tac Q'="\<lambda>_. invs'" in bind_wp_fwd)
   apply (wp contextYieldToUpdateQueues_invs'_helper)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                    simp: cur_tcb'_def)
  apply wpsimp
  done

crunch schedContextResume
  for st_tcb_at'[wp]: "\<lambda>s. Q (st_tcb_at' P tptr s)"
  (wp: crunch_wps threadSet_wp mapM_wp_inv simp: crunch_simps)

crunch schedContextResume
  for scTCBs_of[wp]: "\<lambda>s. P (scTCBs_of s)"
  (wp: crunch_wps threadSet_st_tcb_at2 mapM_wp_inv simp: crunch_simps)

crunch schedContextCompleteYieldTo
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' ptr"
  (simp: crunch_simps tcb_cte_cases_def cteSizeBits_def wp: crunch_wps threadSet_cap_to)

lemma schedContextYiedTo_invs':
  "\<lbrace>invs' and ct_active' and ex_nonz_cap_to' scPtr
    and (\<lambda>s. obj_at' (\<lambda>sc. \<exists>t. scTCB sc = Some t) scPtr s)\<rbrace>
   schedContextYieldTo scPtr buffer
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: schedContextYieldTo_def)
  apply (wpsimp wp: contextYieldToUpdateQueues_invs' setConsumed_invs'
              simp: ct_in_state'_def
         | wps)+
  by (fastforce simp: cur_tcb'_def)

lemma invokeSchedContext_invs':
  "\<lbrace>invs' and  ct_active' and valid_sc_inv' iv\<rbrace>
   invokeSchedContext iv
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: invokeSchedContext_def)
  apply (cases iv; clarsimp)
      apply (wpsimp wp: setConsumed_invs')
     apply (rename_tac scPtr cap)
     apply (case_tac cap; clarsimp)
      apply (wpsimp wp: schedContextBindTCB_invs')
      apply (clarsimp simp: pred_tcb_at'_def obj_at_simps)
     apply (wpsimp wp: schedContextBindNtfn_invs')
    apply (rename_tac scPtr cap)
    apply (case_tac cap; clarsimp)
     apply wpsimp
     using global'_sc_no_ex_cap apply fastforce
    apply wpsimp
   apply wpsimp
   using global'_sc_no_ex_cap apply fastforce
  apply (wpsimp wp: schedContextYiedTo_invs')
  apply (fastforce simp: obj_at_simps)
  done

lemma setDomain_invs':
  "\<lbrace>invs' and tcb_at' ptr and K (domain \<le> maxDomain)\<rbrace>
   setDomain ptr domain
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply comp_apply[simp del]
  unfolding setDomain_def
  apply (wpsimp wp: getSchedulable_wp hoare_vcg_if_lift2)
     apply (rule_tac Q'="\<lambda>_. invs'" in hoare_post_imp)
      apply fastforce
     by (wpsimp wp: threadSet_tcbDomain_update_invs' tcbSchedDequeue_not_queued)+

crunch refillNew, refillUpdate, commitTime
  for pred_tcb_at''[wp]: "\<lambda>s. Q (pred_tcb_at' proj P tcbPtr s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' ptr"
  (simp: crunch_simps wp: crunch_wps hoare_vcg_all_lift)

lemma scSBadge_update_invs'[wp]:
  "updateSchedContext scPtr (scBadge_update f) \<lbrace>invs'\<rbrace>"
  apply (wpsimp wp: updateSchedContext_invs')
  apply (fastforce elim!: live_sc'_ko_ex_nonz_cap_to' dest: invs'_ko_at_valid_sched_context'
                    simp: live_sc'_def)
  done

lemma scSporadic_update_invs'[wp]:
  "updateSchedContext scPtr (scSporadic_update f) \<lbrace>invs'\<rbrace>"
  apply (wpsimp wp: updateSchedContext_invs')
  apply (fastforce elim!: live_sc'_ko_ex_nonz_cap_to' dest: invs'_ko_at_valid_sched_context'
                    simp: live_sc'_def)
  done

lemma invokeSchedControlConfigureFlags_invs':
  "\<lbrace>invs' and valid_sc_ctrl_inv' iv\<rbrace>
   invokeSchedControlConfigureFlags iv
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: invokeSchedControlConfigureFlags_def)
  apply (cases iv; clarsimp)
  apply (rename_tac sc_ptr budget period mrefills badge flag)
  apply (rule bind_wp[OF _ get_sc_sp'])
  apply (rule_tac Q'="\<lambda>_ s. ?pre s \<and> sc_at' sc_ptr s \<and> ex_nonz_cap_to' sc_ptr s"
               in bind_wp_fwd)
   apply (rule hoare_when_cases, simp)
   apply (wpsimp wp: hoare_vcg_if_lift refillNew_invs' refillUpdate_invs' commitTime_invs'
                     tcbReleaseRemove_invs' hoare_vcg_ex_lift hoare_vcg_imp_lift'
          | wps)+
  by (fastforce simp: st_tcb_at'_def obj_at_simps valid_refills_number'_def)

lemma performInv_invs'[wp]:
  "\<lbrace>invs' and ct_active' and valid_invocation' i
          and (\<lambda>s. can_donate \<longrightarrow> bound_sc_tcb_at' bound (ksCurThread s) s)
          and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   performInvocation block call can_donate i
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performInvocation_def)
  apply (cases i)
  by (clarsimp simp: stateAssertE_def sym_refs_asrt_def ct_in_state'_def sch_act_simple_def
      | wp tcbinv_invs' arch_performInvocation_invs' setDomain_invs' stateAssertE_inv
           stateAssertE_wp invokeSchedControlConfigureFlags_invs' invokeSchedContext_invs'
      | erule active_ex_cap'[simplified ct_in_state'_def])+

lemma getSlotCap_to_refs[wp]:
  "\<lbrace>\<top>\<rbrace> getSlotCap ref \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s\<rbrace>"
  by (simp add: getSlotCap_def | wp)+

lemma lcs_valid' [wp]:
  "\<lbrace>invs'\<rbrace> lookupCapAndSlot t xs \<lbrace>\<lambda>x s. s \<turnstile>' fst x\<rbrace>, -"
  unfolding lookupCapAndSlot_def
  apply (rule hoare_pre)
   apply (wp|clarsimp simp: split_def)+
  done

lemma lcs_ex_cap_to' [wp]:
  "\<lbrace>invs'\<rbrace> lookupCapAndSlot t xs \<lbrace>\<lambda>x s. \<forall>r\<in>cte_refs' (fst x) (irq_node' s). ex_cte_cap_to' r s\<rbrace>, -"
  unfolding lookupCapAndSlot_def
  apply (rule hoare_pre)
   apply (wp | simp add: split_def)+
  done

lemma lcs_ex_nonz_cap_to' [wp]:
  "\<lbrace>invs'\<rbrace> lookupCapAndSlot t xs \<lbrace>\<lambda>x s. \<forall>r\<in>zobj_refs' (fst x). ex_nonz_cap_to' r s\<rbrace>, -"
  unfolding lookupCapAndSlot_def
  apply (rule hoare_pre)
   apply (wp | simp add: split_def)+
  done

lemma lcs_cte_at' [wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupCapAndSlot t xs \<lbrace>\<lambda>rv s. cte_at' (snd rv) s\<rbrace>,-"
  unfolding lookupCapAndSlot_def
  apply (rule hoare_pre)
   apply (wp|simp)+
  done

lemma lec_ex_cap_to' [wp]:
  "\<lbrace>invs'\<rbrace>
  lookupExtraCaps t xa mi
  \<lbrace>\<lambda>rv s. (\<forall>cap \<in> set rv. \<forall>r\<in>cte_refs' (fst cap) (irq_node' s). ex_cte_cap_to' r s)\<rbrace>, -"
  unfolding lookupExtraCaps_def
  apply (cases "msgExtraCaps mi = 0")
   apply simp
   apply (wp mapME_set | simp)+
  done

lemma lec_ex_nonz_cap_to' [wp]:
  "\<lbrace>invs'\<rbrace>
  lookupExtraCaps t xa mi
  \<lbrace>\<lambda>rv s. (\<forall>cap \<in> set rv. \<forall>r\<in>zobj_refs' (fst cap). ex_nonz_cap_to' r s)\<rbrace>, -"
  unfolding lookupExtraCaps_def
  apply (cases "msgExtraCaps mi = 0")
   apply simp
   apply (wp mapME_set | simp)+
  done

(* FIXME: move *)
lemma getSlotCap_eq [wp]:
  "\<lbrace>\<top>\<rbrace> getSlotCap slot
  \<lbrace>\<lambda>cap. cte_wp_at' ((=) cap \<circ> cteCap) slot\<rbrace>"
  by (wpsimp wp: getCTE_wp' simp: getSlotCap_def cte_wp_at_ctes_of)

lemma lcs_eq [wp]:
  "\<lbrace>\<top>\<rbrace> lookupCapAndSlot t cptr \<lbrace>\<lambda>rv. cte_wp_at' ((=) (fst rv) o cteCap) (snd rv)\<rbrace>,-"
  by (wpsimp simp: lookupCapAndSlot_def)

lemma lec_dimished'[wp]:
  "\<lbrace>\<top>\<rbrace> lookupExtraCaps t buffer info
   \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s)\<rbrace>,-"
  by (wpsimp wp: mapME_set simp: lookupExtraCaps_def)

lemma lookupExtras_real_ctes[wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupExtraCaps t xs info \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. real_cte_at' (snd x) s\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def Let_def split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply (wp mapME_set)
      apply (simp add: lookupCapAndSlot_def split_def)
      apply (wp case_options_weak_wp mapM_wp' lsft_real_cte | simp)+
  done

lemma lookupExtras_ctes[wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupExtraCaps t xs info \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_at' (snd x) s\<rbrace>,-"
  apply (rule hoare_strengthen_postE_R)
   apply (rule lookupExtras_real_ctes)
  apply (simp add: real_cte_at')
  done

lemma lsft_ex_cte_cap_to':
  "\<lbrace>invs' and K (\<forall>cap. isCNodeCap cap \<longrightarrow> P cap)\<rbrace>
     lookupSlotForThread t cref
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' P rv s\<rbrace>,-"
  apply (simp add: lookupSlotForThread_def split_def)
  apply (wp rab_cte_cap_to' getSlotCap_cap_to2 | simp)+
  done

lemma lec_caps_to'[wp]:
  "\<lbrace>invs' and K (\<forall>cap. isCNodeCap cap \<longrightarrow> P cap)\<rbrace>
     lookupExtraCaps t buffer info
   \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. ex_cte_cap_wp_to' P (snd x) s)\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp mapME_set)
      apply (simp add: lookupCapAndSlot_def split_def)
      apply (wp lsft_ex_cte_cap_to' mapM_wp'
                    | simp | wpc)+
  done

lemma getSlotCap_badge_derived[wp]:
  "\<lbrace>\<top>\<rbrace> getSlotCap p \<lbrace>\<lambda>cap. cte_wp_at' (badge_derived' cap \<circ> cteCap) p\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma lec_derived'[wp]:
  "\<lbrace>invs'\<rbrace>
     lookupExtraCaps t buffer info
   \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. cte_wp_at' (badge_derived' (fst x) o cteCap) (snd x) s)\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp mapME_set)
      apply (simp add: lookupCapAndSlot_def split_def)
      apply (wp | simp)+
  done

lemma get_mrs_length_rv[wp]:
  "\<lbrace>\<lambda>s. \<forall>n. n \<le> msg_max_length \<longrightarrow> P n\<rbrace> get_mrs thread buf mi \<lbrace>\<lambda>rv s. P (length rv)\<rbrace>"
  supply if_split[split del]
  apply (simp add: get_mrs_def)
  apply (wp mapM_length | wpc | simp del: upt.simps)+
  apply (clarsimp simp: msgRegisters_unfold msg_max_length_def)
  done

lemma st_tcb_at_idle_thread':
  "\<lbrakk> st_tcb_at' P (ksIdleThread s) s; valid_idle' s \<rbrakk>
        \<Longrightarrow> P IdleThreadState"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)

crunch replyFromKernel
  for tcb_at'[wp]: "tcb_at' t"

(* FIXME: move *)
lemma rct_sch_act_simple[simp]:
  "ksSchedulerAction s = ResumeCurrentThread \<Longrightarrow> sch_act_simple s"
  by (simp add: sch_act_simple_def)

(* FIXME: move *)
lemma rct_sch_act_sane[simp]:
  "ksSchedulerAction s = ResumeCurrentThread \<Longrightarrow> sch_act_sane s"
  by (simp add: sch_act_sane_def)

lemma lookupCapAndSlot_real_cte_at'[wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupCapAndSlot thread ptr \<lbrace>\<lambda>rv. real_cte_at' (snd rv)\<rbrace>, -"
  apply (simp add: lookupCapAndSlot_def lookupSlotForThread_def)
  apply (wp resolveAddressBits_real_cte_at' | simp add: split_def)+
  done

lemmas set_thread_state_active_valid_sched =
  set_thread_state_runnable_valid_sched[simplified runnable_eq_active]

crunch reply_from_kernel
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

crunch reply_from_kernel
  for valid_objs[wp]: valid_objs
  (simp: crunch_simps wp: crunch_wps)

crunch replyFromKernel
  for valid_objs'[wp]: valid_objs'
  (simp: crunch_simps wp: crunch_wps)

(* Note: the preconditions on the abstract side are based on those of performInvocation_corres. *)
lemma handleInvocation_corres:
  "call \<longrightarrow> blocking \<Longrightarrow>
   cptr = to_bl cptr' \<Longrightarrow>
   corres (dc \<oplus> dc)
          (einvs and valid_machine_time and schact_is_rct and ct_active and ct_released
           and (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and ct_not_in_release_q
           and cur_sc_active and current_time_bounded and consumed_time_bounded
           and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
           and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s))
          invs'
          (handle_invocation call blocking can_donate first_phase cptr)
          (handleInvocation call blocking can_donate first_phase cptr')"
  supply opt_mapE[elim!]
  apply add_cur_tcb'
  apply add_ct_not_inQ
  apply add_valid_idle'
  apply add_sym_refs
  apply (rule_tac Q'="\<lambda>s'. bound_sc_tcb_at' bound (ksCurThread s') s'" in corres_cross_add_guard)
   apply (fastforce intro: ct_released_cross_weak)
  apply (simp add: handle_invocation_def handleInvocation_def liftE_bindE)
  apply (rule corres_stateAssertE_add_assertion[rotated])
   apply (clarsimp simp: ct_not_inQ_asrt_def)
  apply (rule corres_stateAssertE_add_assertion[rotated])
   apply (clarsimp simp: valid_idle'_asrt_def)
  apply (rule corres_stateAssertE_add_assertion[rotated])
   apply (clarsimp simp: cur_tcb'_asrt_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule corres_split [OF getMessageInfo_corres])
        apply (rule syscall_corres)
                apply (rule hinv_corres_assist, simp)
               apply (rule corres_when[OF _ handleFault_corres]; simp)
              apply (simp only: split_def)
              apply (rule corres_split[OF getMRs_corres])
                 apply simp
                apply (rule decodeInvocation_corres; simp)
                 apply (fastforce simp: list_all2_map2 list_all2_map1 elim: list_all2_mono)
                apply (fastforce simp: list_all2_map2 list_all2_map1 elim: list_all2_mono)
               apply simp
               apply (wpsimp wp: hoare_case_option_wp)
              apply (drule sym[OF conjunct1], simp, wp)
             apply (clarsimp simp: when_def)
             apply (rule replyFromKernel_corres)
            apply (rule corres_split [OF setThreadState_corres], simp)
              apply (rule corres_splitEE)
                 apply (rule performInvocation_corres; simp)
                apply simp
                apply (rule corres_split [OF getThreadState_corres])
                  apply (rename_tac state state')
                  apply (case_tac state, simp_all)[1]
                  apply (fold dc_def)[1]
                  apply (rule corres_split [OF _ setThreadState_corres])
                     apply simp
                     apply (rule corres_when [OF refl replyFromKernel_corres])
                    apply simp
                   apply (clarsimp simp: pred_conj_def, strengthen valid_objs_valid_tcbs)
                   apply wpsimp
                  apply (clarsimp simp: pred_conj_def, strengthen valid_objs'_valid_tcbs')
                  apply wpsimp+
               apply (strengthen invs_valid_objs invs_psp_aligned invs_distinct)
               apply (clarsimp cong: conj_cong)
               apply (wpsimp wp: hoare_drop_imp)
              apply (rule_tac Q'="tcb_at' thread and invs'" in hoare_post_impE_R_dc)
               apply wpsimp
              apply (clarsimp simp: invs'_def)
             apply simp
             apply (rule_tac Q'="\<lambda>rv. einvs and valid_machine_time and schact_is_rct
                                 and valid_invocation rve
                                 and (\<lambda>s. thread = cur_thread s)
                                 and st_tcb_at active thread
                                 and ct_not_in_release_q and ct_released
                                 and cur_sc_active and current_time_bounded
                                 and consumed_time_bounded
                                 and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
                                 and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s)"
                        in hoare_post_imp)
              apply (clarsimp simp: simple_from_active ct_in_state_def schact_is_rct_def
                                    current_time_bounded_def
                             elim!: st_tcb_weakenE)
             apply (wp sts_st_tcb_at' set_thread_state_simple_sched_action sts_sym_refs'
                       set_thread_state_active_valid_sched set_thread_state_schact_is_rct_strong)
            apply (rule_tac Q'="\<lambda>_. invs' and (\<lambda>s. sym_refs (state_refs_of' s))
                                   and ct_not_inQ and valid_invocation' rve'
                                   and (\<lambda>s. thread = ksCurThread s)
                                   and st_tcb_at' active' thread
                                   and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                                   and (\<lambda>s. bound_sc_tcb_at' bound (ksCurThread s) s)"
                   in hoare_post_imp)
             apply (clarsimp simp: ct_in_state'_def)
            apply ((wpsimp wp: sts_sym_refs' setThreadState_nonqueued_state_update setThreadState_st_tcb
                               setThreadState_rct setThreadState_ct_not_inQ sts_bound_sc_tcb_at'
                    | wps)+)[1]
           apply clarsimp
           apply (wp | simp add: split_def liftE_bindE[symmetric]
                              ct_in_state'_def ball_conj_distrib
                     | rule hoare_vcg_conj_elimE)+
          apply (rule hoare_vcg_conj_lift)
           apply (rule hoare_strengthen_post[OF lookup_ipc_buffer_in_user_frame])
           apply meson
          apply (wp lookup_ipc_buffer_in_user_frame
                 | simp add: split_def liftE_bindE[symmetric]
                             ball_conj_distrib)+
   apply (clarsimp simp: msg_max_length_def word_bits_def)
   apply (frule schact_is_rct_sane)
   apply (frule invs_valid_objs)
   apply (frule valid_objs_valid_tcbs)
   apply (clarsimp simp: invs_def cur_tcb_def valid_state_def current_time_bounded_def
                         valid_sched_def valid_pspace_def ct_in_state_def simple_from_active)
   apply (frule valid_release_q_distinct)
   apply (erule st_tcb_ex_cap, clarsimp+)
   apply (case_tac st; clarsimp)
  apply (clarsimp cong: conj_cong)
  apply (frule curthread_relation)
  apply (prop_tac "ct_schedulable s")
   apply (clarsimp simp: schedulable_def2 ct_in_state_def runnable_eq_active)
  apply (clarsimp simp: invs'_def valid_pspace'_def cur_tcb'_def)
  apply (frule valid_objs'_valid_tcbs')
  apply (frule ct_active_cross, fastforce, fastforce, simp)
  apply (clarsimp simp: ct_in_state'_def cong: conj_cong)
  apply (frule pred_tcb'_weakenE [where P=active' and P'=simple'], clarsimp)
  apply (frule(1) st_tcb_ex_cap'', fastforce)
  apply (clarsimp simp: valid_pspace'_def schact_is_rct_def)
  apply (frule state_relation_sched_act_relation, simp)
  apply (subgoal_tac "schedulable' (ksCurThread s') s'")
   apply (clarsimp simp: schedulable'_def pred_map_conj[simplified pred_conj_def])
   apply (frule active'_st_tcb_at_state_refs_ofD')
   apply (clarsimp simp: pred_tcb_at'_def)
  apply (force intro!: schedulable_schedulable'_eq[THEN iffD1] schedulable_imp_tcb_at)
  done

lemma ts_Restart_case_helper':
  "(case ts of Structures_H.Restart \<Rightarrow> A | _ \<Rightarrow> B) = (if ts = Structures_H.Restart then A else B)"
  by (cases ts, simp_all)

lemma gts_imp':
  "\<lbrace>Q\<rbrace> getThreadState t \<lbrace>R\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. st_tcb_at' P t s \<longrightarrow> Q s\<rbrace> getThreadState t \<lbrace>\<lambda>rv s. P rv \<longrightarrow> R rv s\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply (erule hoare_vcg_disj_lift[rotated])
  apply (rule hoare_strengthen_post [OF gts_sp'])
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

crunch replyFromKernel
  for st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' P' t s)"
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and sch_act_simple[wp]: sch_act_simple
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  (rule: sch_act_simple_lift simp: crunch_simps wp: crunch_wps)

lemma rfk_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s p)\<rbrace> replyFromKernel t x1 \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  apply (case_tac x1)
  apply (simp add: replyFromKernel_def)
  apply (wp)
  done

lemma hinv_invs'[wp]:
  "\<lbrace>invs' and cur_tcb'
    and (\<lambda>s. schedulable' (ksCurThread s) s)
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   handleInvocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: handleInvocation_def split_def
                   ts_Restart_case_helper' ct_not_inQ_asrt_def)
  apply (rule validE_valid)
  apply (intro bindE_wp[OF _ stateAssertE_sp])
  apply (wp syscall_valid' setThreadState_nonqueued_state_update rfk_invs'
            hoare_vcg_all_lift hoare_weak_lift_imp)
         apply simp
         apply (intro conjI impI)
          apply (wp gts_imp' | simp)+
        apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_strengthen_postE_R[rotated])
         apply clarsimp
          apply (fastforce elim!: pred_tcb'_weakenE st_tcb_ex_cap'')
        apply wp+
       apply (rule_tac Q'="\<lambda>_. invs' and cur_tcb'
                               and ct_not_inQ
                               and valid_invocation' rv
                               and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                               and (\<lambda>s. ksCurThread s = thread)
                               and st_tcb_at' active' thread
                               and (\<lambda>s. bound_sc_tcb_at' bound (ksCurThread s) s)"
                    in hoare_post_imp)
        apply (clarsimp simp: ct_in_state'_def)
       apply (wpsimp wp: sts_invs_minor' sts_sym_refs' setThreadState_st_tcb setThreadState_rct
                         setThreadState_ct_not_inQ hoare_vcg_imp_lift'
              | wps)+
  by (fastforce simp: ct_in_state'_def simple_sane_strg sch_act_simple_def pred_map_simps
                      obj_at_simps pred_tcb_at'_def st_tcb_at'_def schedulable'_def
                      opt_pred_def opt_map_def runnable_eq_active' cur_tcb'_def active_sc_tcb_at'_def
               intro: st_tcb_ex_cap''[where P=runnable'] split: option.splits)

(* NOTE: This is a good candidate for corressimp at some point. For now there are some missing
         lemmas regarding corresK and liftM. *)
lemma getCapReg_corres:
  "corres (\<lambda>x y. x = to_bl y) (ct_active and pspace_aligned and pspace_distinct) ct_active'
          (get_cap_reg cap_register) (getCapReg RISCV64_H.capRegister)"
  apply (simp add: get_cap_reg_def getCapReg_def cap_register_def capRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres], simp)
      apply (rule corres_rel_imp)
       apply (rule asUser_getRegister_corres)
      apply (wpsimp simp: ct_in_state_def ct_in_state'_def)+
  done

lemma handleSend_corres:
  "corres (dc \<oplus> dc)
          (einvs and valid_machine_time and schact_is_rct and ct_active
           and ct_released and (\<lambda>s. active_sc_tcb_at (cur_thread s) s)
           and ct_not_in_release_q and cur_sc_active and current_time_bounded
           and  consumed_time_bounded and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
           and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s))
          (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_active')
          (handle_send blocking) (handleSend blocking)"
  apply add_cur_tcb'
  apply (simp add: handle_send_def handleSend_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_liftEE[OF getCapReg_corres])
      apply (simp, rule handleInvocation_corres; simp)
     apply (wpsimp simp: getCapReg_def)+
   apply (fastforce simp: cur_tcb'_def)+
  done

lemma hs_invs'[wp]:
  "\<lbrace>invs' and cur_tcb' and (\<lambda>s. schedulable' (ksCurThread s) s)
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   handleSend blocking
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: handleSend_def getCapReg_def)
  by wpsimp

lemma tcb_at_cte_at_map:
  "\<lbrakk> tcb_at' t s; offs \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> cte_at' (cte_map (t, offs)) s"
  apply (clarsimp simp: obj_at'_def objBits_simps)
  apply (drule tcb_cases_related)
  apply (auto elim: cte_wp_at_tcbI')
  done

lemma getCapReg_corres_gen:
  "corres (\<lambda>x y. x = to_bl y) (cur_tcb  and pspace_aligned and pspace_distinct) \<top>
          (get_cap_reg rg) (getCapReg rg)"
  apply (simp add: get_cap_reg_def getCapReg_def cap_register_def capRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres], simp)
      apply (rule corres_rel_imp)
       apply (rule asUser_getRegister_corres)
      apply (wpsimp simp: cur_tcb_def cur_tcb'_def)+
  done

lemma lookupReply_corres:
  "corres (fr \<oplus> cap_relation)
     (cur_tcb and valid_objs and pspace_aligned and pspace_distinct)
     (cur_tcb' and valid_objs' and pspace_aligned' and pspace_distinct')
     lookup_reply lookupReply"
  unfolding lookup_reply_def lookupReply_def withoutFailure_def
  apply simp
  apply (rule corres_rel_imp)
   apply (rule corres_guard_imp)
     apply (rule corres_split_liftEE[OF getCapReg_corres_gen])
       apply (rule corres_split_liftEE[OF getCurThread_corres])
         apply simp
         apply (rule corres_splitEE[OF corres_cap_fault[OF lookupCap_corres]])
           apply (rename_tac cref cref' ct ct' cap cap')
           apply (rule corres_if2)
             apply (case_tac cap; case_tac cap'; clarsimp simp: is_reply_cap_def isReplyCap_def)
            apply (rule corres_returnOk[where r=cap_relation])
            apply simp
           apply (simp add: lookup_failure_map_def)
          apply wpsimp+
     apply (wpsimp simp: getCapReg_def)
    apply (clarsimp simp: cur_tcb_def, simp)
   apply (clarsimp simp: cur_tcb'_def)
  apply assumption
  done

lemma lookup_reply_valid [wp]:
  "\<lbrace> valid_objs \<rbrace> lookup_reply \<lbrace> valid_cap \<rbrace>, -"
  unfolding lookup_reply_def get_cap_reg_def
  apply (wpsimp wp: get_cap_wp hoare_vcg_imp_liftE_R)
       apply (rule hoare_FalseE_R)
      apply wpsimp+
  done

lemma lookup_reply_is_reply_cap [wp]:
  "\<lbrace> valid_objs \<rbrace> lookup_reply \<lbrace>\<lambda>rv s. is_reply_cap rv \<rbrace>, -"
  unfolding lookup_reply_def lookup_cap_def
  by (wpsimp wp: get_cap_wp)

crunch lookupReply
  for inv[wp]: "P"
  (simp: crunch_simps wp: crunch_wps)

crunch lookup_reply
  for valid_cap[wp]: "valid_cap c"
  and cte_wp_at[wp]: "\<lambda>s. Q (cte_wp_at P p s)"

lemma lookupReply_valid [wp]:
  "\<lbrace> valid_objs' \<rbrace> lookupReply \<lbrace> valid_cap' \<rbrace>, -"
  unfolding lookupReply_def getCapReg_def
  apply (wpsimp wp: get_cap_wp hoare_vcg_imp_liftE_R)
       apply (rule hoare_FalseE_R)
      apply wpsimp+
  done

lemma getBoundNotification_corres:
  "corres (=) (ntfn_at nptr) (ntfn_at' nptr)
          (get_ntfn_obj_ref ntfn_bound_tcb nptr) (liftM ntfnBoundTCB (getNotification nptr))"
  apply (simp add: get_sk_obj_ref_def)
  apply (rule corres_bind_return2)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getNotification_corres])
      apply (simp add: ntfn_relation_def)
     apply wpsimp+
  done

lemma handleRecv_isBlocking_corres':
   "corres dc (einvs and ct_in_state active and current_time_bounded
               and scheduler_act_sane and ct_not_queued and ct_not_in_release_q
               and (\<lambda>s. ex_nonz_cap_to (cur_thread s) s))
              (invs' and ct_in_state' simple'
                     and sch_act_sane
                     and (\<lambda>s. ex_nonz_cap_to' (ksCurThread s) s))
                    (handle_recv isBlocking canReply) (handleRecv isBlocking canReply)"
  (is "corres dc (?pre1) (?pre2) (handle_recv _ _) (handleRecv _ _)")
  unfolding handle_recv_def handleRecv_def Let_def
  apply add_cur_tcb'
  apply (rule_tac Q'="ct_active'" in corres_cross_add_guard)
   apply (fastforce elim!: ct_active_cross dest: invs_psp_aligned invs_distinct)
  apply (simp add: cap_register_def capRegister_def liftM_bind
             cong: if_cong cap.case_cong capability.case_cong split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule corres_split_eqr[OF asUser_getRegister_corres])
        apply (rule corres_split_catch)
           apply (rule corres_splitEE[OF corres_cap_fault[OF lookupCap_corres]])
             apply (rule_tac P="?pre1 and tcb_at thread
                                and (\<lambda>s. (cur_thread s) = thread  )
                                and valid_cap rv"
                        and P'="?pre2 and cur_tcb' and tcb_at' thread and valid_cap' epCap" in corres_inst)
             apply (clarsimp split: cap_relation_split_asm arch_cap.split_asm split del: if_split
                              simp: lookup_failure_map_def whenE_def)
              apply (rename_tac rights)
              apply (case_tac "AllowRead \<in> rights \<and> canReply")
               apply clarsimp
               apply (rule corres_guard_imp)
                 apply (rule corres_splitEE[OF lookupReply_corres])
                   apply (rule_tac Q="\<lambda>_. is_reply_cap reply_cap" in corres_inst_add)
                   apply (rule corres_gen_asm)
                   apply simp
                   apply (rule corres_guard_imp)
                     apply (rule receiveIPC_corres)
                        apply simp
                       apply (clarsimp simp: cap_relation_def)
                      apply simp+
                  apply (wpsimp wp: typ_at_lifts)+
                apply (clarsimp simp: ct_in_state_def invs_def valid_state_def valid_pspace_def)
               apply (simp add: invs'_def valid_pspace'_def)
              apply (clarsimp simp: lookup_failure_map_def)
              apply (rule corres_guard_imp)
                apply (rule receiveIPC_corres)
                   apply ((clarsimp simp: cap_relation_def ct_in_state_def)+)[6]
             apply (rename_tac rights)
             apply (simp add: bool.case_eq_if if_swap[where P="AllowRead \<in> x" for x, symmetric] split del: if_split)
             apply (case_tac "AllowRead \<in> rights")
              apply clarsimp
              apply (rule stronger_corres_guard_imp)
                apply (rule corres_split_liftEE[OF getBoundNotification_corres])
                  apply (case_tac "rv = Some thread \<or> rv = None")
                   apply simp
                   apply (rule receiveSignal_corres)
                    apply simp
                   apply (clarsimp simp: cap_relation_def)
                  apply (clarsimp simp: lookup_failure_map_def)
                 apply (wpsimp wp: get_sk_obj_ref_wp getNotification_wp)+
               apply (clarsimp simp: valid_cap_def valid_sched_def valid_sched_action_def
                                     current_time_bounded_def ct_in_state_def)
              apply (clarsimp simp: valid_cap_def valid_cap'_def dest!: state_relationD)
             apply (clarsimp simp: lookup_failure_map_def)
            apply wpsimp+
          apply (rule handleFault_corres, clarsimp)
         apply (wpsimp wp: get_sk_obj_ref_wp)
         apply (rule_tac Q'="\<lambda>_. ?pre1 and (\<lambda>s. cur_thread s = thread)
                                 and K (valid_fault (ExceptionTypes_A.fault.CapFault x True
                                        (ExceptionTypes_A.lookup_failure.MissingCapability 0)))"
                     and E=E and E'=E for E
                in hoare_strengthen_postE[rotated])
           apply (fastforce dest: valid_sched_valid_release_q
                            simp: valid_sched_valid_sched_action valid_sched_active_scs_valid
                                  ct_in_state_def)
          apply simp
         apply (wpsimp wp: resolve_address_bits_valid_fault2 simp: lookup_cap_def lookup_cap_and_slot_def lookup_slot_for_thread_def)
        apply wp
         apply (case_tac epCap; simp split del: if_split)
                      apply wpsimp
                     apply wpsimp
                    apply (rename_tac readright; case_tac readright; simp)
                     apply wp
                       apply simp
                       apply wp
                      apply (wp getNotification_wp)
                     apply clarsimp
                    apply (wpsimp wp: hoare_vcg_imp_lift' simp: valid_fault_def)+
   apply (frule valid_sched_valid_release_q)
   apply (frule valid_release_q_distinct)
   apply (clarsimp simp: invs_def cur_tcb_def valid_state_def valid_pspace_def ct_in_state_def
                         valid_sched_valid_sched_action valid_sched_active_scs_valid
                  dest!: get_tcb_SomeD)
   apply (fastforce elim: objs_valid_tcb_ctable)
  apply (clarsimp simp: invs'_def cur_tcb'_def valid_pspace'_def sch_act_sane_def ct_in_state'_def)
  done

lemma handleRecv_isBlocking_corres:
  "corres dc (einvs and ct_active and scheduler_act_sane and current_time_bounded
              and ct_not_queued and ct_not_in_release_q)
             (invs' and ct_active' and sch_act_sane)
            (handle_recv isBlocking canReply) (handleRecv isBlocking canReply)"
  apply (rule corres_guard_imp)
    apply (rule handleRecv_isBlocking_corres')
   apply (clarsimp simp: ct_in_state_def)
   apply (fastforce elim!: st_tcb_weakenE st_tcb_ex_cap)
  apply (clarsimp simp: ct_in_state'_def invs'_def)
  apply (frule(1) st_tcb_ex_cap'')
  apply (auto elim: pred_tcb'_weakenE)
  done

lemma lookupCap_refs[wp]:
  "\<lbrace>invs'\<rbrace> lookupCap t ref \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s\<rbrace>,-"
  by (simp add: lookupCap_def split_def | wp | simp add: o_def)+

lemma hw_invs'[wp]:
  "\<lbrace>invs' and ct_in_state' active'\<rbrace>
   handleRecv isBlocking canReply
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: handleRecv_def cong: if_cong split del: if_split)
  apply (rule bind_wp[OF _ getCurThread_sp])
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (rule catch_wp; (solves wpsimp)?)
  apply (rule_tac P=P and
                  Q'="\<lambda>rv. P and (\<lambda>s. \<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s)
                          and (\<lambda>s. ex_nonz_cap_to' (ksCurThread s) s)
                          and (\<lambda>s. st_tcb_at' active' (ksCurThread s) s)"
         for P in bindE_wp_fwd)
   apply wpsimp
   apply (fastforce simp: ct_in_state'_def)
  apply (rename_tac epCap)
  apply (case_tac epCap; clarsimp split del: if_split; (wpsimp; fail)?)
   apply (rename_tac readright; case_tac readright; (wp getNotification_wp |simp)+)
   apply (clarsimp simp: obj_at_simps isNotificationCap_def)
  by (wpsimp simp: lookupReply_def getCapReg_def
      | wp (once) hoare_drop_imps)+
     (clarsimp simp: obj_at_simps ct_in_state'_def pred_tcb_at'_def)

lemma setSchedulerAction_obj_at'[wp]:
  "\<lbrace>obj_at' P p\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  unfolding setSchedulerAction_def
  by (wp, clarsimp elim!: obj_at'_pspaceI)

lemma live_sc'_ex_cap:
  "if_live_then_nonz_cap' s \<Longrightarrow>
   \<forall>ko. ko_at' ko scPtr s \<longrightarrow> live_sc' ko \<longrightarrow> ex_nonz_cap_to' scPtr s"
  by (clarsimp simp: obj_at'_real_def ko_wp_at'_def
              elim!: if_live_then_nonz_capE')

lemma valid_sc_strengthen:
  "valid_objs' s \<Longrightarrow>
   \<forall>ko. ko_at' ko scPtr s \<longrightarrow>
                valid_sched_context' ko s \<and> valid_sched_context_size' ko"
  by (clarsimp elim!: sc_ko_at_valid_objs_valid_sc')

lemma endTimeslice_corres: (* called when ct_schedulable *)
  "corres dc
     (invs and valid_list and valid_sched_action and active_scs_valid and valid_release_q
      and valid_ready_qs and sorted_ipc_queues and cur_sc_active and ct_active
      and current_time_bounded and ct_not_queued and ct_not_in_release_q
      and cur_sc_tcb_are_bound and scheduler_act_sane and ready_or_release)
     invs'
     (end_timeslice canTimeout) (endTimeslice canTimeout)"
  (is "corres _ ?pre ?pre' _ _")
  unfolding end_timeslice_def endTimeslice_def isValidTimeoutHandler_def bind_assoc
  apply (rule_tac Q'="\<lambda>s. sc_at' (ksCurSc s) s" in corres_cross_add_guard)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                  dest!: state_relationD)
   apply (erule (2) sc_at_cross)
   apply (fastforce simp: cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def is_sc_obj
                    dest: valid_sched_context_size_objsI)
  apply (rule_tac Q'="\<lambda>s. is_active_sc' (ksCurSc s) s" in corres_cross_add_guard)
   apply (prop_tac "cur_sc s = ksCurSc s'", clarsimp dest!: state_relationD)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (fastforce dest: valid_sched_context_size_objsI elim!: is_active_sc'2_cross
                    simp: invs_def valid_state_def valid_pspace_def cur_sc_tcb_def sc_tcb_sc_at_def
                          obj_at_def is_sc_obj)
  apply add_cur_tcb'
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule_tac P="?pre and (\<lambda>s. ct = cur_thread s)"
                 and P'="?pre' and (\<lambda>s. is_active_sc' (ksCurSc s) s) and cur_tcb'
                         and (\<lambda>s. sc_at' (ksCurSc s) s) and (\<lambda>s. ct = ksCurThread s)" in corres_inst)
      apply (rule corres_guard_imp)
        apply (rule corres_split_eqr[OF getCurSc_corres])
          apply (rule_tac P="?pre and (\<lambda>s. ct = cur_thread s) and (\<lambda>s. sc_ptr = cur_sc s)"
                     and P'="?pre' and (\<lambda>s. is_active_sc' (ksCurSc s) s) and cur_tcb'
                             and (\<lambda>s. sc_at' (ksCurSc s) s) and (\<lambda>s. ct = ksCurThread s) and (\<lambda>s. sc_ptr = ksCurSc s)" in corres_inst)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF get_sc_corres])
              apply (rule corres_split_eqr[OF refillReady_corres], simp)
                apply (rule corres_split_eqr[OF getRefillSufficient_corres], simp)
                  apply (rule_tac P="?pre and (\<lambda>s. ct = cur_thread s) and (\<lambda>s. sc_ptr = cur_sc s)
                                     and (\<lambda>s. ready = is_refill_ready sc_ptr s)
                                     and (\<lambda>s. sufficient = is_refill_sufficient 0 sc_ptr s)"
                             and P'="?pre' and (\<lambda>s. is_active_sc' (ksCurSc s) s) and cur_tcb'
                                     and (\<lambda>s. sc_at' (ksCurSc s) s) and (\<lambda>s. sc_ptr = ksCurSc s) and (\<lambda>s. ct = ksCurThread s)" in corres_inst)
                  apply (simp split del: if_split)
                  apply (rule corres_guard_imp)
                    apply (rule corres_split[OF getObject_TCB_corres])
                      apply (rename_tac tcb tcb')
                      apply (rule_tac F="cap_relation (tcb_timeout_handler tcb) (cteCap (tcbTimeoutHandler tcb'))"
                             in corres_req)
                       apply (clarsimp simp: tcb_relation_def)
                      apply (rule_tac F="is_ep_cap (tcb_timeout_handler tcb)
                                         = isEndpointCap (cteCap (tcbTimeoutHandler tcb'))"
                             in corres_req)
                       apply (case_tac "tcb_timeout_handler tcb";
                              case_tac "cteCap (tcbTimeoutHandler tcb')";
                              clarsimp simp: cap_relation_def isEndpointCap_def)
                      apply (rule corres_symb_exec_r)
                         apply (rule_tac P="?pre and (\<lambda>s. ct = cur_thread s) and (\<lambda>s. sc_ptr = cur_sc s)
                                            and (\<lambda>s. ready = is_refill_ready sc_ptr s) and ko_at (TCB tcb) ct
                                            and (\<lambda>s. sufficient = is_refill_sufficient 0 sc_ptr s)"
                                    and P'="?pre' and cur_tcb' and (\<lambda>s. ct = ksCurThread s)
                                            and (\<lambda>s. sc_at' (ksCurSc s) s) and (\<lambda>s. is_active_sc' (ksCurSc s) s) and (\<lambda>s. sc_ptr = ksCurSc s) and
                                            K (valid = isEndpointCap (cteCap (tcbTimeoutHandler tcb')))"
                                in corres_inst)
                         apply (rule corres_gen_asm2')
                         apply (rule corres_guard_imp)
                           apply (rule corres_if2)
                             apply clarsimp
                            apply simp
                            apply (rule handleTimeout_corres)
                            apply clarsimp
                            apply (clarsimp simp: sc_relation_def)
                           apply (rule corres_if2, simp)
                            apply (rule tcbSchedAppend_corres, simp)
                           apply (rule postpone_corres)
                          apply (clarsimp cong: conj_cong imp_cong)
                          apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_def
                                                valid_fault_def valid_fault_handler_def)
                          apply (rule conjI impI; clarsimp)
                           apply (clarsimp simp: ct_in_state_def cte_wp_at_def cur_tcb_def)
                           apply (clarsimp simp: get_cap_caps_of_state obj_at_def is_tcb
                                                 caps_of_state_tcb_index_trans[OF get_tcb_rev]
                                                 tcb_cnode_map_def)
                          apply (frule (1) cur_sc_tcb_are_bound_sym)
                          apply (clarsimp simp: vs_all_heap_simps sc_tcb_sc_at_def obj_at_def
                                                ct_in_state_def st_tcb_at_def runnable_eq_active
                                                is_tcb_def)
                          apply fastforce
                         apply (clarsimp simp: invs'_def valid_pspace'_def cur_tcb'_def)
                        apply (wpsimp wp: getTCB_wp)+
                   apply (frule invs_psp_aligned, frule invs_distinct)
                   apply (clarsimp dest!: invs_cur simp: cur_tcb_def)
                  apply (clarsimp simp: cur_tcb'_def isEndpointCap_def)
                 apply (wpsimp wp: refillReady_wp)+
           apply (clarsimp dest!: valid_sched_active_scs_valid
                            simp: invs_def cur_sc_tcb_def valid_state_def valid_pspace_def
                                  sc_tcb_sc_at_def obj_at_def is_sc_obj opt_map_red vs_all_heap_simps
                                  sc_refills_sc_at_def opt_pred_def)
           apply (drule (1) valid_sched_context_size_objsI, clarsimp)
           apply (drule active_scs_validE[rotated])
            apply (fastforce simp: vs_all_heap_simps)
           apply (clarsimp simp: vs_all_heap_simps rr_valid_refills_def valid_refills_def split: if_split_asm)
          apply (fastforce simp: invs'_def  active_sc_at'_def is_active_sc'_def in_omonad obj_at'_def
                          elim!: valid_objs'_valid_refills')
         apply wpsimp+
  done

crunch end_timeslice, refill_reset_rr
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and valid_list[wp]: valid_list
  and cur_sc_active[wp]: cur_sc_active
  (wp: crunch_wps set_simple_ko_valid_tcbs cur_sc_active_lift
   ignore: set_object)

crunch refill_reset_rr
  for cte_wp_at[wp]: "cte_wp_at P c"

lemma handle_timeout_valid_sched_action:
  "\<lbrace>\<lambda>s. valid_sched_action s \<and> released_ipc_queues s \<and> scheduler_act_not tptr s
      \<and> active_scs_valid s
      \<and> (is_timeout_fault ex \<and> active_sc_tcb_at tptr s \<or> released_if_bound_sc_tcb_at tptr s)\<rbrace>
   handle_timeout tptr ex
   \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  unfolding handle_timeout_def
  apply (wpsimp wp: send_fault_ipc_valid_sched_action)
  done

lemma end_timeslice_valid_sched_action:
  "\<lbrace>valid_sched_action and released_ipc_queues and active_scs_valid and scheduler_act_sane
    and cur_sc_tcb_are_bound and cur_sc_active and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   end_timeslice canTimeout
   \<lbrace>\<lambda>_. valid_sched_action :: det_state \<Rightarrow> _\<rbrace>"
  unfolding end_timeslice_def
  apply (wpsimp wp: handle_timeout_valid_sched_action postpone_valid_sched_action)
  apply (frule (1) cur_sc_tcb_are_bound_sym)
  apply (intro conjI; clarsimp simp: is_timeout_fault_def del: disjCI)
   apply (rule disjI1)
   apply (fastforce simp: active_sc_tcb_at_def2 tcb_at_kh_simps pred_map_eq_normalise
                   dest!: get_tcb_SomeD)
  apply (clarsimp simp: sc_at_kh_simps pred_map_eq_def[symmetric])
  apply (clarsimp simp: pred_map_simps)
  done

lemma sendFaultIPC_invs':
  "\<lbrace>invs' and valid_idle' and st_tcb_at' active' t
          and (\<lambda>s. canDonate \<longrightarrow> bound_sc_tcb_at' bound t s)
          and ex_nonz_cap_to' t
          and (\<lambda>s. \<exists>n\<in>dom tcb_cte_cases. \<exists>cte. cte_wp_at' (\<lambda>cte. cteCap cte = cap) (t + n) s)\<rbrace>
   sendFaultIPC t cap f canDonate
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: sendFaultIPC_def)
  apply (wp threadSet_invs_trivial threadSet_pred_tcb_no_state
            threadSet_cap_to' threadSet_idle'
           | wpc | simp)+
  apply (intro conjI impI allI; (fastforce simp: inQ_def)?)
   apply (clarsimp simp: invs'_def obj_at'_def)
  apply (fastforce simp: ex_nonz_cap_to'_def cte_wp_at'_def)
  done

lemma handleTimeout_Timeout_invs':
  "\<lbrace>invs' and st_tcb_at' active' tptr\<rbrace>
   handleTimeout tptr (Timeout badge)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: handleTimeout_def)
  apply (wpsimp wp: sendFaultIPC_invs' set_tcb'.getObject_wp' simp: isValidTimeoutHandler_def)
  apply (rule conjI; clarsimp simp: obj_at'_real_def pred_tcb_at'_def)
   apply (drule invs_iflive')
   apply (erule (1) if_live_then_nonz_capD')
   apply (fastforce simp: live_def)
  apply (clarsimp simp: ko_wp_at'_def opt_map_red)
  apply (rule_tac x="4 << cteSizeBits" in bexI)
   apply (clarsimp simp: cte_wp_at_cases')
   apply (drule_tac x="4 << cteSizeBits" in spec)
   apply (clarsimp simp: objBits_simps cteSizeBits_def)
   apply fastforce
  apply (clarsimp simp: tcb_cte_cases_def cteSizeBits_def)
  done

lemma endTimeslice_invs'[wp]:
  "\<lbrace>invs' and ct_active'\<rbrace>
   endTimeslice timeout
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding endTimeslice_def
  apply (wpsimp wp: handleTimeout_Timeout_invs' isValidTimeoutHandler_inv hoare_drop_imp
                    refillReady_wp)
  apply (frule (1) active_ex_cap'[OF _ invs_iflive'])
  apply (clarsimp simp: ct_in_state'_def sch_act_sane_def)
  done

crunch setConsumedTime, updateSchedContext
  for sch_act_sane[wp]: sch_act_sane
  and ct_active'[wp]: ct_active'
  (simp: sch_act_sane_def ct_in_state'_def ignore: setSchedContext)

crunch refillResetRR, refillBudgetCheck
  for ct_active'[wp]: ct_active'
  and sch_act_sane[wp]: sch_act_sane
  and ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' p"
  and typ_at'[wp]: "\<lambda>s. Q (typ_at' P p s)"
  and sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

crunch chargeBudget
  for typ_at'[wp]: "\<lambda>s. Q (typ_at' P p s)"
  (wp: crunch_wps simp: crunch_simps)

end

global_interpretation refillResetRR: typ_at_all_props' "refillResetRR scPtr"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch-split*)

lemma refillResetRR_invs'[wp]:
  "refillResetRR scp \<lbrace>invs'\<rbrace>"
  unfolding refillResetRR_def
  apply (wpsimp wp: updateSchedContext_invs')
  apply (intro conjI; clarsimp elim!: live_sc'_ex_cap[OF invs_iflive'])
  by (fastforce dest!: valid_sc_strengthen[OF invs_valid_objs']
                 simp: valid_sched_context'_def valid_sched_context_size'_def scBits_simps
                       objBits_simps' refillSize_def)

lemmas refill_reset_rr_typ_ats [wp] =
  abs_typ_at_lifts [OF refill_reset_rr_typ_at]

crunch refillResetRR
  for ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"

crunch setConsumedTime, refillResetRR
  for cur_tcb'[wp]: cur_tcb'
  (simp: cur_tcb'_def)

crunch end_timeslice
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: crunch_wps ignore: set_simple_ko tcb_sched_action)

lemma in_correct_ready_q_consumed_time_update[simp]:
  "in_correct_ready_q (consumed_time_update f s) = in_correct_ready_q s"
  by (simp add: in_correct_ready_q_def)

lemma ready_qs_distinct_consumed_time_update[simp]:
  "ready_qs_distinct (consumed_time_update f s) = ready_qs_distinct s"
  by (simp add: ready_qs_distinct_def)

lemma chargeBudget_corres:
  "corres dc
     (invs and valid_list and valid_sched_action and active_scs_valid and valid_release_q
      and valid_ready_qs and released_ipc_queues and cur_sc_active and ready_or_release
      and sorted_ipc_queues
      and current_time_bounded and cur_sc_chargeable and scheduler_act_sane
      and ct_not_queued and ct_not_in_release_q and ct_not_blocked
      and cur_sc_offset_ready 0)
     invs'
     (charge_budget consumed canTimeout) (chargeBudget consumed canTimeout True)"
  (is "corres _ (?pred and _ and cur_sc_offset_ready 0) _ _ _")
  unfolding chargeBudget_def charge_budget_def ifM_def bind_assoc
  apply (rule_tac Q'="\<lambda>s. sc_at' (ksCurSc s) s" in corres_cross_add_guard)
   apply clarsimp
   apply (frule (1) cur_sc_tcb_sc_at_cur_sc[OF invs_valid_objs invs_cur_sc_tcb])
   apply (drule state_relationD, clarsimp)
   apply (erule sc_at_cross; fastforce simp: invs_def valid_state_def valid_pspace_def)
  apply (rule_tac Q'="\<lambda>s. is_active_sc' (ksCurSc s) s" in corres_cross_add_guard)
   apply (fastforce intro: valid_objs_valid_sched_context_size
                     simp: sc_at_pred_n_def obj_at_def is_sc_obj_def state_relation_def vs_all_heap_simps
                    intro: is_active_sc'2_cross)
  apply (rule_tac Q="\<lambda>s. sc_at (cur_sc s) s" in corres_cross_add_abs_guard)
   apply (fastforce intro: cur_sc_tcb_sc_at_cur_sc)
  apply add_cur_tcb'
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurSc_sp])
   apply (corresKsimp corres: getCurSc_corres)
  apply (rule corres_symb_exec_r[rotated, OF getIdleSC_sp]; wpsimp simp: getIdleSC_def)
  apply (rule_tac F="idle_sc_ptr = idleSCPtr" in corres_req)
   apply (clarsimp simp: state_relation_def)
  apply (rule_tac Q="\<lambda>_. ?pred"
              and Q'="\<lambda>_. invs' and cur_tcb'"
               in corres_underlying_split)
     apply (clarsimp simp: when_def split del: if_split)
     apply (rule corres_if_split; (solves corresKsimp)?)
     apply (rule corres_guard_imp)
       apply (rule corres_split_eqr[OF isRoundRobin_corres])
         apply (rule corres_split[OF corres_if2], simp)
             apply (rule refillResetRR_corres)
            apply (rule refillBudgetCheck_corres, simp)
           apply (rule updateSchedContext_no_stack_update_corres)
             apply (fastforce simp: sc_relation_def obj_at'_def obj_at_def is_sc_obj opt_map_red
                                    opt_pred_def
                             dest!: state_relation_sc_relation)
            apply (fastforce simp: sc_relation_def obj_at'_def obj_at_def is_sc_obj opt_map_red
                            dest!: state_relation_sc_replies_relation elim: sc_replies_relation_prevs_list)
           apply (clarsimp simp: objBits_simps)
          apply (wpsimp wp: is_round_robin_wp isRoundRobin_wp)+
      apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
      apply (drule (1) active_scs_validE, clarsimp)
      apply (clarsimp simp: round_robin_def vs_all_heap_simps obj_at_def)
     apply (clarsimp simp: obj_at'_def invs'_def valid_pspace'_def elim!: valid_objs'_valid_refills')
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF setConsumedTime_corres], simp)
        apply (simp add: andM_def whenM_def ifM_def when_def[symmetric] bind_assoc)
        apply (rule corres_split_eqr[OF getCurThread_corres _ gets_sp getCurThread_sp])
        apply (rule corres_guard_imp)
          apply (rule corres_split_eqr[OF getSchedulable_corres _ gets_sp getSchedulable_sp])
          apply (rename_tac sched)
          apply (rule corres_guard_imp)
            apply (rule corres_when2, simp)
            apply (rule corres_split[OF endTimeslice_corres])
              apply (rule corres_split[OF rescheduleRequired_corres])
                apply (rule setReprogramTimer_corres)
               apply wpsimp
              apply wpsimp
             apply (rule hoare_strengthen_post
                              [where Q'="\<lambda>_. invs and active_scs_valid and valid_sched_action
                                            and in_correct_ready_q and ready_or_release
                                            and sorted_ipc_queues and ready_qs_distinct", rotated])
              apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_objs_valid_tcbs
                                    valid_sched_action_def)
             apply (wpsimp wp: end_timeslice_invs end_timeslice_valid_sched_action
                               end_timeslice_sorted_ipc_queues)
            apply (rule hoare_strengthen_post[where Q'="\<lambda>_. invs'", rotated])
             apply (clarsimp simp: invs'_def valid_pspace'_def)
            apply wpsimp
           apply simp+
       apply wpsimp
      apply (rule hoare_strengthen_post
                     [where Q'="\<lambda>_. invs' and cur_tcb'", rotated])
       apply (clarsimp simp: invs'_def valid_pspace'_def valid_objs'_valid_tcbs' cur_tcb'_def
                             schedulable'_def runnable_eq_active' opt_pred_def opt_map_def
                             obj_at'_def pred_tcb_at'_def ct_in_state'_def
                      split: option.splits)
      apply wpsimp
     apply (fastforce simp: schedulable_def2 ct_in_state_def runnable_eq_active current_time_bounded_def
                            invs_def valid_state_def valid_pspace_def cur_tcb_def
                            valid_objs_valid_tcbs state_refs_of_def
                     dest!: cur_sc_chargeable_when_ct_active_sc)
    apply clarsimp
   apply wpsimp
      apply (clarsimp simp: consumed_time_update_arch.state_refs_update sc_consumed_update_eq[symmetric])
      apply ((wpsimp wp: hoare_vcg_conj_lift; (solves wpsimp)?
             | strengthen valid_objs_valid_tcbs | wps)+)[1]
     apply wpsimp
      apply (wpsimp wp: sc_at_typ_at refill_reset_rr_valid_sched_action)
     apply (wpsimp wp: sc_at_typ_at refill_reset_rr_valid_sched_action hoare_vcg_disj_lift
                       refill_budget_check_valid_sched_action_act_not
                       refill_budget_check_active_scs_valid
                        refill_budget_check_valid_release_q
                        refill_budget_check_valid_ready_qs_not_queued)
     apply ((wpsimp wp: refill_budget_check_released_ipc_queues
            | strengthen live_sc'_ex_cap[OF invs_iflive'] valid_sc_strengthen[OF invs_valid_objs'])+)[1]
    apply (wpsimp wp: hoare_vcg_disj_lift)
    apply (wpsimp wp: is_round_robin_wp isRoundRobin_wp)+
   apply (rule conjI; clarsimp)
   apply (prop_tac "sc_scheduler_act_not (cur_sc s) s")
    apply (clarsimp simp: vs_all_heap_simps)
    apply (clarsimp simp: cur_sc_chargeable_def)
    apply (rotate_tac -1)
    apply (drule_tac x=t in spec)
    apply (prop_tac "heap_ref_eq (cur_sc s) t (tcb_scps_of s)")
     apply (clarsimp simp: vs_all_heap_simps)
    apply (simp only: scheduler_act_not_def, rule notI)
    apply (drule (1) valid_sched_action_switch_thread_is_schedulable)
    apply (clarsimp simp: schedulable_def3 vs_all_heap_simps)
   apply (frule ct_not_blocked_cur_sc_not_blocked, clarsimp)
   apply (rule conjI; clarsimp)
    apply (drule (1) active_scs_validE, clarsimp)
    apply (clarsimp simp: vs_all_heap_simps obj_at_def sc_refills_sc_at_def
                          sc_valid_refills_def rr_valid_refills_def)
   apply (clarsimp simp: vs_all_heap_simps)
   apply (clarsimp simp: cur_sc_chargeable_def)
   apply (rotate_tac -1)
   apply (intro conjI; clarsimp?)
    apply (drule_tac x=t in spec)
    apply (prop_tac "heap_ref_eq (cur_sc s) t (tcb_scps_of s)")
     apply (clarsimp simp: vs_all_heap_simps)
    apply (clarsimp simp: valid_release_q_def)
    apply (drule_tac x=t in bspec, simp add: in_queue_2_def)
    apply (fastforce simp: tcb_at_kh_simps[symmetric] pred_tcb_at_def obj_at_def)
   apply (drule_tac x=t in spec)
   apply (prop_tac "heap_ref_eq (cur_sc s) t (tcb_scps_of s)")
    apply (clarsimp simp: vs_all_heap_simps)
   apply (clarsimp simp: valid_ready_qs_def in_ready_q_def)
   apply (drule_tac x=d and y=p in spec2, clarsimp)
   apply (drule_tac x=t in bspec, simp)
   apply clarsimp
   apply (clarsimp simp: tcb_at_kh_simps[symmetric] pred_tcb_at_def obj_at_def)
   apply (drule_tac x=d and y=p in spec2)
   apply fastforce
  apply (wpsimp wp: updateSchedContext_invs')
     apply (wpsimp wp: typ_at_lifts
           | strengthen live_sc'_ex_cap[OF invs_iflive'] valid_sc_strengthen[OF invs_valid_objs'])+
  done

lemma checkBudget_corres: (* called when ct_schedulable or in checkBudgetRestart *)
  "corres (=)
     (einvs and current_time_bounded and cur_sc_offset_ready 0 and cur_sc_chargeable
      and cur_sc_active and ct_not_blocked
      and ct_not_queued and ct_not_in_release_q and scheduler_act_sane)
     invs'
     check_budget checkBudget"
  unfolding check_budget_def checkBudget_def
  apply (rule_tac Q'="\<lambda>s'. active_sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: active_sc_at'_cross_valid_objs simp: state_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurSc_corres])
      apply (rule corres_split_eqr[OF getConsumedTime_corres])
        apply (rule corres_split_eqr[OF getRefillSufficient_corres], simp)
          apply (rule corres_if2, simp)
           apply (rule corres_split_eqr[OF isCurDomainExpired_corres])
             apply simp
            apply wpsimp+
          apply (rule corres_split_eqr[OF getConsumedTime_corres])
            apply (rule corres_split[OF chargeBudget_corres])
              apply simp
             apply (wpsimp wp: hoare_drop_imp)+
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def valid_sched_def)
   apply (rule conjI)
    apply (fastforce intro!: valid_sched_context_size_objsI
                       simp: vs_all_heap_simps is_sc_obj_def)
   apply (drule (1) active_scs_validE[rotated])
   apply (frule valid_refills_nonempty_refills)
   apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps
                  split: if_split_asm)
  apply clarsimp
  done

lemma handleYield_corres:
  "corres dc
     (einvs and ct_active and cur_sc_active and schact_is_rct and scheduler_act_sane
      and current_time_bounded and cur_sc_offset_ready 0
      and ct_not_queued and ct_not_in_release_q)
     invs'
     handle_yield handleYield"
  (is "corres _ ?pre ?pre' _ _")
  supply opt_mapE[elim!]
  apply (rule_tac Q'=ct_active' in corres_cross_add_guard)
   apply (fastforce intro!: ct_active_cross simp: invs_def valid_state_def valid_pspace_def)
  apply (rule_tac Q'="\<lambda>s. sc_at' (ksCurSc s) s" in corres_cross_add_guard)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                  dest!: state_relationD schact_is_rct)
   apply (erule (2) sc_at_cross)
   apply (fastforce simp: cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def is_sc_obj
                    dest: valid_sched_context_size_objsI)
  apply (clarsimp simp: handle_yield_def handleYield_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurSc_corres])
      apply (rule corres_split[OF get_sc_corres])
        apply (erule exE)
        apply (rename_tac cursc sc sc' n)
        apply (rule_tac P="(\<lambda>s. scs_of2 s cursc = Some sc) and ?pre
                            and (\<lambda>s. cur_sc s = cursc)"
                   and P'="?pre' and ko_at' sc' cursc"
               in corres_inst)
        apply (rule_tac Q="\<lambda>rv. (\<lambda>s. scs_of2 s cursc = Some sc) and ?pre
                                and (\<lambda>s. cur_sc s = cursc) and K (sc_refills sc = rv)"
                   and P'="?pre' and ko_at' sc' cursc"
               in corres_symb_exec_l)
           apply (rename_tac refills)
           apply (rule corres_gen_asm')
           apply (rule_tac F="r_amount (hd refills) = rAmount (refillHd sc')" in corres_req)
            apply (clarsimp dest!: invs_valid_objs' invs_valid_objs simp: obj_at_def obj_at'_def
                            split: Structures_A.kernel_object.splits)
            apply (erule (1) valid_objsE', clarsimp simp: valid_obj'_def)
            apply (frule (1) refill_hd_relation2[rotated -1])
             apply (drule (1) active_scs_validE[OF _ valid_sched_active_scs_valid])
             apply (clarsimp simp: valid_refills_def vs_all_heap_simps rr_valid_refills_def split: if_split_asm)
            apply clarsimp
           apply simp
           apply (rule corres_guard_imp)
             apply (rule corres_split[OF chargeBudget_corres])
               apply (rule updateSchedContext_no_stack_update_corres)
                  apply (clarsimp simp: sc_relation_def obj_at_simps is_sc_obj opt_map_red opt_pred_def)
                 apply clarsimp
                apply (fastforce simp: sc_relation_def obj_at_simps is_sc_obj opt_map_red
                                 elim: sc_replies_relation_prevs_list)
               apply (clarsimp simp: objBits_simps)
              apply (rule sc_at_typ_at, wp)
             apply (wpsimp wp: typ_at_lifts)
            apply (clarsimp simp: valid_sched_def opt_map_def obj_at_def is_sc_obj
                           split: option.split_asm Structures_A.kernel_object.split_asm)
            apply (frule (1) valid_sched_context_size_objsI[OF invs_valid_objs], clarsimp)
            apply (frule (1) invs_cur_sc_chargeableE)
            apply fastforce
           apply clarsimp
          apply wpsimp
           apply (fastforce intro: cur_sc_tcb_sc_at_cur_sc)
          apply simp
         apply (wpsimp wp: get_refills_wp)
         apply (clarsimp simp: obj_at_def is_sc_obj)
        apply (wpsimp simp: get_refills_def split: Structures_A.kernel_object.splits)
       apply wpsimp+
   apply (frule invs_valid_objs)
   apply (fastforce simp: obj_at_def is_sc_obj cur_sc_tcb_def sc_tcb_sc_at_def opt_map_red
                   dest!: invs_cur_sc_tcb schact_is_rct elim: valid_sched_context_size_objsI)
  apply clarsimp
  done

lemma dmo_read_stval[wp]:
  "doMachineOp read_stval \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs')
  apply (clarsimp simp: in_monad read_stval_def)
  done

lemma chargeBudget_invs'[wp]:
  "chargeBudget consumed canTimeout Flag \<lbrace>invs'\<rbrace>"
  unfolding chargeBudget_def ifM_def bind_assoc
  apply (rule bind_wp[OF _ getCurSc_sp])
  apply (wpsimp wp: getSchedulable_wp)
     apply (rule hoare_strengthen_post[where Q'="\<lambda>_. invs'"])
      apply wpsimp
     apply (clarsimp simp: schedulable'_def obj_at'_def opt_map_def opt_pred_def
                           ct_in_state'_def pred_tcb_at'_def runnable_eq_active')
  by (wpsimp wp: hoare_drop_imp updateSchedContext_invs'
      | strengthen live_sc'_ex_cap[OF invs_iflive'] valid_sc_strengthen[OF invs_valid_objs'])+

lemma hy_invs':
  "handleYield \<lbrace>invs'\<rbrace>"
  apply (simp add: handleYield_def)
  by (wpsimp wp: updateSchedContext_invs' ct_in_state_thread_state_lift'
    | strengthen live_sc'_ex_cap[OF invs_iflive'] valid_sc_strengthen[OF invs_valid_objs'])+

lemma hv_invs'[wp]: "\<lbrace>invs' and tcb_at' t'\<rbrace> handleVMFault t' vptr \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: RISCV64_H.handleVMFault_def
             cong: vmfault_type.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpcw | simp)+
  done

crunch handleVMFault
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma hv_inv_ex':
  "\<lbrace>P\<rbrace> handleVMFault t vp \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: RISCV64_H.handleVMFault_def
             cong: vmfault_type.case_cong)
  apply (rule hoare_pre)
   apply (wp dmo_inv' getRestartPC_inv
             det_getRestartPC asUser_inv
          | wpcw)+
  apply simp
  done

lemma active_from_running':
  "ct_running' s' \<Longrightarrow> ct_active' s'"
  by (clarsimp elim!: pred_tcb'_weakenE
               simp: ct_in_state'_def)+

lemma simple_from_running':
  "ct_running' s' \<Longrightarrow> ct_in_state' simple' s'"
  by (clarsimp elim!: pred_tcb'_weakenE
               simp: ct_in_state'_def)+

lemmas cteDeleteOne_st_tcb_at_simple'[wp] =
    cteDeleteOne_st_tcb_at[where P=simple', simplified]

lemma handleCall_corres:
  "corres (dc \<oplus> dc) (einvs and valid_machine_time and schact_is_rct and ct_active
                     and ct_released and (\<lambda>s. active_sc_tcb_at (cur_thread s) s)
                     and ct_not_in_release_q and cur_sc_active and current_time_bounded
                     and consumed_time_bounded
                     and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
                     and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s))
              (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
                (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
                ct_active')
         handle_call handleCall"
  apply add_cur_tcb'
  apply (simp add: handle_call_def handleCall_def liftE_bindE handleInvocation_corres)
  apply (rule corres_stateAssertE_add_assertion[rotated])
   apply (clarsimp simp: cur_tcb'_asrt_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCapReg_corres])
      apply (simp, rule handleInvocation_corres; simp)
     apply wpsimp+
   apply fastforce+
  done

lemma hc_invs'[wp]:
  "\<lbrace>invs' and cur_tcb'
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
    and (\<lambda>s. schedulable' (ksCurThread s) s)\<rbrace>
   handleCall
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: handleCall_def)
  by (wpsimp wp: stateAssertE_inv)

lemma cteInsert_sane[wp]:
  "\<lbrace>sch_act_sane\<rbrace> cteInsert newCap srcSlot destSlot \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: sch_act_sane_def)
  apply (wp hoare_vcg_all_lift
            hoare_convert_imp [OF cteInsert_nosch cteInsert_ct])
  done

crunch setExtraBadge, transferCaps, handleFaultReply, doIPCTransfer
  for sch_act_sane [wp]: sch_act_sane
  (wp: crunch_wps sch_act_sane_lift simp: crunch_simps)

lemma handleHypervisorFault_corres:
  "corres dc (einvs and  st_tcb_at active thread and ex_nonz_cap_to thread
                   and (%_. valid_fault f))
             (invs' and sch_act_not thread
                    and st_tcb_at' simple' thread and ex_nonz_cap_to' thread)
          (handle_hypervisor_fault w fault) (handleHypervisorFault w fault)"
  apply (cases fault; clarsimp simp add: handleHypervisorFault_def returnOk_def2)
  done

(* FIXME: move *)
crunch handleVMFault,handleHypervisorFault
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  and cap_to'[wp]: "ex_nonz_cap_to' t"
  and ksit[wp]: "\<lambda>s. P (ksIdleThread s)"

lemma hv_inv':
  "\<lbrace>P\<rbrace> handleVMFault p t \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: RISCV64_H.handleVMFault_def)
  apply (rule hoare_pre)
   apply (wp dmo_inv' getRestartPC_inv det_getRestartPC asUser_inv
          | wpc | simp)+
  done

lemma hh_inv':
  "\<lbrace>P\<rbrace> handleHypervisorFault p t \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: RISCV64_H.handleHypervisorFault_def)
  apply (cases t; clarsimp)
  done

lemma ct_not_idle':
  fixes s
  assumes vi:  "valid_idle' s"
      and cts: "ct_in_state' (\<lambda>tcb. \<not>idle' tcb) s"
  shows "ksCurThread s \<noteq> ksIdleThread s"
proof
  assume "ksCurThread s = ksIdleThread s"
  with vi have "ct_in_state' idle' s"
    unfolding ct_in_state'_def valid_idle'_def
    by (clarsimp simp: pred_tcb_at'_def obj_at'_def idle_tcb'_def)

  with cts show False
    unfolding ct_in_state'_def
    by (fastforce dest: pred_tcb_at_conj')
qed

lemma ct_running_not_idle'[simp]:
  "\<lbrakk>valid_idle' s; ct_running' s\<rbrakk> \<Longrightarrow> ksCurThread s \<noteq> ksIdleThread s"
  apply (rule ct_not_idle')
   apply (fastforce simp: ct_in_state'_def
                   elim: pred_tcb'_weakenE)+
  done

lemma ct_active_not_idle'[simp]:
  "\<lbrakk>valid_idle' s; ct_active' s\<rbrakk> \<Longrightarrow> ksCurThread s \<noteq> ksIdleThread s"
  apply (rule ct_not_idle')
   apply (fastforce simp: ct_in_state'_def
                   elim: pred_tcb'_weakenE)+
  done

crunch handleFault, receiveSignal, receiveIPC, asUser
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma checkBudget_true:
  "\<lbrace>P\<rbrace> checkBudget \<lbrace>\<lambda>rv s. rv \<longrightarrow> P s\<rbrace>"
  unfolding checkBudget_def
  by (wpsimp | rule hoare_drop_imp)+

lemma checkBudgetRestart_true:
  "\<lbrace>P\<rbrace> checkBudgetRestart \<lbrace>\<lambda>rv s. rv \<longrightarrow> P s\<rbrace>"
  unfolding checkBudgetRestart_def
  apply (wpsimp wp: checkBudget_true)
   apply (rule hoare_drop_imp)
   apply (wpsimp wp: checkBudget_true)
  by clarsimp

lemma checkBudgetRestart_false:
  "\<lbrace>P\<rbrace> checkBudgetRestart \<lbrace>\<lambda>rv s. Q s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> checkBudgetRestart \<lbrace>\<lambda>rv s. \<not> rv \<longrightarrow> Q s\<rbrace>"
  by (wpsimp wp: hoare_drop_imp)

crunch checkBudget
  for invs'[wp]: invs'

lemma checkBudgetRestart_invs'[wp]:
  "checkBudgetRestart \<lbrace>invs'\<rbrace>"
  unfolding checkBudgetRestart_def
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (wpsimp wp: setThreadState_Restart_invs')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def)
  apply (intro conjI)
    apply (erule ko_wp_at'_weakenE, clarsimp)
   apply (drule invs_iflive')
   apply (erule (1) if_live_then_nonz_capD')
  by (fastforce simp: live_def ko_wp_at'_def opt_map_red is_BlockedOnReply_def)+

crunch check_budget
  for cur_tcb[wp]: cur_tcb
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)

crunch checkBudgetRestart
  for ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma getCurrentTime_invs'[wp]:
  "doMachineOp getCurrentTime \<lbrace>invs'\<rbrace>"
  apply (simp add: getCurrentTime_def modify_def)
  apply (wpsimp wp: dmo_invs' simp: modify_def)
  by (simp add: in_get put_def gets_def in_bind in_return)

lemma invs'_ksCurTime_update[iff]:
  "invs' (ksCurTime_update f s) = invs' s"
  by (clarsimp simp: invs'_def valid_pspace'_def valid_mdb'_def
                     valid_bitmapQ_def bitmapQ_def bitmapQ_no_L2_orphans_def
                     bitmapQ_no_L1_orphans_def valid_irq_node'_def valid_machine_state'_def
                     valid_dom_schedule'_def valid_bitmaps_def)

crunch setDomainTime, setCurTime, setConsumedTime, setExtraBadge, setReleaseQueue, setQueue,
  modifyReadyQueuesL1Bitmap, modifyReadyQueuesL2Bitmap, setReprogramTimer
  for ct_in_state'[wp]: "ct_in_state' P"
  and schedulable'[wp]: "schedulable' p"
  (simp: ct_in_state'_def schedulable'_def active_sc_tcb_at'_def)

crunch updateTimeStamp, tcbSchedAppend, postpone
  for invs'[wp]: invs'
  and ct_in_state'[wp]: "ct_in_state' P"
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  (ignore: doMachineOp wp: crunch_wps)

crunch updateTimeStamp
  for tcbSCs_of_scTCBs_of[wp]: "\<lambda>s. P (tcbSCs_of s) (scTCBs_of s)"
  and tcbs_of'_ct[wp]: "\<lambda>s. P (tcbs_of' s) (ksCurThread s)"
  and tcbSCs_of_ct[wp]: "\<lambda>s. P (tcbSCs_of s) (ksCurThread s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at' T p s)"
  and pred_tcb_at'[wp]: "\<lambda>s. P (pred_tcb_at' proj Q p s)"

lemma installThreadBuffer_ksCurThread[wp]:
  "installThreadBuffer target slot buffer \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> "
  unfolding installThreadBuffer_def
  by (wpsimp wp: checkCap_inv hoare_drop_imp cteDelete_preservation)

crunch RISCV64_H.performInvocation
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps wp: crunch_wps getObject_inv)

crunch resetUntypedCap
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps wp: mapME_x_inv_wp preemptionPoint_inv crunch_wps)

crunch performInvocation
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps cteRevoke_preservation filterM_preserved cteDelete_preservation
       hoare_drop_imps hoare_vcg_all_lift
   simp: crunch_simps)

crunch updateTimeStamp
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and schedulable'[wp]: "schedulable' t"
  and ct_schedulable'[wp]: "\<lambda>s. schedulable' (ksCurThread s) s"
  and cur_tcb'[wp]: cur_tcb'
  (rule: hoare_lift_Pf2[where f=ksCurThread] simp: cur_tcb'_def)

lemma schedulable'_runnableE:
  "schedulable' t s \<Longrightarrow> tcb_at' t s \<Longrightarrow> st_tcb_at' runnable' t s"
  unfolding schedulable'_def
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def opt_pred_def opt_map_def)

lemma he_invs'[wp]:
  "\<lbrace>invs' and cur_tcb' and
      (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> schedulable' (ksCurThread s) s) and
      (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   handleEvent event
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have nidle: "\<And>s. valid_idle' s \<and> ct_active' s \<longrightarrow> ksCurThread s \<noteq> ksIdleThread s"
    by (clarsimp)
  show ?thesis
    apply (case_tac event, simp_all add: handleEvent_def)
         apply (rename_tac syscall)
         apply (case_tac syscall,
                (wpsimp wp: checkBudgetRestart_true checkBudgetRestart_false hoare_vcg_if_lift2
                 | clarsimp simp: active_from_running' simple_from_running' simple_sane_strg
                                  stateAssertE_def stateAssert_def
                        simp del: split_paired_All
                 | rule hoare_strengthen_postE_R[where Q'="\<lambda>_. invs'", rotated],
                   clarsimp simp: ct_active'_asrt_def
                 | clarsimp dest!: schedulable'_runnableE intro!: pred_tcb'_weakenE
                            simp: ct_in_state'_def cur_tcb'_def runnable_eq_active'
                 | rule conjI active_ex_cap'
                 | strengthen nidle)+)
                  apply (rule hoare_strengthen_post,
                         rule hoare_weaken_pre,
                         rule hy_invs')
                   apply (simp add: active_from_running')
                  apply simp
                 apply (wp hv_inv' hh_inv' hoare_vcg_if_lift2 checkBudgetRestart_true checkBudgetRestart_false
                           updateTimeStamp_ct_in_state'[simplified ct_in_state'_def]
                        | strengthen active_ex_cap'[OF _ invs_iflive']
                        | clarsimp dest!: schedulable'_runnableE intro!: pred_tcb'_weakenE
                                    simp: ct_in_state'_def cur_tcb'_def runnable_eq_active'
                        | wpc)+
    done
qed

lemma released_imp_active_sc_tcb_at:
  "released_sc_tcb_at t s \<Longrightarrow> active_sc_tcb_at t s"
  by (clarsimp simp: vs_all_heap_simps)

lemma checkBudgetRestart_corres:
  "corres (=)
     (einvs and current_time_bounded and cur_sc_offset_ready 0
      and cur_sc_active and ct_in_state activatable and schact_is_rct
      and ct_not_queued and ct_not_in_release_q)
     invs'
     check_budget_restart checkBudgetRestart"
  unfolding check_budget_restart_def checkBudgetRestart_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF checkBudget_corres])
      apply (rule corres_split_eqr[OF getCurThread_corres])
        apply (rule corres_split[OF isRunnable_corres'])
           apply simp
          apply (clarsimp simp add: when_def)
          apply (rule corres_split[OF setThreadState_corres])
             apply clarsimp
            apply clarsimp
           apply ((wpsimp simp: cur_tcb_def[symmetric] cong: conj_cong | strengthen valid_objs_valid_tcbs)+)[6]
     apply (rule hoare_strengthen_post[where Q'="\<lambda>_. invs and cur_tcb"])
      apply wpsimp
     apply (clarsimp simp: cur_tcb_def invs_def valid_state_def valid_pspace_def)
    apply (rule hoare_strengthen_post[where Q'="\<lambda>_. invs'"])
     apply wpsimp
    apply (fastforce simp: invs'_def valid_pspace'_def valid_objs'_valid_tcbs'
                    dest!: invs_strengthen_cur_sc_tcb_are_bound)
   apply (clarsimp simp: invs_cur_sc_chargeableE invs_cur ct_activatable_ct_not_blocked)+
  done

lemma ct_not_in_release_q_cross:
  "\<lbrakk>ct_not_in_release_q s; release_queue_relation s s'; cur_thread s = ksCurThread s'; cur_tcb' s'\<rbrakk>
   \<Longrightarrow> pred_map (\<lambda>tcb. \<not> tcbInReleaseQueue tcb) (tcbs_of' s') (ksCurThread s')"
  apply (clarsimp simp: release_queue_relation_def list_queue_relation_def)
  apply (fastforce simp: not_in_release_q_def pred_map_def opt_pred_def opt_map_red obj_at'_def
                         cur_tcb'_def)
  done

lemma handleInv_handleRecv_corres:
  "corres (dc \<oplus> dc)
     (einvs and ct_running and (\<lambda>s. scheduler_action s = resume_cur_thread) and
      valid_machine_time and
      current_time_bounded and
      consumed_time_bounded and
      cur_sc_active and
      ct_released and
      ct_not_in_release_q and
      ct_not_queued and
      (\<lambda>s. cur_sc_offset_ready (consumed_time s) s) and
      (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s))
     (invs' and ct_running' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
     (doE reply_cptr <- liftE (get_cap_reg reg);
          y <- handle_invocation False False True True reply_cptr;
          liftE (handle_recv True canReply)
      odE)
     (doE replyCptr <- liftE (getCapReg reg);
          y <- handleInvocation False False True True replyCptr;
          y \<leftarrow> stateAssertE sch_act_sane_asrt [];
          y \<leftarrow> stateAssertE ct_not_ksQ_asrt [];
          y \<leftarrow> stateAssertE ct_active'_asrt [];
          liftE (handleRecv True canReply)
      odE)"
  apply add_cur_tcb'
  apply add_sym_refs
  apply (rule_tac Q'="\<lambda>s'. schedulable' (ksCurThread s') s'"
               in corres_cross_add_guard)
   apply (frule curthread_relation)
   apply clarsimp
   apply (erule schedulable_schedulable'_eq[THEN iffD1], fastforce+)
   apply (clarsimp simp: schedulable_def2)
   apply (rule conjI)
    apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
   apply (fastforce intro: schact_is_rct_ct_active_sc)
  apply (rule corres_rel_imp)
   apply (rule corres_guard_imp)
     apply (rule corres_split_liftEE[OF getCapReg_corres_gen])
       apply (rule corres_splitEE[OF handleInvocation_corres])
           apply simp
          apply simp
         apply (rule_tac P="(einvs and ct_active and scheduler_act_sane and current_time_bounded
                            and ct_not_queued and ct_not_in_release_q)"
                    and P'=invs'
                in corres_inst)
         apply (rule corres_stateAssertE_add_assertion)
          apply simp
          apply (rule corres_stateAssertE_add_assertion)
           apply (rule corres_stateAssertE_add_assertion)
            apply simp
            apply (clarsimp simp: sch_act_sane_asrt_def ct_not_ksQ_asrt_def ct_active'_asrt_def)
            apply (rule corres_guard_imp)
              apply (rule handleRecv_isBlocking_corres)
             apply simp
            apply simp
           apply (fastforce simp: ct_active'_asrt_def invs_psp_aligned invs_distinct
                           dest!: ct_active_cross)
          apply clarsimp
          apply (frule invs_cur)
          apply (frule cur_tcb_cross, fastforce+)
          apply (clarsimp simp: ct_not_ksQ_asrt_def cur_tcb'_def not_queued_def in_ready_q_def)
          apply (drule obj_at'_prop)+
          apply (frule state_relation_ready_queues_relation)
          apply (frule curthread_relation)
          apply (frule_tac t1="ksCurThread s'" in in_ready_q_tcbQueued_eq[THEN arg_cong_Not])
          apply (fastforce intro: aligned'_distinct'_ko_wp_at'I
                            simp: opt_pred_def opt_map_def obj_at'_real_def in_ready_q_def)
         apply (clarsimp simp: sch_act_sane_asrt_def scheduler_act_not_def sch_act_sane_def sched_act_relation_def
                         dest!: state_relationD)
         apply (case_tac "scheduler_action s"; fastforce)
        apply (wpsimp wp: handle_invocation_valid_sched)
       apply wpsimp
      apply wpsimp
     apply wpsimp
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def active_from_running
                          schedulable_def2 released_sc_tcb_at_def)
    apply (clarsimp simp: ct_in_state_def st_tcb_weakenE)
   apply (fastforce simp: schedulable'_def opt_pred_def opt_map_def pred_map_def
                          ct_in_state'_def st_tcb_at'_def obj_at'_def)
  apply simp
  done

(* these two appreviations are for the two helper lemmas below, which should be identical
   except that they are in different monads *)
abbreviation (input)
  "a_pre \<equiv> (einvs and ct_running and
         (\<lambda>s. scheduler_action s = resume_cur_thread) and
         valid_machine_time and
         current_time_bounded and
         consumed_time_bounded and
         cur_sc_active and (ct_active or ct_idle) and
         ct_not_in_release_q and
         ct_not_queued and
         (\<lambda>s. cur_sc_offset_ready (consumed_time s) s) and
         (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s) and
         ct_released)"

abbreviation (input)
  "c_pre \<equiv> (invs' and ct_running' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))"

lemma updateTimeStamp_checkBudgetRestart_helper:
  assumes H: "corres dc a_pre c_pre f f'"
  shows "corres dc a_pre c_pre
           (do y <- update_time_stamp;
               restart <- check_budget_restart;
               when restart f
            od)
           (do y <- updateTimeStamp;
               restart <- checkBudgetRestart;
               when restart f'
            od)"
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF updateTimeStamp_corres])
      apply (rule_tac P="\<lambda> s. (cur_sc_active s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
                               \<and> cur_sc_active s \<and> ct_running s \<and> valid_machine_time s
                               \<and> ct_released s \<and> ct_not_in_release_q s \<and> ct_not_queued s
                               \<and> current_time_bounded s \<and> consumed_time_bounded s \<and> einvs s
                               \<and> scheduler_action s = resume_cur_thread"
                 and P'=c_pre in corres_inst)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF checkBudgetRestart_corres])
          apply (simp add: when_def split del: if_split)
          apply (rule corres_if2)
            apply simp
           apply (rule_tac P="\<lambda>s. (cur_sc_offset_ready (consumed_time s) s \<and> einvs s
                                   \<and> cur_sc_active s \<and> valid_machine_time s \<and> ct_running s
                                   \<and> ct_released s \<and> ct_not_in_release_q s \<and> ct_not_queued s
                                   \<and> current_time_bounded s \<and> consumed_time_bounded s
                                   \<and> scheduler_action s = resume_cur_thread)
                                   \<and> cur_sc_offset_sufficient (consumed_time s) s"
                      and P'=c_pre in corres_inst)
           apply (rule corres_guard_imp)
             apply (rule H)
            apply (clarsimp simp: active_from_running)
           apply simp
          apply (simp add: corres_return[where P=cur_sc_more_than_ready])
         apply (wpsimp wp: check_budget_restart_false check_budget_restart_true')
        apply (wpsimp wp: checkBudgetRestart_false checkBudgetRestart_true)
       apply (clarsimp dest!: active_from_running
                        simp: cur_sc_offset_ready_def pred_map_def
                              ct_in_state_weaken[OF _ active_activatable])
      apply clarsimp
     apply (wpsimp wp: update_time_stamp_current_time_bounded
                       update_time_stamp_cur_sc_offset_ready_cs)
    apply wpsimp
   apply clarsimp+
  done

lemma updateTimeStamp_checkBudgetRestart_helperE:
  assumes H: "corres (dc \<oplus> dc) a_pre c_pre f f'"
  shows "corres (dc \<oplus> dc) a_pre c_pre
           (doE y <- liftE update_time_stamp;
               restart <- liftE check_budget_restart;
               whenE restart f
            odE)
           (doE y <- liftE updateTimeStamp;
               restart <- liftE checkBudgetRestart;
               whenE restart f'
            odE)"
  apply (rule corres_guard_imp)
    apply (rule corres_split_liftEE[OF updateTimeStamp_corres])
      apply (rule_tac P="\<lambda> s. (cur_sc_active s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
                               \<and> cur_sc_active s \<and> ct_running s \<and> valid_machine_time s
                               \<and> ct_released s \<and> ct_not_in_release_q s \<and> ct_not_queued s
                               \<and> current_time_bounded s \<and> consumed_time_bounded s \<and> einvs s
                               \<and> scheduler_action s = resume_cur_thread"
                 and P'=c_pre in corres_inst)
      apply (rule corres_guard_imp)
        apply (rule corres_split_liftEE[OF checkBudgetRestart_corres])
          apply (simp add: whenE_def split del: if_split)
          apply (rule corres_if2)
            apply simp
           apply (rule_tac P="\<lambda>s. (cur_sc_offset_ready (consumed_time s) s \<and> einvs s
                                   \<and> cur_sc_active s \<and> valid_machine_time s \<and> ct_running s
                                   \<and> ct_released s \<and> ct_not_in_release_q s \<and> ct_not_queued s
                                   \<and> current_time_bounded s \<and> consumed_time_bounded s
                                   \<and> scheduler_action s = resume_cur_thread)
                                   \<and> cur_sc_offset_sufficient (consumed_time s) s"
                      and P'=c_pre in corres_inst)
           apply (rule corres_guard_imp)
             apply (rule H)
            apply (clarsimp simp: active_from_running)
           apply simp
          apply (rule corres_returnOk[where P=cur_sc_more_than_ready])
          apply simp
         apply (wpsimp wp: check_budget_restart_false check_budget_restart_true')
        apply (wpsimp wp: checkBudgetRestart_false checkBudgetRestart_true)
       apply (clarsimp dest!: active_from_running
                        simp: cur_sc_offset_ready_def pred_map_def
                              ct_in_state_weaken[OF _ active_activatable])
      apply clarsimp
     apply (wpsimp wp: update_time_stamp_current_time_bounded
                       update_time_stamp_cur_sc_offset_ready_cs)
    apply wpsimp
   apply clarsimp+
  done

lemma handleEvent_corres:
  "corres (dc \<oplus> dc)
     (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and valid_machine_time and current_time_bounded
      and consumed_time_bounded and cur_sc_active and (ct_active or ct_idle)
      and ct_not_in_release_q and ct_not_queued
      and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
      and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s))
     (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and
      (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
     (handle_event event) (handleEvent event)"
  (is "corres _ (?P and ?ready and _) ?P' _ _")
proof -
  have hw:
    "\<And>isBlocking canGrant.
     corres dc (einvs and ct_running and valid_machine_time and current_time_bounded
                and ct_released and (\<lambda>s. scheduler_action s = resume_cur_thread)
                and ct_not_in_release_q and ct_not_queued)
               (invs' and ct_running'
                      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
               (handle_recv isBlocking canGrant) (handleRecv isBlocking canGrant)"
    apply add_cur_tcb'
    apply add_ct_not_inQ
    apply (rule corres_guard_imp [OF handleRecv_isBlocking_corres])
     apply (fastforce simp: ct_in_state_def ct_in_state'_def
                     elim!: st_tcb_weakenE pred_tcb'_weakenE)+
    done
  show ?thesis
    apply (rule corres_cross_add_abs_guard[where Q="\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_released s"])
     apply (simp only: schact_is_rct_def[symmetric])
     apply clarsimp
     apply (frule (1) invs_strengthen_cur_sc_tcb_are_bound[OF _ invs_cur_sc_tcb])
      apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
     apply (erule (5) schact_is_rct_ct_released)
     apply (erule (2) cur_sc_not_idle_sc_ptr')
    apply (case_tac event)
         apply (simp_all add: handleEvent_def)
         apply (rename_tac syscall)
         apply (rule updateTimeStamp_checkBudgetRestart_helperE)
         apply (case_tac syscall; simp)
                   apply (auto intro: corres_guard_imp[OF handleSend_corres]
                                      corres_guard_imp[OF hw]
                                      corres_guard_imp[OF handleCall_corres]
                                      corres_guard_imp[OF handleInv_handleRecv_corres]
                                      corres_guard_imp[OF handleYield_corres]
                                      active_from_running active_from_running' released_imp_active_sc_tcb_at
                               simp: simple_sane_strg
                              dest!: schact_is_rct)[11]
        apply (rule updateTimeStamp_checkBudgetRestart_helper)
        apply (rule corres_underlying_split)
           apply (rule corres_guard_imp[OF getCurThread_corres], simp+)
          apply (rule handleFault_corres)
          apply simp
         apply wpsimp
         apply (clarsimp simp: valid_fault_def valid_sched_def current_time_bounded_def
                        dest!: active_from_running)
         apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE simp: ct_in_state_def)
        apply wp
        apply (fastforce simp: ct_in_state'_def sch_act_simple_def
                         elim: pred_tcb'_weakenE st_tcb_ex_cap'')

       apply (rule updateTimeStamp_checkBudgetRestart_helper)
       apply (rule corres_underlying_split)
          apply (rule corres_guard_imp[OF getCurThread_corres], simp+)
         apply (rule handleFault_corres)
         apply simp
        apply wpsimp
        apply (clarsimp simp: valid_fault_def valid_sched_def current_time_bounded_def
                       dest!: active_from_running)
        apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE simp: ct_in_state_def)
       apply wp
       apply (fastforce simp: ct_in_state'_def sch_act_simple_def
                        elim: pred_tcb'_weakenE st_tcb_ex_cap'')

      apply (rule corres_guard_imp)
        apply (rule corres_split_eqr[OF corres_machine_op])
           apply (rule corres_Id, simp+)
           apply wp
          apply (rename_tac active)
          apply (rule corres_split[OF updateTimeStamp_corres])
            apply (rule_tac P="\<lambda> s. (cur_sc_active s \<longrightarrow> cur_sc_offset_ready (consumed_time s) s)
                                     \<and> cur_sc_active s \<and> valid_machine_time s \<and> (ct_active s \<or> ct_idle s)
                                     \<and> ct_not_in_release_q s \<and> ct_not_queued s
                                     \<and> current_time_bounded s \<and> consumed_time_bounded s \<and> einvs s
                                     \<and> scheduler_action s = resume_cur_thread"
                       and P'="(invs' and
                                (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) and
                                (\<lambda>s. \<forall>x. active = Some x \<longrightarrow>
                                            intStateIRQTable (ksInterruptState s) x \<noteq> irqstate.IRQInactive)"
                   in corres_inst)
            apply (rule corres_guard_imp)
              apply (rule corres_split[OF checkBudget_corres])
                apply (rule_tac P="einvs and current_time_bounded"
                           and P'="invs' and (\<lambda>s. \<forall>x. active = Some x \<longrightarrow> intStateIRQTable (ksInterruptState s) x \<noteq> irqstate.IRQInactive)"
                       in corres_inst)
                apply (case_tac active; simp)
                apply (rule handleInterrupt_corres)
               apply (wpsimp wp: check_budget_valid_sched)
              apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
             apply (wpsimp wp: update_time_stamp_current_time_bounded hoare_vcg_disj_lift
                               update_time_stamp_cur_sc_offset_ready_cs)
             apply (clarsimp simp: cur_sc_offset_ready_weaken_zero active_from_running current_time_bounded_def)
             apply (frule invs_cur_sc_chargeableE)
              apply (clarsimp simp: schact_is_rct_def)
             apply clarsimp
             apply (rule conjI)
              apply (erule cur_sc_offset_ready_weaken_zero)
             apply (rule conjI)
              apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def cur_tcb_def is_tcb dest!: invs_cur)
             apply (rule conjI)
              apply (erule ct_not_blocked_cur_sc_not_blocked)
              apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def)
             apply fastforce
             apply (fastforce simp: ct_in_state_def pred_tcb_at_def obj_at_def dest!: active_activatable)
            apply clarsimp
           apply (wpsimp wp: update_time_stamp_current_time_bounded hoare_vcg_disj_lift
                             update_time_stamp_cur_sc_offset_ready_cs)
          apply wpsimp
         apply wpsimp
         apply (clarsimp simp: ct_in_state_def)
        apply (wpsimp wp: doMachineOp_getActiveIRQ_IRQ_active' hoare_vcg_all_lift)
       apply (clarsimp elim!: active_from_running)
      apply clarsimp
      apply (simp add: invs'_def)
     apply (rule updateTimeStamp_checkBudgetRestart_helper)
     apply (rule corres_underlying_split)
        apply (rule corres_guard_imp[OF getCurThread_corres], simp+)
       apply (rule corres_split_catch)
          apply (rule handleVMFault_corres)
         apply (erule handleFault_corres)
        apply (rule hoare_elim_pred_conjE2)
        apply (rule hoare_vcg_conj_liftE_E, rule valid_validE_E, wp)
        apply (wpsimp wp: handle_vm_fault_valid_fault)
       apply (rule hv_inv_ex')
      apply wp
      apply (clarsimp simp: active_from_running tcb_at_invs valid_sched_def current_time_bounded_def)
      apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE simp: ct_in_state_def)
     apply wp
     apply clarsimp
     apply (fastforce simp: simple_sane_strg sch_act_simple_def ct_in_state'_def
                      elim: st_tcb_ex_cap'' pred_tcb'_weakenE)
    apply add_ct_not_inQ
    apply (rule corres_underlying_split)
       apply (rule corres_guard_imp[OF getCurThread_corres], simp+)
      apply (rule handleHypervisorFault_corres)
     apply (simp add: valid_fault_def)
     apply wp
     apply clarsimp
     apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE
                      simp: ct_in_state_def)
    apply wp
    apply (clarsimp simp: active_from_running' invs'_def valid_pspace'_def)
    apply (fastforce simp: ct_in_state'_def sch_act_simple_def
                           sch_act_sane_def
                     elim: pred_tcb'_weakenE st_tcb_ex_cap'')
    done
  qed

end

end
