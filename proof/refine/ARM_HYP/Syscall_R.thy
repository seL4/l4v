(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Refinement for handleEvent and syscalls
*)

theory Syscall_R
imports Tcb_R Arch_R Interrupt_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

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
| "inv_relation (Invocations_A.InvokeReply w ptr grant) x =
     (x = InvokeReply w (cte_map ptr) grant)"
| "inv_relation (Invocations_A.InvokeTCB i) x =
     (\<exists>i'. tcbinv_relation i i' \<and> x = InvokeTCB i')"
| "inv_relation (Invocations_A.InvokeDomain tptr domain) x =
     (x = InvokeDomain tptr domain)"
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
  "valid_invocation' (Invocations_H.InvokeUntyped i) = valid_untyped_inv' i"
| "valid_invocation' (Invocations_H.InvokeEndpoint w w2 b c) = (ep_at' w and ex_nonz_cap_to' w)"
| "valid_invocation' (Invocations_H.InvokeNotification w w2) = (ntfn_at' w and ex_nonz_cap_to' w)"
| "valid_invocation' (Invocations_H.InvokeTCB i) = tcb_inv_wf' i"
| "valid_invocation' (Invocations_H.InvokeDomain thread domain) =
   (tcb_at' thread  and K (domain \<le> maxDomain))"
| "valid_invocation' (Invocations_H.InvokeReply thread slot grant) =
       (tcb_at' thread and cte_wp_at' (\<lambda>cte. \<exists>gr. cteCap cte = ReplyCap thread False gr) slot)"
| "valid_invocation' (Invocations_H.InvokeIRQControl i) = irq_control_inv_valid' i"
| "valid_invocation' (Invocations_H.InvokeIRQHandler i) = irq_handler_inv_valid' i"
| "valid_invocation' (Invocations_H.InvokeCNode i) = valid_cnode_inv' i"
| "valid_invocation' (Invocations_H.InvokeArchObject i) = valid_arch_inv' i"


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
                 and (\<lambda>s. length args < 2 ^ word_bits))
           (invs' and valid_cap' cap' and cte_at' slot'
            and (\<lambda>s. \<forall>x\<in>set excaps'. s \<turnstile>' fst x \<and> cte_at' (snd x) s)
            and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
      (decode_invocation (mi_label mi) args cptr slot cap excaps)
      (RetypeDecls_H.decodeInvocation (mi_label mi) args' cptr' slot' cap' excaps')"
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
          apply (rule_tac F="length list \<le> 32" in corres_gen_asm)
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
      apply (simp add: isCap_defs)
      apply (rule corres_guard_imp)
      apply (rule decodeDomainInvocation_corres)
      apply (simp+)[4]
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

declare mapME_Nil [simp]

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

lemma threadSet_tcbDomain_update_ct_idle_or_in_cur_domain':
  "\<lbrace>ct_idle_or_in_cur_domain' and (\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread) \<rbrace>
     threadSet (tcbDomain_update (\<lambda>_. domain)) t
   \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (wp hoare_vcg_disj_lift hoare_vcg_imp_lift)
    apply (wp | wps)+
  apply (auto simp: obj_at'_def)
  done

lemma threadSet_tcbDomain_update_ct_not_inQ:
  "\<lbrace>ct_not_inQ \<rbrace> threadSet (tcbDomain_update (\<lambda>_. domain)) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: threadSet_def ct_not_inQ_def)
  apply (wp)
    apply (rule hoare_convert_imp [OF setObject_nosch])
     apply (rule updateObject_tcb_inv)
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
     apply (wps setObject_sa_unchanged)
     apply (wp hoare_weak_lift_imp getObject_tcb_wp hoare_vcg_all_lift)+
   apply (rename_tac word)
   apply (rule_tac Q="\<lambda>_ s. ksSchedulerAction s = SwitchToThread word \<longrightarrow>
                            st_tcb_at' runnable' word s \<and> tcb_in_cur_domain' word s \<and> word \<noteq> t"
                   in hoare_strengthen_post)
    apply (wp hoare_vcg_all_lift hoare_vcg_conj_lift hoare_vcg_imp_lift)+
     apply (simp add: threadSet_def)
     apply (wp getObject_tcb_wp threadSet_tcbDomain_triv')+
   apply (auto simp: obj_at'_def)
  done

lemma setDomain_corres:
  "corres dc
     (valid_etcbs and valid_sched and tcb_at tptr)
     (invs'  and sch_act_simple
             and tcb_at' tptr and (\<lambda>s. new_dom \<le> maxDomain))
     (set_domain tptr new_dom)
     (setDomain tptr new_dom)"
  apply (rule corres_gen_asm2)
  apply (simp add: set_domain_def setDomain_def thread_set_domain_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split[OF tcbSchedDequeue_corres])
        apply (rule corres_split)
           apply (rule ethread_set_corres; simp)
           apply (clarsimp simp: etcb_relation_def)
          apply (rule corres_split[OF isRunnable_corres])
            apply simp
            apply (rule corres_split)
               apply clarsimp
               apply (rule corres_when[OF refl])
               apply (rule tcbSchedEnqueue_corres)
              apply (rule corres_when[OF refl])
              apply (rule rescheduleRequired_corres)
             apply ((wp hoare_drop_imps hoare_vcg_conj_lift | clarsimp| assumption)+)[5]
        apply clarsimp
        apply (rule_tac Q="\<lambda>_. valid_objs' and valid_queues' and valid_queues and
          (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and tcb_at' tptr"
          in hoare_strengthen_post[rotated])
         apply (auto simp: invs'_def valid_state'_def sch_act_wf_weak st_tcb_at'_def o_def)[1]
        apply (wp threadSet_valid_objs' threadSet_valid_queues'_no_state
          threadSet_valid_queues_no_state
          threadSet_pred_tcb_no_state | simp)+
      apply (rule_tac Q = "\<lambda>r s. invs' s \<and> (\<forall>p. tptr \<notin> set (ksReadyQueues s p)) \<and> sch_act_simple s
        \<and>  tcb_at' tptr s" in hoare_strengthen_post[rotated])
       apply (clarsimp simp:invs'_def valid_state'_def valid_pspace'_def sch_act_simple_def)
       apply (clarsimp simp:valid_tcb'_def)
       apply (drule(1) bspec)
       apply (clarsimp simp:tcb_cte_cases_def)
       apply fastforce
      apply (wp hoare_vcg_all_lift Tcb_R.tcbSchedDequeue_not_in_queue)+
   apply clarsimp
   apply (frule tcb_at_is_etcb_at)
    apply simp+
   apply (auto elim: tcb_at_is_etcb_at valid_objs'_maxDomain valid_objs'_maxPriority pred_tcb'_weakenE
               simp: valid_sched_def valid_sched_action_def)
  done

lemma performInvocation_corres:
  "\<lbrakk> inv_relation i i'; call \<longrightarrow> block \<rbrakk> \<Longrightarrow>
   corres (dc \<oplus> (=))
     (einvs and valid_invocation i
            and schact_is_rct
            and ct_active
            and (\<lambda>s. (\<exists>w w2 b c. i = Invocations_A.InvokeEndpoint w w2 b c) \<longrightarrow> st_tcb_at simple (cur_thread s) s))
     (invs' and sch_act_simple and valid_invocation' i' and ct_active' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
     (perform_invocation block call i) (performInvocation block call i')"
  apply (simp add: performInvocation_def)
  apply (case_tac i)
           apply (clarsimp simp: o_def liftE_bindE)
           apply (rule corres_guard_imp)
             apply (rule corres_split_norE)
                apply (rule corres_rel_imp, rule inv_untyped_corres)
                 apply simp
                apply (case_tac x, simp_all)[1]
               apply (rule corres_returnOkTT)
               apply simp
              apply wp+
            apply simp+
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF getCurThread_corres])
              apply simp
              apply (rule corres_split[OF sendIPC_corres])
                 apply simp
                apply (rule corres_trivial)
                apply simp
               apply wp+
           apply (clarsimp simp: ct_in_state_def)
           apply (fastforce elim: st_tcb_ex_cap)
          apply (clarsimp simp: pred_conj_def invs'_def cur_tcb'_def simple_sane_strg
                                sch_act_simple_def)
         apply (rule corres_guard_imp)
           apply (simp add: liftE_bindE)
           apply (rule corres_split[OF sendSignal_corres])
             apply (rule corres_trivial)
             apply (simp add: returnOk_def)
            apply wp+
          apply (simp+)[2]
        apply simp
        apply (rule corres_guard_imp)
          apply (rule corres_split_eqr[OF getCurThread_corres])
            apply (rule corres_split_nor[OF doReplyTransfer_corres'])
              apply (rule corres_trivial, simp)
             apply wp+
         apply (clarsimp simp: tcb_at_invs)
         apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
         apply (erule cte_wp_at_weakenE, fastforce simp: is_reply_cap_to_def)
        apply (clarsimp simp: tcb_at_invs')
        apply (fastforce elim!: cte_wp_at_weakenE')
       apply (clarsimp simp: liftME_def)
       apply (rule corres_guard_imp)
         apply (erule invokeTCB_corres)
        apply ((clarsimp dest!: schact_is_rct_simple)+)[2]
       \<comment> \<open>domain cap\<close>
      apply (clarsimp simp: invoke_domain_def)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF setDomain_corres])
          apply (rule corres_trivial, simp)
         apply (wp)+
       apply (clarsimp+)[2]
     \<comment> \<open>CNodes\<close>
     apply clarsimp
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE[OF invokeCNode_corres])
          apply assumption
         apply (rule corres_trivial, simp add: returnOk_def)
        apply wp+
      apply ((clarsimp dest!: schact_is_rct_simple)+)[2]
    apply (clarsimp simp: liftME_def[symmetric] o_def dc_def[symmetric])
    apply (rule corres_guard_imp, rule performIRQControl_corres, simp+)
   apply (clarsimp simp: liftME_def[symmetric] o_def dc_def[symmetric])
   apply (rule corres_guard_imp, rule invokeIRQHandler_corres, simp+)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule arch_performInvocation_corres, assumption)
   apply (clarsimp+)[2]
  done

lemma sendSignal_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace>
     sendSignal ntfnptr bdg
   \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  apply (simp add: sendSignal_def
              cong: list.case_cong Structures_H.notification.case_cong)
  apply (wp ntfn'_cases_weak_wp list_cases_weak_wp hoare_drop_imps | wpc | simp)+
  done

lemmas checkCap_inv_typ_at'
  = checkCap_inv[where P="\<lambda>s. P (typ_at' T p s)" for P T p]

crunches restart, bindNotification, performTransfer
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma invokeTCB_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>
     invokeTCB tinv
   \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  apply (cases tinv,
         simp_all add: invokeTCB_def
                       getThreadBufferSlot_def locateSlot_conv
            split del: if_split)
   apply (simp only: cases_simp if_cancel simp_thms conj_comms pred_conj_def
                     Let_def split_def getThreadVSpaceRoot
          | (simp split del: if_split cong: if_cong)
          | (wp mapM_x_wp[where S=UNIV, simplified]
                checkCap_inv_typ_at'
                case_options_weak_wp)[1]
          | wpcw)+
  done

lemmas invokeTCB_typ_ats[wp] = typ_at_lifts [OF invokeTCB_typ_at']

crunch typ_at'[wp]: doReplyTransfer "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps)

lemmas doReplyTransfer_typ_ats[wp] = typ_at_lifts [OF doReplyTransfer_typ_at']

crunch typ_at'[wp]: "performIRQControl" "\<lambda>s. P (typ_at' T p s)"

lemmas invokeIRQControl_typ_ats[wp] =
  typ_at_lifts [OF performIRQControl_typ_at']

crunch typ_at'[wp]: InterruptDecls_H.invokeIRQHandler "\<lambda>s. P (typ_at' T p s)"

lemmas invokeIRQHandler_typ_ats[wp] =
  typ_at_lifts [OF InterruptDecls_H_invokeIRQHandler_typ_at']

crunch tcb_at'[wp]: setDomain "tcb_at' tptr"
  (simp: crunch_simps)

lemma pinv_tcb'[wp]:
  "\<lbrace>invs' and st_tcb_at' active' tptr
          and valid_invocation' i and ct_active'\<rbrace>
     RetypeDecls_H.performInvocation block call i
   \<lbrace>\<lambda>rv. tcb_at' tptr\<rbrace>"
  apply (simp add: performInvocation_def)
  apply (case_tac i, simp_all)
          apply (wp invokeArch_tcb_at' | clarsimp simp: pred_tcb_at')+
  done

lemma sts_cte_at[wp]:
  "\<lbrace>cte_at' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. cte_at' p\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp|simp)+
  done

crunch obj_at_ntfn[wp]: setThreadState "obj_at' (\<lambda>ntfn. P (ntfnBoundTCB ntfn) (ntfnObj ntfn)) ntfnptr"
  (wp: obj_at_setObject2 crunch_wps
   simp: crunch_simps updateObject_default_def in_monad)

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

lemma sts_valid_inv'[wp]:
  "\<lbrace>valid_invocation' i\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_invocation' i\<rbrace>"
  apply (case_tac i, simp_all add: sts_valid_untyped_inv' sts_valid_arch_inv')
         apply (wp | simp)+
     defer
     apply (rename_tac cnode_invocation)
     apply (case_tac cnode_invocation, simp_all add: cte_wp_at_ctes_of)
           apply (wp | simp)+
    apply (rename_tac irqcontrol_invocation)
    apply (case_tac irqcontrol_invocation, simp_all)
     apply (rename_tac arch_irqhandler_issue)
     apply (case_tac arch_irqhandler_issue)
     apply (wp | simp add: irq_issued'_def)+
   apply (rename_tac irqhandler_invocation)
   apply (case_tac irqhandler_invocation, simp_all)
     apply (wp hoare_vcg_ex_lift ex_cte_cap_to'_pres | simp)+
  apply (rename_tac tcbinvocation)
  apply (case_tac tcbinvocation,
      simp_all add: setThreadState_tcb',
      auto  intro!: hoare_vcg_conj_lift hoare_vcg_disj_lift
      simp only: imp_conv_disj simp_thms pred_conj_def,
      auto  intro!: hoare_vcg_prop
      sts_cap_to' sts_cte_cap_to'
      setThreadState_typ_ats
      split: option.splits)[1]
    apply (wp sts_bound_tcb_at' hoare_vcg_all_lift hoare_vcg_const_imp_lift)+
  done

(* FIXME: move to TCB *)
crunch inv[wp]: decodeDomainInvocation P
  (wp: crunch_wps simp: crunch_simps)

lemma decode_inv_inv'[wp]:
  "\<lbrace>P\<rbrace> decodeInvocation label args cap_index slot cap excaps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decodeInvocation_def Let_def
              split del: if_split
              cong: if_cong)
  apply (rule hoare_pre)
   apply (wp decodeTCBInvocation_inv |
          simp only: o_def |
          clarsimp split: capability.split_asm simp: isCap_defs)+
  done

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
          and (\<lambda>s. \<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
          and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs' (fst cap) (irq_node' s). ex_cte_cap_to' r s)
          and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>zobj_refs' (fst cap). ex_nonz_cap_to' r s)
          and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) o cteCap) (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile>' fst x)
          and (\<lambda>s. \<forall>x \<in> set excaps. real_cte_at' (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to' isCNodeCap (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' (badge_derived' (fst x) o cteCap) (snd x) s)
          and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     decodeInvocation label args cap_index slot cap excaps
   \<lbrace>valid_invocation'\<rbrace>,-"
  apply (case_tac cap, simp_all add: decodeInvocation_def Let_def isCap_defs uncurry_def split_def
              split del: if_split
              cong: if_cong)
             apply ((rule hoare_pre,
                     ((wpsimp wp: decodeTCBInv_wf simp: o_def)+)[1],
                     clarsimp simp: valid_cap'_def cte_wp_at_ctes_of)
                    | intro exI conjI | simp)+
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

crunch it[wp]: handleFaultReply "\<lambda>s. P (ksIdleThread s)"
crunch invs'[wp]: handleArchFaultReply "invs'"

lemma handleFaultReply_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> handleFaultReply x t label msg \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: handleFaultReply_def)
  apply (case_tac x, simp_all)
     apply (wp | clarsimp simp: handleArchFaultReply_def
                          split: arch_fault.split)+
  done

crunch sch_act_simple[wp]: handleFaultReply sch_act_simple
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

crunch cte_wp_at' [wp]: setMessageInfo "cte_wp_at' P p"

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

lemma setMRs_cte_wp_at'[wp]:
  "\<lbrace>cte_wp_at' P ptr\<rbrace> setMRs thread buffer messageData \<lbrace>\<lambda>_. cte_wp_at' P ptr\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def, wp crunch_wps)

crunch cte_wp_at'[wp]: makeArchFaultMessage "cte_wp_at' P ptr"
crunch cte_wp_at'[wp]: makeFaultMessage "cte_wp_at' P ptr"

lemma doFaultTransfer_cte_wp_at'[wp]:
  "\<lbrace>cte_wp_at' P ptr\<rbrace>
   doFaultTransfer badge sender receiver receiverIPCBuffer
   \<lbrace>\<lambda>_. cte_wp_at' P ptr\<rbrace>"
  unfolding doFaultTransfer_def
  apply (wp | wpc | simp add: split_def)+
  done

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
  by (case_tac st, (clarsimp simp add: isReply_def)+)

lemma doReply_invs[wp]:
  "\<lbrace>tcb_at' t and tcb_at' t' and
    cte_wp_at' (\<lambda>cte. \<exists>grant. cteCap cte = ReplyCap t False grant) slot and
    invs' and sch_act_simple\<rbrace>
     doReplyTransfer t' t slot grant
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: doReplyTransfer_def liftM_def)
  apply (rule hoare_seq_ext [OF _ gts_sp'])
  apply (rule hoare_seq_ext [OF _ assert_sp])
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (wp, wpc)
        apply (wp)
          apply (wp (once) sts_invs_minor'')
          apply (simp)
          apply (wp (once) sts_st_tcb')
          apply (wp)[1]
         apply (rule_tac Q="\<lambda>rv s. invs' s
                                   \<and> t \<noteq> ksIdleThread s
                                   \<and> st_tcb_at' awaiting_reply' t s"
                 in hoare_post_imp)
          apply (clarsimp)
          apply (frule_tac t=t in invs'_not_runnable_not_queued)
           apply (erule pred_tcb'_weakenE, case_tac st, clarsimp+)
          apply (rule conjI, erule pred_tcb'_weakenE, case_tac st, clarsimp+)
          apply (rule conjI, rule impI, erule pred_tcb'_weakenE, case_tac st)
                  apply (clarsimp | drule(1) obj_at_conj')+
          apply (clarsimp simp: invs'_def valid_state'_def ct_in_state'_def)
          apply (drule(1) pred_tcb_at_conj')
          apply (subgoal_tac "st_tcb_at' (\<lambda>_. False) (ksCurThread s) s")
           apply (clarsimp)
          apply (erule_tac P="\<lambda>st. awaiting_reply' st \<and> activatable' st"
                  in pred_tcb'_weakenE)
          apply (case_tac st, clarsimp+)
         apply (wp cteDeleteOne_reply_pred_tcb_at)+
        apply (clarsimp)
        apply (rule_tac Q="\<lambda>_. (\<lambda>s. t \<noteq> ksIdleThread s)
                          and cte_wp_at' (\<lambda>cte. \<exists>grant. cteCap cte = capability.ReplyCap t False grant) slot"
                in hoare_strengthen_post [rotated])
         apply (fastforce simp: cte_wp_at'_def)
        apply (wp)
        apply (rule hoare_strengthen_post [OF doIPCTransfer_non_null_cte_wp_at'])
         apply (erule conjE)
         apply assumption
        apply (erule cte_wp_at_weakenE')
        apply (fastforce)
       apply (wp sts_invs_minor'' sts_st_tcb' hoare_weak_lift_imp)
             apply (rule_tac Q="\<lambda>rv s. invs' s \<and> sch_act_simple s
                                   \<and> st_tcb_at' awaiting_reply' t s
                                   \<and> t \<noteq> ksIdleThread s"
                         in hoare_post_imp)
              apply (clarsimp)
              apply (frule_tac t=t in invs'_not_runnable_not_queued)
               apply (erule pred_tcb'_weakenE, case_tac st, clarsimp+)
              apply (rule conjI, erule pred_tcb'_weakenE, case_tac st, clarsimp+)
              apply (rule conjI, rule impI, erule pred_tcb'_weakenE, case_tac st)
                      apply (clarsimp | drule(1) obj_at_conj')+
              apply (clarsimp simp: invs'_def valid_state'_def ct_in_state'_def)
              apply (drule(1) pred_tcb_at_conj')
              apply (subgoal_tac "st_tcb_at' (\<lambda>_. False) (ksCurThread s) s")
               apply (clarsimp)
              apply (erule_tac P="\<lambda>st. awaiting_reply' st \<and> activatable' st"
                      in pred_tcb'_weakenE)
              apply (case_tac st, clarsimp+)
             apply (wp threadSet_invs_trivial threadSet_st_tcb_at2 hoare_weak_lift_imp
                    | clarsimp simp add: inQ_def)+
           apply (rule_tac Q="\<lambda>_. invs' and tcb_at' t
                                 and sch_act_simple and st_tcb_at' awaiting_reply' t"
                   in hoare_strengthen_post [rotated])
            apply (clarsimp)
            apply (rule conjI)
             apply (clarsimp simp: invs'_def valid_state'_def valid_idle'_def)
             apply (rule conjI)
              apply clarsimp
             apply (clarsimp simp: obj_at'_def idle_tcb'_def pred_tcb_at'_def)
            apply clarsimp
            apply (rule conjI)
             apply (clarsimp simp: invs'_def valid_state'_def valid_idle'_def)
             apply (erule pred_tcb'_weakenE, clarsimp)
            apply (rule conjI)
             apply (clarsimp simp : invs'_def valid_state'_def valid_idle'_def pred_tcb_at'_def
                                    obj_at'_def idle_tcb'_def)
            apply (rule conjI)
             apply clarsimp
             apply (frule invs'_not_runnable_not_queued)
              apply (erule pred_tcb'_weakenE, clarsimp)
             apply (frule (1) not_tcbQueued_not_ksQ)
             apply simp
            apply clarsimp
           apply (wp cteDeleteOne_reply_pred_tcb_at hoare_drop_imp hoare_allI)+
  apply (clarsimp simp add: isReply_awaiting_reply' cte_wp_at_ctes_of)
  apply (auto dest!: st_tcb_idle'[rotated] simp:isCap_simps)
  done

lemma ct_active_runnable' [simp]:
  "ct_active' s \<Longrightarrow> ct_in_state' runnable' s"
  by (fastforce simp: ct_in_state'_def elim!: pred_tcb'_weakenE)

lemma valid_irq_node_tcbSchedEnqueue[wp]:
  "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s \<rbrace> tcbSchedEnqueue ptr
  \<lbrace>\<lambda>rv s'. valid_irq_node' (irq_node' s') s'\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add:valid_irq_node'_def )
  apply (wp unless_wp hoare_vcg_all_lift | wps)+
  apply (simp add:tcbSchedEnqueue_def)
  apply (wp unless_wp| simp)+
  apply (simp add:valid_irq_node'_def)
  done

lemma rescheduleRequired_valid_queues_but_ct_domain:
  "\<lbrace>\<lambda>s. Invariants_H.valid_queues s \<and> valid_objs' s
     \<and> (\<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s) \<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp)+
  done

lemma rescheduleRequired_valid_queues'_but_ct_domain:
  "\<lbrace>\<lambda>s. valid_queues' s
     \<and> (\<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s)
   \<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp | fastforce simp: valid_queues'_def)+
  done

lemma tcbSchedEnqueue_valid_action:
  "\<lbrace>\<lambda>s. \<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s\<rbrace>
  tcbSchedEnqueue ptr
  \<lbrace>\<lambda>rv s. \<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s\<rbrace>"
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply clarsimp
  done

abbreviation (input) "all_invs_but_sch_extra \<equiv>
    \<lambda>s. valid_pspace' s \<and> Invariants_H.valid_queues s \<and>
    sym_refs (state_refs_of' s) \<and>
    sym_refs (state_hyp_refs_of' s) \<and>
    if_live_then_nonz_cap' s \<and>
    if_unsafe_then_cap' s \<and>
    valid_idle' s \<and>
    valid_global_refs' s \<and>
    valid_arch_state' s \<and>
    valid_irq_node' (irq_node' s) s \<and>
    valid_irq_handlers' s \<and>
    valid_irq_states' s \<and>
    irqs_masked' s \<and>
    valid_machine_state' s \<and>
    cur_tcb' s \<and>
    untyped_ranges_zero' s \<and>
    valid_queues' s \<and>
    valid_pde_mappings' s \<and> pspace_domain_valid s \<and>
    ksCurDomain s \<le> maxDomain \<and> valid_dom_schedule' s \<and>
    (\<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s)"


lemma rescheduleRequired_all_invs_but_extra:
  "\<lbrace>\<lambda>s. all_invs_but_sch_extra s\<rbrace>
    rescheduleRequired \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
  apply (wp add:rescheduleRequired_ct_not_inQ
    rescheduleRequired_sch_act'
    rescheduleRequired_valid_queues_but_ct_domain
    rescheduleRequired_valid_queues'_but_ct_domain
    valid_irq_node_lift valid_irq_handlers_lift''
    irqs_masked_lift cur_tcb_lift)
  apply auto
  done

lemma threadSet_all_invs_but_sch_extra:
  shows      "\<lbrace> tcb_at' t and (\<lambda>s. (\<forall>p. t \<notin> set (ksReadyQueues s p))) and
                all_invs_but_sch_extra and sch_act_simple and
                K (ds \<le> maxDomain) \<rbrace>
                threadSet (tcbDomain_update (\<lambda>_. ds)) t
              \<lbrace>\<lambda>rv. all_invs_but_sch_extra \<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (wp threadSet_valid_pspace'T_P[where P = False and Q = \<top> and Q' = \<top>])
  apply (simp add:tcb_cte_cases_def)+
   apply (wp
     threadSet_valid_pspace'T_P
     threadSet_state_refs_of'T_P[where f'=id and P'=False and Q=\<top> and g'=id and Q'=\<top>]
     threadSet_state_hyp_refs_of'
     threadSet_idle'T
     threadSet_global_refsT
     threadSet_cur
     irqs_masked_lift
     valid_irq_node_lift
     valid_irq_handlers_lift''
     threadSet_ctes_ofT
     threadSet_not_inQ
     threadSet_valid_queues'_no_state
     threadSet_tcbDomain_update_ct_idle_or_in_cur_domain'
     threadSet_valid_queues
     threadSet_valid_dom_schedule'
     threadSet_iflive'T
     threadSet_ifunsafe'T
     untyped_ranges_zero_lift
     | simp add:tcb_cte_cases_def cteCaps_of_def o_def)+
   apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift threadSet_pred_tcb_no_state | simp)+
  apply (clarsimp simp:sch_act_simple_def o_def cteCaps_of_def)
  apply (intro conjI)
   apply fastforce+
  done

lemma threadSet_not_curthread_ct_domain:
  "\<lbrace>\<lambda>s. ptr \<noteq> ksCurThread s \<and> ct_idle_or_in_cur_domain' s\<rbrace> threadSet f ptr \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add:ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (wp hoare_vcg_imp_lift hoare_vcg_disj_lift | wps)+
  apply clarsimp
  done

lemma setDomain_invs':
  "\<lbrace>invs' and sch_act_simple and ct_active' and
  (tcb_at' ptr and
  (\<lambda>s. sch_act_not ptr s) and
  (\<lambda>y. domain \<le> maxDomain))\<rbrace>
  setDomain ptr domain \<lbrace>\<lambda>y. invs'\<rbrace>"
  apply (simp add:setDomain_def )
  apply (wp add: when_wp hoare_weak_lift_imp hoare_weak_lift_imp_conj rescheduleRequired_all_invs_but_extra
    tcbSchedEnqueue_valid_action hoare_vcg_if_lift2)
     apply (rule_tac Q = "\<lambda>r s. all_invs_but_sch_extra s \<and> curThread = ksCurThread s
      \<and> (ptr \<noteq> curThread \<longrightarrow> ct_not_inQ s \<and> sch_act_wf (ksSchedulerAction s) s \<and> ct_idle_or_in_cur_domain' s)"
      in hoare_strengthen_post[rotated])
      apply (clarsimp simp:invs'_def valid_state'_def st_tcb_at'_def[symmetric] valid_pspace'_def)
      apply (erule st_tcb_ex_cap'')
       apply simp
      apply (case_tac st,simp_all)[1]
     apply (rule hoare_strengthen_post[OF hoare_vcg_conj_lift])
       apply (rule threadSet_all_invs_but_sch_extra)
      prefer 2
      apply clarsimp
      apply assumption
     apply (wp hoare_weak_lift_imp threadSet_pred_tcb_no_state threadSet_not_curthread_ct_domain
               threadSet_tcbDomain_update_ct_not_inQ | simp)+
    apply (rule_tac Q = "\<lambda>r s. invs' s \<and> curThread = ksCurThread s \<and> sch_act_simple s
                             \<and> domain \<le> maxDomain
                             \<and> (ptr \<noteq> curThread \<longrightarrow> ct_not_inQ s \<and> sch_act_not ptr s)"
      in hoare_strengthen_post[rotated])
     apply (clarsimp simp:invs'_def valid_state'_def)
    apply (wp hoare_vcg_imp_lift)+
  apply (clarsimp simp:invs'_def valid_pspace'_def valid_state'_def)+
  done

lemma performInv_invs'[wp]:
  "\<lbrace>invs' and sch_act_simple
          and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))
          and ct_active' and valid_invocation' i\<rbrace>
     RetypeDecls_H.performInvocation block call i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding performInvocation_def
  apply (cases i)
  apply ((clarsimp simp: simple_sane_strg sch_act_simple_def
                         ct_not_ksQ sch_act_sane_def
                  | wp tcbinv_invs' arch_performInvocation_invs'
                       setDomain_invs'
                  | rule conjI | erule active_ex_cap')+)
  done

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
  "\<lbrace>\<top>\<rbrace>
     lookupExtraCaps t buffer info
   \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. cte_wp_at' ((=) (fst x) o cteCap) (snd x) s)\<rbrace>,-"
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
  apply (rule hoare_post_imp_R)
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
  apply (simp add: get_mrs_def cong: option.case_cong_weak[cong])
  apply (rule hoare_pre)
   apply (wp mapM_length | wpc | simp del: upt.simps)+
  apply (clarsimp simp: msgRegisters_unfold
                        msg_max_length_def)
  done

lemma st_tcb_at_idle_thread':
  "\<lbrakk> st_tcb_at' P (ksIdleThread s) s; valid_idle' s \<rbrakk>
        \<Longrightarrow> P IdleThreadState"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)

crunch tcb_at'[wp]: replyFromKernel "tcb_at' t"

lemma invs_weak_sch_act_wf_strg:
  "invs' s \<longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  by clarsimp

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

lemma setTCB_valid_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setObject a (tcb::tcb) \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = tcb,simplified])
  apply (clarsimp simp:updateObject_default_def assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def
    split:if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

crunch valid_duplicates'[wp]: threadSet "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt updateObject_default_inv)

crunch valid_duplicates'[wp]: addToBitmap "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt updateObject_default_inv)

lemma tcbSchedEnqueue_valid_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  tcbSchedEnqueue a \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (simp add: tcbSchedEnqueue_def unless_def setQueue_def | wp | wpc)+

crunch valid_duplicates'[wp]: rescheduleRequired "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt updateObject_default_inv)

crunch valid_duplicates'[wp]: setThreadState "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"

(*FIXME: move to Nondet_VCG.valid_validE_R *)
lemma handleInvocation_corres:
  "c \<longrightarrow> b \<Longrightarrow>
   corres (dc \<oplus> dc)
          (einvs and schact_is_rct and ct_active)
          (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
           (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_active')
          (handle_invocation c b)
          (handleInvocation c b)"
  apply (simp add: handle_invocation_def handleInvocation_def liftE_bindE)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule corres_split[OF getMessageInfo_corres])
        apply clarsimp
        apply (simp add: liftM_def cap_register_def capRegister_def)
        apply (rule corres_split_eqr[OF asUser_getRegister_corres])
          apply (rule syscall_corres)
                  apply (rule hinv_corres_assist, simp)
                 apply (clarsimp simp add: when_def)
                 apply (rule handleFault_corres)
                 apply simp
                apply (simp add: split_def)
                apply (rule corres_split[OF getMRs_corres])
                  apply (rule decodeInvocation_corres, simp_all)[1]
                   apply (fastforce simp: list_all2_map2 list_all2_map1 elim:  list_all2_mono)
                  apply (fastforce simp: list_all2_map2 list_all2_map1 elim:  list_all2_mono)
                 apply wp[1]
                apply (drule sym[OF conjunct1])
                apply simp
                apply wp[1]
               apply (clarsimp simp: when_def)
               apply (rule replyFromKernel_corres)
              apply (rule corres_split[OF setThreadState_corres])
                 apply simp
                apply (rule corres_splitEE)
                   apply (rule performInvocation_corres; simp)
                  apply simp
                  apply (rule corres_split[OF getThreadState_corres])
                    apply (rename_tac state state')
                    apply (case_tac state, simp_all)[1]
                    apply (fold dc_def)[1]
                    apply (rule corres_split)
                       apply (rule corres_when [OF refl replyFromKernel_corres])
                      apply (rule setThreadState_corres)
                      apply simp
                     apply (simp add: when_def)
                     apply (rule conjI, rule impI)
                      apply (rule reply_from_kernel_tcb_at)
                     apply (rule impI, wp+)
                 apply simp+
                 apply (wp hoare_drop_imps)+
                apply simp
                apply wp
               apply simp
               apply (rule_tac Q="\<lambda>rv. einvs and schact_is_rct and valid_invocation rve
                                   and (\<lambda>s. thread = cur_thread s)
                                   and st_tcb_at active thread"
                          in hoare_post_imp)
                apply (clarsimp simp: simple_from_active ct_in_state_def
                               elim!: st_tcb_weakenE)
               apply (wp sts_st_tcb_at' set_thread_state_schact_is_rct
                         set_thread_state_active_valid_sched)
              apply (rule_tac Q="\<lambda>rv. invs' and valid_invocation' rve'
                                      and (\<lambda>s. thread = ksCurThread s)
                                      and st_tcb_at' active' thread
                                      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                                      and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
                         in hoare_post_imp)
               apply (clarsimp simp: ct_in_state'_def)
               apply (frule(1) ct_not_ksQ)
               apply (clarsimp)
              apply (wp setThreadState_nonqueued_state_update
                        setThreadState_st_tcb setThreadState_rct)[1]
             apply (wp lec_caps_to lsft_ex_cte_cap_to
                    | simp add: split_def liftE_bindE[symmetric]
                                ct_in_state'_def ball_conj_distrib
                    | rule hoare_vcg_E_elim)+
   apply (clarsimp simp: tcb_at_invs invs_valid_objs
                         valid_tcb_state_def ct_in_state_def
                         simple_from_active invs_mdb)
   apply (clarsimp simp: msg_max_length_def word_bits_def)
   apply (erule st_tcb_ex_cap, clarsimp+)
   apply fastforce
  apply (clarsimp)
  apply (frule tcb_at_invs')
  apply (clarsimp simp: invs'_def valid_state'_def
                        ct_in_state'_def ct_not_inQ_def)
  apply (frule(1) valid_queues_not_tcbQueued_not_ksQ)
  apply (frule pred_tcb'_weakenE [where P=active' and P'=simple'], clarsimp)
  apply (frule(1) st_tcb_ex_cap'', fastforce)
  apply (clarsimp simp: valid_pspace'_def)
  apply (frule(1) st_tcb_at_idle_thread')
  apply (simp)
  done

lemma ts_Restart_case_helper':
  "(case ts of Structures_H.Restart \<Rightarrow> A | _ \<Rightarrow> B)
 = (if ts = Structures_H.Restart then A else B)"
  by (cases ts, simp_all)

lemma gts_imp':
  "\<lbrace>Q\<rbrace> getThreadState t \<lbrace>R\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. st_tcb_at' P t s \<longrightarrow> Q s\<rbrace> getThreadState t \<lbrace>\<lambda>rv s. P rv \<longrightarrow> R rv s\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply (erule hoare_vcg_disj_lift[rotated])
  apply (rule hoare_strengthen_post [OF gts_sp'])
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  done

crunch st_tcb_at'[wp]: replyFromKernel "st_tcb_at' P t"
crunch cap_to'[wp]: replyFromKernel "ex_nonz_cap_to' p"
crunch it'[wp]: replyFromKernel "\<lambda>s. P (ksIdleThread s)"
crunch sch_act_simple[wp]: replyFromKernel sch_act_simple
  (rule: sch_act_simple_lift)

lemma rfk_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s p)\<rbrace> replyFromKernel t x1 \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  apply (case_tac x1)
  apply (simp add: replyFromKernel_def)
  apply (wp)
  done

lemma hinv_invs'[wp]:
  "\<lbrace>invs' and ct_active' and
          (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
          (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
     handleInvocation calling blocking
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: handleInvocation_def split_def
                   ts_Restart_case_helper')
  apply (wp syscall_valid' setThreadState_nonqueued_state_update rfk_invs'
            hoare_vcg_all_lift hoare_weak_lift_imp)
         apply (simp add: if_apply_def2)
         apply (wp gts_imp' | simp)+
        apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp_R[rotated])
         apply clarsimp
         apply (subgoal_tac "thread \<noteq> ksIdleThread s", simp_all)[1]
          apply (fastforce elim!: pred_tcb'_weakenE st_tcb_ex_cap'')
         apply (clarsimp simp: valid_idle'_def valid_state'_def
                               invs'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)
        apply wp+
       apply (wp sts_invs_minor' setThreadState_st_tcb setThreadState_rct
                 ct_in_state_thread_state_lift' sts_st_tcb_at'_cases
        | clarsimp
        | strengthen ct_not_ksQ[rule_format]
        )+
    apply (frule(1) ct_not_ksQ)
    apply (simp add: conj_comms)
    apply (fastforce simp add: tcb_at_invs' ct_in_state'_def
                              simple_sane_strg
                              sch_act_simple_def
                       elim!: pred_tcb'_weakenE st_tcb_ex_cap''
                        dest: st_tcb_at_idle_thread')+
  done

crunch typ_at'[wp]: handleFault "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

lemmas handleFault_typ_ats[wp] = typ_at_lifts [OF handleFault_typ_at']

lemma handleSend_corres:
  "corres (dc \<oplus> dc)
          (einvs and schact_is_rct and ct_active)
          (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
           (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_active')
          (handle_send blocking) (handleSend blocking)"
  by (simp add: handle_send_def handleSend_def handleInvocation_corres)

lemma hs_invs'[wp]:
  "\<lbrace>invs' and ct_active' and
    (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   handleSend blocking \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (rule validE_valid)
  apply (simp add: handleSend_def)
  apply (wp | simp)+
  done

lemma getThreadCallerSlot_map:
  "getThreadCallerSlot t = return (cte_map (t, tcb_cnode_index 3))"
  by (simp add: getThreadCallerSlot_def locateSlot_conv
                cte_map_def tcb_cnode_index_def tcbCallerSlot_def
                cte_level_bits_def)

lemma tcb_at_cte_at_map:
  "\<lbrakk> tcb_at' t s; offs \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> cte_at' (cte_map (t, offs)) s"
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
  apply (drule tcb_cases_related)
  apply (auto elim: cte_wp_at_tcbI')
  done

lemma deleteCallerCap_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
     (delete_caller_cap t)
     (deleteCallerCap t)"
  apply (simp add: delete_caller_cap_def deleteCallerCap_def
                   getThreadCallerSlot_map)
  apply (rule corres_guard_imp)
    apply (rule_tac P'="cte_at' (cte_map (t, tcb_cnode_index 3))" in corres_symb_exec_r_conj)
       apply (rule_tac F="isReplyCap rv \<or> rv = capability.NullCap"
             and P="cte_wp_at (\<lambda>cap. is_reply_cap cap \<or> cap = cap.NullCap) (t, tcb_cnode_index 3)
                 and einvs"
             and P'="invs' and cte_wp_at' (\<lambda>cte. cteCap cte = rv)
                 (cte_map (t, tcb_cnode_index 3))" in corres_req)
        apply (clarsimp simp: cte_wp_at_caps_of_state state_relation_def)
        apply (drule caps_of_state_cteD)
        apply (drule(1) pspace_relation_cte_wp_at, clarsimp+)
        apply (clarsimp simp: cte_wp_at_ctes_of is_reply_cap_relation cap_relation_NullCapI)
       apply simp
       apply (rule corres_guard_imp, rule cap_delete_one_corres)
        apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
        apply (auto simp: can_fast_finalise_def)[1]
       apply (clarsimp simp: cte_wp_at_ctes_of)
      apply ((wp getCTE_wp')+ | simp add: getSlotCap_def)+
   apply clarsimp
   apply (frule tcb_at_cte_at[where ref="tcb_cnode_index 3"])
    apply clarsimp
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (frule tcb_cap_valid_caps_of_stateD, clarsimp)
   apply (drule(1) tcb_cnode_index_3_reply_or_null)
   apply (auto simp: can_fast_finalise_def is_cap_simps
              intro: tcb_at_cte_at_map tcb_at_cte_at)[1]
  apply clarsimp
  apply (frule_tac offs="tcb_cnode_index 3" in tcb_at_cte_at_map)
   apply (simp add: tcb_cap_cases_def)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma deleteCallerCap_invs[wp]:
  "\<lbrace>invs'\<rbrace> deleteCallerCap t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: deleteCallerCap_def getThreadCallerSlot_def
                locateSlot_conv)
  apply (wp cteDeleteOne_invs hoare_drop_imps)
  done

lemma deleteCallerCap_simple[wp]:
  "\<lbrace>st_tcb_at' simple' t\<rbrace> deleteCallerCap t' \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: deleteCallerCap_def getThreadCallerSlot_def
                   locateSlot_conv)
  apply (wp cteDeleteOne_st_tcb_at hoare_drop_imps | simp)+
  done

definition
  "isVCPUCap' cap \<equiv> \<exists>p. cap = ArchObjectCap (VCPUCap p)"

lemma cteDeleteOne_reply_cap_to''[wp]:
  "\<lbrace>ex_nonz_cap_to' p and
    cte_wp_at' (\<lambda>c. isReplyCap (cteCap c) \<or> isNullCap (cteCap c)) slot\<rbrace>
   cteDeleteOne slot
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: cteDeleteOne_def ex_nonz_cap_to'_def unless_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (rule hoare_assume_pre)
  apply (subgoal_tac "isReplyCap (cteCap cte) \<or> isNullCap (cteCap cte)")
   apply (wp hoare_vcg_ex_lift emptySlot_cte_wp_cap_other isFinalCapability_inv
        | clarsimp simp: finaliseCap_def isCap_simps | simp
        | wp (once) hoare_drop_imps)+
   apply (fastforce simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  done

lemma deleteCallerCap_nonz_cap:
  "\<lbrace>ex_nonz_cap_to' p and tcb_at' t and valid_objs'\<rbrace>
      deleteCallerCap t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
   apply (simp add: deleteCallerCap_def getSlotCap_def getThreadCallerSlot_map
                    locateSlot_conv )
  apply (rule hoare_pre)
  apply (wp cteDeleteOne_reply_cap_to'' getCTE_wp')
  apply clarsimp
  apply (frule_tac offs="tcb_cnode_index 3" in tcb_at_cte_at_map)
  apply (clarsimp simp: tcb_cap_cases_def)
  apply (auto simp: ex_nonz_cap_to'_def isCap_simps cte_wp_at_ctes_of)
  done

crunch sch_act_sane[wp]: cteDeleteOne sch_act_sane
  (wp: crunch_wps loadObject_default_inv getObject_inv
   simp: crunch_simps unless_def
   rule: sch_act_sane_lift)

crunch sch_act_sane[wp]: deleteCallerCap sch_act_sane
  (wp: crunch_wps)

lemma delete_caller_cap_valid_ep_cap:
  "\<lbrace>valid_cap (cap.EndpointCap r a b)\<rbrace> delete_caller_cap thread \<lbrace>\<lambda>rv. valid_cap (cap.EndpointCap r a b)\<rbrace>"
  apply (clarsimp simp: delete_caller_cap_def cap_delete_one_def valid_cap_def)
  apply (rule hoare_pre)
   by (wp get_cap_wp fast_finalise_typ_at abs_typ_at_lifts(1)
       | simp add: unless_def valid_cap_def)+

lemma handleRecv_isBlocking_corres':
   "corres dc (einvs and ct_in_state active
                    and (\<lambda>s. ex_nonz_cap_to (cur_thread s) s))
              (invs' and ct_in_state' simple'
                     and sch_act_sane
                     and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))
                     and (\<lambda>s. ex_nonz_cap_to' (ksCurThread s) s))
                    (handle_recv isBlocking) (handleRecv isBlocking)"
  (is "corres dc (?pre1) (?pre2) (handle_recv _) (handleRecv _)")
  apply (simp add: handle_recv_def handleRecv_def liftM_bind Let_def
                   cap_register_def capRegister_def
             cong: if_cong cap.case_cong capability.case_cong bool.case_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule corres_split_eqr[OF asUser_getRegister_corres])
        apply (rule corres_split_catch)
           apply (rule corres_cap_fault)
           apply (rule corres_splitEE[OF lookupCap_corres])
             apply (rule_tac P="?pre1 and tcb_at thread
                                and (\<lambda>s. (cur_thread s) = thread  )
                                and valid_cap rv"
                        and P'="?pre2 and tcb_at' thread and valid_cap' rv'" in corres_inst)
             apply (clarsimp split: cap_relation_split_asm arch_cap.split_asm split del: if_split
                              simp: lookup_failure_map_def whenE_def)
              apply (rule corres_guard_imp)
                apply (rename_tac rights)
                apply (case_tac "AllowRead \<in> rights"; simp)
                 apply (rule corres_split_nor[OF deleteCallerCap_corres])
                   apply (rule receiveIPC_corres)
                    apply (clarsimp)+
                  apply (wp delete_caller_cap_nonz_cap delete_caller_cap_valid_ep_cap)+
                apply (clarsimp)+
                apply (clarsimp simp: lookup_failure_map_def)+
              apply (clarsimp simp: valid_cap'_def capAligned_def)
             apply (rule corres_guard_imp)
               apply (rename_tac rights)
               apply (case_tac "AllowRead \<in> rights"; simp)
                apply (rule_tac r'=ntfn_relation in corres_splitEE)
                   apply clarsimp
                   apply (rule getNotification_corres)
                  apply (rule corres_if)
                    apply (clarsimp simp: ntfn_relation_def)
                   apply (clarsimp, rule receiveSignal_corres)
                    prefer 3
                    apply (rule corres_trivial)
                    apply (clarsimp simp: lookup_failure_map_def)+
                 apply (wp get_simple_ko_wp getNotification_wp | wpcw | simp)+
               apply (clarsimp simp: lookup_failure_map_def)
              apply (clarsimp simp: valid_cap_def ct_in_state_def)
             apply (clarsimp simp: valid_cap'_def capAligned_def)
            apply wp+
          apply (rule handleFault_corres)
          apply simp
         apply (wp get_simple_ko_wp | wpcw | simp)+
         apply (rule hoare_vcg_E_elim)
          apply (simp add: lookup_cap_def lookup_slot_for_thread_def)
          apply wp
           apply (simp add: split_def)
           apply (wp resolve_address_bits_valid_fault2)+
         apply (wp getNotification_wp | wpcw | simp add: valid_fault_def whenE_def split del: if_split)+
   apply (clarsimp simp add: ct_in_state_def  ct_in_state'_def conj_comms invs_valid_tcb_ctable
                             invs_valid_objs tcb_at_invs invs_psp_aligned invs_cur)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                        ct_in_state'_def sch_act_sane_not)
  done

lemma handleRecv_isBlocking_corres:
  "corres dc (einvs and ct_active)
             (invs' and ct_active' and sch_act_sane and
                    (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p)))
            (handle_recv isBlocking) (handleRecv isBlocking)"
  apply (rule corres_guard_imp)
    apply (rule handleRecv_isBlocking_corres')
   apply (clarsimp simp: ct_in_state_def)
   apply (fastforce elim!: st_tcb_weakenE st_tcb_ex_cap)
  apply (clarsimp simp: ct_in_state'_def invs'_def valid_state'_def)
  apply (frule(1) st_tcb_ex_cap'')
  apply (auto elim: pred_tcb'_weakenE)
  done

lemma lookupCap_refs[wp]:
  "\<lbrace>invs'\<rbrace> lookupCap t ref \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s\<rbrace>,-"
  by (simp add: lookupCap_def split_def | wp | simp add: o_def)+

lemma deleteCallerCap_ksQ_ct':
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane and
     (\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p) \<and> thread = ksCurThread s)\<rbrace>
      deleteCallerCap thread
   \<lbrace>\<lambda>rv s. thread \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. thread = ksCurThread s \<and> ksCurThread s \<notin> set (ksReadyQueues s p)"
            in hoare_strengthen_post)
   apply (wp deleteCallerCap_ct_not_ksQ)
    apply auto
  done

lemma hw_invs'[wp]:
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ex_nonz_cap_to' (ksCurThread s) s)
          and (\<lambda>s. ksCurThread s \<noteq> ksIdleThread s)
          and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   handleRecv isBlocking \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: handleRecv_def cong: if_cong)
  apply (rule hoare_pre)
   apply ((wp getNotification_wp | wpc | simp)+)[1]
                apply (clarsimp simp: ct_in_state'_def)
                apply ((wp deleteCallerCap_nonz_cap hoare_vcg_all_lift
                           deleteCallerCap_ksQ_ct'
                           hoare_lift_Pf2[OF deleteCallerCap_simple
                           deleteCallerCap_ct']
                      | wpc | simp)+)[1]
               apply simp
               apply (wp deleteCallerCap_nonz_cap hoare_vcg_all_lift
                         deleteCallerCap_ksQ_ct'
                         hoare_lift_Pf2[OF deleteCallerCap_simple
                         deleteCallerCap_ct']
                    | wpc | simp add: ct_in_state'_def whenE_def split del: if_split)+
     apply (rule validE_validE_R)
     apply (rule_tac Q="\<lambda>rv s. invs' s
                             \<and> sch_act_sane s
                             \<and> (\<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))
                             \<and> thread = ksCurThread s
                             \<and> ct_in_state' simple' s
                             \<and> ex_nonz_cap_to' thread s
                             \<and> thread \<noteq> ksIdleThread s
                            \<and> (\<forall>x \<in> zobj_refs' rv. ex_nonz_cap_to' x s)"
              and E="\<lambda>_ _. True"
           in hoare_post_impErr[rotated])
        apply (clarsimp simp: isCap_simps ct_in_state'_def pred_tcb_at' invs_valid_objs'
                              sch_act_sane_not obj_at'_def projectKOs pred_tcb_at'_def)
      apply (assumption)
     apply (wp)+
  apply (clarsimp)
  apply (auto elim: st_tcb_ex_cap'' pred_tcb'_weakenE
             dest!: st_tcb_at_idle_thread'
              simp: ct_in_state'_def sch_act_sane_def)
  done

lemma setSchedulerAction_obj_at'[wp]:
  "\<lbrace>obj_at' P p\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  unfolding setSchedulerAction_def
  by (wp, clarsimp elim!: obj_at'_pspaceI)

lemma handleYield_corres:
  "corres dc einvs (invs' and ct_active' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) handle_yield handleYield"
  apply (clarsimp simp: handle_yield_def handleYield_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply simp
      apply (rule corres_split[OF tcbSchedDequeue_corres])
        apply (rule corres_split[OF tcbSchedAppend_corres])
          apply (rule rescheduleRequired_corres)
         apply (wp weak_sch_act_wf_lift_linear tcbSchedDequeue_valid_queues | simp add: )+
   apply (simp add: invs_def valid_sched_def valid_sched_action_def
                cur_tcb_def tcb_at_is_etcb_at)
  apply clarsimp
  apply (frule ct_active_runnable')
  apply (clarsimp simp: invs'_def valid_state'_def ct_in_state'_def sch_act_wf_weak cur_tcb'_def
                        valid_pspace_valid_objs' valid_objs'_maxDomain tcb_in_cur_domain'_def)
  apply (erule(1) valid_objs_valid_tcbE[OF valid_pspace_valid_objs'])
  apply (simp add:valid_tcb'_def)
  done

lemma hy_invs':
  "\<lbrace>invs' and ct_active'\<rbrace> handleYield \<lbrace>\<lambda>r. invs' and ct_active'\<rbrace>"
  apply (simp add: handleYield_def)
  apply (wp ct_in_state_thread_state_lift'
            rescheduleRequired_all_invs_but_ct_not_inQ
            tcbSchedAppend_invs_but_ct_not_inQ' | simp)+
  apply (clarsimp simp add: invs'_def valid_state'_def ct_in_state'_def sch_act_wf_weak cur_tcb'_def
                   valid_pspace_valid_objs' valid_objs'_maxDomain tcb_in_cur_domain'_def
                   )
  apply (simp add:ct_active_runnable'[unfolded ct_in_state'_def])
  done

lemma getHSR_invs'[wp]:
  "valid invs' (doMachineOp getHSR) (\<lambda>_. invs')"
  by (simp add: getHSR_def doMachineOp_def split_def select_f_returns | wp)+

lemma getHDFAR_invs'[wp]:
  "valid invs' (doMachineOp getHDFAR) (\<lambda>_. invs')"
  by (simp add: getHDFAR_def doMachineOp_def split_def select_f_returns | wp)+

lemma hv_invs'[wp]: "\<lbrace>invs' and tcb_at' t'\<rbrace> handleVMFault t' vptr \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: ARM_HYP_H.handleVMFault_def
             cong: vmfault_type.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpcw | simp)+
  done

crunch nosch[wp]: handleVMFault "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: getFAR getDFSR getIFSR)

lemma active_from_running':
  "ct_running' s' \<Longrightarrow> ct_active' s'"
  by (clarsimp elim!: pred_tcb'_weakenE
               simp: ct_in_state'_def)+

lemma simple_from_running':
  "ct_running' s' \<Longrightarrow> ct_in_state' simple' s'"
  by (clarsimp elim!: pred_tcb'_weakenE
               simp: ct_in_state'_def)+

lemma handleReply_corres:
  "corres dc (einvs and ct_running) (invs' and ct_running')
         handle_reply handleReply"
  apply (simp add: handle_reply_def handleReply_def
                   getThreadCallerSlot_map
                   getSlotCap_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule corres_split[OF get_cap_corres])
        apply (rule_tac P="einvs and cte_wp_at ((=) caller_cap) (thread, tcb_cnode_index 3)
                                and K (is_reply_cap caller_cap \<or> caller_cap = cap.NullCap)
                                and tcb_at thread and st_tcb_at active thread
                                and valid_cap caller_cap"
                    and P'="invs' and tcb_at' thread
                              and valid_cap' (cteCap rv')
                              and cte_at' (cte_map (thread, tcb_cnode_index 3))"
                    in corres_inst)
        apply (auto split: cap_relation_split_asm arch_cap.split_asm bool.split
                   intro!: corres_guard_imp [OF deleteCallerCap_corres]
                           corres_guard_imp [OF doReplyTransfer_corres]
                           corres_fail
                     simp: valid_cap_def valid_cap'_def is_cap_simps assert_def is_reply_cap_to_def)[1]
        apply (fastforce simp: invs_def valid_state_def
                              cte_wp_at_caps_of_state st_tcb_def2
                        dest: valid_reply_caps_of_stateD)
       apply (wp get_cap_cte_wp_at get_cap_wp | simp add: cte_wp_at_eq_simp)+
   apply (intro conjI impI allI,
          (fastforce simp: invs_def valid_state_def
                   intro: tcb_at_cte_at)+)
      apply (clarsimp, frule tcb_at_invs)
      apply (fastforce dest: tcb_caller_cap simp: cte_wp_at_def)
     apply clarsimp
    apply (clarsimp simp: ct_in_state_def elim!: st_tcb_weakenE)
   apply (fastforce intro: cte_wp_valid_cap elim: cte_wp_at_weakenE)
  apply (fastforce intro: tcb_at_cte_at_map)
  done

lemma hr_invs'[wp]:
  "\<lbrace>invs' and sch_act_simple\<rbrace> handleReply \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: handleReply_def getSlotCap_def
                   getThreadCallerSlot_map getCurThread_def)
  apply (wp getCTE_wp | wpc | simp)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule ctes_of_valid', clarsimp+)
  apply (simp add: valid_cap'_def)
  apply (simp add: invs'_def cur_tcb'_def)
  done

crunch ksCurThread[wp]: handleReply "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps transferCapsToSlots_pres1 setObject_ep_ct
       setObject_ntfn_ct
   simp: unless_def crunch_simps
   ignore: transferCapsToSlots)

lemmas cteDeleteOne_st_tcb_at_simple'[wp] =
    cteDeleteOne_st_tcb_at[where P=simple', simplified]

crunch st_tcb_at_simple'[wp]: handleReply "st_tcb_at' simple' t'"
  (wp: hoare_post_taut crunch_wps sts_st_tcb_at'_cases
       threadSet_pred_tcb_no_state
     ignore: setThreadState)

lemmas handleReply_ct_in_state_simple[wp] =
    ct_in_state_thread_state_lift' [OF handleReply_ksCurThread
                                     handleReply_st_tcb_at_simple']


(* FIXME: move *)
lemma doReplyTransfer_st_tcb_at_active:
  "\<lbrace>st_tcb_at' active' t and tcb_at' t' and K (t \<noteq> t') and
    cte_wp_at' (\<lambda>cte. cteCap cte = (capability.ReplyCap t' False g)) sl\<rbrace>
    doReplyTransfer t t' sl g
   \<lbrace>\<lambda>rv. st_tcb_at' active' t\<rbrace>"
  apply (simp add: doReplyTransfer_def liftM_def)
  apply (wp setThreadState_st_tcb sts_pred_tcb_neq' cteDeleteOne_reply_pred_tcb_at
            hoare_drop_imps threadSet_pred_tcb_no_state hoare_exI
            doIPCTransfer_non_null_cte_wp_at2' | wpc | clarsimp simp:isCap_simps)+
  apply (fastforce)
  done

lemma hr_ct_active'[wp]:
  "\<lbrace>invs' and ct_active'\<rbrace> handleReply \<lbrace>\<lambda>rv. ct_active'\<rbrace>"
  apply (simp add: handleReply_def getSlotCap_def getCurThread_def
                   getThreadCallerSlot_def locateSlot_conv)
  apply (rule hoare_seq_ext, rename_tac cur_thread)
   apply (rule_tac t=cur_thread in ct_in_state'_decomp)
    apply (wpsimp wp: getCTE_wp)
    apply (fastforce simp: cte_wp_at_ctes_of)
   apply (wpsimp wp: getCTE_wp doReplyTransfer_st_tcb_at_active)+
  apply (fastforce simp: ct_in_state'_def cte_wp_at_ctes_of valid_cap'_def
                   dest: ctes_of_valid')
  done

lemma handleCall_corres:
  "corres (dc \<oplus> dc) (einvs and schact_is_rct and ct_active)
              (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
                (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
                ct_active')
         handle_call handleCall"
  by (simp add: handle_call_def handleCall_def liftE_bindE handleInvocation_corres)

lemma hc_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
      ct_active'\<rbrace>
     handleCall
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: handleCall_def)
  apply (wp)
  apply (clarsimp)
  done

lemma cteInsert_sane[wp]:
  "\<lbrace>sch_act_sane\<rbrace> cteInsert newCap srcSlot destSlot \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: sch_act_sane_def)
  apply (wp hoare_vcg_all_lift
            hoare_convert_imp [OF cteInsert_nosch cteInsert_ct])
  done

crunch sane [wp]: setExtraBadge sch_act_sane

crunch sane [wp]: transferCaps "sch_act_sane"
  (wp: transferCapsToSlots_pres1 crunch_wps
   simp: crunch_simps
   ignore: transferCapsToSlots)

lemma possibleSwitchTo_sane:
  "\<lbrace>\<lambda>s. sch_act_sane s \<and> t \<noteq> ksCurThread s\<rbrace> possibleSwitchTo t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: possibleSwitchTo_def setSchedulerAction_def curDomain_def
              cong: if_cong)
  apply (wp hoare_drop_imps | wpc)+
  apply (simp add: sch_act_sane_def)
  done

crunch sane [wp]: handleFaultReply sch_act_sane
  (wp: threadGet_inv hoare_drop_imps crunch_wps
   simp: crunch_simps
   ignore: setSchedulerAction)

crunch sane [wp]: doIPCTransfer sch_act_sane
  (  wp: threadGet_inv hoare_drop_imps crunch_wps
   simp: crunch_simps
   ignore: setSchedulerAction)

lemma doReplyTransfer_sane:
  "\<lbrace>\<lambda>s. sch_act_sane s \<and> t' \<noteq> ksCurThread s\<rbrace>
  doReplyTransfer t t' callerSlot g \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: doReplyTransfer_def liftM_def)
  apply (wp possibleSwitchTo_sane hoare_drop_imps hoare_vcg_all_lift|wpc)+
  apply simp
  done

lemma handleReply_sane:
  "\<lbrace>sch_act_sane\<rbrace> handleReply \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: handleReply_def getSlotCap_def getThreadCallerSlot_def locateSlot_conv)
  apply (rule hoare_pre)
   apply (wp haskell_assert_wp doReplyTransfer_sane getCTE_wp'| wpc)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma handleReply_nonz_cap_to_ct:
  "\<lbrace>ct_active' and invs' and sch_act_simple\<rbrace>
     handleReply
   \<lbrace>\<lambda>rv s. ex_nonz_cap_to' (ksCurThread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>rv. ct_active' and invs'"
               in hoare_post_imp)
   apply (auto simp: ct_in_state'_def elim: st_tcb_ex_cap'')[1]
  apply (wp | simp)+
  done

crunch ksQ[wp]: handleFaultReply "\<lambda>s. P (ksReadyQueues s p)"

lemma doReplyTransfer_ct_not_ksQ:
  "\<lbrace> invs' and sch_act_simple
           and tcb_at' thread and tcb_at' word
           and ct_in_state' simple'
           and (\<lambda>s. ksCurThread s \<noteq> word)
           and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set(ksReadyQueues s p))\<rbrace>
   doReplyTransfer thread word callerSlot g
   \<lbrace>\<lambda>rv s. \<forall>p. ksCurThread s \<notin> set(ksReadyQueues s p)\<rbrace>"
proof -
  have astct: "\<And>t p.
       \<lbrace>(\<lambda>s. ksCurThread s \<notin> set(ksReadyQueues s p) \<and> sch_act_sane s)
             and (\<lambda>s. ksCurThread s \<noteq> t)\<rbrace>
       possibleSwitchTo t \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set(ksReadyQueues s p)\<rbrace>"
    apply (rule hoare_weaken_pre)
     apply (wps possibleSwitchTo_ct')
     apply (wp possibleSwitchTo_ksQ')
    apply (clarsimp simp: sch_act_sane_def)
    done
  have stsct: "\<And>t st p.
       \<lbrace>(\<lambda>s. ksCurThread s \<notin> set(ksReadyQueues s p)) and sch_act_simple\<rbrace>
       setThreadState st t
       \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set(ksReadyQueues s p)\<rbrace>"
    apply (rule hoare_weaken_pre)
     apply (wps setThreadState_ct')
     apply (wp hoare_vcg_all_lift sts_ksQ)
    apply (clarsimp)
    done
  show ?thesis
    apply (simp add: doReplyTransfer_def)
    apply (wp, wpc)
            apply (wp astct stsct hoare_vcg_all_lift
                      cteDeleteOne_ct_not_ksQ hoare_drop_imp
                      hoare_lift_Pf2 [OF cteDeleteOne_sch_act_not cteDeleteOne_ct']
                      hoare_lift_Pf2 [OF doIPCTransfer_pred_tcb_at' doIPCTransfer_ct']
                      hoare_lift_Pf2 [OF doIPCTransfer_ksQ doIPCTransfer_ct']
                      hoare_lift_Pf2 [OF threadSet_ksQ threadSet_ct]
                      hoare_lift_Pf2 [OF handleFaultReply_ksQ handleFaultReply_ct']
                   | simp add: ct_in_state'_def)+
     apply (fastforce simp: sch_act_simple_def sch_act_sane_def ct_in_state'_def)+
    done
qed

lemma handleReply_ct_not_ksQ:
  "\<lbrace>invs' and sch_act_simple
           and ct_in_state' simple'
           and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   handleReply
   \<lbrace>\<lambda>rv s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (simp add: handleReply_def del: split_paired_All)
  apply (subst haskell_assert_def)
  apply (wp | wpc)+
  apply (wp doReplyTransfer_ct_not_ksQ getThreadCallerSlot_inv)+
    apply (rule_tac Q="\<lambda>cap.
                              (\<lambda>s. \<forall>p. ksCurThread s \<notin> set(ksReadyQueues s p))
                          and invs'
                          and sch_act_simple
                          and (\<lambda>s. thread = ksCurThread s)
                          and tcb_at' thread
                          and ct_in_state' simple'
                          and cte_wp_at' (\<lambda>c. cteCap c = cap) callerSlot"
             in hoare_post_imp)
     apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                           cte_wp_at_ctes_of valid_cap'_def
                    dest!: ctes_of_valid')
    apply (wp getSlotCap_cte_wp_at getThreadCallerSlot_inv)+
  apply (clarsimp)
  done

crunch valid_etcbs[wp]: possible_switch_to  "valid_etcbs"
crunch valid_etcbs[wp]: handle_recv "valid_etcbs"
  (wp: crunch_wps simp: crunch_simps)

lemma handleReply_handleRecv_corres:
  "corres dc (einvs and ct_running)
             (invs' and ct_running' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
         (do x \<leftarrow> handle_reply; handle_recv True od)
         (do x \<leftarrow> handleReply; handleRecv True od)"
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor[OF handleReply_corres])
      apply (rule handleRecv_isBlocking_corres')
     apply (wp handle_reply_nonz_cap_to_ct handleReply_sane
               handleReply_nonz_cap_to_ct handleReply_ct_not_ksQ handle_reply_valid_sched)+
   apply (fastforce simp: ct_in_state_def ct_in_state'_def simple_sane_strg
                    elim!: st_tcb_weakenE st_tcb_ex_cap')
  apply (clarsimp simp: ct_in_state'_def)
  apply (frule(1) ct_not_ksQ)
  apply (fastforce elim: pred_tcb'_weakenE)
  done

lemma handleHypervisorFault_corres:
  "corres dc (einvs and  st_tcb_at active thread and ex_nonz_cap_to thread)
             (invs' and sch_act_not thread
                    and (\<lambda>s. \<forall>p. thread \<notin> set(ksReadyQueues s p))
                    and st_tcb_at' simple' thread and ex_nonz_cap_to' thread)
          (handle_hypervisor_fault thread fault)
          (handleHypervisorFault thread fault)"
  apply (cases fault; clarsimp simp add: handleHypervisorFault_def returnOk_def2)
  apply (corresK corres: handleFault_corres)
   apply (simp add: ucast_id)
  apply (clarsimp simp: valid_fault_def)
  done

lemma dmo_machine_rest_lift:
  "(\<And>s m. P (s\<lparr>ksMachineState := ksMachineState s\<lparr>machine_state_rest := m\<rparr>\<rparr>) = P s) \<Longrightarrow>
  \<lbrace>P\<rbrace> doMachineOp (machine_op_lift f') \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: doMachineOp_def machine_op_lift_def machine_rest_lift_def in_monad)
  apply (clarsimp simp: select_f_def ignore_failure_def split: if_split_asm)
  done

lemma hvmf_invs_lift:
  "(\<And>s m. P (s\<lparr>ksMachineState := ksMachineState s\<lparr>machine_state_rest := m\<rparr>\<rparr>) = P s) \<Longrightarrow>
   \<lbrace>P\<rbrace> handleVMFault t flt \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding handleVMFault_def
  by (wpsimp wp: dmo_machine_rest_lift asUser_inv
           simp: getHSR_def getHDFAR_def addressTranslateS1_def
                 doMachineOp_bind getRestartPC_def getRegister_def)

lemma hvmf_invs_etc:
  "\<lbrace>invs' and sch_act_not t and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p)) and st_tcb_at' simple' t and
    ex_nonz_cap_to' t\<rbrace>
    handleVMFault t f
   \<lbrace>\<lambda>_ _. True\<rbrace>,
   \<lbrace>\<lambda>_. invs' and sch_act_not t and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p)) and
        st_tcb_at' simple' t and ex_nonz_cap_to' t\<rbrace>"
  apply (rule hvmf_invs_lift)
  apply (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def)
  done

lemma handleEvent_corres:
  "corres (dc \<oplus> dc) (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and
                       schact_is_rct)
                      (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and
                       (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
                       (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
                      (handle_event event) (handleEvent event)"
  (is "?handleEvent_corres")
proof -
  have hw:
    "\<And>isBlocking. corres dc (einvs and ct_running and (\<lambda>s. scheduler_action s = resume_cur_thread))
               (invs' and ct_running'
                      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
               (handle_recv isBlocking) (handleRecv isBlocking)"
    apply (rule corres_guard_imp [OF handleRecv_isBlocking_corres])
     apply (clarsimp simp: ct_in_state_def ct_in_state'_def
                     elim!: st_tcb_weakenE pred_tcb'_weakenE
                     dest!: ct_not_ksQ)+
    done
    show ?thesis
      apply (case_tac event)
          apply (simp_all add: handleEvent_def)

          apply (rename_tac syscall)
          apply (case_tac syscall)
          apply (auto intro: corres_guard_imp[OF handleSend_corres]
                             corres_guard_imp[OF hw]
                             corres_guard_imp [OF handleReply_corres]
                             corres_guard_imp[OF handleReply_handleRecv_corres]
                             corres_guard_imp[OF handleCall_corres]
                             corres_guard_imp[OF handleYield_corres]
                             active_from_running active_from_running'
                      simp: simple_sane_strg)[8]
         apply (rule corres_underlying_split)
            apply (rule corres_guard_imp[OF getCurThread_corres], simp+)
           apply (rule handleFault_corres)
           apply simp
          apply (simp add: valid_fault_def)
          apply wp
          apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE
                           simp: ct_in_state_def)
         apply wp
         apply (clarsimp)
         apply (frule(1) ct_not_ksQ)
         apply (auto simp: ct_in_state'_def sch_act_simple_def
                           sch_act_sane_def
                     elim: pred_tcb'_weakenE st_tcb_ex_cap'')[1]
        apply (rule corres_underlying_split)
           apply (rule corres_guard_imp, rule getCurThread_corres, simp+)
          apply (rule handleFault_corres)
          apply (simp add: valid_fault_def)
         apply wp
         apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE
                          simp: ct_in_state_def valid_fault_def)
        apply wp
        apply clarsimp
        apply (frule(1) ct_not_ksQ)
        apply (auto simp: ct_in_state'_def sch_act_simple_def
                          sch_act_sane_def
                    elim: pred_tcb'_weakenE st_tcb_ex_cap'')[1]
       apply (rule corres_guard_imp)
         apply (rule corres_split_eqr[where R="\<lambda>rv. einvs"
                                      and R'="\<lambda>rv s. \<forall>x. rv = Some x \<longrightarrow> R'' x s"
                                      for R''])
            apply (rule corres_machine_op)
            apply (rule corres_Id; wpsimp)
           apply (case_tac rv, simp_all add: doMachineOp_return)[1]
           apply (rule handleInterrupt_corres)
          apply (wp hoare_vcg_all_lift
                    doMachineOp_getActiveIRQ_IRQ_active'
                   | simp
                   | simp add: imp_conjR | wp (once) hoare_drop_imps)+
       apply (clarsimp simp: invs'_def valid_state'_def ct_not_inQ_def valid_queues_def
                             valid_queues_no_bitmap_def)
       apply (erule allE)+
       apply (erule conjE, drule (1) bspec)
       apply (clarsimp simp: obj_at'_def inQ_def)
      apply (rule_tac corres_underlying_split)
         apply (rule corres_guard_imp, rule getCurThread_corres, simp+)
        apply (rule corres_split_catch)
           apply (rule handleVMFault_corres)
          apply (erule handleFault_corres)
         apply (wp handle_vm_fault_valid_fault)
        apply (wp hvmf_invs_etc)
       apply wp
       apply (clarsimp simp: simple_from_running tcb_at_invs)
       apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE simp: ct_in_state_def)
      apply wp
      apply (clarsimp)
      apply (frule(1) ct_not_ksQ)
      apply (fastforce simp: simple_sane_strg sch_act_simple_def ct_in_state'_def
                  elim: st_tcb_ex_cap'' pred_tcb'_weakenE)
         apply (rule corres_underlying_split)
            apply (rule corres_guard_imp[OF getCurThread_corres], simp+)
           apply (rule handleHypervisorFault_corres)
          apply wp
          apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE
                           simp: ct_in_state_def)
         apply wp
         apply (clarsimp)
         apply (frule(1) ct_not_ksQ)
         apply (auto simp: ct_in_state'_def sch_act_simple_def
                           sch_act_sane_def
                     elim: pred_tcb'_weakenE st_tcb_ex_cap'')[1]
      done
  qed

crunches handleVMFault
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  and norq[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (ignore: getFAR getDFSR getIFSR)

crunches handleVMFault, handleHypervisorFault
  for cap_to'[wp]: "ex_nonz_cap_to' t"
  and ksit[wp]: "\<lambda>s. P (ksIdleThread s)"
  (ignore: getFAR getDFSR getIFSR wp: crunch_wps)

(* FIXME *)
lemma hv_stuff'[wp]:
  "\<lbrace>\<lambda>s. st_tcb_at' simple' thread s \<and> ex_nonz_cap_to' thread s \<and> thread \<noteq> ksIdleThread s\<rbrace>
  handleVMFault t f
  \<lbrace>\<lambda>rv s. st_tcb_at' simple' thread s \<and> ex_nonz_cap_to' thread s \<and> thread \<noteq> ksIdleThread s\<rbrace>"
  unfolding ARM_HYP_H.handleVMFault_def
  by (wpsimp wp: getDFSR_inv getHSR_inv getHDFAR_inv getRestartPC_inv det_getRestartPC asUser_inv)

lemma hh_invs'[wp]:
  "\<lbrace>invs' and sch_act_not p and (\<lambda>s. \<forall>a b. p \<notin> set (ksReadyQueues s (a, b))) and
    st_tcb_at' simple' p and ex_nonz_cap_to' p and (\<lambda>s. p \<noteq> ksIdleThread s)\<rbrace>
  handleHypervisorFault p t \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: ARM_HYP_H.handleHypervisorFault_def)
  apply (cases t; wpsimp)
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
  "\<lbrakk>invs' s; ct_running' s\<rbrakk> \<Longrightarrow> ksCurThread s \<noteq> ksIdleThread s"
  apply (rule ct_not_idle')
   apply (fastforce simp: invs'_def valid_state'_def ct_in_state'_def
                   elim: pred_tcb'_weakenE)+
  done

lemma ct_active_not_idle'[simp]:
  "\<lbrakk>invs' s; ct_active' s\<rbrakk> \<Longrightarrow> ksCurThread s \<noteq> ksIdleThread s"
  apply (rule ct_not_idle')
   apply (fastforce simp: invs'_def valid_state'_def ct_in_state'_def
                   elim: pred_tcb'_weakenE)+
  done

lemma deleteCallerCap_st_tcb_at_runnable[wp]:
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> deleteCallerCap t' \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
  apply (simp add: deleteCallerCap_def getThreadCallerSlot_def
                   locateSlot_conv)
  apply (wp cteDeleteOne_tcb_at_runnable' hoare_drop_imps | simp)+
  done

crunches handleFault, receiveSignal, receiveIPC, asUser
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: hoare_drop_imps crunch_wps simp: crunch_simps)

lemma handleRecv_ksCurThread[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s) \<rbrace> handleRecv b \<lbrace>\<lambda>rv s. P (ksCurThread s) \<rbrace>"
  unfolding handleRecv_def
  by ((simp, wp hoare_drop_imps) | wpc | wpsimp wp: hoare_drop_imps)+

lemma he_invs'[wp]:
  "\<lbrace>invs' and
      (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and
      (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   handleEvent event
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have nidle: "\<And>s. invs' s \<and> ct_active' s \<longrightarrow> ksCurThread s \<noteq> ksIdleThread s"
    by (clarsimp)
  show ?thesis
    apply (case_tac event, simp_all add: handleEvent_def)
        apply (rename_tac syscall)
        apply (case_tac syscall,
               (wp handleReply_sane handleReply_nonz_cap_to_ct handleReply_ksCurThread
                   handleReply_ct_not_ksQ
                | clarsimp simp: active_from_running' simple_from_running' simple_sane_strg simp del: split_paired_All
                | rule conjI active_ex_cap'
                | drule ct_not_ksQ[rotated]
                | strengthen nidle)+)
        apply (rule hoare_strengthen_post,
               rule hoare_weaken_pre,
               rule hy_invs')
         apply (simp add: active_from_running')
        apply simp
       apply (simp add: active_from_running')
       apply (wp
                 | rule conjI
                 | erule pred_tcb'_weakenE st_tcb_ex_cap''
                 | clarsimp simp: tcb_at_invs ct_in_state'_def simple_sane_strg sch_act_simple_def
                 | drule st_tcb_at_idle_thread'
                 | drule ct_not_ksQ[rotated]
                 | wpc | wp (once) hoare_drop_imps hoare_vcg_all_lift)+
  done
qed

lemma inv_irq_IRQInactive:
  "\<lbrace>\<top>\<rbrace> performIRQControl irqcontrol_invocation
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (simp add: performIRQControl_def)
  apply (rule hoare_pre)
   apply (wpc|wp|simp add: ARM_HYP_H.performIRQControl_def)+
  done

lemma inv_arch_IRQInactive:
  "\<lbrace>\<top>\<rbrace> Arch.performInvocation invocation
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  by (wpsimp simp: ARM_HYP_H.performInvocation_def performARMMMUInvocation_def performARMVCPUInvocation_def)

lemma retype_pi_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace> RetypeDecls_H.performInvocation blocking call v
   -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (simp add: Retype_H.performInvocation_def)
  apply (rule hoare_pre)
   apply (wpc |
          wp inv_tcb_IRQInactive inv_cnode_IRQInactive inv_irq_IRQInactive
             inv_untyped_IRQInactive inv_arch_IRQInactive |
          simp)+
  done

lemma hi_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace> handleInvocation call blocking
    -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (simp add: handleInvocation_def split_def)
  apply (wp syscall_valid' retype_pi_IRQInactive)
  done

lemma handleSend_IRQInactive:
  "\<lbrace>invs'\<rbrace> handleSend blocking
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (simp add: handleSend_def)
  apply (rule hoare_pre)
   apply (wp hi_IRQInactive)
  apply (simp add: invs'_def valid_state'_def)
  done

lemma handleCall_IRQInactive:
  "\<lbrace>invs'\<rbrace> handleCall
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  apply (simp add: handleCall_def)
  apply (rule hoare_pre)
   apply (wp hi_IRQInactive)
  apply (simp add: invs'_def valid_state'_def)
  done

end

end
