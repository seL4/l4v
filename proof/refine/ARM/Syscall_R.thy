(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Refinement for handleEvent and syscalls
*)

theory Syscall_R
imports Tcb_R Arch_R Interrupt_R SchedContextInv_R
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
lemma dec_domain_inv_corres:
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
    apply (rule_tac r'="\<lambda>domain domain'. domain = domain'" and R="\<lambda>_. \<top>" and R'="\<lambda>_. \<top>" in corres_splitEE)
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
     apply (rule whenE_throwError_corres)
     apply (simp+)[2]
     apply (rule corres_returnOkTT)
     apply (wp | simp)+
done

lemma decode_invocation_corres:
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
              apply (rule corres_guard_imp, rule dec_untyped_inv_corres)
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
            apply (rule dec_cnode_inv_corres, simp+)
           apply (simp add: valid_cap_def word_bits_def)
          apply simp
         \<comment> \<open>ThreadCap\<close>
         apply (simp add: isCap_defs Let_def CanModify_def
                     split del: if_split cong: if_cong)
         apply (clarsimp simp add: o_def)
         apply (rule corres_guard_imp)
           apply (rule decode_tcb_inv_corres, rule refl,
                  simp_all add: valid_cap_def valid_cap'_def)[3]
         apply (simp add: split_def)
         apply (rule list_all2_conj)
          apply (simp add: list_all2_map2 list_all2_map1)
         apply assumption
        \<comment> \<open>DomainCap\<close>
        apply (clarsimp simp: isCap_defs)
        apply (rule corres_guard_imp)
          apply (rule dec_domain_inv_corres)
           apply (simp+)[4]
       \<comment> \<open>SchedContextCap\<close>
       apply (clarsimp simp: isCap_defs o_def)
       apply (rule corres_guard_imp, erule decode_sc_inv_corres; clarsimp simp: valid_cap_def)
      \<comment> \<open>SchedControlCap\<close>
      apply (clarsimp simp: isCap_defs o_def)
      apply (rule corres_guard_imp, rule decode_sc_ctrl_inv_corres; clarsimp)
     \<comment> \<open>IRQControl\<close>
     apply (simp add: isCap_defs o_def)
     apply (rule corres_guard_imp, rule decode_irq_control_corres, simp+)[1]
    \<comment> \<open>IRQHandler\<close>
    apply (simp add: isCap_defs o_def)
    apply (rule corres_guard_imp, rule decode_irq_handler_corres, simp+)[1]
   \<comment> \<open>Zombie\<close>
   apply (simp add: isCap_defs)
  \<comment> \<open>Arch\<close>
  apply (clarsimp simp only: cap_relation.simps)
  apply (clarsimp simp add: isCap_defs Let_def o_def)
  apply (rule corres_guard_imp [OF dec_arch_inv_corres])
      apply (simp_all add: list_all2_map2 list_all2_map1)+
  done

declare mapME_Nil [simp] (* FIXME RT: make global *)

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
    apply (rule corres_splitEE [OF _ corres_cap_fault])
       prefer 2
       \<comment> \<open>switched over to argument of corres_cap_fault\<close>
       apply (rule lcs_corres, simp)
      apply (rule corres_split_deprecated [OF _ lipcb_corres])
        apply (rule corres_splitEE [OF _ lec_corres])
            apply (rule corres_returnOkTT)
            apply simp+
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
     apply (wp static_imp_wp getObject_tcb_wp hoare_vcg_all_lift)+
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
     (valid_tcbs and pspace_aligned and pspace_distinct and weak_valid_sched_action and tcb_at tptr)
     (invs' and (\<lambda>_. new_dom \<le> maxDomain))
     (set_domain tptr new_dom)
     (setDomain tptr new_dom)"
  apply (rule corres_gen_asm2)
  apply (simp add: set_domain_def setDomain_def thread_set_domain_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF gct_corres])
      apply (rule corres_split[OF tcbSchedDequeue_corres])
        apply (rule corres_split[OF threadset_corresT])
             apply (clarsimp simp: tcb_relation_def)
            apply (clarsimp simp: tcb_cap_cases_def)
           apply (clarsimp simp: tcb_cte_cases_def)
          apply (rule corres_split[OF isSchedulable_corres])
            apply (rule corres_split[OF corres_when[OF _ tcbSchedEnqueue_corres]], simp)
              apply (rule corres_when[OF _ rescheduleRequired_corres], simp)
             apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2
                               thread_set_weak_valid_sched_action threadSet_valid_tcbs'
                               threadSet_vrq_inv threadSet_vrq'_inv threadSet_valid_queues_no_state
                               threadSet_valid_queues'_no_state)+
      apply (clarsimp cong: conj_cong)
      apply (rule hoare_vcg_conj_lift, strengthen valid_tcb'_tcbDomain_update, wpsimp)
      apply (wpsimp wp: tcbSchedDequeue_valid_queues tcbSchedDequeue_nonq hoare_vcg_all_lift)
     apply wpsimp+
  apply (frule cross_relF[OF _ tcb_at'_cross_rel], fastforce)
  apply (frule invs'_valid_tcbs', clarsimp)
  apply (frule obj_at_ko_at', clarsimp)
  apply (frule tcb_ko_at_valid_objs_valid_tcb', fastforce)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def valid_tcb'_def invs'_def valid_state'_def)
  done

lemma pinv_corres:
  "\<lbrakk> inv_relation i i'; call \<longrightarrow> block \<rbrakk> \<Longrightarrow>
   corres (dc \<oplus> (=))
     (einvs and valid_machine_time and valid_invocation i
            and schact_is_rct
            and current_time_bounded 2
            and ct_active
            and ct_released
            and ct_not_in_release_q
            and (\<lambda>s. (\<exists>w w2 b c. i = Invocations_A.InvokeEndpoint w w2 b c) \<longrightarrow> st_tcb_at simple (cur_thread s) s))
     (invs' and sch_act_simple and valid_invocation' i' and ct_active' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
     (perform_invocation block call can_donate i) (performInvocation block call can_donate i')"
  apply (simp add: performInvocation_def)
  apply add_sym_refs
  apply (case_tac i)

             apply (clarsimp simp: o_def liftE_bindE)
             apply (rule corres_stateAssertE_add_assertion)
             apply (rule corres_guard_imp)

               apply (rule corres_split_norE[OF corres_returnOkTT])
                  apply simp
                 apply (rule corres_rel_imp, rule inv_untyped_corres)
                  apply simp
                 apply (case_tac x, simp_all)[1]
             apply wpsimp+
             apply (clarsimp simp: sym_refs_asrt_def)

            apply (clarsimp simp: liftE_bindE)
            apply (rule corres_guard_imp)
              apply (rule corres_split_deprecated [OF _ gct_corres])
                apply simp
                apply (rule corres_split_deprecated [OF _ sendIPC_corres])
                   apply (rule corres_trivial)
                   apply simp
                  apply simp
                 apply wp+
             apply (clarsimp simp: invs_def valid_sched_def valid_state_def valid_pspace_def
                                   fault_tcbs_valid_states_to_except_set schact_is_rct_sane
                                   ct_in_state_def released_sc_tcb_at_def active_sc_tcb_at_def2)
             apply (intro conjI)
              apply (fastforce elim: st_tcb_ex_cap)
             apply (fastforce simp: pred_tcb_at_def obj_at_def dest: invs_cur_sc_tcb_symref)
            apply (clarsimp simp: pred_conj_def invs'_def cur_tcb'_def simple_sane_strg
                                  sch_act_simple_def)
           apply (rule corres_guard_imp)
             apply (simp add: liftE_bindE)
             apply (rule corres_split_deprecated [OF _ sendSignal_corres])
               apply (rule corres_trivial)
               apply (simp add: returnOk_def)
              apply wpsimp+
          apply (rule corres_guard_imp)
            apply (rule corres_split_eqr [OF _ gct_corres])
              apply (rule corres_split_nor [OF _ doReplyTransfer_corres])
                apply (rule corres_trivial, simp)
               apply wp+
           apply (clarsimp simp: tcb_at_invs)
          apply simp
         apply (clarsimp simp: liftME_def)
         apply (rule corres_guard_imp)
           apply (erule tcbinv_corres)
          apply (fastforce simp: current_time_bounded_def)+
        \<comment> \<open>domain cap\<close>
        apply (clarsimp simp: invoke_domain_def)
        apply (rule corres_guard_imp)
          apply (rule corres_split_deprecated [OF _ setDomain_corres])
            apply (rule corres_trivial, simp)
           apply (wp)+
         apply ((clarsimp | fastforce)+)[3]
       \<comment> \<open>SchedContext\<close>
       apply (rule corres_guard_imp)
         apply (rule corres_splitEE)
            prefer 2
            apply (simp)
            apply (erule invoke_sched_context_corres)
           apply (rule corres_trivial, simp add: returnOk_def)
          apply (wpsimp+)[4]
      \<comment> \<open>SchedControl\<close>
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE)
           prefer 2
           apply (simp)
           apply (erule invokeSchedControlConfigureFlags_corres)
          apply (rule corres_trivial, simp add: returnOk_def)
         apply (wpsimp+)[4]
     \<comment> \<open>CNodes\<close>
     apply clarsimp
     apply (rule corres_stateAssertE_add_assertion)
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE [OF _ inv_cnode_corres])
          apply (rule corres_trivial, simp add: returnOk_def)
         apply assumption
        apply wp+
      apply (clarsimp+)[2]
     apply (clarsimp simp: sym_refs_asrt_def)
    apply (clarsimp simp: liftME_def[symmetric] o_def dc_def[symmetric])
    apply (rule corres_guard_imp, rule invoke_irq_control_corres; fastforce)
   apply (clarsimp simp: liftME_def[symmetric] o_def dc_def[symmetric])
   apply (rule corres_guard_imp, rule invoke_irq_handler_corres; fastforce)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule inv_arch_corres, assumption)
   apply (clarsimp+)[2]
  done

crunches sendSignal, setDomain
  for tcb_at'[wp]: "tcb_at' t"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T t s)"
  (simp: crunch_simps wp: crunch_wps)

crunches restart, bindNotification, performTransfer, invokeTCB, doReplyTransfer,
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
  by (cases i; simp; wpsimp wp: invokeArch_tcb_at' stateAssertE_inv simp: pred_tcb_at')

crunches setThreadState
  for obj_at_ntfn[wp]: "obj_at' (\<lambda>ntfn. P (ntfnBoundTCB ntfn) (ntfnObj ntfn)) ntfnptr"
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

context begin interpretation Arch . (*FIXME: arch_split*)

lemma sts_valid_inv'[wp]:
  "setThreadState st t \<lbrace>valid_invocation' i\<rbrace>"
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
           apply wpsimp
          apply (rename_tac bindCap, case_tac bindCap; wpsimp)
         apply (rename_tac bindCap, case_tac bindCap; wpsimp)
        apply wpsimp
       apply ((wpsimp | wps)+)[1]
       \<comment>\<open>end InvokeSchedContext\<close>
      apply (rename_tac schedcontrolinvocation)
      apply (case_tac schedcontrolinvocation; wpsimp wp: hoare_vcg_ex_lift)
     apply (rename_tac cnode_invocation)
     apply (case_tac cnode_invocation; wpsimp simp: cte_wp_at_ctes_of)
    apply (rename_tac irqcontrol_invocation)
    apply (case_tac irqcontrol_invocation; simp)
     apply (rename_tac arch_irqhandler_issue)
     apply (case_tac arch_irqhandler_issue; wpsimp simp: irq_issued'_def)
    apply (wpsimp simp: irq_issued'_def)
   apply (rename_tac irqhandler_invocation)
   apply (case_tac irqhandler_invocation; wpsimp wp: hoare_vcg_ex_lift simp: comp_def)
  apply (wpsimp wp: sts_valid_arch_inv')
  done

crunches decodeDomainInvocation, decodeSchedContextInvocation, decodeSchedControlInvocation
  for inv[wp]: P
  (wp: crunch_wps simp: crunch_simps)

lemma decode_inv_inv'[wp]:
  "\<lbrace>P\<rbrace> decodeInvocation label args cap_index slot cap excaps first_phase buffer \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding decodeInvocation_def Let_def
  by (wpsimp split: capability.split_asm simp: isCap_defs)

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
  apply (simp add:ucast_nat_def[symmetric])
  apply (rule word_of_nat_le)
  apply (simp add:numDomains_def maxDomain_def)
  done

lemma decode_inv_wf'[wp]:
  "\<lbrace>valid_cap' cap and invs' and sch_act_simple
          and cte_wp_at' ((=) cap \<circ> cteCap) slot and real_cte_at' slot
          and (\<lambda>s. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
          and (\<lambda>s. \<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
          and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs' (fst cap) (irq_node' s). ex_cte_cap_to' r s)
          and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>zobj_refs' (fst cap). ex_nonz_cap_to' r s)
          and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile>' fst x)
          and (\<lambda>s. \<forall>x \<in> set excaps. real_cte_at' (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to' isCNodeCap (snd x) s)
          and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' (badge_derived' (fst x) \<circ> cteCap) (snd x) s)
          and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
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

crunch it[wp]: handleFaultReply "\<lambda>s. P (ksIdleThread s)"

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
        apply (wp hoare_vcg_all_lift static_imp_wp | simp add:ball_conj_distrib)+
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

crunches doFaultTransfer, setMRs
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
      apply (rule_tac Q="\<lambda>_. invs'"
                  and E="\<lambda>_. invs' and st_tcb_at' active' tptr and sch_act_not tptr
                             and (\<lambda>s. False \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> None) tptr s)
                             and ex_nonz_cap_to' tptr
                             and (\<lambda>s. \<exists>n\<in>dom tcb_cte_cases. cte_wp_at' (\<lambda>cte. cteCap cte
                                                                               = cteCap (tcbTimeoutHandler tcb))
                                                                        (tptr + n) s)"
                   in hoare_post_impErr)
        apply (rule sfi_invs_plus')
       apply (wpsimp wp: getTCB_wp
                   simp: isValidTimeoutHandler_def)+
  apply (clarsimp simp: cte_wp_at'_obj_at' tcb_cte_cases_def  projectKOs obj_at'_def)
  done

crunches isValidTimeoutHandler
  for inv[wp]: P

lemma doReplyTransfer_invs'[wp]:
  "\<lbrace>invs' and tcb_at' sender and reply_at' replyPtr and sch_act_simple\<rbrace>
   doReplyTransfer sender replyPtr grant
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (simp add: doReplyTransfer_def liftM_def)
  apply (rule hoare_seq_ext[OF _ get_reply_sp'], rename_tac reply)
  apply (case_tac "replyTCB reply"; clarsimp)
   apply wpsimp
  apply (rename_tac receiver)
  apply (rule hoare_seq_ext[OF _ gts_sp'])
  apply (rule hoare_if)
   apply wpsimp
  apply (rule_tac B="\<lambda>_. ?pre and st_tcb_at' ((=) Inactive) receiver and ex_nonz_cap_to' receiver"
               in hoare_seq_ext[rotated])
   apply (wpsimp wp: replyRemove_invs')
   apply (clarsimp simp: pred_tcb_at'_def)
   apply (fastforce intro: if_live_then_nonz_capE'
                     simp: ko_wp_at'_def obj_at'_def projectKOs isReply_def)
  apply (rule hoare_seq_ext[OF _ threadGet_sp], rename_tac fault)
  apply (rule_tac B="\<lambda>_. ?pre and tcb_at' receiver and ex_nonz_cap_to' receiver"
         in hoare_seq_ext)
   apply (wpsimp wp: possibleSwitchTo_invs' handleTimeout_invs' threadGet_wp hoare_drop_imps)
   apply (fastforce simp: runnable_eq_active' obj_at'_def)
  apply (case_tac fault; clarsimp)
   apply (wpsimp wp: doIPCTransfer_invs setThreadState_Running_invs')
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (rule_tac Q="?pre and st_tcb_at' ((=) Inactive) receiver
                          and ex_nonz_cap_to' receiver and (\<lambda>s. receiver \<noteq> ksIdleThread s)"
               in hoare_weaken_pre[rotated])
  using global'_no_ex_cap apply fastforce
  apply (rule hoare_seq_ext_skip, solves \<open>wpsimp wp: threadSet_fault_invs' threadSet_st_tcb_at2\<close>)+
  apply clarsimp
  apply (intro conjI impI)
   apply (wpsimp wp: setThreadState_Restart_invs')
   apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (wpsimp wp: sts_invs_minor')
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma ct_active_runnable' [simp]:
  "ct_active' s \<Longrightarrow> ct_in_state' runnable' s"
  by (fastforce simp: ct_in_state'_def elim!: pred_tcb'_weakenE)

lemma valid_irq_node_tcbSchedEnqueue[wp]:
  "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s \<rbrace> tcbSchedEnqueue ptr
  \<lbrace>\<lambda>rv s'. valid_irq_node' (irq_node' s') s'\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add:valid_irq_node'_def )
  apply (wp hoare_unless_wp hoare_vcg_all_lift | wps)+
  apply (simp add:tcbSchedEnqueue_def)
  apply (wp hoare_unless_wp| simp)+
  apply (simp add:valid_irq_node'_def)
  done

lemma tcbSchedEnqueue_valid_action:
  "\<lbrace>\<lambda>s. \<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s\<rbrace>
  tcbSchedEnqueue ptr
  \<lbrace>\<lambda>rv s. \<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s\<rbrace>"
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply clarsimp
  done

abbreviation (input) "all_invs_but_sch_extra \<equiv>
    \<lambda>s. valid_pspace' s \<and> valid_queues s \<and>
    sym_refs (list_refs_of_replies' s) \<and>
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
    valid_release_queue s \<and>
    valid_release_queue' s \<and>
    valid_pde_mappings' s \<and> pspace_domain_valid s \<and>
    ksCurDomain s \<le> maxDomain \<and> valid_dom_schedule' s \<and>
    (\<forall>x. ksSchedulerAction s = SwitchToThread x \<longrightarrow> st_tcb_at' runnable' x s)"

lemma rescheduleRequired_all_invs_but_extra:
  "\<lbrace>\<lambda>s. all_invs_but_sch_extra s\<rbrace>
    rescheduleRequired \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (rule hoare_pre)
  apply (wp add: rescheduleRequired_ct_not_inQ irqs_masked_lift cur_tcb_lift
                 rescheduleRequired_sch_act' rescheduleRequired_valid_queues
                 rescheduleRequired_valid_queues'
                 valid_irq_node_lift valid_irq_handlers_lift'')
  apply (auto simp: o_def)
  done

lemma threadSet_all_invs_but_sch_extra:
  "\<lbrace> tcb_at' t and (\<lambda>s. (\<forall>p. t \<notin> set (ksReadyQueues s p))) and
     all_invs_but_sch_extra and sch_act_simple and
     K (ds \<le> maxDomain) \<rbrace>
   threadSet (tcbDomain_update (\<lambda>_. ds)) t
   \<lbrace>\<lambda>_. all_invs_but_sch_extra \<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (wp threadSet_valid_pspace'T_P[where P = False and Q = \<top> and Q' = \<top>])
  apply (simp add:tcb_cte_cases_def)+
   apply (wp threadSet_valid_pspace'T_P
             threadSet_state_refs_of'T_P[where f'=id and P'=False and Q=\<top> and g'=id and Q'=\<top>]
             threadSet_idle'T threadSet_global_refsT threadSet_cur irqs_masked_lift
             valid_irq_node_lift valid_irq_handlers_lift'' threadSet_ctes_ofT threadSet_not_inQ
             threadSet_valid_queues'_no_state threadSet_valid_queues threadSet_valid_dom_schedule'
             threadSet_iflive'T threadSet_ifunsafe'T untyped_ranges_zero_lift
             threadSet_valid_release_queue threadSet_valid_release_queue'
          | simp add: tcb_cte_cases_def cteCaps_of_def o_def
          | intro allI)+
   apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift threadSet_pred_tcb_no_state | simp)+
  by (fastforce simp: sch_act_simple_def o_def cteCaps_of_def valid_release_queue'_def obj_at'_def)

lemma threadSet_not_curthread_ct_domain:
  "\<lbrace>\<lambda>s. ptr \<noteq> ksCurThread s \<and> ct_idle_or_in_cur_domain' s\<rbrace> threadSet f ptr \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add:ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (wp hoare_vcg_imp_lift hoare_vcg_disj_lift | wps)+
  apply clarsimp
  done

lemma setDomain_invs':
  "\<lbrace> invs' and sch_act_simple and tcb_at' ptr and K (domain \<le> maxDomain)\<rbrace>
   setDomain ptr domain
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply rescheduleRequired_invs' [wp del]
  apply (simp add: setDomain_def)
  apply (wp add: hoare_when_wp static_imp_wp static_imp_conj_wp rescheduleRequired_all_invs_but_extra
                 tcbSchedEnqueue_valid_action hoare_vcg_if_lift2 valid_irq_handlers_lift')
      apply (wpsimp wp: isSchedulable_wp)
     apply (rule_tac Q = "\<lambda>r s. all_invs_but_sch_extra s \<and> curThread = ksCurThread s
      \<and> (ptr \<noteq> curThread \<longrightarrow> ct_not_inQ s \<and> sch_act_wf (ksSchedulerAction s) s \<and> ct_idle_or_in_cur_domain' s)"
      in hoare_strengthen_post[rotated])
      apply (clarsimp simp:invs'_def valid_state'_def st_tcb_at'_def[symmetric] valid_pspace'_def)
      apply (intro conjI allI impI)
         apply (erule valid_objs'_valid_tcbs')
        apply (clarsimp simp: comp_def)
       apply (clarsimp simp: isSchedulable_bool_def pred_map_conj)
       apply (erule st_tcb_ex_cap''[where P=runnable', rotated], fastforce)
       apply (clarsimp simp: pred_tcb_at'_equiv pred_map_def opt_map_def)
      apply (clarsimp simp: isSchedulable_bool_def pred_tcb_at'_equiv pred_map_def opt_map_def)
     apply (rule hoare_strengthen_post[OF hoare_vcg_conj_lift])
       apply (rule threadSet_all_invs_but_sch_extra)
      prefer 2
      apply clarsimp
      apply assumption
     apply (wp static_imp_wp threadSet_pred_tcb_no_state threadSet_not_curthread_ct_domain
               threadSet_tcbDomain_update_ct_not_inQ | simp)+
    apply (rule_tac Q = "\<lambda>r s. invs' s \<and> curThread = ksCurThread s \<and> sch_act_simple s
                             \<and> domain \<le> maxDomain
                             \<and> (ptr \<noteq> curThread \<longrightarrow> ct_not_inQ s)
                             \<and> (\<forall>d p. ptr \<notin> set (ksReadyQueues s (d, p)))"
      in hoare_strengthen_post[rotated])
     apply (clarsimp simp:invs'_def valid_state'_def)
    apply (wp hoare_vcg_imp_lift tcbSchedDequeue_nonq hoare_vcg_all_lift)+
  apply (clarsimp simp:invs'_def valid_pspace'_def valid_state'_def)+
  done

lemma performInv_invs'[wp]:
  "\<lbrace>invs' and sch_act_simple
          and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))
          and ct_active' and valid_invocation' i\<rbrace>
     RetypeDecls_H.performInvocation block call can_donate i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding performInvocation_def
  apply (cases i)
  apply ((clarsimp simp: simple_sane_strg sch_act_simple_def
                         ct_not_ksQ sch_act_sane_def
                  | wp tcbinv_invs' arch_performInvocation_invs'
                       setDomain_invs'
                  | rule conjI | erule active_ex_cap')+)
  sorry (* FIXME RT: invokeSchedContext_invs and InvokeSchedControl_invs' *)

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
  "\<lbrace>\<top>\<rbrace> lookupCapAndSlot t cptr \<lbrace>\<lambda>rv. cte_wp_at' ((=) (fst rv) \<circ> cteCap) (snd rv)\<rbrace>,-"
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
  apply (simp add: get_mrs_def)
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
  "setObject a (tcb::tcb) \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = tcb,simplified])
  apply (clarsimp simp: updateObject_default_def assert_def bind_def
                        alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
                        assert_opt_def return_def fail_def typeError_def
                  split: if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

crunch valid_duplicates'[wp]: threadSet "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: updateObject_default_inv)

crunch valid_duplicates'[wp]: addToBitmap "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: updateObject_default_inv)

lemma tcbSchedEnqueue_valid_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  tcbSchedEnqueue a \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (simp add:tcbSchedEnqueue_def unless_def setQueue_def | wp | wpc)+

crunch valid_duplicates'[wp]: rescheduleRequired "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt updateObject_default_inv crunch_wps)

crunch valid_duplicates'[wp]: setThreadState "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"

crunches reply_from_kernel
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and valid_objs[wp]: valid_objs
  (simp: crunch_simps wp: crunch_wps)

crunches replyFromKernel
  for valid_objs'[wp]: valid_objs'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  (simp: crunch_simps wp: crunch_wps)

(* Note: the preconditions on the abstract side are based on those of pinv_corres. *)
lemma hinv_corres:
  "call \<longrightarrow> blocking \<Longrightarrow>
   cptr = to_bl cptr' \<Longrightarrow>
   corres (dc \<oplus> dc)
          (einvs and valid_machine_time and schact_is_rct and ct_active and ct_released
           and (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and ct_not_in_release_q
           and current_time_bounded 2)
          (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
          (handle_invocation call blocking can_donate first_phase cptr)
          (handleInvocation call blocking can_donate first_phase cptr')"
  apply (simp add: handle_invocation_def handleInvocation_def liftE_bindE)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_eqr [OF _ gct_corres])
      apply (rule corres_split [OF get_mi_corres])
        apply (rule syscall_corres)
                apply (rule hinv_corres_assist, simp)
               apply (rule corres_when[OF _ hf_corres]; simp)
              apply (simp only: split_def)
              apply (rule corres_split_deprecated [OF _ get_mrs_corres])
                 apply (rule decode_invocation_corres; simp)
                  apply (fastforce simp: list_all2_map2 list_all2_map1 elim: list_all2_mono)
                 apply (fastforce simp: list_all2_map2 list_all2_map1 elim: list_all2_mono)
                apply simp
               apply wp
              apply (drule sym[OF conjunct1], simp, wp)
             apply (clarsimp simp: when_def)
             apply (rule rfk_corres)
            apply (rule corres_split [OF sts_corres], simp)
              apply (rule corres_splitEE [OF _ pinv_corres])
                  apply simp
                  apply (rule corres_split [OF gts_corres])
                    apply (rename_tac state state')
                    apply (case_tac state, simp_all)[1]
                    apply (fold dc_def)[1]
                    apply (rule corres_split [OF _ sts_corres])
                       apply simp
                       apply (rule corres_when [OF refl rfk_corres])
                      apply simp
                     apply (clarsimp simp: pred_conj_def, strengthen valid_objs_valid_tcbs)
                     apply wpsimp
                    apply (clarsimp simp: pred_conj_def, strengthen valid_objs'_valid_tcbs')
                    apply wpsimp+
               apply (strengthen invs_valid_objs invs_psp_aligned invs_distinct)
               apply (clarsimp cong: conj_cong)
               apply (wpsimp wp: hoare_drop_imp)
              apply (rule_tac Q="tcb_at' thread and invs'" in hoare_post_imp_dc2)
               apply wpsimp
              apply (clarsimp simp: invs'_def valid_state'_def)
             apply simp
             apply (rule_tac Q="\<lambda>rv. einvs and valid_machine_time and schact_is_rct
                                 and valid_invocation rve
                                 and (\<lambda>s. thread = cur_thread s)
                                 and st_tcb_at active thread
                                 and ct_not_in_release_q and ct_released
                                 and current_time_bounded 2"
                        in hoare_post_imp)
              apply (clarsimp simp: simple_from_active ct_in_state_def schact_is_rct_def
                             elim!: st_tcb_weakenE)
             apply (wp sts_st_tcb_at' set_thread_state_simple_sched_action
                       set_thread_state_active_valid_sched set_thread_state_schact_is_rct_strong)
            apply (rule_tac Q="\<lambda>rv. invs' and valid_invocation' rve'
                                    and (\<lambda>s. thread = ksCurThread s)
                                    and st_tcb_at' active' thread
                                    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                                    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
                   in hoare_post_imp)
             apply (clarsimp simp: ct_in_state'_def)
             apply (frule (1) ct_not_ksQ)
             apply (clarsimp)
            apply (wp setThreadState_nonqueued_state_update
                      setThreadState_st_tcb setThreadState_rct)
           apply clarsimp
           apply (wp lec_caps_to lsft_ex_cte_cap_to
                  | simp add: split_def liftE_bindE[symmetric]
                              ct_in_state'_def ball_conj_distrib
                  | rule hoare_vcg_E_elim)+
   apply (clarsimp simp: msg_max_length_def word_bits_def)
   apply (frule schact_is_rct_sane)
   apply (frule invs_valid_objs)
   apply (frule valid_objs_valid_tcbs)
   apply (clarsimp simp: invs_def cur_tcb_def valid_state_def
                         valid_sched_def valid_pspace_def ct_in_state_def simple_from_active)
   apply (erule st_tcb_ex_cap, clarsimp+)
   apply fastforce
  apply (clarsimp cong: conj_cong)
  apply (subgoal_tac "is_schedulable_bool (cur_thread s) s")
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                         cur_tcb'_def)
   apply (frule valid_objs'_valid_tcbs')
   apply (frule ct_active_cross, fastforce, fastforce, simp)
   apply (clarsimp simp: ct_in_state'_def cong: conj_cong)
   apply (frule pred_tcb'_weakenE [where P=active' and P'=simple'], clarsimp)
   apply (frule(1) st_tcb_ex_cap'', fastforce)
   apply (clarsimp simp: valid_pspace'_def schact_is_rct_def)
   apply (frule state_relation_schact, simp)
   apply (subgoal_tac "isSchedulable_bool (ksCurThread s') s'")
    apply (clarsimp simp: isSchedulable_bool_def pred_map_conj)
    apply (frule(1) st_tcb_at_idle_thread', simp)
   apply (frule curthread_relation, simp)
   apply (frule_tac t1="cur_thread s" in cross_relF[OF _ isSchedulable_bool_cross_rel];
          simp add: invs_def valid_state_def valid_pspace_def)
  apply (clarsimp simp: is_schedulable_bool_def2 ct_in_state_def runnable_eq_active)
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
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  done

crunches replyFromKernel
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
  "\<lbrace>invs' and ct_isSchedulable and
          (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
          (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
     handleInvocation calling blocking can_donate first_phase cptr
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: handleInvocation_def split_def
                   ts_Restart_case_helper')
  apply (wp syscall_valid' setThreadState_nonqueued_state_update rfk_invs'
            hoare_vcg_all_lift static_imp_wp)
         apply simp
         apply (intro conjI impI)
          apply (wp gts_imp' | simp)+
        apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp_R[rotated])
         apply clarsimp
         apply (subgoal_tac "thread \<noteq> ksIdleThread s", simp_all)[1]
          apply (fastforce elim!: pred_tcb'_weakenE st_tcb_ex_cap'')
         apply (clarsimp simp: valid_idle'_def valid_state'_def
                               invs'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)
        apply wp+
       apply (rule_tac Q="\<lambda>rv'. invs' and valid_invocation' rv
                                and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
                                and (\<lambda>s. ksCurThread s = thread)
                                and st_tcb_at' active' thread"
                  in hoare_post_imp)
        apply (clarsimp simp: ct_in_state'_def)
        apply (frule(1) ct_not_ksQ)
        apply (clarsimp)
       apply (wp sts_invs_minor' setThreadState_st_tcb setThreadState_rct | simp)+
    apply (clarsimp)
    apply (frule(1) ct_not_ksQ)
    apply (fastforce simp add: tcb_at_invs' ct_in_state'_def
                              simple_sane_strg
                              sch_act_simple_def
                       elim!: pred_tcb'_weakenE st_tcb_ex_cap''
                        dest: st_tcb_at_idle_thread')+
  done

(* NOTE: This is a good candidate for corressimp at some point. For now there are some missing
         lemmas regarding corresK and liftM. *)
lemma getCapReg_corres:
  "corres (\<lambda>x y. x = to_bl y) ct_active ct_active'
          (get_cap_reg cap_register) (getCapReg ARM_H.capRegister)"
  apply (simp add: get_cap_reg_def getCapReg_def cap_register_def capRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF gct_corres], simp)
      apply (rule corres_rel_imp)
       apply (rule user_getreg_corres)
      apply (wpsimp simp: ct_in_state_def ct_in_state'_def)+
  done

lemma hs_corres:
  "corres (dc \<oplus> dc)
          (einvs and valid_machine_time and schact_is_rct and ct_active and
           ct_released and (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and
           ct_not_in_release_q and current_time_bounded 2)
          (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
           (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_active')
          (handle_send blocking) (handleSend blocking)"
  apply (simp add: handle_send_def handleSend_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_liftEE[OF getCapReg_corres])
      apply (simp, rule hinv_corres; simp)
     apply (wpsimp simp: getCapReg_def)+
  done

lemma hs_invs'[wp]:
  "\<lbrace>invs' and ct_isSchedulable and
    (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   handleSend blocking \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (rule validE_valid)
  apply (simp add: handleSend_def getCapReg_def)
  apply (wp | simp)+
  done

lemma tcb_at_cte_at_map:
  "\<lbrakk> tcb_at' t s; offs \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> cte_at' (cte_map (t, offs)) s"
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
  apply (drule tcb_cases_related)
  apply (auto elim: cte_wp_at_tcbI')
  done

crunches tcbSchedEnqueue
  for sch_act_sane[wp]: sch_act_sane
  (rule: sch_act_sane_lift)

lemma possibleSwitchTo_sch_act_sane:
  "\<lbrace> sch_act_sane and (\<lambda>s. t \<noteq> ksCurThread s) \<rbrace> possibleSwitchTo t \<lbrace>\<lambda>_. sch_act_sane \<rbrace>"
  unfolding possibleSwitchTo_def curDomain_def  inReleaseQueue_def
  apply (wpsimp wp: threadGet_wp crunch_wps)
  apply (fastforce simp: obj_at'_def sch_act_sane_def)
  done

crunch sch_act_sane[wp]: cteDeleteOne sch_act_sane
  (wp: crunch_wps loadObject_default_inv getObject_inv
   simp: crunch_simps unless_def
   rule: sch_act_sane_lift)

lemma hw_corres':
   "corres dc (einvs and ct_in_state active
                    and (\<lambda>s. ex_nonz_cap_to (cur_thread s) s))
              (invs' and ct_in_state' simple'
                     and sch_act_sane
                     and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))
                     and (\<lambda>s. ex_nonz_cap_to' (ksCurThread s) s))
                    (handle_recv isBlocking canReply) (handleRecv isBlocking canReply)"
  (is "corres dc (?pre1) (?pre2) (handle_recv _ _) (handleRecv _ _)")
  apply (simp add: handle_recv_def handleRecv_def liftM_bind Let_def
                   cap_register_def capRegister_def
             cong: if_cong cap.case_cong capability.case_cong bool.case_cong split del: if_split)
  sorry (*
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr [OF _ gct_corres])
      apply (rule corres_split_eqr [OF _ user_getreg_corres])
        apply (rule corres_split_catch)
           apply (erule hf_corres)
          apply (rule corres_cap_fault)
          apply (rule corres_splitEE [OF _ lc_corres])
            apply (rule_tac P="?pre1 and tcb_at thread
                               and (\<lambda>s. (cur_thread s) = thread  )
                               and valid_cap rv"
                       and P'="?pre2 and tcb_at' thread and valid_cap' rv'" in corres_inst)
            apply (clarsimp split: cap_relation_split_asm arch_cap.split_asm split del: if_split
                             simp: lookup_failure_map_def whenE_def)
             apply (rule corres_guard_imp)
               apply (rename_tac rights)
                apply (case_tac "AllowRead \<in> rights"; simp)
                 apply (rule corres_split_nor[OF _ delete_caller_cap_corres])
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
                  apply (rule corres_if)
                    apply (clarsimp simp: ntfn_relation_def)
                   apply (clarsimp, rule receive_signal_corres)
                    prefer 3
                    apply (rule corres_trivial)
                    apply (clarsimp simp: lookup_failure_map_def)+
                 apply (rule get_ntfn_corres)
                apply (wp get_simple_ko_wp getNotification_wp | wpcw | simp)+
              apply (clarsimp simp: lookup_failure_map_def)
             apply (clarsimp simp: valid_cap_def ct_in_state_def)
            apply (clarsimp simp: valid_cap'_def capAligned_def)
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
  done *)

lemma hw_corres:
  "corres dc (einvs and ct_active)
             (invs' and ct_active' and sch_act_sane and
                    (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p)))
            (handle_recv isBlocking canReply) (handleRecv isBlocking canReply)"
  apply (rule corres_guard_imp)
    apply (rule hw_corres')
   apply (clarsimp simp: ct_in_state_def)
   apply (fastforce elim!: st_tcb_weakenE st_tcb_ex_cap)
  apply (clarsimp simp: ct_in_state'_def invs'_def valid_state'_def)
  apply (frule(1) st_tcb_ex_cap'')
  apply (auto elim: pred_tcb'_weakenE)
  done

lemma lookupCap_refs[wp]:
  "\<lbrace>invs'\<rbrace> lookupCap t ref \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs' rv. ex_nonz_cap_to' r s\<rbrace>,-"
  by (simp add: lookupCap_def split_def | wp | simp add: o_def)+

lemma hw_invs'[wp]:
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ex_nonz_cap_to' (ksCurThread s) s)
          and (\<lambda>s. ksCurThread s \<noteq> ksIdleThread s)
          and (\<lambda>s. \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   handleRecv isBlocking canReply \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: handleRecv_def cong: if_cong split del: if_split)
  sorry (*
  apply (rule hoare_pre)
   apply ((wp getNotification_wp | wpc | simp)+)[1]
                apply (clarsimp simp: ct_in_state'_def)
                apply ((wp hoare_vcg_all_lift
                      | wpc | simp)+)[1]
               apply simp
               apply (wp hoare_vcg_all_lift
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
  done *)

lemma setSchedulerAction_obj_at'[wp]:
  "\<lbrace>obj_at' P p\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  unfolding setSchedulerAction_def
  by (wp, clarsimp elim!: obj_at'_pspaceI)

lemma hy_corres:
  "corres dc einvs (invs' and ct_active' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)) handle_yield handleYield"
  apply (clarsimp simp: handle_yield_def handleYield_def)
  sorry (*
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ gct_corres])
      apply simp
      apply (rule corres_split_deprecated[OF _ tcbSchedDequeue_corres])
        apply (rule corres_split_deprecated[OF _ tcbSchedAppend_corres])
          apply (rule rescheduleRequired_corres)
         apply (wp weak_sch_act_wf_lift_linear tcbSchedDequeue_valid_queues | simp add: )+
   apply (simp add: invs_def valid_sched_def valid_sched_action_def
                cur_tcb_def tcb_at_is_etcb_at)
  apply clarsimp
  apply (frule ct_active_runnable')
  apply (clarsimp simp: invs'_def valid_state'_def ct_in_state'_def sch_act_wf_weak cur_tcb'_def
                        valid_pspace_valid_objs' valid_objs'_maxDomain tcb_in_cur_domain'_def)
  apply (erule(1) valid_objs_valid_tcbE'[OF valid_pspace_valid_objs'])
  apply (simp add:valid_tcb'_def)
  done *)

lemma hy_invs':
  "\<lbrace>invs' and ct_active'\<rbrace> handleYield \<lbrace>\<lambda>r. invs' and ct_active'\<rbrace>"
  apply (simp add: handleYield_def)
  apply (wp ct_in_state_thread_state_lift'
            rescheduleRequired_all_invs_but_ct_not_inQ
            tcbSchedAppend_invs_but_ct_not_inQ' | simp)+
  apply (clarsimp simp add: invs'_def valid_state'_def ct_in_state'_def sch_act_wf_weak cur_tcb'_def
                   valid_pspace_valid_objs' valid_objs'_maxDomain tcb_in_cur_domain'_def)
  sorry (*
  apply (simp add:ct_active_runnable'[unfolded ct_in_state'_def])
  done *)

lemma getDFSR_invs'[wp]:
  "valid invs' (doMachineOp getDFSR) (\<lambda>_. invs')"
  by (simp add: getDFSR_def doMachineOp_def split_def select_f_returns | wp)+

lemma getFAR_invs'[wp]:
  "valid invs' (doMachineOp getFAR) (\<lambda>_. invs')"
  by (simp add: getFAR_def doMachineOp_def split_def select_f_returns | wp)+

lemma getIFSR_invs'[wp]:
  "valid invs' (doMachineOp getIFSR) (\<lambda>_. invs')"
  by (simp add: getIFSR_def doMachineOp_def split_def select_f_returns | wp)+

lemma hv_invs'[wp]: "\<lbrace>invs' and tcb_at' t'\<rbrace> handleVMFault t' vptr \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: ARM_H.handleVMFault_def
             cong: vmfault_type.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpcw | simp)+
  done

crunch nosch[wp]: handleVMFault "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: getFAR getDFSR getIFSR)

lemma hv_inv_ex':
  "\<lbrace>P\<rbrace> handleVMFault t vp \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: ARM_H.handleVMFault_def
             cong: vmfault_type.case_cong)
  apply (rule hoare_pre)
   apply (wp dmo_inv' getDFSR_inv getFAR_inv getIFSR_inv getRestartPC_inv
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


crunch ksCurThread[wp]: cteDeleteOne "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps
   simp: crunch_simps unless_def)

lemmas cteDeleteOne_st_tcb_at_simple'[wp] =
    cteDeleteOne_st_tcb_at[where P=simple', simplified]

lemma hc_corres:
  "corres (dc \<oplus> dc) (einvs and valid_machine_time and schact_is_rct and ct_active and
                      ct_released and (\<lambda>s. active_sc_tcb_at (cur_thread s) s) and
                      ct_not_in_release_q and current_time_bounded 2)
              (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
                (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
                ct_active')
         handle_call handleCall"
  apply (simp add: handle_call_def handleCall_def liftE_bindE hinv_corres)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCapReg_corres])
      apply (simp, rule hinv_corres; simp)
     apply (wpsimp simp: getCapReg_def)+
  done

lemma hc_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
      ct_isSchedulable\<rbrace>
   handleCall
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding handleCall_def getCapReg_def by wpsimp

lemma cteInsert_sane[wp]:
  "\<lbrace>sch_act_sane\<rbrace> cteInsert newCap srcSlot destSlot \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: sch_act_sane_def)
  apply (wp hoare_vcg_all_lift
            hoare_convert_imp [OF cteInsert_nosch cteInsert_ct])
  done

crunches setExtraBadge, transferCaps, handleFaultReply, doIPCTransfer
  for sch_act_sane [wp]: sch_act_sane
  (wp: crunch_wps simp: crunch_simps)

crunches handleFaultReply
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s p)"

lemma hh_corres:
  "corres dc (einvs and  st_tcb_at active thread and ex_nonz_cap_to thread
                   and (%_. valid_fault f))
             (invs' and sch_act_not thread
                    and (\<lambda>s. \<forall>p. thread \<notin> set(ksReadyQueues s p))
                    and st_tcb_at' simple' thread and ex_nonz_cap_to' thread)
          (handle_hypervisor_fault w fault)
          (handleHypervisorFault w fault)"
  apply (cases fault; clarsimp simp add: handleHypervisorFault_def returnOk_def2)
  done

(* FIXME: move *)
lemma he_corres:
  "corres (dc \<oplus> dc) (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and
                       (\<lambda>s. scheduler_action s = resume_cur_thread))
                      (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and
                       (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
                       (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
                      (handle_event event) (handleEvent event)"
  (is "?he_corres")
proof -
  have hw:
    "\<And>isBlocking canGrant.
     corres dc (einvs and ct_running and (\<lambda>s. scheduler_action s = resume_cur_thread))
               (invs' and ct_running'
                      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
               (handle_recv isBlocking canGrant) (handleRecv isBlocking canGrant)"
    apply (rule corres_guard_imp [OF hw_corres])
     apply (clarsimp simp: ct_in_state_def ct_in_state'_def
                     elim!: st_tcb_weakenE pred_tcb'_weakenE
                     dest!: ct_not_ksQ)+
    done
    show ?thesis
      apply (case_tac event)
          apply (simp_all add: handleEvent_def)

          apply (rename_tac syscall)
          apply (case_tac syscall)
          apply (auto intro: corres_guard_imp[OF hs_corres]
                             corres_guard_imp[OF hw]
                             corres_guard_imp[OF hc_corres]
                             corres_guard_imp[OF hy_corres]
                             active_from_running active_from_running'
                      simp: simple_sane_strg)[8]
  sorry (*
         apply (rule corres_split')
            apply (rule corres_guard_imp[OF gct_corres], simp+)
           apply (rule hf_corres)
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
        apply (rule corres_split')
           apply (rule corres_guard_imp, rule gct_corres, simp+)
          apply (rule hf_corres)
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
            apply (case_tac rv, simp_all add: doMachineOp_return)[1]
            apply (rule handle_interrupt_corres)
           apply (rule corres_machine_op)
           apply (rule corres_Id, simp+)
           apply (wp hoare_vcg_all_lift
                     doMachineOp_getActiveIRQ_IRQ_active'
                    | simp
                    | simp add: imp_conjR | wp (once) hoare_drop_imps)+
        apply force
       apply simp
       apply (simp add: invs'_def valid_state'_def)
      apply (rule_tac corres_split')
         apply (rule corres_guard_imp, rule gct_corres, simp+)
        apply (rule corres_split_catch)
           apply (erule hf_corres)
          apply (rule hv_corres)
         apply (rule hoare_elim_pred_conjE2)
         apply (rule hoare_vcg_E_conj, rule valid_validE_E, wp)
         apply (wp handle_vm_fault_valid_fault)
        apply (rule hv_inv_ex')
       apply wp
       apply (clarsimp simp: simple_from_running tcb_at_invs)
       apply (fastforce elim!: st_tcb_ex_cap st_tcb_weakenE simp: ct_in_state_def)
      apply wp
      apply (clarsimp)
      apply (frule(1) ct_not_ksQ)
      apply (fastforce simp: simple_sane_strg sch_act_simple_def ct_in_state'_def
                  elim: st_tcb_ex_cap'' pred_tcb'_weakenE)
         apply (rule corres_split')
            apply (rule corres_guard_imp[OF gct_corres], simp+)
           apply (rule hh_corres)
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
      done *)
  qed

crunches handleVMFault,handleHypervisorFault
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  and cap_to'[wp]: "ex_nonz_cap_to' t"
  and ksit[wp]: "\<lambda>s. P (ksIdleThread s)"
  (ignore: getFAR getDFSR getIFSR)

lemma hv_inv':
  "\<lbrace>P\<rbrace> handleVMFault p t \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: ARM_H.handleVMFault_def)
  apply (rule hoare_pre)
   apply (wp dmo_inv' getDFSR_inv getFAR_inv getIFSR_inv getRestartPC_inv
             det_getRestartPC asUser_inv
          |wpc|simp)+
  done

lemma hh_inv':
  "\<lbrace>P\<rbrace> handleHypervisorFault p t \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: ARM_H.handleHypervisorFault_def)
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

crunches handleFault, receiveSignal, receiveIPC, asUser
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

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
  sorry (* checkBudgetRestart
        apply (case_tac syscall,
               (wp
                | clarsimp simp: active_from_running' simple_from_running' simple_sane_strg simp del: split_paired_All
                | rule conjI active_ex_cap'
                | drule ct_not_ksQ[rotated]
                | strengthen nidle)+)
        apply (rule hoare_strengthen_post,
               rule hoare_weaken_pre,
               rule hy_invs')
         apply (simp add: active_from_running')
        apply simp
       apply (wp hv_inv' hh_inv'
                 | rule conjI
                 | erule pred_tcb'_weakenE st_tcb_ex_cap''
                 | clarsimp simp: tcb_at_invs ct_in_state'_def simple_sane_strg sch_act_simple_def
                 | drule st_tcb_at_idle_thread'
                 | drule ct_not_ksQ[rotated]
                 | wpc | wp (once) hoare_drop_imps)+
  done *)
qed


end

end
