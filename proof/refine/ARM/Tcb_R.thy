(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_R
imports CNodeInv_R
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemma asUser_setNextPC_corres:
  "corres dc (tcb_at t and invs) (tcb_at' t and invs')
             (as_user t (setNextPC v)) (asUser t (setNextPC v))"
  apply (rule asUser_corres)
  apply (rule corres_Id, simp, simp)
  apply (rule no_fail_setNextPC)
  done

lemma activateIdleThread_corres:
 "corres dc (invs and st_tcb_at idle t)
            (invs' and st_tcb_at' idle' t)
    (arch_activate_idle_thread t) (activateIdleThread t)"
  by (simp add: arch_activate_idle_thread_def activateIdleThread_def)

lemma gts_st_tcb':
  "\<lbrace>tcb_at' t\<rbrace> getThreadState t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>st. st = rv) t\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_post_imp[where Q'="\<lambda>rv s. \<exists>rv'. rv = rv' \<and> st_tcb_at' (\<lambda>st. st = rv') t s"])
    apply simp
   apply (wp hoare_vcg_ex_lift)
  apply (clarsimp simp add: pred_tcb_at'_def obj_at'_def)
  done

lemma activateIdle_invs':
  "activateIdleThread thread \<lbrace>invs'\<rbrace>"
  by (simp add: activateIdleThread_def)

lemma invs'_live_sc'_ex_nonz_cap_to':
  "ko_at' ko scp s \<Longrightarrow> invs' s \<Longrightarrow> live_sc' ko \<longrightarrow> ex_nonz_cap_to' scp s"
  apply (clarsimp simp: invs'_def if_live_then_nonz_cap'_def)
  by (fastforce simp: obj_at'_real_def ko_wp_at'_def projectKO_sc)

lemma activateThread_corres:
 "corres dc (invs and ct_in_state activatable) (invs' and ct_in_state' activatable' and sch_act_simple)
            activate_thread activateThread"
  supply subst_all [simp del]
  apply add_cur_tcb'
  apply (simp add: activate_thread_def activateThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule corres_split[OF get_tcb_yield_to_corres])
        apply (rule corres_split[OF corres_when])
            apply clarsimp
           apply (rule schedContextCompleteYieldTo_corres)
          apply (rule_tac R="\<lambda>ts s. (activatable ts) \<and> invs s \<and> st_tcb_at ((=) ts) thread s"
                      and R'="\<lambda>ts s. (activatable' ts) \<and> invs' s \<and> st_tcb_at' (\<lambda>ts'. ts' = ts) thread s"
                      in  corres_split[OF getThreadState_corres])
            apply (rule_tac F="idle rv \<or> runnable rv" in corres_req, clarsimp)
            apply (rule_tac F="idle' rv' \<or> runnable' rv'" in corres_req, clarsimp)
            apply (case_tac rv, simp_all add: isRunning_def isRestart_def, safe, simp_all)[1]
             apply (rule corres_guard_imp)
               apply (rule corres_split_eqr[OF asUser_getRestartPC_corres])
                 apply (rule corres_split_nor[OF asUser_setNextPC_corres])
                   apply (rule setThreadState_corres, simp)
                  apply (rule_tac Q'="\<lambda>_. invs and tcb_at thread" in hoare_strengthen_post[rotated])
                   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
                  apply wpsimp
                 apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
                  apply (fastforce simp: invs'_def dest: invs'_valid_tcbs')
                 apply wp+
              apply (clarsimp simp: st_tcb_at_tcb_at)
             apply fastforce
            apply (rule corres_guard_imp)
              apply (rule activateIdleThread_corres)
             apply (clarsimp elim!: st_tcb_weakenE)
            apply (clarsimp elim!: pred_tcb'_weakenE)
           apply (wp gts_st_tcb gts_st_tcb' gts_st_tcb_at complete_yield_to_invs)+
        apply (wpsimp wp: schedContextCompleteYieldTo_invs' hoare_drop_imp)
       apply (wp gts_st_tcb gts_st_tcb' gts_st_tcb_at complete_yield_to_invs
                 get_tcb_obj_ref_wp threadGet_wp)+
   apply (clarsimp simp: ct_in_state_def tcb_at_invs invs_def valid_state_def valid_pspace_def
                  elim!: st_tcb_weakenE)
  apply (fastforce simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def
                  elim!: pred_tcb'_weakenE)
  done

lemma bindNotification_corres:
  "corres dc
         (invs and tcb_at t and ntfn_at a) (invs' and tcb_at' t and ntfn_at' a)
         (bind_notification t a) (bindNotification t a)"
  unfolding bind_notification_def bindNotification_def
  apply (simp add: bind_assoc update_sk_obj_ref_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getNotification_corres])
      apply (rule corres_split[OF setNotification_corres])
         apply (clarsimp simp: ntfn_relation_def split: Structures_A.ntfn.splits)
        apply (rule setBoundNotification_corres)
       apply wp+
  by auto

abbreviation
  "ct_idle' \<equiv> ct_in_state' idle'"

lemma activate_invs':
  "activateThread \<lbrace>invs'\<rbrace>"
  apply (simp add: activateThread_def)
  apply (wpsimp wp: activateIdle_invs' sts_invs_minor' schedContextCompleteYieldTo_invs'
                    hoare_vcg_imp_lift')
  by (fastforce simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def sch_act_simple_def)

declare not_psubset_eq[dest!] (* FIXME: remove, not a good dest rule *)

crunch schedContextResume
  for tcb_at'[wp]: "\<lambda>s. P (tcb_at' t s)"
  (wp: crunch_wps)

lemma setThreadState_Restart_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> tcb_at' t s \<and> ex_nonz_cap_to' t s
        \<and> st_tcb_at' (Not \<circ> is_BlockedOnReply) t s\<rbrace>
   setThreadState Restart t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: setThreadState_ct_not_inQ simp: pred_tcb_at'_eq_commute)
  apply (auto dest: global'_no_ex_cap
              simp: o_def pred_tcb_at'_def obj_at'_def)
  done

crunch cancel_ipc
  for valid_sched_action[wp]: valid_sched_action
  (wp: crunch_wps ignore: set_object thread_set update_sched_context)

crunch cancel_ipc
  for sc_tcb_sc_at[wp]: "sc_tcb_sc_at P t"
  (wp: crunch_wps)

lemma restart_corres:
  "corres dc
          (einvs and tcb_at t and ex_nonz_cap_to t and current_time_bounded)
          (invs' and tcb_at' t and ex_nonz_cap_to' t)
          (Tcb_A.restart t) (ThreadDecls_H.restart t)"
  apply (simp add: Tcb_A.restart_def Thread_H.restart_def test_possible_switch_to_def
                   get_tcb_obj_ref_def)
  apply (simp add: isStopped_def2 liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (rule corres_split[OF threadGet_corres[where r="(=)"]])
         apply (clarsimp simp: tcb_relation_def)
        apply (rename_tac scOpt)
        apply (rule corres_when2)
         apply (simp add: idle_tsr runnable_tsr)
        apply (rule corres_split_nor[OF cancel_ipc_corres])
          apply (rule corres_split_nor[OF setThreadState_corres])
             apply (clarsimp simp: thread_state_relation_def)
            apply (simp only:)
            apply (rule corres_split [OF ifCondRefillUnblockCheck_corres])
              apply (simp add: maybeM_when, fold dc_def)
              apply (rule corres_split[OF corres_when2])
                  apply clarsimp
                 apply (rule schedContextResume_corres)
                apply (rule corres_split[OF isSchedulable_corres])
                  apply (rule corres_when2 [OF _ possibleSwitchTo_corres]; (solves simp)?)
                 apply (wpsimp wp: is_schedulable_wp isSchedulable_wp)+
               apply (rule_tac Q'="\<lambda>rv. invs and valid_sched_action and active_scs_valid and tcb_at t"
                      in hoare_strengthen_post)
                apply (wpsimp wp: sched_context_resume_valid_sched_action)
               apply fastforce
              apply (rule_tac Q'="\<lambda>rv. invs' and tcb_at' t" in hoare_strengthen_post)
               apply wpsimp
              apply (fastforce simp: invs'_def sch_act_wf_weak valid_pspace'_def)
             apply (rule_tac Q'="\<lambda>rv. invs and valid_ready_qs and valid_release_q
                                          and current_time_bounded
                                          and (\<lambda>s. \<exists>scp. scOpt = Some scp \<longrightarrow> sc_not_in_release_q scp s)
                                          and active_scs_valid and valid_sched_action
                                          and scheduler_act_not t and bound_sc_tcb_at ((=) scOpt) t"
                    in hoare_strengthen_post)
              apply (wpsimp simp: if_cond_refill_unblock_check_def
                              wp: refill_unblock_check_valid_release_q
                                  refill_unblock_check_active_scs_valid)
             apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
             apply (intro conjI; clarsimp)
              apply (clarsimp simp: pred_tcb_at_tcb_at)
              apply (subst (asm) sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF eq_commute refl])
               apply fastforce
              apply (fastforce simp: sc_at_pred_n_def obj_at_def
                                     sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF eq_commute refl])
             apply fastforce
            apply (wpsimp simp: ifCondRefillUnblockCheck_def
                            wp: refillUnblockCheck_invs')
           apply (rule_tac Q'="\<lambda>rv. invs and valid_ready_qs and valid_release_q
                                        and current_time_bounded
                                        and (\<lambda>s. \<forall>scp. scOpt = Some scp \<longrightarrow> sc_not_in_release_q scp s)
                                        and active_scs_valid and valid_sched_action
                                        and scheduler_act_not t and bound_sc_tcb_at ((=) scOpt) t"
                  in hoare_strengthen_post)
            apply (wpsimp wp: sts_invs_minor set_thread_state_valid_sched_action
                              set_thread_state_valid_ready_qs set_thread_state_valid_release_q)
           apply (case_tac scOpt; clarsimp)
           apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
           apply (rule context_conjI)
            apply (clarsimp simp: valid_objs_def)
            apply (drule_tac x=t in bspec, clarsimp simp: pred_tcb_at_def obj_at_def)
            apply (clarsimp simp: valid_obj_def valid_tcb_def pred_tcb_at_def obj_at_def valid_bound_obj_def
                           dest!: sym[of "Some _"])
           apply (clarsimp simp: obj_at_def opt_map_red opt_pred_def is_sc_obj)
          apply (rule_tac Q'="\<lambda>rv. invs' and tcb_at' t" in hoare_strengthen_post[rotated])
           apply (clarsimp simp: invs'_def valid_pspace'_def o_def)
          apply (wpsimp wp: setThreadState_Restart_invs' hoare_drop_imps)
         apply (rule_tac Q'="\<lambda>rv. invs and valid_sched and valid_sched_action and tcb_at t
                                      and current_time_bounded
                                      and (\<lambda>s. \<forall>scp. scOpt = Some scp \<longrightarrow> sc_not_in_release_q scp s)
                                      and fault_tcb_at ((=) None) t and bound_sc_tcb_at ((=) scOpt) t
                                      and st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = {}) t
                                      and scheduler_act_not t and ex_nonz_cap_to t"
                in hoare_strengthen_post)
          apply (wpsimp wp: cancel_ipc_no_refs cancel_ipc_ex_nonz_cap_to_tcb)
         apply (fastforce simp: invs_def valid_state_def idle_no_ex_cap valid_pspace_def)
        apply (rule_tac Q'="\<lambda>rv. invs' and tcb_at' t and ex_nonz_cap_to' t and st_tcb_at' simple' t"
               in hoare_strengthen_post)
         apply wpsimp
        apply (fastforce simp: invs'_def sch_act_wf_weak valid_pspace'_def
                         elim: pred_tcb'_weakenE)[1]
       apply (wpsimp wp: gts_wp gts_wp' thread_get_wp')+
   apply (prop_tac "scheduler_act_not t s")
    apply (fastforce elim: valid_sched_scheduler_act_not simp: pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb
                         valid_sched_def invs_def valid_state_def valid_pspace_def)
   apply (drule sym_refs_inv_tcb_scps)
   apply (prop_tac "heap_ref_eq scp t (tcb_scps_of s)")
    apply (clarsimp simp: vs_all_heap_simps)
   apply (clarsimp simp: heap_refs_inv_def2)
   apply (clarsimp simp: vs_all_heap_simps)
   apply (drule valid_release_q_not_in_release_q_not_runnable)
    apply (fastforce simp: pred_tcb_at_def obj_at_def o_def)
   apply clarsimp
  apply clarsimp
  done

crunch schedContextResume, ifCondRefillUnblockCheck
  for ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma restart_invs':
  "\<lbrace>invs' and ex_nonz_cap_to' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   ThreadDecls_H.restart t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding restart_def
  apply (simp add: isStopped_def2)
  apply (wp setThreadState_nonqueued_state_update isSchedulable_wp
            cancelIPC_simple setThreadState_st_tcb sch_act_simple_lift)
       apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
        apply wpsimp
        apply (clarsimp simp: isSchedulable_bool_def pred_map_pred_conj[simplified pred_conj_def]
                              projectKO_opt_tcb pred_map_def pred_tcb_at'_def
                              obj_at'_real_def ko_wp_at'_def
                       elim!: opt_mapE)
       apply (wpsimp wp: hoare_vcg_imp_lift')
      apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated])
       apply (fastforce elim: isSchedulable_bool_runnableE)
       apply (wpsimp wp: ifCondRefillUnblockCheck_invs' hoare_vcg_imp_lift')
      apply (wpsimp wp: setThreadState_nonqueued_state_update setThreadState_st_tcb
                        hoare_vcg_if_lift2)
     apply clarsimp
     apply wp+
   apply (clarsimp simp: comp_def)
   apply (rule hoare_strengthen_post[OF gts_sp'])
   prefer 2
   apply assumption
  apply (clarsimp simp: pred_tcb_at' invs'_def ct_in_state'_def)
  done

crunch "ThreadDecls_H.restart"
  for tcb'[wp]: "tcb_at' t"
  (wp: crunch_wps whileM_inv simp: crunch_simps)

lemma no_fail_setRegister: "no_fail \<top> (setRegister r v)"
  by (simp add: setRegister_def)

lemma updateRestartPC_ex_nonz_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> updateRestartPC t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  unfolding updateRestartPC_def
  apply (rule asUser_cap_to')
  done

crunch suspend
  for cap_to': "ex_nonz_cap_to' p"
  (wp: crunch_wps simp: crunch_simps)

declare det_getRegister[simp]
declare det_setRegister[simp]

lemma no_fail_getRegister[wp]: "no_fail \<top> (getRegister r)"
  by (simp add: getRegister_def)

lemma invokeTCB_ReadRegisters_corres:
  "corres (dc \<oplus> (=))
        (einvs  and tcb_at src and ex_nonz_cap_to src)
        (invs' and sch_act_simple and tcb_at' src and ex_nonz_cap_to' src)
        (invoke_tcb (tcb_invocation.ReadRegisters src susp n arch))
        (invokeTCB (tcbinvocation.ReadRegisters src susp n arch'))"
  apply (simp add: invokeTCB_def performTransfer_def genericTake_def
                   frame_registers_def gp_registers_def
                   frameRegisters_def gpRegisters_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_when[OF refl])
       apply (rule suspend_corres)
      apply (rule corres_split[OF getCurThread_corres])
        apply (simp add: liftM_def[symmetric])
        apply (rule asUser_corres)
        apply (rule corres_Id)
          apply simp
         apply simp
        apply (rule no_fail_mapM)
        apply (simp add: no_fail_getRegister)
       apply (wp suspend_invs)+
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_idle_def
                  dest!: idle_no_ex_cap)
  apply (clarsimp simp: invs'_def dest!: global'_no_ex_cap)
  done

lemma asUser_postModifyRegisters_corres:
  "corres dc \<top> (tcb_at' t)
     (arch_post_modify_registers ct t)
     (asUser t $ postModifyRegisters ct t)"
  apply (simp add: arch_post_modify_registers_def postModifyRegisters_def)
  apply (subst submonad_asUser.return)
  apply (rule corres_stateAssert_assume)
   by simp+

crunch restart
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' tcbPtr"
  (wp: crunch_wps threadSet_cap_to simp: crunch_simps tcb_cte_cases_def)

lemma invokeTCB_WriteRegisters_corres:
  "corres (dc \<oplus> (=))
          (einvs and simple_sched_action and tcb_at dest and ex_nonz_cap_to dest
           and current_time_bounded)
          (invs' and tcb_at' dest and ex_nonz_cap_to' dest)
          (invoke_tcb (tcb_invocation.WriteRegisters dest resume values arch))
          (invokeTCB (tcbinvocation.WriteRegisters dest resume values arch'))"
  apply (simp add: invokeTCB_def performTransfer_def arch_get_sanitise_register_info_def
                   frameRegisters_def gpRegisters_def getSanitiseRegisterInfo_def
                   sanitiseRegister_def sanitise_register_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurThread_sp])
   apply (corresKsimp corres: getCurThread_corres)
  apply (rule corres_split_skip; (solves wpsimp)?)
   apply (corresKsimp corres: asUser_corres
                       simp: zipWithM_mapM getRestartPC_def setNextPC_def
                         wp: no_fail_mapM no_fail_setRegister)
  apply (rule corres_split_skip; (solves wpsimp)?)
   apply (corresKsimp corres: asUser_postModifyRegisters_corres[simplified])
  apply (rule_tac Q="\<lambda>_. einvs" and Q'="\<lambda>_. invs'" in corres_underlying_split[rotated 2])
     apply (wpsimp wp: restart_valid_sched)
     using idle_no_ex_cap apply fastforce
    apply (wpsimp wp: restart_invs')
    using global'_no_ex_cap apply fastforce
   apply (corresKsimp corres: restart_corres)
  apply (corresKsimp corres: rescheduleRequired_corres)
  apply fastforce
  done

lemma tcbSchedDequeue_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  by (wp hoare_convert_imp)

lemma updateRestartPC_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   updateRestartPC t
   \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  unfolding updateRestartPC_def
  apply (wp hoare_convert_imp)
  done

lemma schedContextCancelYieldTo_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   schedContextCancelYieldTo t
   \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  by (wp hoare_convert_imp)

lemma tcbReleaseRemove_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   tcbReleaseRemove t
   \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  by (wp hoare_convert_imp)

lemma suspend_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   suspend t
   \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  by (wpsimp simp: suspend_def wp_del: getThreadState_only_state_wp)

crunch restart, suspend
  for cur_tcb'[wp]: cur_tcb'
  (wp: crunch_wps threadSet_cur ignore: threadSet)

lemma invokeTCB_CopyRegisters_corres:
  "corres (dc \<oplus> (=))
        (einvs and simple_sched_action and tcb_at dest and tcb_at src and ex_nonz_cap_to src and
          ex_nonz_cap_to dest and current_time_bounded)
        (invs' and sch_act_simple and tcb_at' dest and tcb_at' src
          and ex_nonz_cap_to' src and ex_nonz_cap_to' dest)
        (invoke_tcb (tcb_invocation.CopyRegisters dest src susp resume frames ints arch))
        (invokeTCB (tcbinvocation.CopyRegisters dest src susp resume frames ints arch'))"
proof -
  have Q: "\<And>src src' des des' r r'. \<lbrakk> src = src'; des = des' \<rbrakk> \<Longrightarrow>
           corres dc (tcb_at src and tcb_at des and invs)
                     (tcb_at' src' and tcb_at' des' and invs')
           (do v \<leftarrow> as_user src (getRegister r);
               as_user des (setRegister r' v)
            od)
           (do v \<leftarrow> asUser src' (getRegister r);
               asUser des' (setRegister r' v)
            od)"
    apply clarsimp
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr)
         apply (rule asUser_getRegister_corres)
        apply (simp add: setRegister_def)
        apply (rule asUser_corres)
        apply (rule corres_modify')
         apply simp
        apply simp
       apply (simp | wp)+
     apply fastforce+
    done
  have R: "\<And>src src' des des' xs ys. \<lbrakk> src = src'; des = des'; xs = ys \<rbrakk> \<Longrightarrow>
           corres dc (tcb_at src and tcb_at des and invs)
                     (tcb_at' src' and tcb_at' des' and invs')
           (mapM_x (\<lambda>r. do v \<leftarrow> as_user src (getRegister r);
               as_user des (setRegister r v)
            od) xs)
           (mapM_x (\<lambda>r'. do v \<leftarrow> asUser src' (getRegister r');
               asUser des' (setRegister r' v)
            od) ys)"
    apply (rule corres_mapM_x [where S=Id])
        apply simp
        apply (rule Q)
          apply (clarsimp simp: set_zip_same | wp)+
    done
  have U: "\<And>t. corres dc (tcb_at t and invs) (tcb_at' t and invs')
                (do pc \<leftarrow> as_user t getRestartPC; as_user t (setNextPC pc) od)
                (do pc \<leftarrow> asUser t getRestartPC; asUser t (setNextPC pc) od)"
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr[OF asUser_getRestartPC_corres])
        apply (rule asUser_setNextPC_corres)
       apply wp+
     apply fastforce+
    done
  show ?thesis
    apply (simp add: invokeTCB_def performTransfer_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_when [OF refl suspend_corres]], simp)
        apply (rule corres_split[OF corres_when [OF refl restart_corres]], simp)
          apply (rule corres_split_nor)
             apply (rule corres_when[OF refl])
             apply (rule corres_split_nor)
                apply (rule R[OF refl refl])
                apply (simp add: frame_registers_def frameRegisters_def)
               apply (simp add: getRestartPC_def setNextPC_def dc_def[symmetric])
               apply (rule Q[OF refl refl])
              apply ((wp mapM_x_wp' hoare_weak_lift_imp | simp)+)[2]
            apply (rule corres_split_nor)
               apply (rule corres_when[OF refl])
               apply (rule R[OF refl refl])
               apply (simp add: gpRegisters_def)
              apply (rule corres_split_eqr [OF getCurThread_corres])
                apply (rule corres_split_nor[OF asUser_postModifyRegisters_corres[simplified]])
                  apply (rule corres_split[OF corres_when[OF refl rescheduleRequired_corres]])
                    apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
                    apply simp
                   apply (solves \<open>wp hoare_weak_lift_imp\<close>)+
             apply (rule_tac Q'="\<lambda>_. einvs and tcb_at dest" in hoare_strengthen_post[rotated])
              apply (clarsimp simp: invs_def valid_sched_weak_strg valid_sched_def valid_state_def
                                    valid_pspace_def)
             prefer 2
             apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' dest" in hoare_strengthen_post[rotated])
              apply (clarsimp simp: invs'_def valid_pspace'_def)
             apply ((wp mapM_x_wp' hoare_weak_lift_imp | simp)+)[4]
         apply ((wp hoare_weak_lift_imp restart_invs' restart_valid_sched | wpc | clarsimp simp: if_apply_def2)+)[2]
       apply (rule_tac Q'="\<lambda>_. einvs and tcb_at dest and tcb_at src and ex_nonz_cap_to dest
                              and simple_sched_action and current_time_bounded"
              in hoare_strengthen_post[rotated])
        apply (clarsimp simp: invs_def valid_sched_weak_strg valid_sched_def valid_state_def
                              valid_pspace_def valid_idle_def
                       dest!: idle_no_ex_cap )
       apply (wp suspend_nonz_cap_to_tcb hoare_weak_lift_imp suspend_invs suspend_cap_to'
                 suspend_valid_sched
              | simp add: if_apply_def2)+
     apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_idle_def
                     dest!: idle_no_ex_cap)
    apply (fastforce simp: invs'_def dest!: global'_no_ex_cap)
    done
qed

lemma readreg_invs':
  "\<lbrace>invs' and tcb_at' src and ex_nonz_cap_to' src\<rbrace>
     invokeTCB (tcbinvocation.ReadRegisters src susp n arch)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: invokeTCB_def performTransfer_def | wp
       | clarsimp simp: invs'_def
                 dest!: global'_no_ex_cap)+

lemma writereg_invs':
  "\<lbrace>invs' and tcb_at' dest and ex_nonz_cap_to' dest\<rbrace>
     invokeTCB (tcbinvocation.WriteRegisters dest resume values arch)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: invokeTCB_def performTransfer_def  | wp restart_invs' | rule conjI
       | clarsimp
       | clarsimp simp: invs'_def
                 dest!: global'_no_ex_cap)+

lemma copyreg_invs'':
  "\<lbrace>invs' and tcb_at' src and tcb_at' dest and ex_nonz_cap_to' src and ex_nonz_cap_to' dest\<rbrace>
     invokeTCB (tcbinvocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace>\<lambda>rv. invs' and tcb_at' dest\<rbrace>"
  supply if_split [split del] if_weak_cong[cong]
  unfolding invokeTCB_def performTransfer_def
  apply (wpsimp wp: mapM_x_wp' restart_invs' hoare_vcg_if_lift2 hoare_drop_imp suspend_cap_to')
  by (fastforce simp: invs'_def dest!: global'_no_ex_cap split: if_split)

lemma copyreg_invs':
  "\<lbrace>invs' and tcb_at' src and
          tcb_at' dest and ex_nonz_cap_to' src and ex_nonz_cap_to' dest\<rbrace>
     invokeTCB (tcbinvocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (rule hoare_strengthen_post, rule copyreg_invs'', simp)

lemma isRunnable_corres':
  "t = t' \<Longrightarrow>
   corres (\<lambda>ts runn. runnable ts = runn)
     (tcb_at t and pspace_aligned and pspace_distinct) \<top>
     (get_thread_state t) (isRunnable t')"
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp add: isRunnable_def)
  apply (subst bind_return[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres'], clarsimp)
      apply (case_tac rv, clarsimp+)
     apply (wp hoare_TrueI)+
   apply auto
  done

lemma isBlocked_corres:
  "corres (\<lambda>ts blocked. ipc_queued_thread_state ts = blocked) (tcb_at t) (tcb_at' t)
     (get_thread_state t) (isBlocked t)"
  apply (simp add: isBlocked_def)
  apply (subst bind_return[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (case_tac rv, clarsimp+)
     apply (wp hoare_TrueI)+
   apply auto
  done

lemma tcbSchedDequeue_not_queued:
  "\<lbrace>\<top>\<rbrace> tcbSchedDequeue t
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp | simp)+
  apply (rule_tac Q'="\<lambda>rv. obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
               in hoare_post_imp)
   apply (clarsimp simp: obj_at'_def)
  apply (wp threadGet_sp' [where P=\<top>, simplified] | simp)+
  done

lemma threadSet_ct_in_state':
  "(\<And>tcb. tcbState (f tcb) = tcbState tcb) \<Longrightarrow>
  \<lbrace>ct_in_state' test\<rbrace> threadSet f t \<lbrace>\<lambda>rv. ct_in_state' test\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply (wp threadSet_pred_tcb_no_state)+
    apply simp+
  apply wp
  done

lemma tcbSchedDequeue_ct_in_state'[wp]:
  "\<lbrace>ct_in_state' test\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>rv. ct_in_state' test\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread]; wp)
  done

lemma valid_tcb'_tcbPriority_update:
  "\<lbrakk> valid_tcb' tcb s; f (tcbPriority tcb) \<le> maxPriority \<rbrakk>
     \<Longrightarrow> valid_tcb' (tcbPriority_update f tcb) s"
  apply (simp add: valid_tcb'_def tcb_cte_cases_def)
  done

lemma threadSet_valid_objs_tcbPriority_update:
  "\<lbrace>valid_objs' and (\<lambda>_. prio \<le> maxPriority)\<rbrace>
   threadSetPriority t prio
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  including no_pre
  apply (simp add: threadSetPriority_def threadSet_def)
  apply wp
   prefer 2
   apply (rule getObject_tcb_sp)
  apply (rule hoare_weaken_pre)
   apply (rule setObject_tcb_valid_objs)
  apply (clarsimp simp: valid_obj'_def)
  apply (frule (1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (simp add: valid_obj'_def)
  apply (subgoal_tac "tcb_at' t s")
   apply simp
   apply (rule valid_tcb'_tcbPriority_update)
    apply (fastforce  simp: obj_at'_def)+
  done

lemma tcbEPDequeueAppend_valid_ntfn'_rv:
  "\<lbrace>valid_ntfn' ntfn and K (ntfnObj ntfn = WaitingNtfn qs \<and> t \<in> set qs)\<rbrace>
   do qs' \<leftarrow> tcbEPDequeue t qs;
      tcbEPAppend t qs'
   od
   \<lbrace>\<lambda>rv s. valid_ntfn' (ntfnObj_update (\<lambda>_. WaitingNtfn rv) ntfn) s\<rbrace>"
  apply (simp only: tcbEPAppend_def tcbEPDequeue_def)
  apply (wp tcbEPFindIndex_wp)
  apply (rule conjI)
   apply (clarsimp simp: valid_ntfn'_def split: option.split)
  apply (clarsimp simp: valid_ntfn'_def simp del: imp_disjL dest!: findIndex_member)
  apply (intro conjI; clarsimp?)
          apply (fastforce dest: in_set_takeD in_set_dropD)
         apply (fastforce dest: in_set_dropD)
        apply (fastforce dest: in_set_dropD)
       apply (fastforce dest: in_set_dropD)
      apply (fastforce dest: in_set_takeD)
     apply (clarsimp simp: Int_Un_distrib set_take_disj_set_drop_if_distinct)
     apply (rule disjoint_subset_both[OF set_take_subset set_drop_subset])
     apply (simp add: Int_commute)
    apply (fastforce dest: in_set_takeD)
   apply (clarsimp simp: Int_Un_distrib set_take_disj_set_drop_if_distinct)
   apply (fastforce dest: in_set_takeD in_set_dropD)
  apply (clarsimp split: option.split)
  apply (rename_tac ys zs i j tcb tcba tptr)
  apply (case_tac ys; clarsimp)
  done

lemma reorderNtfn_invs':
  "\<lbrace>invs' and st_tcb_at' (\<lambda>st. ntfnBlocked st = Some ntfnPtr) tptr\<rbrace>
   reorderNtfn ntfnPtr tptr
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp only: reorderNtfn_def)
  apply (subst bind_assoc[symmetric, where m="tcbEPDequeue tptr _"])
  apply (rule bind_wp | simp only: K_bind_def)+
        apply (wp set_ntfn_minor_invs')
       apply (simp add: pred_conj_def live_ntfn'_def)
       apply (wpsimp wp: getNotification_wp tcbEPDequeueAppend_valid_ntfn'_rv hoare_vcg_conj_lift)+
  apply (frule ntfn_ko_at_valid_objs_valid_ntfn', fastforce)
  apply (clarsimp simp: sym_refs_asrt_def valid_ntfn'_def pred_tcb_at'_def
                        obj_at'_def projectKO_eq projectKO_tcb projectKO_ntfn)
  apply (case_tac "tcbState obj"; clarsimp simp: ntfnBlocked_def getntfnQueue_def split: ntfn.splits)
  apply (frule_tac ko=obj and p=tptr in sym_refs_ko_atD'[rotated])
   apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
  apply (clarsimp simp: invs'_def valid_idle'_def live_ntfn'_def
                        if_live_then_nonz_cap'_def refs_of_rev' get_refs_def
                        ko_wp_at'_def obj_at'_def projectKO_eq projectKO_tcb
                 split: option.splits)
  done

lemma set_ep_minor_invs':
  "\<lbrace>invs' and obj_at' (\<lambda>ep. ep_q_refs_of' ep = ep_q_refs_of' val) ptr
          and valid_ep' val
          and (\<lambda>s. live' (KOEndpoint val) \<longrightarrow> ex_nonz_cap_to' ptr s)\<rbrace>
   setEndpoint ptr val
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (clarsimp simp add: invs'_def cteCaps_of_def valid_dom_schedule'_def)
  apply (wpsimp wp: irqs_masked_lift valid_irq_node_lift untyped_ranges_zero_lift simp: o_def)
  done

lemma getEpQueue_wp[wp]: "\<lbrace>\<lambda>s. ep \<noteq> IdleEP \<longrightarrow> P (epQueue ep) s\<rbrace> getEpQueue ep \<lbrace>P\<rbrace>"
  unfolding getEpQueue_def by wpsimp auto

lemma updateEpQueue_triv: "ep \<noteq> IdleEP \<Longrightarrow> updateEpQueue ep (epQueue ep) = ep"
  by (cases ep; clarsimp simp: updateEpQueue_def)

lemma updateEPQueue_IdleEP[simp]: "(updateEpQueue ep qs = IdleEP) = (ep = IdleEP)"
  by (cases ep; simp add: updateEpQueue_def)

lemma reorderEp_invs':
  "\<lbrace>invs' and st_tcb_at' (\<lambda>st. epBlocked st = Some ntfnPtr) tptr\<rbrace>
   reorderEp ntfnPtr tptr
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp only: reorderEp_def)
  apply (subst bind_assoc[symmetric, where m="tcbEPDequeue tptr _"])
  apply (wp set_ep_minor_invs')
       apply (simp add: pred_conj_def live_ntfn'_def)
       apply (wpsimp wp: getEndpoint_wp tcbEPAppend_valid_ep' tcbEPAppend_rv_wf' tcbEPAppend_rv_wf''
                         tcbEPDequeue_valid_ep' tcbEPDequeue_rv_wf' tcbEPDequeue_rv_wf'')+
  apply (frule ep_ko_at_valid_objs_valid_ep', fastforce)
  apply (clarsimp simp: updateEpQueue_triv sym_refs_asrt_def valid_ep'_def pred_tcb_at'_def
                        obj_at'_def projectKO_eq projectKO_tcb projectKO_ep)
  apply (frule_tac ko=obj and p=tptr in sym_refs_ko_atD'[rotated])
   apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
  apply (case_tac "tcbState obj"; clarsimp simp: epBlocked_def split: ntfn.splits if_splits)
    apply (auto simp: invs'_def if_live_then_nonz_cap'_def
                      refs_of_rev' get_refs_def ko_wp_at'_def obj_at'_def projectKO_eq projectKO_tcb
               split: option.splits)
  done

lemma threadSetPriority_invs':
  "\<lbrace>invs' and obj_at' (Not \<circ> tcbQueued) t and K (p \<le> maxPriority)\<rbrace>
   threadSetPriority t p
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: threadSet_invs_trivial simp: threadSetPriority_def)
  by (fastforce simp: tcb_cte_cases_def invs'_def inQ_def obj_at'_def
                      valid_queues_def valid_queues_no_bitmap_def valid_release_queue'_def)+

crunch reorderEp, threadSetPriority
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (wp: crunch_wps threadSet_st_tcb_at2)

lemma threadSetPriority_onRunning_invs':
   "\<lbrace>\<lambda>s. invs' s \<and> ready_qs_runnable s \<and> ct_active' s \<and> p \<le> maxPriority\<rbrace>
    threadSetPriority_onRunning t p
    \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp only: threadSetPriority_onRunning_def)
  apply (wpsimp wp: hoare_vcg_const_imp_lift rescheduleRequired_invs' hoare_vcg_all_lift)
       apply (wpsimp wp: threadGet_wp threadSetPriority_invs' tcbSchedDequeue_not_queued)+
  apply (drule invs_queues')
  apply (fastforce simp: ready_qs_runnable_def valid_queues'_def inQ_def
                         obj_at'_def ct_in_state'_def runnable_eq_active')
  done

lemma runnable'_case_thread_state_If:
  "(case rv of Structures_H.thread_state.Running \<Rightarrow> threadSetPriority_onRunning t x
             | Structures_H.thread_state.Restart \<Rightarrow> threadSetPriority_onRunning t x
             | _ \<Rightarrow> P) =
   (if runnable' rv then threadSetPriority_onRunning t x else P)"
  by (cases rv; clarsimp)

lemma setP_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> ready_qs_runnable s \<and> ct_active' s \<and> p \<le> maxPriority\<rbrace>
   setPriority t p
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setPriority_def runnable'_case_thread_state_If)
  apply (wpsimp wp: threadSetPriority_onRunning_invs' threadSetPriority_invs' reorderEp_invs'
                    reorderNtfn_invs' gts_wp' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
  apply (drule invs_queues')
  apply (fastforce simp: ready_qs_runnable_def valid_queues'_def inQ_def
                         pred_tcb_at'_def obj_at'_def projectKO_eq)
  done

lemma reorder_ntfn_corres:
  "ntfn = ntfn' \<Longrightarrow> corres dc (invs and st_tcb_at (\<lambda>st. ntfn_blocked st = Some ntfn) t)
                              (invs' and st_tcb_at' (\<lambda>st. ntfnBlocked st = Some ntfn) t)
                              (reorder_ntfn ntfn t) (reorderNtfn ntfn' t)"
  apply add_sym_refs
  apply (clarsimp simp: reorder_ntfn_def reorderNtfn_def)
  apply (rule corres_stateAssert_assume)
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule getNotification_corres)
       apply (rule corres_assert_opt_assume_l)
       apply (rule corres_assert_assume_r)
       apply (rule corres_split)
          apply (rule tcbEPDequeue_corres)
          apply (clarsimp simp: ntfn_relation_def get_ntfn_queue_def getntfnQueue_def
                         split: Structures_A.ntfn.splits)
         apply (rule corres_split)
            apply clarsimp
            apply (rule tcbEPAppend_corres)
           apply (rule setNotification_corres)
           apply (clarsimp simp: ntfn_relation_def)
          apply wp
         apply wp
        apply (rule tcb_ep_dequeue_rv_wf')
       apply (rule tcbEPDequeue_rv_wf')
      apply (wp get_simple_ko_wp)
     apply (wp getNotification_wp)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def ntfn_blocked_def)
    apply (clarsimp split: Structures_A.thread_state.splits)
    apply (frule invs_valid_objs)
    apply (erule (1) valid_objsE[where x=t])
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def obj_at_def)
    apply (frule invs_valid_objs)
    apply (erule (1) valid_objsE[where x=ntfn'])
    apply (clarsimp simp: valid_obj_def valid_ntfn_def)
    apply (frule invs_sym_refs)
    apply (drule_tac p=t in sym_refs_ko_atD[rotated])
     apply (simp add: obj_at_def)
    apply clarsimp
    apply (clarsimp simp: refs_of_rev obj_at_def get_ntfn_queue_def is_tcb_def is_ntfn_def)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKO_eq projectKO_tcb ntfnBlocked_def)
   apply (clarsimp split: thread_state.splits)
   apply (frule invs_valid_objs')
   apply (erule (1) valid_objsE'[where x=t])
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def valid_tcb_state'_def
                         obj_at'_def projectKO_eq projectKO_ntfn)
   apply (frule invs_valid_objs')
   apply (erule (1) valid_objsE'[where x=ntfn'])
   apply (clarsimp simp: valid_obj'_def valid_ntfn'_def)
   apply (drule_tac p=t and ko=obj in sym_refs_ko_atD'[rotated])
    apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
   apply clarsimp
   apply (clarsimp simp: refs_of_rev' ko_wp_at'_def getntfnQueue_def
                         obj_at'_def projectKO_eq projectKO_tcb)
  apply (clarsimp simp: sym_refs_asrt_def)
  done

lemma reorder_ep_corres:
  "a = a' \<Longrightarrow> corres dc (invs and st_tcb_at (\<lambda>st. ep_blocked st = Some a) t)
                        (invs' and st_tcb_at' (\<lambda>st. epBlocked st = Some a) t)
                        (reorder_ep a t) (reorderEp a' t)"
  apply add_sym_refs
  apply (clarsimp simp: reorder_ep_def reorderEp_def)
  apply (rule corres_stateAssert_assume)
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule getEndpoint_corres)
       apply (rename_tac ep ep')
       apply (rule_tac F="ep \<noteq> Structures_A.endpoint.IdleEP" in corres_gen_asm)
       apply (rule_tac r'="(=)" in corres_split)
          apply (rule corres_trivial)
          apply (case_tac ep; clarsimp simp: get_ep_queue_def getEpQueue_def ep_relation_def)
         apply clarsimp
         apply (rule corres_split)
            apply (rule tcbEPDequeue_corres)
            apply clarsimp
           apply (rule corres_split)
              apply clarsimp
              apply (rule tcbEPAppend_corres)
             apply (rule setEndpoint_corres)
             apply (case_tac ep; clarsimp simp: ep_relation_def updateEpQueue_def)
            apply wp
           apply wp
          apply (rule tcb_ep_dequeue_rv_wf')
         apply (rule tcbEPDequeue_rv_wf')
        apply clarsimp
        apply (wpsimp simp: get_ep_queue_def)
       apply (wpsimp simp: getEpQueue_def)
      apply (wp get_simple_ko_wp)
     apply (wp getEndpoint_wp)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def ep_blocked_def)
    apply (frule invs_valid_objs)
    apply (erule (1) valid_objsE[where x=t])
    apply (clarsimp simp: valid_obj_def valid_tcb_def )
    apply (prop_tac "ep_at a' s")
     apply (clarsimp simp: valid_tcb_state_def split: Structures_A.thread_state.splits)
    apply (clarsimp simp: obj_at_def)
    apply (frule invs_valid_objs)
    apply (erule (1) valid_objsE[where x=a'])
    apply (clarsimp simp: valid_obj_def valid_ep_def)
    apply (frule invs_sym_refs)
    apply (drule_tac p=t in sym_refs_ko_atD[rotated])
     apply (simp add: obj_at_def)
    apply (fastforce simp: obj_at_def is_tcb_def split: if_splits Structures_A.thread_state.splits)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKO_eq projectKO_tcb epBlocked_def)
   apply (frule invs_valid_objs')
   apply (erule (1) valid_objsE'[where x=t])
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def)
   apply (prop_tac "ep_at' a' s")
    apply (clarsimp simp: valid_tcb_state'_def obj_at'_def projectKO_eq projectKO_ep
                   split: thread_state.splits)
   apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_ep)
   apply (frule invs_valid_objs')
   apply (erule (1) valid_objsE'[where x=a'])
   apply (clarsimp simp: valid_obj'_def valid_ep'_def)
   apply (drule_tac p=t and ko=obj in sym_refs_ko_atD'[rotated])
    apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb)
   apply (fastforce simp: refs_of_rev' ko_wp_at'_def obj_at'_def projectKO_eq projectKO_tcb
                   split: thread_state.splits if_splits endpoint.splits)
  apply (clarsimp simp: sym_refs_asrt_def)
  done

lemma threadSetPriority_valid_tcbs'[wp]:
  "\<lbrace>valid_tcbs' and K (prio \<le> maxPriority)\<rbrace>
   threadSet (tcbPriority_update (\<lambda>_. prio)) t
   \<lbrace>\<lambda>_. valid_tcbs'\<rbrace>"
  apply (wp threadSet_valid_tcbs')
  apply (fastforce simp: valid_tcbs'_def valid_tcb'_def tcb_cte_cases_def
                         obj_at'_def projectKO_eq projectKO_tcb)
  done

lemma threadSetPriority_onRunning_corres:
  "corres dc (valid_pspace and weak_valid_sched_action and active_scs_valid
              and tcb_at t and K (prio \<le> maxPriority))
             (\<lambda>s. invs' s \<and> tcb_at' t s)
             (do d <- thread_get tcb_domain t;
                 p <- thread_get tcb_priority t;
                 queue <- get_tcb_queue d p;
                 cur <- gets cur_thread;
                 if t \<in> set queue \<or> t = cur
                 then do y <- tcb_sched_action tcb_sched_dequeue t;
                         y <- thread_set_priority t prio;
                         y <- tcb_sched_action tcb_sched_enqueue t;
                         reschedule_required od
                 else thread_set_priority t prio od)
             (threadSetPriority_onRunning t prio)"
  apply (rule corres_gen_asm')
  apply (simp add: threadSetPriority_onRunning_def thread_set_priority_def
                   threadSetPriority_def epBlocked_def ntfnBlocked_def get_tcb_queue_def)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp])
    apply (rule corres_symb_exec_l[OF _ _ thread_get_sp])
      apply (rule corres_symb_exec_l[OF _ _ gets_sp])
        apply (rule corres_symb_exec_r[OF _ threadGet_sp'])
          apply (rule stronger_corres_guard_imp)
            apply (rule_tac F="t \<in> set (queues d p) = queued" in corres_gen_asm)
            apply (rule corres_split)
               apply (rule getCurThread_corres)
              apply (rule corres_if)
                apply clarsimp
               apply (rule corres_split_nor)
                  apply (rule tcbSchedDequeue_corres)
                 apply (rule corres_split_nor)
                    apply (rule threadset_corresT)
                      apply (clarsimp simp: tcb_relation_def)
                     apply (clarsimp simp: tcb_cap_cases_def)
                    apply (clarsimp simp: tcb_cte_cases_def)
                   apply (rule corres_split_nor)
                      apply (rule tcbSchedEnqueue_corres)
                     apply (rule rescheduleRequired_corres)
                    apply wp
                   apply wp
                  apply (wpsimp wp: thread_set_weak_valid_sched_action)
                 apply (wpsimp wp: threadSet_valid_queues_no_state threadSet_valid_queues'_no_state
                                   threadSet_valid_release_queue threadSet_valid_release_queue')
                apply wp
               apply (rule_tac Q'="\<lambda>_ s. tcb_at' t s \<and> valid_tcbs' s \<and>
                                        valid_queues s \<and> valid_queues' s \<and>
                                        valid_release_queue s \<and> valid_release_queue' s \<and>
                                        (\<forall>d p. t \<notin> set (ksReadyQueues s (d,p)))"
                            in hoare_strengthen_post[rotated])
                apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
               apply (wp tcbSchedDequeue_nonq tcbSchedDequeue_valid_queues hoare_vcg_all_lift)
              apply (rule threadset_corresT)
                apply (clarsimp simp: tcb_relation_def)
               apply (clarsimp simp: tcb_cap_cases_def)
              apply (clarsimp simp: tcb_cte_cases_def)
             apply wp
            apply wp
           apply (frule state_relation_pspace_relation)
           apply (clarsimp simp: invs'_def valid_pspace_def pspace_relation_def
                                  obj_at_def is_tcb_def obj_at'_def projectKO_eq projectKO_tcb)
           apply (drule_tac x=t in bspec)
            apply clarsimp
           apply (clarsimp simp: other_obj_relation_def)
           apply (drule state_relation_ready_queues_relation)
           apply (fastforce simp: tcb_relation_def ready_queues_relation_def
                                  obj_at'_def projectKO_eq projectKO_tcb inQ_def
                                  valid_queues_def valid_queues'_def valid_queues_no_bitmap_def)
          apply clarsimp
          apply (frule invs'_valid_tcbs')
          apply (clarsimp simp: invs'_def valid_tcbs'_def
                                valid_tcb'_def obj_at'_def projectKO_eq projectKO_tcb)
         apply (wpsimp wp: thread_get_exs_valid simp: thread_get_def tcb_at_def)+
  done

lemma setPriority:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t and (\<lambda>_. prio \<le> maxPriority))
             (set_priority t prio) (setPriority t prio)"
  apply (simp add: setPriority_def set_priority_def runnable'_case_thread_state_If)
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac r'=thread_state_relation in corres_split)
       apply (rule getThreadState_corres)
      apply (rule corres_if)
        apply (case_tac rv; simp add: thread_state_relation_def)
       apply (rule threadSetPriority_onRunning_corres)
      apply (rule corres_split)
         apply (wpsimp wp: threadset_corresT simp: thread_set_priority_def threadSetPriority_def)
           apply (clarsimp simp: tcb_relation_def)
          apply (clarsimp simp: tcb_cap_cases_def)
         apply (clarsimp simp: tcb_cte_cases_def)
        apply (rule corres_split)
           apply (clarsimp simp: maybeM_def case_option_If2 split del: if_split)
           apply (rule corres_if)
             apply (case_tac rv; simp add: ep_blocked_def epBlocked_def)
            apply (rule reorder_ep_corres)
            apply (case_tac rv; simp add: ep_blocked_def epBlocked_def)
           apply clarsimp
          apply (clarsimp simp: maybeM_def case_option_If2 split del: if_split)
          apply (rule corres_if)
            apply (case_tac rv; simp add: ntfn_blocked_def ntfnBlocked_def)
           apply (rule reorder_ntfn_corres)
           apply (case_tac rv; simp add: ntfn_blocked_def ntfnBlocked_def)
          apply (rule corres_trivial, clarsimp)
         apply (wpsimp wp: hoare_vcg_const_imp_lift simp: if_fun_split)
        apply (wpsimp wp: hoare_vcg_const_imp_lift reorderEp_invs' simp: if_fun_split)
       apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift simp: if_fun_split)
      apply (subgoal_tac "ep_blocked rv = epBlocked rv' \<and> ntfn_blocked rv = ntfnBlocked rv'")
       apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift
                         threadSet_valid_objs_tcbPriority_update threadSetPriority_invs'
                   simp: if_fun_split)
      apply (case_tac rv; simp add: ep_blocked_def epBlocked_def ntfn_blocked_def ntfnBlocked_def)
     apply (wp gts_wp)
    apply (wp gts_wp')
   apply (fastforce simp: pred_tcb_at_def obj_at_def)
  apply (drule ready_qs_runnable_cross; clarsimp simp: ready_qs_runnable_def)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  apply (fastforce simp: invs'_def pred_tcb_at'_def obj_at'_def projectKO_eq projectKO_tcb
                  dest!: valid_queues_not_runnable_not_queued)
  done

lemma setMCPriority_corres: "corres dc (tcb_at t) (tcb_at' t) (set_mcpriority t mcp) (setMCPriority t mcp)"
  apply (rule corres_guard_imp)
    apply (clarsimp simp: setMCPriority_def set_mcpriority_def)
    apply (rule threadset_corresT)
       by (clarsimp simp: tcb_relation_def tcb_cap_cases_tcb_mcpriority tcb_cte_cases_def)+

definition
 "out_rel fn fn' v v' \<equiv>
     ((v = None) = (v' = None)) \<and>
     (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow>
                 tcb_relation (case_option id fn v tcb)
                              (case_option id fn' v' tcb'))"

lemma out_corresT:
  assumes x: "\<And>tcb v. \<forall>(getF, setF)\<in>ran tcb_cap_cases. getF (fn v tcb) = getF tcb"
  assumes y: "\<And>v. \<forall>tcb. \<forall>(getF, setF)\<in>ran tcb_cte_cases. getF (fn' v tcb) = getF tcb"
  shows
  "out_rel fn fn' v v' \<Longrightarrow>
     corres dc (tcb_at t and pspace_aligned and pspace_distinct)
               \<top>
       (option_update_thread t fn v)
       (case_option (return ()) (\<lambda>x. threadSet (fn' x) t) v')"
  apply (case_tac v, simp_all add: out_rel_def
                       option_update_thread_def)
  apply (clarsimp simp add: threadset_corresT [OF _ x y])
  done

lemmas out_corres = out_corresT [OF _ all_tcbI, OF ball_tcb_cap_casesI ball_tcb_cte_casesI]

lemma tcbSchedDequeue_sch_act_simple[wp]:
  "tcbSchedDequeue t \<lbrace>sch_act_simple\<rbrace>"
  by (wpsimp simp: sch_act_simple_def)

lemma tcbSchedNext_update_tcb_cte_cases:
  "(a, b) \<in> ran tcb_cte_cases \<Longrightarrow> a (tcbPriority_update f tcb) = a tcb"
  unfolding tcb_cte_cases_def
  by (case_tac tcb; fastforce simp: objBits_simps')

lemma threadSet_priority_invs':
  "\<lbrace>invs' and tcb_at' t and K (p \<le> maxPriority)\<rbrace>
   threadSet (tcbPriority_update (\<lambda>_. p)) t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: invs'_def valid_state'_def split del: if_split)
  apply (wp threadSet_valid_pspace'
            threadSet_sch_actT_P[where P=False, simplified]
            threadSet_state_refs_of'T[where f'=id]
            threadSet_iflive'T
            threadSet_ifunsafe'T
            threadSet_idle'T
            valid_irq_node_lift
            valid_irq_handlers_lift''
            threadSet_ctes_ofT
            threadSet_not_inQ
            threadSet_ct_idle_or_in_cur_domain'
            threadSet_cur
            untyped_ranges_zero_lift
            sym_heap_sched_pointers_lift threadSet_valid_sched_pointers
            threadSet_tcbSchedPrevs_of threadSet_tcbSchedNexts_of
         | clarsimp simp: cteCaps_of_def tcbSchedNext_update_tcb_cte_cases | rule refl)+
  apply (clarsimp simp: o_def)
  by (auto simp: obj_at'_def)

lemma setP_invs':
  "\<lbrace>invs' and tcb_at' t and K (p \<le> maxPriority)\<rbrace> setPriority t p \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding setPriority_def
  by (wpsimp wp: rescheduleRequired_invs' threadSet_priority_invs')

crunch setPriority, setMCPriority
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation setPriority: typ_at_all_props' "setPriority t prio"
  by typ_at_props'
global_interpretation setMCPriority: typ_at_all_props' "setMCPriority t prio"
  by typ_at_props'
definition
  newroot_rel :: "(cap \<times> cslot_ptr) option \<Rightarrow> (capability \<times> machine_word) option \<Rightarrow> bool"
where
 "newroot_rel \<equiv> opt_rel (\<lambda>(cap, ptr) (cap', ptr').
                           cap_relation cap cap'
                         \<and> ptr' = cte_map ptr)"

function recursive :: "nat \<Rightarrow> ((nat \<times> nat), unit) nondet_monad"
where
  "recursive (Suc n) s = (do f \<leftarrow> gets fst; s \<leftarrow> gets snd; put ((f + s), n); recursive n od) s"
| "recursive 0       s = (modify (\<lambda>(a, b). (a, 0))) s"
  by (case_tac "fst x", fastforce+)

termination recursive
  apply (rule recursive.termination)
   apply (rule wf_measure [where f=fst])
  apply simp
  done

context begin interpretation Arch . (*FIXME: arch-split*)

lemma cte_map_tcb_0:
  "cte_map (t, tcb_cnode_index 0) = t"
  by (simp add: cte_map_def tcb_cnode_index_def)

lemma cte_map_tcb_1:
  "cte_map (t, tcb_cnode_index 1) = t + 2^cteSizeBits"
  by (simp add: cte_map_def tcb_cnode_index_def to_bl_1 objBits_defs cte_level_bits_def)

lemma sameRegion_corres2:
  "\<lbrakk> cap_relation c c'; cap_relation d d' \<rbrakk>
     \<Longrightarrow> same_region_as c d = sameRegionAs c' d'"
  by (erule(1) same_region_as_relation)

lemma sameObject_corres2:
  "\<lbrakk> cap_relation c c'; cap_relation d d' \<rbrakk>
     \<Longrightarrow> same_object_as c d = sameObjectAs c' d'"
  apply (frule(1) sameRegion_corres2[symmetric, where c=c and d=d])
  apply (case_tac c; simp add: sameObjectAs_def same_object_as_def
                               isCap_simps is_cap_simps bits_of_def)
   apply (case_tac d; simp)
   apply (case_tac d'; simp)
  apply (rename_tac arch_cap)
  apply clarsimp
  apply (case_tac d, (simp_all split: arch_cap.split)[13])
  apply (rename_tac arch_capa)
  apply (clarsimp simp add: ARM_H.sameObjectAs_def Let_def)
  apply (intro conjI impI)
   apply (case_tac arch_cap; simp add: isCap_simps del: not_ex)
   apply (case_tac arch_capa; clarsimp simp del: not_ex)
   apply fastforce
  apply (case_tac arch_cap; simp add: sameRegionAs_def isCap_simps)
  apply (case_tac arch_capa; simp)
  done

lemma checkCapAt_corres:
  assumes r: "cap_relation cap cap'"
  assumes c: "corres dc Q Q' f f'"
  assumes Q: "\<And>s. P s \<and> cte_wp_at (same_object_as cap) slot s \<Longrightarrow> Q s"
  assumes Q': "\<And>s. P' s \<and> cte_wp_at' (sameObjectAs cap' o cteCap) (cte_map slot) s \<Longrightarrow> Q' s"
  shows "corres dc (P and cte_at slot and invs) (P' and pspace_aligned' and pspace_distinct')
             (check_cap_at cap slot f)
             (checkCapAt cap' (cte_map slot) f')" using r c
  apply (simp add: check_cap_at_def checkCapAt_def liftM_def when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres])
      apply (rule corres_if [unfolded if_apply_def2])
        apply (erule(1) sameObject_corres2)
       apply assumption
      apply (rule corres_trivial, simp)
     apply (wp get_cap_wp getCTE_wp')+
   apply (fastforce elim: cte_wp_at_weakenE intro: Q)
  apply (fastforce elim: cte_wp_at_weakenE' intro: Q')
  done

lemma checkCapAt_weak_corres:
  assumes r: "cap_relation cap cap'"
  assumes c: "corres dc P P' f f'"
  shows "corres dc (P and cte_at slot and invs) (P' and pspace_aligned' and pspace_distinct')
             (check_cap_at cap slot f)
             (checkCapAt cap' (cte_map slot) f')"
  apply (rule checkCapAt_corres, rule r, rule c)
  apply auto
  done

defs
  assertDerived_def:
  "assertDerived src cap f \<equiv>
  do stateAssert (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap o cteCap) src s) []; f od"

lemma checkCapAt_cteInsert_corres:
  "cap_relation new_cap newCap \<Longrightarrow>
   corres dc (einvs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
                    and cte_at slot and K (is_cnode_or_valid_arch new_cap \<or> is_ep_cap new_cap)
                    and K (is_pt_cap new_cap \<or> is_pd_cap new_cap \<longrightarrow> cap_asid new_cap \<noteq> None)
                    and (\<lambda>s. is_ep_cap new_cap
                             \<longrightarrow> cte_wp_at (\<lambda>c. c = new_cap \<or> c = cap.NullCap) src_slot s)
                    and cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                                       \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                           pt_pd_asid c = pt_pd_asid new_cap) src_slot)
             (invs' and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) (cte_map (target, ref))
                    and valid_cap' newCap)
     (check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))))
     (checkCapAt newCap (cte_map src_slot)
      (checkCapAt (ThreadCap target) (cte_map slot)
       (assertDerived (cte_map src_slot) newCap (cteInsert newCap (cte_map src_slot) (cte_map (target, ref))))))"
  (is "_ \<Longrightarrow> corres _ (?pre1) (?pre2) _ _")
  apply (rule corres_guard_imp)
    apply (rule_tac P="?pre1" and P'="?pre2" in checkCapAt_corres, assumption)
      apply (rule checkCapAt_weak_corres, simp)
      apply (unfold assertDerived_def)[1]
      apply (rule corres_stateAssert_implied [where P'=\<top>])
       apply simp
       apply (erule cteInsert_corres [OF _ refl refl])
      apply clarsimp
      apply (drule cte_wp_at_norm [where p=src_slot])
      apply (case_tac src_slot)
      apply (clarsimp simp: state_relation_def)
      apply (drule (1) pspace_relation_cte_wp_at)
        apply fastforce
       apply fastforce
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (erule (2) is_derived_eq [THEN iffD1])
       apply (erule cte_wp_at_weakenE, rule TrueI)
      apply assumption
     apply clarsimp
     apply (rule conjI, fastforce)+
     apply (cases src_slot)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (rule conjI)
      apply (frule same_object_as_cap_master)
      apply (clarsimp simp: cap_master_cap_simps is_cnode_or_valid_arch_def
                            is_cap_simps is_valid_vtable_root_def
                     dest!: cap_master_cap_eqDs)
     apply (erule disjE)
      apply (erule(1) checked_insert_is_derived)
      apply (fastforce simp: is_derived_def is_cap_simps same_object_as_def cte_wp_at_caps_of_state)+
  done

definition
  "pt_pd_asid' cap \<equiv> case cap of
    ArchObjectCap (PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageDirectoryCap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemma untyped_derived_eq_from_sameObjectAs:
  "sameObjectAs cap cap2
    \<Longrightarrow> untyped_derived_eq cap cap2"
  by (clarsimp simp: untyped_derived_eq_def sameObjectAs_def2 isCap_Master)

lemmas pt_pd_asid'_simps [simp] =
  pt_pd_asid'_def [split_simps capability.split arch_capability.split option.split prod.split]

lemma checked_insert_tcb_invs'[wp]:
  "\<lbrace>invs' and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot
         and valid_cap' new_cap
         and K (slot \<in> cte_refs' (ThreadCap target) 0)
         and K (\<not> isReplyCap new_cap \<and> \<not> isIRQControlCap new_cap)\<rbrace>
     checkCapAt new_cap src_slot
      (checkCapAt (ThreadCap target) slot'
       (assertDerived src_slot new_cap (cteInsert new_cap src_slot slot))) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply if_weak_cong[cong]
  apply (simp add: checkCapAt_def liftM_def assertDerived_def stateAssert_def)
  apply (wp getCTE_cteCap_wp cteInsert_invs)
  apply (clarsimp split: option.splits)
  apply (subst(asm) tree_cte_cteCap_eq[unfolded o_def])
  apply (clarsimp split: option.splits)
  apply (rule conjI)
   apply (clarsimp simp: sameObjectAs_def3)
  apply (clarsimp simp: tree_cte_cteCap_eq
                        is_derived'_def untyped_derived_eq_from_sameObjectAs
                        ex_cte_cap_to'_cteCap)
  apply (erule sameObjectAsE)+
  apply (clarsimp simp: badge_derived'_def)
  apply (rule conjI)
   apply (rule_tac x=slot' in exI)
   apply fastforce
  apply (clarsimp simp: isCap_simps cteCaps_of_def)
  apply (erule(1) valid_irq_handlers_ctes_ofD)
  apply (clarsimp simp: invs'_def)
  done

lemma checkCap_inv:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> checkCapAt cap slot f \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding checkCapAt_def
  by (wp x | simp)+

lemma checkCap_wp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>"
  and PQ: "\<And>s. P s \<Longrightarrow> Q s"
  shows "\<lbrace>P\<rbrace> checkCapAt cap slot f \<lbrace>\<lambda>rv. Q\<rbrace>"
  unfolding checkCapAt_def
  apply (wp x)
   apply (rule hoare_strengthen_post[rotated])
    apply clarsimp
    apply (strengthen PQ)
    apply assumption
   apply simp
  apply (wp x | simp)+
  done

lemma isValidVTableRootD:
  "isValidVTableRoot cap
     \<Longrightarrow> isArchObjectCap cap \<and> isPageDirectoryCap (capCap cap)
             \<and> capPDMappedASID (capCap cap) \<noteq> None"
  by (simp add: isValidVTableRoot_def isCap_simps
         split: capability.split_asm arch_capability.split_asm option.split_asm)

lemma assertDerived_wp:
  "\<lbrace>P and (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) slot cap o cteCap) slot s)\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow>
  \<lbrace>P\<rbrace> assertDerived slot cap f \<lbrace>Q\<rbrace>"
  apply (simp add: assertDerived_def)
  apply wpsimp
  done

lemma assertDerived_wp_weak:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> assertDerived slot cap f \<lbrace>Q\<rbrace>"
  apply (wpsimp simp: assertDerived_def)
  done

lemma tcbMCP_caps_safe:
  "\<forall>tcb. \<forall>x\<in>ran tcb_cte_cases. (\<lambda>(getF, setF). getF (tcbMCP_update f tcb) = getF tcb) x"
  by (rule all_tcbI, rule ball_tcb_cte_casesI, simp+)

lemma tcbMCP_Queued_caps_safe:
  "\<forall>tcb. \<forall>x\<in>ran tcb_cte_cases. (\<lambda>(getF, setF). getF (tcbMCP_update f (tcbQueued_update g tcb)) = getF tcb) x"
  by (rule all_tcbI, rule ball_tcb_cte_casesI, simp+)

lemma setMCPriority_invs':
  "\<lbrace>invs' and tcb_at' t and K (prio \<le> maxPriority)\<rbrace> setMCPriority t prio \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding setMCPriority_def
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (wp threadSet_invs_trivial, (clarsimp simp: inQ_def)+)
  apply (clarsimp dest!: invs_valid_release_queue' simp: valid_release_queue'_def obj_at'_def)
  done

lemma valid_tcb'_tcbMCP_update:
  "\<lbrakk>valid_tcb' tcb s \<and> f (tcbMCP tcb) \<le> maxPriority\<rbrakk> \<Longrightarrow> valid_tcb' (tcbMCP_update f tcb) s"
  apply (simp add: valid_tcb'_def tcb_cte_cases_def)
  done

lemma setMCPriority_valid_objs'[wp]:
  "\<lbrace>valid_objs' and K (prio \<le> maxPriority)\<rbrace> setMCPriority t prio \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  unfolding setMCPriority_def
  including no_pre
  apply (simp add: threadSet_def)
  apply wp
   prefer 2
   apply (rule getObject_tcb_sp)
  apply (rule hoare_weaken_pre)
   apply (rule setObject_tcb_valid_objs)
  apply (clarsimp simp: valid_obj'_def)
  apply (frule (1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (simp add: valid_obj'_def)
  apply (subgoal_tac "tcb_at' t s")
   apply simp
   apply (rule valid_tcb'_tcbMCP_update)
   apply (fastforce  simp: obj_at'_def)+
  done

crunch setMCPriority
  for sch_act_simple[wp]: sch_act_simple
  (wp: ssa_sch_act_simple crunch_wps rule: sch_act_simple_lift simp: crunch_simps)

abbreviation "valid_option_prio \<equiv> case_option True (\<lambda>(p, auth). p \<le> maxPriority)"

definition valid_tcb_invocation :: "tcbinvocation \<Rightarrow> bool" where
   "valid_tcb_invocation i \<equiv> case i of
        ThreadControlSched _ _ _ p mcp _ \<Rightarrow> valid_option_prio p \<and> valid_option_prio mcp
      | _                           \<Rightarrow> True"

lemma threadcontrol_corres_helper1:
  "thread_set (tcb_ipc_buffer_update f) tptr \<lbrace>weak_valid_sched_action\<rbrace>"
  by (wpsimp wp: thread_set_weak_valid_sched_action)

lemma threadcontrol_corres_helper2:
  "is_aligned a msg_align_bits \<Longrightarrow>
   \<lbrace>invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and tcb_at' t\<rbrace>
   threadSet (tcbIPCBuffer_update (\<lambda>_. a)) t
   \<lbrace>\<lambda>_ s. Invariants_H.valid_queues s \<and> valid_queues' s \<and> weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp threadSet_invs_trivial threadSet_sch_act
      | strengthen  invs_valid_queues' invs_queues sch_act_wf_weak
      | clarsimp dest!: invs_valid_release_queue' simp: inQ_def valid_release_queue'_def obj_at'_def)+

lemma threadcontrol_corres_helper3:
  "\<lbrace> einvs and simple_sched_action\<rbrace>
   check_cap_at aaa (ab, ba) (check_cap_at (cap.ThreadCap a) slot (cap_insert aaa (ab, ba) (a, tcb_cnode_index 4)))
   \<lbrace>\<lambda>_. weak_valid_sched_action \<rbrace>"
  apply (wp check_cap_inv | simp add:)+
  by (clarsimp simp: weak_valid_sched_action_def get_tcb_def obj_at_def  valid_sched_def
                     valid_sched_action_def)

lemma threadcontrol_corres_helper4:
  "isArchObjectCap ac \<Longrightarrow>
  \<lbrace>invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
   and cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) (cte_map (a, tcb_cnode_index 4))
   and valid_cap' ac \<rbrace>
  checkCapAt ac (cte_map (ab, ba))
    (checkCapAt (capability.ThreadCap a) (cte_map slot)
       (assertDerived (cte_map (ab, ba)) ac (cteInsert ac (cte_map (ab, ba)) (cte_map (a, tcb_cnode_index 4)))))
  \<lbrace>\<lambda>_. Invariants_H.valid_queues and valid_queues' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>"
  apply (wpsimp | strengthen invs_valid_queues' invs_queues sch_act_wf_weak)+
  apply (wp checkCap_inv assertDerived_wp_weak)+
  apply (case_tac ac;
          clarsimp simp: capBadge_def isArchObjectCap_def isNotificationCap_def isEndpointCap_def
                         isReplyCap_def isIRQControlCap_def tcb_cnode_index_def cte_map_def cte_wp_at'_def
                         cte_level_bits_def)
  done

lemma threadSet_invs_trivialT2:
  assumes x: "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  assumes z: "\<forall>tcb. tcbState (F tcb) = tcbState tcb"
  assumes a: "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
  assumes s: "\<forall>tcb. tcbSchedContext (F tcb) = tcbSchedContext tcb"
  assumes y: "\<forall>tcb. tcbYieldTo (F tcb) = tcbYieldTo tcb"
  assumes v: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes u: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  assumes b: "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  shows
  "\<lbrace>\<lambda>s. invs' s
        \<and> (\<forall>tcb. is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits)
        \<and> tcb_at' t s
        \<and> (\<forall>d p. (\<exists>tcb. inQ d p tcb \<and> \<not> inQ d p (F tcb)) \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))
        \<and> (\<forall>ko d p. ko_at' ko t s \<and> inQ d p (F ko) \<and> \<not> inQ d p ko \<longrightarrow> t \<in> set (ksReadyQueues s (d, p)))
        \<and> ((\<exists>tcb. tcbInReleaseQueue tcb \<and> \<not> tcbInReleaseQueue (F tcb)) \<longrightarrow> t \<notin> set (ksReleaseQueue s))
        \<and> (\<forall>ko. ko_at' ko t s \<and> tcbInReleaseQueue (F ko) \<and> \<not> tcbInReleaseQueue ko \<longrightarrow> t \<in> set (ksReleaseQueue s))
        \<and> ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)) \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
        threadSet F t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  note threadSet_sch_actT_P[where P=False, simplified]
  have r: "\<forall>tcb. tcb_st_refs_of' (tcbState (F tcb)) = tcb_st_refs_of' (tcbState tcb) \<and>
                 valid_tcb_state' (tcbState (F tcb)) = valid_tcb_state' (tcbState tcb)"
    by (auto simp: z)
  show ?thesis
    apply (simp add: invs'_def split del: if_split)
    apply (rule hoare_pre)
  apply (rule hoare_gen_asm [where P="(\<forall>tcb. is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits)"])
     apply (wp x v u b
               threadSet_valid_pspace'T
               threadSet_sch_actT_P[where P=False, simplified]
               threadSet_valid_queues threadSet_valid_release_queue
               threadSet_state_refs_of'T[where f'=id]
               threadSet_iflive'T
               threadSet_ifunsafe'T
               threadSet_idle'T
               threadSet_global_refsT
               irqs_masked_lift
               valid_irq_node_lift
               valid_irq_handlers_lift''
               threadSet_ctes_ofT
               threadSet_not_inQ
               threadSet_ct_idle_or_in_cur_domain'
               threadSet_valid_dom_schedule'
               threadSet_valid_queues' threadSet_valid_release_queue'
               threadSet_cur
               untyped_ranges_zero_lift
            | clarsimp simp: r y z a s cteCaps_of_def | rule refl)+
   apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def valid_release_queue'_def)
   apply (clarsimp simp: cur_tcb'_def valid_irq_node'_def valid_queues'_def  o_def)
   by (intro conjI; fastforce)
qed

lemma threadSet_valid_queues'_no_state2:
  "\<lbrakk> \<And>tcb. tcbQueued tcb = tcbQueued (f tcb);
     \<And>tcb. tcbState tcb = tcbState (f tcb);
     \<And>tcb. tcbPriority tcb = tcbPriority (f tcb);
     \<And>tcb. tcbDomain tcb = tcbDomain (f tcb) \<rbrakk>
   \<Longrightarrow> \<lbrace>valid_queues'\<rbrace> threadSet f t \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: valid_queues'_def threadSet_def obj_at'_real_def
              split del: if_split)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
     apply (wp setObject_ko_wp_at | simp add: objBits_simps')+
    apply (wp getObject_tcb_wp updateObject_default_inv
           | simp split del: if_split)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs
                        objBits_simps addToQs_def
             split del: if_split cong: if_cong)
  apply (fastforce simp: projectKOs inQ_def split: if_split_asm)
  done

lemma getThreadBufferSlot_dom_tcb_cte_cases:
  "\<lbrace>\<top>\<rbrace> getThreadBufferSlot a \<lbrace>\<lambda>rv s. rv \<in> (+) a ` dom tcb_cte_cases\<rbrace>"
  by (wpsimp simp: tcb_cte_cases_def getThreadBufferSlot_def locateSlot_conv cte_level_bits_def
                   tcbIPCBufferSlot_def)

lemma cteDelete_it [wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> cteDelete slot e \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  by (rule cteDelete_preservation) (wp | clarsimp)+

lemmas threadSet_invs_trivial2 =
  threadSet_invs_trivialT2 [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma valid_tcb_ipc_buffer_update:
  "\<And>buf s. is_aligned buf msg_align_bits
   \<Longrightarrow> (\<forall>tcb. valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbIPCBuffer_update (\<lambda>_. buf) tcb) s)"
  by (simp add: valid_tcb'_def tcb_cte_cases_def)

end

consts
  copyregsets_map :: "arch_copy_register_sets \<Rightarrow> Arch.copy_register_sets"

context begin interpretation Arch . (*FIXME: arch-split*)

primrec
  tcbinv_relation :: "tcb_invocation \<Rightarrow> tcbinvocation \<Rightarrow> bool"
where
  "tcbinv_relation (tcb_invocation.ReadRegisters a b c d) x
    = (x = tcbinvocation.ReadRegisters a b c (copyregsets_map d))"
| "tcbinv_relation (tcb_invocation.WriteRegisters a b c d) x
    = (x = tcbinvocation.WriteRegisters a b c (copyregsets_map d))"
| "tcbinv_relation (tcb_invocation.CopyRegisters a b c d e f g) x
    = (x = tcbinvocation.CopyRegisters a b c d e f (copyregsets_map g))"
| "tcbinv_relation (tcb_invocation.ThreadControlCaps t slot fault_h time_h croot vroot ipcb) x
   = (\<exists>sl' fault_h' time_h' croot' vroot' ipcb'.
        ({fault_h, time_h, croot, vroot, option_map undefined ipcb} \<noteq> {None} \<longrightarrow> sl' = cte_map slot) \<and>
        newroot_rel fault_h fault_h' \<and> newroot_rel time_h time_h' \<and>
        newroot_rel croot croot' \<and> newroot_rel vroot vroot' \<and>
        (case ipcb of None \<Rightarrow> ipcb' = None
                    | Some (vptr, g'') \<Rightarrow> \<exists>g'''. ipcb' = Some (vptr, g''') \<and> newroot_rel g'' g''') \<and>
        (x = tcbinvocation.ThreadControlCaps t sl' fault_h' time_h' croot' vroot' ipcb'))"
| "tcbinv_relation (tcb_invocation.ThreadControlSched t sl sc_fault_h mcp prio sc_opt) x
    = (\<exists>sl' sc_fault_h'.
         newroot_rel sc_fault_h sc_fault_h'\<and> (sc_fault_h \<noteq> None \<longrightarrow> sl' = cte_map sl) \<and>
         x = tcbinvocation.ThreadControlSched t sl' sc_fault_h' mcp prio sc_opt)"
| "tcbinv_relation (tcb_invocation.Suspend a) x
    = (x = tcbinvocation.Suspend a)"
| "tcbinv_relation (tcb_invocation.Resume a) x
    = (x = tcbinvocation.Resume a)"
| "tcbinv_relation (tcb_invocation.NotificationControl t ntfnptr) x
    = (x = tcbinvocation.NotificationControl t ntfnptr)"
| "tcbinv_relation (tcb_invocation.SetTLSBase ref w) x
    = (x = tcbinvocation.SetTLSBase ref w)"

primrec
  tcb_inv_wf' :: "tcbinvocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "tcb_inv_wf' (tcbinvocation.Suspend t)
             = (tcb_at' t and ex_nonz_cap_to' t)"
| "tcb_inv_wf' (tcbinvocation.Resume t)
             = (tcb_at' t and ex_nonz_cap_to' t)"
| "tcb_inv_wf' (tcbinvocation.ThreadControlCaps t slot fault_h time_h croot vroot ipcb)
             = (tcb_at' t and ex_nonz_cap_to' t and
                case_option \<top> (valid_cap' o fst) fault_h and
                case_option \<top> (valid_cap' o fst) time_h and
                case_option \<top> (valid_cap' o fst) croot and
                K (case_option True (isCNodeCap o fst) croot) and
                case_option \<top> (valid_cap' o fst) vroot and
                K (case_option True (isValidVTableRoot o fst) vroot) and
                K (case_option True (isValidFaultHandler o fst) fault_h) and
                K (case_option True (isValidFaultHandler o fst) time_h) and
                K (case_option True ((\<lambda>v. is_aligned v msg_align_bits) o fst) ipcb) and
                K (case_option True (case_option True (isArchObjectCap o fst) o snd) ipcb) and
                case_option \<top> (case_option \<top> (valid_cap' o fst) o snd) ipcb and
                (\<lambda>s. {fault_h, time_h, croot, vroot, option_map undefined ipcb} \<noteq> {None} \<longrightarrow>
                     cte_at' slot s))"
| "tcb_inv_wf' (tcbinvocation.ThreadControlSched t slot sc_fault_h mcp_auth p_auth sc_opt)
             = (tcb_at' t and ex_nonz_cap_to' t and
                case_option \<top> (valid_cap' o fst) sc_fault_h and
                K (case_option True (isValidFaultHandler o fst) sc_fault_h) and
                (\<lambda>s. sc_fault_h \<noteq> None \<longrightarrow> cte_at' slot s) and
                K (valid_option_prio p_auth \<and> valid_option_prio mcp_auth) and
                (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at' ((\<le>) pr) auth s) p_auth) and
                (\<lambda>s. case_option True (\<lambda>(m, auth). mcpriority_tcb_at' ((\<le>) m) auth s) mcp_auth) and
                case_option \<top> (\<lambda>sc_opt'. case_option \<top> (\<lambda>p. sc_at' p and ex_nonz_cap_to' p) sc_opt') sc_opt)"
| "tcb_inv_wf' (tcbinvocation.ReadRegisters src susp n arch)
             = (tcb_at' src and ex_nonz_cap_to' src)"
| "tcb_inv_wf' (tcbinvocation.WriteRegisters dest resume values arch)
             = (tcb_at' dest and ex_nonz_cap_to' dest)"
| "tcb_inv_wf' (tcbinvocation.CopyRegisters dest src suspend_source resume_target
                 trans_frame trans_int trans_arch)
             = (tcb_at' dest and tcb_at' src and ex_nonz_cap_to' src and ex_nonz_cap_to' dest)"
| "tcb_inv_wf' (tcbinvocation.NotificationControl t ntfn)
             = (tcb_at' t and ex_nonz_cap_to' t
                  and (case ntfn of None \<Rightarrow> \<top>
                          | Some ntfnptr \<Rightarrow> obj_at' (\<lambda>ko. ntfnBoundTCB ko = None
                                           \<and> (\<forall>q. ntfnObj ko \<noteq> WaitingNtfn q)) ntfnptr
                                          and ex_nonz_cap_to' ntfnptr
                                          and bound_tcb_at' ((=) None) t) )"
| "tcb_inv_wf' (tcbinvocation.SetTLSBase ref w)
             = (tcb_at' ref and ex_nonz_cap_to' ref)"

lemma installTCBCap_corres_helper:
  "n \<in> {0,1,3,4} \<Longrightarrow>
   (if n = 0 then withoutPreemption $ getThreadCSpaceRoot target
    else if n = 1 then withoutPreemption $ getThreadVSpaceRoot target
         else if n = 3 then withoutPreemption $ getThreadFaultHandlerSlot target
               else if n = 4 then withoutPreemption $ getThreadTimeoutHandlerSlot target
                    else haskell_fail []) = returnOk (cte_map (target, tcb_cnode_index n))"
  by (auto simp: getThreadFaultHandlerSlot_def getThreadVSpaceRoot_def getThreadCSpaceRoot_def
                 getThreadTimeoutHandlerSlot_def locateSlotTCB_def locateSlot_conv returnOk_def
                 return_def liftE_def bind_def tcbFaultHandlerSlot_def tcbTimeoutHandlerSlot_def
                 tcbCTableSlot_def tcbVTableSlot_def tcb_cnode_index_def cte_map_def to_bl_def)

lemma installTCBCap_corres:
  "\<lbrakk> newroot_rel slot_opt slot_opt'; slot_opt \<noteq> None \<longrightarrow> slot' = cte_map slot; n \<in> {0,1,3,4} \<rbrakk> \<Longrightarrow>
     corres (dc \<oplus> dc)
            (\<lambda>s. einvs s \<and> valid_machine_time s \<and> simple_sched_action s
                 \<and> cte_at (target, tcb_cnode_index n) s \<and> current_time_bounded s \<and>
                 (\<forall>new_cap src_slot.
                   slot_opt = Some (new_cap, src_slot) \<longrightarrow>
                   (is_cnode_or_valid_arch new_cap \<or> valid_fault_handler new_cap) \<and>
                   (new_cap \<noteq> cap.NullCap \<longrightarrow>
                     s \<turnstile> new_cap \<and>
                     (is_ep_cap new_cap \<and> (target,tcb_cnode_index n) \<noteq> src_slot \<longrightarrow>
                        cte_wp_at valid_fault_handler (target, tcb_cnode_index n) s \<and>
                        cte_wp_at ((=) new_cap) src_slot s) \<and>
                     no_cap_to_obj_dr_emp new_cap s \<and>
                     cte_at src_slot s \<and> cte_at slot s)))
            (\<lambda>s. invs' s \<and> sch_act_simple s \<and> cte_at' (cte_map (target, tcb_cnode_index n)) s \<and>
                 (\<forall>newCap srcSlot.
                   slot_opt' = Some (newCap, srcSlot) \<longrightarrow>
                   newCap \<noteq> NullCap \<longrightarrow>
                     valid_cap' newCap s))
            (install_tcb_cap target slot n slot_opt)
            (installTCBCap target slot' n slot_opt')"
  apply (simp only: install_tcb_cap_def installTCBCap_def
                    installTCBCap_corres_helper unlessE_whenE)
  apply (case_tac slot_opt; clarsimp simp: newroot_rel_def corres_returnOk)
  apply (rule corres_guard_imp)
    apply (rule corres_split_norE)
       apply (rule cteDelete_corres)
      apply (rule corres_whenE)
        apply fastforce
       apply clarsimp
       apply (rule checkCapAt_cteInsert_corres)
       apply simp
      apply simp
     apply ((wp cap_delete_valid_sched cap_delete_deletes_fh cap_delete_deletes cap_delete_cte_at
                cap_delete_valid_cap cteDelete_invs' cteDelete_deletes hoare_vcg_const_imp_liftE_R
             | strengthen use_no_cap_to_obj_asid_strg)+)
   apply (fastforce simp: is_cap_simps valid_fault_handler_def
                          is_cnode_or_valid_arch_def cte_wp_at_def)+
  done

lemma installTCBCap_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>newCap srcSlot. slot_opt = Some (newCap,srcSlot) \<longrightarrow>
                                      sch_act_simple s \<and> valid_cap' newCap s \<and>
                                      \<not> isReplyCap newCap \<and> \<not> isIRQControlCap newCap)\<rbrace>
   installTCBCap target slot n slot_opt
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp only: installTCBCap_def tcbCTableSlot_def tcbVTableSlot_def tcbFaultHandlerSlot_def
                    getThreadCSpaceRoot_def getThreadVSpaceRoot_def getThreadFaultHandlerSlot_def)
  apply (wpsimp split_del: if_split
                       wp: checked_insert_tcb_invs cteDelete_invs'
                           cteDelete_deletes hoare_vcg_const_imp_liftE_R hoare_vcg_if_lift_ER
                     simp: locateSlotBasic_def maybe_def returnOk_bindE
                           getThreadTimeoutHandlerSlot_def locateSlotTCB_def)+
  apply (auto simp: objBits_def objBitsKO_def cteSizeBits_def tcbTimeoutHandlerSlot_def)
  done

lemma installThreadBuffer_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>newCap srcSlot. slot_opt = Some (newCap,srcSlot) \<longrightarrow>
                                     sch_act_simple s \<and> tcb_at' target s \<and>
                                     is_aligned newCap msg_align_bits \<and>
                                     (\<forall>x. (\<exists>y. srcSlot = Some (x, y)) \<longrightarrow>
                                          valid_cap' x s \<and> capBadge x = None \<and>
                                          \<not> isReplyCap x \<and> \<not> isIRQControlCap x))\<rbrace>
   installThreadBuffer target slot slot_opt
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding installThreadBuffer_def maybe_def returnOk_bindE
  apply (wpsimp wp: hoare_weak_lift_imp hoare_vcg_all_lift threadSet_invs_trivial2)
     apply (wpsimp wp: threadSet_cte_wp_at'T)
      apply (clarsimp simp: tcbIPCBuffer_update_def)
      apply (case_tac tcb; fastforce simp: tcb_cte_cases_def)
     apply wpsimp+
    apply (wpsimp wp: cteDelete_invs' cteDelete_deletes getThreadBufferSlot_inv
                      getThreadBufferSlot_dom_tcb_cte_cases hoare_vcg_const_imp_liftE_R
                      hoare_vcg_all_liftE_R hoare_vcg_imp_lift hoare_vcg_all_lift)+
  done

crunch installTCBCap
  for tcb_at'[wp]: "tcb_at' a"
  and cte_at'[wp]: "cte_at' p"
  (wp: crunch_wps checkCap_inv assertDerived_wp_weak simp: crunch_simps)

lemma installTCBCap_valid_cap'[wp]:
  "installTCBCap pa pb pc pd \<lbrace>valid_cap' c\<rbrace>"
  unfolding getThreadTimeoutHandlerSlot_def getThreadFaultHandlerSlot_def
            getThreadVSpaceRoot_def getThreadCSpaceRoot_def installTCBCap_def
  by (wpsimp wp: checkCap_inv crunch_wps assertDerived_wp_weak | intro conjI)+

lemma cteInsert_sa_simple[wp]:
  "cteInsert newCap srcSlot destSlot \<lbrace>sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def, wp)

lemma installTCBCap_sch_act_simple:
  "\<lbrace>invs' and sch_act_simple and tcb_at' a\<rbrace>
    installTCBCap a sl n sl_opt
   \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  unfolding getThreadTimeoutHandlerSlot_def getThreadFaultHandlerSlot_def
            getThreadVSpaceRoot_def getThreadCSpaceRoot_def installTCBCap_def
  by (wpsimp wp: checkCap_inv assertDerived_wp_weak cteDelete_sch_act_simple | rule conjI)+

lemma is_aligned_tcb_ipc_buffer_update:
  "is_aligned aa msg_align_bits \<longrightarrow>
   valid_tcb a tcb s \<longrightarrow> valid_tcb a (tcb\<lparr>tcb_ipc_buffer := aa\<rparr>) s"
  by (clarsimp simp: valid_tcb_def ran_tcb_cap_cases valid_ipc_buffer_cap_def
              split: cap.splits arch_cap.splits bool.splits)

lemma is_aligned_tcbIPCBuffer_update:
  "is_aligned aa msg_align_bits \<longrightarrow>
   valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbIPCBuffer_update (\<lambda>_. aa) tcb) s"
  by (clarsimp simp: valid_tcb'_def tcb_cte_cases_def)

lemma checkCap_inv2:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P and Q ()\<rbrace> checkCapAt cap slot f \<lbrace>Q\<rbrace>"
  unfolding checkCapAt_def
  by (wp x getCTE_wp', clarsimp)

crunch cteInsert
  for valid_release_queue[wp]: "valid_release_queue"
  and valid_release_queue'[wp]: "valid_release_queue'"
  and valid_queues'[wp]: "valid_queues'"
  (wp: crunch_wps simp: crunch_simps)

lemma installThreadBuffer_corres_helper:
  "getThreadBufferSlot a = return (cte_map (a, tcb_cnode_index 2))"
  by (simp add: getThreadBufferSlot_def locateSlot_conv cte_map_def
                cte_level_bits_def tcb_cnode_index_def tcbIPCBufferSlot_def)

lemma installThreadBuffer_corres:
  assumes "case_option (g' = None) (\<lambda>(vptr,g''). \<exists>g'''. g' = Some (vptr, g''') \<and> newroot_rel g'' g''') g"
  and     "g \<noteq> None \<longrightarrow> sl' = cte_map slot"
  shows "corres (dc \<oplus> dc)
         (einvs and valid_machine_time and simple_sched_action and tcb_at a
                and (case_option \<top> (\<lambda>(_,sl). cte_at slot and current_time_bounded and
                        (case_option \<top> (\<lambda>(newCap,srcSlot). cte_at srcSlot and valid_cap newCap and
                                                            no_cap_to_obj_dr_emp newCap) sl)) g)
                and K (case_option True (\<lambda>(x,v).
                           case_option True (\<lambda>(c,sl). is_cnode_or_valid_arch c \<and> is_arch_cap c \<and>
                                                      is_aligned x msg_align_bits \<and>
                                                      valid_ipc_buffer_cap c x) v) g))
         (invs' and sch_act_simple and tcb_at' a
                and (case_option \<top> (\<lambda>(_,sl).
                         (case_option \<top> (\<lambda>(newCap,srcSlot). valid_cap' newCap) sl)) g')
                and K (case_option True (\<lambda>(x, v). is_aligned x msg_align_bits \<and>
                           (case_option True (\<lambda>(ac, _). isArchObjectCap ac) v)) g'))
         (install_tcb_frame_cap a slot g)
         (installThreadBuffer a sl' g')"
  using assms
  apply -
  apply (simp only: install_tcb_frame_cap_def installThreadBuffer_def K_def)
  apply (rule corres_gen_asm2)
  apply (rule corres_guard_imp[where P=P and P'=P' and Q="P and cte_at (a, tcb_cnode_index 2)"
                                         and Q'="P' and cte_at' (cte_map (a, cap))" for P P' a cap])
    apply (cases g, simp add: returnOk_def)
    apply (clarsimp simp: installThreadBuffer_corres_helper bind_liftE_distrib liftE_bindE)
    apply (rule corres_guard_imp)
      apply (rule corres_split_norE)
         apply (rule cteDelete_corres)
        apply (rule_tac F="is_aligned aa msg_align_bits" in corres_gen_asm2)
        apply (rule corres_split_nor)
           apply (rule threadset_corres; simp add: tcb_relation_def)
          apply (rule corres_split_nor)
             apply (simp only: case_option_If2)
             apply (rule corres_if3)
               apply (clarsimp simp: newroot_rel_def split: if_splits)
              apply (clarsimp simp: newroot_rel_def)
              apply wpfix
              apply (erule checkCapAt_cteInsert_corres)
             apply (rule_tac P=\<top> and P'=\<top> in corres_inst, clarsimp)
            apply (rule corres_split[OF getCurThread_corres], clarsimp)
              apply (rule corres_when[OF refl rescheduleRequired_corres])
             apply (rule_tac Q'="\<lambda>_. valid_objs and weak_valid_sched_action
                                    and active_scs_valid and pspace_aligned and pspace_distinct"
                          in hoare_strengthen_post[rotated], fastforce)
             apply wp
            apply (rule_tac Q'="\<lambda>_. valid_objs' and valid_release_queue_iff
                                               and valid_queues and valid_queues'"
                         in hoare_strengthen_post[rotated], fastforce)
            apply wp
           apply (wpsimp wp: check_cap_inv2 cap_insert_ct)
          apply (wpsimp wp: checkCap_inv2 assertDerived_wp_weak)
         apply (clarsimp simp: option.case_eq_if if_fun_split)
         apply (wpsimp simp: ran_tcb_cap_cases
                         wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift
                             thread_set_tcb_ipc_buffer_cap_cleared_invs
                             thread_set_not_state_valid_sched thread_set_valid_objs'
                             thread_set_cte_wp_at_trivial thread_set_ipc_tcb_cap_valid)
        apply (clarsimp simp: option.case_eq_if if_fun_split)
        apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift threadSet_invs_trivial
                          threadSet_cte_wp_at' threadSet_valid_objs' threadSet_valid_release_queue
                          threadSet_valid_release_queue' threadSet_valid_queues threadSet_valid_queues')
       apply ((wp cap_delete_deletes cap_delete_valid_sched cap_delete_cte_at cap_delete_deletes_fh
                  hoare_vcg_const_imp_liftE_R hoare_vcg_all_liftE_R hoare_vcg_disj_lift_R
               | strengthen use_no_cap_to_obj_asid_strg is_aligned_tcb_ipc_buffer_update invs_valid_objs2
                            invs_psp_aligned_strg invs_distinct[atomized] valid_sched_weak_strg
                            valid_sched_active_scs_valid)+)[1]
      apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> tcb_at' a s \<and>
                               (g''' \<noteq> None \<longrightarrow> valid_cap' (fst (the g''')) s) \<and>
                               cte_wp_at' (\<lambda>a. cteCap a = capability.NullCap)
                                          (cte_map (a, tcb_cnode_index 2)) s"
                   in hoare_strengthen_postE[rotated])
        apply (clarsimp simp: valid_pspace'_def is_aligned_tcbIPCBuffer_update
                              valid_release_queue_def valid_release_queue'_def obj_at'_def invs'_def)
       apply assumption
      apply (wp cteDelete_invs' cteDelete_deletes hoare_vcg_const_imp_liftE_R)
     apply (fastforce simp: tcb_ep_slot_cte_wp_ats cte_wp_at_caps_of_state
                            valid_fault_handler_def is_cap_simps valid_ipc_buffer_cap_def
                      dest: is_cnode_or_valid_arch_cap_asid
                     split: arch_cap.splits bool.splits option.splits)
    apply (fastforce split: option.splits)
   apply (fastforce simp: obj_at_def is_tcb intro: cte_wp_at_tcbI)
  apply (fastforce simp: cte_map_def tcb_cnode_index_def obj_at'_def
                         projectKOs cte_level_bits_def objBits_simps cte_wp_at_tcbI')
  done

lemma tcb_at_cte_at'_0: "tcb_at' a s \<Longrightarrow> cte_at' (cte_map (a, tcb_cnode_index 0)) s"
  apply (clarsimp simp: obj_at'_def projectKO_def fail_def return_def projectKO_tcb oassert_opt_def
                 split: option.splits)
  apply (rule_tac ptr'=a in cte_wp_at_tcbI'; simp add: objBitsKO_def)
  apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def)
  done

lemma tcb_at_cte_at'_1: "tcb_at' a s \<Longrightarrow> cte_at' (cte_map (a, tcb_cnode_index (Suc 0))) s"
  apply (clarsimp simp: obj_at'_def projectKO_def fail_def return_def projectKO_tcb oassert_opt_def
                 split: option.splits)
  apply (rule_tac ptr'=a in cte_wp_at_tcbI'; simp add: objBitsKO_def)
  apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def of_bl_def)
  done

lemma tcb_at_cte_at'_3: "tcb_at' a s \<Longrightarrow> cte_at' (cte_map (a, tcb_cnode_index 3)) s"
  apply (clarsimp simp: obj_at'_def projectKO_def fail_def return_def projectKO_tcb oassert_opt_def
                 split: option.splits)
  apply (rule_tac ptr'=a in cte_wp_at_tcbI'; simp add: objBitsKO_def)
  apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def)
  done

lemma tcb_at_cte_at'_4: "tcb_at' a s \<Longrightarrow> cte_at' (cte_map (a, tcb_cnode_index 4)) s"
  apply (clarsimp simp: obj_at'_def projectKO_def fail_def return_def projectKO_tcb oassert_opt_def
                 split: option.splits)
  apply (rule_tac ptr'=a in cte_wp_at_tcbI'; simp add: objBitsKO_def)
  apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def)
  done

lemma tc_corres_caps:
  fixes t slot fault_h time_h croot vroot ipcb sl' fault_h' time_h' croot' vroot' ipcb'
  defines "tc_caps_inv \<equiv> tcb_invocation.ThreadControlCaps t slot fault_h time_h croot vroot ipcb"
  defines "tc_caps_inv' \<equiv> tcbinvocation.ThreadControlCaps t sl' fault_h' time_h' croot' vroot' ipcb'"
  assumes "tcbinv_relation tc_caps_inv tc_caps_inv'"
  defines "valid_tcap c \<equiv> case_option \<top> (valid_cap o fst) c and
                          case_option \<top> (real_cte_at o snd) c and
                          case_option \<top> (no_cap_to_obj_dr_emp o fst) c"
  shows
    "corres (dc \<oplus> (=))
    (einvs and valid_machine_time and simple_sched_action and active_scs_valid
     and tcb_at t and tcb_inv_wf tc_caps_inv and current_time_bounded)
    (invs' and sch_act_simple and tcb_inv_wf' tc_caps_inv')
    (invoke_tcb tc_caps_inv)
    (invokeTCB tc_caps_inv')"
  using assms
  apply -
  apply (simp add: invokeTCB_def liftE_bindE)
  apply (rule corres_guard_imp)
    apply (rule corres_split_norE, (rule installTCBCap_corres; clarsimp))+
            apply (rule corres_split_norE)
               apply (rule installThreadBuffer_corres; clarsimp)
              apply (rule corres_trivial, clarsimp simp: returnOk_def)
             apply wpsimp+
           apply (wpsimp wp: install_tcb_cap_invs hoare_case_option_wpR)
          apply (wpsimp wp: installTCBCap_invs' installTCBCap_sch_act_simple hoare_case_option_wpR)
         apply ((wp hoare_case_option_wpR hoare_vcg_all_liftE_R hoare_vcg_const_imp_liftE_R
                    install_tcb_cap_invs install_tcb_cap_cte_at install_tcb_cap_cte_wp_at_ep
                 | strengthen tcb_cap_always_valid_strg)+)[1]
        apply (wp installTCBCap_invs' installTCBCap_sch_act_simple
                          hoare_case_option_wpR hoare_vcg_all_liftE_R hoare_vcg_const_imp_liftE_R)
       apply ((wp hoare_case_option_wpR hoare_vcg_all_liftE_R hoare_vcg_const_imp_liftE_R
                  install_tcb_cap_invs install_tcb_cap_cte_at install_tcb_cap_cte_wp_at_ep
               | strengthen tcb_cap_always_valid_strg)+)[1]
      apply (wp installTCBCap_invs' installTCBCap_sch_act_simple
                        hoare_case_option_wpR hoare_vcg_all_liftE_R hoare_vcg_const_imp_liftE_R)
     apply ((wp hoare_case_option_wpR hoare_vcg_all_liftE_R hoare_vcg_const_imp_liftE_R
                install_tcb_cap_invs install_tcb_cap_cte_at install_tcb_cap_cte_wp_at_ep
             | strengthen tcb_cap_always_valid_strg)+)[1]
    apply (wp installTCBCap_invs' installTCBCap_sch_act_simple
                      hoare_case_option_wpR hoare_vcg_all_liftE_R hoare_vcg_const_imp_liftE_R)
   apply ((clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified] tcb_at_cte_at_3 tcb_at_cte_at_4
                          tcb_cap_valid_def tcb_at_st_tcb_at[symmetric] is_nondevice_page_cap_def
                          is_nondevice_page_cap_arch_def is_cnode_or_valid_arch_def is_cap_simps
                          is_valid_vtable_root_def valid_ipc_buffer_cap tcb_ep_slot_cte_wp_at
                          cte_wp_at_disj cte_wp_at_eq_simp real_cte_at_cte  real_cte_at_not_tcb_at
                   split: option.split
          | intro conjI | fastforce simp: valid_fault_handler_def)+)[1]
  apply (clarsimp simp: tcb_at_cte_at'_0 tcb_at_cte_at'_1 tcb_at_cte_at'_3
                        tcb_at_cte_at'_4 isCap_simps case_option_If2
                        isValidFaultHandler_def isValidVTableRoot_def | intro conjI)+
  done

lemma sched_context_resume_weak_valid_sched_action:
  "\<lbrace>\<lambda>s. weak_valid_sched_action s \<and>
        (\<forall>ya. sc_tcb_sc_at ((=) (Some ya)) scp s \<longrightarrow> scheduler_act_not ya s)\<rbrace>
   sched_context_resume scp
   \<lbrace>\<lambda>_. weak_valid_sched_action\<rbrace>"
  unfolding sched_context_resume_def
  by (wpsimp wp: postpone_weak_valid_sched_action thread_get_wp' is_schedulable_wp')

crunch sched_context_resume
  for sc_at_ppred[wp]: "sc_at_ppred n P ptr"
  (wp: crunch_wps)

lemma setSchedContext_scTCB_update_valid_refills[wp]:
  "\<lbrace>ko_at' sc ptr and valid_refills' ptr'\<rbrace>
   setSchedContext ptr (scTCB_update f sc)
   \<lbrace>\<lambda>_. valid_refills' ptr'\<rbrace>"
  apply (wpsimp wp: set_sc'.set_wp)
  by (clarsimp simp: valid_refills'_def obj_at_simps opt_map_red opt_pred_def)

lemma schedContextBindTCB_corres:
  "corres dc (valid_objs and pspace_aligned and pspace_distinct and (\<lambda>s. sym_refs (state_refs_of s))
              and valid_sched and simple_sched_action and bound_sc_tcb_at ((=) None) t
              and current_time_bounded
              and active_scs_valid and sc_tcb_sc_at ((=) None) ptr and ex_nonz_cap_to t and ex_nonz_cap_to ptr)
             (invs' and ex_nonz_cap_to' t and ex_nonz_cap_to' ptr)
             (sched_context_bind_tcb ptr t) (schedContextBindTCB ptr t)"
  apply (simp only: sched_context_bind_tcb_def schedContextBindTCB_def)
  apply (rule stronger_corres_guard_imp)
    apply clarsimp
    apply (rule corres_symb_exec_r')
       apply (rule corres_split_nor)
         apply (clarsimp simp: set_tcb_obj_ref_thread_set sc_relation_def)
          apply (rule threadset_corres; clarsimp simp: tcb_relation_def)
         apply (rule corres_split_nor)
            apply (rule_tac f'="scTCB_update (\<lambda>_. Some t)"
                         in update_sc_no_reply_stack_update_ko_at'_corres; clarsimp?)
             apply (clarsimp simp: sc_relation_def)
            apply (clarsimp simp: objBits_def objBitsKO_def)
           apply (rule corres_split[OF ifCondRefillUnblockCheck_corres])
             apply (rule corres_split_nor)
                apply (rule schedContextResume_corres)
               apply (rule corres_split_eqr)
                  apply (rule isSchedulable_corres)
                 apply (rule corres_when, simp)
                 apply (rule corres_split_nor)
                    apply (rule tcbSchedEnqueue_corres)
                   apply (rule rescheduleRequired_corres)
                  apply wp
                 apply wp
                apply (wpsimp simp: is_schedulable_def)
               apply (wpsimp wp: threadGet_wp getTCB_wp simp: isSchedulable_def inReleaseQueue_def)
              apply (rule_tac Q'="\<lambda>rv. valid_objs and pspace_aligned and pspace_distinct and (\<lambda>s. sym_refs (state_refs_of s)) and
                                      weak_valid_sched_action and active_scs_valid and
                                      sc_tcb_sc_at ((=) (Some t)) ptr and current_time_bounded and
                                      bound_sc_tcb_at (\<lambda>sc. sc = Some ptr) t"
                           in hoare_strengthen_post[rotated], fastforce)
              apply (wp sched_context_resume_weak_valid_sched_action sched_context_resume_pred_tcb_at)
             apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated], fastforce)
             apply wp
            apply (rule_tac Q'="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct and
                                   (\<lambda>s. sym_refs (state_refs_of s)) and current_time_bounded and
                                   valid_ready_qs and valid_release_q and weak_valid_sched_action and
                                   active_scs_valid and scheduler_act_not t and
                                   sc_tcb_sc_at ((=) (Some t)) ptr and
                                   bound_sc_tcb_at (\<lambda>a. a = Some ptr) t"
                   in hoare_strengthen_post[rotated])
             apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def valid_sched_action_def dest!: sym[of "Some _"])
            apply (wpsimp simp: if_cond_refill_unblock_check_def
                            wp: refill_unblock_check_valid_release_q
                                refill_unblock_check_valid_sched_action
                                refill_unblock_check_active_scs_valid)
           apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post[rotated], fastforce)
           apply wpsimp
          apply (rule_tac Q'="\<lambda>_. valid_objs and pspace_aligned and pspace_distinct and
                                 (\<lambda>s. sym_refs (state_refs_of s)) and
                                 valid_ready_qs and valid_release_q and active_scs_valid and
                                 sc_tcb_sc_at (\<lambda>sc. sc \<noteq> None) ptr and
                                 (\<lambda>s. (weak_valid_sched_action s \<and> current_time_bounded s \<and>
                                       (\<forall>ya. sc_tcb_sc_at ((=) (Some ya)) ptr s \<longrightarrow>
                                             not_in_release_q ya s \<and> scheduler_act_not ya s)) \<and>
                                      active_scs_valid s \<and>
                                      sc_tcb_sc_at ((=) (Some t)) ptr s \<and>
                                      bound_sc_tcb_at (\<lambda>a. a = Some ptr) t s)"
                 in hoare_strengthen_post[rotated])
           apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_sc_obj invs_def valid_state_def
                                 valid_pspace_def option.case_eq_if opt_map_red opt_pred_def)
           apply (drule (1) valid_sched_context_size_objsI)
           apply clarsimp
           apply (clarsimp simp: pred_tcb_at_def obj_at_def vs_all_heap_simps option.case_eq_if
                                 opt_map_red)
           apply (rename_tac sc ta tcb tcb')
           apply (drule_tac tp=ta in sym_ref_tcb_sc)
             apply (fastforce+)[3]
          apply ((wpsimp wp: valid_irq_node_typ obj_set_prop_at get_sched_context_wp ssc_refs_of_Some
                            update_sched_context_valid_objs_same valid_ioports_lift
                            update_sched_context_iflive_update update_sched_context_refs_of_update
                            update_sched_context_cur_sc_tcb_None update_sched_context_valid_idle
                      simp: invs'_def valid_pspace_def
                 | rule hoare_vcg_conj_lift update_sched_context_wp)+)[2]
        apply (clarsimp simp: pred_conj_def)
        apply ((wp set_tcb_sched_context_valid_ready_qs
                   set_tcb_sched_context_valid_release_q_not_queued
                   set_tcb_sched_context_simple_weak_valid_sched_action
               | ((rule hoare_vcg_conj_lift)?, rule set_tcb_obj_ref_wp))+)[1]
       apply (clarsimp simp: pred_conj_def valid_pspace'_def cong: conj_cong)
       apply (wp threadSet_valid_objs' threadSet_valid_queues threadSet_valid_queues'
                 threadSet_iflive' threadSet_not_inQ threadSet_ifunsafe'T threadSet_idle'T
                 threadSet_sch_actT_P[where P=False, simplified] threadSet_ctes_ofT threadSet_mdb'
                 threadSet_valid_release_queue threadSet_valid_release_queue' valid_irq_node_lift
                 valid_irq_handlers_lift'' untyped_ranges_zero_lift threadSet_valid_dom_schedule'
                 threadSet_ct_idle_or_in_cur_domain' threadSet_cur threadSet_valid_replies'
              | clarsimp simp: tcb_cte_cases_def cteCaps_of_def
              | rule hoare_vcg_conj_lift threadSet_wp refl)+
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_def)
   apply (intro conjI impI allI; (solves clarsimp)?)
            apply (fastforce simp: valid_obj_def obj_at_def sc_at_ppred_def is_sc_obj_def)
           apply (clarsimp simp: valid_sched_context_def obj_at_def pred_tcb_at_def is_tcb_def)
          apply (fastforce simp: obj_at_def pred_tcb_at_def sc_at_ppred_def
                                 tcb_st_refs_of_def state_refs_of_def
                           elim: delta_sym_refs split: if_splits)
         apply (fastforce simp: tcb_at_kh_simps pred_map_eq_def
                         dest!: valid_ready_qs_no_sc_not_queued)
        apply (fastforce simp: tcb_at_kh_simps pred_map_eq_def
                        elim!: valid_release_q_no_sc_not_in_release_q)
       apply (fastforce simp: sc_at_pred_def sc_at_ppred_def obj_at_def bound_sc_tcb_at_def
                       split: if_splits)
      apply (clarsimp simp: weak_valid_sched_action_def simple_sched_action_def)
     apply (fastforce simp: tcb_at_kh_simps pred_map_eq_def sc_tcb_sc_at_def obj_at_def
                     elim!: valid_release_q_no_sc_not_in_release_q)
    apply (clarsimp simp: sc_at_ppred_def obj_at_def bound_sc_tcb_at_def)
   apply (clarsimp simp: sc_at_ppred_def obj_at_def bound_sc_tcb_at_def)
  apply (subgoal_tac "obj_at' (\<lambda>sc. scTCB sc = None) ptr s'")
   apply (subgoal_tac "bound_sc_tcb_at' ((=) None) t s'")
    apply (subgoal_tac "ptr \<noteq> idle_sc_ptr")
     apply (clarsimp simp: invs'_def valid_pspace'_def pred_tcb_at'_def
                           sc_at_ppred_def obj_at'_def projectKO_eq projectKO_tcb projectKO_sc)
     apply (intro conjI allI impI; (solves \<open>clarsimp simp: inQ_def comp_def\<close>)?)
             apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def obj_at'_def projectKO_eq)
            apply (fastforce simp: valid_obj'_def valid_sched_context'_def tcb_cte_cases_def
                                   obj_at'_def projectKO_eq projectKO_sc projectKO_tcb)
           apply (fastforce elim: valid_objs_sizeE'[OF valid_objs'_valid_objs_size']
                            simp: objBits_def objBitsKO_def valid_obj_size'_def
                                  valid_sched_context_size'_def)
          apply (fastforce elim: ex_cap_to'_after_update simp: ko_wp_at'_def tcb_cte_cases_def)
         apply (fastforce elim: ex_cap_to'_after_update simp: ko_wp_at'_def tcb_cte_cases_def)
        apply (clarsimp simp: valid_release_queue'_def obj_at'_def projectKO_eq projectKO_tcb)
       apply (clarsimp simp: valid_release_queue'_def obj_at'_def projectKO_eq projectKO_tcb)
      apply (clarsimp simp: untyped_ranges_zero_inv_def cteCaps_of_def comp_def)
     apply simp
    apply (fastforce simp: invs'_def dest: global'_sc_no_ex_cap)
   apply (clarsimp simp: state_relation_def invs_def valid_state_def valid_pspace_def)
   apply (subgoal_tac "tcb_at' t s'")
    apply (clarsimp simp: pspace_relation_def pred_tcb_at_def pred_tcb_at'_def obj_at_def obj_at'_def)
    apply (drule_tac x=t in bspec; clarsimp simp: other_obj_relation_def tcb_relation_def projectKOs)
   apply (fastforce elim: tcb_at_cross)
  apply (clarsimp simp: sc_relation_def state_relation_def invs_def valid_state_def valid_pspace_def)
  apply (subgoal_tac "sc_at' ptr s'")
   apply (clarsimp simp: obj_at_def sc_at_pred_n_def obj_at'_def projectKOs pspace_relation_def)
   apply (drule_tac x=ptr in bspec; clarsimp simp: sc_relation_def split: if_splits)
  apply (fastforce simp: sc_at_pred_n_def obj_at_def is_sc_obj_def valid_obj_def elim!: sc_at_cross)
  done

schematic_goal finaliseSlot'_def:
  "finaliseSlot' a b = ?X"
  by (rule ext) simp

lemma cteDelete_fh_lift:
  assumes A: "\<And>x. \<lbrace>Q\<rbrace> emptySlot target x \<lbrace>\<lambda>_. P\<rbrace>"
  and     B: "\<And>x. \<lbrace>R\<rbrace> cancelAllIPC x \<lbrace>\<lambda>_. Q\<rbrace>"
  and     C: "\<And>s. (P and invs'  and L) s \<Longrightarrow> Q s \<and> R s"
  shows "\<lbrace>P and invs' and cte_wp_at' (isValidFaultHandler \<circ> cteCap) target and L\<rbrace>
         cteDelete target True
         \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp wp: A simp: cteDelete_def)
   prefer 2
   apply assumption
  apply (subst finaliseSlot_def)
  apply (subst finaliseSlot'_def)
  apply (rule bindE_wp_fwd)
   apply (subst liftE_validE)
   apply (rule getCTE_sp)
  apply (clarsimp split del: if_split)
  apply (rule_tac Q="P and invs' and L and cte_wp_at' (\<lambda>c. c = cte) target
                       and K (isValidFaultHandler (cteCap cte))" in hoare_pre(2))
   apply (case_tac "cteCap cte"; clarsimp simp: isValidFaultHandler_def split: bool.splits)
    apply (wpsimp simp: C)+
         apply (rule hoare_FalseE)
        apply (rule hoare_FalseE)
       apply (rule hoare_FalseE)
      apply (wpsimp wp: B isFinal simp: capRemovable_def finaliseCap_def isEndpointCap_def)+
   apply (fastforce simp: C cte_wp_at'_def final_matters'_def capRemovable_def invs'_def)+
  done

lemma installTCBCap_fh_ex_nonz_cap_to':
  "\<lbrace>\<lambda>s. ex_nonz_cap_to' p s \<and> invs' s \<and> \<not>ep_at' p s \<and>
        cte_wp_at' (isValidFaultHandler \<circ> cteCap) (cte_map (target, tcb_cnode_index 3)) s\<rbrace>
   installTCBCap target slot 3 slot_opt
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  unfolding installTCBCap_def getThreadFaultHandlerSlot_def locateSlotTCB_def locateSlotBasic_def
  apply (case_tac slot_opt; clarsimp)
   apply wpsimp
  apply (rule validE_valid)
  apply (rule bindE_wp_fwd)
   apply (rule liftE_wp[OF hoare_return_sp])
  apply (rule valid_validE)
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: objBits_def objBitsKO_def)
  apply (wpsimp wp: checkCap_wp assertDerived_wp_weak cteInsert_cap_to' split_del: if_splits)
   apply (rule_tac Q'="\<lambda>_ s. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap)
                                       (target + 2 ^ cteSizeBits * tcbFaultHandlerSlot) s \<and>
                            ex_nonz_cap_to' p s" in hoare_strengthen_postE)
     apply (rule hoare_vcg_conj_liftE1[OF _ valid_validE])
      apply (wpsimp wp: cteDelete_deletes)
     apply (rule cteDelete_fh_lift)
       apply (wpsimp wp: hoare_vcg_ex_lift emptySlot_cte_wp_cap_other simp: ex_nonz_cap_to'_def)
      apply (wpsimp wp: hoare_vcg_ex_lift)
     apply (clarsimp simp: ex_nonz_cap_to'_def)
     apply (rule_tac x=cref in exI)
     apply clarsimp
     apply (prop_tac "\<not> ep_at' p s \<and> cte_wp_at' (isValidFaultHandler \<circ> cteCap)
                                                 (target + 2 ^ cteSizeBits * tcbFaultHandlerSlot) s")
      apply assumption
     apply (clarsimp simp: cte_wp_at_ctes_of)
     apply (prop_tac "s \<turnstile>' (cteCap cte)")
      apply fastforce
     apply (prop_tac "\<not> isEndpointCap (cteCap cte)")
      apply (fastforce simp: valid_cap'_def isCap_simps)
     apply (case_tac "cteCap cte"; clarsimp simp: isValidFaultHandler_def isEndpointCap_def)
    apply (wpsimp wp: cteDelete_deletes)+
  apply (clarsimp simp: comp_def cte_map_def tcb_cnode_index_def
                        objBits_defs cte_level_bits_def tcbFaultHandlerSlot_def)
  done

lemma threadSetPriority_ex_nonz_cap_to'[wp]:
  "threadSetPriority param_a param_b \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wpsimp wp: threadSet_cap_to' simp: threadSetPriority_def)

crunch setPriority
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' p"
  (wp: crunch_wps simp: crunch_simps)

crunch setMCPriority
  for tcb_at'[wp]: "tcb_at' t"
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps simp: crunch_simps inQ_def)

lemma setMCPriority_ex_nonz_cap_to'[wp]:
  "setMCPriority param_a param_b \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wpsimp wp: threadSet_cap_to' simp: setMCPriority_def)

lemma mapTCBPtr_threadGet: "mapTCBPtr t f = threadGet f t"
  by (clarsimp simp: mapTCBPtr_def threadGet_getObject)

lemma monadic_rewrite_bind_unbind:
  "monadic_rewrite False True (tcb_at t)
   (case sc_opt of None \<Rightarrow> return ()
                 | Some None \<Rightarrow> maybe_sched_context_unbind_tcb t
                 | Some (Some sc_ptr) \<Rightarrow> maybe_sched_context_bind_tcb sc_ptr t)
   (do y <- get_tcb_obj_ref tcb_sched_context t;
       case sc_opt of None \<Rightarrow> return ()
                    | Some None \<Rightarrow> case y of None \<Rightarrow> return ()
                                           | Some x \<Rightarrow> sched_context_unbind_tcb x
                    | Some (Some sc_ptr) \<Rightarrow> when (y \<noteq> Some sc_ptr) $ sched_context_bind_tcb sc_ptr t
    od)"
  apply (case_tac sc_opt; clarsimp)
   apply (clarsimp simp: monadic_rewrite_def bind_def get_tcb_obj_ref_def thread_get_def
                         gets_the_def get_tcb_def gets_def get_def obj_at_def is_tcb_def)
   apply (case_tac ko; clarsimp simp: return_def)
  apply (case_tac a; clarsimp simp: maybeM_def maybe_sched_context_unbind_tcb_def
                                    maybe_sched_context_bind_tcb_def monadic_rewrite_def)
  done

defs tcs_cross_asrt1_def:
  "tcs_cross_asrt1 t sc_opt \<equiv>
     \<lambda>s. sym_refs (state_refs_of' s) \<and>
         cte_wp_at' (isValidFaultHandler \<circ> cteCap) (cte_map (t, tcb_cnode_index 3)) s \<and>
         (\<forall>x. sc_opt = Some (Some x) \<longrightarrow> bound_sc_tcb_at' (\<lambda>sc. sc = None) t s \<and>
                                         obj_at' (\<lambda>sc. scTCB sc = None) x s)"

defs tcs_cross_asrt2_def:
  "tcs_cross_asrt2 \<equiv> \<lambda>s. ready_qs_runnable s \<and> ct_active' s \<and>
                          bound_sc_tcb_at' bound (ksCurThread s) s"

crunch setPriority, setMCPriority
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and cur_tcb'[wp]: cur_tcb'
  (wp: crunch_wps cur_tcb_lift)

crunch schedContextYieldTo, schedContextCompleteYieldTo
  for tcb_at'[wp]: "tcb_at' tcbPtr"
  (wp: crunch_wps)

lemma schedContextUnbindTCB_corres':
  "corres dc (invs and valid_sched and sc_tcb_sc_at ((\<noteq>) None) scp) invs'
             (sched_context_unbind_tcb scp) (schedContextUnbindTCB scp)"
  apply (rule corres_cross_add_guard[where Q="obj_at' (\<lambda>sc. \<exists>y. scTCB sc = Some y) scp"])
   apply (fastforce elim: sc_tcb_sc_at_bound_cross dest!: state_relation_pspace_relation
                    simp: invs_def valid_state_def valid_pspace_def)

  apply (simp add: neq_None_bound)
  apply (rule schedContextUnbindTCB_corres[simplified])
  done

lemma tc_corres_sched:
  fixes t slot sc_fault_h p_auth mcp_auth sc_opt sl' sc_fault_h' sc_opt'
  defines "tc_inv_sched \<equiv> tcb_invocation.ThreadControlSched t slot sc_fault_h mcp_auth p_auth sc_opt"
  defines "tc_inv_sched' \<equiv> ThreadControlSched t sl' sc_fault_h' mcp_auth p_auth sc_opt'"
  assumes "tcbinv_relation tc_inv_sched tc_inv_sched'"
  shows
    "corres (dc \<oplus> (=))
    (einvs and valid_machine_time and simple_sched_action and tcb_inv_wf tc_inv_sched
           and ct_released and ct_active and ct_not_in_release_q and current_time_bounded)
    (invs' and sch_act_simple and tcb_inv_wf' tc_inv_sched')
    (invoke_tcb tc_inv_sched)
    (invokeTCB tc_inv_sched')"
  using assms
  apply -
  apply add_sym_refs
  apply add_valid_idle'
  apply add_cur_tcb'
  apply (simp add: invokeTCB_def liftE_bindE bind_assoc maybeM_def)
  apply (rule corres_stateAssertE_add_assertion)
  apply (rule corres_stateAssertE_add_assertion[rotated])
   apply (clarsimp simp: valid_idle'_asrt_def)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule installTCBCap_corres; clarsimp)
       apply (rule corres_split_nor)
          apply (rule_tac P=\<top> and P'=\<top> in corres_option_split; clarsimp)
          apply (rule setMCPriority_corres)
         apply (rule corres_stateAssert_add_assertion)
          apply (rule stronger_corres_guard_imp)
            apply (rule corres_split_nor)
               apply (rule_tac P=\<top> and P'=\<top> in corres_option_split; clarsimp)
               apply wpfix
               apply (rule setPriority)
              apply (simp add: bind_assoc[symmetric])
              apply (rule corres_split_nor)
                 apply (rule monadic_rewrite_corres_l[OF monadic_rewrite_bind_unbind])
                 apply (rule corres_split_eqr)
                    apply (simp only: mapTCBPtr_threadGet get_tcb_obj_ref_def)
                    apply (rule threadGet_corres, clarsimp simp: tcb_relation_def)
                   apply (rule_tac P=\<top> and P'=\<top> in corres_option_split; clarsimp)
                   apply (rule corres_option_split; clarsimp?)
                    apply (rule_tac P=\<top> and P'=\<top> in corres_option_split; clarsimp)
                    apply (rule schedContextUnbindTCB_corres')
                   apply (rule corres_when[OF _ schedContextBindTCB_corres], fastforce)
                  apply (wp get_tcb_obj_ref_wp)
                 apply (wpsimp wp: getTCB_wp simp: mapTCBPtr_def)
                apply (clarsimp simp: returnOk_def)
               apply (rule_tac P=\<top> in hoare_TrueI)
              apply (rule hoare_TrueI)
             apply (rule_tac Q'="\<lambda>_ s. invs s \<and> valid_machine_time s \<and> valid_sched s
                                      \<and> simple_sched_action s \<and> current_time_bounded s \<and>
                                      tcb_at t s \<and> ex_nonz_cap_to t s \<and>
                                      (\<forall>scPtr. sc_opt = Some (Some scPtr) \<longrightarrow>
                                                 ex_nonz_cap_to scPtr s \<and>
                                                 sc_tcb_sc_at ((=) None) scPtr s \<and>
                                                 bound_sc_tcb_at ((=) None) t s)"
                          in hoare_strengthen_post[rotated])
              apply (clarsimp simp: obj_at_def split: option.splits)
              apply (frule invs_valid_objs)
              apply (frule valid_sched_active_scs_valid)
              apply (erule (1) valid_objsE)
              apply (clarsimp simp: valid_obj_def valid_tcb_def obj_at_def is_sc_obj_def
                                    invs_def valid_state_def valid_pspace_def)
              apply (clarsimp split: Structures_A.kernel_object.splits)
              apply (drule (2) bound_sc_tcb_bound_sc_at[where tcbptr=t])
               apply (clarsimp simp: pred_tcb_at_def obj_at_def)
              apply (clarsimp simp: sc_at_ppred_def obj_at_def)
             apply (wpsimp wp: set_priority_valid_sched hoare_vcg_all_lift hoare_vcg_const_imp_lift)
            apply (rule_tac Q'=" \<lambda>_ s. invs' s \<and> tcb_at' t s \<and> ex_nonz_cap_to' t s \<and>
                                      (\<forall>scp. sc_opt = Some (Some scp) \<longrightarrow> ex_nonz_cap_to' scp s)"
                         in hoare_strengthen_post[rotated], fastforce split: option.split)
            apply (wpsimp wp: setP_invs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
           apply clarsimp
           apply (prop_tac "ct_active s \<and> ct_released s", erule conjunct1)
           apply simp
          apply clarsimp
          \<comment> \<open>the following is unified with one of the guard schematics\<close>
          apply (prop_tac "invs' s' \<and> tcb_at' t s' \<and> ex_nonz_cap_to' t s' \<and>
                           (\<forall>x. p_auth = Some x \<longrightarrow> fst x \<le> maxPriority) \<and>
                           (\<forall>scp. sc_opt = Some (Some scp) \<longrightarrow> ex_nonz_cap_to' scp s')")
           apply assumption
          apply (fastforce elim: ready_qs_runnable_cross ct_active_cross split: option.splits)
         apply (clarsimp simp: tcs_cross_asrt2_def)
         apply (intro conjI)
           apply (fastforce elim: ready_qs_runnable_cross)
          apply (fastforce elim: ct_active_cross)
         apply (prop_tac "cur_tcb s", fastforce)
         apply (frule cur_tcb_cross)
            apply fastforce
           apply fastforce
          apply fastforce
         apply (fastforce elim: ct_released_cross_weak[simplified])
        apply (rule_tac Q'="\<lambda>_. invs" in hoare_post_add)
        apply (clarsimp simp: invs_cur case_option_If2 if_fun_split
                        cong: conj_cong imp_cong split del: if_split)
        apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift)
       apply (rule_tac Q'="\<lambda>_. invs'" in hoare_post_add)
       apply (clarsimp simp: invs_queues invs_queues' case_option_If2 if_fun_split
                       cong: conj_cong imp_cong split del: if_split)
       apply (rule_tac f="ksCurThread" in hoare_lift_Pf3)
        apply (wpsimp wp: setMCPriority_invs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
       apply wpsimp
      apply (rule_tac Q'="\<lambda>_ s. einvs s \<and> valid_machine_time s \<and> simple_sched_action s \<and> tcb_at t s
                               \<and> ex_nonz_cap_to t s \<and> ct_active s \<and> ct_released s
                               \<and> ct_not_in_release_q s \<and> current_time_bounded s \<and>
                               (\<forall>scp. sc_opt = Some (Some scp) \<longrightarrow> ex_nonz_cap_to scp s \<and>
                                                                   sc_tcb_sc_at ((=) None) scp s \<and>
                                                                   bound_sc_tcb_at ((=) None) t s)"
                  and E'="\<lambda>_. \<top>" in hoare_strengthen_postE[rotated], fastforce split: option.splits, simp)
      apply (rule hoare_vcg_conj_elimE)
       apply wp
      apply (wp install_tcb_cap_invs install_tcb_cap_ex_nonz_cap_to
                install_tcb_cap_ct_active hoare_vcg_all_lift hoare_weak_lift_imp
                hoare_lift_Pf3[where f=cur_thread, OF install_tcb_cap_released_sc_tcb_at
                                                      install_tcb_cap_cur_thread])
     apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> tcb_at' t s \<and> ex_nonz_cap_to' t s \<and>
                              (\<forall>scp. sc_opt = Some (Some scp) \<longrightarrow> ex_nonz_cap_to' scp s) \<and>
                              (\<forall>p. p_auth = Some p \<longrightarrow> fst p \<le> maxPriority) \<and>
                              (\<forall>p. mcp_auth = Some p \<longrightarrow> fst p \<le> maxPriority)"
                 and E'="\<lambda>_. \<top>" in hoare_strengthen_postE[rotated], fastforce split: option.splits, simp)
     apply (wp installTCBCap_invs' installTCBCap_fh_ex_nonz_cap_to'
               hoare_vcg_all_lift hoare_vcg_const_imp_lift)
    apply (prop_tac "(not ep_at t) s")
     apply (clarsimp simp: pred_neg_def obj_at_def is_tcb_def is_ep_def)
     apply (clarsimp split: Structures_A.kernel_object.splits)
    apply (fastforce simp: tcb_cap_valid_def pred_tcb_at_def pred_neg_def
                           sc_at_ppred_def obj_at_def is_ep_def is_tcb_def
                     elim: cte_wp_at_weakenE dest: tcb_ep_slot_cte_wp_ats)
   apply (clarsimp simp: tcs_cross_asrt1_def)
   apply (intro conjI impI allI; clarsimp?)
       apply (clarsimp simp: tcb_at_cte_at'_3)
      apply (clarsimp simp: newroot_rel_def isCap_simps valid_fault_handler_def)
      apply (case_tac a; clarsimp)
     apply (clarsimp simp: newroot_rel_def isCap_simps valid_fault_handler_def)
     apply (case_tac a; clarsimp)
    apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb projectKO_ep)
   apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_sc projectKO_ep)
  apply (clarsimp simp: tcs_cross_asrt1_def)
  apply (intro conjI impI allI)
    apply (drule (1) tcb_ep_slot_cte_wp_ats)
    apply (drule_tac p="(t, tcb_cnode_index 3)" in cte_wp_at_norm)
    apply (fastforce simp: valid_fault_handler_def has_handler_rights_def
                           isValidFaultHandler_def is_cap_simps cte_wp_at'_def
                    dest!: pspace_relation_cte_wp_at[rotated])
   apply (subgoal_tac "tcb_at' t s'")
    apply (clarsimp simp: state_relation_def pspace_relation_def invs_def valid_state_def
                          valid_pspace_def pred_tcb_at_def pred_tcb_at'_def obj_at_def obj_at'_def)
    apply (drule_tac x=t in bspec, clarsimp)
    apply (clarsimp simp: other_obj_relation_def tcb_relation_def projectKOs)
   apply (fastforce elim: tcb_at_cross)
  apply (subgoal_tac "sc_at' x s'")
   apply (clarsimp simp: state_relation_def pspace_relation_def invs_def valid_state_def
                         valid_pspace_def sc_at_ppred_def obj_at_def obj_at'_def)
   apply (drule_tac x=x in bspec, clarsimp)
   apply (clarsimp simp: other_obj_relation_def sc_relation_def projectKOs split: if_splits)
  apply (fastforce elim: sc_at_cross)
  done

lemmas threadSet_ipcbuffer_trivial
    = threadSet_invs_trivial[where F="tcbIPCBuffer_update F'" for F',
                              simplified inQ_def, simplified]

lemma tc_caps_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_inv_wf' (ThreadControlCaps t sl fault_h time_h croot vroot ipcb)\<rbrace>
   invokeTCB (ThreadControlCaps t sl fault_h time_h croot vroot ipcb)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: split_def invokeTCB_def getThreadCSpaceRoot getThreadVSpaceRoot
                   getThreadBufferSlot_def locateSlot_conv
             cong: option.case_cong)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_weak_lift_imp setP_invs' setMCPriority_invs'
                    installTCBCap_invs' installThreadBuffer_invs' installTCBCap_sch_act_simple)
  apply (clarsimp cong: conj_cong)
  apply (intro conjI; intro allI impI; clarsimp;
         fastforce simp: isValidFaultHandler_def isCap_simps isValidVTableRoot_def)
  done

lemma schedContextBindTCB_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> ex_nonz_cap_to' tcbPtr s \<and> ex_nonz_cap_to' scPtr s \<and>
        bound_sc_tcb_at' (\<lambda>sc. sc = None) tcbPtr s \<and> obj_at' (\<lambda>sc. scTCB sc = None) scPtr s\<rbrace>
   schedContextBindTCB scPtr tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: schedContextBindTCB_def)
  apply (subst bind_assoc[symmetric, where m="threadSet _ _"])
  apply (rule bind_wp)+
      apply wpsimp
     apply (wpsimp wp: isSchedulable_wp)
    apply (clarsimp simp: isSchedulable_bool_runnableE)
    apply (wp (once) hoare_drop_imps)
     apply (wp hoare_vcg_imp_lift')
     apply (wp hoare_drop_imps)
    apply (wpsimp wp: hoare_vcg_imp_lift' simp: ifCondRefillUnblockCheck_def)
   apply (rule_tac Q'="\<lambda>_ s. invs' s" in hoare_strengthen_post[rotated], simp)
   apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
   apply (wp threadSet_valid_objs' threadSet_mdb' threadSet_iflive'
             threadSet_cap_to threadSet_ifunsafe'T threadSet_ctes_ofT
             threadSet_valid_queues_new threadSet_valid_queues' threadSet_valid_release_queue
             threadSet_valid_release_queue' untyped_ranges_zero_lift valid_irq_node_lift
             valid_irq_handlers_lift'' hoare_vcg_const_imp_lift hoare_vcg_imp_lift'
             threadSet_valid_replies'
          | clarsimp simp: tcb_cte_cases_def cteCaps_of_def)+
  apply (clarsimp simp: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  by (fastforce simp: pred_tcb_at'_def obj_at'_def projectKOs
                      objBits_def objBitsKO_def valid_tcb'_def tcb_cte_cases_def comp_def
                      valid_obj'_def valid_sched_context'_def valid_sched_context_size'_def
                      valid_release_queue'_def inQ_def cteCaps_of_def
                elim: ps_clear_domE split: if_splits)

lemma threadSetPriority_bound_sc_tcb_at' [wp]:
  "threadSetPriority tptr prio \<lbrace>\<lambda>s. Q (bound_sc_tcb_at' P t s)\<rbrace>"
  by (wpsimp wp: threadSet_pred_tcb_no_state simp: threadSetPriority_def)

crunch setPriority
  for sc_tcb_sc_at'[wp]: "\<lambda>s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) p s)"
  and bound_sc_tcb_at'[wp]: "\<lambda>s. Q (bound_sc_tcb_at' P t s)"
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps)

crunch setMCPriority
  for sc_tcb_sc_at'[wp]: "\<lambda>s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) p s)"
  and bound_sc_tcb_at'[wp]: "\<lambda>s. Q (bound_sc_tcb_at' P t s)"
  and st_tcb_at'[wp]: "\<lambda>s. Q (st_tcb_at' P t s)"
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps threadSet_pred_tcb_no_state)

crunch finaliseCap, capSwapForDelete
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps wp: crunch_wps getObject_inv cteDelete_preservation)

lemma updateRefillHd_sc_tcb_sc_at'[wp]:
  "updateRefillHd scp f \<lbrace>\<lambda>s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) p s)\<rbrace>"
  apply (wpsimp simp: updateRefillHd_def wp: updateSchedContext_wp)
  by (clarsimp simp: obj_at'_def ps_clear_upd projectKOs opt_map_red objBits_simps)

lemma refillPopHead_sc_tcb_sc_at'[wp]:
  "refillPopHead scp \<lbrace>\<lambda>s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) p s)\<rbrace>"
  apply (wpsimp simp: refillPopHead_def wp: updateSchedContext_wp)
  by (clarsimp simp: obj_at'_def ps_clear_upd projectKOs opt_map_red objBits_simps)

crunch cteInsert, emptySlot, cancelAllIPC
  for sc_tcb_sc_at'[wp]: "\<lambda>s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) p s)"
  (wp: crunch_wps simp: crunch_simps ignore: updateRefillHd)

lemma installTCBCap_fh_sc_tcb_sc_at':
  "\<lbrace>\<lambda>s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) p s) \<and> invs' s \<and> tcb_at' target s \<and>
        cte_wp_at' (isValidFaultHandler \<circ> cteCap) (cte_map (target, tcb_cnode_index 3)) s\<rbrace>
   installTCBCap target slot 3 slot_opt
   \<lbrace>\<lambda>_ s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) p s)\<rbrace>"
  by (wpsimp wp: checkCap_inv assertDerived_wp cteDelete_fh_lift
           simp: installTCBCap_def locateSlotTCB_def locateSlotBasic_def tcbFaultHandlerSlot_def
                 getThreadFaultHandlerSlot_def cte_level_bits_def cte_map_def
                 tcb_cnode_index_def objBits_defs objBits_def objBitsKO_def)

lemma installTCBCap_fh_bound_sc_tcb_at':
  "\<lbrace>\<lambda>s. bound_sc_tcb_at' P t s \<and> invs' s \<and> tcb_at' target s \<and>
          cte_wp_at' (isValidFaultHandler \<circ> cteCap) (cte_map (target, tcb_cnode_index 3)) s\<rbrace>
   installTCBCap target slot 3 slot_opt
   \<lbrace>\<lambda>_ s. bound_sc_tcb_at' P t s\<rbrace>"
  by (wpsimp wp: checkCap_inv assertDerived_wp cteDelete_fh_lift hoare_vcg_const_imp_lift
           simp: installTCBCap_def locateSlotTCB_def locateSlotBasic_def tcbFaultHandlerSlot_def
                 getThreadFaultHandlerSlot_def cte_level_bits_def cte_map_def
                 tcb_cnode_index_def objBits_defs objBits_def objBitsKO_def)

lemma installTCBCap_ksCurThread[wp]:
  "installTCBCap target slot n slot_opt \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
  by (wpsimp wp: checkCap_inv assertDerived_wp cteDelete_preservation split_del: if_split
           simp: installTCBCap_def getThreadFaultHandlerSlot_def getThreadTimeoutHandlerSlot_def)

lemma tc_sched_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_inv_wf' (ThreadControlSched t sl sc_fault_h mcp pri sc_opt)\<rbrace>
   invokeTCB (ThreadControlSched t sl sc_fault_h mcp pri sc_opt)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invokeTCB_def)
  apply (wpsimp wp: schedContextUnbindTCB_invs' schedContextBindTCB_invs')
        apply (wpsimp wp: getTCB_wp simp: mapTCBPtr_def)
       apply (rule_tac Q'="\<lambda>rv s. invs' s \<and> ex_nonz_cap_to' t s \<and>
                                 (sc_opt = Some None \<longrightarrow>
                                  bound_sc_tcb_at' (\<lambda>sc. sc \<noteq> Some idle_sc_ptr) t s) \<and>
                                 (\<forall>x. sc_opt = Some (Some x) \<longrightarrow>
                                      ex_nonz_cap_to' x s \<and> obj_at' (\<lambda>sc. scTCB sc = None) x s \<and>
                                      bound_sc_tcb_at' (\<lambda>sc. sc = None) t s \<and>
                                      bound_sc_tcb_at' bound (ksCurThread s) s)"
                    in hoare_strengthen_post[rotated])
        apply (fastforce simp: pred_tcb_at'_def obj_at'_def projectKOs)
       apply (rule hoare_lift_Pf3[where f=ksCurThread])
        apply (wpsimp wp: setP_invs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
       apply wpsimp
      apply wpsimp
     apply (clarsimp simp: tcs_cross_asrt2_def)
     apply (wp (once) hoare_drop_imps)
     apply (wpsimp wp: setMCPriority_invs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
    apply (wpsimp wp: installTCBCap_invs' installTCBCap_fh_ex_nonz_cap_to'
                      installTCBCap_fh_bound_sc_tcb_at' installTCBCap_fh_sc_tcb_sc_at'
                      hoare_vcg_all_lift hoare_vcg_ball_lift2 hoare_vcg_const_imp_lift)
   apply (wpsimp simp: stateAssertE_def)+
  apply (clarsimp cong: conj_cong)
  apply (subgoal_tac "sc_opt = Some None \<longrightarrow> bound_sc_tcb_at' (\<lambda>a. a \<noteq> Some idle_sc_ptr) t s")
   apply (fastforce simp: tcs_cross_asrt1_def comp_def isValidFaultHandler_def
                          isCap_simps pred_tcb_at'_def obj_at'_def projectKOs)
  apply (clarsimp simp: invs'_def valid_idle'_def
                        pred_tcb_at'_def obj_at'_def tcs_cross_asrt1_def valid_idle'_asrt_def)
  apply (frule_tac p=t and ko="ko :: tcb" for ko in sym_refs_ko_atD'[rotated])
   apply (auto simp: ko_wp_at'_def obj_at'_def projectKOs valid_idle'_def dest!: global'_no_ex_cap)
  done

lemma setSchedulerAction_invs'[wp]:
  "\<lbrace>invs' and sch_act_wf sa\<rbrace>
   setSchedulerAction sa
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: setSchedulerAction_def)
  apply wp
  apply (clarsimp simp add: invs'_def valid_irq_node'_def valid_dom_schedule'_def
                valid_queues_def valid_queues_no_bitmap_def bitmapQ_defs cur_tcb'_def
                ct_not_inQ_def valid_release_queue_def valid_release_queue'_def)
  done

lemma invokeTCB_corres:
 "tcbinv_relation ti ti' \<Longrightarrow>
  corres (dc \<oplus> (=))
         (einvs and valid_machine_time and simple_sched_action and Tcb_AI.tcb_inv_wf ti
                and current_time_bounded and ct_released and ct_active and ct_not_in_release_q)
         (invs' and sch_act_simple and tcb_inv_wf' ti')
         (invoke_tcb ti) (invokeTCB ti')"
  apply (case_tac ti, simp_all only: tcbinv_relation.simps valid_tcb_invocation_def)
          apply (rule corres_guard_imp[OF invokeTCB_WriteRegisters_corres], fastforce+)[1]
         apply (rule corres_guard_imp[OF invokeTCB_ReadRegisters_corres], simp+)[1]
        apply (rule corres_guard_imp[OF invokeTCB_CopyRegisters_corres], fastforce+)[1]
       apply (clarsimp simp del: invoke_tcb.simps)
       apply (rule corres_guard_imp[OF tc_corres_caps]; clarsimp)
      apply (clarsimp simp del: invoke_tcb.simps)
      apply (rename_tac word a b sc_fault_h mcp prio sc_opt sl' sc_fault_h')
      apply (rule corres_guard_imp[OF tc_corres_sched]; clarsimp)
     apply (clarsimp simp: invokeTCB_def liftM_def[symmetric] o_def dc_def[symmetric])
     apply (rule corres_guard_imp[OF suspend_corres]; clarsimp)
    apply (clarsimp simp: invokeTCB_def liftM_def[symmetric] o_def dc_def[symmetric])
    apply (rule corres_guard_imp[OF restart_corres]; clarsimp)
   apply (clarsimp simp: invokeTCB_def)
   apply (rename_tac option)
   apply (case_tac option
          ; clarsimp simp: liftM_def[symmetric] o_def dc_def[symmetric])
    apply (rule corres_guard_imp[OF unbindNotification_corres]; clarsimp)
   apply (rule corres_guard_imp[OF bindNotification_corres]
          ; clarsimp simp: obj_at'_def obj_at_def is_ntfn_def)
  apply (clarsimp simp: invokeTCB_def tlsBaseRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF TcbAcc_R.asUser_setRegister_corres])
      apply (rule corres_split[OF Bits_R.getCurThread_corres])
        apply (rule corres_split[OF Corres_UL.corres_when])
            apply simp
           apply (rule TcbAcc_R.rescheduleRequired_corres)
          apply (rule corres_trivial, simp)
         apply (solves \<open>wpsimp wp: hoare_drop_imp\<close>)+
   apply (clarsimp simp: invs_valid_tcbs valid_sched_weak_strg invs_psp_aligned
                         valid_sched_active_scs_valid)
  apply (clarsimp simp: invs_valid_queues' invs_queues invs'_valid_tcbs' invs_valid_release_queue)
  done

lemma tcbBoundNotification_caps_safe[simp]:
  "\<forall>(getF, setF)\<in>ran tcb_cte_cases.
     getF (tcbBoundNotification_update (\<lambda>_. Some ntfnptr) tcb) = getF tcb"
  by (case_tac tcb, simp add: tcb_cte_cases_def)

lemma bindNotification_invs':
  "\<lbrace>bound_tcb_at' ((=) None) tcbptr
       and ex_nonz_cap_to' ntfnptr
       and ex_nonz_cap_to' tcbptr
       and obj_at' (\<lambda>ntfn. ntfnBoundTCB ntfn = None \<and> (\<forall>q. ntfnObj ntfn \<noteq> WaitingNtfn q)) ntfnptr
       and invs'\<rbrace>
    bindNotification tcbptr ntfnptr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding bindNotification_def invs'_def valid_dom_schedule'_def
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (wpsimp wp: set_ntfn_valid_pspace' sbn_sch_act' sbn_valid_queues valid_irq_node_lift
                    setBoundNotification_ct_not_inQ valid_bound_ntfn_lift
                    untyped_ranges_zero_lift irqs_masked_lift
              simp: cteCaps_of_def)
  apply (frule(1) ntfn_ko_at_valid_objs_valid_ntfn'[OF _ valid_pspace_valid_objs'])
  apply (clarsimp simp: obj_at'_def pred_tcb_at'_def valid_ntfn'_def projectKOs o_def
                        global'_no_ex_cap
                 split: ntfn.splits)
  done

lemma tcbntfn_invs':
  "\<lbrace>invs' and tcb_inv_wf' (tcbinvocation.NotificationControl tcb ntfnptr)\<rbrace>
       invokeTCB (tcbinvocation.NotificationControl tcb ntfnptr)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invokeTCB_def)
  apply (case_tac ntfnptr, simp_all)
   apply (wp unbindNotification_invs bindNotification_invs' | simp)+
  done

lemma setTLSBase_invs'[wp]:
  "\<lbrace>invs' and tcb_inv_wf' (tcbinvocation.SetTLSBase tcb tls_base)\<rbrace>
       invokeTCB (tcbinvocation.SetTLSBase tcb tls_base)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wpsimp simp: invokeTCB_def)

lemma tcbinv_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_inv_wf' ti\<rbrace>
     invokeTCB ti
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (case_tac ti; simp only:)
          apply (simp add: invokeTCB_def)
          apply wp
          apply (clarsimp simp: invs'_def
                          dest!: global'_no_ex_cap)
         apply (simp add: invokeTCB_def)
         apply (wp restart_invs')
         apply (clarsimp simp: invs'_def
                         dest!: global'_no_ex_cap)
        apply (wpsimp wp: tc_caps_invs' tc_sched_invs' writereg_invs' readreg_invs'
                          copyreg_invs' tcbntfn_invs')+
  done

declare assertDerived_wp [wp]

lemma copyregsets_map_only[simp]:
  "copyregsets_map v = ARMNoExtraRegisters"
  by (cases "copyregsets_map v", simp)

lemma decodeReadRegisters_corres:
  "corres (ser \<oplus> tcbinv_relation) (invs and tcb_at t) (invs' and tcb_at' t)
     (decode_read_registers args (cap.ThreadCap t))
     (decodeReadRegisters args (ThreadCap t))"
  apply (simp add: decode_read_registers_def decodeReadRegisters_def)
  apply (cases args, simp_all)
  apply (case_tac list, simp_all)
  apply (simp add: decodeTransfer_def)
  apply (simp add: range_check_def rangeCheck_def frameRegisters_def gpRegisters_def)
  apply (simp add: unlessE_def split del: if_split, simp add: returnOk_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_norE)
       apply (rule corres_trivial)
       apply (fastforce simp: returnOk_def)
      apply (simp add: liftE_bindE)
      apply (rule corres_split[OF getCurThread_corres])
        apply (rule corres_trivial)
        apply (clarsimp simp: whenE_def)
       apply (wp|simp)+
  done

lemma decodeWriteRegisters_corres:
  notes if_cong [cong]
  shows
  "\<lbrakk> length args < 2 ^ word_bits \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation) (invs and tcb_at t) (invs' and tcb_at' t)
     (decode_write_registers args (cap.ThreadCap t))
     (decodeWriteRegisters args (ThreadCap t))"
  apply (simp add: decode_write_registers_def decodeWriteRegisters_def)
  apply (cases args, simp_all)
  apply (case_tac list, simp_all)
  apply (simp add: decodeTransfer_def genericLength_def)
  apply (simp add: word_less_nat_alt unat_of_nat32)
  apply (simp add: whenE_def, simp add: returnOk_def)
  apply (simp add: genericTake_def)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (simp add: liftE_bindE)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split_norE)
         apply (rule corres_trivial, simp)
        apply (rule corres_trivial, simp)
       apply (wp)+
   apply simp+
  done

lemma decodeCopyRegisters_corres:
  "\<lbrakk> list_all2 cap_relation extras extras'; length args < 2 ^ word_bits \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation) (invs and tcb_at t) (invs' and tcb_at' t)
     (decode_copy_registers args (cap.ThreadCap t) extras)
     (decodeCopyRegisters args (ThreadCap t) extras')"
  apply (simp add: decode_copy_registers_def decodeCopyRegisters_def)
  apply (cases args, simp_all)
  apply (cases extras, simp_all add: decodeTransfer_def null_def)
  apply (clarsimp simp: list_all2_Cons1 null_def)
  apply (case_tac aa, simp_all)
   apply (simp add: returnOk_def)
  apply clarsimp
  done

lemma decodeReadReg_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     decodeReadRegisters args (ThreadCap t)
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeReadRegisters_def decodeTransfer_def whenE_def
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply simp
  done

lemma decodeWriteReg_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     decodeWriteRegisters args (ThreadCap t)
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeWriteRegisters_def whenE_def decodeTransfer_def
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply simp
  done

lemma decodeCopyReg_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t
       and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile>' x
                \<and> (\<forall>y \<in> zobj_refs' x. ex_nonz_cap_to' y s))\<rbrace>
     decodeCopyRegisters args (ThreadCap t) extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeCopyRegisters_def whenE_def decodeTransfer_def
             cong: list.case_cong capability.case_cong bool.case_cong
               split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply (clarsimp simp: null_def neq_Nil_conv
                        valid_cap'_def[where c="ThreadCap t" for t])
  done

lemma eq_ucast_word8[simp]:
  "((ucast (x :: 8 word) :: word32) = ucast y) = (x = y)"
  apply safe
  apply (drule_tac f="ucast :: (word32 \<Rightarrow> 8 word)" in arg_cong)
  apply (simp add: ucast_up_ucast_id is_up_def
                   source_size_def target_size_def word_size)
  done

lemma checkPrio_corres:
  "corres (ser \<oplus> dc) (tcb_at auth and pspace_aligned and pspace_distinct) \<top>
     (check_prio p auth) (checkPrio p auth)"
  apply (simp add: check_prio_def checkPrio_def)
  apply (rule corres_guard_imp)
    apply (simp add: liftE_bindE)
    apply (rule corres_split[OF threadGet_corres[where r="(=)"]])
       apply (clarsimp simp: tcb_relation_def)
      apply (rule_tac rvr = dc and
                        R = \<top> and
                       R' = \<top> in
               whenE_throwError_corres'[where m="returnOk ()" and m'="returnOk ()", simplified])
        apply (simp add: minPriority_def)
       apply (clarsimp simp: minPriority_def)
      apply (rule corres_returnOkTT)
      apply (simp add: minPriority_def)
     apply (wp gct_wp)+
   apply (simp add: cur_tcb_def cur_tcb'_def)+
  done

lemma decodeSetPriority_corres:
  "\<lbrakk> cap_relation cap cap'; is_thread_cap cap;
     list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation)
       (cur_tcb and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> (fst x)))
       (invs' and (\<lambda>s. \<forall>x \<in> set extras'. s \<turnstile>' (fst x)))
       (decode_set_priority args cap slot extras)
       (decodeSetPriority args cap' extras')"
  apply (cases args; cases extras; cases extras';
         clarsimp simp: decode_set_priority_def decodeSetPriority_def emptyTCSched_def)
  apply (rename_tac auth_cap auth_slot auth_path rest auth_cap' rest')
  apply (rule corres_split_eqrE)
     apply (case_tac auth_cap; clarsimp simp: corres_returnOk)
    apply (rule corres_splitEE[OF checkPrio_corres])
      apply (rule corres_returnOkTT)
      apply (clarsimp simp: newroot_rel_def elim!: is_thread_cap.elims(2))
     apply wpsimp+
   apply (wpsimp simp: valid_cap_def valid_cap'_def)+
  done

lemma decodeSetMCPriority_corres:
  "\<lbrakk> cap_relation cap cap'; is_thread_cap cap;
     list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation)
       (cur_tcb and valid_etcbs and (pspace_aligned and pspace_distinct and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> (fst x))))
       (invs' and (\<lambda>s. \<forall>x \<in> set extras'. s \<turnstile>' (fst x)))
       (decode_set_mcpriority args cap slot extras)
       (decodeSetMCPriority args cap' extras')"
  apply (cases args; cases extras; cases extras';
         clarsimp simp: decode_set_mcpriority_def decodeSetMCPriority_def emptyTCSched_def)
  apply (rename_tac auth_cap auth_slot auth_path rest auth_cap' rest')
  apply (rule corres_split_eqrE)
     apply (case_tac auth_cap; clarsimp simp: corres_returnOk)
    apply (rule corres_splitEE[OF checkPrio_corres])
      apply (rule corres_returnOkTT)
      apply (clarsimp simp: newroot_rel_def elim!: is_thread_cap.elims(2))
     apply wpsimp+
   apply (wpsimp simp: valid_cap_def valid_cap'_def)+
  done

lemma getMCP_sp:
  "\<lbrace>P\<rbrace> threadGet tcbMCP t \<lbrace>\<lambda>rv. mcpriority_tcb_at' (\<lambda>st. st = rv) t and P\<rbrace>"
  apply (simp add: threadGet_getObject)
  apply wp
  apply (simp add: o_def pred_tcb_at'_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma getMCP_wp: "\<lbrace>\<lambda>s. \<forall>mcp. mcpriority_tcb_at' ((=) mcp) t s \<longrightarrow> P mcp s\<rbrace> threadGet tcbMCP t \<lbrace>P\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule getMCP_sp)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

crunch checkPrio
  for inv: "P"
  (simp: crunch_simps)

lemma checkPrio_wp:
  "\<lbrace> \<lambda>s. mcpriority_tcb_at' (\<lambda>mcp. prio \<le> ucast mcp) auth s \<longrightarrow> P s \<rbrace>
    checkPrio prio auth
   \<lbrace> \<lambda>rv. P \<rbrace>,-"
  apply (simp add: checkPrio_def)
  apply (wp Nondet_VCG.whenE_throwError_wp getMCP_wp)
  by (auto simp add: pred_tcb_at'_def obj_at'_def)

lemma checkPrio_lt_ct:
  "\<lbrace>\<top>\<rbrace> checkPrio prio auth \<lbrace>\<lambda>rv s. mcpriority_tcb_at' (\<lambda>mcp. prio \<le> ucast mcp) auth s\<rbrace>, -"
  by (wp checkPrio_wp) simp

lemma checkPrio_lt_ct_weak:
  "\<lbrace>\<top>\<rbrace> checkPrio prio auth \<lbrace>\<lambda>rv s. mcpriority_tcb_at' (\<lambda>mcp. ucast prio \<le> mcp) auth s\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R)
  apply (rule checkPrio_lt_ct)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  by (rule le_ucast_ucast_le) simp

lemma checkPrio_lt_ct_weak':
  "\<lbrace>P\<rbrace> checkPrio prio auth \<lbrace>\<lambda>rv s. P s \<and> mcpriority_tcb_at' (\<lambda>mcp. ucast prio \<le> mcp) auth s\<rbrace>, -"
  apply (wpsimp wp: hoare_vcg_conj_liftE1)
    apply (wpsimp wp: checkPrio_inv)
   apply (wpsimp wp: checkPrio_lt_ct_weak)+
  done

crunch checkPrio
  for tcb_at'[wp]: "tcb_at' t"
  and ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' t"

lemma decodeSetPriority_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t \<rbrace>
   decodeSetPriority args (ThreadCap t) extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  unfolding decodeSetPriority_def
  apply (wpsimp wp: checkPrio_lt_ct_weak simp: emptyTCSched_def)
  apply (clarsimp simp: maxPriority_def numPriorities_def emptyTCSched_def)
  using max_word_max [of \<open>UCAST(32 \<rightarrow> 8) x\<close> for x]
  by (simp add: max_word_mask numeral_eq_Suc mask_Suc)

lemma decodeSetPriority_inv[wp]:
  "\<lbrace>P\<rbrace> decodeSetPriority args cap extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decodeSetPriority_def Let_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp checkPrio_inv | simp add: whenE_def split del: if_split
             | rule hoare_drop_imps
             | wpcw)+
  done

lemma decodeSetMCPriority_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t \<rbrace>
   decodeSetMCPriority args (ThreadCap t) extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  unfolding decodeSetMCPriority_def Let_def
  apply (wpsimp wp: checkPrio_lt_ct_weak simp: emptyTCSched_def)
  apply (clarsimp simp: maxPriority_def numPriorities_def emptyTCSched_def)
  using max_word_max [of \<open>UCAST(32 \<rightarrow> 8) x\<close> for x]
  by (simp add: max_word_mask numeral_eq_Suc mask_Suc)

lemma decodeSetMCPriority_inv[wp]:
  "\<lbrace>P\<rbrace> decodeSetMCPriority args cap extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decodeSetMCPriority_def Let_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp checkPrio_inv | simp add: whenE_def split del: if_split
             | rule hoare_drop_imps
             | wpcw)+
  done

lemma decodeSetSchedParams_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
    and (\<lambda>s. \<forall>x \<in> set extras. real_cte_at' (snd x) s
                              \<and> s \<turnstile>' fst x \<and> (\<forall>y \<in> zobj_refs' (fst x). ex_nonz_cap_to' y s))\<rbrace>
   decodeSetSchedParams args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  unfolding decodeSetSchedParams_def scReleased_def refillReady_def scActive_def isBlocked_def
  apply (cases args; cases extras; clarsimp; (solves \<open>wpsimp wp: checkPrio_inv\<close>)?)
  apply (clarsimp split: list.splits; safe; (solves \<open>wpsimp wp: checkPrio_inv\<close>)?)
  apply (clarsimp simp: validE_R_def)
  apply (rule bindE_wp_fwd_skip, wpsimp wp: checkPrio_inv)
  apply (rule bindE_wp[OF _ checkPrio_lt_ct_weak'[unfolded validE_R_def]])+
  apply (wpsimp wp: checkPrio_lt_ct_weak gts_wp' threadGet_wp)
  apply (clarsimp simp: maxPriority_def numPriorities_def pred_tcb_at'_def obj_at'_def projectKOs)
  using max_word_max [of \<open>UCAST(32 \<rightarrow> 8) x\<close> for x]
  apply (auto simp: max_word_mask numeral_eq_Suc mask_Suc)
  done

(* FIXME RT: There's probably a way to avoid this using cap.case_eq_if and corres_if, but it
             doesn't seem easy to do in a nice way. This lemma is used to "keep" the cap type
             information all the way through to the final WP proofs. *)
lemma corres_case_cap_null_sc:
  assumes "cap_relation cp cp'"
          "cp = cap.NullCap \<Longrightarrow> corres_underlying sr nf nf' rr Pnul Pnul' case_nul case_nul'"
          "\<And>sc_ptr n. cp = cap.SchedContextCap sc_ptr n \<Longrightarrow>
               corres_underlying sr nf nf' rr (Psc sc_ptr n) (Psc' sc_ptr n) (case_sc sc_ptr n)
                   (case_sc' sc_ptr (min_sched_context_bits + n))"
          "\<lbrakk>cp \<noteq> cap.NullCap; \<not>cap.is_SchedContextCap cp\<rbrakk> \<Longrightarrow>
               corres_underlying sr nf nf' rr Pother Pother' case_other case_other'"
  shows "corres_underlying sr nf nf' rr
             (\<lambda>s. (cp = cap.NullCap \<longrightarrow> Pnul s)
                  \<and> (\<forall>sc_ptr n. cp = cap.SchedContextCap sc_ptr n \<longrightarrow> Psc sc_ptr n s)
                  \<and> (\<not>cap.is_SchedContextCap cp \<and> cp \<noteq> cap.NullCap \<longrightarrow> Pother s))
             (\<lambda>s. (cp' = NullCap \<longrightarrow> Pnul' s)
                  \<and> (\<forall>sc_ptr n. cp = cap.SchedContextCap sc_ptr n \<longrightarrow> Psc' sc_ptr n s)
                  \<and> (\<not>cap.is_SchedContextCap cp \<and> cp \<noteq> cap.NullCap \<longrightarrow> Pother' s))
             (case cp of cap.NullCap \<Rightarrow> case_nul
              | cap.SchedContextCap sc_ptr n \<Rightarrow> case_sc sc_ptr n
              | _ \<Rightarrow> case_other)
             (case cp' of capability.NullCap \<Rightarrow> case_nul'
              | capability.SchedContextCap sc_ptr n \<Rightarrow> case_sc' sc_ptr n
              | _ \<Rightarrow> case_other')"
  apply (insert assms)
  apply (case_tac cp; clarsimp)
  done

lemma decodeSetSchedParams_corres:
  "\<lbrakk> cap_relation cap cap'; is_thread_cap cap; slot' = cte_map slot;
     list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation)
       (invs and valid_sched and (\<lambda>s. s \<turnstile> cap \<and> (\<forall>x \<in> set extras. s \<turnstile> (fst x))))
       (invs' and (\<lambda>s. s \<turnstile>' cap' \<and> (\<forall>x \<in> set extras'. s \<turnstile>' (fst x))))
       (decode_set_sched_params args cap slot extras)
       (decodeSetSchedParams args cap' slot' extras')"
  apply (clarsimp simp: is_cap_simps)
  apply (simp add: decode_set_sched_params_def decodeSetSchedParams_def decode_update_sc_def
                   check_handler_ep_def unlessE_whenE)
  apply (cases "length args < 2")
   apply (clarsimp split: list.split)
  apply (cases "length extras < 3")
   apply (clarsimp split: list.split simp: list_all2_Cons2)
  apply (clarsimp simp: list_all2_Cons1 neq_Nil_conv val_le_length_Cons linorder_not_less)
  apply (case_tac cap; clarsimp)
  apply (rule corres_split_eqrE[THEN corres_guard_imp])
       apply (clarsimp split: cap.splits
              ; intro conjI impI allI
              ; fastforce intro: corres_returnOkTT)
      apply (rule corres_split_norE[OF checkPrio_corres])
        apply (rule corres_split_norE[OF checkPrio_corres])
          apply (rule corres_split_eqrE)
             apply (rule corres_case_cap_null_sc[where Pother=\<top> and Pother'=\<top>]
                    ; clarsimp
                    ; (wpfix add: capability.sel)?)
              apply (clarsimp simp: getCurThread_def)
              apply (rule corres_split_liftEE[OF corres_gets_trivial])
                 apply (clarsimp simp: state_relation_def)
                apply (rule whenE_throwError_corres; clarsimp)
                apply (rule corres_returnOkTT, simp)
               apply wpsimp
              apply wpsimp
             apply (clarsimp simp: get_tcb_obj_ref_def)
             apply (rule corres_split_eqrE)
                apply clarsimp
                apply (rule threadGet_corres)
                apply (clarsimp simp: tcb_relation_def)
               apply (rule whenE_throwError_corres; clarsimp)
               apply (rule corres_split_liftEE[OF get_sc_corres])
                 apply (rule whenE_throwError_corres; clarsimp simp: sc_relation_def)
                 apply (rule corres_split_liftEE[OF is_blocked_corres])
                   apply (rule corres_split_liftEE[OF get_sc_released_corres])
                     apply (rule whenE_throwError_corres; clarsimp)
                     apply (rule corres_returnOkTT, simp)
                    apply (wpsimp simp: is_blocked_def)+
              apply (wpsimp wp: thread_get_wp' threadGet_wp)+
            apply (clarsimp simp: bindE_assoc)
            apply (rule whenE_throwError_corres; simp add: cap_rel_valid_fh)
            apply (rule corres_returnOkTT)
            apply (clarsimp simp: newroot_rel_def)
           apply (wpsimp wp: check_prio_inv checkPrio_inv)+
   apply (fastforce simp: valid_cap_def)
  apply (clarsimp simp: valid_cap_simps')
  apply normalise_obj_at'
  apply (intro exI impI conjI allI)
    apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
    apply (rename_tac obj)
    apply (case_tac obj; clarsimp)
   apply (erule invs_valid_objs')
  apply (clarsimp simp: obj_at'_def)
  done

lemma checkValidIPCBuffer_corres:
  "cap_relation cap cap' \<Longrightarrow>
   corres (ser \<oplus> dc) \<top> \<top>
     (check_valid_ipc_buffer vptr cap)
     (checkValidIPCBuffer vptr cap')"
  apply (simp add: check_valid_ipc_buffer_def checkValidIPCBuffer_def
                   unlessE_def Let_def
            split: cap_relation_split_asm arch_cap.split_asm bool.splits)
  apply (simp add: capTransferDataSize_def msgMaxLength_def
                   msg_max_length_def msgMaxExtraCaps_def
                   cap_transfer_data_size_def word_size
                   msgLengthBits_def msgExtraCapBits_def msg_align_bits msgAlignBits_def
                   msg_max_extra_caps_def is_aligned_mask whenE_def split:vmpage_size.splits)
  apply (auto simp add: returnOk_def )
  done

lemma checkValidIPCBuffer_ArchObject_wp:
  "\<lbrace>\<lambda>s. isArchObjectCap cap \<and> is_aligned x msg_align_bits \<longrightarrow> P s\<rbrace>
     checkValidIPCBuffer x cap
   \<lbrace>\<lambda>rv s. P s\<rbrace>,-"
  apply (simp add: checkValidIPCBuffer_def whenE_def unlessE_def
             cong: capability.case_cong
                   arch_capability.case_cong
            split del: if_split)
  apply (rule hoare_pre)
  apply (wp whenE_throwError_wp
    | wpc | clarsimp simp: isCap_simps is_aligned_mask msg_align_bits msgAlignBits_def)+
  done

lemma decodeSetIPCBuffer_corres:
  notes if_cong [cong]
  shows
  "\<lbrakk> cap_relation cap cap'; is_thread_cap cap;
     list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation) (\<lambda>s. \<forall>x \<in> set extras. cte_at (snd x) s)
                            (\<lambda>s. invs' s \<and> (\<forall>x \<in> set extras'. cte_at' (snd x) s))
       (decode_set_ipc_buffer args cap slot extras)
       (decodeSetIPCBuffer args cap' (cte_map slot) extras')"
  apply (simp add: decode_set_ipc_buffer_def decodeSetIPCBuffer_def)
  apply (cases args)
   apply simp
  apply (cases extras)
   apply simp
  apply (clarsimp simp: list_all2_Cons1 liftME_def[symmetric] is_cap_simps)
  apply (clarsimp simp: returnOk_def newroot_rel_def emptyTCCaps_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule deriveCap_corres; simp)
      apply (simp add: o_def newroot_rel_def dc_def[symmetric])
      apply (rule corres_rel_imp)
       apply (erule checkValidIPCBuffer_corres)
      apply (simp add: dc_def)
     apply wpsimp+
  apply fastforce
  done

lemma decodeSetIPC_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
        and (\<lambda>s. \<forall>v \<in> set extras. s \<turnstile>' fst v \<and> cte_at' (snd v) s)\<rbrace>
     decodeSetIPCBuffer args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp   add: decodeSetIPCBuffer_def Let_def whenE_def emptyTCCaps_def
          split del: if_split cong: list.case_cong prod.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
    apply (rule checkValidIPCBuffer_ArchObject_wp)
   apply simp
   apply (wp hoare_drop_imps)
  apply clarsimp
  done

lemma decodeSetIPCBuffer_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetIPCBuffer args cap slot extras \<lbrace>\<lambda>rv s. isThreadControlCaps rv\<rbrace>,-"
  apply (simp add: decodeSetIPCBuffer_def Let_def emptyTCCaps_def
             split del: if_split cong: list.case_cong prod.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
   apply (simp only: isThreadControlCaps_def tcbinvocation.simps)
   apply wp+
  apply (clarsimp simp: isThreadControlCaps_def)
  done

crunch decodeSetIPCBuffer
  for inv[wp]: "P"
  (simp: crunch_simps)

lemma slotCapLongRunningDelete_corres:
  "cte_map ptr = ptr' \<Longrightarrow>
   corres (=) (cte_at ptr and invs) invs'
           (slot_cap_long_running_delete ptr)
           (slotCapLongRunningDelete ptr')"
  apply (clarsimp simp: slot_cap_long_running_delete_def
                        slotCapLongRunningDelete_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres])
      apply (auto split: cap_relation_split_asm arch_cap.split_asm
                 intro!: corres_rel_imp [OF isFinalCapability_corres[where ptr=ptr]]
                   simp: liftM_def[symmetric] final_matters'_def
                         long_running_delete_def
                         longRunningDelete_def isCap_simps)[1]
     apply (wp get_cap_wp getCTE_wp)+
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply fastforce
  done

lemma slot_long_running_inv'[wp]:
  "\<lbrace>P\<rbrace> slotCapLongRunningDelete ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: slotCapLongRunningDelete_def)
  apply (rule bind_wp [OF _ getCTE_inv])
  apply (rule hoare_pre, wpcw, (wp isFinalCapability_inv)+)
  apply simp
  done

lemma cap_CNode_case_throw:
  "(case cap of CNodeCap a b c d \<Rightarrow> m | _ \<Rightarrow> throw x)
     = (doE unlessE (isCNodeCap cap) (throw x); m odE)"
  by (cases cap, simp_all add: isCap_simps unlessE_def)

lemma decodeCVSpace_corres:
  notes if_cong [cong]
  shows
 "\<lbrakk>cap_relation cap cap';
   list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras';
   is_thread_cap cap\<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> (\<lambda>abs_inv conc_inv. tcbinv_relation abs_inv conc_inv))
      (invs and valid_cap cap and (\<lambda>s. \<forall>x \<in> set extras. cte_at (snd x) s))
      (invs' and valid_cap' cap' and (\<lambda>s. \<forall>x \<in> set extras'. cte_at' (snd x) s))
      (decode_cv_space args cap slot extras)
      (decodeCVSpace args cap' (cte_map slot) extras')"
  apply (simp    add: decode_cv_space_def decodeCVSpace_def
                      Let_def
           split del: if_split)
  apply (cases "2 \<le> length args \<and> 2 \<le> length extras'")
   apply (clarsimp simp: val_le_length_Cons list_all2_Cons2
              split del: if_split)
   apply (simp add: liftE_bindE liftM_def cap_CNode_case_throw
                    unlessE_throwError_returnOk unlessE_whenE
                    getThreadCSpaceRoot getThreadVSpaceRoot
                 split del: if_split)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF slotCapLongRunningDelete_corres])
        apply (clarsimp simp: is_cap_simps get_tcb_ctable_ptr_def cte_map_tcb_0)
       apply (rule corres_split[OF slotCapLongRunningDelete_corres])
          apply (clarsimp simp: is_cap_simps get_tcb_vtable_ptr_def cte_map_tcb_1[simplified])
         apply (rule corres_split_norE)
            apply (rule corres_whenE)
              apply simp
             apply (rule corres_trivial, simp)
            apply simp
           apply (simp(no_asm) add: bindE_assoc
                         split del: if_split)
           apply (rule corres_splitEE[OF deriveCap_corres])
               apply (fastforce dest: list_all2_nthD2[where p=0] simp: cap_map_update_data)
              apply (fastforce dest: list_all2_nthD2[where p=0])
             apply (rule corres_split_norE)
                apply (rule corres_whenE)
                  apply simp
                 apply (rule corres_trivial, simp)
                apply simp
               apply (rule corres_splitEE[OF deriveCap_corres])
                   apply (clarsimp simp: cap_map_update_data)
                  apply simp
                 apply (rule corres_split_norE)
                    apply (rule corres_whenE)
                      apply (case_tac vroot_cap', simp_all add:
                                       is_valid_vtable_root_def
                                       ARM_H.isValidVTableRoot_def)[1]
                      apply (rename_tac arch_cap)
                      apply (clarsimp, case_tac arch_cap, simp_all)[1]
                      apply (simp split: option.split)
                     apply (rule corres_trivial, simp)
                    apply simp
                   apply (rule corres_trivial)
                   apply (clarsimp simp: returnOk_def newroot_rel_def is_cap_simps
                                         list_all2_conv_all_nth split_def)
                  apply wp+
                apply ((simp only: simp_thms pred_conj_def | wp)+)[2]
              apply (unfold whenE_def, wp+)[2]
            apply ((simp split del: if_split | wp | rule hoare_drop_imps)+)[2]
          apply (unfold whenE_def, wp+)[2]
        apply simp
        apply (wp hoare_drop_imps)+
    apply (clarsimp simp: get_tcb_ctable_ptr_def get_tcb_vtable_ptr_def
                          is_cap_simps valid_cap_def tcb_at_cte_at_0
                          tcb_at_cte_at_1[simplified])
   apply fastforce
  apply (frule list_all2_lengthD)
  apply (clarsimp split: list.split)
  done

lemma decode_cv_space_is_ThreadControlCaps[wp]:
  "\<lbrace>\<top>\<rbrace>
   decode_cv_space args cap slot excaps
   \<lbrace>\<lambda>rv s. tcb_invocation.is_ThreadControlCaps rv\<rbrace>, -"
  apply (clarsimp simp: decode_cv_space_def returnOk_def validE_R_def)
  apply (rule bindE_wp_fwd_skip, wpsimp)+
  apply (clarsimp simp: return_def validE_def valid_def)
  done

lemma decodeSetSpace_corres:
 "\<lbrakk>cap_relation cap cap';
   list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras';
   is_thread_cap cap\<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> tcbinv_relation)
         (invs and valid_cap cap and (\<lambda>s. \<forall>x \<in> set extras. cte_at (snd x) s))
         (invs' and valid_cap' cap' and (\<lambda>s. \<forall>x \<in> set extras'. cte_at' (snd x) s))
      (decode_set_space args cap slot extras)
      (decodeSetSpace args cap' (cte_map slot) extras')"
  apply (simp add: decode_set_space_def decodeSetSpace_def check_handler_ep_def unlessE_whenE)
  apply (cases "\<not> (2 \<le> length args \<and> 3 \<le> length extras')")
   apply (clarsimp dest!: list_all2_lengthD split: list.split)
   apply fastforce
  apply (clarsimp simp: val_le_length_Cons list_all2_Cons2
             split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF decodeCVSpace_corres])
         apply blast
        apply fastforce+
      apply (rename_tac abs_space conc_space)
      apply (rule_tac F="tcb_invocation.is_ThreadControlCaps abs_space" in corres_gen_asm)
      apply clarsimp
      apply (intro conjI impI; simp add: cap_rel_valid_fh)
      apply (prop_tac "newroot_rel (tc_new_croot abs_space) (tcCapsCRoot conc_space)")
       apply (case_tac abs_space; clarsimp)
      apply (prop_tac "newroot_rel (tc_new_vroot abs_space) (tcCapsVRoot conc_space)")
       apply (case_tac abs_space; clarsimp)
      apply (rule corres_returnOkTT)
      apply (clarsimp simp: returnOk_def newroot_rel_def is_cap_simps list_all2_conv_all_nth)
     apply wp+
   apply fastforce+
  done

lemma decodeCVSpace_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
      and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile>' fst x \<and> cte_at' (snd x) s \<and> t \<noteq> snd x \<and> t + 16 \<noteq> snd x)\<rbrace>
     decodeCVSpace args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp       add: decodeCVSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
                         cap_CNode_case_throw
              split del: if_split cong: if_cong list.case_cong)
  apply (rule hoare_pre)
   apply (wp
             | simp    add: o_def split_def
                 split del: if_split
             | wpc
             | rule hoare_drop_imps)+
  apply (clarsimp simp del: length_greater_0_conv
                 split del: if_split)
  apply (simp del: length_greater_0_conv add: valid_updateCapDataI)
  done

lemma decodeSetSpace_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
      and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile>' fst x \<and> cte_at' (snd x) s \<and> t \<noteq> snd x \<and> t + 16 \<noteq> snd x)\<rbrace>
     decodeSetSpace args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp       add: decodeSetSpace_def decodeCVSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
                         cap_CNode_case_throw
              split del: if_split cong: if_cong list.case_cong)
  apply (rule hoare_pre)
   apply (wp
             | simp    add: o_def split_def
                 split del: if_split
             | wpc
             | rule hoare_drop_imps)+
  apply (clarsimp simp del: length_greater_0_conv
                 split del: if_split)
  apply (simp del: length_greater_0_conv add: valid_updateCapDataI)
  done

lemma decodeCVSpace_inv[wp]:
  "decodeCVSpace args cap slot extras \<lbrace>P\<rbrace>"
  apply (simp       add: decodeCVSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: if_cong list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
            | simp add: o_def split_def split del: if_split
            | wpcw)+
  done

lemma decodeSetSpace_inv[wp]:
  "\<lbrace>P\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp       add: decodeSetSpace_def decodeCVSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: if_cong list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
            | simp add: o_def split_def split del: if_split
            | wpcw)+
  done

lemma decodeCVSpace_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decodeCVSpace args cap slot extras \<lbrace>\<lambda>rv s. isThreadControlCaps rv\<rbrace>,-"
  apply (simp       add: decodeCVSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
           | simp only: isThreadControlCaps_def tcbinvocation.simps
           | wpcw)+
  apply simp
  done

lemma decodeSetSpace_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv s. isThreadControlCaps rv\<rbrace>,-"
  apply (simp       add: decodeSetSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
           | simp only: isThreadControlCaps_def tcbinvocation.simps
           | wpcw)+
  apply simp
  done

lemma decodeCVSpace_tc_target[wp]:
  "\<lbrace>\<lambda>s. P (capTCBPtr cap)\<rbrace> decodeCVSpace args cap slot extras \<lbrace>\<lambda>rv s. P (tcCapsTarget rv)\<rbrace>,-"
  apply (simp       add: decodeCVSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
           | simp only: tcbinvocation.sel
           | wpcw)+
  apply simp
  done

lemma decodeSetSpace_tc_target[wp]:
  "\<lbrace>\<lambda>s. P (capTCBPtr cap)\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv s. P (tcCapsTarget rv)\<rbrace>,-"
  apply (simp       add: decodeSetSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
           | simp only: tcbinvocation.sel
           | wpcw)+
  apply simp
  done

lemma decodeCVSpace_tc_slot[wp]:
  "\<lbrace>\<lambda>s. P slot\<rbrace> decodeCVSpace args cap slot extras \<lbrace>\<lambda>rv s. P (tcCapsSlot rv)\<rbrace>,-"
  apply (simp add: decodeCVSpace_def split_def unlessE_def
                   getThreadVSpaceRoot getThreadCSpaceRoot
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpcw | simp only: tcbinvocation.sel)+
  apply simp
  done

lemma decodeSetSpace_tc_slot[wp]:
  "\<lbrace>\<lambda>s. P slot\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv s. P (tcCapsSlot rv)\<rbrace>,-"
  apply (simp add: decodeSetSpace_def split_def unlessE_def
                   getThreadVSpaceRoot getThreadCSpaceRoot
             cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpcw | simp only: tcbinvocation.sel)+
  apply simp
  done

lemma decodeTCBConfigure_corres:
  notes if_cong [cong] option.case_cong [cong]
  shows
 "\<lbrakk>cap_relation cap cap';
   list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras';
   is_thread_cap cap\<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> tcbinv_relation)
      (einvs and valid_cap cap and (\<lambda>s. \<forall>x \<in> set extras. cte_at (snd x) s))
      (invs' and valid_cap' cap' and (\<lambda>s. \<forall>x \<in> set extras'. cte_at' (snd x) s))
      (decode_tcb_configure args cap slot extras)
      (decodeTCBConfigure args cap' (cte_map slot) extras')"
  apply (clarsimp simp add: decode_tcb_configure_def decodeTCBConfigure_def)
  apply (clarsimp split: list.split)
  apply (cases "length extras < 3")
   apply (clarsimp split: list.split simp: list_all2_Cons2)
  apply (clarsimp simp: linorder_not_less val_le_length_Cons list_all2_Cons1 priorityBits_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule decodeSetIPCBuffer_corres; simp)
      apply (rule corres_splitEE)
         apply (rule decodeCVSpace_corres; simp)
        apply (rule_tac F="tcb_invocation.is_ThreadControlCaps set_params" in corres_gen_asm)
        apply (rule_tac F="tcb_invocation.is_ThreadControlCaps set_space" in corres_gen_asm)
        apply (rule_tac F="tcCapsSlot setSpace = cte_map slot" in corres_gen_asm2)
        apply (rule corres_trivial)
        apply (clarsimp simp: returnOk_def is_cap_simps newroot_rel_def
                              tcb_invocation.is_ThreadControlCaps_def)
       apply (wpsimp simp: invs_def valid_sched_def)+
  done

lemma isThreadControl_def2:
  "isThreadControlCaps tinv = (\<exists>a b c d e f g. tinv = ThreadControlCaps a b c d e f g)"
  by (cases tinv, simp_all add: isThreadControlCaps_def)

lemma decodeCVSpaceSome[wp]:
  "\<lbrace>\<top>\<rbrace> decodeCVSpace xs cap y zs
   \<lbrace>\<lambda>rv s. tcCapsCRoot rv \<noteq> None\<rbrace>,-"
  apply (simp add: decodeCVSpace_def split_def cap_CNode_case_throw
             cong: list.case_cong if_cong del: not_None_eq)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpcw
             | simp only: tcbinvocation.sel option.simps)+
  apply simp
  done

lemma decodeSetSpaceSome[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetSpace xs cap y zs
   \<lbrace>\<lambda>rv s. tcCapsCRoot rv \<noteq> None\<rbrace>,-"
  apply (simp add: decodeSetSpace_def decodeCVSpace_def split_def cap_CNode_case_throw
             cong: list.case_cong if_cong del: not_None_eq)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpcw
             | simp only: tcbinvocation.sel option.simps)+
  apply simp
  done

lemma decodeTCBConf_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
      and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile>' fst x \<and> cte_at' (snd x) s \<and> t \<noteq> snd x \<and> t + 2^cteSizeBits \<noteq> snd x)\<rbrace>
     decodeTCBConfigure args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (clarsimp simp add: decodeTCBConfigure_def Let_def
                 split del: if_split cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
    apply (rule_tac Q'="\<lambda>setSpace s. tcb_inv_wf' setSpace s \<and> tcb_inv_wf' setIPCParams s
                             \<and> isThreadControlCaps setSpace \<and> isThreadControlCaps setIPCParams
                             \<and> tcCapsTarget setSpace = t \<and> tcCapsCRoot setSpace \<noteq> None"
                        in hoare_strengthen_postE_R)
     apply wp
    apply (clarsimp simp: isThreadControl_def2 cong: option.case_cong)
   apply wpsimp
  apply (fastforce simp: isThreadControl_def2 objBits_defs)
  done

lemma lsft_real_cte:
  "\<lbrace>valid_objs'\<rbrace> lookupSlotForThread t x \<lbrace>\<lambda>rv. real_cte_at' rv\<rbrace>, -"
  apply (simp add: lookupSlotForThread_def)
  apply (wp resolveAddressBits_real_cte_at'|simp add: split_def)+
  done

lemma tcb_real_cte_16:
  "\<lbrakk> real_cte_at' (t+2^cteSizeBits) s; tcb_at' t s \<rbrakk> \<Longrightarrow> False"
  by (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_16)

lemma corres_splitEE':
  assumes x: "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
  assumes y: "\<And>x y x' y'. r' (x, y) (x', y')
              \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (R x y) (R' x' y') (b x y) (d x' y')"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>%(x, y). R x y \<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>%(x, y). R' x y\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>(x, y). b x y)) (c >>=E (\<lambda>(x, y). d x y))"
  using assms
  apply (unfold bindE_def validE_def split_def)
  apply (rule corres_split[rotated 2])
     apply assumption+
  apply (case_tac rv)
   apply (clarsimp simp: lift_def y)+
  done

lemma decodeBindNotification_corres:
notes if_cong[cong] shows
  "\<lbrakk> list_all2 (\<lambda>x y. cap_relation (fst x) (fst y)) extras extras' \<rbrakk> \<Longrightarrow>
    corres (ser \<oplus> tcbinv_relation)
      (invs and tcb_at t and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> (fst x)))
      (invs' and tcb_at' t and (\<lambda>s. \<forall>x \<in> set extras'. s \<turnstile>' (fst x)))
     (decode_bind_notification (cap.ThreadCap t) extras)
     (decodeBindNotification (capability.ThreadCap t) extras')"
  apply (simp add: decode_bind_notification_def decodeBindNotification_def)
  apply (simp add: null_def returnOk_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_norE)
       apply (rule corres_trivial)
       apply (auto simp: returnOk_def whenE_def)[1]
      apply (rule_tac F="extras \<noteq> []" in corres_gen_asm)
      apply (rule corres_split_eqrE)
         apply simp
         apply (rule getBoundNotification_corres)
        apply (rule corres_split_norE)
           apply (rule corres_trivial, simp split: option.splits add: returnOk_def)
          apply (rule corres_splitEE'[where r'="\<lambda>rv rv'. ((fst rv) = (fst rv')) \<and> ((snd rv') = (AllowRead \<in> (snd rv)))"])
             apply (rule corres_trivial, simp)
             apply (case_tac extras, simp, clarsimp simp: list_all2_Cons1)
             apply (fastforce split: cap.splits capability.splits simp: returnOk_def)
            apply (rule corres_split_norE)
               apply (rule corres_trivial, clarsimp simp: whenE_def returnOk_def)
              apply (clarsimp split del: if_split)
              apply (rule corres_splitEE[where r'=ntfn_relation])
                 apply simp
                 apply (rule getNotification_corres)
                apply (rule corres_trivial, simp split del: if_split)
                apply (simp add: ntfn_relation_def
                          split: Structures_A.ntfn.splits Structures_H.ntfn.splits
                                 option.splits)
               apply wp+
             apply (wp | simp add: whenE_def split del: if_split)+
           apply (wp | wpc | simp)+
       apply (simp | wp gbn_wp gbn_wp')+
   apply (fastforce simp: valid_cap_def valid_cap'_def obj_at_def is_tcb dest: hd_in_set)+
  done

lemma decodeUnbindNotification_corres:
  "corres (ser \<oplus> tcbinv_relation)
      (tcb_at t and pspace_aligned and pspace_distinct)
      \<top>
     (decode_unbind_notification (cap.ThreadCap t))
     (decodeUnbindNotification (capability.ThreadCap t))"
  apply (simp add: decode_unbind_notification_def decodeUnbindNotification_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply simp
       apply (rule getBoundNotification_corres)
      apply (rule corres_trivial)
      apply (simp split: option.splits)
      apply (simp add: returnOk_def)
     apply wp+
   apply auto
  done

lemma decodeSetTLSBase_corres:
  "corres (ser \<oplus> tcbinv_relation) (tcb_at t) (tcb_at' t)
          (decode_set_tls_base w (cap.ThreadCap t))
          (decodeSetTLSBase w (capability.ThreadCap t))"
  by (clarsimp simp: decode_set_tls_base_def decodeSetTLSBase_def returnOk_def
                 split: list.split)

lemma decodeSetTimeoutEndpoint_corres:
  "list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras' \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation) (tcb_at t) (tcb_at' t)
          (decode_set_timeout_ep (cap.ThreadCap t) slot extras)
          (decodeSetTimeoutEndpoint (capability.ThreadCap t) (cte_map slot) extras')"
  apply (clarsimp simp: decode_set_timeout_ep_def decodeSetTimeoutEndpoint_def)
  apply (cases extras; cases extras'; clarsimp)
  apply (fastforce simp: check_handler_ep_def unlessE_def returnOk_def bindE_def
                         newroot_rel_def emptyTCCaps_def throwError_def
                   dest: cap_rel_valid_fh)
  done

lemma decodeTCBInvocation_corres:
 "\<lbrakk> c = Structures_A.ThreadCap t; cap_relation c c';
      list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras';
      length args < 2 ^ word_bits \<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> tcbinv_relation) (einvs and tcb_at t and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x \<and> cte_at (snd x) s))
                                 (invs' and tcb_at' t and (\<lambda>s. \<forall>x \<in> set extras'. s \<turnstile>' fst x \<and> cte_at' (snd x) s))
         (decode_tcb_invocation label args c slot extras)
         (decodeTCBInvocation label args c' (cte_map slot) extras')"
  apply (rule_tac F="cap_aligned c \<and> capAligned c'" in corres_req)
   apply (clarsimp simp: cap_aligned_def capAligned_def objBits_simps word_bits_def)
   apply (drule obj_at_aligned', simp_all add: objBits_simps')
  apply (clarsimp simp: decode_tcb_invocation_def
                        decodeTCBInvocation_def
             split del: if_split split: gen_invocation_labels.split)
  apply (simp add: returnOk_def)
  apply (intro conjI impI
             corres_guard_imp[OF decodeReadRegisters_corres]
             corres_guard_imp[OF decodeWriteRegisters_corres]
             corres_guard_imp[OF decodeCopyRegisters_corres]
             corres_guard_imp[OF decodeTCBConfigure_corres]
             corres_guard_imp[OF decodeSetPriority_corres]
             corres_guard_imp[OF decodeSetMCPriority_corres]
             corres_guard_imp[OF decodeSetSchedParams_corres]
             corres_guard_imp[OF decodeSetIPCBuffer_corres]
             corres_guard_imp[OF decodeSetSpace_corres]
             corres_guard_imp[OF decodeBindNotification_corres]
             corres_guard_imp[OF decodeUnbindNotification_corres]
             corres_guard_imp[OF decodeSetTLSBase_corres]
             corres_guard_imp[OF decodeSetTimeoutEndpoint_corres],
         simp_all add: valid_cap_simps valid_cap_simps' invs_def valid_sched_def)
  apply (auto simp: list_all2_map1 list_all2_map2
             elim!: list_all2_mono)
  done

crunch decodeTCBInvocation
 for inv[wp]: P
  (simp: crunch_simps wp: crunch_wps)

lemma real_cte_at_not_tcb_at':
  "real_cte_at' x s \<Longrightarrow> \<not> tcb_at' x s"
  "real_cte_at' (x + 2^cteSizeBits) s \<Longrightarrow> \<not> tcb_at' x s"
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp elim!: tcb_real_cte_16)
  done

lemma decodeBindNotification_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t
         and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile>' (fst x) \<and> (\<forall>y \<in> zobj_refs' (fst x). ex_nonz_cap_to' y s))\<rbrace>
     decodeBindNotification (capability.ThreadCap t) extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeBindNotification_def whenE_def
             cong: list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp getNotification_wp getObject_tcb_wp
        | wpc
        | simp add: threadGet_getObject getBoundNotification_def)+
  apply (fastforce simp: valid_cap'_def[where c="capability.ThreadCap t"]
                         is_ntfn invs_def valid_pspace'_def
                         projectKOs null_def pred_tcb_at'_def obj_at'_def
                   dest!: global'_no_ex_cap hd_in_set)
  done

lemma decodeUnbindNotification_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     decodeUnbindNotification (capability.ThreadCap t)
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeUnbindNotification_def)
  apply (wp getObject_tcb_wp | wpc | simp add: threadGet_getObject getBoundNotification_def)+
  apply (auto simp: obj_at'_def pred_tcb_at'_def)
  done

lemma decodeSetTLSBase_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     decodeSetTLSBase w (capability.ThreadCap t)
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeSetTLSBase_def
             cong: list.case_cong)
  by wpsimp

lemma decodeSetTimeoutEndpoint_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
     and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile>' fst x \<and> cte_at' (snd x) s)\<rbrace>
   decodeSetTimeoutEndpoint (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeSetTimeoutEndpoint_def emptyTCCaps_def
             cong: list.case_cong)
  apply wpsimp
  done

lemma decodeTCBInv_wf:
  "\<lbrace>invs' and tcb_at' t and cte_at' slot and ex_nonz_cap_to' t
         and (\<lambda>s. \<forall>x \<in> set extras. real_cte_at' (snd x) s
                          \<and> s \<turnstile>' fst x \<and> (\<forall>y \<in> zobj_refs' (fst x). ex_nonz_cap_to' y s))\<rbrace>
   decodeTCBInvocation label args (capability.ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeTCBInvocation_def Let_def
              cong: if_cong gen_invocation_labels.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wpc, (wp decodeTCBConf_wf decodeReadReg_wf decodeWriteReg_wf decodeSetTLSBase_wf
             decodeCopyReg_wf decodeBindNotification_wf decodeUnbindNotification_wf
             decodeSetSchedParams_wf)+)
  apply (clarsimp simp: real_cte_at')
  apply (fastforce simp: real_cte_at_not_tcb_at' objBits_defs)
  done

crunch getThreadBufferSlot, setPriority, setMCPriority
  for irq_states'[wp]: valid_irq_states'
  (simp: crunch_simps wp: crunch_wps)


end

end
