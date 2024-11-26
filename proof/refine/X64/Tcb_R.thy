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
  "corres dc (tcb_at t and invs) invs'
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

lemma activateThread_corres:
 "corres dc (invs and ct_in_state activatable) (invs' and ct_in_state' activatable')
            activate_thread activateThread"
  supply subst_all [simp del]
  apply (simp add: activate_thread_def activateThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getCurThread_corres])
      apply (rule_tac R="\<lambda>ts s. valid_tcb_state ts s \<and> (idle ts \<or> runnable ts)
                                \<and> invs s \<and> st_tcb_at ((=) ts) thread s"
                  and R'="\<lambda>ts s. valid_tcb_state' ts s \<and> (idle' ts \<or> runnable' ts)
                                \<and> invs' s \<and> st_tcb_at' (\<lambda>ts'. ts' = ts) thread s"
                  in  corres_split[OF getThreadState_corres])
        apply (rule_tac F="idle rv \<or> runnable rv" in corres_req, simp)
        apply (rule_tac F="idle' rv' \<or> runnable' rv'" in corres_req, simp)
        apply (case_tac rv, simp_all add:
                  isRunning_def isRestart_def,
                  safe, simp_all)[1]
         apply (rule corres_guard_imp)
           apply (rule corres_split_eqr[OF asUser_getRestartPC_corres])
             apply (rule corres_split_nor[OF asUser_setNextPC_corres])
               apply (rule setThreadState_corres)
               apply (simp | wp weak_sch_act_wf_lift_linear)+
          apply (fastforce simp: st_tcb_at_tcb_at)
         apply fastforce
        apply (rule corres_guard_imp)
          apply (rule activateIdleThread_corres)
         apply (clarsimp elim!: st_tcb_weakenE)
        apply (clarsimp elim!: pred_tcb'_weakenE)
       apply (wp gts_st_tcb gts_st_tcb' gts_st_tcb_at)+
   apply (fastforce simp: ct_in_state_def tcb_at_invs
                   elim!: st_tcb_weakenE)
  apply (clarsimp simp: tcb_at_invs' ct_in_state'_def
                 elim!: pred_tcb'_weakenE)
  done


lemma bindNotification_corres:
  "corres dc
         (invs and tcb_at t and ntfn_at a) (invs' and tcb_at' t and ntfn_at' a)
         (bind_notification t a) (bindNotification t a)"
  apply (simp add: bind_notification_def bindNotification_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getNotification_corres])
      apply (rule corres_split[OF setNotification_corres])
         apply (clarsimp simp: ntfn_relation_def split: Structures_A.ntfn.splits)
        apply (rule setBoundNotification_corres)
       apply (wp)+
   apply auto
  done


abbreviation
  "ct_idle' \<equiv> ct_in_state' idle'"

lemma gts_st_tcb':
  "\<lbrace>tcb_at' t\<rbrace> getThreadState t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>st. st = rv) t\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_post_imp[where Q'="\<lambda>rv s. \<exists>rv'. rv = rv' \<and> st_tcb_at' (\<lambda>st. st = rv') t s"])
    apply simp
   apply (wp hoare_vcg_ex_lift)
  apply (clarsimp simp add: pred_tcb_at'_def obj_at'_def)
  done

lemma activateIdle_invs:
  "\<lbrace>invs' and ct_idle'\<rbrace>
     activateIdleThread thread
   \<lbrace>\<lambda>rv. invs' and ct_idle'\<rbrace>"
  by (simp add: activateIdleThread_def)

lemma activate_invs':
  "\<lbrace>invs' and sch_act_simple and ct_in_state' activatable'\<rbrace>
     activateThread
   \<lbrace>\<lambda>rv. invs' and (ct_running' or ct_idle')\<rbrace>"
  apply (simp add: activateThread_def)
  apply (rule bind_wp)
   apply (rule_tac Q'="\<lambda>state s. invs' s \<and> sch_act_simple s
                                 \<and> st_tcb_at' (\<lambda>st. st = state) thread s
                                 \<and> thread = ksCurThread s
                                 \<and> (runnable' state \<or> idle' state)"
                in bind_wp)
    apply (case_tac rv, simp_all add: isTS_defs)
      apply (wp)
      apply (clarsimp simp: ct_in_state'_def)
     apply (rule_tac Q'="\<lambda>rv. invs' and ct_idle'" in hoare_post_imp, simp)
     apply (wp activateIdle_invs)
     apply (clarsimp simp: ct_in_state'_def)
    apply (rule_tac Q'="\<lambda>rv. invs' and ct_running' and sch_act_simple"
                 in hoare_post_imp, simp)
    apply (rule hoare_weaken_pre)
     apply (wp ct_in_state'_set asUser_ct sts_invs_minor'
          | wp (once) sch_act_simple_lift)+
      apply (rule_tac Q'="\<lambda>_. st_tcb_at' runnable' thread
                             and sch_act_simple and invs'
                             and (\<lambda>s. thread = ksCurThread s)"
               in hoare_post_imp, clarsimp)
      apply (wp sch_act_simple_lift)+
    apply (clarsimp simp: valid_idle'_def invs'_def valid_state'_def
                          pred_tcb_at'_def obj_at'_def idle_tcb'_def
                   elim!: pred_tcb'_weakenE)
   apply (wp gts_st_tcb')+
  apply (clarsimp simp: tcb_at_invs' ct_in_state'_def
                         pred_disj_def)
  done

crunch activateIdleThread
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: setNextPC)

declare not_psubset_eq[dest!]

lemma setThreadState_runnable_simp:
  "runnable' ts \<Longrightarrow> setThreadState ts t =
   threadSet (tcbState_update (\<lambda>x. ts)) t"
  apply (simp add: setThreadState_def isRunnable_def isStopped_def liftM_def)
  apply (subst bind_return[symmetric], rule bind_cong[OF refl])
  apply (drule use_valid[OF _ threadSet_pred_tcb_at_state[where proj="itcbState" and p=t and P="(=) ts"]])
   apply simp
  apply (subst bind_known_operation_eq)
       apply wp+
     apply clarsimp
    apply (subst eq_commute, erule conjI[OF _ refl])
   apply (rule empty_fail_getThreadState)
  apply (simp add: getCurThread_def getSchedulerAction_def exec_gets)
  apply (auto simp: when_def split: Structures_H.thread_state.split)
  done

lemma activate_sch_act:
  "\<lbrace>ct_in_state' activatable' and (\<lambda>s. P (ksSchedulerAction s))\<rbrace>
     activateThread \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: activateThread_def getCurThread_def
             cong: if_cong Structures_H.thread_state.case_cong)
  apply (rule bind_wp [OF _ gets_sp])
  apply (rule bind_wp[where Q'="\<lambda>st s. (runnable' or idle') st \<and> P (ksSchedulerAction s)"])
   apply (rule hoare_pre)
    apply (wp | wpc | simp add: setThreadState_runnable_simp)+
  apply (clarsimp simp: ct_in_state'_def cur_tcb'_def pred_tcb_at'
                 elim!: pred_tcb'_weakenE)
  done

lemma runnable_tsr:
  "thread_state_relation ts ts' \<Longrightarrow> runnable' ts' = runnable ts"
  by (case_tac ts, auto)

lemma idle_tsr:
  "thread_state_relation ts ts' \<Longrightarrow> idle' ts' = idle ts"
  by (case_tac ts, auto)

crunch cancelIPC
  for cur[wp]: cur_tcb'
  (wp: crunch_wps simp: crunch_simps o_def)

crunch setupReplyMaster
  for cur[wp]: cur_tcb'
  (wp: crunch_wps simp: crunch_simps)

lemma setCTE_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   setCTE c cte
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: weak_sch_act_wf_def)
  apply (wp hoare_vcg_all_lift hoare_convert_imp setCTE_pred_tcb_at' setCTE_tcb_in_cur_domain')
  done

lemma setupReplyMaster_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   setupReplyMaster thread
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setupReplyMaster_def)
  apply (wp)
    apply (rule_tac Q'="\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s"
               in hoare_post_imp, clarsimp)
    apply (wp)+
  apply assumption
  done

crunch setup_reply_master
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

lemma restart_corres:
  "corres dc (einvs  and tcb_at t) (invs' and tcb_at' t and ex_nonz_cap_to' t)
      (Tcb_A.restart t) (ThreadDecls_H.restart t)"
  apply (simp add: Tcb_A.restart_def Thread_H.restart_def)
  apply (simp add: isStopped_def2 liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (clarsimp simp add: runnable_tsr idle_tsr when_def)
      apply (rule corres_split_nor[OF cancel_ipc_corres])
        apply (rule corres_split_nor[OF setupReplyMaster_corres])
          apply (rule corres_split_nor[OF setThreadState_corres])
             apply clarsimp
            apply (rule corres_split[OF tcbSchedEnqueue_corres possibleSwitchTo_corres])
              apply (wp set_thread_state_runnable_weak_valid_sched_action sts_st_tcb_at'
                        sts_st_tcb' sts_valid_objs'
                     | clarsimp simp: valid_tcb_state'_def | strengthen valid_objs'_valid_tcbs')+
         apply (rule_tac Q'="\<lambda>rv. valid_sched and cur_tcb and pspace_aligned and pspace_distinct"
                         in hoare_strengthen_post)
          apply wp
         apply (fastforce simp: valid_sched_def valid_sched_action_def)
        apply (rule_tac Q'="\<lambda>rv. invs' and ex_nonz_cap_to' t" in hoare_strengthen_post)
         apply wp
        apply (clarsimp simp: invs'_def valid_state'_def sch_act_wf_weak valid_pspace'_def
                              valid_tcb_state'_def)
       apply wp+
   apply (fastforce simp: valid_sched_def invs_def tcb_at_is_etcb_at)
  apply (clarsimp simp add: invs'_def valid_state'_def sch_act_wf_weak)
  done

lemma restart_invs':
  "\<lbrace>invs' and ex_nonz_cap_to' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   ThreadDecls_H.restart t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: restart_def isStopped_def2)
  apply (wp setThreadState_nonqueued_state_update
            cancelIPC_simple setThreadState_st_tcb
       | wp (once) sch_act_simple_lift)+
       apply (wp hoare_convert_imp)
      apply (wp setThreadState_nonqueued_state_update
                setThreadState_st_tcb)
     apply (clarsimp)
     apply (wp hoare_convert_imp)[1]
    apply (clarsimp)
    apply (wp)+
   apply (clarsimp simp: comp_def)
   apply (rule hoare_strengthen_post, rule gts_sp')
   prefer 2
   apply assumption
  apply (clarsimp simp: pred_tcb_at' invs'_def valid_state'_def
                        ct_in_state'_def)
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma restart_tcb'[wp]:
  "\<lbrace>tcb_at' t'\<rbrace> ThreadDecls_H.restart t \<lbrace>\<lambda>rv. tcb_at' t'\<rbrace>"
  apply (simp add: restart_def isStopped_def2)
  apply wpsimp
  done

lemma no_fail_setRegister: "no_fail \<top> (setRegister r v)"
  by (simp add: setRegister_def)

lemma suspend_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> suspend t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: suspend_def)
  unfolding updateRestartPC_def
  apply (wp threadSet_cap_to' | simp)+
  done

declare det_getRegister[simp]
declare det_setRegister[simp]

lemma
  no_fail_getRegister[wp]: "no_fail \<top> (getRegister r)"
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
       apply wp+
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                  dest!: idle_no_ex_cap)
  apply (clarsimp simp: invs'_def valid_state'_def dest!: global'_no_ex_cap)
  done

lemma einvs_valid_etcbs: "einvs s \<longrightarrow> valid_etcbs s"
  by (clarsimp simp: valid_sched_def)

lemma asUser_postModifyRegisters_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) (tcb_at' ct)
     (arch_post_modify_registers ct t)
     (asUser t $ postModifyRegisters ct t)"
  apply (clarsimp simp: arch_post_modify_registers_def postModifyRegisters_def when_def)
  apply (rule conjI; clarsimp)
   apply (corres corres: asUser_setRegister_corres)
  apply (subst submonad_asUser.return)
  apply (rule corres_stateAssert_assume; simp)
  done

crunch Tcb_A.restart, IpcCancel_A.suspend
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

crunch restart
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  (simp: crunch_simps wp: crunch_wps threadSet_sched_pointers threadSet_valid_sched_pointers)

lemma invokeTCB_WriteRegisters_corres:
  "corres (dc \<oplus> (=)) (einvs  and tcb_at dest and ex_nonz_cap_to dest)
        (invs' and sch_act_simple and tcb_at' dest and ex_nonz_cap_to' dest)
        (invoke_tcb (tcb_invocation.WriteRegisters dest resume values arch))
        (invokeTCB (tcbinvocation.WriteRegisters dest resume values arch'))"
  apply (simp add: invokeTCB_def performTransfer_def arch_get_sanitise_register_info_def
                   sanitiseRegister_def sanitise_register_def getSanitiseRegisterInfo_def
                   frameRegisters_def gpRegisters_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split_nor)
         apply (rule asUser_corres)
         apply (simp add: zipWithM_mapM getRestartPC_def setNextPC_def)
         apply (rule corres_Id)
           apply (clarsimp simp: sanitise_or_flags_def sanitise_and_flags_def
                                 sanitiseOrFlags_def sanitiseAndFlags_def
                                 mask_def user_vtop_def
                           cong: if_cong)
          apply simp
         apply (wpsimp wp: no_fail_mapM no_fail_setRegister)
            apply (clarsimp simp: sanitiseOrFlags_def sanitiseAndFlags_def)
            apply ((safe)[1], (wp no_fail_setRegister | simp)+)
        apply (rule corres_split_nor[OF asUser_postModifyRegisters_corres[simplified]])
          apply (rule corres_split_nor[OF corres_when[OF refl restart_corres]])
            apply (rule corres_split_nor[OF corres_when[OF refl rescheduleRequired_corres]])
              apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
              apply simp
             apply (wp+)[2]
           apply ((wp hoare_weak_lift_imp restart_invs'
                   | strengthen valid_sched_weak_strg einvs_valid_etcbs
                                invs_weak_sch_act_wf
                                valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct
                                valid_sched_valid_queues valid_objs'_valid_tcbs' invs_valid_objs'
                   | clarsimp simp: invs_def valid_state_def valid_sched_def invs'_def valid_state'_def
                             dest!: global'_no_ex_cap idle_no_ex_cap)+)[2]
         apply (rule_tac Q'="\<lambda>_. einvs and tcb_at dest and ex_nonz_cap_to dest" in hoare_post_imp)
          apply (fastforce simp: invs_def valid_sched_weak_strg valid_sched_def valid_state_def dest!: idle_no_ex_cap)
         prefer 2
         apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' dest and ex_nonz_cap_to' dest" in hoare_post_imp)
          apply (fastforce simp: sch_act_wf_weak invs'_def valid_state'_def dest!: global'_no_ex_cap)
         apply wpsimp+
   apply fastforce
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

lemma suspend_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   suspend t
   \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  by (wpsimp simp: suspend_def)

crunch restart, suspend
  for cur_tcb'[wp]: cur_tcb'
  (wp: crunch_wps threadSet_cur ignore: threadSet)

lemma invokeTCB_CopyRegisters_corres:
  "corres (dc \<oplus> (=))
        (einvs and simple_sched_action and tcb_at dest and tcb_at src and ex_nonz_cap_to src and
          ex_nonz_cap_to dest)
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
     apply fastforce
    apply simp
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
              apply (wpsimp wp: mapM_x_wp' hoare_weak_lift_imp)+
            apply (rule corres_split_nor)
               apply (rule corres_when[OF refl])
               apply (rule R[OF refl refl])
               apply (simp add: gpRegisters_def)
              apply (rule corres_split_eqr[OF getCurThread_corres])
                apply (rule corres_split_nor[OF asUser_postModifyRegisters_corres[simplified]])
                  apply (rule corres_split[OF corres_when[OF refl rescheduleRequired_corres]])
                    apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
                    apply simp
                   apply ((solves \<open>wpsimp wp: hoare_weak_lift_imp\<close>)+)
                 apply (rule_tac Q'="\<lambda>_. einvs and tcb_at dest" in hoare_post_imp)
                  apply (fastforce simp: invs_def valid_sched_weak_strg valid_sched_def)
                 prefer 2
                 apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' dest" in hoare_post_imp)
                  apply (fastforce simp: invs'_def valid_state'_def invs_weak_sch_act_wf cur_tcb'_def)
                 apply ((wp mapM_x_wp' hoare_weak_lift_imp | simp flip: cur_tcb'_def)+)[8]
         apply ((wp hoare_weak_lift_imp restart_invs' | wpc |
                 clarsimp simp: if_apply_def2 simp flip: cur_tcb'_def)+)[2]
       apply (wp suspend_nonz_cap_to_tcb hoare_weak_lift_imp
              | simp add: if_apply_def2 flip: cur_tcb'_def)+
     apply (fastforce simp: invs_def valid_state_def valid_pspace_def
                     dest!: idle_no_ex_cap)
    apply clarsimp
    apply (fastforce simp: invs'_def valid_state'_def dest!: global'_no_ex_cap)
    done
qed

lemma readreg_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' src and ex_nonz_cap_to' src\<rbrace>
     invokeTCB (tcbinvocation.ReadRegisters src susp n arch)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: invokeTCB_def performTransfer_def | wp
       | clarsimp simp: invs'_def valid_state'_def
                 dest!: global'_no_ex_cap)+

crunch getSanitiseRegisterInfo
  for invs'[wp]: invs'

crunch getSanitiseRegisterInfo
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' d"
crunch getSanitiseRegisterInfo
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch getSanitiseRegisterInfo
  for tcb_at'[wp]: "tcb_at' a"

lemma writereg_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' dest and ex_nonz_cap_to' dest\<rbrace>
     invokeTCB (tcbinvocation.WriteRegisters dest resume values arch)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: invokeTCB_def performTransfer_def | wp restart_invs' | rule conjI
       | clarsimp
       | clarsimp simp: invs'_def valid_state'_def
                 dest!: global'_no_ex_cap)+

lemma copyreg_invs'':
  "\<lbrace>invs' and sch_act_simple and tcb_at' src and tcb_at' dest and ex_nonz_cap_to' src and ex_nonz_cap_to' dest\<rbrace>
     invokeTCB (tcbinvocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace>\<lambda>rv. invs' and tcb_at' dest\<rbrace>"
  apply (simp add: invokeTCB_def performTransfer_def)
  apply (wp mapM_x_wp' restart_invs' hoare_vcg_imp_lift | wps | simp add: if_apply_def2)+
  by (fastforce simp: invs'_def valid_state'_def dest!: global'_no_ex_cap)

lemma copyreg_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' src and
          tcb_at' dest and ex_nonz_cap_to' src and ex_nonz_cap_to' dest\<rbrace>
     invokeTCB (tcbinvocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (rule hoare_strengthen_post, rule copyreg_invs'', simp)

lemma isRunnable_corres:
  "corres (\<lambda>ts runn. runnable ts = runn) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (get_thread_state t) (isRunnable t)"
  apply (simp add: isRunnable_def)
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
  apply (wp tg_sp' [where P=\<top>, simplified] | simp)+
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

lemma valid_tcb'_tcbPriority_update: "\<lbrakk>valid_tcb' tcb s; f (tcbPriority tcb) \<le> maxPriority \<rbrakk> \<Longrightarrow> valid_tcb' (tcbPriority_update f tcb) s"
  apply (simp add: valid_tcb'_def tcb_cte_cases_def)
  done

lemma threadSet_valid_objs_tcbPriority_update:
  "\<lbrace>valid_objs' and (\<lambda>_. x \<le> maxPriority)\<rbrace>
     threadSet (tcbPriority_update (\<lambda>_. x)) t
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
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
   apply (rule valid_tcb'_tcbPriority_update)
    apply (fastforce  simp: obj_at'_def)+
  done

lemma tcbSchedDequeue_ct_in_state'[wp]:
  "\<lbrace>ct_in_state' test\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>rv. ct_in_state' test\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread]; wp)
  done

lemma sp_corres2:
  "corres dc
     (valid_etcbs and weak_valid_sched_action and cur_tcb and tcb_at t
      and valid_queues and pspace_aligned and pspace_distinct)
     (tcb_at' t and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and valid_objs' and (\<lambda>_. x \<le> maxPriority)
      and sym_heap_sched_pointers and valid_sched_pointers and pspace_aligned' and pspace_distinct')
     (set_priority t x) (setPriority t x)"
  apply (simp add: setPriority_def set_priority_def thread_set_priority_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF tcbSchedDequeue_corres], simp)
      apply (rule corres_split[OF ethread_set_corres], simp_all)[1]
         apply (simp add: etcb_relation_def)
        apply (rule corres_split[OF isRunnable_corres])
          apply (erule corres_when)
          apply(rule corres_split[OF getCurThread_corres])
            apply (wp corres_if; clarsimp)
             apply (rule rescheduleRequired_corres)
            apply (rule possibleSwitchTo_corres)
           apply ((clarsimp
                   | wp hoare_weak_lift_imp hoare_vcg_if_lift hoare_wp_combs gts_wp
                        isRunnable_wp)+)[4]
       apply (wp hoare_vcg_imp_lift' hoare_vcg_if_lift hoare_vcg_all_lift
                 ethread_set_not_queued_valid_queues
              | strengthen valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct)+
      apply ((wp hoare_vcg_imp_lift' hoare_vcg_all_lift
                 isRunnable_wp threadSet_pred_tcb_no_state
                 threadSet_valid_objs_tcbPriority_update threadSet_sched_pointers
                 threadSet_valid_sched_pointers tcb_dequeue_not_queued tcbSchedDequeue_not_queued
                 threadSet_weak_sch_act_wf
              | simp add: etcb_relation_def
              | strengthen valid_objs'_valid_tcbs'
                obj_at'_weakenE[where P="Not \<circ> tcbQueued"]
              | wps)+)
   apply (force simp: valid_etcbs_def tcb_at_st_tcb_at[symmetric] state_relation_def
                dest: pspace_relation_tcb_at intro: st_tcb_at_opeqI)
  apply clarsimp
  done

lemma setPriority_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t and valid_objs' and (\<lambda>_. x \<le> maxPriority))
          (set_priority t x) (setPriority t x)"
  apply (rule corres_guard_imp)
    apply (rule sp_corres2)
   apply (fastforce simp: valid_sched_def valid_sched_action_def)
  apply (fastforce simp: invs'_def valid_state'_def sch_act_wf_weak)
  done

lemma setMCPriority_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (set_mcpriority t x) (setMCPriority t x)"
  apply (rule corres_guard_imp)
    apply (clarsimp simp: setMCPriority_def set_mcpriority_def)
    apply (rule threadset_corresT)
       by (clarsimp simp: tcb_relation_def tcb_cap_cases_tcb_mcpriority
                          tcb_cte_cases_def exst_same_def)+

definition
 "out_rel fn fn' v v' \<equiv>
     ((v = None) = (v' = None)) \<and>
     (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow>
                 tcb_relation (case_option id fn v tcb)
                              (case_option id fn' v' tcb'))"

lemma out_corresT:
  assumes x: "\<And>tcb v. \<forall>(getF, setF)\<in>ran tcb_cap_cases. getF (fn v tcb) = getF tcb"
  assumes y: "\<And>v. \<forall>tcb. \<forall>(getF, setF)\<in>ran tcb_cte_cases. getF (fn' v tcb) = getF tcb"
  assumes sched_pointers: "\<And>tcb v. tcbSchedPrev (fn' v tcb) = tcbSchedPrev tcb"
                          "\<And>tcb v. tcbSchedNext (fn' v tcb) = tcbSchedNext tcb"
  assumes flag: "\<And>tcb v. tcbQueued (fn' v tcb) = tcbQueued tcb"
  assumes e: "\<And>tcb v. exst_same tcb (fn' v tcb)"
  shows
  "out_rel fn fn' v v' \<Longrightarrow>
     corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
       (option_update_thread t fn v)
       (case_option (return ()) (\<lambda>x. threadSet (fn' x) t) v')"
  apply (case_tac v, simp_all add: out_rel_def option_update_thread_def)
  apply (clarsimp simp: threadset_corresT [OF _ x y sched_pointers flag e])
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
         | clarsimp simp: cteCaps_of_def tcbSchedNext_update_tcb_cte_cases o_def | rule refl)+
  by (auto simp: obj_at'_def)

lemma setP_invs':
  "\<lbrace>invs' and tcb_at' t and K (p \<le> maxPriority)\<rbrace> setPriority t p \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding setPriority_def
  by (wpsimp wp: rescheduleRequired_invs' threadSet_priority_invs')

crunch setPriority, setMCPriority
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and valid_cap[wp]: "valid_cap' c"
  (simp: crunch_simps wp: crunch_wps)

lemmas setPriority_typ_ats [wp] = typ_at_lifts [OF setPriority_typ_at']

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
  apply (case_tac d, (simp_all split: arch_cap.split)[11])
  apply (rename_tac arch_capa)
  apply (clarsimp simp add: X64_H.sameObjectAs_def Let_def)
  apply (intro conjI impI)
     apply (case_tac arch_cap; simp add: isCap_simps del: not_ex)
    apply (case_tac arch_cap; simp add: isCap_simps del: not_ex)
    apply (case_tac arch_capa; clarsimp simp del: not_ex simp add: isCap_simps)
   apply (case_tac arch_cap; simp add: isCap_simps del: not_ex)
   apply (case_tac arch_capa; clarsimp simp del: not_ex simp add: isCap_simps)
   apply fastforce
  apply (case_tac arch_cap; simp add: sameRegionAs_def isCap_simps)
   apply (case_tac arch_capa; simp)
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
               and cte_at slot and K (is_cnode_or_valid_arch new_cap
                                        \<and> (is_pt_cap new_cap \<or> is_pd_cap new_cap \<or> is_pdpt_cap new_cap \<or> is_pml4_cap new_cap
                                               \<longrightarrow> cap_asid new_cap \<noteq> None))
               and cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                                \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                    vspace_asid c = vspace_asid new_cap) src_slot)
             (invs' and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) (cte_map (target, ref))
               and valid_cap' newCap)
     (check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))))
     (checkCapAt newCap (cte_map src_slot)
      (checkCapAt (ThreadCap target) (cte_map slot)
       (assertDerived (cte_map src_slot) newCap (cteInsert newCap (cte_map src_slot) (cte_map (target, ref))))))"
  apply (rule corres_guard_imp)
  apply (rule_tac P="cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref) and
                           cte_at slot and
                           cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                                   \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and> vspace_asid c = vspace_asid new_cap) src_slot
                           and einvs and K (is_cnode_or_valid_arch new_cap
                                            \<and> (is_pt_cap new_cap \<or> is_pd_cap new_cap \<or> is_pdpt_cap new_cap \<or> is_pml4_cap new_cap
                                                 \<longrightarrow> cap_asid new_cap \<noteq> None))"
                        and
                        P'="cte_wp_at' (\<lambda>c. cteCap c = NullCap) (cte_map (target, ref))
                            and invs' and valid_cap' newCap"
                       in checkCapAt_corres, assumption)
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
     apply (erule(1) checked_insert_is_derived)
      apply simp
     apply simp
    apply fastforce
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply clarsimp
  apply fastforce
  done

lemma capBadgeNone_masters:
  "capMasterCap cap = capMasterCap cap'
      \<Longrightarrow> (capBadge cap = None) = (capBadge cap' = None)"
  apply (rule master_eqI)
   apply (auto simp add: capBadge_def capMasterCap_def isCap_simps
             split: capability.split)
  done

definition
  "vspace_asid' cap \<equiv> case cap of
    ArchObjectCap (PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageDirectoryCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PDPointerTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PML4Cap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemma untyped_derived_eq_from_sameObjectAs:
  "sameObjectAs cap cap2
    \<Longrightarrow> untyped_derived_eq cap cap2"
  by (clarsimp simp: untyped_derived_eq_def sameObjectAs_def2 isCap_Master)

lemmas vspace_asid'_simps [simp] =
  vspace_asid'_def [split_simps capability.split arch_capability.split option.split prod.split]

lemma checked_insert_tcb_invs'[wp]:
  "\<lbrace>invs' and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot
         and valid_cap' new_cap
         and K (capBadge new_cap = None)
         and K (slot \<in> cte_refs' (ThreadCap target) 0)
         and K (\<not> isReplyCap new_cap \<and> \<not> isIRQControlCap new_cap)\<rbrace>
     checkCapAt new_cap src_slot
      (checkCapAt (ThreadCap target) slot'
       (assertDerived src_slot new_cap (cteInsert new_cap src_slot slot))) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply o_apply[simp del]
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
  apply (frule capBadgeNone_masters, simp)
  apply (rule conjI)
   apply (rule_tac x=slot' in exI)
   subgoal by (clarsimp simp: isCap_simps)
  apply (clarsimp simp: isCap_simps cteCaps_of_def o_apply)
  apply (erule(1) valid_irq_handlers_ctes_ofD)
  apply (clarsimp simp: invs'_def valid_state'_def)
  done

lemma checkCap_inv:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> checkCapAt cap slot f \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding checkCapAt_def
  by (wp x | simp)+

lemma isValidVTableRootD:
  "isValidVTableRoot cap
     \<Longrightarrow> isArchObjectCap cap \<and> isPML4Cap (capCap cap)
             \<and> capPML4MappedASID (capCap cap) \<noteq> None"
  by (simp add: isValidVTableRoot_def
                X64_H.isValidVTableRoot_def
                isCap_simps
         split: capability.split_asm arch_capability.split_asm
                option.split_asm)

lemma assertDerived_wp:
  "\<lbrace>P and (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) slot cap o cteCap) slot s)\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow>
  \<lbrace>P\<rbrace> assertDerived slot cap f \<lbrace>Q\<rbrace>"
  apply (simp add: assertDerived_def)
  apply wpsimp
  done

lemma setMCPriority_invs':
  "\<lbrace>invs' and tcb_at' t and K (prio \<le> maxPriority)\<rbrace> setMCPriority t prio \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding setMCPriority_def
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  by (wp threadSet_invs_trivial, (clarsimp simp: inQ_def)+)

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
        ThreadControl _ _ _ mcp p _ _ _ \<Rightarrow> valid_option_prio p \<and> valid_option_prio mcp
      | _                           \<Rightarrow> True"

lemma threadcontrol_corres_helper1:
  "\<lbrace>einvs and simple_sched_action\<rbrace>
   thread_set (tcb_ipc_buffer_update f) a
   \<lbrace>\<lambda>_. weak_valid_sched_action and valid_etcbs\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: thread_set_def)
   apply (wp set_object_wp)
  apply (simp | intro impI | elim exE conjE)+
  apply (frule get_tcb_SomeD)
  apply (erule ssubst)
  apply (clarsimp simp add: weak_valid_sched_action_def valid_etcbs_2_def st_tcb_at_kh_def
              get_tcb_def obj_at_kh_def obj_at_def is_etcb_at'_def valid_sched_def valid_sched_action_def)
  apply (erule_tac x=a in allE)+
  apply (clarsimp simp: is_tcb_def)
  done

lemma threadcontrol_corres_helper3:
  "\<lbrace>einvs and simple_sched_action\<rbrace>
   check_cap_at cap p (check_cap_at (cap.ThreadCap cap') slot (cap_insert cap p tcb_slot))
   \<lbrace>\<lambda>_ s. weak_valid_sched_action s \<and> in_correct_ready_q s \<and> ready_qs_distinct s \<and> valid_etcbs s
          \<and> pspace_aligned s \<and> pspace_distinct s\<rbrace>"
   apply (wpsimp
          | strengthen valid_sched_valid_queues valid_queues_in_correct_ready_q
                       valid_sched_weak_strg[rule_format] valid_queues_ready_qs_distinct)+
   apply (wpsimp wp: check_cap_inv)
  apply (fastforce simp: valid_sched_def)
  done

lemma threadcontrol_corres_helper4:
  "isArchObjectCap ac \<Longrightarrow>
   \<lbrace>invs' and cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) (cte_map (a, tcb_cnode_index 4))
    and valid_cap' ac\<rbrace>
   checkCapAt ac (cte_map (ab, ba))
     (checkCapAt (capability.ThreadCap a) (cte_map slot)
        (assertDerived (cte_map (ab, ba)) ac (cteInsert ac (cte_map (ab, ba)) (cte_map (a, tcb_cnode_index 4)))))
   \<lbrace>\<lambda>_ s. sym_heap_sched_pointers s \<and> valid_sched_pointers s \<and> valid_tcbs' s \<and> pspace_aligned' s \<and>
          pspace_distinct' s\<rbrace>"
  apply (wpsimp wp:
         | strengthen invs_sym_heap_sched_pointers invs_valid_sched_pointers
                      invs_valid_objs' valid_objs'_valid_tcbs' invs_pspace_aligned'
                      invs_pspace_distinct')+
  by (case_tac ac;
      clarsimp simp: capBadge_def isCap_simps tcb_cnode_index_def cte_map_def cte_wp_at'_def
                     cte_level_bits_def)

lemma threadSet_invs_trivialT2:
  assumes
    "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
    "\<forall>tcb. tcbState (F tcb) = tcbState tcb"
    "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
    "\<forall>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb"
    "\<forall>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb"
    "\<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb"
    "\<forall>tcb. tcbDomain (F tcb) = tcbDomain tcb"
    "\<forall>tcb. tcbPriority (F tcb) = tcbPriority tcb"
    "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
    "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
    "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  shows
    "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>tcb. is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits)\<rbrace>
     threadSet F t
     \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (rule hoare_gen_asm [where P="\<forall>tcb. is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"])
   apply (wp threadSet_valid_pspace'T
             threadSet_iflive'T
             threadSet_ifunsafe'T
             threadSet_global_refsT
             valid_irq_node_lift
             valid_irq_handlers_lift''
             threadSet_ctes_ofT
             threadSet_valid_dom_schedule'
             untyped_ranges_zero_lift
             sym_heap_sched_pointers_lift threadSet_valid_sched_pointers
             threadSet_tcbSchedPrevs_of threadSet_tcbSchedNexts_of
             threadSet_sch_actT_P[where P=False, simplified]
             threadSet_state_refs_of'T[where f'=id]
             threadSet_idle'T
             threadSet_not_inQ
             threadSet_ct_idle_or_in_cur_domain'
             threadSet_cur
          | clarsimp simp: assms cteCaps_of_def | rule refl)+
  apply (clarsimp simp: o_def)
  by (auto simp: obj_at'_def)

lemma getThreadBufferSlot_dom_tcb_cte_cases:
  "\<lbrace>\<top>\<rbrace> getThreadBufferSlot a \<lbrace>\<lambda>rv s. rv \<in> (+) a ` dom tcb_cte_cases\<rbrace>"
  by (wpsimp simp: tcb_cte_cases_def getThreadBufferSlot_def locateSlot_conv cte_level_bits_def
                   tcbIPCBufferSlot_def)

lemma tcb_at'_cteInsert[wp]:
  "\<lbrace>\<lambda>s. tcb_at' (ksCurThread s) s\<rbrace> cteInsert t x y \<lbrace>\<lambda>_ s. tcb_at' (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps cteInsert_ct, wp, simp)

lemma tcb_at'_threadSet[wp]:
  "\<lbrace>\<lambda>s. tcb_at' (ksCurThread s) s\<rbrace> threadSet (tcbIPCBuffer_update (\<lambda>_. b)) a \<lbrace>\<lambda>_ s. tcb_at' (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps threadSet_tcb', wp, simp)

lemma cteDelete_it [wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> cteDelete slot e \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  by (rule cteDelete_preservation) (wp | clarsimp)+

lemma cteDelete_pspace_aligned'[wp]:
  "cteDelete slot e \<lbrace>pspace_aligned'\<rbrace>"
  by (rule cteDelete_preservation; wpsimp)

lemma cteDelete_pspace_distinct'[wp]:
  "cteDelete slot e \<lbrace>pspace_distinct'\<rbrace>"
  by (rule cteDelete_preservation; wpsimp)

lemmas threadSet_invs_trivial2 =
  threadSet_invs_trivialT2 [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma valid_tcb_ipc_buffer_update:
  "\<And>buf s. is_aligned buf msg_align_bits
   \<Longrightarrow> (\<forall>tcb. valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbIPCBuffer_update (\<lambda>_. buf) tcb) s)"
  by (simp add: valid_tcb'_def tcb_cte_cases_def)

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

lemma assertDerived_wp_weak:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> assertDerived slot cap f \<lbrace>Q\<rbrace>"
  apply (wpsimp simp: assertDerived_def)
  done

lemma thread_set_ipc_weak_valid_sched_action:
  "\<lbrace> einvs and simple_sched_action\<rbrace>
   thread_set (tcb_ipc_buffer_update f) a
   \<lbrace>\<lambda>x. weak_valid_sched_action\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: thread_set_def)
   apply (wp set_object_wp)
  apply (simp | intro impI | elim exE conjE)+
  apply (frule get_tcb_SomeD)
  apply (erule ssubst)
  apply (clarsimp simp add: weak_valid_sched_action_def valid_etcbs_2_def st_tcb_at_kh_def
              get_tcb_def obj_at_kh_def obj_at_def is_etcb_at'_def valid_sched_def valid_sched_action_def)
  done

crunch cap_insert
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: crunch_wps ready_qs_distinct_lift)

crunch cap_delete
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  (ignore_del: preemption_point
   wp: crunch_wps
   simp: crunch_simps OR_choiceE_def
   ignore: wrap_ext_bool OR_choiceE)

crunch option_update_thread
  for aligned[wp]: "pspace_aligned"
  and distinct[wp]: "pspace_distinct"

lemma threadSet_invs_tcbIPCBuffer_update:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>tcb. is_aligned (tcbIPCBuffer (tcbIPCBuffer_update f tcb)) msg_align_bits)\<rbrace>
   threadSet (tcbIPCBuffer_update f) t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wp threadSet_invs_trivialT2; simp add: tcb_cte_cases_def cteSizeBits_def)

lemma transferCaps_corres:
  assumes x: "newroot_rel e e'"
  and y: "newroot_rel f f'"
  and z: "(case g of None \<Rightarrow> g' = None
                   | Some (vptr, g'') \<Rightarrow> \<exists>g'''. g' = Some (vptr, g''')
                          \<and> newroot_rel g'' g''')"
  and u: "{e, f, option_map undefined g} \<noteq> {None} \<longrightarrow> sl' = cte_map slot"
  shows
    "corres (dc \<oplus> (=))
    (einvs and simple_sched_action and tcb_at a and
     (\<lambda>s. {e, f, option_map undefined g} \<noteq> {None} \<longrightarrow> cte_at slot s) and
     case_option \<top> (valid_cap o fst) e and
     case_option \<top> (cte_at o snd) e and
     case_option \<top> (no_cap_to_obj_dr_emp o fst) e and
     K (case_option True (is_cnode_cap o fst) e) and
     case_option \<top> (valid_cap o fst) f and
     case_option \<top> (cte_at o snd) f and
     case_option \<top> (no_cap_to_obj_dr_emp o fst) f and
     K (case_option True (is_valid_vtable_root o fst) f)
      and case_option \<top> (case_option \<top> (cte_at o snd) o snd) g
      and case_option \<top> (case_option \<top> (no_cap_to_obj_dr_emp o fst) o snd) g
      and case_option \<top> (case_option \<top> (valid_cap o fst) o snd) g
      and K (case_option True ((\<lambda>v. is_aligned v msg_align_bits) o fst) g)
      and K (case_option True (\<lambda>v. case_option True ((swp valid_ipc_buffer_cap (fst v)
                                  and is_arch_cap and is_cnode_or_valid_arch) o fst) (snd v)) g)
      and (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at (\<lambda>m. pr \<le> m) auth s) p_auth) \<comment> \<open>only set prio \<le> mcp\<close>
      and (\<lambda>s. case_option True (\<lambda>(mcp, auth). mcpriority_tcb_at (\<lambda>m. mcp \<le> m) auth s) mcp_auth) \<comment> \<open>only set mcp \<le> prev_mcp\<close>)
    (invs' and sch_act_simple and case_option \<top> (valid_cap' o fst) e' and
     (\<lambda>s. {e', f', option_map undefined g'} \<noteq> {None} \<longrightarrow> cte_at' (cte_map slot) s) and
     K (case_option True (isCNodeCap o fst) e') and
     case_option \<top> (valid_cap' o fst) f' and
     K (case_option True (isValidVTableRoot o fst) f') and
     K (case_option True ((\<lambda>v. is_aligned v msg_align_bits) o fst) g') and
     K (case_option True (case_option True (isArchObjectCap o fst) o snd) g') and
     case_option \<top> (case_option \<top> (valid_cap' o fst) o snd) g' and
     tcb_at' a and ex_nonz_cap_to' a and K (valid_option_prio p_auth \<and> valid_option_prio mcp_auth) and
     (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at' ((\<le>) pr) auth s) p_auth) and
     (\<lambda>s. case_option True (\<lambda>(m, auth). mcpriority_tcb_at' ((\<le>) m) auth s) mcp_auth))
    (invoke_tcb (tcb_invocation.ThreadControl a slot (option_map to_bl b') mcp_auth p_auth e f g))
    (invokeTCB (tcbinvocation.ThreadControl a sl' b' mcp_auth p_auth e' f' g'))"
proof -
  have P: "\<And>t v. corres dc
               (tcb_at t and pspace_aligned and pspace_distinct)
               \<top>
               (option_update_thread t (tcb_fault_handler_update o (%x _. x))
               (option_map to_bl v))
               (case v of None \<Rightarrow> return ()
                 | Some x \<Rightarrow> threadSet (tcbFaultHandler_update (%_. x)) t)"
    apply (rule out_corres, simp_all add: exst_same_def)
    apply (case_tac v, simp_all add: out_rel_def)
    apply (safe, case_tac tcb', simp add: tcb_relation_def split: option.split)
    done
  have R: "\<And>t v. corres dc
               (tcb_at t and pspace_aligned and pspace_distinct)
               \<top>
               (option_update_thread t (tcb_ipc_buffer_update o (%x _. x)) v)
               (case v of None \<Rightarrow> return ()
                 | Some x \<Rightarrow> threadSet (tcbIPCBuffer_update (%_. x)) t)"
    apply (rule out_corres, simp_all add: exst_same_def)
    apply (case_tac v, simp_all add: out_rel_def)
    apply (safe, case_tac tcb', simp add: tcb_relation_def)
    done
  have S: "\<And>t x. corres dc (einvs and tcb_at t) (invs' and tcb_at' t and valid_objs' and K (valid_option_prio p_auth))
                   (case_option (return ()) (\<lambda>(p, auth). set_priority t p) p_auth)
                   (case_option (return ()) (\<lambda>p'. setPriority t (fst p')) p_auth)"
    apply (case_tac p_auth; clarsimp simp: setPriority_corres)
    done
  have S': "\<And>t x. corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                    (case_option (return ()) (\<lambda>(mcp, auth). set_mcpriority t mcp) mcp_auth)
                    (case_option (return ()) (\<lambda>mcp'. setMCPriority t (fst mcp')) mcp_auth)"
    apply(case_tac mcp_auth; clarsimp simp: setMCPriority_corres)
    done
  have T: "\<And>x x' ref getfn target.
     \<lbrakk> newroot_rel x x'; getfn = return (cte_map (target, ref));
            x \<noteq> None \<longrightarrow> {e, f, option_map undefined g} \<noteq> {None} \<rbrakk> \<Longrightarrow>
     corres (dc \<oplus> dc)

            (einvs and simple_sched_action and cte_at (target, ref) and emptyable (target, ref) and
             (\<lambda>s. \<forall>(sl, c) \<in> (case x of None \<Rightarrow> {} | Some (c, sl) \<Rightarrow> {(sl, c), (slot, c)}).
                       cte_at sl s \<and> no_cap_to_obj_dr_emp c s \<and> valid_cap c s)
             and K (case x of None \<Rightarrow> True
                      | Some (c, sl) \<Rightarrow> is_cnode_or_valid_arch c))
            (invs' and sch_act_simple and cte_at' (cte_map (target, ref)) and
             (\<lambda>s. \<forall>cp \<in> (case x' of None \<Rightarrow> {} | Some (c, sl) \<Rightarrow> {c}). s \<turnstile>' cp))
         (case x of None \<Rightarrow> returnOk ()
          | Some pr \<Rightarrow> case_prod (\<lambda>new_cap src_slot.
              doE cap_delete (target, ref);
                  liftE $ check_cap_at new_cap src_slot $
                          check_cap_at (cap.ThreadCap target) slot $
                          cap_insert new_cap src_slot (target, ref)
              odE) pr)
         (case x' of
             None \<Rightarrow> returnOk ()
             | Some pr \<Rightarrow> (\<lambda>(newCap, srcSlot).
                 do slot \<leftarrow> getfn;
                    doE uu \<leftarrow> cteDelete slot True;
                        liftE (checkCapAt newCap srcSlot
                              (checkCapAt (capability.ThreadCap target) sl'
                              (assertDerived srcSlot newCap (cteInsert newCap srcSlot slot))))
                    odE
                 od) pr)"
    apply (case_tac "x = None")
     apply (simp add: newroot_rel_def returnOk_def)
    apply (drule(1) mp, drule mp [OF u])
    apply (clarsimp simp add: newroot_rel_def returnOk_def split_def)
    apply (rule corres_gen_asm)
    apply (rule corres_guard_imp)
      apply (rule corres_split_norE[OF cteDelete_corres])
        apply (simp del: dc_simp)
        apply (erule checkCapAt_cteInsert_corres)
       apply (fold validE_R_def)
       apply (wp cap_delete_deletes cap_delete_cte_at cap_delete_valid_cap
                    | strengthen use_no_cap_to_obj_asid_strg)+
      apply (wp cteDelete_invs' cteDelete_deletes)
     apply (clarsimp dest!: is_cnode_or_valid_arch_cap_asid)
    apply clarsimp
    done
  have U2: "getThreadBufferSlot a = return (cte_map (a, tcb_cnode_index 4))"
    by (simp add: getThreadBufferSlot_def locateSlot_conv
                  cte_map_def tcb_cnode_index_def tcbIPCBufferSlot_def
                  cte_level_bits_def)
  have T2: "corres (dc \<oplus> dc)
     (einvs and simple_sched_action and tcb_at a and
         (\<lambda>s. \<forall>(sl, c) \<in> (case g of None \<Rightarrow> {} | Some (x, v) \<Rightarrow> {(slot, cap.NullCap)} \<union>
             (case v of None \<Rightarrow> {} | Some (c, sl) \<Rightarrow> {(sl, c), (slot, c)})).
                   cte_at sl s \<and> no_cap_to_obj_dr_emp c s \<and> valid_cap c s)
         and K (case g of None \<Rightarrow> True | Some (x, v) \<Rightarrow> (case v of
                   None \<Rightarrow> True | Some (c, sl) \<Rightarrow> is_cnode_or_valid_arch c
                                                 \<and> is_arch_cap c
                                                 \<and> valid_ipc_buffer_cap c x
                                                 \<and> is_aligned x msg_align_bits)))
     (invs' and sch_act_simple and tcb_at' a and
       (\<lambda>s. \<forall>cp \<in> (case g' of None \<Rightarrow> {} | Some (x, v) \<Rightarrow> (case v of
                              None \<Rightarrow> {} | Some (c, sl) \<Rightarrow> {c})). s \<turnstile>' cp) and
        K (case g' of None \<Rightarrow> True | Some (x, v) \<Rightarrow> is_aligned x msg_align_bits
        \<and> (case v of None \<Rightarrow> True | Some (ac, _) \<Rightarrow> isArchObjectCap ac)) )
     (case_option (returnOk ())
       (case_prod
         (\<lambda>ptr frame.
             doE cap_delete (a, tcb_cnode_index 4);
                 do y \<leftarrow> thread_set (tcb_ipc_buffer_update (\<lambda>_. ptr)) a;
                   y \<leftarrow> case_option (return ())
                   (case_prod
                      (\<lambda>new_cap src_slot.
                          check_cap_at new_cap src_slot $
                          check_cap_at (cap.ThreadCap a) slot $
                          cap_insert new_cap src_slot (a, tcb_cnode_index 4)))
                        frame;
                    cur \<leftarrow> gets cur_thread;
                    liftE $ when (cur = a) (reschedule_required)
                 od
             odE))
       g)
     (case_option (returnOk ())
        (\<lambda>(ptr, frame).
            do bufferSlot \<leftarrow> getThreadBufferSlot a;
            doE y \<leftarrow> cteDelete bufferSlot True;
            do y \<leftarrow> threadSet (tcbIPCBuffer_update (\<lambda>_. ptr)) a;
               y \<leftarrow> (case_option (return ())
                      (case_prod
                        (\<lambda>newCap srcSlot.
                            checkCapAt newCap srcSlot $
                            checkCapAt
                             (capability.ThreadCap a)
                             sl' $
                            assertDerived srcSlot newCap $
                            cteInsert newCap srcSlot bufferSlot))
                         frame);
               cur \<leftarrow> getCurThread;
               liftE $ when (cur = a) rescheduleRequired
            od odE od)
        g')" (is "corres _ ?T2_pre ?T2_pre' _ _")
    using z u
    apply -
    apply (rule corres_guard_imp[where P=P and P'=P'
                                  and Q="P and cte_at (a, tcb_cnode_index 4)"
                                  and Q'="P' and cte_at' (cte_map (a, cap))" for P P' a cap])
      apply (cases g)
       apply (simp, simp add: returnOk_def)
      apply (clarsimp simp: liftME_def[symmetric] U2 liftE_bindE)
      apply (case_tac b, simp_all add: newroot_rel_def)
       apply (rule corres_guard_imp)
         apply (rule corres_split_norE)
            apply (rule cteDelete_corres)
           apply (rule_tac F="is_aligned aa msg_align_bits" in corres_gen_asm2)
           apply (rule corres_split_nor)
              apply (rule threadset_corres,
                      (simp add: tcb_relation_def), (simp add: exst_same_def)+)[1]
             apply (rule corres_split[OF getCurThread_corres], clarsimp)
               apply (rule corres_when[OF refl rescheduleRequired_corres])
              apply (wpsimp wp: gct_wp)+
            apply (strengthen valid_queues_ready_qs_distinct)
            apply (wpsimp wp: thread_set_ipc_weak_valid_sched_action thread_set_valid_queues
                              hoare_drop_imp)
           apply clarsimp
           apply (strengthen valid_objs'_valid_tcbs' invs_valid_objs')+
           apply (wpsimp wp: threadSet_sched_pointers threadSet_valid_sched_pointers hoare_drop_imp
                             threadSet_invs_tcbIPCBuffer_update)
          apply (clarsimp simp: pred_conj_def)
          apply (strengthen einvs_valid_etcbs valid_queues_in_correct_ready_q
                            valid_sched_valid_queues)+
          apply wp
         apply (clarsimp simp: pred_conj_def)
         apply (strengthen invs_sym_heap_sched_pointers invs_valid_sched_pointers
                           valid_objs'_valid_tcbs' invs_valid_objs')
         apply (wpsimp wp: cteDelete_invs' hoare_vcg_conj_lift)
        apply (fastforce simp: emptyable_def)
       apply fastforce
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule corres_split_norE[OF cteDelete_corres])
          apply (rule_tac F="is_aligned aa msg_align_bits"
                        in corres_gen_asm)
          apply (rule_tac F="isArchObjectCap ac" in corres_gen_asm2)
          apply (rule corres_split_nor)
             apply (rule threadset_corres,
                    simp add: tcb_relation_def, (simp add: exst_same_def)+)
            apply (rule corres_split)
               apply (erule checkCapAt_cteInsert_corres)
              apply (rule corres_split[OF getCurThread_corres], clarsimp)
                apply (rule corres_when[OF refl rescheduleRequired_corres])
               apply (wp gct_wp)+
             apply (wp hoare_drop_imp)
             apply (wp hoare_drop_imp threadcontrol_corres_helper3)[1]
            apply (wp hoare_drop_imp threadcontrol_corres_helper4)[1]
           apply (wp thread_set_tcb_ipc_buffer_cap_cleared_invs ready_qs_distinct_lift
                     thread_set_cte_wp_at_trivial thread_set_not_state_valid_sched
                       | simp add: ran_tcb_cap_cases)+
          apply (wp threadSet_invs_trivial
                    threadSet_cte_wp_at' | simp)+
         apply (wp cap_delete_deletes cap_delete_cte_at
                   cap_delete_valid_cap cteDelete_deletes
                   cteDelete_invs'
                   | strengthen use_no_cap_to_obj_asid_strg
                   | clarsimp simp: inQ_def)+
       apply (clarsimp simp: cte_wp_at_caps_of_state
                      dest!: is_cnode_or_valid_arch_cap_asid)
       apply (fastforce simp: emptyable_def)
      apply (clarsimp simp: inQ_def)
     apply (clarsimp simp: obj_at_def is_tcb)
     apply (rule cte_wp_at_tcbI, simp, fastforce, simp)
    apply (clarsimp simp: cte_map_def tcb_cnode_index_def obj_at'_def objBits_simps projectKOs)
    apply (erule(2) cte_wp_at_tcbI', fastforce simp: objBits_defs cte_level_bits_def, simp)
    done
  have U: "getThreadCSpaceRoot a = return (cte_map (a, tcb_cnode_index 0))"
    apply (clarsimp simp add: getThreadCSpaceRoot)
    apply (simp add: cte_map_def tcb_cnode_index_def
                     cte_level_bits_def word_bits_def)
    done
  have V: "getThreadVSpaceRoot a = return (cte_map (a, tcb_cnode_index 1))"
    apply (clarsimp simp add: getThreadVSpaceRoot)
    apply (simp add: cte_map_def tcb_cnode_index_def to_bl_1 objBits_defs
                     cte_level_bits_def word_bits_def)
    done
  have X: "\<And>x P Q R M. (\<And>y. x = Some y \<Longrightarrow> \<lbrace>P y\<rbrace> M y \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>)
               \<Longrightarrow> \<lbrace>case_option (Q ()) P x\<rbrace> case_option (returnOk ()) M x \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
    by (case_tac x, simp_all, wp)
  have Y: "\<And>x P Q M. (\<And>y. x = Some y \<Longrightarrow> \<lbrace>P y\<rbrace> M y \<lbrace>Q\<rbrace>,-)
               \<Longrightarrow> \<lbrace>case_option (Q ()) P x\<rbrace> case_option (returnOk ()) M x \<lbrace>Q\<rbrace>,-"
    by (case_tac x, simp_all, wp)
  have Z: "\<And>P f R Q x. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q and R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. case_option Q (\<lambda>y. R) x\<rbrace>"
    apply (rule hoare_post_imp)
     defer
     apply assumption
    apply (case_tac x, simp_all)
    done
  have A: "\<And>x P Q M. (\<And>y. x = Some y \<Longrightarrow> \<lbrace>P y\<rbrace> M y \<lbrace>Q\<rbrace>)
               \<Longrightarrow> \<lbrace>case_option (Q ()) P x\<rbrace> case_option (return ()) M x \<lbrace>Q\<rbrace>"
    by (case_tac x, simp_all, wp)
  have B: "\<And>t v. \<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbFaultHandler_update v) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
    by (wp threadSet_invs_trivial | clarsimp simp: inQ_def)+
  note stuff = Z B out_invs_trivial hoare_case_option_wp
    hoare_vcg_const_Ball_lift hoare_vcg_const_Ball_liftE_R
    cap_delete_deletes cap_delete_valid_cap out_valid_objs
    cap_insert_objs
    cteDelete_deletes cteDelete_sch_act_simple
    out_valid_cap out_cte_at out_tcb_valid out_emptyable
    CSpaceInv_AI.cap_insert_valid_cap cap_insert_cte_at cap_delete_cte_at
    cap_delete_tcb cteDelete_invs' checkCap_inv [where P="valid_cap' c0" for c0]
    check_cap_inv[where P="tcb_at p0" for p0] checkCap_inv [where P="tcb_at' p0" for p0]
    check_cap_inv[where P="cte_at p0" for p0] checkCap_inv [where P="cte_at' p0" for p0]
    check_cap_inv[where P="valid_cap c" for c] checkCap_inv [where P="valid_cap' c" for c]
    check_cap_inv[where P="tcb_cap_valid c p1" for c p1]
    check_cap_inv[where P=valid_sched]
    check_cap_inv[where P=simple_sched_action]
    checkCap_inv [where P=sch_act_simple]
    out_no_cap_to_trivial [OF ball_tcb_cap_casesI]
    checked_insert_no_cap_to
  note if_cong [cong] option.case_cong [cong]
  \<comment> \<open>This proof is quite fragile and was written when bind_wp was added to the wp set later
     in the theory dependencies, and so was matched with before alternatives. We re-add it here to
     create a similar environment and avoid needing to rework the proof.\<close>
  note bind_wp[wp]
  show ?thesis
    apply (simp add: invokeTCB_def liftE_bindE)
    apply (simp only: eq_commute[where a= "a"])
    apply (rule corres_guard_imp)
      apply (rule corres_split_nor[OF P])
        apply (rule corres_split_nor[OF S', simplified])
          apply (rule corres_split_norE[OF T [OF x U], simplified])
            apply (rule corres_split_norE[OF T [OF y V], simplified])
              apply (rule corres_split_norE)
                 apply (rule T2[simplified])
                apply (rule corres_split_nor[OF S, simplified])
                  apply (rule corres_returnOkTT, simp)
                 apply wp
                apply wp
               apply (wpsimp wp: hoare_vcg_const_imp_liftE_R hoare_vcg_const_imp_lift
                                 hoare_vcg_all_liftE_R hoare_vcg_all_lift
                                 as_user_invs thread_set_ipc_tcb_cap_valid
                                 thread_set_tcb_ipc_buffer_cap_cleared_invs
                                 thread_set_cte_wp_at_trivial
                                 thread_set_valid_cap
                                 reschedule_preserves_valid_sched
                                 check_cap_inv[where P=valid_sched] (* from stuff *)
                                 check_cap_inv[where P="tcb_at p0" for p0]
                                 thread_set_not_state_valid_sched
                                 check_cap_inv[where P=simple_sched_action]
                                 cap_delete_deletes hoare_drop_imps
                                 cap_delete_valid_cap
                           simp: ran_tcb_cap_cases
                      | strengthen simple_sched_action_sched_act_not)+
                apply (strengthen use_no_cap_to_obj_asid_strg)
                apply (wpsimp wp: cap_delete_cte_at cap_delete_valid_cap)
               apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_drop_imps hoare_vcg_all_lift
                                 threadSet_invs_tcbIPCBuffer_update threadSet_cte_wp_at'
                      | strengthen simple_sched_action_sched_act_not)+
                apply ((wpsimp wp: stuff hoare_vcg_all_liftE_R hoare_vcg_all_lift
                                   hoare_vcg_const_imp_liftE_R hoare_vcg_const_imp_lift
                                   threadSet_valid_objs' thread_set_not_state_valid_sched
                                   thread_set_tcb_ipc_buffer_cap_cleared_invs thread_set_cte_wp_at_trivial
                                   thread_set_no_cap_to_trivial getThreadBufferSlot_dom_tcb_cte_cases
                                   assertDerived_wp_weak threadSet_cap_to' out_pred_tcb_at_preserved
                                   checkCap_wp assertDerived_wp_weak cap_insert_objs'
                        | simp add: ran_tcb_cap_cases split_def U V
                                  emptyable_def
                        | strengthen tcb_cap_always_valid_strg
                                   tcb_at_invs
                                   use_no_cap_to_obj_asid_strg
                        | (erule exE, clarsimp simp: word_bits_def) | wp (once) hoare_drop_imps)+)
                apply (strengthen valid_tcb_ipc_buffer_update)
                apply (strengthen invs_valid_objs' invs_pspace_aligned' invs_pspace_distinct')
                apply (wpsimp wp: cteDelete_invs' hoare_vcg_imp_lift' hoare_vcg_all_lift)
               apply wpsimp
              apply wpsimp
             apply (clarsimp cong: imp_cong conj_cong simp: emptyable_def)
             apply (rule_tac Q'="\<lambda>_. ?T2_pre" in hoare_strengthen_postE_R[simplified validE_R_def, rotated])
              (* beginning to deal with is_nondevice_page_cap *)
              apply (clarsimp simp: emptyable_def is_nondevice_page_cap_simps is_cap_simps
                                    is_cnode_or_valid_arch_def obj_ref_none_no_asid cap_asid_def
                              cong: conj_cong imp_cong
                             split: option.split_asm)
              (* newly added proof scripts for dealing with is_nondevice_page_cap *)
              apply (simp add: case_bool_If valid_ipc_buffer_cap_def is_nondevice_page_cap_arch_def
                        split: arch_cap.splits if_splits)
             (* is_nondevice_page_cap discharged *)
             apply ((wp stuff checkCap_wp assertDerived_wp_weak cap_insert_objs'
                     | simp add: ran_tcb_cap_cases split_def U V emptyable_def
                     | wpc | strengthen tcb_cap_always_valid_strg use_no_cap_to_obj_asid_strg)+)[1]
            apply (clarsimp cong: imp_cong conj_cong)
            apply (rule_tac Q'="\<lambda>_. ?T2_pre' and (\<lambda>s. valid_option_prio p_auth)"
                         in hoare_strengthen_postE_R[simplified validE_R_def, rotated])
             apply (case_tac g'; clarsimp simp: isCap_simps ; clarsimp elim: invs_valid_objs' cong:imp_cong)
            apply (wp add: stuff hoare_vcg_all_liftE_R hoare_vcg_all_lift
                                 hoare_vcg_const_imp_liftE_R hoare_vcg_const_imp_lift setMCPriority_invs'
                                 threadSet_valid_objs' thread_set_not_state_valid_sched setP_invs'
                                 typ_at_lifts [OF setPriority_typ_at']
                                 typ_at_lifts [OF setMCPriority_typ_at']
                                 threadSet_cap_to' out_pred_tcb_at_preserved assertDerived_wp
                      del: cteInsert_invs
                   | simp add: ran_tcb_cap_cases split_def U V
                               emptyable_def
                   | wpc | strengthen tcb_cap_always_valid_strg
                                      use_no_cap_to_obj_asid_strg
                   | wp add: sch_act_simple_lift hoare_drop_imps del: cteInsert_invs
                   | (erule exE, clarsimp simp: word_bits_def))+
     (* the last two subgoals *)
     apply (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified] tcb_at_st_tcb_at[symmetric]
                           tcb_cap_valid_def is_cnode_or_valid_arch_def invs_valid_objs emptyable_def
                           obj_ref_none_no_asid no_cap_to_obj_with_diff_ref_Null is_valid_vtable_root_def
                           is_cap_simps cap_asid_def vs_cap_ref_def arch_cap_fun_lift_def
                           invs_psp_aligned invs_distinct
                     cong: conj_cong imp_cong
                    split: option.split_asm)
    by (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def objBits_defs
                       cte_map_tcb_0 cte_map_tcb_1[simplified] tcb_at_cte_at' cte_at_tcb_at_32'
                       isCap_simps domIff valid_tcb'_def tcb_cte_cases_def
                split: option.split_asm
                dest!: isValidVTableRootD)
qed

lemmas threadSet_ipcbuffer_trivial
    = threadSet_invs_trivial[where F="tcbIPCBuffer_update F'" for F',
                              simplified inQ_def, simplified]

crunch setPriority, setMCPriority
  for cap_to'[wp]: "ex_nonz_cap_to' a"
  (simp: crunch_simps)

lemma cteInsert_sa_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> cteInsert newCap srcSlot destSlot \<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def, wp)

lemma isReplyCapD:
  "isReplyCap cap \<Longrightarrow> \<exists>ptr master grant. cap = capability.ReplyCap ptr master grant"
  by (simp add: isCap_simps)

lemma tc_invs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' a and ex_nonz_cap_to' a and
    K (valid_option_prio d \<and> valid_option_prio mcp) and
    case_option \<top> (valid_cap' o fst) e' and
    K (case_option True (isCNodeCap o fst) e') and
    case_option \<top> (valid_cap' o fst) f' and
    K (case_option True (isValidVTableRoot o fst) f') and
    case_option \<top> (valid_cap') (case_option None (case_option None (Some o fst) o snd) g) and
    K (case_option True isArchObjectCap (case_option None (case_option None (Some o fst) o snd) g))
    and K (case_option True (swp is_aligned msg_align_bits o fst) g) \<rbrace>
      invokeTCB (tcbinvocation.ThreadControl a sl b' mcp d e' f' g)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: split_def invokeTCB_def getThreadCSpaceRoot getThreadVSpaceRoot
                   getThreadBufferSlot_def locateSlot_conv
             cong: option.case_cong)
  apply (simp only: eq_commute[where a="a"])
  apply (rule hoare_walk_assmsE)
    apply (clarsimp simp: pred_conj_def option.splits [where P="\<lambda>x. x s" for s])
    apply ((wp case_option_wp threadSet_invs_trivial hoare_weak_lift_imp
               hoare_vcg_all_lift threadSet_cap_to' | clarsimp simp: inQ_def)+)[2]
  apply (rule hoare_walk_assmsE)
    apply (clarsimp simp: pred_conj_def option.splits [where P="\<lambda>x. x s" for s])
    apply ((wp case_option_wp threadSet_invs_trivial hoare_weak_lift_imp setMCPriority_invs'
               typ_at_lifts[OF setMCPriority_typ_at']
               hoare_vcg_all_lift threadSet_cap_to' | clarsimp simp: inQ_def)+)[2]
  apply (wp add: setP_invs' hoare_weak_lift_imp hoare_vcg_all_lift)+
      apply (rule case_option_wp_None_return[OF setP_invs'[simplified pred_conj_assoc]])
      apply clarsimp
      apply wpfix
      apply assumption
     apply (rule case_option_wp_None_returnOk)
      apply (wpsimp wp: hoare_weak_lift_imp hoare_vcg_all_lift
                        checkCap_inv[where P="tcb_at' t" for t] assertDerived_wp_weak
                        threadSet_invs_trivial2 threadSet_tcb'  hoare_vcg_all_lift threadSet_cte_wp_at')+
       apply (wpsimp wp: hoare_weak_lift_impE_R cteDelete_deletes
                         hoare_vcg_all_liftE_R hoare_vcg_conj_liftE1 hoare_vcg_const_imp_liftE_R hoare_vcg_propE_R
                         cteDelete_invs' cteDelete_invs' cteDelete_typ_at'_lifts)+
     apply (assumption | clarsimp cong: conj_cong imp_cong | (rule case_option_wp_None_returnOk)
            | wpsimp wp: hoare_weak_lift_imp hoare_vcg_all_lift checkCap_inv[where P="tcb_at' t" for t] assertDerived_wp_weak
                         hoare_vcg_imp_lift' hoare_vcg_all_lift checkCap_inv[where P="tcb_at' t" for t]
                         checkCap_inv[where P="valid_cap' c" for c] checkCap_inv[where P=sch_act_simple]
                         hoare_vcg_const_imp_liftE_R assertDerived_wp_weak hoare_weak_lift_impE_R cteDelete_deletes
                         hoare_vcg_all_liftE_R hoare_vcg_conj_liftE1 hoare_vcg_const_imp_liftE_R hoare_vcg_propE_R
                         cteDelete_invs' cteDelete_typ_at'_lifts cteDelete_sch_act_simple)+
  apply (clarsimp simp: tcb_cte_cases_def cte_level_bits_def objBits_defs tcbIPCBufferSlot_def)
  by (auto dest!: isCapDs isReplyCapD isValidVTableRootD simp: isCap_simps)

lemma setSchedulerAction_invs'[wp]:
  "\<lbrace>invs' and sch_act_wf sa
          and (\<lambda>s. sa = ResumeCurrentThread
                     \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s)
          and (\<lambda>s. sa = ResumeCurrentThread
          \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s)\<rbrace>
    setSchedulerAction sa
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setSchedulerAction_def)
  apply wp
  apply (clarsimp simp add: invs'_def valid_state'_def valid_irq_node'_def
                valid_queues_def bitmapQ_defs cur_tcb'_def
                ct_not_inQ_def)
  apply (simp add: ct_idle_or_in_cur_domain'_def)
  done

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
| "tcbinv_relation (tcb_invocation.ThreadControl a sl flt_ep mcp prio croot vroot buf) x
    = (\<exists>flt_ep' croot' vroot' sl' buf'. flt_ep = option_map to_bl flt_ep' \<and>
                        newroot_rel croot croot' \<and> newroot_rel vroot vroot' \<and>
                        ({croot, vroot, option_map undefined buf} \<noteq> {None}
                           \<longrightarrow> sl' = cte_map sl) \<and>
                        (case buf of None \<Rightarrow> buf' = None
                          | Some (vptr, g'') \<Rightarrow> \<exists>g'''. buf' = Some (vptr, g''')
                               \<and> newroot_rel g'' g''') \<and>
       x = tcbinvocation.ThreadControl a sl' flt_ep' mcp prio croot' vroot' buf')"
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
| "tcb_inv_wf' (tcbinvocation.ThreadControl t sl fe mcp p croot vroot buf)
             = (tcb_at' t and ex_nonz_cap_to' t and
               K (valid_option_prio p \<and> valid_option_prio mcp) and
               case_option \<top> (valid_cap' o fst) croot and
               K (case_option True (isCNodeCap o fst) croot) and
               case_option \<top> (valid_cap' o fst) vroot and
               K (case_option True (isValidVTableRoot o fst) vroot) and
               case_option \<top> (case_option \<top> (valid_cap' o fst) o snd) buf and
               case_option \<top> (case_option \<top> (cte_at' o snd) o snd) buf and
               K (case_option True (swp is_aligned msg_align_bits o fst) buf) and
               K (case_option True (case_option True (isArchObjectCap o fst) o snd) buf) and
               (\<lambda>s. {croot, vroot, option_map undefined buf} \<noteq> {None}
                     \<longrightarrow> cte_at' sl s) and
               (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at' ((\<le>) pr) auth s) p) and
               (\<lambda>s. case_option True (\<lambda>(m, auth). mcpriority_tcb_at' ((\<le>) m) auth s) mcp))"
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

lemma invokeTCB_corres:
 "tcbinv_relation ti ti' \<Longrightarrow>
  corres (dc \<oplus> (=))
         (einvs and simple_sched_action and Tcb_AI.tcb_inv_wf ti)
         (invs' and sch_act_simple and tcb_inv_wf' ti')
         (invoke_tcb ti) (invokeTCB ti')"
  apply (case_tac ti, simp_all only: tcbinv_relation.simps valid_tcb_invocation_def)
         apply (rule corres_guard_imp [OF invokeTCB_WriteRegisters_corres], simp+)[1]
        apply (rule corres_guard_imp [OF invokeTCB_ReadRegisters_corres], simp+)[1]
       apply (rule corres_guard_imp [OF invokeTCB_CopyRegisters_corres], simp+)[1]
      apply (clarsimp simp del: invoke_tcb.simps)
      apply (rename_tac word one t2 mcp t3 t4 t5 t6 t7 t8 t9 t10 t11)
      apply (rule_tac F="is_aligned word 5" in corres_req)
       apply (clarsimp simp add: is_aligned_weaken [OF tcb_aligned])
      apply (rule corres_guard_imp [OF transferCaps_corres], clarsimp+)
       apply (clarsimp simp: is_cnode_or_valid_arch_def
                      split: option.split option.split_asm)
      apply clarsimp
      apply (auto split: option.split_asm simp: newroot_rel_def)[1]
     apply (simp add: invokeTCB_def liftM_def[symmetric]
                      o_def dc_def[symmetric])
     apply (rule corres_guard_imp [OF suspend_corres], simp+)
    apply (simp add: invokeTCB_def liftM_def[symmetric]
                     o_def dc_def[symmetric])
    apply (rule corres_guard_imp [OF restart_corres], simp+)
   apply (simp add:invokeTCB_def)
   apply (rename_tac option)
   apply (case_tac option)
    apply simp
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF unbindNotification_corres])
        apply (rule corres_trivial, simp)
       apply wp+
     apply (clarsimp)
    apply clarsimp
   apply simp
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF bindNotification_corres])
       apply (rule corres_trivial, simp)
      apply wp+
    apply clarsimp
    apply (clarsimp simp: obj_at_def is_ntfn)
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (simp add: invokeTCB_def tlsBaseRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF TcbAcc_R.asUser_setRegister_corres])
      apply (rule corres_split[OF Bits_R.getCurThread_corres])
        apply (rule corres_split[OF Corres_UL.corres_when])
            apply simp
           apply (rule TcbAcc_R.rescheduleRequired_corres)
          apply (rule corres_trivial, simp)
         apply (wpsimp wp: hoare_drop_imp)+
   apply (fastforce dest: valid_sched_valid_queues simp: valid_sched_weak_strg einvs_valid_etcbs)
  apply fastforce
  done

lemma tcbBoundNotification_caps_safe[simp]:
  "\<forall>(getF, setF)\<in>ran tcb_cte_cases.
     getF (tcbBoundNotification_update (\<lambda>_. Some ntfnptr) tcb) = getF tcb"
  by (case_tac tcb, simp add: tcb_cte_cases_def)

lemma valid_bound_ntfn_lift:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_bound_ntfn' a s\<rbrace> f \<lbrace>\<lambda>rv s. valid_bound_ntfn' a s\<rbrace>"
  apply (simp add: valid_bound_ntfn'_def, case_tac a, simp_all)
  apply (wp typ_at_lifts[OF P])+
  done

crunch setBoundNotification
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (ignore: threadSet wp: threadSet_sched_pointers)

lemma bindNotification_invs':
  "\<lbrace>bound_tcb_at' ((=) None) tcbptr
       and ex_nonz_cap_to' ntfnptr
       and ex_nonz_cap_to' tcbptr
       and obj_at' (\<lambda>ntfn. ntfnBoundTCB ntfn = None \<and> (\<forall>q. ntfnObj ntfn \<noteq> WaitingNtfn q)) ntfnptr
       and invs'\<rbrace>
    bindNotification tcbptr ntfnptr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  including no_pre
  apply (simp add: bindNotification_def invs'_def valid_state'_def)
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wp set_ntfn_valid_pspace' sbn_sch_act' valid_irq_node_lift
             setBoundNotification_ct_not_inQ valid_bound_ntfn_lift
             untyped_ranges_zero_lift
          | clarsimp dest!: global'_no_ex_cap simp: cteCaps_of_def)+
  apply (clarsimp simp: valid_pspace'_def)
  apply (cases "tcbptr = ntfnptr")
   apply (clarsimp dest!: pred_tcb_at' simp: obj_at'_def projectKOs)
  apply (clarsimp simp: pred_tcb_at' conj_comms o_def)
  apply (subst delta_sym_refs, assumption)
    apply (fastforce simp: ntfn_q_refs_of'_def obj_at'_def projectKOs
                    dest!: symreftype_inverse'
                    split: ntfn.splits if_split_asm)
   apply (clarsimp split: if_split_asm)
    apply (fastforce simp: tcb_st_refs_of'_def
                    dest!: bound_tcb_at_state_refs_ofD'
                    split: if_split_asm thread_state.splits)
   apply (fastforce simp: obj_at'_def projectKOs state_refs_of'_def
                   dest!: symreftype_inverse')
  apply (clarsimp simp: valid_pspace'_def)
  apply (frule_tac P="\<lambda>k. k=ntfn" in obj_at_valid_objs', simp)
  apply (clarsimp simp: valid_obj'_def projectKOs valid_ntfn'_def obj_at'_def
                    dest!: pred_tcb_at'
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
  "\<lbrace>invs' and sch_act_simple and ct_in_state' runnable' and tcb_inv_wf' ti\<rbrace>
     invokeTCB ti
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (case_tac ti, simp_all only:)
         apply (simp add: invokeTCB_def)
         apply wp
         apply (clarsimp simp: invs'_def valid_state'_def
                         dest!: global'_no_ex_cap)
        apply (simp add: invokeTCB_def)
        apply (wp restart_invs')
        apply (clarsimp simp: invs'_def valid_state'_def
                        dest!: global'_no_ex_cap)
       apply (wp tc_invs')
       apply (clarsimp split: option.split dest!: isCapDs)
      apply (wp writereg_invs' readreg_invs' copyreg_invs' tcbntfn_invs'
             | simp)+
  done

declare assertDerived_wp [wp]

lemma copyregsets_map_only[simp]:
  "copyregsets_map v = X64NoExtraRegisters"
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
  apply (simp add: word_less_nat_alt unat_of_nat64)
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
  "((ucast (x :: 8 word) :: machine_word) = ucast y) = (x = y)"
  apply safe
  apply (drule_tac f="ucast :: (machine_word \<Rightarrow> 8 word)" in arg_cong)
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
       (cur_tcb and valid_etcbs and
        (pspace_aligned and pspace_distinct and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x)))
       (invs' and (\<lambda>s. \<forall>x \<in> set extras'. s \<turnstile>' fst x))
       (decode_set_priority args cap slot extras)
       (decodeSetPriority args cap' extras')"
  apply (cases args; cases extras; cases extras';
         clarsimp simp: decode_set_priority_def decodeSetPriority_def)
  apply (rename_tac auth_cap auth_slot auth_path rest auth_cap' rest')
  apply (rule corres_split_eqrE)
     apply corresKsimp
    apply (rule corres_splitEE[OF checkPrio_corres])
      apply (rule corres_returnOkTT)
      apply (clarsimp simp: newroot_rel_def elim!: is_thread_cap.elims(2))
     apply (wpsimp simp: valid_cap_def valid_cap'_def)+
  done

lemma decodeSetMCPriority_corres:
  "\<lbrakk> cap_relation cap cap'; is_thread_cap cap;
     list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation)
       (cur_tcb and valid_etcbs and
        (pspace_aligned and pspace_distinct and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x)))
       (invs' and (\<lambda>s. \<forall>x \<in> set extras'. s \<turnstile>' fst x))
       (decode_set_mcpriority args cap slot extras)
       (decodeSetMCPriority args cap' extras')"
  apply (cases args; cases extras; cases extras';
         clarsimp simp: decode_set_mcpriority_def decodeSetMCPriority_def)
  apply (rename_tac auth_cap auth_slot auth_path rest auth_cap' rest')
  apply (rule corres_split_eqrE)
     apply corresKsimp
    apply (rule corres_splitEE[OF checkPrio_corres])
      apply (rule corres_returnOkTT)
      apply (clarsimp simp: newroot_rel_def elim!: is_thread_cap.elims(2))
     apply (wpsimp simp: valid_cap_def valid_cap'_def)+
  done

lemma getMCP_sp:
  "\<lbrace>P\<rbrace> threadGet tcbMCP t \<lbrace>\<lambda>rv. mcpriority_tcb_at' (\<lambda>st. st = rv) t and P\<rbrace>"
  apply (simp add: threadGet_def)
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

lemma decodeSetPriority_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t \<rbrace>
    decodeSetPriority args (ThreadCap t) extras \<lbrace>tcb_inv_wf'\<rbrace>,-"
  unfolding decodeSetPriority_def
  apply (rule hoare_pre)
  apply (wp checkPrio_lt_ct_weak | wpc | simp | wp (once) checkPrio_inv)+
  apply (clarsimp simp: maxPriority_def numPriorities_def)
  using max_word_max [of \<open>UCAST(64 \<rightarrow> 8) x\<close> for x]
  apply (simp add: max_word_mask numeral_eq_Suc mask_Suc)
  done

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
    decodeSetMCPriority args (ThreadCap t) extras \<lbrace>tcb_inv_wf'\<rbrace>,-"
  unfolding decodeSetMCPriority_def Let_def
  apply (rule hoare_pre)
  apply (wp checkPrio_lt_ct_weak | wpc | simp | wp (once) checkPrio_inv)+
  apply (clarsimp simp: maxPriority_def numPriorities_def)
  using max_word_max [of \<open>UCAST(64 \<rightarrow> 8) x\<close> for x]
  apply (simp add: max_word_mask numeral_eq_Suc mask_Suc)
  done

lemma decodeSetMCPriority_inv[wp]:
  "\<lbrace>P\<rbrace> decodeSetMCPriority args cap extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decodeSetMCPriority_def Let_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp checkPrio_inv | simp add: whenE_def split del: if_split
             | rule hoare_drop_imps
             | wpcw)+
  done

lemma decodeSetSchedParams_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t \<rbrace>
    decodeSetSchedParams args (ThreadCap t) extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  unfolding decodeSetSchedParams_def
  apply (wpsimp wp: checkPrio_lt_ct_weak | wp (once) checkPrio_inv)+
  apply (clarsimp simp: maxPriority_def numPriorities_def)
  using max_word_max [of \<open>UCAST(64 \<rightarrow> 8) x\<close> for x]
  apply (simp add: max_word_mask numeral_eq_Suc mask_Suc)
  done

lemma decodeSetSchedParams_corres:
  "\<lbrakk> cap_relation cap cap'; is_thread_cap cap;
     list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> tcbinv_relation)
       (cur_tcb and valid_etcbs and
        (pspace_aligned and pspace_distinct and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile> fst x)))
       (invs' and (\<lambda>s. \<forall>x \<in> set extras'. s \<turnstile>' fst x))
       (decode_set_sched_params args cap slot extras)
       (decodeSetSchedParams args cap' extras')"
  apply (simp add: decode_set_sched_params_def decodeSetSchedParams_def)
  apply (cases "length args < 2")
   apply (clarsimp split: list.split)
  apply (cases "length extras < 1")
   apply (clarsimp split: list.split simp: list_all2_Cons2)
  apply (clarsimp simp: list_all2_Cons1 neq_Nil_conv val_le_length_Cons linorder_not_less)
  apply (rule corres_split_eqrE)
     apply corresKsimp
    apply (rule corres_split_norE[OF checkPrio_corres])
      apply (rule corres_splitEE[OF checkPrio_corres])
        apply (rule corres_returnOkTT)
        apply (clarsimp simp: newroot_rel_def elim!: is_thread_cap.elims(2))
       apply (wpsimp wp: check_prio_inv checkPrio_inv
                   simp: valid_cap_def valid_cap'_def)+
  done

lemma checkValidIPCBuffer_corres:
  "cap_relation cap cap' \<Longrightarrow>
   corres (ser \<oplus> dc) \<top> \<top>
     (check_valid_ipc_buffer vptr cap)
     (checkValidIPCBuffer vptr cap')"
  apply (simp add: check_valid_ipc_buffer_def
                   checkValidIPCBuffer_def
                   X64_H.checkValidIPCBuffer_def
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
  apply (simp add: checkValidIPCBuffer_def
                   X64_H.checkValidIPCBuffer_def
                   whenE_def unlessE_def
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
  apply (simp    add: decode_set_ipc_buffer_def decodeSetIPCBuffer_def
           split del: if_split)
  apply (cases args)
   apply simp
  apply (cases extras)
   apply simp
  apply (clarsimp simp: list_all2_Cons1 liftME_def[symmetric]
                        is_cap_simps
             split del: if_split)
  apply (clarsimp simp add: returnOk_def newroot_rel_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule deriveCap_corres; simp)
        apply (simp add: o_def newroot_rel_def split_def dc_def[symmetric])
        apply (erule checkValidIPCBuffer_corres)
       apply (wp hoareE_TrueI | simp)+
  apply fastforce
  done

lemma decodeSetIPC_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
        and (\<lambda>s. \<forall>v \<in> set extras. s \<turnstile>' fst v \<and> cte_at' (snd v) s)\<rbrace>
     decodeSetIPCBuffer args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp   add: decodeSetIPCBuffer_def Let_def whenE_def
          split del: if_split cong: list.case_cong prod.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
    apply (rule checkValidIPCBuffer_ArchObject_wp)
   apply simp
   apply (wp hoare_drop_imps)
  apply clarsimp
  done

lemma decodeSetIPCBuffer_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetIPCBuffer args cap slot extras \<lbrace>\<lambda>rv s. isThreadControl rv\<rbrace>,-"
  apply (simp add: decodeSetIPCBuffer_def Let_def
             split del: if_split cong: list.case_cong prod.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
   apply (simp only: isThreadControl_def tcbinvocation.simps)
   apply wp+
  apply (clarsimp simp: isThreadControl_def)
  done

lemma decodeSetPriority_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetPriority args cap extras \<lbrace>\<lambda>rv s. isThreadControl rv\<rbrace>,-"
  apply (simp add: decodeSetPriority_def)
  apply wpsimp
  apply (clarsimp simp: isThreadControl_def)
  done

lemma decodeSetMCPriority_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetMCPriority args cap extras \<lbrace>\<lambda>rv s. isThreadControl rv\<rbrace>,-"
  apply (simp add: decodeSetMCPriority_def)
  apply wpsimp
  apply (clarsimp simp: isThreadControl_def)
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

lemma decodeSetSpace_corres:
  notes if_cong [cong]
  shows
 "\<lbrakk> cap_relation cap cap'; list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras';
      is_thread_cap cap \<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> tcbinv_relation)
         (invs and valid_cap cap and (\<lambda>s. \<forall>x \<in> set extras. cte_at (snd x) s))
         (invs' and valid_cap' cap'  and (\<lambda>s. \<forall>x \<in> set extras'. cte_at' (snd x) s))
      (decode_set_space args cap slot extras)
      (decodeSetSpace args cap' (cte_map slot) extras')"
  apply (simp    add: decode_set_space_def decodeSetSpace_def
                      Let_def
           split del: if_split)
  apply (cases "3 \<le> length args \<and> 2 \<le> length extras'")
   apply (clarsimp simp: val_le_length_Cons list_all2_Cons2
              split del: if_split)
   apply (simp add: liftE_bindE liftM_def getThreadCSpaceRoot getThreadVSpaceRoot
                    cap_CNode_case_throw unlessE_throwError_returnOk unlessE_whenE
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
           apply (simp(no_asm) add: split_def bindE_assoc
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
                                       is_valid_vtable_root_def isValidVTableRoot_def
                                       X64_H.isValidVTableRoot_def)[1]
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

lemma decodeSetSpace_wf[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t and cte_at' slot
      and (\<lambda>s. \<forall>x \<in> set extras. s \<turnstile>' fst x \<and> cte_at' (snd x) s \<and> t \<noteq> snd x \<and> t + 32 \<noteq> snd x)\<rbrace>
     decodeSetSpace args (ThreadCap t) slot extras
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp       add: decodeSetSpace_def Let_def split_def
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

lemma decodeSetSpace_inv[wp]:
  "\<lbrace>P\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp       add: decodeSetSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: if_cong list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
            | simp add: o_def split_def split del: if_split
            | wpcw)+
  done

lemma decodeSetSpace_is_tc[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv s. isThreadControl rv\<rbrace>,-"
  apply (simp       add: decodeSetSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
           | simp only: isThreadControl_def tcbinvocation.simps
           | wpcw)+
  apply simp
  done

lemma decodeSetSpace_tc_target[wp]:
  "\<lbrace>\<lambda>s. P (capTCBPtr cap)\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv s. P (tcThread rv)\<rbrace>,-"
  apply (simp       add: decodeSetSpace_def Let_def split_def
                         unlessE_def getThreadVSpaceRoot getThreadCSpaceRoot
              split del: if_split cong: list.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps
           | simp only: tcbinvocation.sel
           | wpcw)+
  apply simp
  done

lemma decodeSetSpace_tc_slot[wp]:
  "\<lbrace>\<lambda>s. P slot\<rbrace> decodeSetSpace args cap slot extras \<lbrace>\<lambda>rv s. P (tcThreadCapSlot rv)\<rbrace>,-"
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
 "\<lbrakk> cap_relation cap cap'; list_all2 (\<lambda>(c, sl) (c', sl'). cap_relation c c' \<and> sl' = cte_map sl) extras extras';
     is_thread_cap cap \<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> tcbinv_relation) (einvs and valid_cap cap and (\<lambda>s. \<forall>x \<in> set extras. cte_at (snd x) s))
                                 (invs' and valid_cap' cap' and (\<lambda>s. \<forall>x \<in> set extras'. cte_at' (snd x) s))
      (decode_tcb_configure args cap slot extras)
      (decodeTCBConfigure args cap' (cte_map slot) extras')"
  apply (clarsimp simp add: decode_tcb_configure_def decodeTCBConfigure_def)
  apply (cases "length args < 4")
  apply (clarsimp split: list.split)
  apply (cases "length extras < 3")
  apply (clarsimp split: list.split simp: list_all2_Cons2)
  apply (clarsimp simp: linorder_not_less val_le_length_Cons list_all2_Cons1
      priorityBits_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule decodeSetIPCBuffer_corres; simp)
      apply (rule corres_splitEE)
         apply (rule decodeSetSpace_corres; simp)
        apply (rule_tac F="tcb_invocation.is_ThreadControl set_params" in corres_gen_asm)
        apply (rule_tac F="tcb_invocation.is_ThreadControl set_space" in corres_gen_asm)
        apply (rule_tac F="tcThreadCapSlot setSpace = cte_map slot" in corres_gen_asm2)
        apply (rule corres_trivial)
        apply (clarsimp simp: tcb_invocation.is_ThreadControl_def returnOk_def is_cap_simps)
       apply (wp | simp add: invs_def valid_sched_def)+
  done

lemma isThreadControl_def2:
  "isThreadControl tinv = (\<exists>a b c d e f g h. tinv = ThreadControl a b c d e f g h)"
  by (cases tinv, simp_all add: isThreadControl_def)

lemma decodeSetSpaceSome[wp]:
  "\<lbrace>\<top>\<rbrace> decodeSetSpace xs cap y zs
   \<lbrace>\<lambda>rv s. tcNewCRoot rv \<noteq> None\<rbrace>,-"
  apply (simp add: decodeSetSpace_def split_def cap_CNode_case_throw
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
                             \<and> isThreadControl setSpace \<and> isThreadControl setIPCParams
                             \<and> tcThread setSpace = t \<and> tcNewCRoot setSpace \<noteq> None"
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

lemma tcb_real_cte_32:
  "\<lbrakk> real_cte_at' (t + 2^cteSizeBits) s; tcb_at' t s \<rbrakk> \<Longrightarrow> False"
  by (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_32)

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
   apply (fastforce simp: valid_cap_def valid_cap'_def dest: hd_in_set)+
  done

lemma decodeUnbindNotification_corres:
  "corres (ser \<oplus> tcbinv_relation)
          (tcb_at t and pspace_aligned and pspace_distinct) \<top>
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
             corres_guard_imp[OF decodeSetTLSBase_corres],
         simp_all add: valid_cap_simps valid_cap_simps' invs_def valid_sched_def)
  apply (auto simp: list_all2_map1 list_all2_map2 valid_state_def
             elim!: list_all2_mono)
  done

crunch decodeTCBInvocation
  for inv[wp]: P
(simp: crunch_simps)

lemma real_cte_at_not_tcb_at':
  "real_cte_at' x s \<Longrightarrow> \<not> tcb_at' x s"
  "real_cte_at' (x + 2^cteSizeBits) s \<Longrightarrow> \<not> tcb_at' x s"
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp elim!: tcb_real_cte_32)
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
        | simp add: threadGet_def getBoundNotification_def)+
  apply (fastforce simp: valid_cap'_def[where c="capability.ThreadCap t"]
                         is_ntfn invs_def valid_state'_def valid_pspace'_def
                         projectKOs null_def pred_tcb_at'_def obj_at'_def
                   dest!: global'_no_ex_cap hd_in_set)
  done

lemma decodeUnbindNotification_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     decodeUnbindNotification (capability.ThreadCap t)
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeUnbindNotification_def)
  apply (wp getObject_tcb_wp | wpc | simp add: threadGet_def getBoundNotification_def)+
  apply (auto simp: obj_at'_def pred_tcb_at'_def)
  done

lemma decodeSetTLSBase_wf:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     decodeSetTLSBase w (capability.ThreadCap t)
   \<lbrace>tcb_inv_wf'\<rbrace>,-"
  apply (simp add: decodeSetTLSBase_def
             cong: list.case_cong)
  by wpsimp

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
             decodeCopyReg_wf decodeBindNotification_wf decodeUnbindNotification_wf)+)
  apply (clarsimp simp: real_cte_at')
  apply (fastforce simp: real_cte_at_not_tcb_at' objBits_defs)
  done

lemma restart_makes_simple':
  "\<lbrace>st_tcb_at' simple' t\<rbrace>
     restart t'
   \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: restart_def)
  apply (wp sts_st_tcb_at'_cases cancelIPC_simple
            cancelIPC_st_tcb_at hoare_weak_lift_imp | simp)+
   apply (rule hoare_strengthen_post [OF isStopped_inv])
   prefer 2
   apply assumption
  apply clarsimp
  done

lemma setPriority_st_tcb_at'[wp]:
  "\<lbrace>st_tcb_at' P t\<rbrace> setPriority t' p \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: setPriority_def)
  apply (wp threadSet_pred_tcb_no_state | simp)+
  done

lemma setMCPriority_st_tcb_at'[wp]:
  "\<lbrace>st_tcb_at' P t\<rbrace> setMCPriority t' p \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: setMCPriority_def)
  apply (wp threadSet_pred_tcb_no_state | simp)+
  done

lemma cteDelete_makes_simple':
  "\<lbrace>st_tcb_at' simple' t\<rbrace> cteDelete slot v \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  by (wp cteDelete_st_tcb_at' | simp)+

crunch getThreadBufferSlot, setPriority, setMCPriority
  for irq_states'[wp]: valid_irq_states'
  (simp: crunch_simps)

lemma inv_tcb_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace> invokeTCB tcb_inv
  -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  including classic_wp_pre
  apply (simp add: invokeTCB_def)
  apply (rule hoare_pre)
   apply (wpc |
          wp withoutPreemption_R cteDelete_IRQInactive checkCap_inv
             hoare_vcg_const_imp_liftE_R cteDelete_irq_states'
             hoare_vcg_const_imp_lift |
          simp add: split_def)+
  done

end

end
