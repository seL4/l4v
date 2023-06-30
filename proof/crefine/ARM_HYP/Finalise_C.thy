(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_C
imports IpcCancel_C
begin

context kernel_m
begin

declare if_split [split del]

definition
  "option_map2 f m = option_map f \<circ> m"

lemma tcbSchedEnqueue_cslift_spec:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace>s. \<exists>d v. option_map2 tcbPriority_C (cslift s) \<acute>tcb = Some v
                       \<and> unat v \<le> numPriorities
                       \<and> option_map2 tcbDomain_C (cslift s) \<acute>tcb = Some d
                       \<and> unat d < Kernel_Config.numDomains
                       \<and> (end_C (index \<acute>ksReadyQueues (unat (d*0x100 + v))) \<noteq> NULL
                           \<longrightarrow> option_map2 tcbPriority_C (cslift s)
                                   (head_C (index \<acute>ksReadyQueues (unat (d*0x100 + v))))
                                           \<noteq> None
                             \<and> option_map2 tcbDomain_C (cslift s)
                                   (head_C (index \<acute>ksReadyQueues (unat (d*0x100 + v))))
                                           \<noteq> None)\<rbrace>
       Call tcbSchedEnqueue_'proc
      {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
           \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
           \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
           \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: option_map2_def fun_eq_iff h_t_valid_clift
                        h_t_valid_field[OF h_t_valid_clift])
  apply (rule conjI)
   apply (clarsimp simp: typ_heap_simps le_maxDomain_eq_less_numDomains)
   apply unat_arith
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: typ_heap_simps cong: if_cong)
   apply (simp split: if_split)
  apply (clarsimp simp: typ_heap_simps if_Some_helper cong: if_cong)
  by (simp split: if_split)

lemma setThreadState_cslift_spec:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace>s. s \<Turnstile>\<^sub>c \<acute>tptr \<and> (\<forall>x. ksSchedulerAction_' (globals s) = tcb_Ptr x
                 \<and> x \<noteq> 0 \<and> x \<noteq> 1
              \<longrightarrow> (\<exists>d v. option_map2 tcbPriority_C (cslift s) (tcb_Ptr x) = Some v
                       \<and> unat v \<le> numPriorities
                       \<and> option_map2 tcbDomain_C (cslift s) (tcb_Ptr x) = Some d
                       \<and> unat d < Kernel_Config.numDomains
                       \<and> (end_C (index \<acute>ksReadyQueues (unat (d*0x100 + v))) \<noteq> NULL
                           \<longrightarrow> option_map2 tcbPriority_C (cslift s)
                                   (head_C (index \<acute>ksReadyQueues (unat (d*0x100 + v))))
                                           \<noteq> None
                             \<and> option_map2 tcbDomain_C (cslift s)
                                   (head_C (index \<acute>ksReadyQueues (unat (d*0x100 + v))))
                                           \<noteq> None)))\<rbrace>
          Call setThreadState_'proc
      {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
           \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
           \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
           \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)
           \<and> ksReadyQueues_' (globals s') = ksReadyQueues_' (globals s)}"
  apply (rule allI, rule conseqPre)
   apply vcg_step
   apply vcg_step
    apply vcg_step
   apply vcg_step
    apply vcg_step
     apply vcg_step
    apply vcg_step
       apply (vcg exspec=tcbSchedEnqueue_cslift_spec)
    apply (vcg_step+)[2]
   apply vcg_step
      apply (vcg exspec=isRunnable_modifies)
     apply vcg
    apply vcg_step
    apply vcg_step
       apply (vcg_step+)[1]
      apply vcg
     apply vcg_step+
  apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff fun_eq_iff option_map2_def)
  by (simp split: if_split)

lemma ep_queue_relation_shift:
  "(option_map2 tcbEPNext_C (cslift s')
         = option_map2 tcbEPNext_C (cslift s)
    \<and> option_map2 tcbEPPrev_C (cslift s')
         = option_map2 tcbEPPrev_C (cslift s))
     \<longrightarrow> ep_queue_relation (cslift s') ts qPrev qHead
          = ep_queue_relation (cslift s) ts qPrev qHead"
  apply clarsimp
  apply (induct ts arbitrary: qPrev qHead)
   apply simp
  apply simp
  apply (simp add: option_map2_def fun_eq_iff
                   map_option_case)
  apply (drule_tac x=qHead in spec)+
  apply (clarsimp split: option.split_asm)
  done

lemma rf_sr_cscheduler_relation:
  "(s, s') \<in> rf_sr \<Longrightarrow> cscheduler_action_relation
       (ksSchedulerAction s) (ksSchedulerAction_' (globals s'))"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma obj_at_ko_at2':
  "\<lbrakk> obj_at' P p s; ko_at' ko p s \<rbrakk> \<Longrightarrow> P ko"
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (drule ko_at_obj_congD', simp+)
  done

lemma ctcb_relation_tcbDomain:
  "ctcb_relation tcb tcb' \<Longrightarrow> ucast (tcbDomain tcb) = tcbDomain_C tcb'"
  by (simp add: ctcb_relation_def)

lemma ctcb_relation_tcbPriority:
  "ctcb_relation tcb tcb' \<Longrightarrow> ucast (tcbPriority tcb) = tcbPriority_C tcb'"
  by (simp add: ctcb_relation_def)

lemma ctcb_relation_tcbDomain_maxDomain_numDomains:
  "\<lbrakk> ctcb_relation tcb tcb'; tcbDomain tcb \<le> maxDomain \<rbrakk>
   \<Longrightarrow> unat (tcbDomain_C tcb') < Kernel_Config.numDomains"
  apply (subst ctcb_relation_tcbDomain[symmetric], simp)
  apply (simp add: le_maxDomain_eq_less_numDomains)
  done

lemma ctcb_relation_tcbPriority_maxPriority_numPriorities:
  "\<lbrakk> ctcb_relation tcb tcb'; tcbPriority tcb \<le> maxPriority \<rbrakk>
    \<Longrightarrow> unat (tcbPriority_C tcb') < numPriorities"
  apply (subst ctcb_relation_tcbPriority[symmetric], simp)
  apply (simp add: maxPriority_def numPriorities_def word_le_nat_alt)
  done

lemma tcbSchedEnqueue_cslift_precond_discharge:
  "\<lbrakk> (s, s') \<in> rf_sr; obj_at' (P :: tcb \<Rightarrow> bool) x s;
        valid_queues s; valid_objs' s \<rbrakk> \<Longrightarrow>
   (\<exists>d v. option_map2 tcbPriority_C (cslift s') (tcb_ptr_to_ctcb_ptr x) = Some v
        \<and> unat v < numPriorities
        \<and> option_map2 tcbDomain_C (cslift s') (tcb_ptr_to_ctcb_ptr x) = Some d
        \<and> unat d < Kernel_Config.numDomains
        \<and> (end_C (index (ksReadyQueues_' (globals s')) (unat (d*0x100 + v))) \<noteq> NULL
                \<longrightarrow> option_map2 tcbPriority_C (cslift s')
                     (head_C (index (ksReadyQueues_' (globals s')) (unat (d*0x100 + v))))
                                    \<noteq> None
                  \<and> option_map2 tcbDomain_C (cslift s')
                     (head_C (index (ksReadyQueues_' (globals s')) (unat (d*0x100 + v))))
                                    \<noteq> None))"
  apply (drule(1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps' option_map2_def)
  apply (frule_tac t=x in valid_objs'_maxPriority, fastforce simp: obj_at'_def)
  apply (frule_tac t=x in valid_objs'_maxDomain, fastforce simp: obj_at'_def)
  apply (drule_tac P="\<lambda>tcb. tcbPriority tcb \<le> maxPriority" in obj_at_ko_at2', simp)
  apply (drule_tac P="\<lambda>tcb. tcbDomain tcb \<le> maxDomain" in obj_at_ko_at2', simp)
  apply (simp add: ctcb_relation_tcbDomain_maxDomain_numDomains
                   ctcb_relation_tcbPriority_maxPriority_numPriorities)
  apply (frule_tac d="tcbDomain ko" and p="tcbPriority ko"
              in rf_sr_sched_queue_relation)
    apply (simp add: maxDom_to_H maxPrio_to_H)+
  apply (simp add: cready_queues_index_to_C_def2 numPriorities_def le_maxDomain_eq_less_numDomains)
  apply (clarsimp simp: ctcb_relation_def)
  apply (frule arg_cong[where f=unat], subst(asm) unat_ucast_8_32)
  apply (frule tcb_queue'_head_end_NULL)
   apply (erule conjunct1[OF valid_queues_valid_q])
  apply (frule(1) tcb_queue_relation_qhead_valid')
   apply (simp add: valid_queues_valid_q)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  done

lemma cancel_all_ccorres_helper:
  "ccorres dc xfdc
      (\<lambda>s. valid_objs' s \<and> valid_queues s
             \<and> (\<forall>t\<in>set ts. tcb_at' t s \<and> t \<noteq> 0)
             \<and> sch_act_wf (ksSchedulerAction s) s)
      {s'. \<exists>p. ep_queue_relation (cslift s') ts
                p (thread_' s')} hs
      (mapM_x (\<lambda>t. do
              y \<leftarrow> setThreadState Restart t;
              tcbSchedEnqueue t
            od) ts)
      (WHILE \<acute>thread \<noteq> tcb_Ptr 0 DO
        (CALL setThreadState(\<acute>thread, scast ThreadState_Restart));;
        (CALL tcbSchedEnqueue(\<acute>thread));;
        Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>thread\<rbrace>
         (\<acute>thread :== h_val (hrs_mem \<acute>t_hrs) (Ptr &(\<acute>thread\<rightarrow>[''tcbEPNext_C'']) :: tcb_C ptr ptr))
       OD)"
  unfolding whileAnno_def
proof (induct ts)
  case Nil
  show ?case
    apply (simp del: Collect_const)
    apply (rule iffD1 [OF ccorres_expand_while_iff])
    apply (rule ccorres_tmp_lift2[where G'=UNIV and G''="\<lambda>x. UNIV", simplified])
     apply ceqv
    apply (simp add: ccorres_cond_iffs mapM_x_def sequence_x_def)
    apply (rule ccorres_guard_imp2, rule ccorres_return_Skip)
    apply simp
    done
next
  case (Cons thread threads)
  show ?case
    apply (rule iffD1 [OF ccorres_expand_while_iff])
    apply (simp del: Collect_const
                add: mapM_x_Cons)
    apply (rule ccorres_guard_imp2)
     apply (rule_tac xf'=thread_' in ccorres_abstract)
      apply ceqv
     apply (rule_tac P="rv' = tcb_ptr_to_ctcb_ptr thread"
                     in ccorres_gen_asm2)
     apply (rule_tac P="tcb_ptr_to_ctcb_ptr thread \<noteq> Ptr 0"
                     in ccorres_gen_asm)
     apply (clarsimp simp add: Collect_True ccorres_cond_iffs
                     simp del: Collect_const)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow[where F=UNIV])
         apply (intro ccorres_rhs_assoc)
         apply (ctac(no_vcg) add: setThreadState_ccorres)
          apply (rule ccorres_add_return2)
          apply (ctac(no_vcg) add: tcbSchedEnqueue_ccorres)
           apply (rule_tac P="tcb_at' thread"
                      in ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
           apply (drule obj_at_ko_at', clarsimp)
           apply (erule cmap_relationE1 [OF cmap_relation_tcb])
            apply (erule ko_at_projectKO_opt)
           apply (fastforce intro: typ_heap_simps)
          apply (wp sts_running_valid_queues | simp)+
        apply (rule ceqv_refl)
       apply (rule "Cons.hyps")
      apply (wp sts_valid_objs' sts_sch_act sch_act_wf_lift hoare_vcg_const_Ball_lift
                sts_running_valid_queues sts_st_tcb' setThreadState_oa_queued | simp)+

     apply (vcg exspec=setThreadState_cslift_spec exspec=tcbSchedEnqueue_cslift_spec)
    apply (clarsimp simp: tcb_at_not_NULL
                          Collect_const_mem valid_tcb_state'_def
                          ThreadState_Restart_def mask_def
                          valid_objs'_maxDomain valid_objs'_maxPriority)
    apply (drule(1) obj_at_cslift_tcb)
    apply (clarsimp simp: typ_heap_simps)
    apply (rule conjI)
     apply clarsimp
     apply (frule rf_sr_cscheduler_relation)
     apply (clarsimp simp: cscheduler_action_relation_def
                           st_tcb_at'_def
                    split: scheduler_action.split_asm)
     apply (rename_tac word)
     apply (frule_tac x=word in tcbSchedEnqueue_cslift_precond_discharge)
        apply simp
       apply clarsimp
      apply clarsimp
     apply clarsimp
    apply clarsimp
    apply (rule conjI)
     apply (frule(3) tcbSchedEnqueue_cslift_precond_discharge)
     apply clarsimp
    apply clarsimp
    apply (subst ep_queue_relation_shift, fastforce)
    apply (drule_tac x="tcb_ptr_to_ctcb_ptr thread"
                in fun_cong)+
    apply (clarsimp simp add: option_map2_def typ_heap_simps)
    apply fastforce
    done
qed

lemma cancelAllIPC_ccorres:
  "ccorres dc xfdc
   (invs') (UNIV \<inter> {s. epptr_' s = Ptr epptr}) []
   (cancelAllIPC epptr) (Call cancelAllIPC_'proc)"
  apply (cinit lift: epptr_')
   apply (rule ccorres_symb_exec_l [OF _ getEndpoint_inv _ empty_fail_getEndpoint])
    apply (rule_tac xf'=ret__unsigned_'
                and val="case ep of IdleEP \<Rightarrow> scast EPState_Idle
                            | RecvEP _ \<Rightarrow> scast EPState_Recv | SendEP _ \<Rightarrow> scast EPState_Send"
                and R="ko_at' ep epptr"
             in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply vcg
       apply clarsimp
       apply (erule cmap_relationE1 [OF cmap_relation_ep])
        apply (erule ko_at_projectKO_opt)
       apply (clarsimp simp add: typ_heap_simps)
       apply (simp add: cendpoint_relation_def Let_def
                 split: endpoint.split_asm)
      apply ceqv
     apply (rule_tac A="invs' and ko_at' ep epptr"
              in ccorres_guard_imp2[where A'=UNIV])
      apply wpc
        apply (rename_tac list)
        apply (simp add: endpoint_state_defs
                         Collect_False Collect_True
                         ccorres_cond_iffs
                    del: Collect_const)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply (rule ccorres_abstract_cleanup)
        apply csymbr
        apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
        apply (rule_tac r'=dc and xf'=xfdc
                       in ccorres_split_nothrow)
            apply (rule_tac P="ko_at' (RecvEP list) epptr and invs'"
                     in ccorres_from_vcg[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (rule cmap_relationE1 [OF cmap_relation_ep])
              apply assumption
             apply (erule ko_at_projectKO_opt)
            apply (clarsimp simp: typ_heap_simps setEndpoint_def)
            apply (rule rev_bexI)
             apply (rule setObject_eq; simp add: objBits_simps')[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def
                                  Let_def carch_state_relation_def carch_globals_def
                                  cmachine_state_relation_def)
            apply (clarsimp simp: cpspace_relation_def
                                  update_ep_map_tos typ_heap_simps')
            apply (erule(2) cpspace_relation_ep_update_ep)
             subgoal by (simp add: cendpoint_relation_def endpoint_state_defs)
            subgoal by simp
           apply (rule ceqv_refl)
          apply (simp only: ccorres_seq_skip)
          apply (rule ccorres_split_nothrow_novcg)
              apply (rule cancel_all_ccorres_helper)
             apply ceqv
            apply (ctac add: rescheduleRequired_ccorres)
           apply (wp weak_sch_act_wf_lift_linear
                     cancelAllIPC_mapM_x_valid_queues
                  | simp)+
              apply (rule mapM_x_wp', wp)+
             apply (wp sts_st_tcb')
             apply (clarsimp split: if_split)
            apply (rule mapM_x_wp', wp)+
           apply (clarsimp simp: valid_tcb_state'_def)
          apply (simp add: guard_is_UNIV_def)
         apply (wp set_ep_valid_objs' hoare_vcg_const_Ball_lift
                   weak_sch_act_wf_lift_linear)
        apply vcg
       apply (simp add: ccorres_cond_iffs)
       apply (rule ccorres_return_Skip)
      apply (rename_tac list)
      apply (simp add: endpoint_state_defs Collect_False Collect_True ccorres_cond_iffs
                  del: Collect_const)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (rule ccorres_abstract_cleanup)
      apply csymbr
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
      apply (rule_tac r'=dc and xf'=xfdc
                     in ccorres_split_nothrow)
          apply (rule_tac P="ko_at' (SendEP list) epptr and invs'"
                   in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply clarsimp
          apply (rule cmap_relationE1 [OF cmap_relation_ep])
            apply assumption
           apply (erule ko_at_projectKO_opt)
          apply (clarsimp simp: typ_heap_simps setEndpoint_def)
          apply (rule rev_bexI)
           apply (rule setObject_eq, simp_all add: objBits_simps')[1]
          apply (clarsimp simp: rf_sr_def cstate_relation_def
                                Let_def carch_state_relation_def carch_globals_def
                                cmachine_state_relation_def)
          apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                update_ep_map_tos)
          apply (erule(2) cpspace_relation_ep_update_ep)
           subgoal by (simp add: cendpoint_relation_def endpoint_state_defs)
          subgoal by simp
         apply (rule ceqv_refl)
        apply (simp only: ccorres_seq_skip)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule cancel_all_ccorres_helper)
           apply ceqv
          apply (ctac add: rescheduleRequired_ccorres)
         apply (wp cancelAllIPC_mapM_x_valid_queues)
         apply (wp mapM_x_wp' weak_sch_act_wf_lift_linear
                   sts_st_tcb' | clarsimp simp: valid_tcb_state'_def split: if_split)+
        apply (simp add: guard_is_UNIV_def)
       apply (wp set_ep_valid_objs' hoare_vcg_const_Ball_lift
                 weak_sch_act_wf_lift_linear)
      apply vcg
     apply (clarsimp simp: valid_ep'_def invs_valid_objs' invs_queues)
     apply (rule cmap_relationE1[OF cmap_relation_ep], assumption)
      apply (erule ko_at_projectKO_opt)
     apply (frule obj_at_valid_objs', clarsimp+)
     apply (clarsimp simp: projectKOs valid_obj'_def valid_ep'_def)
     subgoal by (auto simp: typ_heap_simps cendpoint_relation_def
                       Let_def tcb_queue_relation'_def
                       invs_valid_objs' valid_objs'_maxDomain valid_objs'_maxPriority
               intro!: obj_at_conj')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (wp getEndpoint_wp)
  apply clarsimp
  done

lemma cancelAllSignals_ccorres:
  "ccorres dc xfdc
   (invs') (UNIV \<inter> {s. ntfnPtr_' s = Ptr ntfnptr}) []
   (cancelAllSignals ntfnptr) (Call cancelAllSignals_'proc)"
  apply (cinit lift: ntfnPtr_')
   apply (rule ccorres_symb_exec_l [OF _ get_ntfn_inv' _ empty_fail_getNotification])
    apply (rule_tac xf'=ret__unsigned_'
                and val="case ntfnObj ntfn of IdleNtfn \<Rightarrow> scast NtfnState_Idle
                            | ActiveNtfn _ \<Rightarrow> scast NtfnState_Active | WaitingNtfn _ \<Rightarrow> scast NtfnState_Waiting"
                and R="ko_at' ntfn ntfnptr"
             in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply vcg
       apply clarsimp
       apply (erule cmap_relationE1 [OF cmap_relation_ntfn])
        apply (erule ko_at_projectKO_opt)
       apply (clarsimp simp add: typ_heap_simps)
       apply (simp add: cnotification_relation_def Let_def
                 split: ntfn.split_asm)
      apply ceqv
     apply (rule_tac A="invs' and ko_at' ntfn ntfnptr"
              in ccorres_guard_imp2[where A'=UNIV])
      apply wpc
        apply (simp add: notification_state_defs ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (simp add: notification_state_defs ccorres_cond_iffs)
       apply (rule ccorres_return_Skip)
      apply (rename_tac list)
      apply (simp add: notification_state_defs ccorres_cond_iffs Collect_True
                  del: Collect_const)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (rule ccorres_abstract_cleanup)
      apply csymbr
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
      apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
          apply (rule_tac P="ko_at' ntfn ntfnptr and invs'"
                   in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply clarsimp
          apply (rule_tac x=ntfnptr in cmap_relationE1 [OF cmap_relation_ntfn], assumption)
           apply (erule ko_at_projectKO_opt)
          apply (clarsimp simp: typ_heap_simps setNotification_def)
          apply (rule rev_bexI)
           apply (rule setObject_eq, simp_all add: objBits_simps')[1]
          apply (clarsimp simp: rf_sr_def cstate_relation_def
                                Let_def carch_state_relation_def carch_globals_def
                                cmachine_state_relation_def)
          apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                update_ntfn_map_tos)
          apply (erule(2) cpspace_relation_ntfn_update_ntfn)
           subgoal by (simp add: cnotification_relation_def notification_state_defs Let_def)
          subgoal by simp
         apply (rule ceqv_refl)
        apply (simp only: ccorres_seq_skip)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule cancel_all_ccorres_helper)
           apply ceqv
          apply (ctac add: rescheduleRequired_ccorres)
         apply (wp cancelAllIPC_mapM_x_valid_queues)
         apply (wp mapM_x_wp' weak_sch_act_wf_lift_linear
                   sts_st_tcb' | clarsimp simp: valid_tcb_state'_def split: if_split)+
        apply (simp add: guard_is_UNIV_def)
       apply (wp set_ntfn_valid_objs' hoare_vcg_const_Ball_lift
                 weak_sch_act_wf_lift_linear)
      apply vcg
     apply clarsimp
     apply (rule cmap_relationE1[OF cmap_relation_ntfn], assumption)
      apply (erule ko_at_projectKO_opt)
     apply (frule obj_at_valid_objs', clarsimp+)
     apply (clarsimp simp add: valid_obj'_def valid_ntfn'_def projectKOs)
     subgoal by (auto simp: typ_heap_simps cnotification_relation_def
                       Let_def tcb_queue_relation'_def
                       invs_valid_objs' valid_objs'_maxDomain valid_objs'_maxPriority
               intro!: obj_at_conj')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (wp getNotification_wp)
  apply clarsimp
  done

lemma tcb_queue_concat:
  "tcb_queue_relation getNext getPrev mp (xs @ z # ys) qprev qhead
        \<Longrightarrow> tcb_queue_relation getNext getPrev mp (z # ys)
                (tcb_ptr_to_ctcb_ptr (last ((ctcb_ptr_to_tcb_ptr qprev) # xs))) (tcb_ptr_to_ctcb_ptr z)"
  apply (induct xs arbitrary: qprev qhead)
   apply clarsimp
  apply clarsimp
  apply (elim meta_allE, drule(1) meta_mp)
  apply (clarsimp cong: if_cong)
  done

lemma tcb_fields_ineq_helper:
  "\<lbrakk> tcb_at' (ctcb_ptr_to_tcb_ptr x) s; tcb_at' (ctcb_ptr_to_tcb_ptr y) s \<rbrakk> \<Longrightarrow>
     &(x\<rightarrow>[''tcbSchedPrev_C'']) \<noteq> &(y\<rightarrow>[''tcbSchedNext_C''])"
  apply (clarsimp dest!: tcb_aligned'[OF obj_at'_weakenE, OF _ TrueI]
                         ctcb_ptr_to_tcb_ptr_aligned)
  apply (clarsimp simp: field_lvalue_def ctcb_size_bits_def)
  apply (subgoal_tac "is_aligned (ptr_val y - ptr_val x) 8")
   apply (drule sym, fastforce simp: is_aligned_def dvd_def)
  apply (erule(1) aligned_sub_aligned)
   apply (simp add: word_bits_conv)
  done

end

primrec
  tcb_queue_relation2 :: "(tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow> (tcb_C \<Rightarrow> tcb_C ptr)
                               \<Rightarrow> (tcb_C ptr \<rightharpoonup> tcb_C) \<Rightarrow> tcb_C ptr list
                               \<Rightarrow> tcb_C ptr \<Rightarrow> tcb_C ptr \<Rightarrow> bool"
where
  "tcb_queue_relation2 getNext getPrev hp [] before after = True"
| "tcb_queue_relation2 getNext getPrev hp (x # xs) before after =
   (\<exists>tcb. hp x = Some tcb \<and> getPrev tcb = before
      \<and> getNext tcb = hd (xs @ [after])
      \<and> tcb_queue_relation2 getNext getPrev hp xs x after)"

lemma use_tcb_queue_relation2:
  "tcb_queue_relation getNext getPrev hp xs qprev qhead
     = (tcb_queue_relation2 getNext getPrev hp
            (map tcb_ptr_to_ctcb_ptr xs) qprev (tcb_Ptr 0)
           \<and> qhead = (hd (map tcb_ptr_to_ctcb_ptr xs @ [tcb_Ptr 0])))"
  apply (induct xs arbitrary: qhead qprev)
   apply simp
  apply (simp add: conj_comms cong: conj_cong)
  done

lemma tcb_queue_relation2_concat:
  "tcb_queue_relation2 getNext getPrev hp
            (xs @ ys) before after
     = (tcb_queue_relation2 getNext getPrev hp
            xs before (hd (ys @ [after]))
         \<and> tcb_queue_relation2 getNext getPrev hp
              ys (last (before # xs)) after)"
  apply (induct xs arbitrary: before)
   apply simp
  apply (rename_tac x xs before)
  apply (simp split del: if_split)
  apply (case_tac "hp x")
   apply simp
  apply simp
  done

lemma tcb_queue_relation2_cong:
  "\<lbrakk>queue = queue'; before = before'; after = after';
   \<And>p. p \<in> set queue' \<Longrightarrow> mp p = mp' p\<rbrakk>
  \<Longrightarrow> tcb_queue_relation2 getNext getPrev mp queue before after =
     tcb_queue_relation2 getNext getPrev mp' queue' before' after'"
  using [[hypsubst_thin = true]]
  apply clarsimp
  apply (induct queue' arbitrary: before')
   apply simp+
  done

context kernel_m begin

lemma setThreadState_ccorres_valid_queues'_simple:
  "ccorres dc xfdc (\<lambda>s. tcb_at' thread s \<and> valid_queues' s \<and> \<not> runnable' st \<and> sch_act_simple s)
   ({s'. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := ts_' s' && mask 4\<rparr>, fl))}
    \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) []
         (setThreadState st thread) (Call setThreadState_'proc)"
  apply (cinit lift: tptr_' cong add: call_ignore_cong)
    apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
   apply (ctac add: scheduleTCB_ccorres_valid_queues'_simple)
  apply (wp threadSet_valid_queues'_and_not_runnable')
  apply (clarsimp simp: weak_sch_act_wf_def valid_queues'_def)
  done

lemma updateRestartPC_ccorres:
  "ccorres dc xfdc (tcb_at' thread) \<lbrace> \<acute>tcb = tcb_ptr_to_ctcb_ptr thread \<rbrace> hs
     (updateRestartPC thread) (Call updateRestartPC_'proc)"
  apply (cinit lift: tcb_')
   apply (subst asUser_bind_distrib; (wp add: empty_fail_getRegister)?)
   apply (ctac (no_vcg) add: getRegister_ccorres)
    apply (ctac (no_vcg) add: setRegister_ccorres)
   apply wpsimp+
   apply (simp add: ARM_HYP_H.faultRegister_def ARM_HYP_H.nextInstructionRegister_def
                    ARM_HYP.faultRegister_def ARM_HYP.nextInstructionRegister_def)
  done

crunches updateRestartPC
  for valid_queues'[wp]: valid_queues'
  and sch_act_simple[wp]: sch_act_simple
  and valid_queues[wp]: Invariants_H.valid_queues
  and valid_objs'[wp]: valid_objs'
  and tcb_at'[wp]: "tcb_at' p"

lemma suspend_ccorres:
  assumes cteDeleteOne_ccorres:
  "\<And>w slot. ccorres dc xfdc
   (invs' and cte_wp_at' (\<lambda>ct. w = -1 \<or> cteCap ct = NullCap
        \<or> (\<forall>cap'. ccap_relation (cteCap ct) cap' \<longrightarrow> cap_get_tag cap' = w)) slot)
   ({s. gs_get_assn cteDeleteOne_'proc (ghost'state_' (globals s)) = w}
        \<inter> {s. slot_' s = Ptr slot}) []
   (cteDeleteOne slot) (Call cteDeleteOne_'proc)"
  shows
  "ccorres dc xfdc
   (invs' and sch_act_simple and tcb_at' thread and (\<lambda>s. thread \<noteq> ksIdleThread s))
   (UNIV \<inter> {s. target_' s = tcb_ptr_to_ctcb_ptr thread}) []
   (suspend thread) (Call suspend_'proc)"
  apply (cinit lift: target_')
   apply (ctac(no_vcg) add: cancelIPC_ccorres1 [OF cteDeleteOne_ccorres])
    apply (rule getThreadState_ccorres_foo)
    apply (rename_tac threadState)
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule_tac xf'=ret__unsigned_'
            and val="thread_state_to_tsType threadState"
            and R="st_tcb_at' ((=) threadState) thread"
            and R'=UNIV
            in
            ccorres_symb_exec_r_known_rv)
       apply clarsimp
       apply (rule conseqPre, vcg)
       apply (clarsimp simp: st_tcb_at'_def)
       apply (frule (1) obj_at_cslift_tcb)
       apply (clarsimp simp: typ_heap_simps ctcb_relation_thread_state_to_tsType)
      apply ceqv
     supply Collect_const[simp del]
     apply (rule ccorres_split_nothrow)
         apply (rule ccorres_cond[where R=\<top> and xf=xfdc])
           apply clarsimp
           apply (rule iffI)
            apply simp
           apply (erule thread_state_to_tsType.elims; simp add: StrictC'_thread_state_defs)
          apply (ctac (no_vcg) add: updateRestartPC_ccorres)
         apply (rule ccorres_return_Skip)
        apply ceqv
       apply (ctac(no_vcg) add: setThreadState_ccorres_valid_queues'_simple)
        apply (ctac add: tcbSchedDequeue_ccorres')
       apply (rule_tac Q="\<lambda>_.
                        (\<lambda>s. \<forall>t' d p. (t' \<in> set (ksReadyQueues s (d, p)) \<longrightarrow>
                              obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d
                                                           \<and> tcbPriority tcb = p) t' s \<and>
                (t' \<noteq> thread \<longrightarrow> st_tcb_at' runnable' t' s)) \<and>
                distinct (ksReadyQueues s (d, p))) and valid_queues' and valid_objs' and tcb_at' thread"
              in hoare_post_imp)
        apply clarsimp
        apply (drule_tac x="t" in spec)
        apply (drule_tac x=d in spec)
        apply (drule_tac x=p in spec)
        apply (clarsimp elim!: obj_at'_weakenE simp: inQ_def)
       apply (wp sts_valid_queues_partial)[1]
      apply clarsimp
      apply (wpsimp simp: valid_tcb_state'_def)
     apply clarsimp
     apply (rule conseqPre, vcg exspec=updateRestartPC_modifies)
     apply (rule subset_refl)
    apply clarsimp
    apply (rule conseqPre, vcg)
    apply (rule subset_refl)
  apply (rule hoare_strengthen_post)
    apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_vcg_conj_lift)
      apply (rule cancelIPC_sch_act_simple)
     apply (rule cancelIPC_tcb_at'[where t=thread])
    apply (rule delete_one_conc_fr.cancelIPC_invs)
   apply (fastforce simp: invs_valid_queues' invs_queues invs_valid_objs'
                          valid_tcb_state'_def)
  apply clarsimp
  apply (auto simp: "StrictC'_thread_state_defs")
  done

lemma cap_to_H_NTFNCap_tag:
  "\<lbrakk> cap_to_H cap = NotificationCap word1 word2 a b;
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_notification_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     by (simp_all add: Let_def cap_lift_def split: if_splits)

lemmas ccorres_pre_getBoundNotification = ccorres_pre_threadGet [where f=tcbBoundNotification, folded getBoundNotification_def]

lemma option_to_ptr_not_NULL:
  "option_to_ptr x \<noteq> NULL \<Longrightarrow> x \<noteq> None"
  by (auto simp: option_to_ptr_def option_to_0_def split: option.splits)

lemma doUnbindNotification_ccorres:
  "ccorres dc xfdc (invs' and tcb_at' tcb)
    (UNIV \<inter> {s. ntfnPtr_' s = ntfn_Ptr ntfnptr} \<inter> {s. tcbptr_' s = tcb_ptr_to_ctcb_ptr tcb}) []
   (do ntfn \<leftarrow> getNotification ntfnptr; doUnbindNotification ntfnptr ntfn tcb od)
   (Call doUnbindNotification_'proc)"
  apply (cinit' lift: ntfnPtr_' tcbptr_')
   apply (rule ccorres_symb_exec_l [OF _ get_ntfn_inv' _ empty_fail_getNotification])
    apply (rule_tac P="invs' and ko_at' ntfn ntfnptr" and P'=UNIV
             in ccorres_split_nothrow_novcg)
        apply (rule ccorres_from_vcg[where rrel=dc and xf=xfdc])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: option_to_ptr_def option_to_0_def)
        apply (frule cmap_relation_ntfn)
        apply (erule (1) cmap_relation_ko_atE)
        apply (rule conjI)
         apply (erule h_t_valid_clift)
        apply (clarsimp simp: setNotification_def split_def)
        apply (rule bexI [OF _ setObject_eq])
            apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                             typ_heap_simps'
                             cpspace_relation_def update_ntfn_map_tos)
            apply (elim conjE)
            apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
              apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
               apply (clarsimp simp: cnotification_relation_def Let_def
                                     mask_def [where n=2] NtfnState_Waiting_def)
               apply (case_tac "ntfnObj ntfn", ((simp add: option_to_ctcb_ptr_def)+)[4])
             subgoal by (simp add: carch_state_relation_def typ_heap_simps')
            subgoal by (simp add: cmachine_state_relation_def)
           subgoal by (simp add: h_t_valid_clift_Some_iff)
          subgoal by (simp add: objBits_simps')
         subgoal by (simp add: objBits_simps)
        apply assumption
       apply ceqv
      apply (rule ccorres_move_c_guard_tcb)
      apply (simp add: setBoundNotification_def)
      apply (rule_tac P'="\<top>" and P="\<top>"
                   in threadSet_ccorres_lemma3)
       apply vcg
      apply simp
      apply (erule(1) rf_sr_tcb_update_no_queue2)
              apply (simp add: typ_heap_simps')+
       apply (simp add: tcb_cte_cases_def)
      apply (simp add: ctcb_relation_def option_to_ptr_def option_to_0_def)
     apply (simp add: invs'_def valid_state'_def)
     apply (wp get_ntfn_ko' | simp add: guard_is_UNIV_def)+
  done

lemma doUnbindNotification_ccorres':
  "ccorres dc xfdc (invs' and tcb_at' tcb and ko_at' ntfn ntfnptr)
    (UNIV \<inter> {s. ntfnPtr_' s = ntfn_Ptr ntfnptr} \<inter> {s. tcbptr_' s = tcb_ptr_to_ctcb_ptr tcb}) []
   (doUnbindNotification ntfnptr ntfn tcb)
   (Call doUnbindNotification_'proc)"
  apply (cinit' lift: ntfnPtr_' tcbptr_')
    apply (rule_tac P="invs' and ko_at' ntfn ntfnptr" and P'=UNIV
                in ccorres_split_nothrow_novcg)
        apply (rule ccorres_from_vcg[where rrel=dc and xf=xfdc])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: option_to_ptr_def option_to_0_def)
        apply (frule cmap_relation_ntfn)
        apply (erule (1) cmap_relation_ko_atE)
        apply (rule conjI)
         apply (erule h_t_valid_clift)
        apply (clarsimp simp: setNotification_def split_def)
        apply (rule bexI [OF _ setObject_eq])
            apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                             typ_heap_simps'
                             cpspace_relation_def update_ntfn_map_tos)
            apply (elim conjE)
            apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
              apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
               apply (clarsimp simp: cnotification_relation_def Let_def
                                     mask_def [where n=2] NtfnState_Waiting_def)
               apply (fold_subgoals (prefix))[2]
               subgoal premises prems using prems
                       by (case_tac "ntfnObj ntfn", (simp add: option_to_ctcb_ptr_def)+)
             subgoal by (simp add: carch_state_relation_def typ_heap_simps')
            subgoal by (simp add: cmachine_state_relation_def)
           subgoal by (simp add: h_t_valid_clift_Some_iff)
          subgoal by (simp add: objBits_simps')
         subgoal by (simp add: objBits_simps)
        apply assumption
       apply ceqv
      apply (rule ccorres_move_c_guard_tcb)
      apply (simp add: setBoundNotification_def)
      apply (rule_tac P'="\<top>" and P="\<top>"
                   in threadSet_ccorres_lemma3)
       apply vcg
      apply simp
      apply (erule(1) rf_sr_tcb_update_no_queue2)
              apply (simp add: typ_heap_simps')+
       apply (simp add: tcb_cte_cases_def)
      apply (simp add: ctcb_relation_def option_to_ptr_def option_to_0_def)
     apply (simp add: invs'_def valid_state'_def)
     apply (wp get_ntfn_ko' | simp add: guard_is_UNIV_def)+
  done


lemma unbindNotification_ccorres:
  "ccorres dc xfdc
    (invs') (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr tcb}) []
    (unbindNotification tcb) (Call unbindNotification_'proc)"
  supply option.case_cong[cong]
  apply (cinit lift: tcb_')
   apply (rule_tac xf'=ntfnPtr_'
                    and r'="\<lambda>rv rv'. rv' = option_to_ptr rv \<and> rv \<noteq> Some 0"
                    in ccorres_split_nothrow)
       apply (simp add: getBoundNotification_def)
       apply (rule_tac P="no_0_obj' and valid_objs'" in threadGet_vcg_corres_P)
       apply (rule allI, rule conseqPre, vcg)
       apply clarsimp
       apply (drule obj_at_ko_at', clarsimp)
       apply (drule spec, drule(1) mp, clarsimp)
       apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
       apply (drule(1) ko_at_valid_objs', simp add: projectKOs)
       apply (clarsimp simp: option_to_ptr_def option_to_0_def projectKOs
                             valid_obj'_def valid_tcb'_def)
      apply ceqv
     apply simp
     apply wpc
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip)
     apply (rule ccorres_cond_true)
     apply (ctac (no_vcg) add: doUnbindNotification_ccorres[simplified])
    apply (wp gbn_wp')
   apply vcg
  apply (clarsimp simp: option_to_ptr_def option_to_0_def pred_tcb_at'_def
                        obj_at'_weakenE[OF _ TrueI]
                 split: option.splits)
  apply (clarsimp simp: invs'_def valid_pspace'_def valid_state'_def)
  done


lemma unbindMaybeNotification_ccorres:
  "ccorres dc xfdc (invs') (UNIV \<inter> {s. ntfnPtr_' s = ntfn_Ptr ntfnptr}) []
        (unbindMaybeNotification ntfnptr) (Call unbindMaybeNotification_'proc)"
  supply option.case_cong[cong]
  apply (cinit lift: ntfnPtr_')
   apply (rule ccorres_symb_exec_l [OF _ get_ntfn_inv' _ empty_fail_getNotification])
    apply (rule ccorres_rhs_assoc2)
    apply (rule_tac P="ntfnBoundTCB ntfn \<noteq> None \<longrightarrow>
                         option_to_ctcb_ptr (ntfnBoundTCB ntfn) \<noteq> NULL"
             in ccorres_gen_asm)
    apply (rule_tac xf'=boundTCB_'
                and val="option_to_ctcb_ptr (ntfnBoundTCB ntfn)"
                and R="ko_at' ntfn ntfnptr and valid_bound_tcb' (ntfnBoundTCB ntfn)"
             in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply vcg
       apply clarsimp
       apply (erule cmap_relationE1[OF cmap_relation_ntfn])
        apply (erule ko_at_projectKO_opt)
       apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def)
      apply ceqv
     apply wpc
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip)
     apply (rule ccorres_cond_true)
     apply (rule ccorres_call[where xf'=xfdc])
        apply (rule doUnbindNotification_ccorres'[simplified])
       apply simp
      apply simp
     apply simp
    apply (clarsimp simp add: guard_is_UNIV_def option_to_ctcb_ptr_def )
   apply (wp getNotification_wp)
  apply (clarsimp )
  apply (frule (1) ko_at_valid_ntfn'[OF _ invs_valid_objs'])
  by (auto simp: valid_ntfn'_def valid_bound_tcb'_def obj_at'_def projectKOs
                      objBitsKO_def is_aligned_def option_to_ctcb_ptr_def tcb_at_not_NULL
             split: ntfn.splits)

lemma finaliseCap_True_cases_ccorres:
  "\<And>final. isEndpointCap cap \<or> isNotificationCap cap
             \<or> isReplyCap cap \<or> isDomainCap cap \<or> cap = NullCap \<Longrightarrow>
   ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (finaliseCap_ret_C.remainder_C rv')
                   \<and> ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
   ret__struct_finaliseCap_ret_C_'
   (invs') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. final_' s = from_bool final}
                        \<inter> {s. exposed_' s = from_bool flag \<comment> \<open>dave has name wrong\<close>}) []
   (finaliseCap cap final flag) (Call finaliseCap_'proc)"
  apply (subgoal_tac "\<not> isArchCap \<top> cap")
   prefer 2
   apply (clarsimp simp: isCap_simps)
  apply (cinit lift: cap_' final_' exposed_' cong: call_ignore_cong)
   apply csymbr
   apply (simp add: cap_get_tag_isCap Collect_False del: Collect_const)
   apply (fold case_bool_If)
   apply simp
   apply csymbr
   apply wpc
    apply (simp add: cap_get_tag_isCap ccorres_cond_univ_iff Let_def)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_split_nothrow_novcg)
        apply (simp add: when_def)
        apply (rule ccorres_cond2)
          apply (clarsimp simp: Collect_const_mem from_bool_0)
         apply csymbr
         apply (rule ccorres_call[where xf'=xfdc], rule cancelAllIPC_ccorres)
           apply simp
          apply simp
         apply simp
        apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
        apply (simp add: return_def, vcg)
       apply (rule ceqv_refl)
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_split_throws)
       apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                                 irq_opt_relation_def)
      apply vcg
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply wpc
    apply (simp add: cap_get_tag_isCap Let_def
                     ccorres_cond_empty_iff ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_split_nothrow_novcg)
        apply (simp add: when_def)
        apply (rule ccorres_cond2)
          apply (clarsimp simp: Collect_const_mem from_bool_0)
          apply (subgoal_tac "cap_get_tag capa = scast cap_notification_cap") prefer 2
          apply (clarsimp simp: ccap_relation_def isNotificationCap_def)
          apply (case_tac cap, simp_all)[1]
          apply (clarsimp simp: option_map_def split: option.splits)
          apply (drule (2) cap_to_H_NTFNCap_tag[OF sym])
         apply (rule ccorres_rhs_assoc)
         apply (rule ccorres_rhs_assoc)
         apply csymbr
         apply csymbr
         apply (ctac (no_vcg) add: unbindMaybeNotification_ccorres)
          apply (rule ccorres_call[where xf'=xfdc], rule cancelAllSignals_ccorres)
            apply simp
           apply simp
          apply simp
         apply (wp | wpc | simp add: guard_is_UNIV_def)+
        apply (rule ccorres_return_Skip')
       apply (rule ceqv_refl)
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_split_throws)
       apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                                 irq_opt_relation_def)
      apply vcg
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply wpc
    apply (simp add: cap_get_tag_isCap Let_def
                     ccorres_cond_empty_iff ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_split_throws)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                               irq_opt_relation_def)
    apply vcg
   apply wpc
    apply (simp add: cap_get_tag_isCap Let_def
                     ccorres_cond_empty_iff ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_split_throws)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp add: return_def ccap_relation_NullCap_iff)
     apply (clarsimp simp add: irq_opt_relation_def)
    apply vcg
   \<comment> \<open>NullCap case by exhaustion\<close>
   apply (simp add: cap_get_tag_isCap Let_def
                    ccorres_cond_empty_iff ccorres_cond_univ_iff)
   apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
          rule ccorres_split_throws)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                              irq_opt_relation_def)
   apply vcg
  apply (clarsimp simp: Collect_const_mem cap_get_tag_isCap)
  apply (rule TrueI conjI impI TrueI)+
   apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def isNotificationCap_def
                         isEndpointCap_def valid_obj'_def projectKOs valid_ntfn'_def
                         valid_bound_tcb'_def
                  dest!: obj_at_valid_objs')
  apply clarsimp
  apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
  apply clarsimp
  done

lemma finaliseCap_True_standin_ccorres:
  "\<And>final.
   ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (finaliseCap_ret_C.remainder_C rv')
                   \<and> ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
   ret__struct_finaliseCap_ret_C_'
   (invs') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. final_' s = from_bool final}
                        \<inter> {s. exposed_' s = from_bool True \<comment> \<open>dave has name wrong\<close>}) []
   (finaliseCapTrue_standin cap final) (Call finaliseCap_'proc)"
  unfolding finaliseCapTrue_standin_simple_def
  apply (case_tac "P :: bool" for P)
   apply (erule finaliseCap_True_cases_ccorres)
  apply (simp add: finaliseCap_def ccorres_fail')
  done

lemma offset_xf_for_sequence:
  "\<forall>s f. offset_' (offset_'_update f s) = f (offset_' s)
          \<and> globals (offset_'_update f s) = globals s"
  by simp

end

context begin interpretation Arch . (*FIXME: arch_split*)
crunch pde_mappings'[wp]: invalidateHWASIDEntry "valid_pde_mappings'"
end

context kernel_m begin


lemma invalidateASIDEntry_ccorres:
  "ccorres dc xfdc (\<lambda>s. valid_pde_mappings' s \<and> asid \<le> mask asid_bits)
      (UNIV \<inter> {s. asid_' s = asid}) []
      (invalidateASIDEntry asid) (Call invalidateASIDEntry_'proc)"
  apply (cinit lift: asid_')
   apply (ctac(no_vcg) add: loadHWASID_ccorres)
    apply csymbr
    apply (simp(no_asm) add: when_def del: Collect_const)
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (rule ccorres_cond2[where R=\<top>])
         apply (clarsimp simp: Collect_const_mem pde_stored_asid_def to_bool_def
                        split: if_split)
        apply csymbr
        apply (rule ccorres_Guard)+
        apply (rule_tac P="pde_stored_asid stored_hw_asid___struct_pde_C \<noteq> None" in ccorres_gen_asm)
        apply (ctac(no_simp) add: invalidateHWASIDEntry_ccorres)
        apply (clarsimp simp: pde_stored_asid_def unat_ucast
                       split: if_split_asm)
        apply (rule sym, rule nat_mod_eq')
        apply (simp add: pde_pde_invalid_lift_def pde_lift_def)
        apply (rule unat_less_power[where sz=8, simplified])
         apply (simp add: word_bits_conv)
        apply (rule order_le_less_trans, rule word_and_le1)
        apply (simp add: mask_def)
       apply (rule ccorres_return_Skip)
      apply (ctac add: invalidateASID_ccorres)
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply wp
  apply (clarsimp simp: Collect_const_mem pde_pde_invalid_lift_def pde_lift_def
                   order_le_less_trans[OF word_and_le1] mask_def)
  done

end

context begin interpretation Arch . (*FIXME: arch_split*)
crunch obj_at'[wp]: invalidateASIDEntry "obj_at' P p"
crunch obj_at'[wp]: flushSpace "obj_at' P p"
crunch valid_objs'[wp]: invalidateASIDEntry "valid_objs'"
crunch valid_objs'[wp]: flushSpace "valid_objs'"
crunch pde_mappings'[wp]: invalidateASIDEntry "valid_pde_mappings'"
crunch pde_mappings'[wp]: flushSpace "valid_pde_mappings'"
end

context kernel_m begin

lemma invs'_invs_no_cicd':
  "invs' s \<longrightarrow> all_invs_but_ct_idle_or_in_cur_domain' s"
  by (simp add: invs'_invs_no_cicd)

lemma deleteASIDPool_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>_. base < 2 ^ 17 \<and> pool \<noteq> 0))
      (UNIV \<inter> {s. asid_base_' s = base} \<inter> {s. pool_' s = Ptr pool}) []
      (deleteASIDPool base pool) (Call deleteASIDPool_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_base_' pool_' simp: whileAnno_def)
   apply (rule ccorres_assert)
   apply (clarsimp simp: liftM_def fun_upd_def[symmetric] when_def
               simp del: Collect_const)
   apply (rule ccorres_Guard)+
   apply (rule ccorres_pre_gets_armKSASIDTable_ksArchState)
   apply (rule_tac R="\<lambda>s. rv = armKSASIDTable (ksArchState s)" in ccorres_cond2)
     apply clarsimp
     apply (subst rf_sr_armKSASIDTable, assumption)
      apply (simp add: asid_high_bits_word_bits)
      apply (rule shiftr_less_t2n)
      apply (simp add: asid_low_bits_def asid_high_bits_def)
     apply (subst ucast_asid_high_bits_is_shift)
      apply (simp add: mask_def, simp add: asid_bits_def)
     apply (simp add: option_to_ptr_def option_to_0_def split: option.split)
    apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
    apply (rule ccorres_pre_getObject_asidpool)
    apply (rename_tac poolKO)
    apply (simp only: mapM_discarded)
    apply (rule ccorres_rhs_assoc2,
           rule ccorres_split_nothrow_novcg)
        apply (simp add: word_sle_def Kernel_C.asidLowBits_def Collect_True
                    del: Collect_const)
        apply (rule ccorres_semantic_equivD2[rotated])
         apply (simp only: semantic_equiv_def)
         apply (rule Seq_ceqv [OF ceqv_refl _ xpres_triv])
         apply (simp only: ceqv_Guard_UNIV)
         apply (rule While_ceqv [OF _ _ xpres_triv], rule impI, rule refl)
         apply (rule ceqv_remove_eqv_skip)
         apply (simp add: ceqv_Guard_UNIV ceqv_refl)
        apply (rule_tac F="\<lambda>n. ko_at' poolKO pool and valid_objs' and valid_pde_mappings'"
                    in ccorres_mapM_x_while_gen[OF _ _ _ _ _ offset_xf_for_sequence,
                                                where j=1, simplified])
            apply (intro allI impI)
            apply (rule ccorres_guard_imp2)
             apply (rule_tac xf'="offset_'" in ccorres_abstract, ceqv)
             apply (rule_tac P="rv' = of_nat n" in ccorres_gen_asm2)
             apply (rule ccorres_Guard[where F=ArrayBounds])
             apply (rule ccorres_move_c_guard_ap)
             apply (rule_tac R="ko_at' poolKO pool and valid_objs'" in ccorres_cond2)
               apply (clarsimp dest!: rf_sr_cpspace_asidpool_relation)
               apply (erule cmap_relationE1, erule ko_at_projectKO_opt)
               apply (clarsimp simp: casid_pool_relation_def typ_heap_simps
                                     inv_ASIDPool
                              split: asidpool.split_asm asid_pool_C.split_asm)
               apply (simp add: upto_enum_word  del: upt.simps)
               apply (drule(1) ko_at_valid_objs')
                apply (simp add: projectKOs)
               apply (clarsimp simp: array_relation_def valid_obj'_def
                                     ran_def)
               apply (drule_tac x="of_nat n" in spec)+
               apply (simp add: asid_low_bits_def word_le_nat_alt)
               apply (simp add: word_unat.Abs_inverse unats_def)
               apply (simp add: option_to_ptr_def option_to_0_def split: option.split_asm)
               apply clarsimp
              apply (ctac(no_vcg) add: flushSpace_ccorres)
               apply (ctac add: invalidateASIDEntry_ccorres)
              apply wp
             apply (rule ccorres_return_Skip)
            apply (clarsimp simp: Collect_const_mem)
            apply (simp add: upto_enum_word  typ_at_to_obj_at_arches
                             obj_at'_weakenE[OF _ TrueI]
                        del: upt.simps)
            apply (simp add: is_aligned_mask[symmetric])
            apply (rule conjI[rotated])
             apply (simp add: asid_low_bits_def word_of_nat_less)
            apply (clarsimp simp: mask_def)
            apply (erule is_aligned_add_less_t2n)
              apply (subst(asm) Suc_unat_diff_1)
               apply (simp add: asid_low_bits_def)
              apply (simp add: asid_low_bits_word_bits)
              apply (erule of_nat_less_pow_32 [OF _ asid_low_bits_word_bits])
             apply (simp add: asid_low_bits_def asid_bits_def)
            apply (simp add: asid_bits_def)
           apply (simp add: upto_enum_word )
          apply (vcg exspec=flushSpace_modifies exspec=invalidateASIDEntry_modifies)
          apply clarsimp
         apply (rule hoare_pre, wp)
         apply simp
        apply (simp add: upto_enum_word  asid_low_bits_def)
       apply ceqv
      apply (rule ccorres_move_const_guard)+
      apply (rule ccorres_split_nothrow_novcg_dc)
         apply (rule_tac P="\<lambda>s. rv = armKSASIDTable (ksArchState s)"
                      in ccorres_from_vcg[where P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: simpler_modify_def)
         apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                               carch_state_relation_def cmachine_state_relation_def
                               carch_globals_def h_t_valid_clift_Some_iff)
         apply (erule array_relation_update[unfolded fun_upd_def])
           apply (simp add: asid_high_bits_of_def unat_ucast asid_low_bits_def)
           apply (rule sym, rule nat_mod_eq')
           apply (rule order_less_le_trans, rule iffD1[OF word_less_nat_alt])
            apply (rule shiftr_less_t2n[where m=7])
            subgoal by simp
           subgoal by simp
          subgoal by (simp add: option_to_ptr_def option_to_0_def)
         subgoal by (simp add: asid_high_bits_def)
        apply (rule ccorres_pre_getCurThread)
        apply (ctac add: setVMRoot_ccorres)
       apply wp
      apply (simp add: guard_is_UNIV_def)
     apply (simp add: pred_conj_def fun_upd_def[symmetric]
                      cur_tcb'_def[symmetric])
     apply (strengthen invs'_invs_no_cicd', strengthen invs_asid_update_strg')
     apply (rule mapM_x_wp')
     apply (rule hoare_pre, wp)
     apply simp
    apply (simp add: guard_is_UNIV_def Kernel_C.asidLowBits_def
                     word_sle_def word_sless_def Collect_const_mem
                     mask_def asid_bits_def plus_one_helper
                     asid_shiftr_low_bits_less)
   apply (rule ccorres_return_Skip)
  apply (simp add: Kernel_C.asidLowBits_def
                   word_sle_def word_sless_def)
  apply (auto simp: asid_shiftr_low_bits_less Collect_const_mem
                    mask_def asid_bits_def plus_one_helper)
  done

lemma deleteASID_ccorres:
  "ccorres dc xfdc (invs' and K (asid < 2 ^ 17) and K (pdPtr \<noteq> 0))
      (UNIV \<inter> {s. asid_' s = asid} \<inter> {s. pd_' s = Ptr pdPtr}) []
      (deleteASID asid pdPtr) (Call deleteASID_'proc)"
  apply (cinit lift: asid_' pd_' cong: call_ignore_cong)
   apply (rule ccorres_Guard_Seq)+
   apply (rule_tac r'="\<lambda>rv rv'. case rv (ucast (asid_high_bits_of asid)) of
                                None \<Rightarrow> rv' = NULL
                              | Some v \<Rightarrow> rv' = Ptr v \<and> rv' \<noteq> NULL"
               and xf'="poolPtr_'" in ccorres_split_nothrow)
       apply (rule_tac P="invs' and K (asid < 2 ^ 17)"
                   and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: simpler_gets_def Let_def)
       apply (erule(1) getKSASIDTable_ccorres_stuff)
        apply (simp add: asid_high_bits_of_def
                         asidLowBits_def Kernel_C.asidLowBits_def
                         asid_low_bits_def unat_ucast)
        apply (rule sym, rule Divides.mod_less, simp)
        apply (rule unat_less_power[where sz=7, simplified])
         apply (simp add: word_bits_conv)
        apply (rule shiftr_less_t2n[where m=7, simplified])
        apply simp
       apply (rule order_less_le_trans, rule ucast_less)
        apply simp
       apply (simp add: asid_high_bits_def)
      apply ceqv
     apply csymbr
     apply wpc
      apply (simp add: ccorres_cond_iffs Collect_False
                  del: Collect_const
                 cong: call_ignore_cong)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip)
     apply (simp add: when_def Collect_True liftM_def
                cong: conj_cong call_ignore_cong
                 del: Collect_const)
     apply (rule ccorres_pre_getObject_asidpool)
     apply (rule ccorres_Guard_Seq[where F=ArrayBounds])
     apply (rule ccorres_move_c_guard_ap)
     apply (rule ccorres_Guard_Seq)+
     apply (rename_tac pool)
     apply (rule_tac xf'=ret__int_'
                 and val="from_bool (inv ASIDPool pool (asid && mask asid_low_bits)
                                            = Some pdPtr)"
                   and R="ko_at' pool x2 and K (pdPtr \<noteq> 0)"
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
        apply (vcg, clarsimp)
        apply (clarsimp dest!: rf_sr_cpspace_asidpool_relation)
        apply (erule(1) cmap_relation_ko_atE)
        apply (clarsimp simp: typ_heap_simps casid_pool_relation_def
                              array_relation_def
                       split: asidpool.split_asm asid_pool_C.split_asm)
        apply (drule_tac x="asid && mask asid_low_bits" in spec)
        apply (simp add: asid_low_bits_def Kernel_C.asidLowBits_def
                         mask_def word_and_le1)
        apply (drule sym, simp)
        apply (simp add: option_to_ptr_def option_to_0_def inv_ASIDPool
                  split: option.split if_split bool.split)
       apply ceqv
      apply (rule ccorres_cond2[where R=\<top>])
        apply (simp add: Collect_const_mem from_bool_0)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac (no_vcg) add: flushSpace_ccorres)
        apply (ctac (no_vcg) add: invalidateASIDEntry_ccorres)
         apply (rule ccorres_Guard_Seq[where F=ArrayBounds])
         apply (rule ccorres_move_c_guard_ap)
         apply (rule ccorres_Guard_Seq)+
         apply (rule ccorres_split_nothrow_novcg_dc)
            apply (rule_tac P="ko_at' pool x2" in ccorres_from_vcg[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (rule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                   assumption, erule ko_at_projectKO_opt)
            apply (rule bexI [OF _ setObject_eq],
                   simp_all add: objBits_simps archObjSize_def pageBits_def)[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps)
            apply (rule conjI)
             apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                   update_asidpool_map_tos
                                   update_asidpool_map_to_asidpools)
             apply (rule cmap_relation_updI, simp_all)[1]
             apply (simp add: casid_pool_relation_def fun_upd_def[symmetric]
                              inv_ASIDPool
                       split: asidpool.split_asm asid_pool_C.split_asm)
             apply (erule array_relation_update)
               subgoal by (simp add: mask_def)
              subgoal by (simp add: option_to_ptr_def option_to_0_def)
             subgoal by (simp add: asid_low_bits_def)
            subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                             carch_globals_def update_asidpool_map_tos
                             typ_heap_simps')
           apply (rule ccorres_pre_getCurThread)
           apply (ctac add: setVMRoot_ccorres)
          apply (simp add: cur_tcb'_def[symmetric])
          apply (strengthen invs'_invs_no_cicd')
          apply wp
         apply (clarsimp simp: rf_sr_def guard_is_UNIV_def
                               cstate_relation_def Let_def)
        apply wp[1]
       apply (simp add: fun_upd_def[symmetric])
       apply wp
      apply (rule ccorres_return_Skip)
     subgoal by (clarsimp simp: guard_is_UNIV_def Collect_const_mem
                           word_sle_def word_sless_def
                           Kernel_C.asidLowBits_def
                           asid_low_bits_def order_le_less_trans [OF word_and_le1])
    apply wp
   apply vcg
  apply (clarsimp simp: word_sless_def word_sle_def
                        Kernel_C.asidLowBits_def
                        typ_at_to_obj_at_arches)
  apply (rule conjI)
   apply (clarsimp simp: mask_def inv_ASIDPool
                  split: asidpool.split)
   apply (frule obj_at_valid_objs', clarsimp+)
   apply (clarsimp simp: asid_bits_def typ_at_to_obj_at_arches
                         obj_at'_weakenE[OF _ TrueI]
                         fun_upd_def[symmetric] valid_obj'_def
                         projectKOs invs_valid_pde_mappings'
                         invs_cur')
   apply (rule conjI, blast)
   subgoal by (fastforce simp: inv_into_def ran_def  split: if_split_asm)
  by (clarsimp simp: order_le_less_trans [OF word_and_le1]
                        asid_shiftr_low_bits_less asid_bits_def mask_def
                        plus_one_helper arg_cong[where f="\<lambda>x. 2 ^ x", OF meta_eq_to_obj_eq, OF asid_low_bits_def]
                 split: option.split_asm)

lemma setObject_ccorres_lemma:
  fixes val :: "'a :: pspace_storable" shows
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> (Q s) c {s'. (s \<lparr> ksPSpace := ksPSpace s (ptr \<mapsto> injectKO val) \<rparr>, s') \<in> rf_sr},{};
     \<And>s s' val (val' :: 'a). \<lbrakk> ko_at' val' ptr s; (s, s') \<in> rf_sr \<rbrakk>
           \<Longrightarrow> s' \<in> Q s;
     \<And>val :: 'a. updateObject val = updateObject_default val;
     \<And>val :: 'a. (1 :: word32) < 2 ^ objBits val;
     \<And>(val :: 'a) (val' :: 'a). objBits val = objBits val';
     \<Gamma> \<turnstile> Q' c UNIV \<rbrakk>
    \<Longrightarrow> ccorres dc xfdc \<top> Q' hs
             (setObject ptr val) c"
  apply (rule ccorres_from_vcg_nofail)
  apply (rule allI)
  apply (case_tac "obj_at' (\<lambda>x :: 'a. True) ptr \<sigma>")
   apply (rule_tac P'="Q \<sigma>" in conseqPre, rule conseqPost, assumption)
     apply clarsimp
     apply (rule bexI [OF _ setObject_eq], simp+)
   apply (drule obj_at_ko_at')
   apply clarsimp
  apply clarsimp
  apply (rule conseqPre, erule conseqPost)
    apply clarsimp
    apply (subgoal_tac "fst (setObject ptr val \<sigma>) = {}")
     apply simp
     apply (erule notE, erule_tac s=\<sigma> in empty_failD[rotated])
     apply (simp add: setObject_def split_def empty_fail_cond)
    apply (rule ccontr)
    apply (clarsimp elim!: nonemptyE)
    apply (frule use_valid [OF _ obj_at_setObject3[where P=\<top>]], simp_all)[1]
    apply (simp add: typ_at_to_obj_at'[symmetric])
    apply (frule(1) use_valid [OF _ setObject_typ_at'])
    apply simp
   apply simp
  apply clarsimp
  done

lemma findPDForASID_nonzero:
  "\<lbrace>\<top>\<rbrace> findPDForASID asid \<lbrace>\<lambda>rv s. rv \<noteq> 0\<rbrace>,-"
  apply (simp add: findPDForASID_def cong: option.case_cong)
  apply (wp | wpc | simp only: o_def simp_thms)+
  done


lemma pageTableMapped_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = option_to_ptr rv \<and> rv \<noteq> Some 0) ret__ptr_to_struct_pde_C_'
           (invs' and K (asid \<le> mask asid_bits))
           (UNIV \<inter> {s. asid_' s = asid} \<inter> {s. vaddr_' s = vaddr} \<inter> {s. pt_' s = Ptr ptPtr}) []
      (pageTableMapped asid vaddr ptPtr) (Call pageTableMapped_'proc)"
  apply (cinit lift: asid_' vaddr_' pt_')
   apply (simp add: ignoreFailure_def catch_def
                    bindE_bind_linearise liftE_def
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_split_nothrow_novcg_case_sum)
         apply clarsimp
         apply (ctac (no_vcg) add: findPDForASID_ccorres)
        apply ceqv
       apply (simp add: Collect_False del: Collect_const cong: call_ignore_cong)
       apply csymbr
       apply (rule_tac xf'=pde_' and r'=cpde_relation in ccorres_split_nothrow_novcg)
           apply (rule ccorres_add_return2, rule ccorres_pre_getObject_pde)
           apply (rule ccorres_move_array_assertion_pd
             | (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_pd))+
           apply (rule_tac P="ko_at' x (lookup_pd_slot rv vaddr) and no_0_obj'
                            and page_directory_at' rv"
                         in ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def lookup_pd_slot_def Let_def)
           apply (drule(1) page_directory_at_rf_sr)
           apply (erule cmap_relationE1[OF rf_sr_cpde_relation],
                  erule ko_at_projectKO_opt)
           apply (clarsimp simp: typ_heap_simps' shiftl_t2n field_simps table_bits_defs)
          apply ceqv
         apply (rule_tac P="rv \<noteq> 0" in ccorres_gen_asm)
         apply csymbr+
         apply (wpc, simp_all add: if_1_0_0 returnOk_bind throwError_bind
                              del: Collect_const)
            prefer 2
            apply (rule ccorres_cond_true_seq)
            apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: if_1_0_0 cpde_relation_def Let_def
                                  return_def addrFromPPtr_def
                                  pde_pde_coarse_lift_def)
            apply (rule conjI)
             apply (simp add: pde_lift_def Let_def split: if_split_asm)
            apply (clarsimp simp: option_to_0_def option_to_ptr_def split: if_split)
            apply (clarsimp simp: ARM_HYP.addrFromPPtr_def ARM_HYP.ptrFromPAddr_def)
           apply ((rule ccorres_cond_false_seq ccorres_cond_false
                          ccorres_return_C | simp)+)[3]
        apply (simp only: simp_thms)
        apply wp
       apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem if_1_0_0)
       apply (simp add: cpde_relation_def Let_def pde_lift_def
                 split: if_split_asm,
              auto simp: option_to_0_def option_to_ptr_def pde_tag_defs)[1]
      apply simp
      apply (rule ccorres_split_throws)
       apply (rule ccorres_return_C, simp+)
      apply vcg
     apply (wp hoare_drop_imps findPDForASID_nonzero)
    apply (simp add: guard_is_UNIV_def word_sle_def table_bits_defs
                     unat_gt_0 unat_shiftr_le_bound)
   apply (simp add: guard_is_UNIV_def option_to_0_def option_to_ptr_def)
  apply auto[1]
  done

lemma pageTableMapped_pd:
  "\<lbrace>\<top>\<rbrace> pageTableMapped asid vaddr ptPtr
   \<lbrace>\<lambda>rv s. case rv of Some x \<Rightarrow> page_directory_at' x s | _ \<Rightarrow> True\<rbrace>"
  apply (simp add: pageTableMapped_def)
  apply (rule hoare_pre)
   apply (wp getPDE_wp hoare_vcg_all_lift_R | wpc)+
   apply (rule hoare_post_imp_R, rule findPDForASID_page_directory_at'_simple)
   apply (clarsimp split: if_split)
  apply simp
  done

lemma unmapPageTable_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. asid \<le> mask asid_bits \<and> vaddr < pptrBase))
      (UNIV \<inter> {s. asid_' s = asid} \<inter> {s. vaddr_' s = vaddr} \<inter> {s. pt_' s = Ptr ptPtr}) []
      (unmapPageTable asid vaddr ptPtr) (Call unmapPageTable_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_' vaddr_' pt_')
   apply (ctac(no_vcg) add: pageTableMapped_ccorres)
    apply wpc
     apply (simp add: option_to_ptr_def option_to_0_def ccorres_cond_iffs)
     apply (rule ccorres_return_Skip)
    apply (simp add: option_to_ptr_def option_to_0_def ccorres_cond_iffs)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply (rule ccorres_move_array_assertion_pd)
    apply csymbr
    apply csymbr
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (rule storePDE_Basic_ccorres)
       apply (simp add: cpde_relation_def Let_def pde_lift_pde_invalid)
      apply csymbr
      apply (ctac add: cleanByVA_PoU_ccorres)
        apply (ctac(no_vcg) add:flushTable_ccorres)
       apply wp
      apply (vcg exspec=cleanByVA_PoU_modifies)
     apply wp
    apply (fastforce simp: guard_is_UNIV_def Collect_const_mem Let_def
      shiftl_t2n field_simps lookup_pd_slot_def table_bits_defs)
   apply (rule_tac Q="\<lambda>rv s. (case rv of Some pd \<Rightarrow> page_directory_at' pd s | _ \<Rightarrow> True) \<and> invs' s"
             in hoare_post_imp)
    apply (clarsimp simp: lookup_pd_slot_def Let_def
                          mask_add_aligned less_pptrBase_valid_pde_offset''
                          page_directory_at'_def table_bits_defs)
   apply (wp pageTableMapped_pd)
  apply (clarsimp simp: word_sle_def lookup_pd_slot_def
                        Let_def shiftl_t2n field_simps
                        Collect_const_mem table_bits_defs)
  apply (simp add: unat_shiftr_le_bound unat_eq_0)
  done

lemma return_Null_ccorres:
  "ccorres ccap_relation ret__struct_cap_C_'
   \<top> UNIV (SKIP # hs)
   (return NullCap) (\<acute>ret__struct_cap_C :== CALL cap_null_cap_new()
                       ;; return_C ret__struct_cap_C_'_update ret__struct_cap_C_')"
  apply (rule ccorres_from_vcg_throws)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp add: ccap_relation_NullCap_iff return_def)
  done

lemma no_0_pd_at'[elim!]:
  "\<lbrakk> page_directory_at' 0 s; no_0_obj' s \<rbrakk> \<Longrightarrow> P"
  apply (clarsimp simp: page_directory_at'_def)
  apply (drule spec[where x=0], clarsimp)
  done

lemma isFinalCapability_ccorres:
  "ccorres ((=) \<circ> from_bool) ret__unsigned_long_'
   (cte_wp_at' ((=) cte) slot and invs')
   (UNIV \<inter> {s. cte_' s = Ptr slot}) []
   (isFinalCapability cte) (Call isFinalCapability_'proc)"
  apply (cinit lift: cte_')
   apply (rule ccorres_Guard_Seq)
   apply (simp add: Let_def del: Collect_const)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'="mdb_'" in ccorres_abstract)
      apply ceqv
     apply (rule_tac P="mdb_node_to_H (mdb_node_lift rv') = cteMDBNode cte" in ccorres_gen_asm2)
     apply csymbr
     apply (rule_tac r'="(=) \<circ> from_bool" and xf'="prevIsSameObject_'"
               in ccorres_split_nothrow_novcg)
         apply (rule ccorres_cond2[where R=\<top>])
           apply (clarsimp simp: Collect_const_mem nullPointer_def)
           apply (simp add: mdbPrev_to_H[symmetric])
          apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (simp add: return_def)
         apply (rule ccorres_rhs_assoc)+
         apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_wp empty_fail_getCTE])
         apply (rule_tac P="cte_wp_at' ((=) cte) slot
                             and cte_wp_at' ((=) rv) (mdbPrev (cteMDBNode cte))
                             and valid_cap' (cteCap rv)
                             and K (capAligned (cteCap cte) \<and> capAligned (cteCap rv))"
                    and P'=UNIV in ccorres_from_vcg)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def mdbPrev_to_H[symmetric])
         apply (simp add: rf_sr_cte_at_validD)
         apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (rule cmap_relationE1 [OF cmap_relation_cte], assumption+,
                    simp?, simp add: typ_heap_simps)+
         apply (drule ccte_relation_ccap_relation)+
         apply (rule exI, rule conjI, assumption)+
         apply (auto)[1]
        apply ceqv
       apply (clarsimp simp del: Collect_const)
       apply (rule ccorres_cond2[where R=\<top>])
         apply (simp add: from_bool_0 Collect_const_mem)
        apply (rule ccorres_return_C, simp+)[1]
       apply csymbr
       apply (rule ccorres_cond2[where R=\<top>])
         apply (simp add: nullPointer_def Collect_const_mem mdbNext_to_H[symmetric])
        apply (rule ccorres_return_C, simp+)[1]
       apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_wp empty_fail_getCTE])
       apply (rule_tac P="cte_wp_at' ((=) cte) slot
                           and cte_wp_at' ((=) rva) (mdbNext (cteMDBNode cte))
                           and K (capAligned (cteCap rva) \<and> capAligned (cteCap cte))
                           and valid_cap' (cteCap cte)"
                  and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def from_bool_eq_if from_bool_0
                             mdbNext_to_H[symmetric] rf_sr_cte_at_validD)
       apply (clarsimp simp: cte_wp_at_ctes_of split: if_split)
       apply (rule cmap_relationE1 [OF cmap_relation_cte], assumption+,
                  simp?, simp add: typ_heap_simps)+
       apply (drule ccte_relation_ccap_relation)+
       apply (auto simp: from_bool_def split: bool.splits)[1]
      apply (wp getCTE_wp')
     apply (clarsimp simp add: guard_is_UNIV_def Collect_const_mem)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: Collect_const_mem)
  apply (frule(1) rf_sr_cte_at_validD, simp add: typ_heap_simps)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
  apply (simp add: typ_heap_simps)
  apply (clarsimp simp add: ccte_relation_def map_option_Some_eq2)
  by (auto,
         auto dest!: ctes_of_valid' [OF _ invs_valid_objs']
              elim!: valid_capAligned)

lemmas cleanup_info_wf'_simps[simp] = cleanup_info_wf'_def[split_simps capability.split]

lemma cteDeleteOne_ccorres:
  "ccorres dc xfdc
   (invs' and cte_wp_at' (\<lambda>ct. w = -1 \<or> cteCap ct = NullCap
        \<or> (\<forall>cap'. ccap_relation (cteCap ct) cap' \<longrightarrow> cap_get_tag cap' = w)) slot)
   ({s. gs_get_assn cteDeleteOne_'proc (ghost'state_' (globals s)) = w}
        \<inter> {s. slot_' s = Ptr slot}) []
   (cteDeleteOne slot) (Call cteDeleteOne_'proc)"
  unfolding cteDeleteOne_def
  apply (rule ccorres_symb_exec_l'
                [OF _ getCTE_inv getCTE_sp empty_fail_getCTE])
  apply (cinit' lift: slot_' cong: call_ignore_cong)
   apply (rule ccorres_move_c_guard_cte)
   apply csymbr
   apply (rule ccorres_abstract_cleanup)
   apply csymbr
   apply (rule ccorres_gen_asm2,
          erule_tac t="ret__unsigned = scast cap_null_cap"
                and s="cteCap cte = NullCap"
                 in ssubst)
   apply (clarsimp simp only: when_def unless_def)
   apply (rule ccorres_cond2[where R=\<top>])
     apply (clarsimp simp: Collect_const_mem)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (rule ccorres_Guard_Seq)
    apply (rule ccorres_basic_srnoop)
      apply (ctac(no_vcg) add: isFinalCapability_ccorres[where slot=slot])
       apply (rule_tac A="invs'  and cte_wp_at' ((=) cte) slot"
                     in ccorres_guard_imp2[where A'=UNIV])
        apply (simp add: split_def del: Collect_const)
        apply (rule ccorres_move_c_guard_cte)
        apply (ctac(no_vcg) add: finaliseCap_True_standin_ccorres)
         apply (rule ccorres_assert)
         apply simp
         apply csymbr
         apply (ctac add: emptySlot_ccorres)
        apply (simp add: pred_conj_def finaliseCapTrue_standin_simple_def)
        apply (strengthen invs_mdb_strengthen' invs_urz)
        apply (wp typ_at_lifts isFinalCapability_inv
            | strengthen invs_valid_objs')+
       apply (clarsimp simp: irq_opt_relation_def invs_pspace_aligned' cte_wp_at_ctes_of)
       apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
       apply (clarsimp simp: typ_heap_simps ccte_relation_ccap_relation ccap_relation_NullCap_iff)
      apply (wp isFinalCapability_inv)
     apply simp
    apply (simp del: Collect_const)
   apply (rule ccorres_return_Skip)
  apply (clarsimp simp: Collect_const_mem cte_wp_at_ctes_of)
  apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
  apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap
                 dest!: ccte_relation_ccap_relation)
  apply (auto simp: o_def)
  done


lemma getIRQSlot_ccorres_stuff:
  "\<lbrakk> (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow>
   CTypesDefs.ptr_add intStateIRQNode_Ptr (uint (irq :: 10 word))
     = Ptr (irq_node' s + 2 ^ cte_level_bits * ucast irq)"
  apply (clarsimp simp add: rf_sr_def cstate_relation_def Let_def
                            cinterrupt_relation_def)
  apply (simp add: objBits_simps cte_level_bits_def
                   size_of_def mult.commute mult.left_commute of_int_uint_ucast )
  done

lemma deletingIRQHandler_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
                   (UNIV \<inter> {s. irq_opt_relation (Some irq) (irq_' s)}) []
   (deletingIRQHandler irq) (Call deletingIRQHandler_'proc)"
  apply (cinit lift: irq_' cong: call_ignore_cong)
   apply (clarsimp simp: irq_opt_relation_def ptr_add_assertion_def
                   cong: call_ignore_cong )
   apply (rule_tac r'="\<lambda>rv rv'. rv' = Ptr rv"
                and xf'="slot_'" in ccorres_split_nothrow)
       apply (rule ccorres_Guard_intStateIRQNode_array_Ptr)
       apply (rule ccorres_move_array_assertion_irq)
       apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])

       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: getIRQSlot_def liftM_def getInterruptState_def
                             locateSlot_conv)
       apply (simp add: bind_def simpler_gets_def return_def getIRQSlot_ccorres_stuff[simplified])
      apply ceqv
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_symb_exec_l)
           apply (rule ccorres_symb_exec_r)
             apply (ctac add: cteDeleteOne_ccorres[where w="scast cap_notification_cap"])
            apply vcg
           apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
                gs_set_assn_Delete_cstate_relation[unfolded o_def])
          apply (wp getCTE_wp' | simp add: getSlotCap_def getIRQSlot_def locateSlot_conv
                                           getInterruptState_def)+
   apply vcg
  apply (clarsimp simp: cap_get_tag_isCap ghost_assertion_data_get_def
                        ghost_assertion_data_set_def)
  apply (simp add: cap_tag_defs)
  apply (clarsimp simp: cte_wp_at_ctes_of Collect_const_mem
                        irq_opt_relation_def Kernel_C.maxIRQ_def)
  apply (drule word_le_nat_alt[THEN iffD1])
  apply (clarsimp simp: uint_0_iff unat_gt_0 uint_up_ucast is_up)
  done

lemma Zombie_new_spec:
  "\<forall>s. \<Gamma>\<turnstile> ({s} \<inter> {s. type_' s = 32 \<or> type_' s < 31}) Call Zombie_new_'proc
          {s'. cap_zombie_cap_lift (ret__struct_cap_C_' s') =
                \<lparr> capZombieID_CL = \<^bsup>s\<^esup>ptr && ~~ mask (if \<^bsup>s\<^esup>type = (1 << 5) then 5 else unat (\<^bsup>s\<^esup>type + 1))
                                    || \<^bsup>s\<^esup>number___unsigned_long && mask (if \<^bsup>s\<^esup>type = (1 << 5) then 5 else unat (\<^bsup>s\<^esup>type + 1)),
                  capZombieType_CL = \<^bsup>s\<^esup>type && mask 6 \<rparr>
               \<and> cap_get_tag (ret__struct_cap_C_' s') = scast cap_zombie_cap}"
  apply vcg
  apply (clarsimp simp: word_sle_def)
  apply (simp add: mask_def word_log_esimps[where 'a=32, simplified])
  apply clarsimp
  apply (simp add: word_add_less_mono1[where k=1 and j="0x1F", simplified])
  done


lemma irq_opt_relation_Some_ucast:
  "\<lbrakk> x && mask 10 = x; ucast x \<le> (ucast Kernel_C.maxIRQ :: 10 word) \<or> x \<le> (ucast Kernel_C.maxIRQ :: machine_word) \<rbrakk>
    \<Longrightarrow> irq_opt_relation (Some (ucast x)) (ucast ((ucast x):: 10 word))"
  using ucast_ucast_mask[where x=x and 'a=10, symmetric]
  apply (simp add: irq_opt_relation_def)
  apply (rule conjI, clarsimp simp: minus_one_norm irqInvalid_def Kernel_C.maxIRQ_def)
  apply (simp only: unat_arith_simps)
  by (clarsimp simp: word_le_nat_alt Kernel_C.maxIRQ_def)

lemmas upcast_ucast_id = More_Word.ucast_up_inj

lemma irq_opt_relation_Some_ucast':
  "\<lbrakk> x && mask 10 = x; ucast x \<le> (ucast Kernel_C.maxIRQ :: 10 word) \<or> x \<le> (ucast Kernel_C.maxIRQ :: machine_word) \<rbrakk>
    \<Longrightarrow> irq_opt_relation (Some (ucast x)) (ucast x)"
  apply (rule_tac P = "%y. irq_opt_relation (Some (ucast x)) y" in subst[rotated])
  apply (rule irq_opt_relation_Some_ucast[rotated]; simp)
  apply word_eqI_solve
  done

lemma irq_opt_relation_Some_ucast_left:
  "\<lbrakk> x && mask 10 = x; ucast x \<le> (ucast Kernel_C.maxIRQ :: 10 word) \<or> x \<le> (ucast Kernel_C.maxIRQ :: machine_word) \<rbrakk>
    \<Longrightarrow> irq_opt_relation (Some (ucast x)) x"
  apply (rule_tac P = "%y. irq_opt_relation (Some (ucast x)) y" in subst[rotated])
  apply (rule irq_opt_relation_Some_ucast[rotated]; simp)
  apply word_eqI_solve
  done

lemma ccap_relation_IRQHandler_mask:
  "\<lbrakk> ccap_relation acap ccap; isIRQHandlerCap acap \<rbrakk>
    \<Longrightarrow> capIRQ_CL (cap_irq_handler_cap_lift ccap) && mask 10
        = capIRQ_CL (cap_irq_handler_cap_lift ccap)"
  apply (simp only: cap_get_tag_isCap[symmetric])
  apply (drule ccap_relation_c_valid_cap)
  apply (simp add: c_valid_cap_def cap_irq_handler_cap_lift cl_valid_cap_def)
  done

(* FIXME ARMHYP MOVE to LevityCatch_C *)
lemma option_to_ctcb_ptr_not_0:
  "\<lbrakk> tcb_at' p s; option_to_ctcb_ptr v = tcb_ptr_to_ctcb_ptr p\<rbrakk> \<Longrightarrow> v = Some p"
  apply (clarsimp simp: option_to_ctcb_ptr_def tcb_ptr_to_ctcb_ptr_def
                  split: option.splits)
  apply (frule tcb_aligned')
  apply (frule_tac y=ctcb_offset and n=tcbBlockSizeBits in aligned_offset_non_zero)
    apply (clarsimp simp: ctcb_offset_defs objBits_defs)+
  done

lemma update_tcb_map_to_tcb:
  "map_to_tcbs (ksPSpace s(p \<mapsto> KOTCB tcb))
             = (map_to_tcbs (ksPSpace s))(p \<mapsto> tcb)"
  by (rule ext, clarsimp simp: projectKOs map_comp_def split: if_split)

lemma ep_queue_relation_shift2:
  "(option_map2 tcbEPNext_C (f (cslift s))
         = option_map2 tcbEPNext_C (cslift s)
    \<and> option_map2 tcbEPPrev_C (f (cslift s))
         = option_map2 tcbEPPrev_C (cslift s))
     \<Longrightarrow> ep_queue_relation (f (cslift s)) ts qPrev qHead
          = ep_queue_relation (cslift s) ts qPrev qHead"
  apply clarsimp
  apply (induct ts arbitrary: qPrev qHead)
   apply simp
  apply simp
  apply (simp add: option_map2_def fun_eq_iff
                   map_option_case)
  apply (drule_tac x=qHead in spec)+
  apply (clarsimp split: option.split_asm)
  done

lemma sched_queue_relation_shift:
  "(option_map2 tcbSchedNext_C (f (cslift s))
         = option_map2 tcbSchedNext_C (cslift s)
    \<and> option_map2 tcbSchedPrev_C (f (cslift s))
         = option_map2 tcbSchedPrev_C (cslift s))
     \<Longrightarrow>  sched_queue_relation (f (cslift s)) ts qPrev qHead
          =  sched_queue_relation (cslift s) ts qPrev qHead"
  apply clarsimp
  apply (induct ts arbitrary: qPrev qHead)
   apply simp
  apply simp
  apply (simp add: option_map2_def fun_eq_iff
                   map_option_case)
  apply (drule_tac x=qHead in spec)+
  apply (clarsimp split: option.split_asm)
  done

lemma cendpoint_relation_udpate_arch:
  "\<lbrakk> cslift x p = Some tcb ; cendpoint_relation (cslift x) v v' \<rbrakk>
    \<Longrightarrow> cendpoint_relation (cslift x(p \<mapsto> tcbArch_C_update f tcb)) v v'"
  apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def
                  split: endpoint.splits)
   apply (subst ep_queue_relation_shift2; simp add: fun_eq_iff)
   apply (safe ; case_tac "xa = p" ; clarsimp simp: option_map2_def map_option_case)
  apply (subst ep_queue_relation_shift2; simp add: fun_eq_iff)
  apply (safe ; case_tac "xa = p" ; clarsimp simp: option_map2_def map_option_case)
  done

lemma cnotification_relation_udpate_arch:
  "\<lbrakk> cslift x p = Some tcb ;  cnotification_relation (cslift x) v v' \<rbrakk>
    \<Longrightarrow>  cnotification_relation (cslift x(p \<mapsto> tcbArch_C_update f tcb)) v v'"
  apply (clarsimp simp: cnotification_relation_def Let_def tcb_queue_relation'_def
                  split: notification.splits ntfn.splits)
  apply (subst ep_queue_relation_shift2; simp add: fun_eq_iff)
  apply (safe ; case_tac "xa = p" ; clarsimp simp: option_map2_def map_option_case)
  done

lemma archThreadSet_tcbVCPU_Basic_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
                    (archThreadSet (atcbVCPUPtr_update (\<lambda>_. vcpuptr)) tptr)
     ((Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (Ptr &((atcb_Ptr &(tcb_ptr_to_ctcb_ptr tptr\<rightarrow>[''tcbArch_C'']))\<rightarrow>[''tcbVCPU_C'']))
                                         (option_to_ptr vcpuptr :: vcpu_C ptr)))) s)))"
  apply (simp add: archThreadSet_def)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getObject_tcb)
   apply (rule_tac P="tcb_at' tptr and ko_at' tcb tptr" and P'=UNIV in setObject_ccorres_helper)
     apply (simp_all add: objBits_simps' archObjSize_def pageBits_def obj_tcb_at')
  apply (rule conseqPre, vcg, clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_tcb], assumption, erule ko_at_projectKO_opt)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def update_tcb_map_tos
                        typ_heap_simps' cpspace_relation_def update_tcb_map_tos)
   apply (safe ; (clarsimp simp: cpspace_relation_def typ_heap_simps
                                 carch_state_relation_def Let_def
                                 update_tcb_map_to_tcb
                                 cmachine_state_relation_def
                                 update_tcb_map_tos)?)
      apply (subst map_to_ctes_upd_tcb_no_ctes; simp add: tcb_cte_cases_def)
     apply (erule cmap_relation_updI, erule ko_at_projectKO_opt, simp+)
      apply (clarsimp simp: ctcb_relation_def carch_tcb_relation_def ccontext_relation_def atcbContextGet_def)
     apply clarsimp
    apply (rule cmap_relation_rel_upd[OF _ cendpoint_relation_udpate_arch], simp+)
    apply (rule cmap_relation_rel_upd[OF _ cnotification_relation_udpate_arch], simp+)
      apply (clarsimp simp add: cready_queues_relation_def Let_def tcb_queue_relation'_def)
   apply (subst sched_queue_relation_shift; simp add: fun_eq_iff)
   apply (safe ; case_tac "xa = tcb_ptr_to_ctcb_ptr tptr" ; clarsimp simp: option_map2_def map_option_case)
    apply (clarsimp simp: cvariable_relation_upd_const)
  done

(* MOVE *)
lemma update_vcpu_map_to_vcpu:
  "map_to_vcpus (ksPSpace s(p \<mapsto> KOArch (KOVCPU vcpu)))
             = (map_to_vcpus (ksPSpace s))(p \<mapsto> vcpu)"
  by (rule ext, clarsimp simp: projectKOs map_comp_def split: if_split)

lemma setObject_vcpuTCB_updated_Basic_ccorres:
  "ccorres dc xfdc (ko_at' (vcpuTCBPtr_update t vcpu) vcpuptr) UNIV hs
                    (setObject vcpuptr (vcpuTCBPtr_update (\<lambda>_. tptr) vcpu))
     ((Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vcpuTCB_C'']))
                                         ( option_to_ctcb_ptr tptr :: tcb_C ptr)))) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule_tac P="ko_at' (vcpuTCBPtr_update t vcpu) vcpuptr" and P'=UNIV in setObject_ccorres_helper)
     apply (simp_all add: objBits_simps archObjSize_def pageBits_def obj_tcb_at' vcpuBits_def vcpu_bits_def)
  apply (rule conseqPre, vcg, clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_vcpu], assumption, erule ko_at_projectKO_opt)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps'
                        cpspace_relation_def update_vcpu_map_tos)
  apply (safe ; (clarsimp simp: cpspace_relation_def typ_heap_simps carch_state_relation_def Let_def
                                 update_vcpu_map_to_vcpu cmachine_state_relation_def update_vcpu_map_tos)?)
  apply (erule cmap_relation_updI, erule ko_at_projectKO_opt, simp+)
   apply (clarsimp simp add: cvcpu_relation_def cvcpu_vppi_masked_relation_def option_to_ctcb_ptr_def
                             cvcpu_regs_relation_def Let_def vcpuSCTLR_def)
  apply simp
  done

lemma vcpuTCBPtr_update_trivial: "vcpuTCBPtr_update id vcpu = vcpu"
  apply (cases vcpu)
  apply clarsimp
  done

lemmas  setObject_vcpuTCB_Basic_ccorres =
  setObject_vcpuTCB_updated_Basic_ccorres[where t=id, simplified vcpuTCBPtr_update_trivial]

lemma modify_armHSCurVCPU_split:
  "modifyArchState (armHSCurVCPU_update (\<lambda>_. p)) = do modifyArchState (armHSCurVCPU_update f);
                                                      modifyArchState (armHSCurVCPU_update (\<lambda>_. p))
                                                   od"
  apply (clarsimp simp: modifyArchState_def modify_modify)
  apply (rule ext)
  apply (rule_tac f="\<lambda>t. modify t s" for s in arg_cong)
  apply (rule ext)
  apply (case_tac "ksArchState s")
  apply clarsimp
  done

lemma modify_armHSCurVCPU_when_split:
  "modifyArchState (armHSCurVCPU_update (\<lambda>_. p)) = do when P (modifyArchState (armHSCurVCPU_update f));
                                                      modifyArchState (armHSCurVCPU_update (\<lambda>_. p))
                                                   od"
  apply (cases P; clarsimp)
  apply (subst modify_armHSCurVCPU_split[of _ f])
  apply simp
  done

lemma modifyArchState_armHSCurVCPU_Skip:
  "ccorres dc xfdc (\<lambda>s. armHSCurVCPU (ksArchState s) = curvcpu) UNIV hs (modifyArchState (armHSCurVCPU_update (\<lambda>_. curvcpu))) SKIP"
  apply (clarsimp simp: modifyArchState_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: simpler_gets_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: carch_state_relation_def carch_globals_def cur_vcpu_relation_def)
  done

(* FIX ARMHYP MOVE *)
lemma armHSCurVCPU_update_active_false_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
      (modifyArchState (armHSCurVCPU_update (case_option None (\<lambda>(a, _). Some (a, False)))))
      (Basic (\<lambda>s. globals_update (armHSVCPUActive_'_update (\<lambda>_. scast false)) s))"
  apply (clarsimp simp: modifyArchState_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_gets_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: cmachine_state_relation_def)
  apply (clarsimp simp: carch_state_relation_def carch_globals_def cur_vcpu_relation_def)
  apply (case_tac "armHSCurVCPU (ksArchState \<sigma>)"; clarsimp)
  done

lemma armHSCurVCPU_update_curv_Null_ccorres:
  "ccorres dc xfdc (\<lambda>s. case armHSCurVCPU (ksArchState s) of None \<Rightarrow> True | Some (a,b) \<Rightarrow> \<not> b) UNIV hs
    (modifyArchState (armHSCurVCPU_update Map.empty))
    (Basic (\<lambda>s. globals_update (armHSCurVCPU_'_update (\<lambda>_. NULL)) s))"
  apply (clarsimp simp: modifyArchState_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_gets_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: carch_state_relation_def carch_globals_def cur_vcpu_relation_def
                        cmachine_state_relation_def
                 split: bool.split option.splits)
  done

lemma vcpuInvalidateActive_ccorres:
  "ccorres dc xfdc invs' UNIV hs
           vcpuInvalidateActive
           (Call vcpu_invalidate_active_'proc)"
  apply cinit
   apply (rule ccorres_pre_getCurVCPU)
        apply (subst modify_armHSCurVCPU_when_split)
   apply (subst bind_assoc[symmetric])
   apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
    apply (rule_tac Q="\<lambda>s. (armHSCurVCPU \<circ> ksArchState) s = hsCurVCPU"
                   and Q'=UNIV
                   and C'="{s. \<exists> t. hsCurVCPU =  Some t \<and> snd t}"
                   in ccorres_rewrite_cond_sr)
        apply clarsimp
        apply (frule rf_sr_ksArchState_armHSCurVCPU)
        apply (case_tac "\<exists> t. (armHSCurVCPU \<circ> ksArchState) s =  Some t \<and> snd t")
         apply (clarsimp simp: cur_vcpu_relation_def)
        apply (clarsimp simp: cur_vcpu_relation_def)
        apply (case_tac "(armHSCurVCPU \<circ> ksArchState) s"; clarsimp)
       apply (rule_tac a=" _ >>= (\<lambda>_. when (hsCurVCPU \<noteq> None \<and> snd (the hsCurVCPU))
                                          (modifyArchState(armHSCurVCPU_update
                                             (\<lambda>a. case a of None \<Rightarrow> None
                                                                 | Some (a,_) \<Rightarrow> Some (a, False)))))"
                       in match_ccorres)
       apply (wpc; clarsimp ; ccorres_rewrite)
        apply (rule ccorres_return_Skip)
       apply (rule_tac Q="\<lambda>s. (b \<longrightarrow> _ s) \<and> (\<not> b \<longrightarrow> _ s)" in  ccorres_guard_imp)
        apply (case_tac b)
        apply clarsimp
        apply ccorres_rewrite
          apply (rule ccorres_guard_imp)
          apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
            apply (ctac add: vcpu_disable_ccorres)
           apply ceqv
              apply (rule armHSCurVCPU_update_active_false_ccorres)
             apply wp
            apply (vcg exspec=vcpu_disable_modifies)
           apply clarsimp
           apply assumption
          apply simp
         apply simp
         apply ccorres_rewrite
         apply (rule ccorres_return_Skip)
        apply clarsimp
        apply assumption
        apply simp
      apply ceqv
     apply clarsimp
     apply (rule armHSCurVCPU_update_curv_Null_ccorres)
    apply (wpsimp simp: modifyArchState_def if_apply_def2)
   apply (vcg exspec=vcpu_disable_modifies)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule UNIV_I)
  done

lemma sanitiseSetRegister_ccorres:
  "\<lbrakk> val = val'; reg' = register_from_H reg\<rbrakk> \<Longrightarrow>
     ccorres dc xfdc (tcb_at' tptr)
                      UNIV
                      hs
             (asUser tptr (setRegister reg (local.sanitiseRegister False reg val)))
             (\<acute>unsigned_long_eret_2 :== CALL sanitiseRegister(reg',val',scast false);;
              CALL setRegister(tcb_ptr_to_ctcb_ptr tptr,reg',\<acute>unsigned_long_eret_2))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_r)
     apply (ctac add: setRegister_ccorres)
    apply (vcg)
   apply (rule conseqPre, vcg)
   apply (fastforce simp: sanitiseRegister_def C_register_defs split: register.splits)
  by (auto simp: sanitiseRegister_def from_bool_def simp del: Collect_const split: register.splits bool.splits)

lemma dissociateVCPUTCB_ccorres:
  "ccorres dc xfdc
     (invs' and (tcb_at' tptr or vcpu_at' vcpuptr))
     (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr tptr }
       \<inter> {s. vcpu_' s = vcpu_Ptr vcpuptr }) hs
     (dissociateVCPUTCB vcpuptr tptr) (Call dissociateVCPUTCB_'proc)"
  apply (cinit lift: tcb_' vcpu_')
   apply (rule ccorres_pre_archThreadGet, rename_tac tcbVCPU)
  apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
  apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_rhs_assoc2)
   apply clarsimp
   apply (rule_tac xf'=ret__int_'
                   and R="(\<lambda>s. \<exists>tcb. ko_at' tcb tptr s \<and> (atcbVCPUPtr o tcbArch)  tcb = tcbVCPU) and
                          no_0_obj' and
                          ko_at' vcpu vcpuptr"
                   and val="from_bool (tcbVCPU = Some vcpuptr \<longrightarrow> vcpuTCBPtr vcpu \<noteq> Some tptr)"
                   in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply vcg
      apply clarsimp
      apply (frule cmap_relation_vcpu)
      apply (frule cmap_relation_tcb)
      apply (erule cmap_relationE1)
       apply (erule ko_at_projectKO_opt, rename_tac cvcpu)
      apply (erule cmap_relationE1)
       apply (erule ko_at_projectKO_opt, rename_tac ctcb)
      apply (clarsimp simp add: typ_heap_simps)
      apply (rule conjI)
       apply (case_tac "tcbVCPU_C (tcbArch_C ctcb) \<noteq> vcpu_Ptr vcpuptr";
              clarsimp simp add: ctcb_relation_def carch_tcb_relation_def)
      apply (case_tac "tcbVCPU_C (tcbArch_C ctcb) \<noteq> vcpu_Ptr vcpuptr";
             case_tac "vcpuTCB_C cvcpu \<noteq> tcb_ptr_to_ctcb_ptr tptr";
             clarsimp simp add: cvcpu_relation_def
                                ctcb_relation_def
                                carch_tcb_relation_def
                                option_to_ctcb_ptr_def[of "Some tptr"]
                                from_bool_0)
      apply (frule_tac p=vcpuptr in option_to_ptr_not_0[OF ko_at'_not_NULL];simp?)
      apply (frule_tac p=tptr in option_to_ctcb_ptr_not_0[OF obj_tcb_at']; simp?)
     apply ceqv
    apply (case_tac "tcbVCPU = Some vcpuptr \<longrightarrow> vcpuTCBPtr vcpu \<noteq> Some tptr")
     apply simp
     apply (rule ccorres_fail')
    apply simp
    apply ccorres_rewrite
    apply (rule ccorres_pre_getCurVCPU)
    apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
        apply wpc
         apply (rule ccorres_cond_false)
         apply (rule ccorres_return_Skip)
        apply (simp add: split_def)
        apply (rule_tac R="\<lambda>s. Some x2 = (armHSCurVCPU \<circ> ksArchState) s" in ccorres_when)
         apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def cur_vcpu_relation_def
                         dest!: sym[where s="Some x" for x])
         apply (simp add: eq_commute)
        apply (ctac add: vcpuInvalidateActive_ccorres)
        apply ceqv
       apply (rule ccorres_move_c_guard_tcb)
       apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
           apply (rule archThreadSet_tcbVCPU_Basic_ccorres[of _ None, simplified])
          apply ceqv
         apply (rule ccorres_move_c_guard_vcpu)
         apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
             apply (rule setObject_vcpuTCB_Basic_ccorres[of _ _ _ None, simplified option_to_ctcb_ptr_def, simplified])
            apply ceqv
           apply (subst asUser_bind_distrib; simp)
           apply (rule ccorres_split_nothrow[where r'="(=)" and xf'=ret__unsigned_long_'])
               apply (ctac add: getRegister_ccorres)
              apply ceqv
            apply (erule sanitiseSetRegister_ccorres, simp)
           apply wpsimp
          apply vcg
         apply (wpsimp wp: hoare_drop_imp setObject_vcpu_valid_objs')
        apply vcg
       apply wpsimp
      apply vcg
     apply (wpsimp simp: valid_arch_tcb'_def valid_vcpu'_def)
     apply wpsimp
    apply (vcg exspec=vcpu_invalidate_active_modifies)
   apply vcg
  apply clarsimp
  apply (safe ; (clarsimp simp: valid_arch_tcb'_def valid_vcpu'_def
                               typ_at_to_obj_at_arches obj_at'_def
                               obj_at'_def invs_valid_objs'
                         split: if_split
          | fastforce
          | clarsimp simp: ctcb_relation_def carch_tcb_relation_def typ_heap_simps' cur_vcpu_relation_def invs_no_0_obj' c_typ_rewrs)+)
  done

lemma dissociateVCPUTCB_tcb_ccorres:
    "ccorres dc xfdc
     (invs' and tcb_at' tptr )
     (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr tptr }
       \<inter> {s. vcpu_' s = vcpu_Ptr vcpuptr }) hs
     (dissociateVCPUTCB vcpuptr tptr) (Call dissociateVCPUTCB_'proc)"
    by (rule ccorres_guard_imp2[OF dissociateVCPUTCB_ccorres]) clarsimp

lemma dissociateVCPUTCB_vcpu_ccorres:
    "ccorres dc xfdc
     (invs' and vcpu_at' vcpuptr )
     (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr tptr }
       \<inter> {s. vcpu_' s = vcpu_Ptr vcpuptr }) hs
     (dissociateVCPUTCB vcpuptr tptr) (Call dissociateVCPUTCB_'proc)"
  by (rule ccorres_guard_imp2[OF dissociateVCPUTCB_ccorres]) clarsimp

lemma associateVCPUTCB_ccorres:
  "ccorres dc xfdc
     (invs' and tcb_at' tptr
            and vcpu_at' vcpuptr)
     (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr tptr }
           \<inter> {s. vcpu_' s = vcpu_Ptr vcpuptr }) hs
     (associateVCPUTCB vcpuptr tptr) (Call associateVCPUTCB_'proc)"
  apply (cinit lift: tcb_' vcpu_')
  apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_pre_archThreadGet, rename_tac tcbVCPU)
   apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
       apply (rule_tac Q="(\<lambda>s. \<exists>tcb. ko_at' tcb tptr s \<and> (atcbVCPUPtr o tcbArch) tcb = tcbVCPU) and
                          no_0_obj' and
                          valid_objs'"
                   and Q'=UNIV
                   and C'="{s. (tcbVCPU \<noteq> None) }"
                   in ccorres_rewrite_cond_sr)
        apply clarsimp
        apply (frule cmap_relation_tcb)
        apply (erule cmap_relationE1)
         apply (erule ko_at_projectKO_opt, rename_tac ctcb)
        apply (clarsimp simp: typ_heap_simps')
        apply (case_tac "atcbVCPUPtr (tcbArch tcba) \<noteq> None")
         apply (clarsimp simp add: ctcb_relation_def carch_tcb_relation_def)
         apply(frule valid_objs_valid_tcb', simp)
         apply (clarsimp simp: valid_tcb'_def valid_arch_tcb'_def)
        apply (clarsimp simp: ctcb_relation_def carch_tcb_relation_def)
       apply (wpc ; clarsimp ; ccorres_rewrite)
        apply (rule ccorres_return_Skip)
       apply (ctac add: dissociateVCPUTCB_tcb_ccorres)
      apply ceqv
     apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
     apply (rule ccorres_move_c_guard_vcpu)
     apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
         apply (rule_tac Q="(\<lambda>s. \<exists>tcb. ko_at' vcpu vcpuptr s) and
                            no_0_obj' and
                            valid_objs'"
                     and Q'=UNIV
                     and C'="{s. (vcpuTCBPtr vcpu \<noteq> None)}"
                     in ccorres_rewrite_cond_sr)
          apply clarsimp
          apply (frule cmap_relation_vcpu)
          apply (erule cmap_relationE1)
           apply (erule ko_at_projectKO_opt, rename_tac cvcpu)
          apply (clarsimp simp add: typ_heap_simps')
          apply (case_tac "vcpuTCBPtr vcpu \<noteq> None")
           apply(frule valid_objs_valid_vcpu', simp)
           apply (clarsimp simp add: cvcpu_relation_def
                                     option_to_ctcb_ptr_def
                                     tcb_ptr_to_ctcb_ptr_def
                                     typ_at_tcb'
                                     valid_vcpu'_def)
           apply (frule tcb_aligned')
           apply (frule_tac y=ctcb_offset and n=tcbBlockSizeBits in aligned_offset_non_zero
                 ; clarsimp simp: ctcb_offset_defs objBits_defs)
          apply (clarsimp simp: cvcpu_relation_def option_to_ctcb_ptr_def)
         apply (wpc ; clarsimp ; ccorres_rewrite)
          apply (rule ccorres_return_Skip)
         apply (rule ccorres_move_c_guard_vcpu)
         apply (ctac add: dissociateVCPUTCB_vcpu_ccorres)
        apply ceqv
       apply (rule ccorres_move_c_guard_tcb)
       apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
           apply simp
           apply (rule archThreadSet_tcbVCPU_Basic_ccorres[of _ "Some vcpuptr", simplified])
          apply ceqv
         apply (rule ccorres_move_c_guard_vcpu)
         apply clarsimp
         apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
             apply (rule setObject_vcpuTCB_updated_Basic_ccorres[where tptr="Some tptr" and t="Map.empty",
                                                                 simplified option_to_ctcb_ptr_def, simplified])
            apply ceqv
           apply (rule ccorres_pre_getCurThread, rename_tac curThread)
           apply (subst ccorres_seq_skip'[symmetric])
           apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
               apply (rule_tac R="\<lambda>s. curThread = ksCurThread s" in ccorres_when)
                apply (clarsimp simp: rf_sr_ksCurThread)
               apply (ctac add: vcpu_switch_ccorres_Some)
              apply ceqv
             apply (rule ccorres_return_Skip)
            apply (rule wp_post_taut)
           apply (vcg exspec=vcpu_switch_modifies)
          apply (wpsimp wp: setObject_vcpu_valid_objs' hoare_drop_imps)
         apply vcg
        apply wpsimp
       apply (vcg exspec=dissociateVCPUTCB_modifies)
      apply ((wpsimp wp: hoare_vcg_all_lift hoare_drop_imps
              | strengthen invs_valid_objs' invs_arch_state')+)[1]
     apply (vcg exspec=dissociateVCPUTCB_modifies)
    apply (rule_tac Q="\<lambda>_. invs' and vcpu_at' vcpuptr and tcb_at' tptr" in hoare_post_imp)
     apply (clarsimp simp: valid_vcpu'_def typ_at_tcb' obj_at'_def projectKOs)
     apply (rename_tac vcpu obj, case_tac vcpu)
     apply (fastforce simp: valid_arch_tcb'_def)
    apply wpsimp
   apply (vcg exspec=dissociateVCPUTCB_modifies)
  apply (fastforce simp: ctcb_relation_def carch_tcb_relation_def typ_heap_simps
                         cvcpu_relation_def option_to_ctcb_ptr_def)
  done

lemma vcpuFinalise_ccorres:
  "ccorres dc xfdc (invs' and vcpu_at' vcpuptr)
      ({s. vcpu_' s = Ptr vcpuptr}) []
      (vcpuFinalise vcpuptr) (Call vcpu_finalise_'proc)"
  apply (cinit lift: vcpu_')
   apply (rule ccorres_move_c_guard_vcpu)
   apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
   apply (rule_tac Q="(\<lambda>s. \<exists>tcb. ko_at' vcpu vcpuptr s) and
                           no_0_obj' and
                           valid_objs'"
                   and Q'=UNIV
                   and C'="{s. (vcpuTCBPtr vcpu \<noteq> None)}"
                   in ccorres_rewrite_cond_sr)
    apply clarsimp
    apply (frule cmap_relation_vcpu)
    apply (erule cmap_relationE1)
     apply (erule ko_at_projectKO_opt, rename_tac cvcpu)
    apply (clarsimp simp add: typ_heap_simps')
    apply (case_tac "vcpuTCBPtr vcpu \<noteq> None")
     apply(frule valid_objs_valid_vcpu', simp)
     apply (clarsimp simp add: cvcpu_relation_def
                               option_to_ctcb_ptr_def
                               tcb_ptr_to_ctcb_ptr_def
                               typ_at_tcb'
                               valid_vcpu'_def)
     apply (frule tcb_aligned')
     apply (frule_tac y=ctcb_offset and n=tcbBlockSizeBits in aligned_offset_non_zero
           ; clarsimp simp: ctcb_offset_defs objBits_defs)
    apply (clarsimp simp: cvcpu_relation_def option_to_ctcb_ptr_def)
   apply (wpc ; clarsimp ; ccorres_rewrite)
    apply (rule ccorres_return_Skip)
   apply (rule ccorres_move_c_guard_vcpu)
   apply (ctac add: dissociateVCPUTCB_vcpu_ccorres)
  apply (fastforce simp: ctcb_relation_def carch_tcb_relation_def typ_heap_simps
                         cvcpu_relation_def option_to_ctcb_ptr_def)
  done

lemma capFSize_eq: "\<lbrakk>ccap_relation (capability.ArchObjectCap (arch_capability.PageCap x31 x32 x33 x34 (Some (a, b)))) cap;
              x34 \<noteq> Wellformed_C.ARMSmallPage\<rbrakk>
  \<Longrightarrow> gen_framesize_to_H (capFSize_CL (cap_frame_cap_lift cap)) = x34"
  apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                            case_option_over_if gen_framesize_to_H_def
                            ARM_HYP.pptrBase_def
                            framesize_to_H_def valid_cap'_def
                     elim!: ccap_relationE simp del: Collect_const)
  apply (subgoal_tac "capFSize_CL (cap_frame_cap_lift cap) \<noteq> scast Kernel_C.ARMSmallPage")
  apply simp
  apply (clarsimp simp: c_valid_cap_def cl_valid_cap_def)
  done

method return_NullCap_pair_ccorres =
   solves \<open>((rule ccorres_rhs_assoc2)+), (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV]),
          (rule allI, rule conseqPre, vcg), (clarsimp simp: return_def ccap_relation_NullCap_iff)\<close>

lemma Arch_finaliseCap_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (remainder_C rv') \<and>
                     ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
      ret__struct_finaliseCap_ret_C_'
   (invs' and valid_cap' (ArchObjectCap cp)
       and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s))
   (UNIV \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
                        \<inter> {s. final_' s = from_bool is_final}) []
   (Arch.finaliseCap cp is_final) (Call Arch_finaliseCap_'proc)"
  supply if_cong[cong]
  apply (cinit lift: cap_' final_' cong: call_ignore_cong)
   apply csymbr
   apply (simp add: ARM_HYP_H.finaliseCap_def cap_get_tag_isCap_ArchObject)
   apply (simp add: split_def)
   apply (rule ccorres_cases[where P=is_final]; clarsimp)
    prefer 2
    apply (subgoal_tac "isPageCap cp \<longrightarrow> \<not> isPageTableCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isVCPUCap cp \<and> \<not> isPageDirectoryCap cp")
     apply (rule ccorres_cases[where P="isPageCap cp"]; clarsimp)
      prefer 2
      apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
      apply (cases cp; clarsimp simp: isCap_simps; ccorres_rewrite)
         apply return_NullCap_pair_ccorres
        apply return_NullCap_pair_ccorres
       apply (subst ccorres_cond_seq2_seq[symmetric])
       apply (rule ccorres_guard_imp)
          apply (rule ccorres_rhs_assoc)
          apply csymbr
          apply clarsimp
          apply ccorres_rewrite
          apply (return_NullCap_pair_ccorres, simp+)
       apply (subst ccorres_cond_seq2_seq[symmetric])
       apply (rule ccorres_guard_imp)
         apply (rule ccorres_rhs_assoc)
         apply csymbr
         apply clarsimp
         apply ccorres_rewrite
         apply (return_NullCap_pair_ccorres, simp+)
      apply (return_NullCap_pair_ccorres)
     apply ccorres_rewrite
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subgoal_tac "isPageCap cp \<longrightarrow> \<not> isPageDirectoryCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isVCPUCap cp \<and> \<not> isPageTableCap cp")
       apply clarsimp
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply clarsimp
       apply (rule ccorres_Cond_rhs_Seq)
        apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
         prefer 2
         apply (clarsimp simp: isCap_simps)
         apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
         apply (frule small_frame_cap_is_mapped_alt)
         apply (clarsimp simp: cap_small_frame_cap_lift cap_to_H_def
                               case_option_over_if
                         elim!: ccap_relationE)
        apply (simp add: split_def)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac (no_vcg) add:  unmapPage_ccorres)
         apply return_NullCap_pair_ccorres
        apply (rule wp_post_taut)
       apply (subgoal_tac "capVPMappedAddress cp = None")
        prefer 2
        apply (clarsimp simp: isCap_simps)
        apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
        apply (frule small_frame_cap_is_mapped_alt)
        apply (clarsimp simp: cap_small_frame_cap_lift cap_to_H_def
                              case_option_over_if
                        elim!: ccap_relationE)
       apply (simp add: split_def)
       apply return_NullCap_pair_ccorres
      apply (clarsimp simp: isCap_simps)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subgoal_tac "isPageCap cp \<longrightarrow> \<not> isPageDirectoryCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isVCPUCap cp \<and> \<not> isPageTableCap cp")
       apply clarsimp
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply clarsimp
       apply (rule ccorres_Cond_rhs_Seq)
        apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
         prefer 2
         apply (clarsimp simp: isCap_simps)
         apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
         apply (frule frame_cap_is_mapped_alt)
         apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                               case_option_over_if
                         elim!: ccap_relationE)
        apply simp
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac (no_vcg) add:  unmapPage_ccorres)
         apply return_NullCap_pair_ccorres
        apply (rule wp_post_taut)
       apply (subgoal_tac "capVPMappedAddress cp = None")
        prefer 2
        apply (clarsimp simp: isCap_simps)
        apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
        apply (frule frame_cap_is_mapped_alt)
        apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                              case_option_over_if
                        elim!: ccap_relationE)
       apply clarsimp
       apply return_NullCap_pair_ccorres
      apply (clarsimp simp: isCap_simps)
     apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: isCap_simps)
   apply ccorres_rewrite
   apply (rule ccorres_Cond_rhs_Seq; clarsimp)
  apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
  apply (ctac (no_vcg) add: deleteASIDPool_ccorres)
  apply return_NullCap_pair_ccorres
    apply (rule wp_post_taut)
   apply (rule ccorres_Cond_rhs_Seq; clarsimp)
  apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply clarsimp
    apply ccorres_rewrite
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (simp add: if_1_0_0)
    apply (subgoal_tac "isPageDirectoryCap cp \<longrightarrow> \<not> isPageTableCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isVCPUCap cp \<and> \<not> isPageCap cp")
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subgoal_tac "capPDMappedASID cp \<noteq> None")
       prefer 2
       apply (clarsimp simp add: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (frule cap_lift_page_directory_cap)
       apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                             to_bool_def cap_page_directory_cap_lift_def
                             asid_bits_def
                       split: if_split_asm)
      apply simp
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply (ctac (no_vcg) add: deleteASID_ccorres)
       apply return_NullCap_pair_ccorres
      apply (rule wp_post_taut)
     apply (subgoal_tac "capPDMappedASID cp = None")
      prefer 2
      apply (clarsimp simp add: isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (frule cap_lift_page_directory_cap)
      apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                            cap_page_directory_cap_lift_def
                            asid_bits_def
                      split: if_split_asm)
     apply simp
     apply return_NullCap_pair_ccorres
    apply (clarsimp simp add: isCap_simps)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (subgoal_tac "isPageTableCap cp \<longrightarrow> \<not> isPageDirectoryCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isVCPUCap cp \<and> \<not> isPageCap cp")
     apply clarsimp
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply simp
     apply ccorres_rewrite
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subgoal_tac "capPTMappedAddress cp \<noteq> None")
       prefer 2
       apply (clarsimp simp add: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (frule cap_lift_page_table_cap)
       apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                             to_bool_def cap_page_table_cap_lift_def
                             asid_bits_def
                       split: if_split_asm)
      apply simp
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply (simp add: split_def)
      apply (ctac (no_vcg) add: unmapPageTable_ccorres)
       apply return_NullCap_pair_ccorres
      apply (rule wp_post_taut)
     apply clarsimp
     apply (subgoal_tac "capPTMappedAddress cp = None")
      prefer 2
      apply (clarsimp simp add: isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (frule cap_lift_page_table_cap)
      apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                            cap_page_table_cap_lift_def asid_bits_def
                     split: if_split_asm)
     apply simp
     apply return_NullCap_pair_ccorres
    apply (clarsimp simp: isCap_simps)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (subgoal_tac "isPageCap cp \<longrightarrow> \<not> isPageDirectoryCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isVCPUCap cp \<and> \<not> isPageTableCap cp")
     apply clarsimp
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
       prefer 2
       apply (clarsimp simp: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
       apply (frule small_frame_cap_is_mapped_alt)
       apply (clarsimp simp: cap_small_frame_cap_lift cap_to_H_def
                             case_option_over_if
                       elim!: ccap_relationE)
      apply (simp add: split_def)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply (ctac (no_vcg) add:  unmapPage_ccorres)
       apply return_NullCap_pair_ccorres
      apply (rule wp_post_taut)
     apply (subgoal_tac "capVPMappedAddress cp = None")
      prefer 2
      apply (clarsimp simp: isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
      apply (frule small_frame_cap_is_mapped_alt)
      apply (clarsimp simp: cap_small_frame_cap_lift cap_to_H_def
                            case_option_over_if
                     elim!: ccap_relationE)
     apply (simp add: split_def)
     apply return_NullCap_pair_ccorres
    apply (clarsimp simp: isCap_simps)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (subgoal_tac "isPageCap cp \<longrightarrow> \<not> isPageDirectoryCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isVCPUCap cp \<and> \<not> isPageTableCap cp")
     apply clarsimp
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
       prefer 2
       apply (clarsimp simp: isCap_simps)
       apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
       apply (frule frame_cap_is_mapped_alt)
       apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                             case_option_over_if
                       elim!: ccap_relationE)
      apply simp
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply csymbr
      apply (ctac (no_vcg) add:  unmapPage_ccorres)
       apply return_NullCap_pair_ccorres
      apply (rule wp_post_taut)
     apply (subgoal_tac "capVPMappedAddress cp = None")
      prefer 2
      apply (clarsimp simp: isCap_simps)
      apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
      apply (frule frame_cap_is_mapped_alt)
      apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                            case_option_over_if
                      elim!: ccap_relationE)
     apply clarsimp
     apply (return_NullCap_pair_ccorres)
    apply (clarsimp simp: isCap_simps)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (subgoal_tac "isVCPUCap cp \<longrightarrow> \<not> isPageDirectoryCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isPageCap cp \<and> \<not> isPageTableCap cp")
     apply clarsimp
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply (ctac (no_vcg) add: vcpuFinalise_ccorres)
      apply (return_NullCap_pair_ccorres)
     apply (rule wp_post_taut)
    apply (clarsimp simp: isCap_simps)
   apply clarsimp
   apply (return_NullCap_pair_ccorres)
  apply (clarsimp simp: isCap_simps)
  apply (cases cp ; clarsimp)
      apply (cases is_final; clarsimp)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (frule cap_lift_asid_pool_cap)
      apply (clarsimp simp: valid_cap'_def)
      apply (clarsimp simp: ccap_relation_def cap_to_H_def
                            cap_asid_pool_cap_lift_def asid_bits_def)
     apply (intro conjI; clarsimp)
        apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
         apply (clarsimp simp: valid_cap'_def asid_bits_def mask_def word_less_sub_1)
        apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
        apply (frule small_frame_cap_is_mapped_alt)
        apply (clarsimp simp: cap_small_frame_cap_lift cap_to_H_def
                              case_option_over_if
                        elim!: ccap_relationE)
       apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
        apply (clarsimp simp: valid_cap'_def asid_bits_def mask_def word_less_sub_1)
       apply (frule (1) cap_get_tag_isCap_unfolded_H_cap, simp)
       apply (frule frame_cap_is_mapped_alt)
       apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                             case_option_over_if
                       elim!: ccap_relationE)
      apply (rule conjI, clarsimp)
       apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
       apply (frule small_frame_cap_is_mapped_alt)
       apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
        apply (clarsimp simp: cap_small_frame_cap_lift cap_to_H_def
                              case_option_over_if gen_framesize_to_H_def
                              Kernel_C.ARMSmallPage_def ARM_HYP.pptrBase_def
                              if_split
                       elim!: ccap_relationE)
       apply (clarsimp simp: cap_small_frame_cap_lift cap_to_H_def
                             case_option_over_if
                        elim!: ccap_relationE)
      apply (frule cap_get_tag_isCap_unfolded_H_cap, simp, simp)
     apply (rule conjI, clarsimp)
      apply (subgoal_tac "capVPMappedAddress cp \<noteq> None")
       apply clarsimp
       apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
       apply (frule frame_cap_is_mapped_alt)
       apply (frule capFSize_eq, simp)
       apply simp
       apply (rule conjI)
        apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
        apply (frule capFSize_range)
        apply (rule order_le_less_trans, assumption, simp)
       apply (clarsimp simp: word_less_sub_1)
       apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                             case_option_over_if gen_framesize_to_H_def
                             if_split
                       elim!: ccap_relationE)
      apply (frule (1) cap_get_tag_isCap_unfolded_H_cap)
      apply (frule frame_cap_is_mapped_alt)
      apply (clarsimp simp: cap_frame_cap_lift cap_to_H_def
                     elim!: ccap_relationE)
     apply (frule (1) cap_get_tag_isCap_unfolded_H_cap, simp)
    apply (cases is_final; clarsimp)
    apply (intro conjI; clarsimp?)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (frule cap_lift_page_table_cap)
      apply (subgoal_tac "x42 \<noteq> None")
       apply (clarsimp simp: valid_cap'_def asid_bits_def mask_def word_less_sub_1)
      apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                             to_bool_def cap_page_table_cap_lift_def
                             asid_bits_def
                      split: if_split_asm)
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (frule cap_lift_page_table_cap)
     apply (subgoal_tac "x42 \<noteq> None")
      apply ((clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                             to_bool_def cap_page_table_cap_lift_def
                             asid_bits_def
                      split: if_split_asm)+)[2]
  apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
   apply (cases is_final; clarsimp)
   apply (intro conjI; clarsimp?)
     apply (subgoal_tac "x52 \<noteq> None")
      apply (clarsimp simp: valid_cap'_def)
      apply (clarsimp simp: asid_bits_def mask_def word_less_sub_1)
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (frule cap_lift_page_directory_cap)
     apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                           to_bool_def cap_page_directory_cap_lift_def
                           asid_bits_def
                     split: if_split_asm)
    apply (subgoal_tac "x52 \<noteq> None")
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (frule cap_lift_page_directory_cap)
     apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                           cap_page_directory_cap_lift_def
                           asid_bits_def
                     split: if_split_asm)
    apply (frule cap_get_tag_isCap_unfolded_H_cap)
    apply (frule cap_lift_page_directory_cap)
    apply (clarsimp simp: ccap_relation_def cap_to_H_def capAligned_def
                          to_bool_def cap_page_directory_cap_lift_def
                          asid_bits_def
                    split: if_split_asm)
   apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
  apply (rule conjI)
   apply (clarsimp simp: valid_cap'_def)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (frule cap_lift_vcpu_cap)
  apply (clarsimp simp: cap_vcpu_cap_lift cap_to_H_def
                        case_option_over_if gen_framesize_to_H_def
                  elim!: ccap_relationE)
  done

lemma prepareThreadDelete_ccorres:
  "ccorres dc xfdc
     (invs' and tcb_at' thread)
     (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}) hs
   (prepareThreadDelete thread) (Call Arch_prepareThreadDelete_'proc)"
  apply (cinit lift: thread_', rename_tac cthread)
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_pre_archThreadGet, rename_tac vcpuopt)
   apply simp
   apply (rule_tac Q="valid_objs' and
                      no_0_obj'   and
                      obj_at' (\<lambda>tcb. atcbVCPUPtr (tcbArch tcb) = vcpuopt) thread"
               and Q'=UNIV  and C'="{s. vcpuopt \<noteq> None}" in ccorres_rewrite_cond_sr)
    apply clarsimp
    apply (drule (1) obj_at_cslift_tcb)
    apply (fastforce simp: typ_heap_simps ctcb_relation_def carch_tcb_relation_def
                           option_to_ptr_NULL_eq
                     dest: ko_at'_tcb_vcpu_not_NULL
                    split: option.splits)
   apply (wpc ; clarsimp ; ccorres_rewrite)
    apply (rule ccorres_return_Skip)
   apply (rule ccorres_move_c_guard_tcb)
   apply (ctac add: dissociateVCPUTCB_tcb_ccorres)
  apply (clarsimp simp: invs_valid_pspace')
  apply (rule conjI; clarsimp simp: typ_heap_simps)
   apply (rule conjI)
    apply (clarsimp simp: invs'_def valid_pspace'_def valid_state'_def)
    apply (clarsimp simp: invs'_def valid_pspace'_def valid_state'_def obj_at'_def)
  apply (clarsimp simp: typ_heap_simps ctcb_relation_def carch_tcb_relation_def)
  done

lemma finaliseCap_ccorres:
  "\<And>final.
   ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (finaliseCap_ret_C.remainder_C rv')
                   \<and> ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
   ret__struct_finaliseCap_ret_C_'
   (invs' and sch_act_simple and valid_cap' cap and (\<lambda>s. ksIdleThread s \<notin> capRange cap)
          and (\<lambda>s. 2 ^ capBits cap \<le> gsMaxObjectSize s))
   (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. final_' s = from_bool final}
                        \<inter> {s. exposed_' s = from_bool flag \<comment> \<open>dave has name wrong\<close>}) []
   (finaliseCap cap final flag) (Call finaliseCap_'proc)"
  apply (rule_tac F="capAligned cap" in Corres_UL_C.ccorres_req)
   apply (clarsimp simp: valid_capAligned)
  apply (case_tac "P :: bool" for P)
   apply (rule ccorres_guard_imp2, erule finaliseCap_True_cases_ccorres)
   apply simp
  apply (subgoal_tac "\<exists>acap. (0 <=s (-1 :: word8)) \<or> acap = capCap cap")
   prefer 2 apply simp
  apply (erule exE)
  apply (cinit lift: cap_' final_' exposed_' cong: call_ignore_cong)
   apply csymbr
   apply (simp del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (clarsimp simp: cap_get_tag_isCap isCap_simps
                    cong: if_cong)
    apply (clarsimp simp: word_sle_def)
    apply (rule ccorres_if_lhs)
     apply (rule ccorres_fail)
    apply (simp add: liftM_def del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_add_return2)
    apply (ccorres_rewrite)
    apply (ctac add: Arch_finaliseCap_ccorres)
      apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def Collect_const_mem)
     apply wp
    apply (vcg exspec=Arch_finaliseCap_modifies)
   apply (simp add: cap_get_tag_isCap Collect_False
               del: Collect_const)
   apply csymbr
   apply (simp add: cap_get_tag_isCap Collect_False Collect_True
               del: Collect_const)
   apply (rule ccorres_if_lhs)
    apply (simp, rule ccorres_fail)
   apply (simp add: from_bool_0 Collect_True Collect_False
               del: Collect_const)
   apply csymbr
   apply (simp add: cap_get_tag_isCap Collect_False Collect_True
               del: Collect_const)
   apply (rule ccorres_if_lhs)
    apply (simp add: Let_def)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: cap_get_tag_isCap word_sle_def
                          return_def word_mod_less_divisor
                          less_imp_neq [OF word_mod_less_divisor])
    apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
    apply (clarsimp simp: isCap_simps capAligned_def ccap_relation_NullCap_iff
                          objBits_simps' word_bits_conv
                          signed_shift_guard_simpler_32)
    apply (rule conjI)
     apply (simp add: word_less_nat_alt)
    apply (rule conjI)
     apply (auto simp: word_less_nat_alt)[1]
    apply (simp add: ccap_relation_def cap_zombie_cap_lift)
    apply (simp add: cap_to_H_def isZombieTCB_C_def ZombieTCB_C_def)
    apply (simp add: less_mask_eq word_less_nat_alt less_imp_neq)
    apply (simp add: mod_mask_drop[where n=5] mask_def[where n=5]
                     less_imp_neq [OF word_mod_less_divisor]
                     less_imp_neq Let_def)
    apply (thin_tac "a = b" for a b)+
    apply (subgoal_tac "P" for P)
     apply (subst add.commute, subst unatSuc, assumption)+
     apply (intro impI, rule conjI)
      subgoal
        apply (subst bit.conj_disj_distrib2)
        apply (subst zero_OR_eq, fastforce)
        by fastforce
     subgoal
       apply (simp add: shiftL_nat ccap_relation_NullCap_iff)
       apply (rule trans, rule unat_power_lower32[symmetric])
        apply (simp add: word_bits_conv)
       apply (rule unat_cong, rule word_eqI)
       apply (simp add: word_size word_ops_nth_size nth_w2p is_aligned_nth less_Suc_eq_le)
       by auto[1]
    subgoal
      apply (subst add.commute, subst eq_diff_eq[symmetric])
      by (clarsimp simp: minus_one_norm)
   apply (rule ccorres_if_lhs)
    apply (simp add: Let_def getThreadCSpaceRoot_def locateSlot_conv
                     Collect_True Collect_False
                del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply csymbr
    apply (rule ccorres_Guard_Seq)+
    apply csymbr
    apply (ctac(no_vcg) add: unbindNotification_ccorres)
     apply (ctac(no_vcg) add: suspend_ccorres[OF cteDeleteOne_ccorres])
     apply (ctac(no_vcg) add: prepareThreadDelete_ccorres)
      apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: word_sle_def return_def)
      apply (subgoal_tac "cap_get_tag capa = scast cap_thread_cap")
       apply (drule(1) cap_get_tag_to_H)
       apply (clarsimp simp: isCap_simps capAligned_def ccap_relation_NullCap_iff)
       apply (simp add: ccap_relation_def cap_zombie_cap_lift)
       apply (simp add: cap_to_H_def isZombieTCB_C_def ZombieTCB_C_def
                        mask_def)
       apply (simp add: cte_level_bits_def tcbCTableSlot_def
                        Kernel_C.tcbCTable_def tcbCNodeEntries_def
                        bit.conj_disj_distrib2
                        word_bw_assocs)
       apply (simp add: objBits_simps ctcb_ptr_to_tcb_ptr_def)
       apply (frule is_aligned_add_helper[where p="tcbptr - ctcb_offset" and d=ctcb_offset for tcbptr])
        apply (simp add: ctcb_offset_defs objBits_defs)
       apply (simp add: mask_def irq_opt_relation_def objBits_defs)
      apply (simp add: cap_get_tag_isCap)
     apply wp+
   apply (rule ccorres_if_lhs)
    apply (simp add: Let_def)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: return_def ccap_relation_NullCap_iff)
   apply (simp add: isArchCap_T_isArchObjectCap[symmetric]
               del: Collect_const)
   apply (rule ccorres_if_lhs)
    apply (simp add: Collect_False Collect_True Let_def
                del: Collect_const)
    apply (rule_tac P="(capIRQ cap) \<le>  ARM_HYP.maxIRQ" in ccorres_gen_asm)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (rule_tac xf'=irq_' in ccorres_abstract,ceqv)
    apply (rule_tac P="rv' = ucast (capIRQ cap)" in ccorres_gen_asm2)
    apply (ctac(no_vcg) add: deletingIRQHandler_ccorres)
     apply (rule ccorres_from_vcg_throws[where P=\<top> ])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
     apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
     apply (simp add: ccap_relation_NullCap_iff split: if_split)
    apply wp
   apply (rule ccorres_if_lhs)
    apply simp
    apply (rule ccorres_fail)
   apply (rule ccorres_add_return, rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
       apply (rule ccorres_Cond_rhs)
        apply (simp add: ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (rule ccorres_Cond_rhs)
        apply (simp add: ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (rule ccorres_Cond_rhs)
        apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
        apply simp
       apply (rule ccorres_Cond_rhs)
        apply (simp add: ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (simp add: ccorres_cond_iffs)
       apply (rule ccorres_return_Skip)
      apply (rule ceqv_refl)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def ccap_relation_NullCap_iff
                           irq_opt_relation_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap word_sle_def Collect_const_mem)
  apply (intro impI conjI)
                apply (clarsimp split: bool.splits)
               apply (clarsimp split: bool.splits)
              apply (clarsimp simp: valid_cap'_def isCap_simps)
             apply (clarsimp simp: isCap_simps capRange_def capAligned_def)
            apply (clarsimp simp: isCap_simps valid_cap'_def)
           apply (clarsimp simp: isCap_simps capRange_def capAligned_def)
          apply (clarsimp simp: isCap_simps valid_cap'_def )
         apply clarsimp
        apply (clarsimp simp: isCap_simps valid_cap'_def )
      apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def ccap_relation_def isCap_simps
                            c_valid_cap_def cap_thread_cap_lift_def cap_to_H_def
                            ctcb_ptr_to_tcb_ptr_def Let_def
                      split: option.splits cap_CL.splits if_splits)
     apply clarsimp
     apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
     apply (clarsimp simp: isCap_simps)
     apply (clarsimp simp: tcb_cnode_index_defs ptr_add_assertion_def)
    apply clarsimp
    apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
    apply (frule(1) ccap_relation_IRQHandler_mask)
    apply (clarsimp simp: isCap_simps irqInvalid_def
                          valid_cap'_def ARM_HYP.maxIRQ_def
                          Kernel_C.maxIRQ_def)
    apply (rule irq_opt_relation_Some_ucast_left, simp)
    apply (clarsimp simp: isCap_simps irqInvalid_def
                          valid_cap'_def ARM_HYP.maxIRQ_def
                          Kernel_C.maxIRQ_def)
   apply fastforce
  apply clarsimp
  apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
  apply (frule(1) ccap_relation_IRQHandler_mask)
  apply (clarsimp simp add:mask_eq_ucast_eq)
  done

lemma checkIRQ_ret_good:
  "\<lbrace>\<lambda>s. (irq \<le> scast Kernel_C.maxIRQ \<longrightarrow> P s) \<and> Q s\<rbrace> checkIRQ irq \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (clarsimp simp: checkIRQ_def rangeCheck_def maxIRQ_def minIRQ_def)
  apply (rule hoare_pre,wp)
  by (clarsimp simp: Kernel_C.maxIRQ_def split: if_split)

lemma Arch_checkIRQ_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>r r'. irq \<le> scast Kernel_C.maxIRQ))
           (liftxf errstate id undefined ret__unsigned_long_')
   \<top> (UNIV \<inter> \<lbrace>irq = \<acute>irq_w___unsigned_long\<rbrace>) []
   (checkIRQ irq) (Call Arch_checkIRQ_'proc)"
  apply (cinit lift: irq_w___unsigned_long_' )
   apply (simp add: rangeCheck_def unlessE_def ARM_HYP.minIRQ_def checkIRQ_def
                    ucast_nat_def word_le_nat_alt[symmetric]
                    linorder_not_le[symmetric] maxIRQ_def
                    length_ineq_not_Nil hd_conv_nth cast_simps
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def Kernel_C.maxIRQ_def
                          exception_defs syscall_error_rel_def
                          syscall_error_to_H_cases)
   apply (clarsimp simp: Kernel_C.maxIRQ_def)
   apply (rule ccorres_return_CE, simp+)
  done

end

end
