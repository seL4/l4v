(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Orphanage
imports Refine.Refine
begin

text \<open>
  Proof that calling the kernel never leaves threads orphaned.
  More specifically, every active thread must be the current thread,
  or about to be switched to, or be in a scheduling queue.
\<close>

(*FIXME: arch_split: move up? *)
context Arch begin

requalify_facts
  switchToIdleThread_def
  switchToThread_def

lemmas [crunch_def] = switchToIdleThread_def switchToThread_def

context begin global_naming global
requalify_facts
  Thread_H.switchToIdleThread_def
  Thread_H.switchToThread_def
end
end

context begin interpretation Arch . (*FIXME: arch_split*)

definition
   is_active_thread_state :: "thread_state \<Rightarrow> bool"
where
   "is_active_thread_state ts \<equiv>
       isRunning ts \<or> isRestart ts"

definition
   is_active_tcb_ptr :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
   "is_active_tcb_ptr tcb_ptr s \<equiv>
       st_tcb_at' is_active_thread_state tcb_ptr s"

lemma is_active_tcb_ptr_runnable':
  "is_active_tcb_ptr t s = st_tcb_at' runnable' t s"
  by (auto simp: is_active_tcb_ptr_def pred_tcb_at'_def obj_at'_def
                 is_active_thread_state_def isRunning_def isRestart_def
          split: Structures_H.thread_state.split_asm)

definition
   all_active_tcb_ptrs :: "kernel_state \<Rightarrow> machine_word set"
where
   "all_active_tcb_ptrs s \<equiv>
       { tcb_ptr. is_active_tcb_ptr tcb_ptr s }"

definition
   all_queued_tcb_ptrs :: "kernel_state \<Rightarrow> machine_word set"
where
   "all_queued_tcb_ptrs s \<equiv> { tcb_ptr. obj_at' tcbQueued tcb_ptr s }"

lemma st_tcb_at_neg':
  "(st_tcb_at' (\<lambda> ts. \<not> P ts) t s) = (tcb_at' t s \<and> \<not> st_tcb_at' P t s)"
  by (auto simp: pred_tcb_at'_def obj_at'_def)

lemma st_tcb_at_neg2:
  "(\<not> st_tcb_at' P t s) = (st_tcb_at' (\<lambda> ts. \<not> P ts) t s \<or> \<not> tcb_at' t s)"
  by (auto simp: pred_tcb_at'_def obj_at'_def)

lemma st_tcb_at_double_neg':
  "(st_tcb_at' (\<lambda> ts. \<not> P ts \<and> \<not> Q ts) t s) =
   ((st_tcb_at' (\<lambda> ts. \<not> P ts) t s) \<and> (st_tcb_at' (\<lambda> ts. \<not> Q ts) t s))"
  apply (auto simp: pred_tcb_at'_def obj_at'_def)
  done

definition
   no_orphans :: " kernel_state \<Rightarrow> bool"
where
  "no_orphans s \<equiv>
      \<forall> tcb_ptr.
         (tcb_ptr : all_active_tcb_ptrs s
         \<longrightarrow>
         tcb_ptr = ksCurThread s \<or> tcb_ptr : all_queued_tcb_ptrs s \<or>
         ksSchedulerAction s = SwitchToThread tcb_ptr)"

lemma no_orphans_disj:
   "no_orphans = (\<lambda> s.
           \<forall> tcb_ptr. tcb_ptr = ksCurThread s \<or>
                      tcb_ptr : all_queued_tcb_ptrs s \<or>
                      \<not> typ_at' TCBT tcb_ptr s \<or>
                      st_tcb_at' (\<lambda> state. \<not> is_active_thread_state state) tcb_ptr s \<or>
                      ksSchedulerAction s = SwitchToThread tcb_ptr)"
  apply clarsimp
  apply (rule ext)
  apply (unfold no_orphans_def all_active_tcb_ptrs_def
                is_active_tcb_ptr_def st_tcb_at_neg' typ_at_tcb')
  apply (auto del: pred_tcb_at' intro: pred_tcb_at')
  done

lemma no_orphans_lift:
   assumes typ_at'_is_lifted:
     "\<And> tcb_ptr. \<lbrace> \<lambda>s. \<not> typ_at' TCBT tcb_ptr s\<rbrace> f \<lbrace> \<lambda>_ s. \<not> typ_at' TCBT tcb_ptr s \<rbrace>"
   assumes ksCurThread_is_lifted:
     "\<And> tcb_ptr. \<lbrace> \<lambda>s. tcb_ptr = ksCurThread s \<rbrace> f \<lbrace> \<lambda>_ s. tcb_ptr = ksCurThread s \<rbrace>"
   assumes st_tcb_at'_is_lifted:
     "\<And>P p. \<lbrace> \<lambda>s. st_tcb_at' P p s\<rbrace> f \<lbrace> \<lambda>_ s. st_tcb_at' P p s \<rbrace>"
   assumes tcbQueued_is_lifted:
     "\<And>P tcb_ptr. f \<lbrace> \<lambda>s. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s \<rbrace>"
   assumes ksSchedulerAction_is_lifted:
     "\<And>P. \<lbrace> \<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace> \<lambda>_ s. P (ksSchedulerAction s) \<rbrace>"
   shows
     "\<lbrace> \<lambda>s. no_orphans s \<rbrace> f \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  apply (unfold no_orphans_disj
                all_active_tcb_ptrs_def
                all_queued_tcb_ptrs_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (rule ksCurThread_is_lifted)
   apply (wp hoare_vcg_disj_lift)
    apply (wpsimp wp: tcbQueued_is_lifted)
   apply (wp hoare_vcg_disj_lift)
    apply (rule typ_at'_is_lifted)
   apply (wp hoare_vcg_disj_lift)
    apply (rule st_tcb_at'_is_lifted)
   apply (rule ksSchedulerAction_is_lifted)
  apply simp
  done

lemma st_tcb_at'_is_active_tcb_ptr_lift:
  assumes "\<And>P P' t. \<lbrace>\<lambda>s. P (st_tcb_at' P' t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (st_tcb_at' P' t s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (is_active_tcb_ptr t s)\<rbrace> f \<lbrace>\<lambda>_ s. P (is_active_tcb_ptr t s)\<rbrace>"
  by (clarsimp simp: is_active_tcb_ptr_def) (rule assms)

lemma st_tcb_at'_all_active_tcb_ptrs_lift:
  assumes "\<And>P P' t. \<lbrace>\<lambda>s. P (st_tcb_at' P' t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (st_tcb_at' P' t s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (t \<in> all_active_tcb_ptrs s)\<rbrace> f \<lbrace>\<lambda>_ s. P (t \<in> all_active_tcb_ptrs s)\<rbrace>"
  by (clarsimp simp: all_active_tcb_ptrs_def)
     (rule st_tcb_at'_is_active_tcb_ptr_lift [OF assms])

lemma tcbQueued_all_queued_tcb_ptrs_lift:
  assumes "\<And>Q P tcb_ptr. f \<lbrace>\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace> f \<lbrace>\<lambda>_ s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace>"
  apply (clarsimp simp: all_queued_tcb_ptrs_def)
  apply (rule_tac P=P in P_bool_lift)
   apply (wp hoare_vcg_ex_lift assms)
  apply (wp hoare_vcg_all_lift assms)
  done

definition
   almost_no_orphans :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "almost_no_orphans tcb_ptr s \<equiv>
      \<forall>ptr. ptr = tcb_ptr \<or>
         (ptr : all_active_tcb_ptrs s
         \<longrightarrow>
         ptr = ksCurThread s \<or> ptr : all_queued_tcb_ptrs s \<or>
         ksSchedulerAction s = SwitchToThread ptr)"

lemma no_orphans_strg_almost:
   "no_orphans s \<longrightarrow> almost_no_orphans tcb_ptr s"
  unfolding no_orphans_def almost_no_orphans_def
  apply simp
  done

lemma almost_no_orphans_disj:
   "almost_no_orphans tcb_ptr = (\<lambda> s.
           \<forall> ptr. ptr = ksCurThread s \<or>
                  ptr : all_queued_tcb_ptrs s \<or>
                  \<not> typ_at' TCBT ptr s \<or>
                  st_tcb_at' (\<lambda> thread_state. \<not> is_active_thread_state thread_state) ptr s \<or>
                  ptr = tcb_ptr \<or>
                  ksSchedulerAction s = SwitchToThread ptr)"
  apply clarsimp
  apply (rule ext)
  apply (unfold almost_no_orphans_def all_active_tcb_ptrs_def
                is_active_tcb_ptr_def st_tcb_at_neg' typ_at_tcb')
  apply (auto del: pred_tcb_at' intro: pred_tcb_at')
  done

lemma all_queued_tcb_ptrs_ksReadyQueues_update[simp]:
  "tcb_ptr \<in> all_queued_tcb_ptrs (ksReadyQueues_update f s) = (tcb_ptr \<in> all_queued_tcb_ptrs s)"
  unfolding all_queued_tcb_ptrs_def
  by (clarsimp simp: obj_at'_def)

lemma no_orphans_update_simps[simp]:
  "no_orphans (gsCNodes_update f s) = no_orphans s"
  "no_orphans (gsUserPages_update g s) = no_orphans s"
  "no_orphans (gsUntypedZeroRanges_update h s) = no_orphans s"
  by (simp_all add: no_orphans_def all_active_tcb_ptrs_def
                    is_active_tcb_ptr_def all_queued_tcb_ptrs_def)

lemma no_orphans_ksReadyQueuesL1Bitmap_update[simp]:
  "no_orphans (ksReadyQueuesL1Bitmap_update f s) = no_orphans s"
  unfolding no_orphans_def all_active_tcb_ptrs_def all_queued_tcb_ptrs_def is_active_tcb_ptr_def
  by auto

lemma no_orphans_ksReadyQueuesL2Bitmap_update[simp]:
  "no_orphans (ksReadyQueuesL2Bitmap_update f s) = no_orphans s"
  unfolding no_orphans_def all_active_tcb_ptrs_def all_queued_tcb_ptrs_def is_active_tcb_ptr_def
  by auto

lemma no_orphans_ksIdle[simp]:
   "no_orphans (ksIdleThread_update f s) = no_orphans s"
  unfolding no_orphans_def all_active_tcb_ptrs_def all_queued_tcb_ptrs_def is_active_tcb_ptr_def
  apply auto
  done

lemma no_orphans_ksWorkUnits [simp]:
   "no_orphans (ksWorkUnitsCompleted_update f s) = no_orphans s"
  unfolding no_orphans_def all_active_tcb_ptrs_def all_queued_tcb_ptrs_def is_active_tcb_ptr_def
  apply auto
  done

lemma no_orphans_irq_state_independent[intro!, simp]:
  "no_orphans (s \<lparr>ksMachineState := ksMachineState s \<lparr> irq_state := f (irq_state (ksMachineState s)) \<rparr> \<rparr>)
   = no_orphans s"
  by (simp add: no_orphans_def all_active_tcb_ptrs_def
                all_queued_tcb_ptrs_def is_active_tcb_ptr_def)

add_upd_simps "no_orphans (gsUntypedZeroRanges_update f s)"
declare upd_simps[simp]

lemma almost_no_orphans_ksReadyQueuesL1Bitmap_update[simp]:
  "almost_no_orphans t (ksReadyQueuesL1Bitmap_update f s) = almost_no_orphans t s"
  unfolding almost_no_orphans_def all_active_tcb_ptrs_def all_queued_tcb_ptrs_def is_active_tcb_ptr_def
  by auto

lemma almost_no_orphans_ksReadyQueuesL2Bitmap_update[simp]:
  "almost_no_orphans t (ksReadyQueuesL2Bitmap_update f s) = almost_no_orphans t s"
  unfolding almost_no_orphans_def all_active_tcb_ptrs_def all_queued_tcb_ptrs_def is_active_tcb_ptr_def
  by auto

lemma all_active_tcb_ptrs_queue [simp]:
  "all_active_tcb_ptrs (ksReadyQueues_update f s) = all_active_tcb_ptrs s"
  by (clarsimp simp: all_active_tcb_ptrs_def is_active_tcb_ptr_def)

(****************************************************************************************************)

crunch no_orphans [wp]: addToBitmap "no_orphans"
crunch no_orphans [wp]: removeFromBitmap "no_orphans"

crunch almost_no_orphans [wp]: addToBitmap "almost_no_orphans x"
crunch almost_no_orphans [wp]: removeFromBitmap "almost_no_orphans x"

lemma setCTE_tcbQueued[wp]:
  "setCTE ptr v \<lbrace>\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t s)\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

lemma setCTE_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   setCTE p cte
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (rule no_orphans_lift)
  apply (wp setCTE_typ_at' setCTE_pred_tcb_at')+
  done

lemma setCTE_almost_no_orphans [wp]:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<rbrace>
   setCTE p cte
   \<lbrace> \<lambda>rv s. almost_no_orphans tcb_ptr s \<rbrace>"
  unfolding almost_no_orphans_disj all_queued_tcb_ptrs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift setCTE_typ_at' setCTE_pred_tcb_at')
  done

crunch no_orphans [wp]: activateIdleThread "no_orphans"

lemma asUser_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   asUser thread f
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma threadSet_all_queued_tcb_ptrs:
  "\<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb \<Longrightarrow> threadSet F tptr \<lbrace>\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace>"
  unfolding almost_no_orphans_disj all_queued_tcb_ptrs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_st_tcb_at2 threadSet_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: obj_at'_def ps_clear_upd objBits_simps)
  done

crunches removeFromBitmap, addToBitmap, setQueue
  for all_queued_tcb_ptrs[wp]: "\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)"
  (wp: tcbQueued_all_queued_tcb_ptrs_lift)

crunches tcbQueuePrepend, tcbQueueAppend
  for all_queued_tcb_ptrs[wp]: "\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)"
  (wp: threadSet_all_queued_tcb_ptrs ignore: threadSet)

lemma tcbQueued_update_True_all_queued_tcb_ptrs[wp]:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> tcb_ptr' \<longrightarrow> tcb_ptr' \<in> all_queued_tcb_ptrs s\<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. True)) tcb_ptr
   \<lbrace>\<lambda>_ s. tcb_ptr' \<in> all_queued_tcb_ptrs s\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: all_queued_tcb_ptrs_def obj_at'_def ps_clear_upd objBits_simps)
  done

lemma tcbSchedEnqueue_all_queued_tcb_ptrs[wp]:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> tcb_ptr' \<longrightarrow> tcb_ptr \<in> all_queued_tcb_ptrs s\<rbrace>
   tcbSchedEnqueue tcb_ptr'
   \<lbrace>\<lambda>_ s. tcb_ptr \<in> all_queued_tcb_ptrs s\<rbrace>"
  unfolding tcbSchedEnqueue_def tcbQueuePrepend_def
  apply (wpsimp wp: hoare_vcg_imp_lift' threadGet_wp
         | wpsimp wp: threadSet_all_queued_tcb_ptrs)+
  apply (clarsimp simp: all_queued_tcb_ptrs_def obj_at'_def)
  done

lemmas tcbSchedEnqueue_all_queued_tcb_ptrs'[wp] =
  tcbSchedEnqueue_all_queued_tcb_ptrs[simplified all_queued_tcb_ptrs_def, simplified]

lemma tcbSchedAppend_all_queued_tcb_ptrs[wp]:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> tcb_ptr' \<longrightarrow> tcb_ptr \<in> all_queued_tcb_ptrs s\<rbrace>
   tcbSchedAppend tcb_ptr'
   \<lbrace>\<lambda>_ s. tcb_ptr \<in> all_queued_tcb_ptrs s\<rbrace>"
  unfolding tcbSchedAppend_def tcbQueueAppend_def
  apply (wpsimp wp: hoare_vcg_imp_lift' threadGet_wp
         | wpsimp wp: threadSet_all_queued_tcb_ptrs)+
  apply (clarsimp simp: all_queued_tcb_ptrs_def obj_at'_def)
  done

lemmas tcbSchedAppend_all_queued_tcb_ptrs'[wp] =
  tcbSchedAppend_all_queued_tcb_ptrs[simplified all_queued_tcb_ptrs_def, simplified]

lemma threadSet_no_orphans:
  "\<lbrakk>\<forall>tcb. \<not> is_active_thread_state (tcbState tcb) \<longrightarrow> \<not> is_active_thread_state (tcbState (F tcb));
    \<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb\<rbrakk>
   \<Longrightarrow> threadSet F tptr \<lbrace>no_orphans\<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_st_tcb_at2)

lemma tcbQueued_update_True_no_orphans:
  "\<lbrace>almost_no_orphans tptr and tcb_at' tptr\<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. True)) tptr
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding no_orphans_disj
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_st_tcb_at2)
  apply (fastforce simp: almost_no_orphans_def all_active_tcb_ptrs_def
                         tcb_at_typ_at' st_tcb_at_neg' is_active_tcb_ptr_def)
  done

lemma tcbQueued_update_True_almost_no_orphans:
  "threadSet (tcbQueued_update (\<lambda>_. True)) tptr' \<lbrace>almost_no_orphans tptr\<rbrace>"
  unfolding almost_no_orphans_disj
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift threadSet_st_tcb_at2)
  apply fastforce
  done

lemma threadSet_almost_no_orphans:
  "\<lbrakk>\<forall>tcb. \<not> is_active_thread_state (tcbState tcb) \<longrightarrow> \<not> is_active_thread_state (tcbState (F tcb));
    \<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb\<rbrakk>
   \<Longrightarrow> threadSet F tptr \<lbrace>almost_no_orphans ptr\<rbrace>"
  unfolding almost_no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_st_tcb_at2)

lemma setQueue_no_orphans[wp]:
  "setQueue d prio qs \<lbrace>no_orphans\<rbrace>"
  unfolding setQueue_def
  apply wp
  apply (clarsimp simp: no_orphans_def)
  done

lemma setQueue_almost_no_orphans[wp]:
  "setQueue d prio qs \<lbrace>almost_no_orphans tptr\<rbrace>"
  unfolding setQueue_def
  apply wp
  apply (clarsimp simp: almost_no_orphans_def)
  done

lemma tcbSchedEnqueue_no_orphans[wp]:
  "tcbSchedEnqueue tcb_ptr \<lbrace>no_orphans\<rbrace>"
  unfolding tcbSchedEnqueue_def tcbQueuePrepend_def
  apply (wpsimp wp: tcbQueued_update_True_no_orphans threadSet_almost_no_orphans threadGet_wp)
  apply (fastforce simp: no_orphans_strg_almost)
  done

lemma tcbSchedAppend_no_orphans[wp]:
  "tcbSchedAppend tcb_ptr \<lbrace>no_orphans\<rbrace>"
  unfolding tcbSchedAppend_def tcbQueueAppend_def
  apply (wpsimp wp: tcbQueued_update_True_no_orphans threadSet_almost_no_orphans threadGet_wp)
  apply (fastforce simp: no_orphans_strg_almost)
  done

lemma tcbSchedEnqueue_almost_no_orphans:
  "\<lbrace>almost_no_orphans tcb_ptr\<rbrace>
   tcbSchedEnqueue tcb_ptr
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding tcbSchedEnqueue_def tcbQueuePrepend_def
  apply (wpsimp wp: tcbQueued_update_True_no_orphans threadSet_almost_no_orphans threadGet_wp)
  apply (fastforce simp: no_orphans_def almost_no_orphans_def all_queued_tcb_ptrs_def obj_at'_def)
  done

lemma tcbSchedEnqueue_almost_no_orphans_lift:
  "tcbSchedEnqueue tcb_ptr \<lbrace>almost_no_orphans ptr\<rbrace>"
  unfolding tcbSchedEnqueue_def tcbQueuePrepend_def
  by (wpsimp wp: tcbQueued_update_True_almost_no_orphans threadSet_almost_no_orphans)

lemma ssa_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and>
     (\<forall>t. sch_act_not t s \<or> t : all_queued_tcb_ptrs s \<or> ksCurThread s = t) \<rbrace>
   setSchedulerAction sa
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setSchedulerAction_def no_orphans_disj all_queued_tcb_ptrs_def
  apply wp
  apply auto
  done

lemma ssa_almost_no_orphans:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and>
     (\<forall>t. sch_act_not t s \<or> t : all_queued_tcb_ptrs s \<or> ksCurThread s = t) \<rbrace>
   setSchedulerAction (SwitchToThread tcb_ptr)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setSchedulerAction_def no_orphans_disj almost_no_orphans_disj all_queued_tcb_ptrs_def
  apply wp
  apply auto
  done

lemma ssa_almost_no_orphans_lift [wp]:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and>
     (\<forall>t. sch_act_not t s \<or> t : all_queued_tcb_ptrs s \<or> ksCurThread s = t) \<rbrace>
   setSchedulerAction sa
   \<lbrace> \<lambda>rv s. almost_no_orphans tcb_ptr s \<rbrace>"
  unfolding setSchedulerAction_def almost_no_orphans_disj all_queued_tcb_ptrs_def
  apply wp
  apply auto
  done

lemma rescheduleRequired_no_orphans [wp]:
  "rescheduleRequired \<lbrace>no_orphans\<rbrace>"
  unfolding rescheduleRequired_def
  by (wpsimp wp: ssa_no_orphans hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift | wpc)+

lemma rescheduleRequired_almost_no_orphans [wp]:
  "rescheduleRequired \<lbrace>almost_no_orphans tcb_ptr\<rbrace>"
  unfolding rescheduleRequired_def
  by (wpsimp wp: ssa_almost_no_orphans_lift hoare_vcg_all_lift tcbSchedEnqueue_almost_no_orphans_lift
                 hoare_vcg_imp_lift' hoare_vcg_disj_lift)

lemma setThreadState_current_no_orphans:
  "\<lbrace>\<lambda>s. no_orphans s \<and> ksCurThread s = tcb_ptr\<rbrace>
   setThreadState state tcb_ptr
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding setThreadState_def
  apply wpsimp
  unfolding no_orphans_disj
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state
             threadSet_all_queued_tcb_ptrs
          | fastforce)+
  done

lemma setThreadState_isRestart_no_orphans:
  "\<lbrace>no_orphans and st_tcb_at' isRestart tcb_ptr\<rbrace>
   setThreadState state tcb_ptr
   \<lbrace>\<lambda>_ . no_orphans\<rbrace>"
  unfolding setThreadState_def
  apply wpsimp
   unfolding no_orphans_disj
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state
             threadSet_all_queued_tcb_ptrs
          | fastforce)+
  apply (auto simp: is_active_thread_state_def st_tcb_at_double_neg' st_tcb_at_neg')
  done

lemma setThreadState_almost_no_orphans [wp]:
  "\<lbrace>no_orphans\<rbrace> setThreadState state tcb_ptr \<lbrace>\<lambda>_. almost_no_orphans tcb_ptr\<rbrace>"
  unfolding setThreadState_def
  apply wpsimp
   apply (unfold no_orphans_disj almost_no_orphans_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state
             threadSet_all_queued_tcb_ptrs
          | fastforce)+
  done

lemma setThreadState_not_active_no_orphans:
  "\<not> is_active_thread_state state \<Longrightarrow> setThreadState state tcb_ptr \<lbrace>no_orphans\<rbrace>"
  unfolding setThreadState_def
  apply wpsimp
   apply (unfold no_orphans_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state
             threadSet_all_queued_tcb_ptrs
          | fastforce)+
  done

lemma setThreadState_not_active_almost_no_orphans:
  "\<not> is_active_thread_state state \<Longrightarrow> setThreadState state tcb_ptr \<lbrace>almost_no_orphans thread\<rbrace>"
  unfolding setThreadState_def
  apply wpsimp
   apply (unfold almost_no_orphans_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state
             threadSet_all_queued_tcb_ptrs
          | fastforce)+
  done

lemma activateThread_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> ct_in_state' activatable' s \<and> invs' s \<rbrace>
   activateThread
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding activateThread_def
  apply (wp gts_wp' setThreadState_isRestart_no_orphans | wpc | clarsimp)+
  apply (auto simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def isRestart_def)
  done

crunches removeFromBitmap, tcbQueueRemove, setQueue
  for almost_no_orphans[wp]: "almost_no_orphans thread"
  and no_orphans[wp]: no_orphans
  and all_queued_tcb_ptrs[wp]: "\<lambda>s. tcb_ptr \<in> all_queued_tcb_ptrs s"
  (wp: crunch_wps)

lemma tcbQueued_update_False_all_queued_tcb_ptrs:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> tcb_ptr' \<and> tcb_ptr' \<in> all_queued_tcb_ptrs s\<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. False)) tcb_ptr
   \<lbrace>\<lambda>_ s. tcb_ptr' \<in> all_queued_tcb_ptrs s\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: all_queued_tcb_ptrs_def obj_at'_def ps_clear_upd)
  done

lemma tcbSchedDequeue_all_queued_tcb_ptrs_other:
  "\<lbrace>\<lambda>s. tcb_ptr \<noteq> tcb_ptr' \<and> tcb_ptr' \<in> all_queued_tcb_ptrs s\<rbrace>
   tcbSchedDequeue tcb_ptr
   \<lbrace>\<lambda>_ s. tcb_ptr' \<in> all_queued_tcb_ptrs s\<rbrace>"
  unfolding tcbSchedDequeue_def
  by (wpsimp wp: tcbQueued_update_False_all_queued_tcb_ptrs threadGet_wp)

lemma tcbQueued_update_False_almost_no_orphans:
  "\<lbrace>no_orphans\<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. False)) tptr
   \<lbrace>\<lambda>_. almost_no_orphans tptr\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: no_orphans_def almost_no_orphans_def)
  apply (rename_tac tcb_ptr)
  apply (case_tac "tcb_ptr = tptr")
   apply fastforce
  apply (fastforce simp: all_queued_tcb_ptrs_def obj_at'_def all_active_tcb_ptrs_def
                         is_active_tcb_ptr_def st_tcb_at'_def ps_clear_upd)
  done

lemma tcbSchedDequeue_almost_no_orphans [wp]:
  "\<lbrace>no_orphans\<rbrace> tcbSchedDequeue thread \<lbrace>\<lambda>_. almost_no_orphans thread\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp wp: tcbQueued_update_False_almost_no_orphans threadGet_wp)
  apply (simp add: no_orphans_strg_almost)
  done

lemma tcbSchedDequeue_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> \<not> is_active_tcb_ptr tcbPtr s \<and> tcb_at' tcbPtr s\<rbrace>
   tcbSchedDequeue tcbPtr
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  supply disj_not1[simp del]
  unfolding no_orphans_disj almost_no_orphans_disj
  apply (rule hoare_allI)
  apply (rename_tac tcb_ptr)
  apply (case_tac "tcb_ptr = tcbPtr")
   apply (rule_tac Q="\<lambda>_ s. st_tcb_at' (\<lambda>state. \<not> is_active_thread_state state) tcbPtr s"
                in hoare_post_imp)
    apply fastforce
   apply wpsimp
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def is_active_tcb_ptr_def disj_not1)
  apply (wpsimp wp: tcbQueued_update_False_all_queued_tcb_ptrs hoare_vcg_disj_lift
              simp: tcbSchedDequeue_def)
  done

lemma switchToIdleThread_no_orphans' [wp]:
  "\<lbrace>\<lambda>s. no_orphans s
        \<and> (is_active_tcb_ptr (ksCurThread s) s \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s)\<rbrace>
   switchToIdleThread
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  apply (clarsimp simp: switchToIdleThread_def setCurThread_def AARCH64_H.switchToIdleThread_def)
  apply (simp add: no_orphans_disj all_queued_tcb_ptrs_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift
                    hoare_drop_imp[where R="\<lambda>_. idleThreadNotQueued"] hoare_vcg_imp_lift')
  apply (force simp: is_active_tcb_ptr_def st_tcb_at_neg' typ_at_tcb')
  done

crunches getVMID, Arch.switchToThread
  for ksCurThread[wp]: "\<lambda> s. P (ksCurThread s)"
  (wp: crunch_wps getObject_inv loadObject_default_inv findVSpaceForASID_vs_at_wp
   simp: getThreadVSpaceRoot_def if_distribR)

crunches updateASIDPoolEntry, Arch.switchToThread
  for no_orphans[wp]: "no_orphans"
  (wp: no_orphans_lift crunch_wps)

lemma all_queued_tcb_ptrs_machine_state[simp]:
  "all_queued_tcb_ptrs (s\<lparr>ksMachineState := m\<rparr>) = all_queued_tcb_ptrs s"
  by (simp add: all_queued_tcb_ptrs_def)

lemma all_queued_tcb_ptrs_arch_state[simp]:
  "all_queued_tcb_ptrs (s\<lparr>ksArchState := as\<rparr>) = all_queued_tcb_ptrs s"
  by (simp add: all_queued_tcb_ptrs_def)

lemma setObject_vcpu_all_queued_tcb_ptrs[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace>"
  apply (simp add: all_queued_tcb_ptrs_def)
  apply (rule setObject_vcpu_obj_at'_no_vcpu)
  done

lemma setASID_all_queued_tcb_ptrs[wp]:
  "setObject ptr (ap::asidpool) \<lbrace>\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace>"
  apply (simp add: all_queued_tcb_ptrs_def obj_at'_real_def)
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps)
    apply (simp add: pageBits_def)
   apply simp
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  done

crunches Arch.switchToThread
  for all_queued_tcb_ptrs[wp]: "\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)"
  (wp: getASID_wp crunch_wps simp: crunch_simps)

crunch ksSchedulerAction [wp]: "Arch.switchToThread" "\<lambda>s. P (ksSchedulerAction s)"

lemma setCurThread_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and>
         (is_active_tcb_ptr (ksCurThread s) s \<longrightarrow> ksCurThread s : all_queued_tcb_ptrs s) \<rbrace>
   setCurThread newThread
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setCurThread_def
  apply (wp | clarsimp)+
  apply (unfold no_orphans_def all_queued_tcb_ptrs_def
                all_active_tcb_ptrs_def is_active_tcb_ptr_def)
  apply auto
  done

lemma tcbSchedDequeue_all_active_tcb_ptrs[wp]:
  "\<lbrace>\<lambda>s. P (t' \<in> all_active_tcb_ptrs s)\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_ s. P (t' \<in> all_active_tcb_ptrs s)\<rbrace>"
  by (clarsimp simp: all_active_tcb_ptrs_def is_active_tcb_ptr_def) wp

lemma setCurThread_almost_no_orphans:
  "\<lbrace>\<lambda>s. almost_no_orphans t s \<and>
          (ksCurThread s \<noteq> t \<longrightarrow>
             ksCurThread s \<in> all_active_tcb_ptrs s \<longrightarrow>
             ksCurThread s \<in> all_queued_tcb_ptrs s)\<rbrace>
   setCurThread t \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding setCurThread_def
  apply wp
  apply (fastforce simp: almost_no_orphans_def
                        no_orphans_def
                        all_queued_tcb_ptrs_def
                        all_active_tcb_ptrs_def
                        is_active_tcb_ptr_def)
  done

lemmas ArchThreadDecls_H_switchToThread_all_active_tcb_ptrs[wp] =
  st_tcb_at'_all_active_tcb_ptrs_lift [OF Arch_switchToThread_pred_tcb']

lemma ThreadDecls_H_switchToThread_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and>
         st_tcb_at' runnable' tcb_ptr s \<and>
         (ksCurThread s \<in> all_active_tcb_ptrs s
            \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s)\<rbrace>
   ThreadDecls_H.switchToThread tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding Thread_H.switchToThread_def
  by (wpsimp wp: setCurThread_almost_no_orphans hoare_vcg_imp_lift'
                 tcbSchedDequeue_all_queued_tcb_ptrs_other
      | wps)+

lemma findM_failure':
  "\<lbrakk> \<And>x S. \<lbrace> \<lambda>s. P S s \<rbrace> f x \<lbrace> \<lambda>rv s. \<not> rv \<longrightarrow> P (insert x S) s \<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace> \<lambda>s. P S s \<rbrace> findM f xs \<lbrace> \<lambda>rv s. rv = None \<longrightarrow> P (S \<union> set xs) s \<rbrace>"
  apply (induct xs arbitrary: S)
   apply (clarsimp, wp, clarsimp)
  apply clarsimp
  apply (rule bind_wp_fwd, assumption)
  apply (case_tac r)
   apply (clarsimp, wp, clarsimp)
  apply clarsimp
  apply (rule hoare_strengthen_post, assumption)
  apply clarsimp
  done

lemmas findM_failure = findM_failure'[where S="{}", simplified]

lemma findM_on_success:
  "\<lbrakk> \<And>x. \<lbrace> P x \<rbrace> f x \<lbrace> \<lambda>rv s. rv \<rbrace>; \<And>x y. \<lbrace> P x \<rbrace> f y \<lbrace> \<lambda>rv. P x \<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>x \<in> set xs. P x s \<rbrace> findM f xs \<lbrace> \<lambda>rv s. \<exists> y. rv = Some y \<rbrace>"
  apply (induct xs; clarsimp)
  apply wp+
  apply (clarsimp simp: imp_conv_disj Bex_def)
  apply (wp hoare_vcg_disj_lift hoare_vcg_ex_lift | clarsimp | assumption)+
  done

crunch st_tcb' [wp]: switchToThread "\<lambda>s. P' (st_tcb_at' P t s)"

lemmas switchToThread_all_active_tcb_ptrs[wp] =
  st_tcb_at'_all_active_tcb_ptrs_lift [OF switchToThread_st_tcb']

(* ksSchedulerAction s = ChooseNewThread *)
lemma chooseThread_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> all_invs_but_ct_idle_or_in_cur_domain' s
        \<and> (is_active_tcb_ptr (ksCurThread s) s \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s)\<rbrace>
   chooseThread
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  unfolding chooseThread_def Let_def
  supply if_split[split del]
  apply (simp only: return_bind, simp)
  apply (intro bind_wp[OF _ stateAssert_sp])
  apply (rule bind_wp[where Q'="\<lambda>rv s. ?PRE s \<and> ksReadyQueues_asrt s \<and> ready_qs_runnable s
                                            \<and> rv = ksCurDomain s"])
   apply (rule_tac Q'="\<lambda>rv s. ?PRE s \<and> ksReadyQueues_asrt s \<and> ready_qs_runnable s
                              \<and> curdom = ksCurDomain s \<and> rv = ksReadyQueuesL1Bitmap s curdom"
                in bind_wp)
    apply (rename_tac l1)
    apply (case_tac "l1 = 0")
     (* switch to idle thread *)
     apply (simp, wp, simp)
    (* we have a thread to switch to *)
    apply (wp assert_inv ThreadDecls_H_switchToThread_no_orphans)
    apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def st_tcb_at'_def)
    apply (fastforce dest!: lookupBitmapPriority_obj_at' elim: obj_at'_weaken
                     simp: all_active_tcb_ptrs_def)
   apply (wpsimp simp: bitmap_fun_defs)
  apply (wp curDomain_or_return_0[simplified])
    apply (wpsimp simp: curDomain_def simp: invs_no_cicd_ksCurDomain_maxDomain')+
  done

lemma hoare_neg_imps:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda> rv s. \<not> R rv s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp: valid_def)

lemma setCurThread_ct [wp]:
  "\<lbrace> \<top> \<rbrace>
   setCurThread tcb_ptr
   \<lbrace> \<lambda>rv s. ksCurThread s = tcb_ptr \<rbrace>"
  unfolding setCurThread_def
  apply (wp | clarsimp)+
  done

lemma ThreadDecls_H_switchToThread_ct [wp]:
  "\<lbrace> \<top> \<rbrace>
   switchToThread tcb_ptr
   \<lbrace> \<lambda>rv s. ksCurThread s = tcb_ptr \<rbrace>"
  unfolding switchToThread_def
  apply (wp | clarsimp)+
  done

crunch no_orphans [wp]: nextDomain no_orphans
(wp: no_orphans_lift simp: Let_def)

crunch tcbQueued[wp]: nextDomain "\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s)"
(simp: Let_def)

crunch st_tcb_at' [wp]: nextDomain "\<lambda>s. P (st_tcb_at' P' p s)"
(simp: Let_def)

crunch ct' [wp]: nextDomain "\<lambda>s. P (ksCurThread s)"
(simp: Let_def)

crunch sch_act_not [wp]: nextDomain "sch_act_not t"
(simp: Let_def)

lemma all_invs_but_ct_idle_or_in_cur_domain'_strg:
  "invs' s \<longrightarrow> all_invs_but_ct_idle_or_in_cur_domain' s"
  by (clarsimp simp: invs'_to_invs_no_cicd'_def)

lemma setSchedulerAction_cnt_sch_act_not[wp]:
  "\<lbrace> \<top> \<rbrace> setSchedulerAction ChooseNewThread \<lbrace>\<lambda>rv s. sch_act_not x s\<rbrace>"
  by (rule hoare_pre, rule hoare_strengthen_post[OF setSchedulerAction_direct]) auto

crunches setSchedulerAction
  for pred_tcb_at': "\<lambda>s. P (pred_tcb_at' proj Q t s)"
  and ct': "\<lambda>s. P (ksCurThread s)"
  (wp_del: ssa_wp)

lemmas ssa_st_tcb_at'_ksCurThread[wp] =
  hoare_lift_Pf2[where f=ksCurThread, OF setSchedulerAction_pred_tcb_at' setSchedulerAction_ct']

lemma ct_active_st_tcb_at':
  "ct_active' s = st_tcb_at' runnable' (ksCurThread s) s"
  apply (rule iffI)
   apply (drule ct_active_runnable')
   apply (simp add: ct_in_state'_def)
  apply (clarsimp simp: ct_in_state'_def)
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st, auto)
  done

(* FIXME move *)
lemma invs_switchToThread_runnable':
  "\<lbrakk> invs' s ; ksSchedulerAction s = SwitchToThread t \<rbrakk> \<Longrightarrow> st_tcb_at' runnable' t s"
  by (simp add: invs'_def valid_state'_def)

(* for shoving pred_tcb_at' through hoare_vcg_imp_lift for tcbs we know are there *)
lemma not_pred_tcb_at'I:
  "\<lbrakk> pred_tcb_at' f (Not \<circ> P) t s ; tcb_at' t s \<rbrakk> \<Longrightarrow> \<not> pred_tcb_at' f P t s"
  by (subst (asm) pred_tcb_at'_Not, blast)

lemma in_all_active_tcb_ptrsD:
  "t \<in> all_active_tcb_ptrs s \<Longrightarrow> st_tcb_at' runnable' t s"
  unfolding all_active_tcb_ptrs_def is_active_tcb_ptr_def
             is_active_thread_state_def isRunning_def isRestart_def
  apply clarsimp
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st; clarsimp)
  done

lemma chooseThread_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
  chooseThread
  \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  unfolding chooseThread_def Let_def curDomain_def
  supply if_split[split del]
  apply (simp only: return_bind, simp)
  apply (wp findM_inv | simp)+
  apply (case_tac queue)
  apply (wp stt_nosch | simp add: curDomain_def bitmap_fun_defs)+
  done

lemma scheduleChooseNewThread_no_orphans:
  "\<lbrace>invs' and no_orphans
    and (\<lambda>s. ksSchedulerAction s = ChooseNewThread
             \<and> (st_tcb_at' runnable' (ksCurThread s) s \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s))\<rbrace>
   scheduleChooseNewThread
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding scheduleChooseNewThread_def
     apply (wp add: ssa_no_orphans hoare_vcg_all_lift)
         apply (wp hoare_disjI1 chooseThread_nosch)+
    apply (wp nextDomain_invs_no_cicd' hoare_vcg_imp_lift
               hoare_lift_Pf2 [OF tcbQueued_all_queued_tcb_ptrs_lift[OF nextDomain_tcbQueued]
                                  nextDomain_ct']
               hoare_lift_Pf2 [OF st_tcb_at'_is_active_tcb_ptr_lift[OF nextDomain_st_tcb_at']
                                  nextDomain_ct']
               hoare_vcg_all_lift getDomainTime_wp)[2]
   apply (wpsimp simp: if_apply_def2 invs'_invs_no_cicd all_queued_tcb_ptrs_def
                       is_active_tcb_ptr_runnable')+
  done

lemma setSchedulerAction_tcbQueued[wp]:
  "setSchedulerAction sa \<lbrace>\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s)\<rbrace>"
  by wpsimp

lemma schedule_no_orphans[wp]:
  notes ssa_wp[wp del]
  shows
  "\<lbrace>no_orphans and invs'\<rbrace> schedule \<lbrace>\<lambda>_. no_orphans\<rbrace>"
proof -

  have do_switch_to:
    "\<And>candidate.
     \<lbrace>\<lambda>s. no_orphans s \<and> ksSchedulerAction s = SwitchToThread candidate
          \<and> st_tcb_at' runnable' candidate s
          \<and> (st_tcb_at' runnable' (ksCurThread s) s \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s) \<rbrace>
     do ThreadDecls_H.switchToThread candidate;
        setSchedulerAction ResumeCurrentThread
     od
     \<lbrace>\<lambda>_. no_orphans\<rbrace>"
    apply (wpsimp wp: scheduleChooseNewThread_no_orphans ssa_no_orphans
                      hoare_vcg_all_lift ThreadDecls_H_switchToThread_no_orphans)+
     apply (rule_tac Q="\<lambda>_ s. (t = candidate \<longrightarrow> ksCurThread s = candidate) \<and>
                               (t \<noteq> candidate \<longrightarrow> sch_act_not t s)"
              in hoare_post_imp)
      apply (wpsimp wp: stt_nosch hoare_weak_lift_imp)+
    apply (fastforce dest!: in_all_active_tcb_ptrsD simp: all_queued_tcb_ptrs_def comp_def)
    done

  have abort_switch_to_enq:
    "\<And>candidate.
     \<lbrace>\<lambda>s. no_orphans s \<and> invs' s
          \<and> ksSchedulerAction s = SwitchToThread candidate
          \<and> (st_tcb_at' runnable' (ksCurThread s) s \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s) \<rbrace>
     do tcbSchedEnqueue candidate;
        setSchedulerAction ChooseNewThread;
        scheduleChooseNewThread
     od
     \<lbrace>\<lambda>_. no_orphans\<rbrace>"
    apply (wpsimp wp: scheduleChooseNewThread_no_orphans ssa_no_orphans setSchedulerAction_direct)
      apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift
                  simp: is_active_tcb_ptr_runnable' all_queued_tcb_ptrs_def
             | rule hoare_lift_Pf2[where f=ksCurThread, OF setSchedulerAction_tcbQueued])+
     apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift
            | strengthen not_pred_tcb_at'_strengthen
            | rule hoare_lift_Pf2[where f=ksCurThread])+
    apply (simp add: st_tcb_at_neg' tcb_at_invs' all_queued_tcb_ptrs_def)
    done

  have abort_switch_to_app:
    "\<And>candidate.
     \<lbrace>\<lambda>s. no_orphans s \<and> invs' s
          \<and> ksSchedulerAction s = SwitchToThread candidate
          \<and> (st_tcb_at' runnable' (ksCurThread s) s
             \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s ) \<rbrace>
     do tcbSchedAppend candidate;
        setSchedulerAction ChooseNewThread;
        scheduleChooseNewThread
     od
     \<lbrace>\<lambda>_. no_orphans\<rbrace>"
    apply (wpsimp wp: scheduleChooseNewThread_no_orphans ssa_no_orphans setSchedulerAction_direct)
      apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift
                  simp: is_active_tcb_ptr_runnable' all_queued_tcb_ptrs_def
             | rule hoare_lift_Pf2[where f=ksCurThread, OF setSchedulerAction_tcbQueued])+
     apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift
            | strengthen not_pred_tcb_at'_strengthen
            | rule hoare_lift_Pf2[where f=ksCurThread])+
    apply (simp add: st_tcb_at_neg' tcb_at_invs' all_queued_tcb_ptrs_def)
    done

  show ?thesis
    supply K_bind_def[simp del]
    unfolding schedule_def
    apply (wp, wpc)
         \<comment> \<open>action = ResumeCurrentThread\<close>
         apply (wp)[1]
        \<comment> \<open>action = ChooseNewThread\<close>
        apply (clarsimp simp: when_def scheduleChooseNewThread_def)
        apply (wp ssa_no_orphans hoare_vcg_all_lift)
            apply (wp hoare_disjI1 chooseThread_nosch)
           apply (wp nextDomain_invs_no_cicd' hoare_vcg_imp_lift
                     hoare_lift_Pf2 [OF tcbQueued_all_queued_tcb_ptrs_lift
                                      [OF nextDomain_tcbQueued]
                                      nextDomain_ct']
                     hoare_lift_Pf2 [OF st_tcb_at'_is_active_tcb_ptr_lift
                                      [OF nextDomain_st_tcb_at']
                                      nextDomain_ct']
                     hoare_vcg_all_lift getDomainTime_wp)[2]
          apply wpsimp
         apply ((wp tcbSchedEnqueue_no_orphans tcbSchedEnqueue_all_queued_tcb_ptrs'
                    hoare_drop_imp
                 | clarsimp simp: all_queued_tcb_ptrs_def
                 | strengthen all_invs_but_ct_idle_or_in_cur_domain'_strg
                 | wps)+)[1]
        apply wpsimp
       \<comment> \<open>action = SwitchToThread candidate\<close>
       apply (clarsimp)
       apply (rename_tac candidate)
       apply (wpsimp wp: do_switch_to abort_switch_to_enq abort_switch_to_app)
              (* isHighestPrio *)
              apply (wp hoare_drop_imps)
             apply (wp add: tcbSchedEnqueue_no_orphans)+
        apply (clarsimp simp: conj_comms cong: conj_cong imp_cong split del: if_split)
        apply (wp hoare_vcg_imp_lift'
               | strengthen not_pred_tcb_at'_strengthen)+
        apply (wps | wpsimp wp: tcbSchedEnqueue_all_queued_tcb_ptrs')+
    apply (fastforce simp: is_active_tcb_ptr_runnable' all_invs_but_ct_idle_or_in_cur_domain'_strg
                           invs_switchToThread_runnable')
    done
qed

lemma setNotification_no_orphans[wp]:
  "setNotification p ntfn \<lbrace> no_orphans \<rbrace>"
  by (rule no_orphans_lift; wpsimp simp: setNotification_def updateObject_default_def)

crunch no_orphans [wp]: doMachineOp "no_orphans"
  (wp: no_orphans_lift)

crunch no_orphans [wp]: setMessageInfo "no_orphans"

crunch no_orphans [wp]: completeSignal "no_orphans"
  (simp: crunch_simps wp: crunch_wps)

lemma possibleSwitchTo_almost_no_orphans [wp]:
  "\<lbrace>\<lambda>s. almost_no_orphans target s \<and> st_tcb_at' runnable' target s
        \<and> weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   possibleSwitchTo target
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding possibleSwitchTo_def
  by (wpsimp wp: tcbSchedEnqueue_almost_no_orphans
                 ssa_almost_no_orphans hoare_weak_lift_imp
     | wp (once) hoare_drop_imp)+

lemma possibleSwitchTo_almost_no_orphans':
  "\<lbrace>\<lambda>s. almost_no_orphans target s \<and> st_tcb_at' runnable' target s
        \<and> sch_act_wf (ksSchedulerAction s) s \<rbrace>
   possibleSwitchTo target
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  by wp (strengthen sch_act_wf_weak, assumption)

crunches tcbQueueAppend, tcbQueuePrepend
  for almost_no_orphans[wp]: "almost_no_orphans tcbPtr"

lemma tcbSchedAppend_almost_no_orphans:
  "\<lbrace>almost_no_orphans thread\<rbrace>
   tcbSchedAppend thread
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp wp: tcbQueued_update_True_no_orphans threadGet_wp)
  apply (fastforce simp: almost_no_orphans_def no_orphans_def all_queued_tcb_ptrs_def obj_at'_def)
  done

lemma no_orphans_is_almost[simp]:
  "no_orphans s \<Longrightarrow> almost_no_orphans t s"
  by (clarsimp simp: no_orphans_def almost_no_orphans_def)

crunches decDomainTime
  for no_orphans[wp]: no_orphans
  (wp: no_orphans_lift)

lemma timerTick_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   timerTick
   \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  unfolding timerTick_def getDomainTime_def
  supply if_split[split del]
  apply (subst threadState_case_if)
  apply (wpsimp wp: threadSet_no_orphans tcbSchedAppend_almost_no_orphans
                    threadSet_almost_no_orphans threadSet_no_orphans tcbSchedAppend_sch_act_wf
                    hoare_drop_imp
                simp: if_apply_def2
         | strengthen sch_act_wf_weak)+
  done

lemma handleDoubleFault_no_orphans [wp]:
  "\<lbrace>no_orphans\<rbrace> handleDoubleFault tptr ex1 ex2 \<lbrace>\<lambda>_. no_orphans \<rbrace>"
  unfolding handleDoubleFault_def
  by (wpsimp wp: setThreadState_not_active_no_orphans
             simp: is_active_thread_state_def isRestart_def isRunning_def)

crunch st_tcb' [wp]: getThreadCallerSlot "st_tcb_at' (\<lambda>st. P st) t"

crunches cteInsert, getThreadCallerSlot, getThreadReplySlot
  for almost_no_orphans[wp]: "almost_no_orphans tcb_ptr"
  and no_orphans[wp]: no_orphans
  (wp: crunch_wps)

lemma setupCallerCap_no_orphans [wp]:
  "setupCallerCap sender receiver gr \<lbrace>no_orphans\<rbrace>"
  unfolding setupCallerCap_def
  by (wpsimp wp: setThreadState_not_active_no_orphans hoare_drop_imps
             simp: is_active_thread_state_def isRestart_def isRunning_def)

lemma setupCallerCap_almost_no_orphans [wp]:
  "\<lbrace>almost_no_orphans tcb_ptr\<rbrace>
   setupCallerCap sender receiver gr
   \<lbrace>\<lambda>_. almost_no_orphans tcb_ptr\<rbrace>"
  unfolding setupCallerCap_def
  by (wpsimp wp: setThreadState_not_active_almost_no_orphans hoare_drop_imps
             simp: is_active_thread_state_def isRestart_def isRunning_def)

crunches cteInsert, setExtraBadge, setMessageInfo, transferCaps, copyMRs,
         doNormalTransfer, doFaultTransfer,
         invalidateVMIDEntry, invalidateASID, invalidateASIDEntry
  for tcbQueued[wp]: "obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr"
  (wp: crunch_wps simp: crunch_simps)

crunches doIPCTransfer, setMRs
  for no_orphans [wp]: "no_orphans"
  (wp: no_orphans_lift)

crunch ksQ'[wp]: setEndpoint "\<lambda>s. P (ksReadyQueues s)"
  (wp: setObject_queues_unchanged_tcb updateObject_default_inv)

crunch no_orphans [wp]: setEndpoint "no_orphans"
  (wp: no_orphans_lift)

lemma sendIPC_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   sendIPC blocking call badge canGrant canGrantReply thread epptr
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding sendIPC_def
  apply (wp hoare_drop_imps setThreadState_not_active_no_orphans sts_st_tcb'
            possibleSwitchTo_almost_no_orphans'
         | wpc
         | clarsimp simp: is_active_thread_state_def isRestart_def isRunning_def)+
   apply (rule_tac Q="\<lambda>rv. no_orphans and valid_objs' and ko_at' rv epptr
                           and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp)
    apply (fastforce simp: valid_objs'_def valid_obj'_def valid_ep'_def obj_at'_def)
   apply (wp get_ep_sp' | clarsimp)+
  done

lemma sendFaultIPC_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   sendFaultIPC tptr fault
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding sendFaultIPC_def
  apply (wpsimp wp: threadSet_no_orphans threadSet_valid_objs' threadSet_sch_act)
    apply (rule_tac Q'="\<lambda>_ s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s"
                    in hoare_strengthen_postE_R)
     apply wpsimp+
  done

lemma handleFault_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   handleFault tptr ex1
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding handleFault_def
  by wpsimp

lemma replyFromKernel_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   replyFromKernel thread r
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  by (wpsimp simp: replyFromKernel_def)

crunch inv [wp]: alignError "P"

lemma createObjects_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> pspace_aligned' s \<and> pspace_no_overlap' ptr sz s \<and> pspace_distinct' s
        \<and> n \<noteq> 0 \<and> range_cover ptr sz (objBitsKO val + gbits) n
        \<and> \<not> case_option False (is_active_thread_state \<circ> tcbState) (projectKO_opt val)
        \<and> \<not> case_option False tcbQueued (projectKO_opt val)\<rbrace>
   createObjects ptr n val gbits
   \<lbrace>\<lambda>_ s. no_orphans s\<rbrace>"
  apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                        is_active_tcb_ptr_def all_queued_tcb_ptrs_def)
  apply (simp only: imp_conv_disj pred_tcb_at'_def createObjects_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift createObjects_orig_obj_at2'[where sz=sz])
  apply (clarsimp split: option.splits)
  done

crunch no_orphans [wp]: insertNewCap "no_orphans"
  (wp: hoare_drop_imps)

lemma no_orphans_ksArchState_idem[simp]:
  "no_orphans (s\<lparr>ksArchState := f (ksArchState s)\<rparr>) = no_orphans s"
  unfolding no_orphans_def all_queued_tcb_ptrs_def all_active_tcb_ptrs_def is_active_tcb_ptr_def
  by clarsimp

lemma createNewCaps_no_orphans:
  "\<lbrace> (\<lambda>s. no_orphans s
         \<and>  pspace_aligned' s \<and> pspace_distinct' s
         \<and>  pspace_no_overlap' ptr sz s
         \<and>  (tp = APIObjectType CapTableObject \<longrightarrow> us > 0))
         and K (range_cover ptr sz (APIType_capBits tp us) n \<and> 0 < n) \<rbrace>
   createNewCaps tp ptr n us d
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: createNewCaps_def toAPIType_def cong: option.case_cong)
  apply (cases tp; simp)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp)
            apply (wpsimp wp: mapM_x_wp' threadSet_no_orphans
                   | clarsimp simp: is_active_thread_state_def makeObject_tcb
                                    projectKO_opt_tcb isRunning_def isRestart_def
                                    APIType_capBits_def Arch_createNewCaps_def
                                    objBits_if_dev
                   | simp add: objBits_simps mult_2 nat_arith.add1 split: if_split)+
  done

crunches updatePTType
  for no_orphans[wp]: "no_orphans"
  (wp: no_orphans_lift)

lemma createObject_no_orphans:
  "\<lbrace>pspace_no_overlap' ptr sz and pspace_aligned' and pspace_distinct' and
    cte_wp_at' (\<lambda>cte. cteCap cte = (capability.UntypedCap d ptr sz idx)) cref and
    K (range_cover ptr sz (APIType_capBits tp us) (Suc 0)) and no_orphans\<rbrace>
   RetypeDecls_H.createObject tp ptr us d
   \<lbrace>\<lambda>xa. no_orphans\<rbrace>"
  apply (simp only: createObject_def AARCH64_H.createObject_def placeNewObject_def2)
  apply (wpsimp wp: createObjects'_wp_subst threadSet_no_orphans
                    createObjects_no_orphans[where sz = sz]
                simp: placeNewObject_def2 placeNewDataObject_def
                      projectKO_opt_tcb cte_wp_at_ctes_of projectKO_opt_ep
                      is_active_thread_state_def makeObject_tcb pageBits_def unless_def
                      projectKO_opt_tcb isRunning_def isRestart_def
                      APIType_capBits_def objBits_simps
                split_del: if_split)
  apply (clarsimp simp: toAPIType_def APIType_capBits_def objBits_simps
                        bit_simps
                  split: object_type.split_asm apiobject_type.split_asm if_splits)
  done

lemma createNewObjects_no_orphans:
  "\<lbrace>\<lambda>s. no_orphans s \<and> invs' s \<and> pspace_no_overlap' ptr sz s
         \<and> (\<forall>slot\<in>set slots. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s)
         \<and> cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d (ptr && ~~ mask sz) sz idx) cref s
         \<and> caps_no_overlap'' ptr sz s
         \<and> range_cover ptr sz (APIType_capBits tp us) (length slots)
         \<and> (tp = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> us > 0)
         \<and> caps_overlap_reserved' {ptr..ptr + of_nat (length slots) * 2 ^ APIType_capBits tp us - 1} s
         \<and> slots \<noteq> [] \<and> distinct slots \<and> ptr \<noteq> 0
         \<and> sz \<le> maxUntypedSizeBits \<and> canonical_address (ptr && ~~ mask sz)\<rbrace>
   createNewObjects tp cref slots ptr us d
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (rule hoare_pre)
   apply (rule createNewObjects_wp_helper; simp?)
   apply (simp add:insertNewCaps_def)
   apply wp
    apply (rule_tac P = "length caps = length slots" in hoare_gen_asm)
    apply (wp zipWithM_x_inv)
    apply simp
   apply (wp createNewCaps_no_orphans[where sz = sz] | clarsimp)+
   apply (rule hoare_strengthen_post[OF createNewCaps_ret_len])
   apply simp
  apply (clarsimp simp:invs_pspace_aligned' invs_valid_pspace' invs_pspace_distinct')
  apply (intro conjI)
     apply (erule range_cover.range_cover_n_less[where 'a=machine_word_len, folded word_bits_def])
    apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (simp add:invs'_def valid_state'_def)
  apply (simp add: invs_ksCurDomain_maxDomain')
  done

lemma ksMachineState_ksPSpace_upd_comm:
  "ksPSpace_update g (ksMachineState_update f s) =
   ksMachineState_update f (ksPSpace_update g s)"
  by simp

lemma deleteObjects_no_orphans [wp]:
  "\<lbrace> (\<lambda>s. no_orphans s \<and> pspace_distinct' s) and K (is_aligned ptr bits) \<rbrace>
   deleteObjects ptr bits
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (rule hoare_gen_asm)
  apply (unfold deleteObjects_def2 doMachineOp_def split_def)
  apply wpsimp
  apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                        all_queued_tcb_ptrs_def is_active_tcb_ptr_def
                        ksMachineState_ksPSpace_upd_comm)
  apply (drule_tac x=tcb_ptr in spec)
  apply (clarsimp simp: pred_tcb_at'_def obj_at_delete')
  done

crunch no_orphans[wp]: updateFreeIndex "no_orphans"

lemma resetUntypedCap_no_orphans [wp]:
  "\<lbrace> (\<lambda>s. no_orphans s \<and> pspace_distinct' s \<and> valid_objs' s)
      and cte_wp_at' (isUntypedCap o cteCap) slot\<rbrace>
    resetUntypedCap slot
  \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (simp add: resetUntypedCap_def)
  apply (wpsimp wp: mapME_x_inv_wp preemptionPoint_inv getSlotCap_wp hoare_drop_imps
                split_del: if_split)
  apply (clarsimp simp: cte_wp_at_ctes_of split del: if_split)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD])
  apply (clarsimp simp: isCap_simps valid_cap_simps' capAligned_def)
  done

lemma invokeUntyped_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_untyped_inv' ui s \<and> ct_active' s \<rbrace>
   invokeUntyped ui
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (rule hoare_chain, rule invokeUntyped_invs''[where Q=no_orphans])
       apply (wp createNewCaps_no_orphans)+
      apply (fastforce simp: valid_pspace'_def)
     apply wpsimp+
   apply (cases ui, auto simp: cte_wp_at_ctes_of)[2]
  done

lemma setInterruptState_no_orphans [wp]:
  "setInterruptState a \<lbrace>no_orphans\<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)

crunch no_orphans [wp]: emptySlot "no_orphans"

lemma mapM_x_match:
  "\<lbrace>I and V xs\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace> \<Longrightarrow> \<lbrace>I and V xs\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  by assumption

lemma cancelAllIPC_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding cancelAllIPC_def
  apply (wp sts_valid_objs' set_ep_valid_objs' sts_st_tcb'
            hoare_vcg_const_Ball_lift tcbSchedEnqueue_almost_no_orphans
             | wpc
             | rule mapM_x_match,
               rename_tac list,
               rule_tac V="\<lambda>_. valid_objs' and pspace_aligned' and pspace_distinct'"
                    and I="no_orphans and (\<lambda>s. \<forall>t\<in>set list. tcb_at' t s)"
                     in mapM_x_inv_wp2
             | clarsimp simp: valid_tcb_state'_def)+
  apply (rule_tac Q="\<lambda>rv. no_orphans and valid_objs' and pspace_aligned' and pspace_distinct' and
                          ko_at' rv epptr"
                 in hoare_post_imp)
   apply (fastforce simp: valid_obj'_def valid_ep'_def obj_at'_def)
  apply (wp get_ep_sp' | clarsimp)+
  done

lemma cancelAllSignals_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
    cancelAllSignals ntfn
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding cancelAllSignals_def
  apply (wp sts_valid_objs' set_ntfn_valid_objs' sts_st_tcb'
            hoare_vcg_const_Ball_lift tcbSchedEnqueue_almost_no_orphans
             | wpc
             | clarsimp simp: valid_tcb_state'_def)+
    apply (rename_tac list)
    apply (rule_tac V="\<lambda>_. valid_objs' and pspace_aligned' and pspace_distinct'"
                and I="no_orphans and (\<lambda>s. \<forall>t\<in>set list. tcb_at' t s)"
                in mapM_x_inv_wp2)
    apply simp
   apply (wp sts_valid_objs' set_ntfn_valid_objs' sts_st_tcb'
            hoare_vcg_const_Ball_lift tcbSchedEnqueue_almost_no_orphans|
          clarsimp simp: valid_tcb_state'_def)+
  apply (rule_tac Q="\<lambda>rv. no_orphans and valid_objs' and pspace_aligned' and pspace_distinct' and
                          ko_at' rv ntfn"
                 in hoare_post_imp)
   apply (fastforce simp: valid_obj'_def valid_ntfn'_def obj_at'_def)
  apply (wp get_ntfn_sp' | clarsimp)+
  done

crunches setBoundNotification, unbindNotification, unbindMaybeNotification
  for no_orphans[wp]: no_orphans

lemma finaliseCapTrue_standin_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
    finaliseCapTrue_standin cap final
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding finaliseCapTrue_standin_def Let_def
  by wpsimp

lemma cteDeleteOne_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   cteDeleteOne slot
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding cteDeleteOne_def
  by (wpsimp wp: assert_inv haskell_assert_inv isFinalCapability_inv weak_if_wp)

crunch valid_objs' [wp]: getThreadReplySlot "valid_objs'"

lemma cancelSignal_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s\<rbrace>
   cancelSignal t ntfn
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding cancelSignal_def Let_def
  by (wpsimp wp: hoare_drop_imps setThreadState_not_active_no_orphans
             simp: is_active_thread_state_def isRestart_def isRunning_def)

lemma cancelIPC_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   cancelIPC t
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding cancelIPC_def Let_def
  by (wpsimp wp: setThreadState_not_active_no_orphans hoare_drop_imps weak_if_wp
                 threadSet_valid_objs' threadSet_no_orphans
             simp: is_active_thread_state_def isRestart_def isRunning_def inQ_def)

lemma asUser_almost_no_orphans:
  "\<lbrace>almost_no_orphans t\<rbrace> asUser a f \<lbrace>\<lambda>_. almost_no_orphans t\<rbrace>"
  unfolding almost_no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma sendSignal_no_orphans [wp]:
  "\<lbrace>\<lambda>s. no_orphans s  \<and> valid_objs' s \<and> pspace_aligned' s \<and> pspace_distinct' s \<and>
        sch_act_wf (ksSchedulerAction s) s\<rbrace>
   sendSignal ntfnptr badge
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding sendSignal_def
  by (wpsimp wp: sts_st_tcb' gts_wp' getNotification_wp asUser_almost_no_orphans
                 cancelIPC_weak_sch_act_wf
             simp: sch_act_wf_weak)

crunches vgicUpdateLR
  for no_orphans[wp]: "no_orphans"
  (wp: no_orphans_lift crunch_wps)

crunch not_pred_tcb_at'[wp]: vgicUpdateLR,doMachineOp "\<lambda>s. \<not> (pred_tcb_at' proj P' t) s"

crunches vcpuUpdate, vgicUpdateLR, doMachineOp
  for no_orphans[wp]: no_orphans
  and tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' t"
  (wp: no_orphans_lift tcb_in_cur_domain'_lift)

lemma vgicMaintenance_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   vgicMaintenance
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding vgicMaintenance_def Let_def
  by (wpsimp wp: sch_act_wf_lift hoare_drop_imp[where f="vgicUpdateLR v idx virq" for v idx virq]
                 hoare_drop_imp[where f="return v" for v]
                 hoare_drop_imp[where f="doMachineOp f" for f])

lemma vppiEvent_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   vppiEvent irq
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding vppiEvent_def Let_def
  by (wpsimp wp: hoare_vcg_imp_lift' sch_act_wf_lift | wps)+

(* FIXME AARCH64: move *)
lemma irqVPPIEventIndex_irqVGICMaintenance_None[simp]:
  "irqVPPIEventIndex irqVGICMaintenance = None"
  unfolding irqVTimerEvent_def irqVGICMaintenance_def IRQ_def irqVPPIEventIndex_def
  by simp

lemma handleReservedIRQ_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   handleReservedIRQ irq
   \<lbrace>\<lambda>_. no_orphans \<rbrace>"
  unfolding handleReservedIRQ_def
  by (case_tac "irq = irqVGICMaintenance"; wpsimp)

lemma handleInterrupt_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   handleInterrupt irq
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding handleInterrupt_def
  supply if_split[split del]
  apply (wp hoare_drop_imps hoare_vcg_all_lift getIRQState_inv
         | wpc | clarsimp simp: invs'_def valid_state'_def maskIrqSignal_def
                                if_apply_def2)+
  apply fastforce
  done

lemma updateRestartPC_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   updateRestartPC t
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  by (wpsimp simp: updateRestartPC_def asUser_no_orphans)

lemma suspend_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_at' t s \<rbrace>
   suspend t
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding suspend_def
  apply (wp | clarsimp simp: unless_def | rule conjI)+
      apply (clarsimp simp: is_active_tcb_ptr_def is_active_thread_state_def st_tcb_at_neg2)
      apply (wp setThreadState_not_active_no_orphans hoare_disjI1 setThreadState_st_tcb
             | clarsimp simp: is_active_thread_state_def isRunning_def isRestart_def)+
    apply (wp hoare_drop_imp)+
  apply auto
  done

crunches invalidateASIDEntry, invalidateTLBByASID
  for no_orphans[wp]: no_orphans
  (wp: no_orphans_lift)

lemma deleteASIDPool_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   deleteASIDPool asid pool
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding deleteASIDPool_def
  apply (wp | clarsimp)+
     apply (rule_tac Q="\<lambda>rv s. no_orphans s" in hoare_post_imp)
      apply (clarsimp simp: no_orphans_def all_queued_tcb_ptrs_def
                            all_active_tcb_ptrs_def is_active_tcb_ptr_def)
     apply (wp mapM_wp_inv getObject_inv loadObject_default_inv | clarsimp)+
  done

lemma storePTE_no_orphans [wp]:
  "storePTE ptr val \<lbrace> no_orphans \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma archThreadSet_tcbQueued_inv[wp]:
  "archThreadSet f t \<lbrace>\<lambda>s. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s\<rbrace>"
  unfolding archThreadSet_def
  by (wp setObject_tcb_strongest getObject_tcb_wp) (fastforce simp: obj_at'_def)

crunches dissociateVCPUTCB
  for tcbQueued_inv[wp]: "\<lambda>s. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t s"
  (wp: threadGet_wp crunch_wps asUser_tcbQueued_inv simp: crunch_simps)

crunches modifyArchState, vcpuUpdate, archThreadSet, dissociateVCPUTCB, vcpuFinalise
  for no_orphans[wp]: "no_orphans"
  (wp: no_orphans_lift crunch_wps)

crunch no_orphans [wp]: unmapPage "no_orphans"
  (wp: crunch_wps)

crunches unmapPageTable, prepareThreadDelete
  for no_orphans [wp]: "no_orphans"
  (wp: lookupPTSlotFromLevel_inv)

lemma setASIDPool_no_orphans [wp]:
  "setObject p (ap :: asidpool) \<lbrace> no_orphans \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)

crunches deleteASID, Arch.finaliseCap
  for no_orphans [wp]: "no_orphans"
  (wp: getObject_inv loadObject_default_inv)

lemma deletingIRQHandler_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   deletingIRQHandler irq
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding deletingIRQHandler_def
  by (wpsimp wp: hoare_drop_imps) auto

lemma finaliseCap_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> valid_cap' cap s \<rbrace>
   finaliseCap cap final flag
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (wpsimp simp: finaliseCap_def Let_def split_del: if_split)
  apply (auto simp: valid_cap'_def dest!: isCapDs)
  done

crunches cteSwap, capSwapForDelete
  for no_orphans[wp]: "no_orphans"

declare withoutPreemption_lift [wp del]

lemma no_orphans_finalise_prop_stuff:
  "no_cte_prop no_orphans = no_orphans"
  "finalise_prop_stuff no_orphans"
  by (simp_all add: no_cte_prop_def finalise_prop_stuff_def
                    setCTE_no_orphans,
      simp_all add: no_orphans_def all_active_tcb_ptrs_def
                    is_active_tcb_ptr_def all_queued_tcb_ptrs_def)

lemma finaliseSlot_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> (\<not> e \<longrightarrow> ex_cte_cap_to' slot s) \<rbrace>
    finaliseSlot slot e
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding finaliseSlot_def
  apply (rule validE_valid, rule hoare_pre, rule hoare_strengthen_postE, rule use_spec)
     apply (rule finaliseSlot_invs'[where p=slot and slot=slot and Pr=no_orphans])
      apply (simp_all add: no_orphans_finalise_prop_stuff)
   apply wpsimp
   apply (auto dest: cte_wp_at_valid_objs_valid_cap')
  done

lemma cteDelete_no_orphans [wp]:
  "\<lbrace> no_orphans and invs' and sch_act_simple and K ex \<rbrace>
   cteDelete ptr ex
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: cteDelete_def whenE_def split_def)
  apply (rule hoare_pre, wp)
  apply clarsimp
  done

crunch no_orphans [wp]: cteMove "no_orphans"
  (wp: crunch_wps)

lemma cteRevoke_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<rbrace>
   cteRevoke ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. no_orphans s \<and> invs' s \<and> sch_act_simple s" in hoare_strengthen_post)
   apply (wpsimp wp: cteRevoke_preservation cteDelete_invs' cteDelete_sch_act_simple)+
  done

lemma cancelBadgedSends_no_orphans [wp]:
  "cancelBadgedSends epptr badge \<lbrace>no_orphans\<rbrace>"
  unfolding cancelBadgedSends_def
  by (wpsimp wp: filterM_preserved tcbSchedEnqueue_almost_no_orphans gts_wp' sts_st_tcb'
      | wp (once) hoare_drop_imps)+

crunch no_orphans [wp]: handleFaultReply "no_orphans"

lemma doReplyTransfer_no_orphans[wp]:
  "\<lbrace>no_orphans and invs' and tcb_at' sender and tcb_at' receiver\<rbrace>
   doReplyTransfer sender receiver slot grant
   \<lbrace>\<lambda>rv. no_orphans\<rbrace>"
  unfolding doReplyTransfer_def
  apply (wp sts_st_tcb' setThreadState_not_active_no_orphans threadSet_no_orphans
            threadSet_weak_sch_act_wf
         | wpc | clarsimp simp: is_active_thread_state_def isRunning_def isRestart_def
         | wp (once) hoare_drop_imps
         | strengthen sch_act_wf_weak)+
              apply (rule_tac Q="\<lambda>rv. invs' and no_orphans" in hoare_post_imp)
               apply (fastforce simp: inQ_def)
              apply (wp hoare_drop_imps | clarsimp)+
  apply (clarsimp simp:invs'_def valid_state'_def valid_pspace'_def)
  done

crunch no_orphans [wp]: setupReplyMaster "no_orphans"
  (wp: crunch_wps simp: crunch_simps)

lemma restart_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_at' t s \<rbrace>
   restart t
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding restart_def isStopped_def2
  apply (wp tcbSchedEnqueue_almost_no_orphans sts_st_tcb' cancelIPC_weak_sch_act_wf
         | clarsimp simp: o_def if_apply_def2
         | strengthen no_orphans_strg_almost
         | wp (once) hoare_drop_imps)+
  apply auto
  done

lemma readreg_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_at' src s \<rbrace>
     invokeTCB (tcbinvocation.ReadRegisters src susp n arch)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def
  by wpsimp

lemma writereg_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s
       \<and> tcb_at' dest s \<and> ex_nonz_cap_to' dest s\<rbrace>
     invokeTCB (tcbinvocation.WriteRegisters dest resume values arch)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def postModifyRegisters_def
  by (wp hoare_vcg_if_lift hoare_vcg_conj_lift restart_invs' hoare_weak_lift_imp
      | strengthen
      | clarsimp  simp: invs'_def valid_state'_def dest!: global'_no_ex_cap )+

lemma copyreg_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_at' src s
         \<and> tcb_at' dest s \<and> ex_nonz_cap_to' src s \<and> ex_nonz_cap_to' dest s \<rbrace>
     invokeTCB (tcbinvocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def postModifyRegisters_def
  apply simp
  apply (wp hoare_vcg_if_lift hoare_weak_lift_imp)
      apply (wp hoare_weak_lift_imp hoare_vcg_conj_lift hoare_drop_imp mapM_x_wp' restart_invs'
                restart_no_orphans asUser_no_orphans suspend_nonz_cap_to_tcb
             | wpc | simp add: if_apply_def2)+
  apply (fastforce simp: invs'_def valid_state'_def dest!: global'_no_ex_cap)
  done

lemma settlsbase_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
     invokeTCB (tcbinvocation.SetTLSBase src dest)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def
  by (wpsimp wp: hoare_vcg_imp_lift' mapM_x_wp' asUser_no_orphans)

lemma almost_no_orphans_no_orphans:
  "\<lbrakk> almost_no_orphans t s; \<not> is_active_tcb_ptr t s \<rbrakk> \<Longrightarrow> no_orphans s"
  by (auto simp: almost_no_orphans_def no_orphans_def all_active_tcb_ptrs_def)

lemma almost_no_orphans_no_orphans':
  "\<lbrakk> almost_no_orphans t s; ksCurThread s = t\<rbrakk> \<Longrightarrow> no_orphans s"
  by (auto simp: almost_no_orphans_def no_orphans_def all_active_tcb_ptrs_def)

lemma setPriority_no_orphans[wp]:
  "\<lbrace>no_orphans and invs' and tcb_at' tptr\<rbrace>
   setPriority tptr prio
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding setPriority_def
  apply wpsimp
    apply (rule_tac Q="\<lambda>_ s. almost_no_orphans tptr s \<and> weak_sch_act_wf (ksSchedulerAction s) s" in hoare_post_imp)
     apply clarsimp
     apply (clarsimp simp: is_active_tcb_ptr_runnable' pred_tcb_at'_def obj_at'_def
                           almost_no_orphans_no_orphans elim!: almost_no_orphans_no_orphans')
    apply (wp threadSet_almost_no_orphans | clarsimp simp: inQ_def)+
    apply (wpsimp wp: threadSet_weak_sch_act_wf)
   apply (wp tcbSchedDequeue_almost_no_orphans| clarsimp)+
  done

crunches bindNotification, setMCPriority
  for no_orphans[wp]: no_orphans

lemma threadSet_ipcbuffer_invs:
  "is_aligned a msg_align_bits \<Longrightarrow>
  \<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbIPCBuffer_update (\<lambda>_. a)) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wp threadSet_invs_trivial, simp_all add: inQ_def cong: conj_cong)

lemma tc_no_orphans:
  "\<lbrace> no_orphans and invs' and sch_act_simple and tcb_at' a and ex_nonz_cap_to' a and
    case_option \<top> (valid_cap' o fst) e' and
    K (case_option True (isCNodeCap o fst) e') and
    case_option \<top> (valid_cap' o fst) f' and
    K (case_option True (isValidVTableRoot o fst) f') and
    case_option \<top> (valid_cap') (case_option None (case_option None (Some o fst) o snd) g) and
    K (case_option True isArchObjectCap (case_option None (case_option None (Some o fst) o snd) g)) and
    K (case_option True (swp is_aligned 2 o fst) g) and
    K (case_option True (swp is_aligned msg_align_bits o fst) g) and
    K (case g of None \<Rightarrow> True | Some x \<Rightarrow> (case_option True (isArchObjectCap \<circ> fst) \<circ> snd) x) and
    K (valid_option_prio d \<and> valid_option_prio mcp) \<rbrace>
      invokeTCB (tcbinvocation.ThreadControl a sl b' mcp d e' f' g)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_gen_asm)
  apply (rule hoare_gen_asm)
  apply (simp add: invokeTCB_def getThreadCSpaceRoot getThreadVSpaceRoot
                   getThreadBufferSlot_def split_def)
  apply (simp only: eq_commute[where a="a"])
  apply (rule hoare_walk_assmsE)
    apply (clarsimp simp: pred_conj_def option.splits[where P="\<lambda>x. x s" for s])
    apply ((wp case_option_wp threadSet_no_orphans threadSet_invs_trivial
               threadSet_cap_to' hoare_vcg_all_lift hoare_weak_lift_imp | clarsimp simp: inQ_def)+)[2]
  apply (rule hoare_walk_assmsE)
    apply (cases mcp; clarsimp simp: pred_conj_def option.splits[where P="\<lambda>x. x s" for s])
     apply ((wp case_option_wp threadSet_no_orphans threadSet_invs_trivial setMCPriority_invs'
                typ_at_lifts[OF setMCPriority_typ_at']
                threadSet_cap_to' hoare_vcg_all_lift hoare_weak_lift_imp | clarsimp simp: inQ_def)+)[3]
  apply ((simp only: simp_thms cong: conj_cong
          | wp cteDelete_deletes cteDelete_invs' cteDelete_sch_act_simple
               case_option_wp[where m'="return ()", OF setPriority_no_orphans return_inv,simplified]
               checkCap_inv[where P="valid_cap' c" for c] checkCap_inv[where P=sch_act_simple]
               checkCap_inv[where P=no_orphans] checkCap_inv[where P="tcb_at' a"]
               threadSet_cte_wp_at' hoare_vcg_all_liftE_R hoare_vcg_all_lift threadSet_no_orphans
               hoare_vcg_const_imp_lift_R hoare_weak_lift_imp hoare_drop_imp threadSet_ipcbuffer_invs
          | (simp add: locateSlotTCB_def locateSlotBasic_def objBits_def
                     objBitsKO_def tcbIPCBufferSlot_def tcb_cte_cases_def,
           wp hoare_return_sp)
          | wpc | clarsimp)+)
  apply (fastforce simp: objBits_defs isCap_simps dest!: isValidVTableRootD)
  done

lemma invokeTCB_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_inv_wf' tinv s \<rbrace>
   invokeTCB tinv
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (case_tac tinv; simp; (solves wpsimp)?)
     apply (wpsimp simp: invokeTCB_def)
    apply (wpsimp simp: invokeTCB_def)
   apply (wp tc_no_orphans)
   apply (clarsimp split: option.splits simp: msg_align_bits elim!:is_aligned_weaken)
  apply (wpsimp simp: invokeTCB_def)
  done

lemma invokeCNode_no_orphans [wp]:
  "\<lbrace>no_orphans and invs' and valid_cnode_inv' cinv and sch_act_simple\<rbrace>
   invokeCNode cinv
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding invokeCNode_def
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps unless_wp | wpc | clarsimp split del: if_split)+
  done

crunches performIRQControl, InterruptDecls_H.invokeIRQHandler, performPageTableInvocation,
         performVSpaceInvocation, performPageInvocation, handleVMFault
  for no_orphans[wp]: no_orphans
  (wp: crunch_wps)

lemma handleHypervisorFault_no_orphans[wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s \<and> no_orphans s\<rbrace>
   handleHypervisorFault w f
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding handleHypervisorFault_def isFpuEnable_def
  by (wpsimp wp: undefined_valid)

lemma associateVCPUTCB_no_orphans[wp]:
  "associateVCPUTCB vcpuPtr tcbPtr \<lbrace>no_orphans\<rbrace>"
  unfolding associateVCPUTCB_def
  by (rule no_orphans_lift; wpsimp wp: setObject_typ_at_not)

crunches invokeVCPUInjectIRQ, invokeVCPUWriteReg, invokeVCPUAckVPPI, performARMVCPUInvocation
  for no_orphans [wp]: "no_orphans"
  (wp: crunch_wps simp: crunch_simps)

lemma performASIDControlInvocation_no_orphans [wp]:
  notes [simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                     Int_atLeastAtMost  usableUntypedRange.simps
  shows "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_aci' aci s \<and> ct_active' s \<rbrace>
   performASIDControlInvocation aci
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:valid_aci'_def cte_wp_at_ctes_of
    split:asidcontrol_invocation.splits)
  apply (rename_tac s ptr_base p cref ptr null_cte ut_cte idx)
  proof -
  fix s ptr_base p cref ptr null_cte ut_cte idx
  assume no_orphans: "no_orphans s"
    and  invs'     : "invs' s"
    and  cte       : "ctes_of s p = Some null_cte" "cteCap null_cte = capability.NullCap"
                     "ctes_of s cref = Some ut_cte" "cteCap ut_cte = capability.UntypedCap False ptr_base pageBits idx"
    and  desc      : "descendants_of' cref (ctes_of s) = {}"
    and  misc      : "p \<noteq> cref" "ex_cte_cap_wp_to' (\<lambda>_. True) p s" "sch_act_simple s" "is_aligned ptr asid_low_bits"
                     "asid_wf ptr" "ct_active' s"

  have vc:"s \<turnstile>' UntypedCap False ptr_base pageBits idx"
    using cte misc invs'
    apply -
    apply (case_tac ut_cte)
    apply (rule ctes_of_valid_cap')
     apply simp
    apply fastforce
    done

   hence cover:
    "range_cover ptr_base pageBits pageBits (Suc 0)"
    apply -
    apply (rule range_cover_full)
     apply (simp add:valid_cap'_def capAligned_def)
    apply simp
    done

  have exclude: "cref \<notin> mask_range ptr_base pageBits"
    apply (rule descendants_range_ex_cte'[where cte = "ut_cte"])
        apply (rule empty_descendants_range_in'[OF desc])
       apply (rule if_unsafe_then_capD'[where P = "\<lambda>c. c = ut_cte"])
         apply (clarsimp simp: cte_wp_at_ctes_of cte)
        apply (simp add:invs' invs_unsafe_then_cap')
     apply (simp add:cte invs' add_mask_fold)+
    done

  show "\<lbrace>(=) s\<rbrace>performASIDControlInvocation (asidcontrol_invocation.MakePool ptr_base p cref ptr)
       \<lbrace>\<lambda>reply. no_orphans\<rbrace>"
  apply (clarsimp simp: performASIDControlInvocation_def
                  split: asidcontrol_invocation.splits)
  apply (wp hoare_weak_lift_imp | clarsimp)+
    apply (rule_tac Q="\<lambda>rv s. no_orphans s" in hoare_post_imp)
     apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                           is_active_tcb_ptr_def all_queued_tcb_ptrs_def)
    apply (wp | clarsimp simp:placeNewObject_def2)+
     apply (wp createObjects'_wp_subst)+
     apply (wp hoare_weak_lift_imp updateFreeIndex_pspace_no_overlap'[where sz= pageBits] getSlotCap_wp | simp)+
  apply (strengthen invs_pspace_aligned' invs_pspace_distinct' invs_valid_pspace')
  apply (clarsimp simp:conj_comms)
     apply (wp deleteObjects_invs'[where idx = idx and d=False]
       hoare_vcg_ex_lift deleteObjects_cte_wp_at'[where idx = idx and d=False] hoare_vcg_const_imp_lift )
  using invs' misc cte exclude no_orphans cover
  apply (clarsimp simp: is_active_thread_state_def makeObject_tcb valid_aci'_def
                        cte_wp_at_ctes_of invs_pspace_aligned' invs_pspace_distinct'
                        projectKO_opt_tcb isRunning_def isRestart_def conj_comms
                        invs_valid_pspace' vc objBits_simps range_cover.aligned)
  apply (intro conjI)
    apply (rule vc)
   apply (simp add:descendants_range'_def2)
   apply (rule empty_descendants_range_in'[OF desc])
  apply clarsimp
  done
qed

crunches performASIDPoolInvocation
  for no_orphans[wp]: no_orphans
  (wp: getObject_inv loadObject_default_inv)

lemma arch_performInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_arch_inv' i s \<and> ct_active' s \<rbrace>
   Arch.performInvocation i
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  unfolding AARCH64_H.performInvocation_def performARMMMUInvocation_def
  by (wpsimp simp: valid_arch_inv'_def)

lemma setDomain_no_orphans [wp]:
  "\<lbrace>no_orphans and cur_tcb' and tcb_at' tptr\<rbrace>
   setDomain tptr newdom
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  apply (simp add: setDomain_def when_def)
  apply (wp tcbSchedEnqueue_almost_no_orphans hoare_vcg_imp_lift threadSet_almost_no_orphans
            threadSet_st_tcb_at2 hoare_vcg_disj_lift
            threadSet_no_orphans
         | clarsimp simp: st_tcb_at_neg2 not_obj_at')+
  apply (fastforce simp: tcb_at_typ_at'  is_active_tcb_ptr_runnable')
  done

lemma performInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_invocation' i s \<and> ct_active' s \<and> sch_act_simple s \<rbrace>
   performInvocation block call i
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  by (wpsimp simp: performInvocation_def) auto

lemma getThreadState_restart [wp]:
  "\<lbrace> \<lambda>s. tcb_at' thread s \<rbrace>
   getThreadState thread
   \<lbrace> \<lambda>rv s. rv = Structures_H.thread_state.Restart \<longrightarrow> st_tcb_at' isRestart thread s \<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule gts_st_tcb')
  apply (clarsimp simp add: pred_tcb_at'_def obj_at'_def isRestart_def)
  done

lemma handleInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and>
         ct_active' s \<and> ksSchedulerAction s = ResumeCurrentThread \<rbrace>
   handleInvocation isCall isBlocking
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding handleInvocation_def
  apply (rule hoare_pre)
   apply (wp syscall_valid' setThreadState_isRestart_no_orphans | wpc | clarsimp)+
          apply (rule_tac Q="\<lambda>state s. no_orphans s \<and> invs' s \<and>
                             (state = Structures_H.thread_state.Restart \<longrightarrow>
                              st_tcb_at' isRestart thread s)"
                       in hoare_post_imp)
           apply (wp | clarsimp)+
        apply (wp setThreadState_current_no_orphans sts_invs_minor'
                  ct_in_state'_set setThreadState_st_tcb
                  hoare_vcg_all_lift
                | simp add: split_def split del: if_split)+
  apply (clarsimp simp: if_apply_def2)
  by (auto simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def invs'_def
                    cur_tcb'_def valid_state'_def valid_idle'_def)

lemma receiveSignal_no_orphans [wp]:
  "receiveSignal thread cap isBlocking \<lbrace>no_orphans\<rbrace>"
  unfolding receiveSignal_def
  apply (wp hoare_drop_imps setThreadState_not_active_no_orphans | wpc
         | clarsimp simp: is_active_thread_state_def isRunning_def isRestart_def
                          doNBRecvFailedTransfer_def)+
  done


lemma receiveIPC_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   receiveIPC thread cap is_blocking
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding receiveIPC_def
  apply (rule hoare_pre)
   apply (wp setThreadState_not_active_no_orphans hoare_drop_imps
             hoare_vcg_all_lift sts_st_tcb'
          | wpc
          | clarsimp simp: is_active_thread_state_def isRunning_def isRestart_def
                           doNBRecvFailedTransfer_def
          | strengthen sch_act_wf_weak)+
  done

crunch valid_objs' [wp]: getThreadCallerSlot "valid_objs'"

lemma deleteCallerCap_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   deleteCallerCap receiver
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding deleteCallerCap_def
  by (wpsimp wp: hoare_drop_imps) auto

lemma remove_neg_strg:
  "(A \<and> B) \<longrightarrow> ((x \<longrightarrow> A) \<and> (\<not> x \<longrightarrow> B))"
  by blast

lemma handleRecv_no_orphans [wp]:
notes if_cong[cong] shows
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   handleRecv isBlocking
   \<lbrace> \<lambda>rv . no_orphans \<rbrace>"
  unfolding handleRecv_def
  apply (clarsimp simp: whenE_def split del: if_split | wp hoare_drop_imps getNotification_wp | wpc )+ (*takes a while*)
     apply (rule_tac Q'="\<lambda>rv s. no_orphans s \<and> invs' s" in hoare_strengthen_postE_R)
      apply (wp, fastforce)
    apply (rule_tac Q="\<lambda>rv s. no_orphans s \<and> invs' s" in hoare_post_imp)
     apply (wp | clarsimp | fastforce)+
  done

crunches getThreadCallerSlot, handleHypervisorFault
  for invs' [wp]: "invs'"

lemma handleReply_no_orphans [wp]:
  "\<lbrace>no_orphans and invs'\<rbrace> handleReply \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding handleReply_def
  apply (wpsimp wp: hoare_drop_imps)
     apply (wp (once) hoare_vcg_all_lift)
      apply (rule_tac Q="\<lambda>rv s. no_orphans s \<and> invs' s \<and> tcb_at' thread s \<and>
                                valid_cap' rv s" in hoare_post_imp)
       apply (wpsimp wp: hoare_drop_imps
                     simp: valid_cap'_def invs'_def cur_tcb'_def valid_state'_def)+
  done

lemma handleYield_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   handleYield
   \<lbrace> \<lambda>rv . no_orphans \<rbrace>"
  unfolding handleYield_def
  by (wp tcbSchedAppend_almost_no_orphans) auto

lemma activatable_from_running':
  "ct_running' s \<Longrightarrow> ct_in_state' activatable' s"
  by (clarsimp simp: ct_in_state'_def elim!: pred_tcb'_weakenE)

(* FIXME move *)
lemma sts_tcb_at'_preserve:
  "\<lbrace> st_tcb_at' P t and K (P st) \<rbrace> setThreadState st t' \<lbrace>\<lambda>_. st_tcb_at' P t \<rbrace>"
  by (wpsimp wp: sts_st_tcb')

(* FIXME move *)
(* e.g. if you set a non-runnable thread to Inactive, all runnable threads are still runnable *)
lemma sts_tcb_at'_preserve':
  "\<lbrace> st_tcb_at' P t and st_tcb_at' (\<lambda>st. \<not> P st) t' and K (\<not> P st) \<rbrace>
  setThreadState st t'
  \<lbrace>\<lambda>_. st_tcb_at' P t \<rbrace>"
  by (wpsimp wp: sts_st_tcb' simp: st_tcb_at_neg')

lemma handleEvent_no_orphans [wp]:
  "\<lbrace> \<lambda>s. invs' s \<and>
         (e \<noteq> Interrupt \<longrightarrow> ct_running' s) \<and>
         ksSchedulerAction s = ResumeCurrentThread \<and> no_orphans s \<rbrace>
   handleEvent e
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (simp add: handleEvent_def handleSend_def handleCall_def
              cong: event.case_cong syscall.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpc | clarsimp simp: handleHypervisorFault_def
          | strengthen invs_valid_objs' invs_sch_act_wf')+
  apply (auto simp: activatable_from_running' active_from_running')
  done

theorem callKernel_no_orphans[wp]:
  "\<lbrace> \<lambda>s. invs' s \<and>
          (e \<noteq> Interrupt \<longrightarrow> ct_running' s) \<and>
          ksSchedulerAction s = ResumeCurrentThread \<and> no_orphans s \<rbrace>
   callKernel e
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding callKernel_def
  apply (wpsimp wp: hoare_drop_imp[where f=activateThread] schedule_invs'
         (* getActiveIRQ can't return a non-kernel IRQ *)
         | wp (once) hoare_post_imp[
                       where a="doMachineOp (getActiveIRQ True)"
                         and Q="\<lambda>rv s. no_orphans s \<and> invs' s \<and> rv \<notin> Some ` non_kernel_IRQs"])+
  done

end

end
