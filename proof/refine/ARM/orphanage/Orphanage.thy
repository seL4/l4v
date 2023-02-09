(*
 * Copyright 2014, General Dynamics C4 Systems
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
   "all_queued_tcb_ptrs s \<equiv>
       { tcb_ptr. \<exists> priority. tcb_ptr : set ((ksReadyQueues s) priority) }"

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
  apply (auto intro: pred_tcb_at')
  done

lemma no_orphans_lift:
   assumes typ_at'_is_lifted:
     "\<And> tcb_ptr. \<lbrace> \<lambda>s. \<not> typ_at' TCBT tcb_ptr s\<rbrace> f \<lbrace> \<lambda>_ s. \<not> typ_at' TCBT tcb_ptr s \<rbrace>"
   assumes ksCurThread_is_lifted:
     "\<And> tcb_ptr. \<lbrace> \<lambda>s. tcb_ptr = ksCurThread s \<rbrace> f \<lbrace> \<lambda>_ s. tcb_ptr = ksCurThread s \<rbrace>"
   assumes st_tcb_at'_is_lifted:
     "\<And>P p. \<lbrace> \<lambda>s. st_tcb_at' P p s\<rbrace> f \<lbrace> \<lambda>_ s. st_tcb_at' P p s \<rbrace>"
   assumes ksReadyQueues_is_lifted:
     "\<And>P. \<lbrace> \<lambda>s. P (ksReadyQueues s)\<rbrace> f \<lbrace> \<lambda>_ s. P (ksReadyQueues s) \<rbrace>"
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
    apply (rule ksReadyQueues_is_lifted)
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

lemma ksQ_all_queued_tcb_ptrs_lift:
  assumes "\<And>P p. \<lbrace>\<lambda>s. P (ksReadyQueues s p)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksReadyQueues s p)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace> f \<lbrace>\<lambda>_ s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace>"
  apply (clarsimp simp: all_queued_tcb_ptrs_def)
  apply (rule_tac P=P in P_bool_lift)
   apply (wp hoare_vcg_ex_lift assms)
  apply (clarsimp)
  apply (wp hoare_vcg_all_lift assms)
  done

definition
   almost_no_orphans :: "word32 \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "almost_no_orphans tcb_ptr s \<equiv>
      \<forall> ptr. ptr = tcb_ptr \<or>
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
  apply (auto intro: pred_tcb_at')
  done

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

crunch ksCurThread [wp]: setVMRoot "\<lambda> s. P (ksCurThread s)"
(wp: crunch_wps simp: crunch_simps)

crunch ksReadyQueues [wp]: asUser "\<lambda>s. P (ksReadyQueues s)"
(wp: crunch_wps simp: crunch_simps)

crunch no_orphans [wp]: getCurThread "no_orphans"

crunch no_orphans [wp]: threadGet "no_orphans"

crunch no_orphans [wp]: getNotification "no_orphans"

crunch no_orphans [wp]: addToBitmap "no_orphans"
crunch no_orphans [wp]: removeFromBitmap "no_orphans"

crunch almost_no_orphans [wp]: addToBitmap "almost_no_orphans x"
crunch almost_no_orphans [wp]: removeFromBitmap "almost_no_orphans x"

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
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift setCTE_typ_at' setCTE_pred_tcb_at')
  done

crunch no_orphans [wp]: activateIdleThread "no_orphans"

lemma asUser_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   asUser thread f
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma threadSet_no_orphans:
  "\<forall>tcb. \<not> is_active_thread_state (tcbState tcb) \<longrightarrow> \<not> is_active_thread_state (tcbState (F tcb)) \<Longrightarrow>
   \<lbrace> \<lambda>s. no_orphans s \<rbrace>
   threadSet F tptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_st_tcb_at2 | clarsimp)+
  done

lemma threadSet_almost_no_orphans:
  "\<forall>tcb. \<not> is_active_thread_state (tcbState tcb) \<longrightarrow> \<not> is_active_thread_state (tcbState (F tcb)) \<Longrightarrow>
   \<lbrace> \<lambda>s. almost_no_orphans ptr s \<rbrace>
   threadSet F tptr
   \<lbrace> \<lambda>rv s. almost_no_orphans ptr s \<rbrace>"
  unfolding almost_no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_st_tcb_at2 | clarsimp)+
  done

lemma setQueue_no_orphans_enq:
  "\<lbrace> \<lambda>s. no_orphans s \<and> set (ksReadyQueues s (d, prio)) \<subseteq> set qs \<rbrace>
   setQueue d prio qs
   \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  unfolding setQueue_def
  apply wp
  apply (clarsimp simp: no_orphans_def all_queued_tcb_ptrs_def
                  split: if_split_asm)
  apply fastforce
  done

lemma setQueue_almost_no_orphans_enq:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and> set (ksReadyQueues s (d, prio)) \<subseteq> set qs \<and> tcb_ptr \<in> set qs \<rbrace>
   setQueue d prio qs
   \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  unfolding setQueue_def
  apply wp
  apply (clarsimp simp: no_orphans_def almost_no_orphans_def all_queued_tcb_ptrs_def
                  split: if_split_asm)
  apply fastforce
  done

lemma setQueue_almost_no_orphans_enq_lift:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and> set (ksReadyQueues s (d, prio)) \<subseteq> set qs \<rbrace>
   setQueue d prio qs
   \<lbrace> \<lambda>_ s. almost_no_orphans tcb_ptr s \<rbrace>"
  unfolding setQueue_def
  apply wp
  apply (clarsimp simp: almost_no_orphans_def all_queued_tcb_ptrs_def
                  split: if_split_asm)
  apply fastforce
  done

lemma tcbSchedEnqueue_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   tcbSchedEnqueue tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding tcbSchedEnqueue_def
  apply (wp setQueue_no_orphans_enq threadSet_no_orphans | clarsimp simp: unless_def)+
   apply (wp getObject_tcb_wp | clarsimp simp: threadGet_def)+
  apply (drule obj_at_ko_at')
  apply auto
  done

lemma tcbSchedAppend_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   tcbSchedAppend tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wp setQueue_no_orphans_enq threadSet_no_orphans | clarsimp simp: unless_def)+
   apply (wp getObject_tcb_wp | clarsimp simp: threadGet_def)+
  apply (drule obj_at_ko_at')
  apply auto
  done

lemma ko_at_obj_at':
  "ko_at' ko p s \<and> P ko \<Longrightarrow> obj_at' P p s"
  unfolding  obj_at'_def
  apply clarsimp
  done

lemma queued_in_queue:
  "\<lbrakk>valid_queues' s; ko_at' tcb tcb_ptr s; tcbQueued tcb\<rbrakk> \<Longrightarrow>
   \<exists> p. tcb_ptr \<in> set (ksReadyQueues s p)"
  unfolding valid_queues'_def
   apply (drule_tac x="tcbDomain tcb" in spec)
   apply (drule_tac x="tcbPriority tcb" in spec)
   apply (drule_tac x="tcb_ptr" in spec)
   apply (drule mp)
    apply (rule ko_at_obj_at')
    apply (auto simp: inQ_def)
  done

lemma tcbSchedEnqueue_almost_no_orphans:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and> valid_queues' s \<rbrace>
   tcbSchedEnqueue tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding tcbSchedEnqueue_def
  apply simp
  apply (wp setQueue_almost_no_orphans_enq[where tcb_ptr=tcb_ptr] threadSet_no_orphans
            | clarsimp)+
   apply (wp getObject_tcb_wp | clarsimp simp: threadGet_def)+
  apply normalise_obj_at'
  apply (rule_tac x=ko in exI)
  apply (clarsimp simp: subset_insertI)
  apply (unfold no_orphans_def almost_no_orphans_def)
  apply clarsimp
  apply (drule(2) queued_in_queue)
  apply (fastforce simp: all_queued_tcb_ptrs_def)
  done

lemma tcbSchedEnqueue_almost_no_orphans_lift:
  "\<lbrace> \<lambda>s. almost_no_orphans ptr s \<rbrace>
   tcbSchedEnqueue tcb_ptr
   \<lbrace> \<lambda>rv s. almost_no_orphans ptr s \<rbrace>"
  unfolding tcbSchedEnqueue_def
  apply (wp setQueue_almost_no_orphans_enq_lift threadSet_almost_no_orphans | clarsimp simp: unless_def)+
   apply (wp getObject_tcb_wp | clarsimp simp: threadGet_def)+
  apply (drule obj_at_ko_at')
  apply auto
  done

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

lemma tcbSchedEnqueue_inQueue [wp]:
  "\<lbrace> \<lambda>s. valid_queues' s \<rbrace>
   tcbSchedEnqueue tcb_ptr
   \<lbrace> \<lambda>rv s. tcb_ptr \<in> all_queued_tcb_ptrs s \<rbrace>"
  unfolding tcbSchedEnqueue_def all_queued_tcb_ptrs_def
  apply (wp | clarsimp simp: unless_def)+
   apply (rule_tac Q="\<lambda>rv. \<top>" in hoare_post_imp)
    apply fastforce
   apply (wp getObject_tcb_wp | clarsimp simp: threadGet_def)+
  apply (fastforce simp: obj_at'_def valid_queues'_def inQ_def)
  done

lemma tcbSchedAppend_inQueue [wp]:
  "\<lbrace> \<lambda>s. valid_queues' s \<rbrace>
   tcbSchedAppend tcb_ptr
   \<lbrace> \<lambda>rv s. tcb_ptr \<in> all_queued_tcb_ptrs s \<rbrace>"
  unfolding tcbSchedAppend_def all_queued_tcb_ptrs_def
  apply (wp | clarsimp simp: unless_def)+
   apply (rule_tac Q="\<lambda>rv. \<top>" in hoare_post_imp)
    apply fastforce
   apply (wp getObject_tcb_wp | clarsimp simp: threadGet_def)+
  apply (fastforce simp: obj_at'_def valid_queues'_def inQ_def)
  done

lemma rescheduleRequired_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<rbrace>
   rescheduleRequired
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding rescheduleRequired_def
  apply (wp tcbSchedEnqueue_no_orphans hoare_vcg_all_lift ssa_no_orphans | wpc | clarsimp)+
   apply (wps tcbSchedEnqueue_nosch, wp static_imp_wp)
   apply (rename_tac word t p)
   apply (rule_tac P="word = t" in hoare_gen_asm)
   apply (wp hoare_disjI1 | clarsimp)+
  done

lemma rescheduleRequired_almost_no_orphans [wp]:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and> valid_queues' s \<rbrace>
   rescheduleRequired
   \<lbrace> \<lambda>rv s. almost_no_orphans tcb_ptr s \<rbrace>"
  unfolding rescheduleRequired_def
  apply (wp tcbSchedEnqueue_almost_no_orphans_lift hoare_vcg_all_lift | wpc | clarsimp)+
   apply (wps tcbSchedEnqueue_nosch, wp static_imp_wp)
   apply (rename_tac word t p)
   apply (rule_tac P="word = t" in hoare_gen_asm)
   apply (wp hoare_disjI1 | clarsimp)+
  done

lemma setThreadState_current_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and> ksCurThread s = tcb_ptr \<and> valid_queues' s \<rbrace>
   setThreadState state tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setThreadState_def
  apply (wp | clarsimp)+
  apply (rule_tac Q="\<lambda>rv s. valid_queues' s \<and> no_orphans s" in hoare_post_imp)
   apply clarsimp
  apply (wp threadSet_valid_queues')
   apply (unfold no_orphans_disj all_queued_tcb_ptrs_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state)
   apply (auto simp: inQ_def)
  done

lemma setThreadState_isRestart_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and> st_tcb_at' isRestart tcb_ptr s \<and> valid_queues' s\<rbrace>
   setThreadState state tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setThreadState_def
  apply (wp | clarsimp)+
  apply (rule_tac Q="\<lambda>rv s. valid_queues' s \<and> no_orphans s" in hoare_post_imp)
   apply clarsimp
  apply (wp threadSet_valid_queues')
   apply (unfold no_orphans_disj all_queued_tcb_ptrs_def is_active_thread_state_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state)
   apply (auto simp: st_tcb_at_double_neg' st_tcb_at_neg' inQ_def)
  done

lemma setThreadState_almost_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s\<rbrace>
   setThreadState state tcb_ptr
   \<lbrace> \<lambda>rv s. almost_no_orphans tcb_ptr s \<rbrace>"
  unfolding setThreadState_def
  apply (wp | clarsimp)+
  apply (rule_tac Q="\<lambda>rv s. valid_queues' s \<and> almost_no_orphans tcb_ptr s" in hoare_post_imp)
   apply clarsimp
  apply (wp threadSet_valid_queues')
   apply (unfold no_orphans_disj almost_no_orphans_disj all_queued_tcb_ptrs_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state)
   apply (auto simp: inQ_def)
  done

lemma setThreadState_not_active_no_orphans:
  "\<not> is_active_thread_state state \<Longrightarrow>
   \<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<rbrace>
   setThreadState state tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setThreadState_def
  apply (wp | clarsimp)+
  apply (rule_tac Q="\<lambda>rv s. valid_queues' s \<and> no_orphans s" in hoare_post_imp)
   apply clarsimp
  apply (wp threadSet_valid_queues')
   apply (unfold no_orphans_disj all_queued_tcb_ptrs_def is_active_thread_state_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state)
   apply (auto simp: isRunning_def isRestart_def inQ_def)
  done

lemma setThreadState_not_active_almost_no_orphans:
  "\<not> is_active_thread_state state \<Longrightarrow>
   \<lbrace> \<lambda>s. almost_no_orphans thread s \<and> valid_queues' s \<rbrace>
   setThreadState state tcb_ptr
   \<lbrace> \<lambda>rv s. almost_no_orphans thread s \<rbrace>"
  unfolding setThreadState_def
  apply (wp | clarsimp)+
  apply (rule_tac Q="\<lambda>rv s. valid_queues' s \<and> almost_no_orphans thread s" in hoare_post_imp)
   apply clarsimp
  apply (wp threadSet_valid_queues')
   apply (unfold almost_no_orphans_disj all_queued_tcb_ptrs_def is_active_thread_state_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift threadSet_pred_tcb_at_state)
   apply (auto simp: isRunning_def isRestart_def inQ_def)
  done

lemma activateThread_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> ct_in_state' activatable' s \<and> invs' s \<rbrace>
   activateThread
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding activateThread_def
  apply (wp gts_wp' setThreadState_isRestart_no_orphans | wpc | clarsimp)+
  apply (auto simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def isRestart_def)
  done

lemma setQueue_no_orphans_deq:
  "\<lbrace> \<lambda>s. \<exists> tcb_ptr. no_orphans s \<and> \<not> is_active_tcb_ptr tcb_ptr s \<and>
        queue = [x\<leftarrow>((ksReadyQueues s) (d, priority)). x \<noteq> tcb_ptr] \<rbrace>
   setQueue d priority queue
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setQueue_def
  apply (wp | clarsimp)+
  apply (fastforce simp: no_orphans_def all_queued_tcb_ptrs_def
                        all_active_tcb_ptrs_def is_active_tcb_ptr_def)
  done

lemma setQueue_almost_no_orphans_deq [wp]:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and>
        queue = [x\<leftarrow>((ksReadyQueues s) (d, priority)). x \<noteq> tcb_ptr] \<rbrace>
   setQueue d priority queue
   \<lbrace> \<lambda>rv s. almost_no_orphans tcb_ptr s \<rbrace>"
  unfolding setQueue_def
  apply (wp | clarsimp)+
  apply (fastforce simp: almost_no_orphans_def all_queued_tcb_ptrs_def
                        all_active_tcb_ptrs_def is_active_tcb_ptr_def)
  done

lemma tcbSchedDequeue_almost_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   tcbSchedDequeue thread
   \<lbrace> \<lambda>rv s. almost_no_orphans thread s \<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wp threadSet_almost_no_orphans | simp cong: if_cong)+
  apply (simp add:no_orphans_strg_almost cong: if_cong)
  done

lemma tcbSchedDequeue_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> \<not> is_active_tcb_ptr tcb_ptr s \<rbrace>
   tcbSchedDequeue tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wp setQueue_no_orphans_deq threadSet_no_orphans | clarsimp)+
   apply (wp getObject_tcb_wp | clarsimp simp: threadGet_def)+
  apply (drule obj_at_ko_at')
  apply auto
  done

lemma switchToIdleThread_no_orphans' [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and>
          (is_active_tcb_ptr (ksCurThread s) s
             \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s) \<rbrace>
   switchToIdleThread
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding switchToIdleThread_def setCurThread_def ARM_H.switchToIdleThread_def
  apply (simp add: no_orphans_disj all_queued_tcb_ptrs_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_disj_lift
       | clarsimp)+
  apply (auto simp: no_orphans_disj all_queued_tcb_ptrs_def is_active_tcb_ptr_def
                    st_tcb_at_neg' tcb_at_typ_at')
  done

crunch no_orphans [wp]: "Arch.switchToThread" "no_orphans"
  (wp: no_orphans_lift ignore: ARM.clearExMonitor)

crunch ksCurThread [wp]: "Arch.switchToThread" "\<lambda> s. P (ksCurThread s)"
  (ignore: ARM.clearExMonitor)

crunch ksIdleThread [wp]: "Arch.switchToThread" "\<lambda> s. P (ksIdleThread s)"
  (ignore: ARM.clearExMonitor)

lemma ArchThreadDecls_H_switchToThread_all_queued_tcb_ptrs [wp]:
  "\<lbrace> \<lambda>s. P (all_queued_tcb_ptrs s) \<rbrace>
   Arch.switchToThread tcb_ptr
   \<lbrace> \<lambda>rv s. P (all_queued_tcb_ptrs s) \<rbrace>"
  unfolding ARM_H.switchToThread_def all_queued_tcb_ptrs_def
  apply (wp | clarsimp)+
  done

crunch ksSchedulerAction [wp]: "Arch.switchToThread" "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: ARM.clearExMonitor)


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

lemma tcbSchedDequeue_all_queued_tcb_ptrs:
  "\<lbrace>\<lambda>s. x \<in> all_queued_tcb_ptrs s \<and> x \<noteq> t \<rbrace>
   tcbSchedDequeue t \<lbrace>\<lambda>_ s. x \<in> all_queued_tcb_ptrs s\<rbrace>"
  apply (rule_tac Q="(\<lambda>s. x \<in> all_queued_tcb_ptrs s) and K (x \<noteq> t)"
           in hoare_pre_imp, clarsimp)
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: tcbSchedDequeue_def all_queued_tcb_ptrs_def)
  apply (rule hoare_pre)
   apply (wp, clarsimp)
       apply (wp hoare_vcg_ex_lift)+
     apply (rename_tac d p)
     apply (rule_tac Q="\<lambda>_ s. x \<in> set (ksReadyQueues s (d, p))"
                     in hoare_post_imp, clarsimp)
     apply (wp hoare_vcg_all_lift | simp)+
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

lemmas ArchThreadDecls_H_switchToThread_all_queued_tcb_ptrs_lift[wp] =
  ksQ_all_queued_tcb_ptrs_lift [OF arch_switch_thread_ksQ]

lemma ThreadDecls_H_switchToThread_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and>
         st_tcb_at' runnable' tcb_ptr s \<and>
         (ksCurThread s \<in> all_active_tcb_ptrs s
            \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s)\<rbrace>
   ThreadDecls_H.switchToThread tcb_ptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding Thread_H.switchToThread_def
  apply (wp setCurThread_almost_no_orphans
            tcbSchedDequeue_almost_no_orphans)
    apply (wps tcbSchedDequeue_ct')
    apply (wp tcbSchedDequeue_all_queued_tcb_ptrs hoare_convert_imp)+
    apply (wps)
    apply (wp)+
   apply (wps)
   apply (wp)
  apply (clarsimp)
  done

lemma findM_failure':
  "\<lbrakk> \<And>x S. \<lbrace> \<lambda>s. P S s \<rbrace> f x \<lbrace> \<lambda>rv s. \<not> rv \<longrightarrow> P (insert x S) s \<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace> \<lambda>s. P S s \<rbrace> findM f xs \<lbrace> \<lambda>rv s. rv = None \<longrightarrow> P (S \<union> set xs) s \<rbrace>"
  apply (induct xs arbitrary: S)
   apply (clarsimp, wp, clarsimp)
  apply clarsimp
  apply (rule hoare_seq_ext[rotated], assumption)
  apply (case_tac r)
   apply (clarsimp, wp, clarsimp)
  apply clarsimp
  apply (rule hoare_strengthen_post, assumption)
  apply clarsimp
  done

lemmas findM_failure = findM_failure'[where S="{}", simplified]

lemma tcbSchedEnqueue_inQueue_eq:
  "\<lbrace> valid_queues' and K (tcb_ptr = tcb_ptr') \<rbrace>
   tcbSchedEnqueue tcb_ptr
   \<lbrace> \<lambda>rv s. tcb_ptr' \<in> all_queued_tcb_ptrs s \<rbrace>"
  apply (rule hoare_gen_asm, simp)
  apply wp
  done

lemma tcbSchedAppend_inQueue_eq:
  "\<lbrace> valid_queues' and K (tcb_ptr = tcb_ptr') \<rbrace>
   tcbSchedAppend tcb_ptr
   \<lbrace> \<lambda>rv s. tcb_ptr' \<in> all_queued_tcb_ptrs s \<rbrace>"
  apply (rule hoare_gen_asm, simp)
  apply wp
  done

lemma findM_on_success:
  "\<lbrakk> \<And>x. \<lbrace> P x \<rbrace> f x \<lbrace> \<lambda>rv s. rv \<rbrace>; \<And>x y. \<lbrace> P x \<rbrace> f y \<lbrace> \<lambda>rv. P x \<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>x \<in> set xs. P x s \<rbrace> findM f xs \<lbrace> \<lambda>rv s. \<exists> y. rv = Some y \<rbrace>"
  apply (induct xs; clarsimp)
  apply wp+
  apply (clarsimp simp: imp_conv_disj Bex_def)
  apply (wp hoare_vcg_disj_lift hoare_vcg_ex_lift | clarsimp | assumption)+
  done

crunch st_tcb' [wp]: switchToThread "\<lambda>s. P' (st_tcb_at' P t s)"
  (ignore: ARM.clearExMonitor)

lemma setQueue_deq_not_empty:
  "\<lbrace> \<lambda>s. (\<exists>tcb. tcb \<in> set (ksReadyQueues s p) \<and> st_tcb_at' P tcb s) \<and>
         (\<exists>tcb_ptr. \<not> st_tcb_at' P tcb_ptr s \<and>
                    queue = [x\<leftarrow>((ksReadyQueues s) (d, priority)). x \<noteq> tcb_ptr]) \<rbrace>
   setQueue d priority queue
   \<lbrace> \<lambda>rv s. \<exists>tcb. tcb \<in> set (ksReadyQueues s p) \<and> st_tcb_at' P tcb s \<rbrace>"
  unfolding setQueue_def
  apply wp
  apply auto
  done

lemma tcbSchedDequeue_not_empty:
  "\<lbrace> \<lambda>s. (\<exists>tcb. tcb \<in> set (ksReadyQueues s p) \<and> st_tcb_at' P tcb s) \<and> \<not> st_tcb_at' P thread s \<rbrace>
   tcbSchedDequeue thread
   \<lbrace> \<lambda>rv s. \<exists>tcb. tcb \<in> set (ksReadyQueues s p) \<and> st_tcb_at' P tcb s \<rbrace>"
  unfolding tcbSchedDequeue_def
  apply wp
         apply (wp hoare_vcg_ex_lift threadSet_pred_tcb_no_state)
         apply clarsimp
        apply (wp setQueue_deq_not_empty)
       apply clarsimp
       apply (rule hoare_pre_post, assumption)
       apply (clarsimp simp: bitmap_fun_defs)
       apply wp
       apply clarsimp
      apply clarsimp
      apply (wp setQueue_deq_not_empty)+
   apply (rule_tac Q="\<lambda>rv s. \<not> st_tcb_at' P thread s" in hoare_post_imp)
    apply fastforce
   apply (wp weak_if_wp | clarsimp)+
  done

lemmas switchToThread_all_active_tcb_ptrs[wp] =
  st_tcb_at'_all_active_tcb_ptrs_lift [OF switchToThread_st_tcb']

(* ksSchedulerAction s = ChooseNewThread *)
lemma chooseThread_no_orphans [wp]:
  notes hoare_TrueI[simp]
  shows
  "\<lbrace>\<lambda>s. no_orphans s \<and> all_invs_but_ct_idle_or_in_cur_domain' s \<and>
          (is_active_tcb_ptr (ksCurThread s) s
             \<longrightarrow> ksCurThread s \<in> all_queued_tcb_ptrs s)\<rbrace>
   chooseThread
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  unfolding chooseThread_def Let_def
  supply if_split[split del]
  apply (simp only: return_bind, simp)
  apply (rule hoare_seq_ext[where B="\<lambda>rv s. ?PRE s \<and> rv = ksCurDomain s"])
   apply (rule_tac B="\<lambda>rv s. ?PRE s \<and> curdom = ksCurDomain s \<and>
    rv = ksReadyQueuesL1Bitmap s curdom" in hoare_seq_ext)
    apply (rename_tac l1)
    apply (case_tac "l1 = 0")
     (* switch to idle thread *)
     apply (simp, wp (once), simp)
    (* we have a thread to switch to *)
    apply (clarsimp simp: bitmap_fun_defs)
    apply (wp assert_inv ThreadDecls_H_switchToThread_no_orphans)
    apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def
                          valid_queues_def st_tcb_at'_def)
    apply (fastforce dest!: lookupBitmapPriority_obj_at' elim: obj_at'_weaken
                     simp: all_active_tcb_ptrs_def)
   apply (wpsimp simp: bitmap_fun_defs)
  apply (wp curDomain_or_return_0[simplified])
    apply (wpsimp simp: curDomain_def simp: invs_no_cicd_ksCurDomain_maxDomain')+
  done

lemma tcbSchedAppend_in_ksQ:
  "\<lbrace>valid_queues' and tcb_at' t\<rbrace> tcbSchedAppend t
   \<lbrace>\<lambda>r s. \<exists>domain priority. t \<in> set (ksReadyQueues s (domain, priority))\<rbrace>"
  apply (rule_tac Q="\<lambda>s. \<exists>d p. valid_queues' s \<and>
                             obj_at' (\<lambda>tcb. tcbPriority tcb = p) t s \<and>
                             obj_at' (\<lambda>tcb. tcbDomain tcb = d) t s"
           in hoare_pre_imp)
   apply (clarsimp simp: tcb_at'_has_tcbPriority tcb_at'_has_tcbDomain)
  apply (rule hoare_vcg_ex_lift)+
  apply (simp add: tcbSchedAppend_def unless_def)
  apply wpsimp
     apply (rule_tac Q="\<lambda>rv s. tdom = d \<and> rv = p \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = p) t s
                            \<and> obj_at' (\<lambda>tcb. tcbDomain tcb = d) t s"
             in hoare_post_imp, clarsimp)
     apply (wp, (wp threadGet_const)+)
   apply (rule_tac Q="\<lambda>rv s.
             obj_at' (\<lambda>tcb. tcbPriority tcb = p) t s \<and>
             obj_at' (\<lambda>tcb. tcbDomain tcb = d) t s \<and>
             obj_at' (\<lambda>tcb. tcbQueued tcb = rv) t s \<and>
             (rv \<longrightarrow> t \<in> set (ksReadyQueues s (d, p)))" in hoare_post_imp)
   apply (clarsimp simp: o_def elim!: obj_at'_weakenE)
   apply (wp threadGet_obj_at' hoare_vcg_imp_lift threadGet_const)
  apply clarsimp
  apply normalise_obj_at'
  apply (drule(1) valid_queues'_ko_atD, simp+)
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

crunch ksQ [wp]: nextDomain "\<lambda>s. P (ksReadyQueues s p)"
(simp: Let_def)

crunch st_tcb_at' [wp]: nextDomain "\<lambda>s. P (st_tcb_at' P' p s)"
(simp: Let_def)

crunch ct' [wp]: nextDomain "\<lambda>s. P (ksCurThread s)"
(simp: Let_def)

crunch sch_act_not [wp]: nextDomain "sch_act_not t"
(simp: Let_def)

lemma tcbSchedEnqueue_in_ksQ':
  "\<lbrace>valid_queues' and tcb_at' t and K (t = t')\<rbrace>
     tcbSchedEnqueue t'
   \<lbrace>\<lambda>r s. \<exists>domain priority. t \<in> set (ksReadyQueues s (domain, priority))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp tcbSchedEnqueue_in_ksQ | clarsimp)+
  done

lemma all_invs_but_ct_idle_or_in_cur_domain'_strg:
  "invs' s \<longrightarrow> all_invs_but_ct_idle_or_in_cur_domain' s"
  by (clarsimp simp: invs'_to_invs_no_cicd'_def)

lemma setSchedulerAction_cnt_sch_act_not[wp]:
  "\<lbrace> \<top> \<rbrace> setSchedulerAction ChooseNewThread \<lbrace>\<lambda>rv s. sch_act_not x s\<rbrace>"
  by (rule hoare_pre, rule hoare_strengthen_post[OF setSchedulerAction_direct]) auto

lemma obj_at'_static_fix:
  "\<lbrakk> obj_at' (\<lambda>(ko::'a::pspace_storable). True) p s ; P \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>(ko::'a::pspace_storable). P) p s"
  by (erule obj_at'_weakenE, simp)

lemma tcbSchedEnqueue_in_ksQ_aqtp[wp]:
  "\<lbrace>valid_queues' and tcb_at' t\<rbrace> tcbSchedEnqueue t
   \<lbrace>\<lambda>r s. t \<in> all_queued_tcb_ptrs s\<rbrace>"
  apply (clarsimp simp: all_queued_tcb_ptrs_def)
  apply (rule tcbSchedEnqueue_in_ksQ)
  done

crunch ksReadyQueues[wp]: threadGet "\<lambda>s. P (ksReadyQueues s)"

lemma tcbSchedEnqueue_in_ksQ_already_queued:
  "\<lbrace>\<lambda>s. valid_queues' s \<and> tcb_at' t s \<and>
    (\<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))) \<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>r s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))\<rbrace>"
  apply (case_tac "t'=t", wpsimp wp: tcbSchedEnqueue_in_ksQ)
  apply (wpsimp simp:  tcbSchedEnqueue_def unless_def)
     apply (rule_tac Q="\<lambda>_ s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))"
              in hoare_post_imp)
      apply metis
     apply wpsimp+
  done

lemma tcbSchedAppend_in_ksQ_already_queued:
  "\<lbrace>\<lambda>s. valid_queues' s \<and> tcb_at' t s \<and>
    (\<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))) \<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>r s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))\<rbrace>"
  apply (case_tac "t'=t", wpsimp wp: tcbSchedAppend_in_ksQ)
  apply (wpsimp simp:  tcbSchedAppend_def unless_def)
     apply (rule_tac Q="\<lambda>_ s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))"
              in hoare_post_imp)
      apply metis
     apply wpsimp+
  done

lemma tcbSchedEnqueue_in_ksQ'':
  "\<lbrace>\<lambda>s. valid_queues' s \<and> tcb_at' t s \<and>
    (t' \<noteq> t \<longrightarrow> (\<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority)))) \<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>r s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))\<rbrace>"
  apply (case_tac "t'=t", wpsimp wp: tcbSchedEnqueue_in_ksQ)
  apply clarsimp
  apply (wpsimp simp:  tcbSchedEnqueue_def unless_def)
     apply (rule_tac Q="\<lambda>_ s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))"
              in hoare_post_imp)
      apply metis
     apply wpsimp+
  done

lemma tcbSchedAppend_in_ksQ'':
  "\<lbrace>\<lambda>s. valid_queues' s \<and> tcb_at' t s \<and>
    (t' \<noteq> t \<longrightarrow> (\<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority)))) \<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>r s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))\<rbrace>"
  apply (case_tac "t'=t", wpsimp wp: tcbSchedAppend_in_ksQ)
  apply clarsimp
  apply (wpsimp simp:  tcbSchedAppend_def unless_def)
     apply (rule_tac Q="\<lambda>_ s. \<exists>domain priority. t' \<in> set (ksReadyQueues s (domain, priority))"
              in hoare_post_imp)
      apply metis
     apply wpsimp+
  done

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

lemma tcbSchedEnqueue_in_ksQ_already_queued_aqtp:
  "\<lbrace>\<lambda>s. valid_queues' s \<and> tcb_at' t s \<and>
    t' \<in> all_queued_tcb_ptrs s \<rbrace> tcbSchedEnqueue t
   \<lbrace>\<lambda>r s. t' \<in> all_queued_tcb_ptrs s \<rbrace>"
  by (clarsimp simp: all_queued_tcb_ptrs_def tcbSchedEnqueue_in_ksQ_already_queued)

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

lemma scheduleChooseNewThread_no_orphans:
  "\<lbrace> invs' and no_orphans
     and (\<lambda>s. ksSchedulerAction s = ChooseNewThread
              \<and> (st_tcb_at' runnable' (ksCurThread s) s
                 \<longrightarrow> (\<exists>d p. ksCurThread s \<in> set (ksReadyQueues s (d, p))))) \<rbrace>
   scheduleChooseNewThread
   \<lbrace>\<lambda>_. no_orphans \<rbrace>"
  unfolding scheduleChooseNewThread_def
     apply (wp add: ssa_no_orphans hoare_vcg_all_lift)
         apply (wp hoare_disjI1 chooseThread_nosch)+
    apply (wp nextDomain_invs_no_cicd' hoare_vcg_imp_lift
               hoare_lift_Pf2 [OF ksQ_all_queued_tcb_ptrs_lift[OF nextDomain_ksQ]
                                  nextDomain_ct']
               hoare_lift_Pf2 [OF st_tcb_at'_is_active_tcb_ptr_lift[OF nextDomain_st_tcb_at']
                                  nextDomain_ct']
               hoare_vcg_all_lift getDomainTime_wp)[2]
   apply (wpsimp simp: if_apply_def2 invs'_invs_no_cicd all_queued_tcb_ptrs_def
                       is_active_tcb_ptr_runnable')+
  done

lemma schedule_no_orphans[wp]:
  notes ssa_wp[wp del]
  shows
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   schedule
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
proof -

  have do_switch_to:
    "\<And>candidate.
     \<lbrace>\<lambda>s. no_orphans s \<and> ksSchedulerAction s = SwitchToThread candidate
          \<and> st_tcb_at' runnable' candidate s
          \<and> (st_tcb_at' runnable' (ksCurThread s) s
             \<longrightarrow> (\<exists>d p. ksCurThread s \<in> set (ksReadyQueues s (d, p)))) \<rbrace>
      do ThreadDecls_H.switchToThread candidate;
         setSchedulerAction ResumeCurrentThread
      od
    \<lbrace>\<lambda>rv. no_orphans\<rbrace>"
    apply (wpsimp wp: scheduleChooseNewThread_no_orphans ssa_no_orphans
                      hoare_vcg_all_lift ThreadDecls_H_switchToThread_no_orphans)+
     apply (rule_tac Q="\<lambda>_ s. (t = candidate \<longrightarrow> ksCurThread s = candidate) \<and>
                               (t \<noteq> candidate \<longrightarrow> sch_act_not t s)"
              in hoare_post_imp)
      apply (wpsimp wp: stt_nosch static_imp_wp)+
    apply (fastforce dest!: in_all_active_tcb_ptrsD simp: all_queued_tcb_ptrs_def comp_def)
    done

  have abort_switch_to_enq:
    "\<And>candidate.
     \<lbrace>\<lambda>s. no_orphans s \<and> invs' s \<and> valid_queues' s
          \<and> ksSchedulerAction s = SwitchToThread candidate
          \<and> (st_tcb_at' runnable' (ksCurThread s) s
               \<longrightarrow> (\<exists>d p. ksCurThread s \<in> set (ksReadyQueues s (d, p)))) \<rbrace>
       do tcbSchedEnqueue candidate;
          setSchedulerAction ChooseNewThread;
          scheduleChooseNewThread
       od
     \<lbrace>\<lambda>rv. no_orphans\<rbrace>"
     apply (rule hoare_pre)
     apply (wp scheduleChooseNewThread_no_orphans ssa_no_orphans setSchedulerAction_direct)
      apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift
                    simp: is_active_tcb_ptr_runnable' all_queued_tcb_ptrs_def
             | rule hoare_lift_Pf2[where f=ksCurThread, OF setSchedulerAction_ksQ])+
     apply (wp tcbSchedEnqueue_in_ksQ' tcbSchedEnqueue_no_orphans hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift)
      apply (wp hoare_lift_Pf2[where f=ksCurThread, OF tcbSchedEnqueue_pred_tcb_at']
                hoare_lift_Pf2[where f=ksCurThread, OF tcbSchedEnqueue_in_ksQ_already_queued]
                tcbSchedEnqueue_no_orphans
             | strengthen not_pred_tcb_at'_strengthen
             | wp (once) hoare_vcg_imp_lift')+
    apply (clarsimp)
    apply (frule invs_sch_act_wf', clarsimp simp: pred_tcb_at')
    apply (simp add: st_tcb_at_neg' tcb_at_invs')
    done

  have abort_switch_to_app:
    "\<And>candidate.
     \<lbrace>\<lambda>s. no_orphans s \<and> invs' s \<and> valid_queues' s
          \<and> ksSchedulerAction s = SwitchToThread candidate
          \<and> (st_tcb_at' runnable' (ksCurThread s) s
             \<longrightarrow> (\<exists>d p. ksCurThread s \<in> set (ksReadyQueues s (d, p))) ) \<rbrace>
       do tcbSchedAppend candidate;
          setSchedulerAction ChooseNewThread;
          scheduleChooseNewThread
       od
     \<lbrace>\<lambda>rv. no_orphans\<rbrace>"
     apply (rule hoare_pre)
     apply (wp scheduleChooseNewThread_no_orphans ssa_no_orphans setSchedulerAction_direct)
      apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift
                    simp: is_active_tcb_ptr_runnable' all_queued_tcb_ptrs_def
             | rule hoare_lift_Pf2[where f=ksCurThread, OF setSchedulerAction_ksQ])+
     apply (wp tcbSchedAppend_in_ksQ'' tcbSchedAppend_no_orphans hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift)
      apply (wp hoare_lift_Pf2[where f=ksCurThread, OF tcbSchedAppend_pred_tcb_at']
                hoare_lift_Pf2[where f=ksCurThread, OF tcbSchedAppend_in_ksQ_already_queued]
                tcbSchedAppend_no_orphans
             | strengthen not_pred_tcb_at'_strengthen
             | wp (once) hoare_vcg_imp_lift')+
    apply (clarsimp)
    apply (frule invs_sch_act_wf', clarsimp simp: pred_tcb_at')
    apply (simp add: st_tcb_at_neg' tcb_at_invs')
    done

  show ?thesis
  unfolding schedule_def
  supply if_weak_cong[cong]
  apply (wp, wpc)
       \<comment> \<open>action = ResumeCurrentThread\<close>
      apply (wp)[1]
     \<comment> \<open>action = ChooseNewThread\<close>
     apply (clarsimp simp: when_def scheduleChooseNewThread_def)
     apply (wp ssa_no_orphans hoare_vcg_all_lift)
         apply (wp hoare_disjI1 chooseThread_nosch)
         apply (wp nextDomain_invs_no_cicd' hoare_vcg_imp_lift
                   hoare_lift_Pf2 [OF ksQ_all_queued_tcb_ptrs_lift
                                      [OF nextDomain_ksQ]
                                      nextDomain_ct']
                   hoare_lift_Pf2 [OF st_tcb_at'_is_active_tcb_ptr_lift
                                    [OF nextDomain_st_tcb_at']
                                    nextDomain_ct']
                   hoare_vcg_all_lift getDomainTime_wp)[2]
       apply ((wp tcbSchedEnqueue_no_orphans tcbSchedEnqueue_in_ksQ'
                  hoare_drop_imp
             | clarsimp simp: all_queued_tcb_ptrs_def
             | strengthen all_invs_but_ct_idle_or_in_cur_domain'_strg
             | wps tcbSchedEnqueue_ct')+)[1]
       apply ((wp tcbSchedEnqueue_no_orphans tcbSchedEnqueue_in_ksQ'
                  hoare_drop_imp
             | clarsimp simp: all_queued_tcb_ptrs_def
             | strengthen all_invs_but_ct_idle_or_in_cur_domain'_strg
             | wps tcbSchedEnqueue_ct')+)[1]
     apply wp[1]
    \<comment> \<open>action = SwitchToThread candidate\<close>
     apply (clarsimp)
    apply (rename_tac candidate)
   apply (wpsimp wp: do_switch_to abort_switch_to_enq abort_switch_to_app)
          (* isHighestPrio *)
          apply (wp hoare_drop_imps)
         apply (wp add: tcbSchedEnqueue_no_orphans)+
    apply (clarsimp simp: conj_comms cong: conj_cong imp_cong split del: if_split)
    apply (wp hoare_lift_Pf2[where f=ksCurThread, OF tcbSchedEnqueue_pred_tcb_at']
              hoare_lift_Pf2[where f=ksCurThread, OF tcbSchedEnqueue_in_ksQ']
              hoare_vcg_imp_lift'
           | strengthen not_pred_tcb_at'_strengthen)+

  apply (clarsimp simp: comp_def)
  apply (frule invs_queues)
  apply (clarsimp simp: invs_valid_queues' tcb_at_invs' st_tcb_at_neg' is_active_tcb_ptr_runnable')
  apply (fastforce simp: all_invs_but_ct_idle_or_in_cur_domain'_strg invs_switchToThread_runnable')
  done
qed

lemma setNotification_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   setNotification p ntfn
   \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  apply (rule no_orphans_lift)
      apply (wp | clarsimp simp: setNotification_def updateObject_default_def)+
  done

crunches doMachineOp, setMessageInfo
  for no_orphans [wp]: "no_orphans"
  (wp: no_orphans_lift)

crunches completeSignal
  for no_orphans [wp]: "no_orphans"
  (simp: crunch_simps wp: crunch_wps)

lemma possibleSwitchTo_almost_no_orphans [wp]:
  "\<lbrace> \<lambda>s. almost_no_orphans target s \<and> valid_queues' s \<and> st_tcb_at' runnable' target s
         \<and> weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>
   possibleSwitchTo target
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding possibleSwitchTo_def
  by (wp rescheduleRequired_valid_queues'_weak tcbSchedEnqueue_almost_no_orphans
         ssa_almost_no_orphans static_imp_wp
     | wpc | clarsimp
     | wp (once) hoare_drop_imp)+

lemma possibleSwitchTo_almost_no_orphans':
  "\<lbrace> \<lambda>s. almost_no_orphans target s \<and> valid_queues' s \<and> st_tcb_at' runnable' target s
         \<and> sch_act_wf (ksSchedulerAction s) s \<rbrace>
   possibleSwitchTo target
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  by wp (strengthen sch_act_wf_weak, assumption)

lemma tcbSchedAppend_almost_no_orphans:
  "\<lbrace> \<lambda>s. almost_no_orphans thread s \<and> valid_queues' s \<rbrace>
   tcbSchedAppend thread
   \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wp setQueue_almost_no_orphans_enq[where tcb_ptr=thread] threadSet_no_orphans
            | clarsimp simp: unless_def | simp only: subset_insertI)+
  apply (unfold threadGet_def)
  apply (wp getObject_tcb_wp | clarsimp)+
  apply (drule obj_at_ko_at', clarsimp)
  apply (rule_tac x=ko in exI)
  apply (clarsimp simp: almost_no_orphans_def no_orphans_def)
  apply (drule queued_in_queue | simp)+
  apply (auto simp: all_queued_tcb_ptrs_def)
  done

lemma no_orphans_is_almost[simp]:
  "no_orphans s \<Longrightarrow> almost_no_orphans t s"
  by (clarsimp simp: no_orphans_def almost_no_orphans_def)

crunches decDomainTime
  for no_orphans [wp]: no_orphans
  and valid_queues' [wp]: valid_queues'
  (wp: no_orphans_lift)

lemma timerTick_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   timerTick
   \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  unfolding timerTick_def getDomainTime_def
  supply if_split[split del]
  apply (subst threadState_case_if)
  apply (wpsimp wp: threadSet_no_orphans threadSet_valid_queues'
                    threadSet_valid_queues' tcbSchedAppend_almost_no_orphans
                    threadSet_almost_no_orphans threadSet_no_orphans tcbSchedAppend_sch_act_wf
                    hoare_drop_imp
                simp: if_apply_def2
         | strengthen sch_act_wf_weak)+
      apply (rule_tac Q="\<lambda>rv s. no_orphans s \<and> valid_queues' s \<and> tcb_at' thread s
                                \<and> sch_act_wf  (ksSchedulerAction s) s" in hoare_post_imp)
       apply (clarsimp simp: inQ_def)
      apply (wp hoare_drop_imps | clarsimp)+
  apply (auto split: if_split)
  done


lemma handleDoubleFault_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<rbrace>
   handleDoubleFault tptr ex1 ex2
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding handleDoubleFault_def
  apply (wp setThreadState_not_active_no_orphans
         | clarsimp simp: is_active_thread_state_def isRestart_def isRunning_def)+
  done

crunches cteInsert, getThreadCallerSlot, getThreadReplySlot
  for st_tcb' [wp]: "st_tcb_at' (\<lambda>st. P st) t"
  and no_orphans [wp]: "no_orphans"
  and almost_no_orphans [wp]: "almost_no_orphans tcb_ptr"
  (wp: crunch_wps)

lemma setupCallerCap_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<rbrace>
   setupCallerCap sender receiver gr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setupCallerCap_def
  apply (wp setThreadState_not_active_no_orphans
         | clarsimp simp: is_active_thread_state_def isRestart_def isRunning_def)+
  done

lemma setupCallerCap_almost_no_orphans [wp]:
  "\<lbrace> \<lambda>s. almost_no_orphans tcb_ptr s \<and> valid_queues' s \<rbrace>
   setupCallerCap sender receiver gr
   \<lbrace> \<lambda>rv s. almost_no_orphans tcb_ptr s \<rbrace>"
  unfolding setupCallerCap_def
  apply (wp setThreadState_not_active_almost_no_orphans
         | clarsimp simp: is_active_thread_state_def isRestart_def isRunning_def)+
  done

crunches doIPCTransfer, setMRs, setEndpoint
  for ksReadyQueues [wp]: "\<lambda>s. P (ksReadyQueues s)"
  and no_orphans [wp]: "no_orphans"
  (wp: transferCapsToSlots_pres1 crunch_wps no_orphans_lift updateObject_default_inv)

lemma sendIPC_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s \<rbrace>
   sendIPC blocking call badge canGrant canGrantReply thread epptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding sendIPC_def
  apply (wp hoare_drop_imps setThreadState_not_active_no_orphans sts_st_tcb'
            possibleSwitchTo_almost_no_orphans'
         | wpc
         | clarsimp simp: is_active_thread_state_def isRestart_def isRunning_def)+

  apply (rule_tac Q="\<lambda>rv. no_orphans and valid_queues' and valid_objs' and ko_at' rv epptr
                          and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp)
   apply (fastforce simp: valid_objs'_def valid_obj'_def valid_ep'_def obj_at'_def projectKOs)
  apply (wp get_ep_sp' | clarsimp)+
  done

lemma sendFaultIPC_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s \<rbrace>
   sendFaultIPC tptr fault
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding sendFaultIPC_def
  apply (rule hoare_pre)
   apply (wp threadSet_valid_queues' threadSet_no_orphans threadSet_valid_objs'
             threadSet_sch_act | wpc | clarsimp)+
    apply (rule_tac Q'="\<lambda>handlerCap s. no_orphans s \<and> valid_queues' s
                                         \<and> valid_objs' s
                                         \<and> sch_act_wf (ksSchedulerAction s) s"
             in hoare_post_imp_R)
     apply (wp | clarsimp simp: inQ_def valid_tcb'_def tcb_cte_cases_def)+
  done

lemma sendIPC_valid_queues' [wp]:
  "\<lbrace> \<lambda>s. valid_queues' s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s \<rbrace>
   sendIPC blocking call badge canGrant canGrantReply thread epptr
   \<lbrace> \<lambda>rv s. valid_queues' s \<rbrace>"
  unfolding sendIPC_def
  apply (wpsimp wp: hoare_drop_imps)
        apply (wpsimp | wp (once) sts_st_tcb')+
  apply (rule_tac Q="\<lambda>rv. valid_queues' and valid_objs' and ko_at' rv epptr
                          and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp)
   apply (clarsimp)
  apply (wp get_ep_sp' | clarsimp)+
  done

lemma sendFaultIPC_valid_queues' [wp]:
  "\<lbrace> \<lambda>s. valid_queues' s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s \<rbrace>
   sendFaultIPC tptr fault
   \<lbrace> \<lambda>rv s. valid_queues' s \<rbrace>"
  unfolding sendFaultIPC_def
  apply (rule hoare_pre)
   apply (wp threadSet_valid_queues' threadSet_valid_objs' threadSet_sch_act
          | wpc | clarsimp)+
    apply (rule_tac Q'="\<lambda>handlerCap s. valid_queues' s \<and> valid_objs' s
                                         \<and> sch_act_wf (ksSchedulerAction s) s"
             in hoare_post_imp_R)
     apply (wp | clarsimp simp: inQ_def valid_tcb'_def tcb_cte_cases_def)+
  done

lemma handleFault_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s \<rbrace>
   handleFault tptr ex1
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding handleFault_def
  apply (rule hoare_pre)
   apply (wp | clarsimp)+
  done

lemma replyFromKernel_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   replyFromKernel thread r
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (cases r, simp_all add: replyFromKernel_def)
  apply wp
  done

crunch ksSchedulerAction [wp]: setMessageInfo "\<lambda>s. P (ksSchedulerAction s)"

crunch ksCurThread [wp]: createNewCaps "\<lambda> s. P (ksCurThread s)"

crunch ksReadyQueues  [wp]: createNewCaps "\<lambda> s. P (ksReadyQueues s)"

crunch inv [wp]: alignError "P"

lemma createObjects_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> pspace_aligned' s \<and> pspace_no_overlap' ptr sz s \<and> pspace_distinct' s
      \<and> n \<noteq> 0 \<and> range_cover ptr sz (objBitsKO val + gbits) n
      \<and> \<not> case_option False (is_active_thread_state \<circ> tcbState) (projectKO_opt val) \<rbrace>
   createObjects ptr n val gbits
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                        is_active_tcb_ptr_def all_queued_tcb_ptrs_def)
  apply (simp only: imp_conv_disj pred_tcb_at'_def createObjects_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift createObjects_orig_obj_at2')
  apply clarsimp
  apply (erule(1) impE)
  apply clarsimp
  apply (drule_tac x = x in spec)
  apply (erule impE)
   apply (clarsimp simp:obj_at'_def projectKOs split: option.splits)
  apply simp
  done

lemma copyGlobalMappings_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   copyGlobalMappings newPD
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch no_orphans [wp]: insertNewCap "no_orphans"
(wp: hoare_drop_imps)

lemma createNewCaps_no_orphans:
  "\<lbrace> (\<lambda>s. no_orphans s
         \<and>  pspace_aligned' s \<and> pspace_distinct' s
         \<and>  pspace_no_overlap' ptr sz s
         \<and>  (tp = APIObjectType CapTableObject \<longrightarrow> us > 0))
         and K (range_cover ptr sz (APIType_capBits tp us) n \<and> 0 < n) \<rbrace>
   createNewCaps tp ptr n us d
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (clarsimp simp: createNewCaps_def toAPIType_def
    split del: if_split cong: option.case_cong)
  apply (cases tp, simp_all split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all)
            apply (wp mapM_x_wp' threadSet_no_orphans
                   | clarsimp simp: is_active_thread_state_def makeObject_tcb
                                    projectKO_opt_tcb isRunning_def isRestart_def
                                    APIType_capBits_def Arch_createNewCaps_def
                                    objBits_if_dev
                          split del: if_split
                   | simp add: objBits_simps
                   | fastforce simp:pageBits_def pteBits_def archObjSize_def ptBits_def pdBits_def
                                    pdeBits_def objBits_simps)+
  done

lemma createObject_no_orphans:
  "\<lbrace>pspace_no_overlap' ptr sz and pspace_aligned' and pspace_distinct' and
    cte_wp_at' (\<lambda>cte. cteCap cte = (capability.UntypedCap d ptr sz idx)) cref and
    K (range_cover ptr sz (APIType_capBits tp us) (Suc 0)) and no_orphans\<rbrace>
   RetypeDecls_H.createObject tp ptr us d
   \<lbrace>\<lambda>xa. no_orphans\<rbrace>"
  apply (simp only: createObject_def ARM_H.createObject_def placeNewObject_def2)
  apply (wpsimp wp: createObjects'_wp_subst threadSet_no_orphans
                  createObjects_no_orphans[where sz = sz]
    simp: placeNewObject_def2 placeNewDataObject_def
                       projectKO_opt_tcb cte_wp_at_ctes_of projectKO_opt_ep
                       is_active_thread_state_def makeObject_tcb pageBits_def unless_def
                       projectKO_opt_tcb isRunning_def isRestart_def
                       APIType_capBits_def objBits_simps
    split_del: if_split)
  apply (clarsimp simp: toAPIType_def APIType_capBits_def objBits_simps
                        archObjSize_def pteBits_def ptBits_def
                        pdeBits_def pdBits_def
      split: object_type.split_asm apiobject_type.split_asm)
  done

lemma createNewObjects_no_orphans:
  "\<lbrace>\<lambda>s. no_orphans s \<and> invs' s \<and> pspace_no_overlap' ptr sz s
         \<and> (\<forall>slot\<in>set slots. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s)
         \<and> cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d (ptr && ~~ mask sz) sz idx) cref s
         \<and> caps_no_overlap'' ptr sz s
         \<and> range_cover ptr sz (APIType_capBits tp us) (length slots)
         \<and> (tp = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> us > 0)
         \<and> caps_overlap_reserved' {ptr..ptr + of_nat (length slots) * 2 ^ APIType_capBits tp us - 1} s
         \<and> slots \<noteq> [] \<and> distinct slots \<and> ptr \<noteq> 0\<rbrace>
   createNewObjects tp cref slots ptr us d
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (rule hoare_pre)
   apply (rule createNewObjects_wp_helper)
       apply simp+
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
     apply (erule range_cover.range_cover_n_less[where 'a=32, folded word_bits_def])
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
  apply (wp hoare_drop_imps | clarsimp)+
  apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                        all_queued_tcb_ptrs_def is_active_tcb_ptr_def
                        ksMachineState_ksPSpace_upd_comm)
  apply (drule_tac x=tcb_ptr in spec)
  apply (clarsimp simp: pred_tcb_at'_def obj_at_delete'[simplified field_simps]
                  cong: if_cong)
  done

crunch no_orphans[wp]: updateFreeIndex "no_orphans"

lemma resetUntypedCap_no_orphans [wp]:
  "\<lbrace> (\<lambda>s. no_orphans s \<and> pspace_distinct' s \<and> valid_objs' s)
      and cte_wp_at' (isUntypedCap o cteCap) slot\<rbrace>
    resetUntypedCap slot
  \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (simp add: resetUntypedCap_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp preemptionPoint_inv getSlotCap_wp hoare_drop_imps
     | simp add: unless_def split del: if_split)+
  apply (clarsimp simp: cte_wp_at_ctes_of split del: if_split)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD])
  apply (clarsimp simp: isCap_simps valid_cap_simps' capAligned_def)
  done

lemma invokeUntyped_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_untyped_inv' ui s \<and> ct_active' s \<rbrace>
   invokeUntyped ui
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule invokeUntyped_invs''[where Q=no_orphans])
       apply (wp createNewCaps_no_orphans)+
      apply (clarsimp simp: valid_pspace'_def)
      apply (intro conjI, simp_all)[1]
     apply (wp | simp)+
  apply (cases ui, auto simp: cte_wp_at_ctes_of)[1]
  done

lemma setInterruptState_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   setInterruptState a
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift | clarsimp)+
  done

crunch no_orphans [wp]: emptySlot "no_orphans"

lemma mapM_x_match:
  "\<lbrace>I and V xs\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace> \<Longrightarrow> \<lbrace>I and V xs\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  by assumption

lemma cancelAllIPC_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<rbrace>
    cancelAllIPC epptr
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding cancelAllIPC_def
  apply (wp sts_valid_objs' set_ep_valid_objs' sts_st_tcb'
            hoare_vcg_const_Ball_lift tcbSchedEnqueue_almost_no_orphans
             | wpc
             | rule mapM_x_match,
               rename_tac list,
               rule_tac V="\<lambda>_. valid_queues' and valid_objs'"
                    and I="no_orphans and (\<lambda>s. \<forall>t\<in>set list. tcb_at' t s)"
                     in mapM_x_inv_wp2
             | clarsimp simp: valid_tcb_state'_def)+
  apply (rule_tac Q="\<lambda>rv. no_orphans and valid_objs' and valid_queues' and ko_at' rv epptr"
                 in hoare_post_imp)
   apply (fastforce simp: valid_obj'_def valid_ep'_def obj_at'_def projectKOs)
  apply (wp get_ep_sp' | clarsimp)+
  done

lemma cancelAllSignals_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<rbrace>
    cancelAllSignals ntfn
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding cancelAllSignals_def
  apply (wp sts_valid_objs' set_ntfn_valid_objs' sts_st_tcb'
            hoare_vcg_const_Ball_lift tcbSchedEnqueue_almost_no_orphans
             | wpc
             | clarsimp simp: valid_tcb_state'_def)+
    apply (rename_tac list)
    apply (rule_tac V="\<lambda>_. valid_queues' and valid_objs'"
                and I="no_orphans and (\<lambda>s. \<forall>t\<in>set list. tcb_at' t s)"
                in mapM_x_inv_wp2)
    apply simp
   apply (wp sts_valid_objs' set_ntfn_valid_objs' sts_st_tcb'
            hoare_vcg_const_Ball_lift tcbSchedEnqueue_almost_no_orphans|
          clarsimp simp: valid_tcb_state'_def)+
  apply (rule_tac Q="\<lambda>rv. no_orphans and valid_objs' and valid_queues' and ko_at' rv ntfn"
                 in hoare_post_imp)
   apply (fastforce simp: valid_obj'_def valid_ntfn'_def obj_at'_def projectKOs)
  apply (wp get_ntfn_sp' | clarsimp)+
  done

crunch no_orphans[wp]: setBoundNotification "no_orphans"

lemma unbindNotification_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s\<rbrace>
    unbindNotification t
   \<lbrace> \<lambda>rv s. no_orphans s\<rbrace>"
  unfolding unbindNotification_def
  apply (rule hoare_seq_ext[OF _ gbn_sp'])
  apply (case_tac ntfnPtr, simp_all, wp, simp)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (wp | simp)+
  done

lemma unbindMaybeNotification_no_orphans[wp]:
  "\<lbrace>\<lambda>s. no_orphans s\<rbrace>
    unbindMaybeNotification a
   \<lbrace> \<lambda>rv s. no_orphans s\<rbrace>"
  unfolding unbindMaybeNotification_def
  by (wp getNotification_wp | simp | wpc)+

lemma finaliseCapTrue_standin_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<rbrace>
    finaliseCapTrue_standin cap final
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding finaliseCapTrue_standin_def
  apply (rule hoare_pre)
   apply (wp | clarsimp simp: Let_def | wpc)+
  done

lemma cteDeleteOne_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<rbrace>
   cteDeleteOne slot
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding cteDeleteOne_def
  apply (wp assert_inv isFinalCapability_inv weak_if_wp | clarsimp simp: unless_def)+
  done

crunch valid_objs' [wp]: getThreadReplySlot "valid_objs'"

lemma cancelSignal_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<rbrace>
   cancelSignal t ntfn
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding cancelSignal_def Let_def
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps setThreadState_not_active_no_orphans | wpc
          | clarsimp simp: is_active_thread_state_def isRestart_def isRunning_def)+
  done

lemma cancelIPC_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<rbrace>
   cancelIPC t
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding cancelIPC_def Let_def
  apply (rule hoare_pre)
   apply (wp setThreadState_not_active_no_orphans hoare_drop_imps weak_if_wp
             threadSet_valid_queues' threadSet_valid_objs' threadSet_no_orphans | wpc
          | clarsimp simp: is_active_thread_state_def isRestart_def isRunning_def
                           inQ_def valid_tcb'_def tcb_cte_cases_def)+
  done


lemma asUser_almost_no_orphans:
  "\<lbrace>almost_no_orphans t\<rbrace> asUser a f \<lbrace>\<lambda>_. almost_no_orphans t\<rbrace>"
  unfolding almost_no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch almost_no_orphans[wp]: asUser "almost_no_orphans t"
  (simp: almost_no_orphans_disj all_queued_tcb_ptrs_def wp: hoare_vcg_all_lift hoare_vcg_disj_lift crunch_wps)

lemma sendSignal_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   sendSignal ntfnptr badge
   \<lbrace> \<lambda>_ s. no_orphans s \<rbrace>"
  unfolding sendSignal_def
  apply (rule hoare_pre)
   apply (wp sts_st_tcb' gts_wp' getNotification_wp asUser_almost_no_orphans
                          cancelIPC_weak_sch_act_wf
          | wpc | clarsimp simp: sch_act_wf_weak)+
  done

lemma handleInterrupt_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   handleInterrupt irq
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding handleInterrupt_def
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps hoare_vcg_all_lift getIRQState_inv
          | wpc | clarsimp simp: invs'_def valid_state'_def maskIrqSignal_def
                                 handleReservedIRQ_def)+
  done

lemma updateRestartPC_no_orphans[wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   updateRestartPC t
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  by (wpsimp simp: updateRestartPC_def asUser_no_orphans)

lemma updateRestartPC_valid_queues'[wp]:
  "\<lbrace> \<lambda>s. valid_queues' s \<rbrace>
   updateRestartPC t
   \<lbrace> \<lambda>rv s. valid_queues' s \<rbrace>"
  unfolding updateRestartPC_def
  apply (rule asUser_valid_queues')
  done

lemma updateRestartPC_no_orphans_invs'_valid_queues'[wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> invs' s \<and> valid_queues' s \<rbrace>
   updateRestartPC t
   \<lbrace>\<lambda>rv s. no_orphans s \<and> valid_queues' s \<rbrace>"
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

lemma storeHWASID_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   storeHWASID asid hw_asid
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma invalidateHWASIDEntry_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   invalidateHWASIDEntry hwASID
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma invalidateASID_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   invalidateASID asid
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma findFreeHWASID_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   findFreeHWASID
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch ksCurThread [wp]: invalidateASIDEntry "\<lambda> s. P (ksCurThread s)"

crunch ksReadyQueues[wp]: invalidateASIDEntry "\<lambda>s. P (ksReadyQueues s)"

lemma invalidateASIDEntry_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   invalidateASIDEntry asid
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch no_orphans [wp]: flushSpace "no_orphans"

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
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   storePTE ptr val
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma storePDE_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   storePDE ptr val
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunches unmapPage
  for no_orphans [wp]: "no_orphans"
  (wp: crunch_wps)

lemma flushTable_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   flushTable pd asid vptr
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  unfolding flushTable_def
  apply (wp hoare_drop_imps | wpc | clarsimp)+
  done

crunches unmapPageTable, prepareThreadDelete
  for no_orphans [wp]: "no_orphans"

lemma setASIDPool_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   setObject p (ap :: asidpool)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma deleteASID_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   deleteASID asid pd
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding deleteASID_def
  apply (wp getObject_inv loadObject_default_inv | wpc | clarsimp)+
  done

lemma arch_finaliseCap_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   Arch.finaliseCap cap fin
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding ARM_H.finaliseCap_def
  apply (wpsimp simp: isCap_simps)
  apply (safe; wpsimp)
  done

lemma deletingIRQHandler_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   deletingIRQHandler irq
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding deletingIRQHandler_def
  apply (wp, auto)
  done

lemma finaliseCap_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> valid_cap' cap s \<rbrace>
   finaliseCap cap final flag
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (simp add: finaliseCap_def Let_def
              cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp | clarsimp simp: o_def | wpc)+
  apply (auto simp: valid_cap'_def dest!: isCapDs)
  done

crunches cteSwap, capSwapForDelete
  for no_orphans [wp]: "no_orphans"

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
  apply (rule validE_valid, rule hoare_pre,
    rule hoare_post_impErr, rule use_spec)
     apply (rule finaliseSlot_invs'[where p=slot and slot=slot and Pr=no_orphans])
      apply (simp_all add: no_orphans_finalise_prop_stuff)
   apply (wp | simp)+
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
  apply (rule_tac Q="\<lambda>rv s. no_orphans s \<and> invs' s \<and> sch_act_simple s"
                      in hoare_strengthen_post)
   apply (wp cteRevoke_preservation cteDelete_invs' cteDelete_sch_act_simple)+
      apply auto
  done

lemma cancelBadgedSends_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<rbrace>
   cancelBadgedSends epptr badge
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding cancelBadgedSends_def
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpc | clarsimp)+
      apply (wp filterM_preserved tcbSchedEnqueue_almost_no_orphans gts_wp'
                sts_st_tcb' hoare_drop_imps | clarsimp)+
  done

crunch no_orphans [wp]: invalidateTLBByASID "no_orphans"

crunch no_orphans [wp]: handleFaultReply "no_orphans"

crunch valid_queues' [wp]: handleFaultReply "valid_queues'"

lemma doReplyTransfer_no_orphans[wp]:
  "\<lbrace>no_orphans and invs' and tcb_at' sender and tcb_at' receiver\<rbrace>
   doReplyTransfer sender receiver slot grant
   \<lbrace>\<lambda>rv. no_orphans\<rbrace>"
  unfolding doReplyTransfer_def
  apply (wp sts_st_tcb' setThreadState_not_active_no_orphans threadSet_no_orphans
            threadSet_valid_queues' threadSet_weak_sch_act_wf
         | wpc | clarsimp simp: is_active_thread_state_def isRunning_def isRestart_def
         | wp (once) hoare_drop_imps
         | strengthen sch_act_wf_weak invs_valid_queues')+
              apply (rule_tac Q="\<lambda>rv. invs' and no_orphans" in hoare_post_imp)
               apply (fastforce simp: inQ_def)
              apply (wp hoare_drop_imps | clarsimp)+
  apply (clarsimp simp:invs'_def valid_state'_def valid_pspace'_def)
  done

lemma cancelSignal_valid_queues' [wp]:
  "\<lbrace> \<lambda>s. valid_queues' s \<and> valid_objs' s \<rbrace>
   cancelSignal t ntfn
   \<lbrace> \<lambda>rv s. valid_queues' s \<rbrace>"
  unfolding cancelSignal_def Let_def
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpc | clarsimp)+
  done

crunch no_orphans [wp]: setupReplyMaster "no_orphans"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_queues' [wp]: setupReplyMaster "valid_queues'"

lemma restart_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_at' t s \<rbrace>
   restart t
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding restart_def isStopped_def2
  apply (wp tcbSchedEnqueue_almost_no_orphans sts_st_tcb' cancelIPC_weak_sch_act_wf
         | clarsimp simp: o_def if_apply_def2
         | strengthen no_orphans_strg_almost
         | strengthen invs_valid_queues'
         | wp (once) hoare_drop_imps)+
  apply auto
  done

lemma readreg_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_at' src s \<rbrace>
     invokeTCB (tcbinvocation.ReadRegisters src susp n arch)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def
  apply (wp | clarsimp)+
  done

lemma writereg_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s
       \<and> tcb_at' dest s \<and> ex_nonz_cap_to' dest s\<rbrace>
     invokeTCB (tcbinvocation.WriteRegisters dest resume values arch)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def postModifyRegisters_def
  apply simp
  apply (rule hoare_pre)
  by (wp hoare_vcg_if_lift hoare_vcg_conj_lift restart_invs' static_imp_wp
       | strengthen invs_valid_queues'  | clarsimp  simp: invs'_def valid_state'_def dest!: global'_no_ex_cap )+


lemma copyreg_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_at' src s
         \<and> tcb_at' dest s \<and> ex_nonz_cap_to' src s \<and> ex_nonz_cap_to' dest s \<rbrace>
     invokeTCB (tcbinvocation.CopyRegisters dest src susp resume frames ints arch)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def postModifyRegisters_def
  supply if_weak_cong[cong]
  apply simp
  apply (wp hoare_vcg_if_lift static_imp_wp)
      apply (wp hoare_vcg_imp_lift' mapM_x_wp' asUser_no_orphans
             | wpc | clarsimp split del: if_splits)+
       apply (wp static_imp_wp hoare_vcg_conj_lift hoare_drop_imp mapM_x_wp' restart_invs'
              restart_no_orphans asUser_no_orphans suspend_nonz_cap_to_tcb
              | strengthen invs_valid_queues' | wpc | simp add: if_apply_def2)+
  apply (fastforce simp: invs'_def valid_state'_def dest!: global'_no_ex_cap)
  done

lemma settlsbase_no_orphans:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
     invokeTCB (tcbinvocation.SetTLSBase src dest)
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding invokeTCB_def performTransfer_def
  apply simp
  apply (wp hoare_vcg_if_lift static_imp_wp)
   apply (wpsimp wp: hoare_vcg_imp_lift' mapM_x_wp' asUser_no_orphans)+
  done

lemma almost_no_orphans_no_orphans:
  "\<lbrakk> almost_no_orphans t s; \<not> is_active_tcb_ptr t s \<rbrakk> \<Longrightarrow> no_orphans s"
  by (auto simp: almost_no_orphans_def no_orphans_def all_active_tcb_ptrs_def)

lemma almost_no_orphans_no_orphans':
  "\<lbrakk> almost_no_orphans t s; ksCurThread s = t\<rbrakk> \<Longrightarrow> no_orphans s"
  by (auto simp: almost_no_orphans_def no_orphans_def all_active_tcb_ptrs_def)

lemma setPriority_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> tcb_at' tptr s \<rbrace>
   setPriority tptr prio
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding setPriority_def
  apply wpsimp
    apply (rule_tac Q="\<lambda>rv s. almost_no_orphans tptr s \<and> valid_queues' s \<and> weak_sch_act_wf (ksSchedulerAction s) s" in hoare_post_imp)
     apply clarsimp
     apply (clarsimp simp: is_active_tcb_ptr_runnable' pred_tcb_at'_def obj_at'_def
                           almost_no_orphans_no_orphans elim!: almost_no_orphans_no_orphans')
    apply (wp threadSet_almost_no_orphans threadSet_valid_queues' | clarsimp simp: inQ_def)+
    apply (wpsimp wp: threadSet_weak_sch_act_wf)
   apply (wp tcbSchedDequeue_almost_no_orphans| clarsimp)+
   apply (rule_tac Q="\<lambda>rv. obj_at' (Not \<circ> tcbQueued) tptr and invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp)
    apply (clarsimp simp: obj_at'_def inQ_def)
   apply (wp tcbSchedDequeue_not_queued | clarsimp)+
  done

lemma setMCPriority_no_orphans[wp]:
  "\<lbrace>no_orphans\<rbrace> setMCPriority t prio \<lbrace>\<lambda>rv. no_orphans\<rbrace>"
  unfolding setMCPriority_def
  apply (rule hoare_pre)
   apply (wp threadSet_no_orphans)
   by clarsimp+

lemma threadSet_ipcbuffer_invs:
  "is_aligned a msg_align_bits \<Longrightarrow>
  \<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbIPCBuffer_update (\<lambda>_. a)) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp threadSet_invs_trivial, simp_all add: inQ_def cong: conj_cong)
  done

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
               threadSet_cap_to' hoare_vcg_all_lift static_imp_wp | clarsimp simp: inQ_def)+)[2]
  apply (rule hoare_walk_assmsE)
    apply (cases mcp; clarsimp simp: pred_conj_def option.splits[where P="\<lambda>x. x s" for s])
     apply ((wp case_option_wp threadSet_no_orphans threadSet_invs_trivial setMCPriority_invs'
                typ_at_lifts[OF setMCPriority_typ_at']
                threadSet_cap_to' hoare_vcg_all_lift static_imp_wp | clarsimp simp: inQ_def)+)[3]
  apply ((simp only: simp_thms cong: conj_cong
          | wp cteDelete_deletes cteDelete_invs' cteDelete_sch_act_simple
               case_option_wp[where m'="return ()", OF setPriority_no_orphans return_inv,simplified]
               checkCap_inv[where P="valid_cap' c" for c] checkCap_inv[where P=sch_act_simple]
               checkCap_inv[where P=no_orphans] checkCap_inv[where P="tcb_at' a"]
               threadSet_cte_wp_at' hoare_vcg_all_lift_R hoare_vcg_all_lift threadSet_no_orphans
               hoare_vcg_const_imp_lift_R static_imp_wp hoare_drop_imp threadSet_ipcbuffer_invs
          | strengthen invs_valid_queues'
          | (simp add: locateSlotTCB_def locateSlotBasic_def objBits_def
                     objBitsKO_def tcbIPCBufferSlot_def tcb_cte_cases_def,
           wp hoare_return_sp)
          | wpc | clarsimp)+)
  apply (fastforce simp: objBits_defs isCap_simps dest!: isValidVTableRootD)
  done

lemma bindNotification_no_orphans[wp]:
  "\<lbrace>no_orphans\<rbrace> bindNotification t ntfn \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding bindNotification_def
  by wp

lemma invokeTCB_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> sch_act_simple s \<and> tcb_inv_wf' tinv s \<rbrace>
   invokeTCB tinv
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (case_tac tinv, simp_all)
       apply (clarsimp simp: invokeTCB_def)
       apply (wp, clarsimp)
      apply (clarsimp simp: invokeTCB_def)
      apply (wp, clarsimp)
     apply (wp tc_no_orphans)
     apply (clarsimp split: option.splits simp: msg_align_bits elim!:is_aligned_weaken)
     apply (rename_tac option)
     apply (case_tac option)
      apply ((wp | simp add: invokeTCB_def)+)[2]
    apply (wp writereg_no_orphans readreg_no_orphans copyreg_no_orphans settlsbase_no_orphans | clarsimp)+
  done

lemma invokeCNode_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_cnode_inv' cinv s \<and> sch_act_simple s \<rbrace>
   invokeCNode cinv
   \<lbrace> \<lambda>rv. no_orphans \<rbrace>"
  unfolding invokeCNode_def
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps unless_wp | wpc | clarsimp split del: if_split)+
  apply (simp add: invs_valid_queues')
  done

lemma invokeIRQControl_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   performIRQControl i
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (cases i, simp_all add: performIRQControl_def ARM_H.performIRQControl_def)
  apply (rename_tac archinv)
  apply (case_tac archinv)
  apply (wp | clarsimp)+
  done

lemma invokeIRQHandler_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   invokeIRQHandler i
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (cases i, simp_all add: invokeIRQHandler_def)
    apply (wp | clarsimp | fastforce)+
  done

crunch no_orphans [wp]: setVMRootForFlush "no_orphans"
(wp: crunch_wps)

lemma performPageTableInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   performPageTableInvocation pti
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (cases pti, simp_all add: performPageTableInvocation_def)
   apply (rule hoare_pre)
    apply (wp mapM_x_wp' | wpc | clarsimp)+
  done

lemma performPageInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   performPageInvocation pgi
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (simp add: performPageInvocation_def
              cong: page_invocation.case_cong)
  apply (rule hoare_pre)
   apply (wp mapM_x_wp' mapM_wp' static_imp_wp | wpc | clarsimp simp: pdeCheckIfMapped_def pteCheckIfMapped_def)+
  done

lemma performASIDControlInvocation_no_orphans [wp]:
  notes blah[simp del] =
  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex usableUntypedRange.simps
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
                     "(ptr :: word32) < 2 ^ asid_bits" "ct_active' s"
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

  have exclude: "cref \<notin> {ptr_base..ptr_base + 2 ^ pageBits - 1}"
    apply (rule descendants_range_ex_cte'[where cte = "ut_cte"])
        apply (rule empty_descendants_range_in'[OF desc])
       apply (rule if_unsafe_then_capD'[where P = "\<lambda>c. c = ut_cte"])
         apply (clarsimp simp: cte_wp_at_ctes_of cte)
        apply (simp add:invs' invs_unsafe_then_cap')
     apply (simp add:cte invs')+
    done

  show "\<lbrace>(=) s\<rbrace>performASIDControlInvocation (asidcontrol_invocation.MakePool ptr_base p cref ptr)
       \<lbrace>\<lambda>reply. no_orphans\<rbrace>"
  apply (clarsimp simp: performASIDControlInvocation_def
                  split: asidcontrol_invocation.splits)
  apply (wp static_imp_wp | clarsimp)+
    apply (rule_tac Q="\<lambda>rv s. no_orphans s" in hoare_post_imp)
     apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                           is_active_tcb_ptr_def all_queued_tcb_ptrs_def)
    apply (wp | clarsimp simp:placeNewObject_def2)+
     apply (wp createObjects'_wp_subst)+
     apply (wp static_imp_wp updateFreeIndex_pspace_no_overlap'[where sz= pageBits] getSlotCap_wp | simp)+
  apply (strengthen invs_pspace_aligned' invs_pspace_distinct' invs_valid_pspace')
  apply (clarsimp simp:conj_comms)
     apply (wp deleteObjects_invs'[where idx = idx and d=False]
       hoare_vcg_ex_lift deleteObjects_cte_wp_at'[where idx = idx and d=False] hoare_vcg_const_imp_lift )
  using invs' misc cte exclude no_orphans cover
  apply (clarsimp simp: is_active_thread_state_def makeObject_tcb valid_aci'_def
                        cte_wp_at_ctes_of invs_pspace_aligned' invs_pspace_distinct'
                        projectKO_opt_tcb isRunning_def isRestart_def conj_comms
                        invs_valid_pspace' vc objBits_simps archObjSize_def range_cover.aligned)
  apply (intro conjI)
    apply (rule vc)
   apply (simp add:descendants_range'_def2)
   apply (rule empty_descendants_range_in'[OF desc])
  apply clarsimp
  done
qed

lemma performASIDPoolInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   performASIDPoolInvocation api
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (cases api, simp_all add: performASIDPoolInvocation_def)
  apply (wp getObject_inv loadObject_default_inv | clarsimp)+
  done

lemma performPageDirectoryInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   performPageDirectoryInvocation pdi
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (cases pdi, simp_all add: performPageDirectoryInvocation_def)
  apply (wp | simp)+
  done

lemma arch_performInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_arch_inv' i s \<and> ct_active' s \<rbrace>
   Arch.performInvocation i
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  unfolding ARM_H.performInvocation_def performARMMMUInvocation_def
  apply (cases i, simp_all add: valid_arch_inv'_def)
      apply (wp | clarsimp)+
  done

lemma setDomain_no_orphans [wp]:
  "\<lbrace>no_orphans and valid_queues and valid_queues' and cur_tcb'\<rbrace>
     setDomain tptr newdom
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  apply (simp add: setDomain_def when_def)
  apply (wp tcbSchedEnqueue_almost_no_orphans hoare_vcg_imp_lift threadSet_almost_no_orphans
            threadSet_valid_queues'_no_state threadSet_st_tcb_at2 hoare_vcg_disj_lift
            threadSet_no_orphans
       | clarsimp simp: st_tcb_at_neg2 not_obj_at')+
   apply (auto simp: tcb_at_typ_at' st_tcb_at_neg' is_active_tcb_ptr_runnable'
                     cur_tcb'_def obj_at'_def
               dest: pred_tcb_at')
  done

crunch no_orphans[wp]: InterruptDecls_H.invokeIRQHandler no_orphans

lemma performInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_invocation' i s \<and> ct_active' s \<and> sch_act_simple s \<rbrace>
   performInvocation block call i
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (simp add: performInvocation_def
              cong: invocation.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc | clarsimp)+
  apply auto
  done

lemma getThreadState_restart [wp]:
  "\<lbrace> \<lambda>s. tcb_at' thread s \<rbrace>
   getThreadState thread
   \<lbrace> \<lambda>rv s. rv = Structures_H.thread_state.Restart \<longrightarrow> st_tcb_at' isRestart thread s \<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule gts_st_tcb')
  apply (clarsimp simp add: pred_tcb_at'_def obj_at'_def isRestart_def)
  done

lemma K_bind_hoareE [wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> K_bind f x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

crunch valid_queues' [wp]: replyFromKernel "valid_queues'"

lemma handleInvocation_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> vs_valid_duplicates' (ksPSpace s) \<and>
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
         apply (wps setThreadState_ct')
         apply (wp sts_ksQ
                   setThreadState_current_no_orphans sts_invs_minor'
                   ct_in_state'_set setThreadState_st_tcb
                 | simp add: split_def split del: if_split)+
  apply (clarsimp simp: if_apply_def2)
  apply (frule(1) ct_not_ksQ)
  by (auto simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def invs'_def
                    cur_tcb'_def valid_state'_def valid_idle'_def)

lemma receiveSignal_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> valid_queues' s \<rbrace>
   receiveSignal thread cap isBlocking
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
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
                           doNBRecvFailedTransfer_def invs_valid_queues'
          | strengthen sch_act_wf_weak)+
  done

crunch valid_objs' [wp]: getThreadCallerSlot "valid_objs'"

lemma deleteCallerCap_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   deleteCallerCap receiver
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding deleteCallerCap_def
  by wpsimp auto

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
     apply (rule_tac Q'="\<lambda>rv s. no_orphans s \<and> invs' s" in hoare_post_imp_R)
      apply (wp, fastforce)
    apply (rule_tac Q="\<lambda>rv s. no_orphans s \<and> invs' s" in hoare_post_imp)
     apply (wp | clarsimp | fastforce)+
  done

crunches getThreadCallerSlot, handleHypervisorFault
  for invs' [wp]: "invs'"

lemma handleReply_no_orphans [wp]:
  "\<lbrace>no_orphans and invs'\<rbrace> handleReply \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding handleReply_def
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpc | clarsimp)+
     apply (wp hoare_vcg_all_lift)
      apply (rule_tac Q="\<lambda>rv s. no_orphans s \<and> invs' s \<and> tcb_at' thread s \<and>
                                valid_cap' rv s" in hoare_post_imp)
       apply (wp hoare_drop_imps | clarsimp simp: valid_cap'_def
              | clarsimp simp: invs'_def cur_tcb'_def valid_state'_def)+
  done

lemma handleYield_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<rbrace>
   handleYield
   \<lbrace> \<lambda>rv . no_orphans \<rbrace>"
  unfolding handleYield_def
  apply (wp tcbSchedAppend_almost_no_orphans)
  apply auto
  done

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
  "\<lbrace> \<lambda>s. invs' s \<and> vs_valid_duplicates' (ksPSpace s) \<and>
         (e \<noteq> Interrupt \<longrightarrow> ct_running' s) \<and>
         ksSchedulerAction s = ResumeCurrentThread \<and> no_orphans s \<rbrace>
   handleEvent e
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  apply (simp add: handleEvent_def handleSend_def handleCall_def
              cong: event.case_cong syscall.case_cong)
  apply (rule hoare_pre)
   apply (wp hv_inv' hoare_drop_imps | wpc | clarsimp simp: handleHypervisorFault_def)+
  apply (auto simp: activatable_from_running' active_from_running')
  done

theorem callKernel_no_orphans [wp]:
  "\<lbrace> \<lambda>s. invs' s \<and> vs_valid_duplicates' (ksPSpace s) \<and>
          (e \<noteq> Interrupt \<longrightarrow> ct_running' s) \<and>
          ksSchedulerAction s = ResumeCurrentThread \<and> no_orphans s \<rbrace>
   callKernel e
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding callKernel_def
  by (wpsimp wp: weak_if_wp schedule_invs' hoare_drop_imps)

end

end
