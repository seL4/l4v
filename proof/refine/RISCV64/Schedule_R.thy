(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_R
imports VSpace_R
begin

context begin interpretation Arch . (*FIXME: arch-split*)

declare hoare_weak_lift_imp[wp_split del]

(* Levity: added (20090713 10:04:12) *)
declare sts_rel_idle [simp]

lemma corres_if2:
 "\<lbrakk> G = G'; G \<Longrightarrow> corres r P P' a c; \<not> G' \<Longrightarrow> corres r Q Q' b d \<rbrakk>
    \<Longrightarrow> corres r (if G then P else Q) (if G' then P' else Q') (if G then a else b) (if G' then c else d)"
  by simp

lemma findM_awesome':
  assumes x: "\<And>x xs. suffix (x # xs) xs' \<Longrightarrow>
                  corres (\<lambda>a b. if b then (\<exists>a'. a = Some a' \<and> r a' (Some x)) else a = None)
                      P (P' (x # xs))
                      ((f >>= (\<lambda>x. return (Some x))) \<sqinter> (return None)) (g x)"
  assumes y: "corres r P (P' []) f (return None)"
  assumes z: "\<And>x xs. suffix (x # xs) xs' \<Longrightarrow>
                 \<lbrace>P' (x # xs)\<rbrace> g x \<lbrace>\<lambda>rv s. \<not> rv \<longrightarrow> P' xs s\<rbrace>"
  assumes p: "suffix xs xs'"
  shows      "corres r P (P' xs) f (findM g xs)"
proof -
  have P: "f = do x \<leftarrow> (do x \<leftarrow> f; return (Some x) od) \<sqinter> return None; if x \<noteq> None then return (the x) else f od"
    apply (rule ext)
    apply (auto simp add: bind_def alternative_def return_def split_def prod_eq_iff)
    done
  have Q: "\<lbrace>P\<rbrace> (do x \<leftarrow> f; return (Some x) od) \<sqinter> return None \<lbrace>\<lambda>rv. if rv \<noteq> None then \<top> else P\<rbrace>"
    by (wp | simp)+
  show ?thesis using p
    apply (induct xs)
     apply (simp add: y del: dc_simp)
    apply (simp only: findM.simps)
    apply (subst P)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF x])
         apply assumption
        apply (rule corres_if2)
          apply (case_tac ra, clarsimp+)[1]
         apply (rule corres_trivial, clarsimp)
         apply (case_tac ra, simp_all)[1]
        apply (erule(1) meta_mp [OF _ suffix_ConsD])
       apply (rule Q)
      apply (rule hoare_post_imp [OF _ z])
       apply simp+
    done
qed

lemmas findM_awesome = findM_awesome' [OF _ _ _ suffix_order.refl]

(* Levity: added (20090721 10:56:29) *)
declare objBitsT_koTypeOf [simp]

crunch set_vm_root
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  (simp: crunch_simps)

lemma arch_switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and pspace_aligned and pspace_distinct
                and valid_vspace_objs and st_tcb_at runnable t)
             (no_0_obj')
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  apply (simp add: arch_switch_to_thread_def RISCV64_H.switchToThread_def)
  apply (rule corres_guard_imp)
    apply (rule setVMRoot_corres[OF refl])
   apply (clarsimp simp: st_tcb_at_tcb_at valid_arch_state_asid_table
                         valid_arch_state_global_arch_objs)
  apply simp
  done

lemma schedule_choose_new_thread_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>rs s. scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by wp

\<comment> \<open>This proof shares many similarities with the proof of @{thm tcbSchedEnqueue_corres}\<close>
lemma tcbSchedAppend_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (in_correct_ready_q and ready_qs_distinct and st_tcb_at runnable tcb_ptr
      and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_sched_pointers and valid_tcbs')
     (tcb_sched_action tcb_sched_append tcb_ptr) (tcbSchedAppend tcbPtr)"
  supply if_split[split del]
         heap_path_append[simp del] fun_upd_apply[simp del] distinct_append[simp del]
  apply (rule_tac Q'="st_tcb_at' runnable' tcbPtr" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  apply (rule_tac Q="tcb_at tcb_ptr" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_tcb_at)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (clarsimp simp: tcb_sched_action_def tcb_sched_append_def get_tcb_queue_def
                        tcbSchedAppend_def getQueue_def unless_def when_def)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac domain)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac priority)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; wpsimp?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (subst if_distrib[where f="set_tcb_queue domain prio" for domain prio])
  apply (rule corres_if_strong')
    subgoal
      by (fastforce dest!: state_relation_ready_queues_relation
                           in_ready_q_tcbQueued_eq[where t=tcbPtr]
                     simp: obj_at'_def opt_pred_def opt_map_def in_correct_ready_q_def
                           obj_at_def etcb_at_def etcbs_of'_def)
   apply (find_goal \<open>match conclusion in "corres _ _ _ _ (return ())" \<Rightarrow> \<open>-\<close>\<close>)
   apply (rule monadic_rewrite_corres_l[where P=P and Q=P for P, simplified])
    apply (clarsimp simp: set_tcb_queue_def)
    apply (rule monadic_rewrite_guard_imp)
     apply (rule monadic_rewrite_modify_noop)
    apply (prop_tac "(\<lambda>d p. if d = domain \<and> p = priority
                            then ready_queues s domain priority
                            else ready_queues s d p)
                     = ready_queues s")
     apply (fastforce split: if_splits)
    apply fastforce
   apply clarsimp
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ gets_sp]; (solves wpsimp)?)

  \<comment> \<open>break off the addToBitmap\<close>
  apply (rule corres_add_noop_lhs)
  apply (rule corres_underlying_split[rotated 2,
                                      where Q="\<lambda>_. P" and P=P and Q'="\<lambda>_. P'" and P'=P' for P P'])

     apply wpsimp
    apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_ex_lift)
   apply (corres corres: addToBitmap_if_null_noop_corres)

  apply (rule corres_from_valid_det)
    apply (fastforce intro: det_wp_modify det_wp_pre simp: set_tcb_queue_def)
   apply (wpsimp simp: tcbQueueAppend_def wp: hoare_vcg_if_lift2 | drule Some_to_the)+
   apply (clarsimp simp: ex_abs_underlying_def split: if_splits)
   apply (frule state_relation_ready_queues_relation)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (drule_tac x="tcbDomain tcb" in spec)
   apply (drule_tac x="tcbPriority tcb" in spec)
   subgoal by (force dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: obj_at'_def)

  apply (rename_tac s rv t)
  apply (clarsimp simp: state_relation_def)
  apply (intro hoare_vcg_conj_lift_pre_fix;
         (solves \<open>frule singleton_eqD, frule set_tcb_queue_projs_inv, wpsimp simp: swp_def\<close>)?)

  \<comment> \<open>ready_queues_relation\<close>
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (intro hoare_allI)
  apply (drule singleton_eqD)
  apply (drule set_tcb_queue_new_state)
  apply (wpsimp wp: threadSet_wp simp: setQueue_def tcbQueueAppend_def)
  apply normalise_obj_at'
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac s d p s' tcb' tcb)
  apply (frule_tac t=tcbPtr in pspace_relation_tcb_domain_priority)
    apply (force simp: obj_at_def)
   apply (force simp: obj_at'_def)
  apply (clarsimp split: if_splits)
  apply (cut_tac ts="ready_queues s d p" in list_queue_relation_nil)
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (cut_tac ts="ready_queues s (tcb_domain tcb) (tcb_priority tcb)"
              in obj_at'_tcbQueueEnd_ksReadyQueues)
      apply fast
     apply fast
    apply fastforce
   apply fastforce
  apply (cut_tac xs="ready_queues s d p" in heap_path_head')
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (clarsimp simp: list_queue_relation_def)

  apply (case_tac "d \<noteq> tcb_domain tcb \<or> p \<noteq> tcb_priority tcb")
   apply (cut_tac d=d and d'="tcb_domain tcb" and p=p and p'="tcb_priority tcb"
               in ready_queues_disjoint)
      apply force
     apply fastforce
    apply fastforce
   apply (prop_tac "tcbPtr \<notin> set (ready_queues s d p)")
    apply (clarsimp simp: obj_at'_def opt_pred_def opt_map_def)
    apply (metis inQ_def option.simps(5) tcb_of'_TCB)
   apply (intro conjI impI; clarsimp)

    \<comment> \<open>the ready queue was originally empty\<close>
         apply (rule heap_path_heap_upd_not_in)
          apply (clarsimp simp: fun_upd_apply split: if_splits)
         apply fastforce
        apply (clarsimp simp: queue_end_valid_def fun_upd_apply split: if_splits)
       apply (rule prev_queue_head_heap_upd)
        apply (clarsimp simp: fun_upd_apply split: if_splits)
       apply (case_tac "ready_queues s d p";
              clarsimp simp: fun_upd_apply tcbQueueEmpty_def split: if_splits)
      apply (clarsimp simp: inQ_def in_opt_pred fun_upd_apply obj_at'_def split: if_splits)
     apply (clarsimp simp: fun_upd_apply split: if_splits)
    apply (clarsimp simp: fun_upd_apply split: if_splits)

   \<comment> \<open>the ready queue was not originally empty\<close>
   apply (clarsimp simp: obj_at'_def)
   apply (prop_tac "the (tcbQueueEnd (ksReadyQueues s' (tcb_domain tcb, tcb_priority tcb)))
                    \<notin> set (ready_queues s d p)")
    apply (erule orthD2)
    apply (drule_tac x="tcb_domain tcb" in spec)
    apply (drule_tac x="tcb_priority tcb" in spec)
    apply clarsimp
    apply (drule_tac x="the (tcbQueueEnd (ksReadyQueues s' (tcb_domain tcb, tcb_priority tcb)))"
                 in spec)
    subgoal by (auto simp: in_opt_pred opt_map_red)
   apply (intro conjI impI allI)
        apply (intro heap_path_heap_upd_not_in)
          apply (clarsimp simp: fun_upd_apply split: if_splits)
         apply simp
        apply fastforce
       apply (clarsimp simp: queue_end_valid_def fun_upd_apply split: if_splits)
      apply (intro prev_queue_head_heap_upd)
        apply (force simp: fun_upd_apply split: if_splits)
       apply (case_tac "ready_queues s d p";
              clarsimp simp: fun_upd_apply tcbQueueEmpty_def split: if_splits)
      apply (clarsimp simp: fun_upd_apply inQ_def split: if_splits)
      apply (case_tac "ready_queues s d p"; force simp: tcbQueueEmpty_def)
     apply (case_tac "t = tcbPtr")
      apply (clarsimp simp: inQ_def fun_upd_apply split: if_splits)
     apply (case_tac "t = the (tcbQueueEnd (ksReadyQueues s' (tcb_domain tcb, tcb_priority tcb)))")
      apply (clarsimp simp: inQ_def opt_pred_def fun_upd_apply)
     apply (clarsimp simp: inQ_def in_opt_pred opt_map_def fun_upd_apply)
    apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (clarsimp simp: fun_upd_apply split: if_splits)

  \<comment> \<open>d = tcb_domain tcb \<and> p = tcb_priority tcb\<close>
  apply clarsimp
  apply (drule_tac x="tcb_domain tcb" in spec)
  apply (drule_tac x="tcb_priority tcb" in spec)
  apply (cut_tac ts="ready_queues s (tcb_domain tcb) (tcb_priority tcb)"
              in tcbQueueHead_iff_tcbQueueEnd)
   apply (force simp: list_queue_relation_def)
  apply (frule valid_tcbs'_maxDomain[where t=tcbPtr], simp add: obj_at'_def)
  apply (frule valid_tcbs'_maxPriority[where t=tcbPtr], simp add: obj_at'_def)
  apply (drule valid_sched_pointersD[where t=tcbPtr])
    apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def)
   apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def)
  apply (intro conjI; clarsimp)

   \<comment> \<open>the ready queue was originally empty\<close>
   apply (force simp: inQ_def in_opt_pred fun_upd_apply opt_map_def obj_at'_def
                      queue_end_valid_def prev_queue_head_def
               split: if_splits option.splits)

   \<comment> \<open>the ready queue was not originally empty\<close>
  apply (drule (2) heap_ls_append[where new=tcbPtr])
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply queue_end_valid_def opt_map_def split: if_splits)
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply queue_end_valid_def)
  apply (rule conjI)
   apply (subst opt_map_upd_triv)
    apply (clarsimp simp: opt_map_def fun_upd_apply queue_end_valid_def split: if_splits)
   apply (clarsimp simp: prev_queue_head_def fun_upd_apply split: if_splits)
  by (clarsimp simp: inQ_def in_opt_pred fun_upd_apply queue_end_valid_def split: if_splits)

lemma tcbQueueAppend_valid_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> tcb_at' tcbPtr s \<and> (\<forall>end. tcbQueueEnd queue = Some end \<longrightarrow> tcb_at' end s)\<rbrace>
   tcbQueueAppend queue tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (clarsimp simp: tcbQueueEmpty_def valid_bound_tcb'_def split: option.splits)
  done

lemma tcbSchedAppend_valid_objs'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def setQueue_def)
  apply (wpsimp wp: threadSet_valid_objs' threadGet_wp hoare_vcg_all_lift)
  apply (normalise_obj_at', rename_tac tcb "end")
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply clarsimp
  apply (frule tcbQueueHead_iff_tcbQueueEnd)
  apply (force dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: tcbQueueEmpty_def obj_at'_def)
  done

crunch tcbSchedAppend, tcbSchedDequeue
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: threadSet_pred_tcb_no_state simp: unless_def tcb_to_itcb'_def)

(* FIXME move *)
lemmas obj_at'_conjI = obj_at_conj'

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for tcb_at'[wp]: "tcb_at' t"
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and ifunsafe'[wp]: if_unsafe_then_cap'
  (wp: crunch_wps simp: crunch_simps)

lemma tcbSchedAppend_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp wp: tcbQueueAppend_if_live_then_nonz_cap' threadGet_wp simp: bitmap_fun_defs)
  apply (frule_tac p=tcbPtr in if_live_then_nonz_capE')
   apply (fastforce simp: ko_wp_at'_def st_tcb_at'_def obj_at'_def runnable_eq_active' live'_def)
  apply (clarsimp simp: tcbQueueEmpty_def)
  apply (erule if_live_then_nonz_capE')
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce dest!: obj_at'_tcbQueueEnd_ksReadyQueues
                    simp: ko_wp_at'_def inQ_def obj_at'_def tcbQueueEmpty_def live'_def)
  done

lemma tcbSchedDequeue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and valid_objs' and sym_heap_sched_pointers\<rbrace>
   tcbSchedDequeue tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wpsimp wp: tcbQueueRemove_if_live_then_nonz_cap' threadGet_wp)
  apply (fastforce elim: if_live_then_nonz_capE' simp: obj_at'_def ko_wp_at'_def live'_def)
  done

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and tcb_at'[wp]: "tcb_at' t"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  and irq_states[wp]: valid_irq_states'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  and global_refs'[wp]: valid_global_refs'
  and ifunsafe'[wp]: if_unsafe_then_cap'
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and idle'[wp]: valid_idle'
  (simp: unless_def crunch_simps)

lemma tcbSchedEnqueue_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift tcbSchedEnqueue_ksMachine)
  done

lemma tcbSchedEnqueue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp
  apply (clarsimp simp: tcbSchedEnqueue_def)
  apply (wpsimp simp: unless_def)+
  done

lemma ct_idle_or_in_cur_domain'_lift2:
  "\<lbrakk> \<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace>         f \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksCurThread s) \<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s) \<rbrace>      f \<lbrace>\<lambda>_ s. P (ksIdleThread s) \<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s) \<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s) \<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace> ct_idle_or_in_cur_domain'\<rbrace> f \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (unfold ct_idle_or_in_cur_domain'_def)
  apply (rule hoare_lift_Pf2[where f=ksCurThread])
  apply (rule hoare_lift_Pf2[where f=ksSchedulerAction])
  including no_pre
  apply (wp hoare_weak_lift_imp hoare_vcg_disj_lift)
  apply simp+
  done

lemma threadSet_mdb':
  "\<lbrace>valid_mdb' and obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF (f t)) t\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (wpsimp wp: setObject_tcb_mdb' getTCB_wp simp: threadSet_def obj_at'_def)
  apply fastforce
  done

lemma tcbSchedNext_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbSchedPrev_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbQueueRemove_valid_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> valid_objs' s\<rbrace> tcbQueueRemove q tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getTCB_wp)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (fastforce simp: valid_tcb'_def obj_at'_def)
  done

lemma tcbQueuePrepend_valid_mdb':
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr
    and (\<lambda>s. \<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueHead queue)) s)\<rbrace>
   tcbQueuePrepend queue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')

lemma tcbQueueAppend_valid_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> tcb_at' tcbPtr s
        \<and> (\<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueEnd queue)) s)\<rbrace>
   tcbQueueAppend queue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueueAppend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')

lemma tcbQueued_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbQueued_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma valid_mdb'_ksReadyQueuesL1Bitmap_update[simp]:
  "valid_mdb' (ksReadyQueuesL1Bitmap_update f s) = valid_mdb' s"
  by (simp add: valid_mdb'_def)

lemma valid_mdb'_ksReadyQueuesL2Bitmap_update[simp]:
  "valid_mdb' (ksReadyQueuesL2Bitmap_update f s) = valid_mdb' s"
  by (simp add: valid_mdb'_def)

lemma tcbSchedEnqueue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def setQueue_def)
  apply (wpsimp wp: tcbQueuePrepend_valid_mdb' threadGet_wp simp: bitmap_fun_defs)
  apply normalise_obj_at'
  apply (fastforce dest!: obj_at'_tcbQueueHead_ksReadyQueues
                    simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def)
  done

crunch tcbSchedEnqueue
  for cur_tcb'[wp]: cur_tcb'
  (wp: threadSet_cur)

lemma tcbSchedEnqueue_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift tcbSchedEnqueue_ct_not_inQ
              simp: cteCaps_of_def o_def)
  done

crunch tcbSchedAppend
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  (simp: unless_def)

lemma tcbSchedAppend_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch tcbSchedAppend
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (simp: unless_def)

crunch tcbSchedAppend
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
(simp: unless_def)

crunch tcbSchedAppend
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
(simp: unless_def)

crunch tcbSchedAppend
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
(simp: unless_def)

lemma tcbQueueAppend_tcbPriority_obj_at'[wp]:
  "tcbQueueAppend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def objBits_simps ps_clear_def split: if_splits)

lemma tcbQueueAppend_tcbDomain_obj_at'[wp]:
  "tcbQueueAppend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def objBits_simps ps_clear_def split: if_splits)

lemma tcbSchedAppend_tcbDomain[wp]:
  "tcbSchedAppend t \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  by wpsimp

lemma tcbSchedAppend_tcbPriority[wp]:
  "tcbSchedAppend t \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  by wpsimp

lemma tcbSchedAppend_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

crunch tcbSchedAppend
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (simp: unless_def)

crunch tcbSchedAppend, tcbSchedDequeue
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (simp: unless_def)

crunch tcbSchedDequeue, tcbSchedAppend
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"

lemma tcbSchedAppend_sch_act_wf[wp]:
  "tcbSchedAppend thread \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wpsimp wp: sch_act_wf_lift)

lemma tcbSchedAppend_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmaps\<rbrace> tcbSchedAppend tcbPtr \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  supply if_split[split del]
  unfolding tcbSchedAppend_def
  apply (wpsimp simp: tcbQueueAppend_def
                  wp: setQueue_valid_bitmapQ' addToBitmap_valid_bitmapQ_except addToBitmap_bitmapQ
                      threadGet_wp hoare_vcg_if_lift2)
  apply (clarsimp simp: ksReadyQueues_asrt_def split: if_splits)
  apply normalise_obj_at'
  apply (force dest: tcbQueueHead_iff_tcbQueueEnd
               simp: valid_bitmaps_def valid_bitmapQ_def tcbQueueEmpty_def)
  done

lemma tcbSchedAppend_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_tcbs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def setQueue_def)
  apply (wpsimp wp: tcbQueueAppend_valid_mdb' threadGet_wp simp: bitmap_fun_defs)
  apply (fastforce dest: obj_at'_tcbQueueEnd_ksReadyQueues
                   simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def)
  done

lemma tcbSchedAppend_valid_bitmaps[wp]:
  "tcbSchedAppend tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  unfolding valid_bitmaps_def
  apply wpsimp
  apply (clarsimp simp: valid_bitmaps_def)
  done

lemma tcbSchedAppend_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift tcbSchedAppend_ct_not_inQ
                    ct_idle_or_in_cur_domain'_lift2 cur_tcb_lift
              simp: cteCaps_of_def o_def)
  done

lemma tcbSchedAppend_all_invs_but_ct_not_inQ':
  "\<lbrace>invs'\<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>_. all_invs_but_ct_not_inQ'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift tcbSchedAppend_ct_not_inQ
                    ct_idle_or_in_cur_domain'_lift2 cur_tcb_lift
              simp: cteCaps_of_def o_def)
  done

lemma tcbSchedEnqueue_invs'_not_ResumeCurrentThread:
  "\<lbrace>invs'
    and st_tcb_at' runnable' t
    and (\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread)\<rbrace>
     tcbSchedEnqueue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by wpsimp

lemma tcbSchedAppend_invs'_not_ResumeCurrentThread:
  "\<lbrace>invs'
    and st_tcb_at' runnable' t
    and (\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread)\<rbrace>
     tcbSchedAppend t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by wpsimp

lemma tcb_at'_has_tcbDomain:
 "tcb_at' t s \<Longrightarrow> \<exists>p. obj_at' (\<lambda>tcb. tcbDomain tcb = p) t s"
 by (clarsimp simp add: obj_at'_def)

crunch tcbSchedDequeue
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  (simp: unless_def)

lemma tcbSchedDequeue_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch tcbSchedDequeue
  for pspace_domain_valid[wp]: "pspace_domain_valid"

crunch tcbSchedDequeue
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
(simp: unless_def)

crunch tcbSchedDequeue
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
(simp: unless_def)

crunch tcbSchedDequeue
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
(simp: unless_def)

lemma tcbSchedDequeue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp
  apply (clarsimp simp: tcbSchedDequeue_def tcbQueueRemove_def)
  apply (wpsimp wp: hoare_when_weak_wp getObject_tcb_wp threadGet_wp)
  done

crunch tcbSchedDequeue
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (simp: unless_def)

lemma tcbSchedDequeue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_objs'\<rbrace> tcbSchedDequeue tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp simp: bitmap_fun_defs setQueue_def wp: threadSet_mdb' tcbQueueRemove_valid_mdb')
      apply (rule_tac Q'="\<lambda>_. tcb_at' tcbPtr" in hoare_post_imp)
       apply (fastforce simp: tcb_cte_cases_def cteSizeBits_def)
      apply (wpsimp wp: threadGet_wp)+
  apply (fastforce simp: obj_at'_def)
  done

lemma tcbSchedDequeue_invs'[wp]:
  "tcbSchedDequeue t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift ct_idle_or_in_cur_domain'_lift2 cur_tcb_lift
              simp: cteCaps_of_def o_def)
  done

lemma ready_qs_runnable_cross:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_queues s\<rbrakk>
   \<Longrightarrow> ready_qs_runnable s'"
  apply (clarsimp simp: ready_qs_runnable_def)
  apply normalise_obj_at'
  apply (frule state_relation_ready_queues_relation)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply (clarsimp simp: valid_queues_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec)
   apply (fastforce simp: inQ_def in_opt_pred obj_at'_def opt_map_red)
  apply (fastforce dest: st_tcb_at_runnable_cross simp: obj_at'_def st_tcb_at'_def)
  done

method add_ready_qs_runnable =
  rule_tac Q'=ready_qs_runnable in corres_cross_add_guard,
  (clarsimp simp: pred_conj_def)?,
  (frule valid_sched_valid_queues)?, (frule invs_psp_aligned)?, (frule invs_distinct)?,
  fastforce dest: ready_qs_runnable_cross

defs idleThreadNotQueued_def:
  "idleThreadNotQueued s \<equiv> obj_at' (Not \<circ> tcbQueued) (ksIdleThread s) s"

lemma idle_thread_not_queued:
  "\<lbrakk>valid_idle s; valid_queues s\<rbrakk>
   \<Longrightarrow> \<not> (\<exists>d p. idle_thread s \<in> set (ready_queues s d p))"
  apply (clarsimp simp: valid_queues_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule_tac x="idle_thread s" in bspec)
   apply fastforce
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma valid_idle_tcb_at:
  "valid_idle s \<Longrightarrow> tcb_at (idle_thread s) s"
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_tcb_def)

lemma setCurThread_corres:
  "corres dc (valid_idle and valid_queues and pspace_aligned and pspace_distinct) \<top>
     (modify (cur_thread_update (\<lambda>_. t))) (setCurThread t)"
  apply (clarsimp simp: setCurThread_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: idleThreadNotQueued_def)
   apply (frule (1) idle_thread_not_queued)
   apply (frule state_relation_pspace_relation)
   apply (frule state_relation_ready_queues_relation)
   apply (frule state_relation_idle_thread)
   apply (frule valid_idle_tcb_at)
   apply (frule (3) tcb_at_cross)
   apply (fastforce dest!: in_ready_q_tcbQueued_eq[THEN arg_cong_Not, THEN iffD1]
                     simp: obj_at'_def opt_pred_def opt_map_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma arch_switch_thread_tcb_at' [wp]: "\<lbrace>tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (unfold RISCV64_H.switchToThread_def, wp typ_at_lift_tcb')

crunch "switchToThread"
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

crunch setVMRoot
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t'"
  (simp: crunch_simps wp: crunch_wps)

lemma Arch_switchToThread_pred_tcb'[wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. Arch.switchToThread t \<lbrace>pred_tcb_at' proj P t'\<rbrace>"
    by (wpsimp wp: setVMRoot_obj_at simp: RISCV64_H.switchToThread_def)
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_RISCV64_H_switchToThread_typ_at' pos])
qed

crunch storeWordUser, setVMRoot, asUser, storeWordUser, Arch.switchToThread
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_objs'[wp]: valid_objs'
  (wp: crunch_wps threadSet_sched_pointers simp: crunch_simps)

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and ready_qs_distinct[wp]: ready_qs_distinct
  and valid_idle[wp]: valid_idle
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  (wp: ready_qs_distinct_lift)

lemma valid_queues_in_correct_ready_q[elim!]:
  "valid_queues s \<Longrightarrow> in_correct_ready_q s"
  by (clarsimp simp: valid_queues_def in_correct_ready_q_def)

lemma valid_queues_ready_qs_distinct[elim!]:
  "valid_queues s \<Longrightarrow> ready_qs_distinct s"
  by (clarsimp simp: valid_queues_def ready_qs_distinct_def)

lemma switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs
                and st_tcb_at runnable t and valid_queues and valid_idle)
             (no_0_obj' and sym_heap_sched_pointers and valid_objs')
             (switch_to_thread t) (switchToThread t)"
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  apply add_ready_qs_runnable
  apply (simp add: switch_to_thread_def Thread_H.switchToThread_def)
  apply (rule corres_symb_exec_l[OF _ _ get_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_l[OF _ _ assert_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
    apply (rule corres_stateAssert_ignore)
     apply (fastforce dest!: state_relation_ready_queues_relation intro: ksReadyQueues_asrt_cross)
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply fastforce
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF arch_switchToThread_corres])
        apply (rule corres_split[OF tcbSchedDequeue_corres setCurThread_corres])
          apply (wpsimp simp: is_tcb_def wp: in_correct_ready_q_lift)+
     apply (fastforce intro!: st_tcb_at_tcb_at)
    apply wpsimp
   apply wpsimp
   apply (fastforce dest!: st_tcb_at_tcb_at simp: tcb_at_def)
  apply wpsimp
  apply (fastforce dest!: st_tcb_at_tcb_at simp: tcb_at_def)
  done

lemma arch_switchToIdleThread_corres:
  "corres dc
        (valid_arch_state and valid_objs and pspace_aligned and pspace_distinct
           and valid_vspace_objs and valid_idle)
        (no_0_obj')
        arch_switch_to_idle_thread Arch.switchToIdleThread"
  apply (simp add: arch_switch_to_idle_thread_def
                RISCV64_H.switchToIdleThread_def)
  apply (corresKsimp corres: getIdleThread_corres setVMRoot_corres)
  apply (clarsimp simp: valid_idle_def valid_idle'_def pred_tcb_at_def obj_at_def is_tcb
                        valid_arch_state_asid_table valid_arch_state_global_arch_objs)
  done

lemma switchToIdleThread_corres:
  "corres dc
     (invs and valid_queues)
     invs_no_cicd'
     switch_to_idle_thread switchToIdleThread"
  apply (simp add: switch_to_idle_thread_def Thread_H.switchToIdleThread_def)
  apply add_ready_qs_runnable
  apply (rule corres_stateAssert_ignore, fastforce)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getIdleThread_corres])
      apply (rule corres_split[OF arch_switchToIdleThread_corres])
        apply clarsimp
        apply (rule setCurThread_corres)
       apply wpsimp
      apply (simp add: state_relation_def cdt_relation_def)
      apply wpsimp+
   apply (simp add: invs_unique_refs invs_valid_vs_lookup invs_valid_objs invs_valid_asid_map
                    invs_arch_state invs_valid_global_objs invs_psp_aligned invs_distinct
                    invs_valid_idle invs_vspace_objs)
  apply (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_pspace'_def)
  done

lemma gq_sp: "\<lbrace>P\<rbrace> getQueue d p \<lbrace>\<lambda>rv. P and (\<lambda>s. ksReadyQueues s (d, p) = rv)\<rbrace>"
  by (unfold getQueue_def, rule gets_sp)

lemma sch_act_wf:
  "sch_act_wf sa s = ((\<forall>t. sa = SwitchToThread t \<longrightarrow> st_tcb_at' runnable' t s \<and>
                                                    tcb_in_cur_domain' t s) \<and>
                      (sa = ResumeCurrentThread \<longrightarrow> ct_in_state' activatable' s))"
  by (case_tac sa,  simp_all add: )

declare gq_wp[wp]
declare setQueue_obj_at[wp]

lemma threadSet_timeslice_invs:
  "\<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbTimeSlice_update b) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wp threadSet_invs_trivial, simp_all add: inQ_def cong: conj_cong)

lemma setCurThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd' and st_tcb_at' activatable' t and obj_at' (\<lambda>x. \<not> tcbQueued x) t and tcb_in_cur_domain' t\<rbrace>
     setCurThread t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have ct_not_inQ_ct: "\<And>s t . \<lbrakk> ct_not_inQ s; obj_at' (\<lambda>x. \<not> tcbQueued x) t s\<rbrakk> \<Longrightarrow> ct_not_inQ (s\<lparr> ksCurThread := t \<rparr>)"
    apply (simp add: ct_not_inQ_def o_def)
    done
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (clarsimp simp add: all_invs_but_ct_idle_or_in_cur_domain'_def invs'_def cur_tcb'_def
                              valid_state'_def sch_act_wf ct_in_state'_def state_refs_of'_def
                              ps_clear_def valid_irq_node'_def ct_not_inQ_ct
                              ct_idle_or_in_cur_domain'_def bitmapQ_defs valid_bitmaps_def
                        cong: option.case_cong)
    done
qed

(* Don't use this rule when considering the idle thread. The invariant ct_idle_or_in_cur_domain'
   says that either "tcb_in_cur_domain' t" or "t = ksIdleThread s".
   Use setCurThread_invs_idle_thread instead. *)
lemma setCurThread_invs:
  "\<lbrace>invs' and st_tcb_at' activatable' t and obj_at' (\<lambda>x. \<not> tcbQueued x) t and
    tcb_in_cur_domain' t\<rbrace> setCurThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (rule hoare_pre, rule setCurThread_invs_no_cicd')
     (simp add: invs'_to_invs_no_cicd'_def)

lemma setCurThread_invs_no_cicd'_idle_thread:
  "\<lbrace>invs_no_cicd' and (\<lambda>s. t = ksIdleThread s) \<rbrace> setCurThread t \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def invs'_def cur_tcb'_def
                        valid_state'_def valid_idle'_def
                        sch_act_wf ct_in_state'_def state_refs_of'_def
                        ps_clear_def valid_irq_node'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                        valid_queues_def bitmapQ_defs valid_bitmaps_def pred_tcb_at'_def
                  cong: option.case_cong)
  apply (clarsimp simp: idle_tcb'_def ct_not_inQ_def ps_clear_def obj_at'_def st_tcb_at'_def
                        idleThreadNotQueued_def)
  done

lemma setCurThread_invs_idle_thread:
  "\<lbrace>invs' and (\<lambda>s. t = ksIdleThread s) \<rbrace> setCurThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (rule hoare_pre, rule setCurThread_invs_no_cicd'_idle_thread)
     (clarsimp simp: invs'_to_invs_no_cicd'_def all_invs_but_ct_idle_or_in_cur_domain'_def)

lemma Arch_switchToThread_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: RISCV64_H.switchToThread_def)
  apply (wp; auto)
  done

crunch "Arch.switchToThread"
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (simp: crunch_simps wp: crunch_wps)

lemma Arch_swichToThread_tcbDomain_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>"
  apply (clarsimp simp: RISCV64_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_swichToThread_tcbPriority_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>"
  apply (clarsimp simp: RISCV64_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_switchToThread_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

lemma tcbSchedDequeue_not_tcbQueued:
  "\<lbrace>\<top>\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. obj_at' (\<lambda>x. \<not> tcbQueued x) t\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp|clarsimp)+
  apply (rule_tac Q'="\<lambda>queued. obj_at' (\<lambda>x. tcbQueued x = queued) t" in hoare_post_imp)
     apply (clarsimp simp: obj_at'_def)
    apply (wpsimp wp: threadGet_wp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma asUser_tcbState_inv[wp]:
  "asUser t m \<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace>"
  apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
  apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | wpc | simp | clarsimp simp: obj_at'_def)+
  done

lemma Arch_switchToThread_obj_at[wp]:
  "Arch.switchToThread t \<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace>"
  by (wpsimp simp: RISCV64_H.switchToThread_def)

declare doMachineOp_obj_at[wp]

crunch asUser
  for valid_arch_state'[wp]: "valid_arch_state'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_irq_states'[wp]: "valid_irq_states'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_machine_state'[wp]: "valid_machine_state'"
(wp: crunch_wps simp: crunch_simps)

lemma asUser_valid_irq_node'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (rule_tac valid_irq_node_lift)
   apply (simp add: asUser_def)
   apply (wpsimp wp: crunch_wps)+
  done

crunch asUser
  for irq_masked'_helper: "\<lambda>s. P (intStateIRQTable (ksInterruptState s))"
(wp: crunch_wps simp: crunch_simps)

lemma asUser_irq_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ . irqs_masked'\<rbrace>"
  apply (rule irqs_masked_lift)
  apply (rule asUser_irq_masked'_helper)
  done

lemma asUser_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ . ct_not_inQ\<rbrace>"
  apply (clarsimp simp: submonad_asUser.fn_is_sm submonad_fn_def)
  apply (rule bind_wp)+
     prefer 4
     apply (rule stateAssert_sp)
    prefer 3
    apply (rule gets_inv)
   defer
   apply (rule select_f_inv)
  apply (case_tac rv; simp)
  apply (clarsimp simp: asUser_replace_def obj_at'_def fun_upd_def
                  split: option.split kernel_object.split)
  apply wp
  apply (clarsimp simp: ct_not_inQ_def obj_at'_def objBitsKO_def ps_clear_def dom_def)
  apply (rule conjI; clarsimp; blast)
  done

crunch asUser
  for pspace_domain_valid[wp]: "pspace_domain_valid"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_dom_schedule'[wp]: "valid_dom_schedule'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: unless_def)

crunch asUser
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: unless_def)

lemmas asUser_cteCaps_of[wp] = cteCaps_of_ctes_of_lift[OF asUser_ctes_of]

lemma asUser_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> asUser f t \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (rule hoare_pre, wp untyped_ranges_zero_lift)
  apply (simp add: o_def)
  done

lemma threadSet_invs_no_cicd'_trivialT:
  assumes
    "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
    "\<forall>tcb. tcbState (F tcb) = tcbState tcb \<and> tcbDomain (F tcb) = tcbDomain tcb"
    "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
    "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
    "\<forall>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb"
    "\<forall>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb"
    "\<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb"
    "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
    "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
    "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  shows
  "threadSet F t \<lbrace>invs_no_cicd'\<rbrace>"
  apply (simp add: invs_no_cicd'_def valid_state'_def)
  apply (wp threadSet_valid_pspace'T
            threadSet_sch_actT_P[where P=False, simplified]
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
            threadSet_valid_dom_schedule' threadSet_sched_pointers threadSet_valid_sched_pointers
            threadSet_cur
            untyped_ranges_zero_lift
         | clarsimp simp: assms cteCaps_of_def | rule refl)+
  by (auto simp: o_def)

lemmas threadSet_invs_no_cicd'_trivial =
    threadSet_invs_no_cicd'_trivialT [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma asUser_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> asUser t m \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  apply (wp threadSet_invs_no_cicd'_trivial hoare_drop_imps | simp)+
  done

lemma Arch_switchToThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: RISCV64_H.switchToThread_def)
  apply (wp setVMRoot_invs_no_cicd')
  done

lemma tcbSchedDequeue_invs_no_cicd'[wp]:
  "tcbSchedDequeue t \<lbrace>invs_no_cicd'\<rbrace>"
  unfolding all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_pspace'_def
  apply (wp tcbSchedDequeue_ct_not_inQ sch_act_wf_lift valid_irq_node_lift irqs_masked_lift
            valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
            untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma switchToThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd' and tcb_in_cur_domain' t \<rbrace> ThreadDecls_H.switchToThread t \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: Thread_H.switchToThread_def)
  apply (wp setCurThread_invs_no_cicd' tcbSchedDequeue_not_tcbQueued
            Arch_switchToThread_invs_no_cicd' Arch_switchToThread_pred_tcb')
  apply (auto elim!: pred_tcb'_weakenE)
  done

lemma switchToThread_invs[wp]:
  "\<lbrace>invs' and tcb_in_cur_domain' t \<rbrace> switchToThread t \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: Thread_H.switchToThread_def )
  apply (wp threadSet_timeslice_invs setCurThread_invs
             Arch_switchToThread_invs dmo_invs'
             doMachineOp_obj_at tcbSchedDequeue_not_tcbQueued)
  by (auto elim!: pred_tcb'_weakenE)

lemma setCurThread_ct_in_state:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace> setCurThread t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
proof -
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (simp add: ct_in_state'_def pred_tcb_at'_def o_def)
    done
qed

lemma switchToThread_ct_in_state[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace> switchToThread t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
proof -
  show ?thesis
    apply (simp add: Thread_H.switchToThread_def tcbSchedEnqueue_def unless_def)
    apply (wp setCurThread_ct_in_state Arch_switchToThread_obj_at
         | simp add: o_def cong: if_cong)+
    done
qed

lemma setCurThread_obj_at[wp]:
  "\<lbrace>obj_at' P addr\<rbrace> setCurThread t \<lbrace>\<lambda>rv. obj_at' P addr\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply (fastforce intro: obj_at'_pspaceI)
  done

lemma dmo_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace>
     doMachineOp m
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma sct_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setCurThread t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: setCurThread_def)
  apply (wpsimp wp: ex_nonz_cap_to_pres')
  done


crunch "Arch.switchToThread"
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps wp: crunch_wps)

crunch switchToThread
  for cap_to'[wp]: "ex_nonz_cap_to' p"
  (simp: crunch_simps)

lemma no_longer_inQ[simp]:
  "\<not> inQ d p (tcbQueued_update (\<lambda>x. False) tcb)"
  by (simp add: inQ_def)

lemma iflive_inQ_nonz_cap_strg:
  "if_live_then_nonz_cap' s \<and> obj_at' (inQ d prio) t s
          \<longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: obj_at'_real_def inQ_def live'_def
              elim!: if_live_then_nonz_capE' ko_wp_at'_weakenE)

lemmas iflive_inQ_nonz_cap[elim]
    = mp [OF iflive_inQ_nonz_cap_strg, OF conjI[rotated]]

declare Cons_eq_tails[simp]

crunch "ThreadDecls_H.switchToThread"
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

(* FIXME move *)
lemma obj_tcb_at':
  "obj_at' (\<lambda>tcb::tcb. P tcb) t s \<Longrightarrow> tcb_at' t s"
  by (clarsimp simp: obj_at'_def)

lemma setThreadState_rct:
  "\<lbrace>\<lambda>s. (runnable' st \<or> ksCurThread s \<noteq> t)
        \<and> ksSchedulerAction s = ResumeCurrentThread\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (rule hoare_pre_disj')
   apply (rule bind_wp [OF _
                 hoare_vcg_conj_lift
                   [OF threadSet_tcbState_st_tcb_at' [where P=runnable']
                       threadSet_nosch]])
   apply (rule bind_wp [OF _
                 hoare_vcg_conj_lift [OF isRunnable_const isRunnable_inv]])
   apply (clarsimp simp: when_def)
   apply (case_tac rv)
    apply (clarsimp, wp)[1]
   apply (clarsimp)
  apply (rule bind_wp [OF _
                hoare_vcg_conj_lift
                  [OF threadSet_ct threadSet_nosch]])
  apply (rule bind_wp [OF _ isRunnable_inv])
  apply (rule bind_wp [OF _
                hoare_vcg_conj_lift
                  [OF gct_wp gct_wp]])
  apply (rename_tac ct)
  apply (case_tac "ct\<noteq>t")
   apply (clarsimp simp: when_def)
   apply (wp)[1]
  apply (clarsimp)
  done

lemma bitmapQ_lookupBitmapPriority_simp: (* neater unfold, actual unfold is really ugly *)
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ;
     valid_bitmapQ s ; bitmapQ_no_L1_orphans s \<rbrakk> \<Longrightarrow>
   bitmapQ d (lookupBitmapPriority d s) s =
    (ksReadyQueuesL1Bitmap s d !! word_log2 (ksReadyQueuesL1Bitmap s d) \<and>
     ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d))) !!
       word_log2 (ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d)))))"
  unfolding bitmapQ_def lookupBitmapPriority_def
  apply (drule word_log2_nth_same, clarsimp)
  apply (drule (1) bitmapQ_no_L1_orphansD, clarsimp)
  apply (drule word_log2_nth_same, clarsimp)
  apply (frule test_bit_size[where n="word_log2 (ksReadyQueuesL2Bitmap _ _)"])
  apply (clarsimp simp: numPriorities_def wordBits_def word_size)
  apply (subst prioToL1Index_l1IndexToPrio_or_id)
    apply (subst unat_of_nat_eq)
    apply (fastforce intro: unat_less_helper word_log2_max[THEN order_less_le_trans]
                      simp: wordRadix_def word_size l2BitmapSize_def')+
  apply (subst prioToL1Index_l1IndexToPrio_or_id)
    apply (fastforce intro: unat_less_helper word_log2_max of_nat_mono_maybe
                      simp: wordRadix_def word_size l2BitmapSize_def')+
  apply (simp add: word_ao_dist)
  apply (subst less_mask_eq)
   apply (rule word_of_nat_less)
    apply (fastforce intro: word_of_nat_less simp: wordRadix_def' unat_of_nat word_size)+
  done

lemma bitmapQ_from_bitmap_lookup:
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ;
     valid_bitmapQ s ; bitmapQ_no_L1_orphans s
     \<rbrakk>
   \<Longrightarrow> bitmapQ d (lookupBitmapPriority d s) s"
  apply (simp add: bitmapQ_lookupBitmapPriority_simp)
  apply (drule word_log2_nth_same)
  apply (drule (1) bitmapQ_no_L1_orphansD)
  apply (fastforce dest!: word_log2_nth_same
                   simp: word_ao_dist lookupBitmapPriority_def word_size numPriorities_def
                         wordBits_def)
  done

lemma lookupBitmapPriority_obj_at':
  "\<lbrakk>ksReadyQueuesL1Bitmap s d \<noteq> 0; valid_bitmapQ s; bitmapQ_no_L1_orphans s;
    ksReadyQueues_asrt s; ready_qs_runnable s; pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> obj_at' (inQ d (lookupBitmapPriority d s) and runnable' \<circ> tcbState)
               (the (tcbQueueHead (ksReadyQueues s (d, lookupBitmapPriority d s)))) s"
  apply (drule (2) bitmapQ_from_bitmap_lookup)
  apply (simp add: valid_bitmapQ_bitmapQ_simp)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def tcbQueueEmpty_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x="lookupBitmapPriority d s" in spec)
  apply clarsimp
  apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
  apply (fastforce simp: obj_at'_and ready_qs_runnable_def obj_at'_def st_tcb_at'_def inQ_def
                         tcbQueueEmpty_def)
  done

lemma bitmapL1_zero_ksReadyQueues:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s \<rbrakk>
   \<Longrightarrow> (ksReadyQueuesL1Bitmap s d = 0) = (\<forall>p. tcbQueueEmpty (ksReadyQueues s (d, p)))"
  apply (cases "ksReadyQueuesL1Bitmap s d = 0")
   apply (force simp add: bitmapQ_def valid_bitmapQ_def)
  apply (fastforce dest: bitmapQ_from_bitmap_lookup simp: valid_bitmapQ_bitmapQ_simp)
  done

lemma prioToL1Index_le_mask:
  "\<lbrakk> prioToL1Index p = prioToL1Index p' ; p && mask wordRadix \<le> p' && mask wordRadix \<rbrakk>
   \<Longrightarrow> p \<le> p'"
  unfolding prioToL1Index_def
  apply (simp add: wordRadix_def word_le_nat_alt[symmetric])
  apply (drule shiftr_eq_neg_mask_eq)
  apply (metis add.commute word_and_le2 word_plus_and_or_coroll2 word_plus_mono_left)
  done

lemma prioToL1Index_le_index:
  "\<lbrakk> prioToL1Index p \<le> prioToL1Index p' ; prioToL1Index p \<noteq> prioToL1Index p' \<rbrakk>
   \<Longrightarrow> p \<le> p'"
  unfolding prioToL1Index_def
  apply (simp add: wordRadix_def word_le_nat_alt[symmetric])
  apply (erule (1) le_shiftr')
  done

lemma bitmapL1_highest_lookup:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s ;
     bitmapQ d p' s \<rbrakk>
   \<Longrightarrow> p' \<le> lookupBitmapPriority d s"
  apply (subgoal_tac "ksReadyQueuesL1Bitmap s d \<noteq> 0")
   prefer 2
   apply (clarsimp simp add: bitmapQ_def)
  apply (case_tac "prioToL1Index (lookupBitmapPriority d s) = prioToL1Index p'")
   apply (rule prioToL1Index_le_mask, simp)
   apply (frule (2) bitmapQ_from_bitmap_lookup)
   apply (clarsimp simp: bitmapQ_lookupBitmapPriority_simp)
   apply (clarsimp simp: bitmapQ_def lookupBitmapPriority_def)
   apply (subst mask_or_not_mask[where n=wordRadix and x=p', symmetric])
   apply (subst word_bw_comms(2)) (* || commute *)
   apply (simp add: word_ao_dist mask_AND_NOT_mask mask_twice)
   apply (subst less_mask_eq[where x="of_nat _"])
    apply (subst word_less_nat_alt)
    apply (subst unat_of_nat_eq)
     apply (rule order_less_le_trans[OF word_log2_max])
     apply (simp add: word_size)
    apply (rule order_less_le_trans[OF word_log2_max])
    apply (simp add: word_size wordRadix_def')
   apply (subst word_le_nat_alt)
   apply (subst unat_of_nat_eq)
    apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size)
   apply (rule word_log2_highest)
   apply (subst (asm) prioToL1Index_l1IndexToPrio_or_id)
     apply (subst unat_of_nat_eq)
      apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size)
     apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size wordRadix_def')
    apply (simp add: word_size wordRadix_def')
    apply (drule (1) bitmapQ_no_L1_orphansD[where d=d and i="word_log2 _"])
    apply (simp add: l2BitmapSize_def')
   apply simp
  apply (rule prioToL1Index_le_index[rotated], simp)
  apply (frule (2) bitmapQ_from_bitmap_lookup)
  apply (clarsimp simp: bitmapQ_lookupBitmapPriority_simp)
  apply (clarsimp simp: bitmapQ_def lookupBitmapPriority_def)
  apply (subst prioToL1Index_l1IndexToPrio_or_id)
    apply (subst unat_of_nat_eq)
     apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size)
    apply (rule order_less_le_trans[OF word_log2_max], simp add: word_size wordRadix_def')
   apply (fastforce dest: bitmapQ_no_L1_orphansD
                    simp: wordBits_def numPriorities_def word_size wordRadix_def' l2BitmapSize_def')
  apply (erule word_log2_highest)
  done

lemma bitmapQ_ksReadyQueuesI:
  "\<lbrakk> bitmapQ d p s ; valid_bitmapQ s \<rbrakk> \<Longrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (d, p))"
  unfolding valid_bitmapQ_def by simp

lemma getReadyQueuesL2Bitmap_inv[wp]:
  "\<lbrace> P \<rbrace> getReadyQueuesL2Bitmap d i \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding getReadyQueuesL2Bitmap_def by wp

lemma switchToThread_lookupBitmapPriority_wp:
  "\<lbrace>\<lambda>s. invs_no_cicd' s \<and> bitmapQ (ksCurDomain s) (lookupBitmapPriority (ksCurDomain s) s) s \<and>
        t = the (tcbQueueHead (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)))\<rbrace>
   ThreadDecls_H.switchToThread t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def)
  apply (wp setCurThread_invs_no_cicd' tcbSchedDequeue_not_tcbQueued
            Arch_switchToThread_invs_no_cicd')
  apply (auto elim!: pred_tcb'_weakenE)
  apply (prop_tac "valid_bitmapQ s")
   apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_bitmaps_def)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def valid_bitmapQ_bitmapQ_simp)
  apply (drule_tac x="ksCurDomain s" in spec)
  apply (drule_tac x="lookupBitmapPriority (ksCurDomain s) s" in spec)
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def)
  apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
  apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def tcbQueueEmpty_def inQ_def)
  done

lemma switchToIdleThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (clarsimp simp: Thread_H.switchToIdleThread_def RISCV64_H.switchToIdleThread_def)
  apply (wp setCurThread_invs_no_cicd'_idle_thread setVMRoot_invs_no_cicd')
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_idle'_def)
  done

crunch "Arch.switchToIdleThread"
  for obj_at'[wp]: "\<lambda>s. obj_at' P t s"


declare hoare_weak_lift_imp_conj[wp_split del]

lemma setCurThread_const:
  "\<lbrace>\<lambda>_. P t \<rbrace> setCurThread t \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>"
  by (simp add: setCurThread_def | wp)+



crunch switchToIdleThread
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch switchToThread
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"

lemma switchToIdleThread_curr_is_idle:
  "\<lbrace>\<top>\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv s. ksCurThread s = ksIdleThread s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (wps switchToIdleThread_it)
   apply (simp add: Thread_H.switchToIdleThread_def)
   apply (wp setCurThread_const)
  apply (simp)
 done

lemma chooseThread_it[wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> chooseThread \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  supply if_split[split del]
  by (wpsimp simp: chooseThread_def curDomain_def bitmap_fun_defs)

lemma threadGet_inv [wp]: "\<lbrace>P\<rbrace> threadGet f t \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: threadGet_def)
  apply (wp | simp)+
  done

lemma corres_split_sched_act:
  "\<lbrakk>sched_act_relation act act';
    corres r P P' f1 g1;
    \<And>t. corres r (Q t) (Q' t) (f2 t) (g2 t);
    corres r R R' f3 g3\<rbrakk>
    \<Longrightarrow> corres r (case act of resume_cur_thread \<Rightarrow> P
                           | switch_thread t \<Rightarrow> Q t
                           | choose_new_thread \<Rightarrow> R)
               (case act' of ResumeCurrentThread \<Rightarrow> P'
                           | SwitchToThread t \<Rightarrow> Q' t
                           | ChooseThread \<Rightarrow> R')
       (case act of resume_cur_thread \<Rightarrow> f1
                  | switch_thread t \<Rightarrow> f2 t
                  | choose_new_thread \<Rightarrow> f3)
       (case act' of ResumeCurrentThread \<Rightarrow> g1
                   | ChooseNewThread \<Rightarrow> g3
                   | SwitchToThread t \<Rightarrow> g2 t)"
  apply (cases act)
    apply (rule corres_guard_imp, force+)+
    done

lemma corres_assert_ret:
  "corres dc (\<lambda>s. P) \<top> (assert P) (return ())"
  apply (rule corres_no_failI)
   apply simp
  apply (simp add: assert_def return_def fail_def)
  done

lemma corres_assert_assume_r:
  "corres dc P Q f (g ())
  \<Longrightarrow> corres dc P (Q and (\<lambda>s. Q')) f (assert Q' >>= g)"
  by (force simp: corres_underlying_def assert_def return_def bind_def fail_def)

crunch tcbSchedEnqueue
  for cur[wp]: cur_tcb'
  (simp: unless_def)

lemma thread_get_exs_valid[wp]:
  "tcb_at t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> thread_get f t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_thread_state_def  assert_opt_def fail_def
             thread_get_def gets_the_def exs_valid_def gets_def
             get_def bind_def return_def split: option.splits)
  apply (erule get_tcb_at)
  done

lemma gts_exs_valid[wp]:
  "tcb_at t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_thread_state t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_thread_state_def  assert_opt_def fail_def
             thread_get_def gets_the_def exs_valid_def gets_def
             get_def bind_def return_def split: option.splits)
  apply (erule get_tcb_at)
  done

lemma guarded_switch_to_corres:
  "corres dc (valid_arch_state and valid_objs
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs
                and st_tcb_at runnable t and valid_queues and valid_idle)
             (no_0_obj' and sym_heap_sched_pointers and valid_objs')
             (guarded_switch_to t) (switchToThread t)"
  apply (simp add: guarded_switch_to_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l'[OF _ gts_exs_valid])
      apply (rule corres_assert_assume_l)
      apply (rule switchToThread_corres)
     apply (force simp: st_tcb_at_tcb_at)
    apply (wp gts_st_tcb_at)
   apply (force simp: st_tcb_at_tcb_at)+
  done

abbreviation "enumPrio \<equiv> [0.e.maxPriority]"

lemma enumPrio_word_div:
  fixes v :: "8 word"
  assumes vlt: "unat v \<le> unat maxPriority"
  shows "\<exists>xs ys. enumPrio = xs @ [v] @ ys \<and> (\<forall>x\<in>set xs. x < v) \<and> (\<forall>y\<in>set ys. v < y)"
  apply (subst upto_enum_word)
  apply (subst upt_add_eq_append'[where j="unat v"])
    apply simp
   apply (rule le_SucI)
   apply (rule vlt)
  apply (simp only: upt_conv_Cons vlt[simplified less_Suc_eq_le[symmetric]])
  apply (intro exI conjI)
    apply fastforce
   apply clarsimp
   apply (drule of_nat_mono_maybe[rotated, where 'a="8"])
    apply (fastforce simp: vlt)
   apply simp
  apply (clarsimp simp: Suc_le_eq)
  apply (erule disjE)
   apply (drule of_nat_mono_maybe[rotated, where 'a="8"])
    apply (simp add: maxPriority_def numPriorities_def)
   apply (clarsimp simp: unat_of_nat_eq)
  apply (erule conjE)
  apply (drule_tac y="unat v" and x="x" in of_nat_mono_maybe[rotated, where 'a="8"])
   apply (simp add: maxPriority_def numPriorities_def)+
  done

lemma curDomain_corres: "corres (=) \<top> \<top> (gets cur_domain) (curDomain)"
  by (simp add: curDomain_def state_relation_def)

lemma curDomain_corres':
  "corres (=) \<top> (\<lambda>s. ksCurDomain s \<le> maxDomain)
    (gets cur_domain) (if Suc 0 < numDomains then curDomain else return 0)"
  apply (case_tac "1 < numDomains"; simp)
   apply (rule corres_guard_imp[OF curDomain_corres]; solves simp)
  (* if we have only one domain, then we are in it *)
  apply (clarsimp simp: return_def simpler_gets_def bind_def maxDomain_def
                        state_relation_def corres_underlying_def)
  done

lemma lookupBitmapPriority_Max_eqI:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s ; ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s = (Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s (d, prio))})"
  apply (rule Max_eqI[simplified eq_commute]; simp)
   apply (fastforce simp: bitmapL1_highest_lookup valid_bitmapQ_bitmapQ_simp)
  apply (metis valid_bitmapQ_bitmapQ_simp bitmapQ_from_bitmap_lookup)
  done

lemma corres_gets_queues_getReadyQueuesL1Bitmap:
  "corres (\<lambda>qs l1. (l1 = 0) = (\<forall>p. qs p = [])) \<top> valid_bitmaps
    (gets (\<lambda>s. ready_queues s d)) (getReadyQueuesL1Bitmap d)"
  unfolding state_relation_def valid_bitmaps_def getReadyQueuesL1Bitmap_def
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (drule_tac x=d in spec)
  apply (fastforce simp: bitmapL1_zero_ksReadyQueues list_queue_relation_def tcbQueueEmpty_def)
  done

lemma guarded_switch_to_chooseThread_fragment_corres:
  "corres dc
    (P and st_tcb_at runnable t and invs and valid_sched)
    (P' and invs_no_cicd')
    (guarded_switch_to t)
    (do runnable \<leftarrow> isRunnable t;
        y \<leftarrow> assert runnable;
        ThreadDecls_H.switchToThread t
     od)"
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  unfolding guarded_switch_to_def isRunnable_def
  apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getThreadState_corres])
      apply (rule corres_assert_assume_l)
      apply (rule corres_assert_assume_r)
      apply (rule switchToThread_corres)
     apply (wp gts_st_tcb_at)+
   apply (clarsimp simp: st_tcb_at_tcb_at invs_def valid_state_def valid_pspace_def valid_sched_def
                          invs_valid_vs_lookup invs_unique_refs)
  apply (auto elim!: pred_tcb'_weakenE split: thread_state.splits
              simp: pred_tcb_at' runnable'_def all_invs_but_ct_idle_or_in_cur_domain'_def)
  done

lemma Max_prio_helper:
  "ready_queues_relation s s'
   \<Longrightarrow> Max {prio. ready_queues s d prio \<noteq> []}
       = Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s' (d, prio))}"
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def tcbQueueEmpty_def)
  apply (rule Max_eq_if)
     apply fastforce
    apply fastforce
   apply (fastforce dest: heap_path_head)
  apply clarsimp
  apply (drule_tac x=d in spec)
  apply (drule_tac x=b in spec)
  apply force
  done

lemma bitmap_lookup_queue_is_max_non_empty:
  "\<lbrakk> valid_bitmaps s'; (s, s') \<in> state_relation; invs s;
     ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0 \<rbrakk>
   \<Longrightarrow> the (tcbQueueHead (ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')))
       = hd (max_non_empty_queue (ready_queues s (cur_domain s)))"
  apply (clarsimp simp: max_non_empty_queue_def valid_bitmaps_def lookupBitmapPriority_Max_eqI)
  apply (frule curdomain_relation)
  apply (drule state_relation_ready_queues_relation)
  apply (simp add: Max_prio_helper)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
  apply (frule (2) bitmapL1_zero_ksReadyQueues[THEN arg_cong_Not, THEN iffD1])
  apply clarsimp
  apply (cut_tac P="\<lambda>x. \<not> tcbQueueEmpty (ksReadyQueues s' (ksCurDomain s', x))"
              in setcomp_Max_has_prop)
   apply fastforce
  apply (clarsimp simp: ready_queues_relation_def Let_def list_queue_relation_def tcbQueueEmpty_def)
  apply (drule_tac x="ksCurDomain s'" in spec)
  apply (drule_tac x="Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s' (ksCurDomain s', prio))}"
                in spec)
  using heap_path_head tcbQueueEmpty_def
  by fastforce

lemma ksReadyQueuesL1Bitmap_return_wp:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s d) s \<rbrace> getReadyQueuesL1Bitmap d \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getReadyQueuesL1Bitmap_def
  by wp

lemma curDomain_or_return_0:
  "\<lbrakk> \<lbrace>P\<rbrace> curDomain \<lbrace>\<lambda>rv s. Q rv s \<rbrace>; \<And>s. P s \<Longrightarrow> ksCurDomain s \<le> maxDomain \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> if 1 < numDomains then curDomain else return 0 \<lbrace>\<lambda>rv s. Q rv s \<rbrace>"
  apply (case_tac "1 < numDomains"; simp)
  apply (simp add: valid_def curDomain_def simpler_gets_def return_def maxDomain_def)
  done

lemma invs_no_cicd_ksCurDomain_maxDomain':
  "invs_no_cicd' s \<Longrightarrow> ksCurDomain s \<le> maxDomain"
  unfolding invs_no_cicd'_def by simp

crunch curDomain
  for valid_bitmaps[wp]: valid_bitmaps

lemma chooseThread_corres:
  "corres dc (invs and valid_sched) invs_no_cicd' choose_thread chooseThread"
  (is "corres _ ?PREI ?PREH _ _")
proof -

  (* if we only have one domain, we are in it *)
  have one_domain_case:
    "\<And>s. \<lbrakk> invs_no_cicd' s; numDomains \<le> 1 \<rbrakk> \<Longrightarrow> ksCurDomain s = 0"
    by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def maxDomain_def)

  show ?thesis
    supply if_split[split del]
    apply (clarsimp simp: choose_thread_def chooseThread_def)
    apply add_ready_qs_runnable
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply (fastforce intro: ksReadyQueues_asrt_cross)
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply fastforce
    apply (simp only: return_bind Let_def)
    apply (subst if_swap[where P="_ \<noteq> 0"]) (* put switchToIdleThread on first branch*)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF curDomain_corres'])
        apply clarsimp
        apply (rule corres_split[OF corres_gets_queues_getReadyQueuesL1Bitmap])
          apply (erule corres_if2[OF sym])
           apply (rule switchToIdleThread_corres)
          apply (rule corres_symb_exec_r)
             apply (rule corres_symb_exec_r)
                apply (rule_tac P="\<lambda>s. ?PREI s \<and> queues = ready_queues s (cur_domain s)
                                       \<and> st_tcb_at runnable (hd (max_non_empty_queue queues)) s"
                            and P'="\<lambda>s. ?PREH s \<and> l1 = ksReadyQueuesL1Bitmap s (ksCurDomain s)
                                        \<and> l1 \<noteq> 0
                                        \<and> queue = ksReadyQueues s (ksCurDomain s,
                                                                   lookupBitmapPriority (ksCurDomain s) s)"
                            and F="the (tcbQueueHead queue) = hd (max_non_empty_queue queues)"
                             in corres_req)
                 apply (fastforce simp: bitmap_lookup_queue_is_max_non_empty
                                        all_invs_but_ct_idle_or_in_cur_domain'_def)
                apply clarsimp
                apply (rule corres_guard_imp)
                  apply (rule_tac P=\<top> and P'=\<top> in guarded_switch_to_chooseThread_fragment_corres)
                 apply (wpsimp simp: getQueue_def getReadyQueuesL2Bitmap_def)+
        apply (wp hoare_vcg_conj_lift hoare_vcg_imp_lift ksReadyQueuesL1Bitmap_return_wp)
       apply (wpsimp wp: curDomain_or_return_0 simp: curDomain_def)+
     apply (clarsimp simp: valid_sched_def max_non_empty_queue_def valid_queues_def split: if_splits)
     apply (erule_tac x="cur_domain s" in allE)
     apply (erule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in allE)
     apply (case_tac "ready_queues s (cur_domain s)
                                     (Max {prio. ready_queues s (cur_domain s) prio
                      \<noteq> []})")
      apply (clarsimp)
      apply (subgoal_tac "ready_queues s (cur_domain s)
                                         (Max {prio. ready_queues s (cur_domain s) prio \<noteq> []})
                          \<noteq> []")
       apply fastforce
      apply (fastforce elim!: setcomp_Max_has_prop)
     apply fastforce
    apply clarsimp
    apply (frule invs_no_cicd_ksCurDomain_maxDomain')
    apply (prop_tac "valid_bitmaps s")
     apply (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def)
    apply (fastforce dest: one_domain_case split: if_splits)
    done
qed

lemma thread_get_comm: "do x \<leftarrow> thread_get f p; y \<leftarrow> gets g; k x y od =
           do y \<leftarrow> gets g; x \<leftarrow> thread_get f p; k x y od"
  apply (rule ext)
  apply (clarsimp simp add: gets_the_def assert_opt_def
                   bind_def gets_def get_def return_def
                   thread_get_def
                   fail_def split: option.splits)
  done

lemma schact_bind_inside: "do x \<leftarrow> f; (case act of resume_cur_thread \<Rightarrow> f1 x
                     | switch_thread t \<Rightarrow> f2 t x
                     | choose_new_thread \<Rightarrow> f3 x) od
          = (case act of resume_cur_thread \<Rightarrow> (do x \<leftarrow> f; f1 x od)
                     | switch_thread t \<Rightarrow> (do x \<leftarrow> f; f2 t x od)
                     | choose_new_thread \<Rightarrow> (do x \<leftarrow> f; f3 x od))"
  apply (case_tac act,simp_all)
  done

lemma getDomainTime_corres:
  "corres (=) \<top> \<top> (gets domain_time) getDomainTime"
  by (simp add: getDomainTime_def state_relation_def)

lemma reset_work_units_equiv:
  "do_extended_op (modify (work_units_completed_update (\<lambda>_. 0)))
   = (modify (work_units_completed_update (\<lambda>_. 0)))"
  by (clarsimp simp: reset_work_units_def[symmetric])

lemma nextDomain_corres:
  "corres dc \<top> \<top> next_domain nextDomain"
  apply (clarsimp simp: next_domain_def nextDomain_def reset_work_units_equiv modify_modify)
  apply (rule corres_modify)
  apply (simp add: state_relation_def Let_def dschLength_def dschDomain_def cdt_relation_def)
  done

lemma next_domain_valid_sched[wp]:
  "\<lbrace> valid_sched and (\<lambda>s. scheduler_action s  = choose_new_thread)\<rbrace> next_domain \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: next_domain_def Let_def)
  apply (wpsimp wp: dxo_wp_weak)
  apply (clarsimp simp: valid_sched_def)
  done

lemma nextDomain_invs_no_cicd':
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread)\<rbrace> nextDomain \<lbrace> \<lambda>_. invs_no_cicd' \<rbrace>"
  apply (simp add: nextDomain_def Let_def dschLength_def dschDomain_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def
                        ct_not_inQ_def cur_tcb'_def ct_idle_or_in_cur_domain'_def dschDomain_def
                        all_invs_but_ct_idle_or_in_cur_domain'_def)
  done

lemma prepareNextDomain_corres[corres]:
  "corres dc (pspace_aligned and pspace_distinct) \<top>
             arch_prepare_next_domain prepareNextDomain"
  by (clarsimp simp: arch_prepare_next_domain_def prepareNextDomain_def)

crunch prepareNextDomain
  for invs'[wp]: invs'
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma scheduleChooseNewThread_fragment_corres:
  "corres dc (invs and valid_sched and (\<lambda>s. scheduler_action s = choose_new_thread)) (invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread))
     (do _ \<leftarrow> when (domainTime = 0) (do
           _ \<leftarrow> arch_prepare_next_domain;
           next_domain
         od);
         choose_thread
      od)
     (do _ \<leftarrow> when (domainTime = 0) (do
           _ \<leftarrow> prepareNextDomain;
           nextDomain
         od);
         chooseThread
      od)"
  apply (subst bind_dummy_ret_val)+
  apply (corres corres: nextDomain_corres chooseThread_corres
                    wp: nextDomain_invs_no_cicd')
   apply (auto simp: valid_sched_def invs'_def valid_state'_def all_invs_but_ct_idle_or_in_cur_domain'_def)
  done

lemma scheduleSwitchThreadFastfail_corres:
  "\<lbrakk> ct \<noteq> it \<longrightarrow> (tp = tp' \<and> cp = cp') ; ct = ct' ; it = it' \<rbrakk> \<Longrightarrow>
   corres ((=)) (is_tcb_at ct) (tcb_at' ct)
     (schedule_switch_thread_fastfail ct it cp tp)
     (scheduleSwitchThreadFastfail ct' it' cp' tp')"
  by (clarsimp simp: schedule_switch_thread_fastfail_def scheduleSwitchThreadFastfail_def)

lemma gets_is_highest_prio_expand:
  "gets (is_highest_prio d p) \<equiv> do
    q \<leftarrow> gets (\<lambda>s. ready_queues s d);
    return ((\<forall>p. q p = []) \<or> Max {prio. q prio \<noteq> []} \<le> p)
   od"
  by (clarsimp simp: is_highest_prio_def gets_def)

lemma isHighestPrio_corres:
  assumes "d' = d"
  assumes "p' = p"
  shows
    "corres ((=)) \<top> valid_bitmaps
      (gets (is_highest_prio d p))
      (isHighestPrio d' p')"
  using assms
  apply (clarsimp simp: gets_is_highest_prio_expand isHighestPrio_def)
  apply (subst getHighestPrio_def')
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_queues_getReadyQueuesL1Bitmap])
      apply (rule corres_if_r'[where P'="\<lambda>_. True",rotated])
       apply (rule_tac corres_symb_exec_r)
          apply (rule_tac P="\<lambda>s. q = ready_queues s d"
                      and P'="\<lambda>s. valid_bitmaps s \<and> l1 = ksReadyQueuesL1Bitmap s d \<and>
                                  l1 \<noteq> 0 \<and> hprio = lookupBitmapPriority d s"
                      and F="hprio = Max {prio. q prio \<noteq> []}" in corres_req)
           apply (elim conjE)
           apply (clarsimp simp: valid_bitmaps_def)
           apply (subst lookupBitmapPriority_Max_eqI; blast?)
           apply (fastforce dest: state_relation_ready_queues_relation Max_prio_helper[where d=d]
                            simp: tcbQueueEmpty_def)
          apply fastforce
         apply (wpsimp simp: if_apply_def2 wp: hoare_drop_imps ksReadyQueuesL1Bitmap_return_wp)+
  done

crunch isHighestPrio
  for inv[wp]: P
crunch curDomain
  for inv[wp]: P
crunch scheduleSwitchThreadFastfail
  for inv[wp]: P

lemma setSchedulerAction_invs': (* not in wp set, clobbered by ssa_wp *)
  "setSchedulerAction ChooseNewThread \<lbrace>invs' \<rbrace>"
  by (wpsimp simp: invs'_def cur_tcb'_def valid_state'_def valid_irq_node'_def ct_not_inQ_def
                   ct_idle_or_in_cur_domain'_def)

lemma scheduleChooseNewThread_corres:
  "corres dc
    (\<lambda>s. invs s \<and> valid_sched s \<and> scheduler_action s = choose_new_thread)
    (\<lambda>s. invs' s \<and> ksSchedulerAction s = ChooseNewThread)
           schedule_choose_new_thread scheduleChooseNewThread"
  unfolding schedule_choose_new_thread_def scheduleChooseNewThread_def
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getDomainTime_corres], clarsimp)
      apply (rule corres_split[OF scheduleChooseNewThread_fragment_corres, simplified bind_assoc])
        apply (rule setSchedulerAction_corres)
        apply (wp | simp)+
    apply (wp | simp add: getDomainTime_def)+
   apply auto
  done

lemma thread_get_when_corres:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> r (f tcb) (f' tcb')"
  shows      "corres (\<lambda>rv rv'. b \<longrightarrow> r rv rv') (tcb_at t and pspace_aligned and pspace_distinct) (tcb_at' t)
                ((if b then thread_get f t else return 0)) (threadGet f' t)"
  apply clarsimp
  apply (rule conjI; clarsimp)
  apply (rule corres_guard_imp, rule threadGet_corres; simp add: x)
  apply (clarsimp simp: threadGet_def)
  apply (rule corres_noop)
  apply wpsimp+
  done

lemma tcb_sched_enqueue_in_correct_ready_q[wp]:
  "tcb_sched_action tcb_sched_enqueue t \<lbrace>in_correct_ready_q\<rbrace> "
  unfolding tcb_sched_action_def tcb_sched_enqueue_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: in_correct_ready_q_def obj_at_def etcb_at_def is_etcb_at_def etcbs_of'_def)
  done

lemma tcb_sched_append_in_correct_ready_q[wp]:
  "tcb_sched_action tcb_sched_append tcb_ptr \<lbrace>in_correct_ready_q\<rbrace> "
  unfolding tcb_sched_action_def tcb_sched_append_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: in_correct_ready_q_def obj_at_def etcb_at_def is_etcb_at_def etcbs_of'_def)
  done

lemma tcb_sched_enqueue_ready_qs_distinct[wp]:
  "tcb_sched_action tcb_sched_enqueue t \<lbrace>ready_qs_distinct\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: ready_qs_distinct_def etcb_at_def is_etcb_at_def)
  done

lemma tcb_sched_append_ready_qs_distinct[wp]:
  "tcb_sched_action tcb_sched_append t \<lbrace>ready_qs_distinct\<rbrace> "
  unfolding tcb_sched_action_def tcb_sched_append_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: ready_qs_distinct_def etcb_at_def is_etcb_at_def)
  done

crunch set_scheduler_action
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: crunch_wps simp: in_correct_ready_q_def ready_qs_distinct_def)

crunch reschedule_required
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (ignore: tcb_sched_action wp: crunch_wps)

crunch tcb_sched_action
  for valid_vs_lookup[wp]: valid_vs_lookup

lemma schedule_corres:
  "corres dc (invs and valid_sched and valid_list) invs' (Schedule_A.schedule) ThreadDecls_H.schedule"
  supply ssa_wp[wp del]
  supply tcbSchedEnqueue_invs'[wp del]
  supply tcbSchedEnqueue_invs'_not_ResumeCurrentThread[wp del]
  supply setSchedulerAction_direct[wp]
  supply if_split[split del]

  apply (clarsimp simp: Schedule_A.schedule_def Thread_H.schedule_def)
  apply (subst thread_get_test)
  apply (subst thread_get_comm)
  apply (subst schact_bind_inside)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres[THEN corres_rel_imp[where r="\<lambda>x y. y = x"],simplified]])
      apply (rule corres_split[OF getSchedulerAction_corres])
        apply (rule corres_split_sched_act,assumption)
          apply (rule_tac P="tcb_at ct" in corres_symb_exec_l')
            apply (rule_tac corres_symb_exec_l)
               apply simp
               apply (rule corres_assert_ret)
              apply ((wpsimp wp: thread_get_wp' gets_exs_valid)+)
         prefer 2
         (* choose thread *)
         apply clarsimp
         apply (rule corres_split[OF thread_get_isRunnable_corres])
           apply (rule corres_split)
              apply (rule corres_when, simp)
              apply (rule tcbSchedEnqueue_corres, simp)
             apply (rule scheduleChooseNewThread_corres, simp)
            apply (wp thread_get_wp' tcbSchedEnqueue_invs' hoare_vcg_conj_lift hoare_drop_imps
                   | clarsimp)+
        (* switch to thread *)
        apply (rule corres_split[OF thread_get_isRunnable_corres],
                rename_tac was_running wasRunning)
          apply (rule corres_split)
             apply (rule corres_when, simp)
             apply (rule tcbSchedEnqueue_corres, simp)
            apply (rule corres_split[OF getIdleThread_corres], rename_tac it it')
              apply (rule_tac F="was_running \<longrightarrow> ct \<noteq> it" in corres_gen_asm)
              apply (rule corres_split)
                 apply (rule threadGet_corres[where r="(=)"])
                 apply (clarsimp simp: tcb_relation_def)
                apply (rename_tac tp tp')
                apply (rule corres_split)
                   apply (rule thread_get_when_corres[where r="(=)"])
                   apply (clarsimp simp: tcb_relation_def)
                  apply (rename_tac cp cp')
                  apply (rule corres_split)
                     apply (rule scheduleSwitchThreadFastfail_corres; simp)
                    apply (rule corres_split[OF curDomain_corres])
                      apply (rule corres_split[OF isHighestPrio_corres]; simp only:)
                        apply (rule corres_if, simp)
                         apply (rule corres_split[OF tcbSchedEnqueue_corres], simp)
                           apply (simp, fold dc_def)
                           apply (rule corres_split)
                              apply (rule setSchedulerAction_corres; simp)
                             apply (rule scheduleChooseNewThread_corres)
                            apply (wp | simp)+
                            apply (simp add: valid_sched_def)
                            apply wp
                            apply (rule hoare_vcg_conj_lift)
                             apply (rule_tac t=t in set_scheduler_action_cnt_valid_blocked')
                            apply (wpsimp wp: setSchedulerAction_invs')+
                          apply (wp tcb_sched_action_enqueue_valid_blocked hoare_vcg_all_lift enqueue_thread_queued)
                         apply (wp tcbSchedEnqueue_invs'_not_ResumeCurrentThread)
                        apply (rule corres_if, fastforce)
                         apply (rule corres_split[OF tcbSchedAppend_corres], simp)
                           apply (simp, fold dc_def)
                           apply (rule corres_split)
                              apply (rule setSchedulerAction_corres; simp)
                             apply (rule scheduleChooseNewThread_corres)
                            apply (wp | simp)+
                            apply (simp add: valid_sched_def)
                            apply wp
                            apply (rule hoare_vcg_conj_lift)
                             apply (rule_tac t=t in set_scheduler_action_cnt_valid_blocked')
                            apply (wpsimp wp: setSchedulerAction_invs')+
                          apply (wp tcb_sched_action_append_valid_blocked hoare_vcg_all_lift append_thread_queued)
                         apply (wp tcbSchedAppend_invs'_not_ResumeCurrentThread)

                        apply (rule corres_split[OF guarded_switch_to_corres], simp)
                          apply (rule setSchedulerAction_corres[simplified dc_def])
                          apply (wp | simp)+

                      (* isHighestPrio *)
                      apply (clarsimp simp: if_apply_def2)
                      apply ((wp (once) hoare_drop_imp)+)[1]

                     apply (simp add: if_apply_def2)
                     apply ((wp (once) hoare_drop_imp)+)[1]
                    apply wpsimp+

           apply (clarsimp simp: conj_ac cong: conj_cong)
           apply wp
           apply (rule_tac Q'="\<lambda>_ s. valid_blocked_except t s \<and> scheduler_action s = switch_thread t"
                    in hoare_post_imp, fastforce)
           apply (wp add: tcb_sched_action_enqueue_valid_blocked_except
                          tcbSchedEnqueue_invs'_not_ResumeCurrentThread thread_get_wp
                     del: gets_wp
                  | strengthen valid_objs'_valid_tcbs')+
       apply (clarsimp simp: conj_ac if_apply_def2 cong: imp_cong conj_cong)
       apply (wp gets_wp)+

   (* abstract final subgoal *)
   apply clarsimp

   subgoal for s
     apply (clarsimp split: Structures_A.scheduler_action.splits
                     simp: invs_psp_aligned invs_distinct invs_valid_objs invs_arch_state
                           invs_vspace_objs[simplified] tcb_at_invs)
     apply (rule conjI, clarsimp)
      apply (fastforce simp: invs_def
                            valid_sched_def valid_sched_action_def is_activatable_def
                            st_tcb_at_def obj_at_def valid_state_def only_idle_def
                            )
     apply (rule conjI, clarsimp)
      subgoal for candidate
        apply (clarsimp simp: valid_sched_def invs_def valid_state_def cur_tcb_def
                               valid_arch_caps_def valid_sched_action_def
                               weak_valid_sched_action_def
                               valid_blocked_except_def valid_blocked_def)
        apply (fastforce simp add: pred_tcb_at_def obj_at_def is_tcb valid_idle_def)
        done
     (* choose new thread case *)
     apply (intro impI conjI allI tcb_at_invs
            | fastforce simp: invs_def cur_tcb_def
                              valid_sched_def st_tcb_at_def obj_at_def valid_state_def
                              weak_valid_sched_action_def not_cur_thread_def)+
     done

  (* haskell final subgoal *)
  apply (clarsimp simp: if_apply_def2 invs'_def valid_state'_def valid_sched_def
                  cong: imp_cong  split: scheduler_action.splits)
  apply (fastforce simp: cur_tcb'_def valid_pspace'_def)
  done

lemma ssa_all_invs_but_ct_not_inQ':
  "\<lbrace>all_invs_but_ct_not_inQ' and sch_act_wf sa and
   (\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s)\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. all_invs_but_ct_not_inQ'\<rbrace>"
proof -
  show ?thesis
    apply (simp add: setSchedulerAction_def)
    apply wp
    apply (clarsimp simp add: invs'_def valid_state'_def cur_tcb'_def
                              state_refs_of'_def ps_clear_def valid_irq_node'_def
                              tcb_in_cur_domain'_def ct_idle_or_in_cur_domain'_def bitmapQ_defs
                        cong: option.case_cong)
    done
qed

lemma ssa_ct_not_inQ:
  "\<lbrace>\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. ct_not_inQ\<rbrace>"
  by (simp add: setSchedulerAction_def ct_not_inQ_def, wp, clarsimp)

lemma ssa_all_invs_but_ct_not_inQ''[simplified]:
  "\<lbrace>\<lambda>s. (all_invs_but_ct_not_inQ' s \<and> sch_act_wf sa s)
    \<and> (sa = ResumeCurrentThread \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s)
    \<and> (sa = ResumeCurrentThread \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s)\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp only: all_invs_but_not_ct_inQ_check' [symmetric])
  apply (rule hoare_elim_pred_conj)
  apply (wp hoare_vcg_conj_lift [OF ssa_all_invs_but_ct_not_inQ' ssa_ct_not_inQ])
  apply (clarsimp)
  done

lemma ssa_invs':
  "\<lbrace>invs' and sch_act_wf sa and
    (\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s) and
    (\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s)\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp ssa_all_invs_but_ct_not_inQ'')
  apply (clarsimp simp add: invs'_def valid_state'_def)
  done

lemma getDomainTime_wp[wp]: "\<lbrace>\<lambda>s. P (ksDomainTime s) s \<rbrace> getDomainTime \<lbrace> P \<rbrace>"
  unfolding getDomainTime_def
  by wp

lemma switchToThread_ct_not_queued_2:
  "\<lbrace>invs_no_cicd' and tcb_at' t\<rbrace> switchToThread t \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (simp add: Thread_H.switchToThread_def)
  apply (wp)
    apply (simp add: RISCV64_H.switchToThread_def setCurThread_def)
    apply (wp tcbSchedDequeue_not_tcbQueued hoare_drop_imp | simp )+
  done

lemma setCurThread_obj_at':
  "\<lbrace> obj_at' P t \<rbrace> setCurThread t \<lbrace>\<lambda>rv s. obj_at' P (ksCurThread s) s \<rbrace>"
proof -
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (simp add: ct_in_state'_def st_tcb_at'_def)
    done
qed

lemma switchToIdleThread_ct_not_queued_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>_ s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def)
  apply (wp setCurThread_obj_at')
  apply (clarsimp simp: ready_qs_runnable_def)
  apply (drule_tac x="ksIdleThread s" in spec)
  apply (clarsimp simp: invs_no_cicd'_def valid_idle'_def st_tcb_at'_def idle_tcb'_def obj_at'_def)
  done

lemma switchToIdleThread_activatable_2[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv. ct_in_state' activatable'\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   RISCV64_H.switchToIdleThread_def)
  apply (wp setCurThread_ct_in_state)
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_idle'_def
                        pred_tcb_at'_def obj_at'_def idle_tcb'_def)
  done

lemma switchToThread_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' thread\<rbrace>
   ThreadDecls_H.switchToThread thread
   \<lbrace>\<lambda>y s. tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def setCurThread_def)
  apply (wpsimp wp: tcbSchedDequeue_not_tcbQueued hoare_drop_imps)
  done

lemma chooseThread_invs_no_cicd'_posts: (* generic version *)
  "\<lbrace> invs_no_cicd' \<rbrace> chooseThread
   \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and>
           ct_in_state' activatable' s \<and>
           (ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s) \<rbrace>"
    (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
proof -
  note switchToThread_invs[wp del]
  note switchToThread_invs_no_cicd'[wp del]
  note switchToThread_lookupBitmapPriority_wp[wp]
  note assert_wp[wp del]
  note if_split[split del]

  (* if we only have one domain, we are in it *)
  have one_domain_case:
    "\<And>s. \<lbrakk> invs_no_cicd' s; numDomains \<le> 1 \<rbrakk> \<Longrightarrow> ksCurDomain s = 0"
    by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def maxDomain_def)

  show ?thesis
    apply (clarsimp simp: chooseThread_def Let_def curDomain_def)
    apply (rule bind_wp[OF _ stateAssert_sp])+
    apply (simp only: return_bind, simp)
    apply (rule bind_wp[where Q'="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s
                                              \<and> ksReadyQueues_asrt s \<and> ready_qs_runnable s"])
     apply (rule_tac Q'="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                                rv = ksReadyQueuesL1Bitmap s curdom \<and>
                                ksReadyQueues_asrt s \<and> ready_qs_runnable s"
                  in bind_wp)
      apply (rename_tac l1)
      apply (case_tac "l1 = 0")
       (* switch to idle thread *)
       apply simp
       apply (rule hoare_pre)
        apply (wp (once) switchToIdleThread_ct_not_queued_no_cicd')
        apply (wp (once))
        apply ((wp hoare_disjI1 switchToIdleThread_curr_is_idle)+)[1]
       apply simp
      (* we have a thread to switch to *)
      apply (clarsimp simp: bitmap_fun_defs)
      apply (wp assert_inv switchToThread_ct_not_queued_2 assert_inv hoare_disjI2
                switchToThread_tcb_in_cur_domain')
      apply (clarsimp simp:  all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def
                             valid_bitmaps_def)
      apply (frule (6) lookupBitmapPriority_obj_at')
      apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def tcbQueueEmpty_def inQ_def)
     apply (wpsimp simp: bitmap_fun_defs curDomain_def one_domain_case)+
    done
qed

lemma chooseThread_activatable_2:
  "\<lbrace>invs_no_cicd'\<rbrace> chooseThread \<lbrace>\<lambda>rv. ct_in_state' activatable'\<rbrace>"
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs_no_cicd'_posts)
   apply simp+
  done

lemma chooseThread_ct_not_queued_2:
  "\<lbrace> invs_no_cicd'\<rbrace> chooseThread \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
    (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs_no_cicd'_posts)
   apply simp+
  done

lemma chooseThread_invs_no_cicd':
  "\<lbrace> invs_no_cicd' \<rbrace> chooseThread \<lbrace>\<lambda>rv. invs' \<rbrace>"
proof -
  note switchToThread_invs[wp del]
  note switchToThread_invs_no_cicd'[wp del]
  note switchToThread_lookupBitmapPriority_wp[wp]
  note assert_wp[wp del]
  note if_split[split del]

  (* if we only have one domain, we are in it *)
  have one_domain_case:
    "\<And>s. \<lbrakk> invs_no_cicd' s; numDomains \<le> 1 \<rbrakk> \<Longrightarrow> ksCurDomain s = 0"
    by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def maxDomain_def)

  (* NOTE: do *not* unfold numDomains in the rest of the proof,
           it should work for any number *)

  (* FIXME this is almost identical to the chooseThread_invs_no_cicd'_posts proof, can generalise? *)
  show ?thesis
    apply (clarsimp simp: chooseThread_def Let_def curDomain_def)
    apply (rule bind_wp[OF _ stateAssert_sp])+
    apply (simp only: return_bind, simp)
    apply (rule bind_wp[where Q'="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s
                                              \<and> ksReadyQueues_asrt s \<and> ready_qs_runnable s"])
     apply (rule_tac Q'="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                                rv = ksReadyQueuesL1Bitmap s curdom \<and>
                                ksReadyQueues_asrt s \<and> ready_qs_runnable s"
                  in bind_wp)
      apply (rename_tac l1)
      apply (case_tac "l1 = 0")
       (* switch to idle thread *)
       apply (simp, wp switchToIdleThread_invs_no_cicd', simp)
      (* we have a thread to switch to *)
      apply (clarsimp simp: bitmap_fun_defs)
      apply (wp assert_inv)
      apply (clarsimp simp:  all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def
                             valid_bitmaps_def)
      apply (frule (6) lookupBitmapPriority_obj_at')
      apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def tcbQueueEmpty_def inQ_def)
      apply (fastforce elim: bitmapQ_from_bitmap_lookup simp: lookupBitmapPriority_def)
     apply (wpsimp simp: bitmap_fun_defs curDomain_def one_domain_case)+
    done
qed

lemma chooseThread_in_cur_domain':
  "\<lbrace> invs_no_cicd' \<rbrace> chooseThread \<lbrace>\<lambda>rv s. ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs_no_cicd'_posts, simp_all)
  done

lemma scheduleChooseNewThread_invs':
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread) \<rbrace>
   scheduleChooseNewThread
   \<lbrace> \<lambda>_ s. invs' s \<rbrace>"
  unfolding scheduleChooseNewThread_def
  apply (wpsimp wp: ssa_invs' chooseThread_invs_no_cicd' chooseThread_ct_not_queued_2
                    chooseThread_activatable_2 chooseThread_invs_no_cicd'
                    chooseThread_in_cur_domain' nextDomain_invs_no_cicd' chooseThread_ct_not_queued_2)
  apply (clarsimp simp: invs'_to_invs_no_cicd'_def)
  done

lemma schedule_invs':
  "\<lbrace>invs'\<rbrace> ThreadDecls_H.schedule \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply ssa_wp[wp del]
  apply (simp add: schedule_def)
  apply (rule_tac bind_wp, rename_tac t)
   apply (wp, wpc)
      \<comment> \<open>action = ResumeCurrentThread\<close>
      apply (wp)[1]
     \<comment> \<open>action = ChooseNewThread\<close>
     apply (wp scheduleChooseNewThread_invs')
    \<comment> \<open>action = SwitchToThread candidate\<close>
    apply (wpsimp wp: scheduleChooseNewThread_invs' ssa_invs'
                      chooseThread_invs_no_cicd' setSchedulerAction_invs' setSchedulerAction_direct
                      switchToThread_tcb_in_cur_domain' switchToThread_ct_not_queued_2
           | wp hoare_disjI2[where Q'="\<lambda>_ s. tcb_in_cur_domain' (ksCurThread s) s"]
           | wp hoare_drop_imp[where f="isHighestPrio d p" for d p]
           | simp only: obj_at'_activatable_st_tcb_at'[simplified comp_def]
           | strengthen invs'_invs_no_cicd
           | wp hoare_vcg_imp_lift)+
  apply (frule invs_sch_act_wf')
  apply (auto simp: invs_sch_act_wf' obj_at'_activatable_st_tcb_at'
                     st_tcb_at'_runnable_is_activatable)
  done

lemma setCurThread_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
  setCurThread t
  \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply simp
  done

lemma stt_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
  switchToThread t
  \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def RISCV64_H.switchToThread_def storeWordUser_def)
  apply (wp setCurThread_nosch hoare_drop_imp |simp)+
  done

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   RISCV64_H.switchToIdleThread_def  storeWordUser_def)
  apply (wp setCurThread_nosch | simp add: getIdleThread_def)+
  done

lemma schedule_sch:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  by (wp setSchedulerAction_direct | wpc| simp add: schedule_def scheduleChooseNewThread_def)+

lemma schedule_sch_act_simple:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (rule hoare_strengthen_post [OF schedule_sch])
  apply (simp add: sch_act_simple_def)
  done

lemma ssa_ct:
  "\<lbrace>ct_in_state' P\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
proof -
  show ?thesis
    apply (unfold setSchedulerAction_def)
    apply wp
    apply (clarsimp simp add: ct_in_state'_def pred_tcb_at'_def)
    done
qed

lemma scheduleChooseNewThread_ct_activatable'[wp]:
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread) \<rbrace>
   scheduleChooseNewThread
   \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  unfolding scheduleChooseNewThread_def
  by (wpsimp simp: ct_in_state'_def
                wp: ssa_invs' nextDomain_invs_no_cicd'
                    chooseThread_activatable_2[simplified ct_in_state'_def]
         | (rule hoare_lift_Pf[where f=ksCurThread], solves wp)
         | strengthen invs'_invs_no_cicd)+

lemma schedule_ct_activatable'[wp]:
  "\<lbrace>invs'\<rbrace> ThreadDecls_H.schedule \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  supply ssa_wp[wp del]
  apply (simp add: schedule_def)
  apply (rule_tac bind_wp, rename_tac t)
   apply (wp, wpc)
      \<comment> \<open>action = ResumeCurrentThread\<close>
      apply (wp)[1]
     \<comment> \<open>action = ChooseNewThread\<close>
     apply wpsimp
    \<comment> \<open>action = SwitchToThread\<close>
    apply (wpsimp wp: ssa_invs' setSchedulerAction_direct ssa_ct
           | wp hoare_drop_imp[where f="isHighestPrio d p" for d p]
           | simp only: obj_at'_activatable_st_tcb_at'[simplified comp_def]
           | strengthen invs'_invs_no_cicd
           | wp hoare_vcg_imp_lift)+
  apply (fastforce dest: invs_sch_act_wf' elim: pred_tcb'_weakenE
                   simp: sch_act_wf obj_at'_activatable_st_tcb_at')
  done

lemma threadSet_sch_act_sane:
  "\<lbrace>sch_act_sane\<rbrace> threadSet f t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  by (wp sch_act_sane_lift)

lemma rescheduleRequired_sch_act_sane[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: rescheduleRequired_def sch_act_sane_def
                   setSchedulerAction_def)
  by (wp | wpc | clarsimp)+

lemma sts_sch_act_sane:
  "\<lbrace>sch_act_sane\<rbrace> setThreadState st t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: setThreadState_def)
  including no_pre
  apply (wp hoare_drop_imps
           | simp add: threadSet_sch_act_sane)+
  done

lemma sbn_sch_act_sane:
  "\<lbrace>sch_act_sane\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp | simp add: threadSet_sch_act_sane)+
  done

lemma possibleSwitchTo_corres:
  "corres dc
     (weak_valid_sched_action and cur_tcb and st_tcb_at runnable t
      and in_correct_ready_q and ready_qs_distinct and pspace_aligned and pspace_distinct)
     ((\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and sym_heap_sched_pointers and valid_sched_pointers and valid_objs')
     (possible_switch_to t) (possibleSwitchTo t)"
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (rule corres_cross_over_guard[where P'=Q and Q="tcb_at' t and Q" for Q])
   apply (clarsimp simp: state_relation_def)
   apply (rule tcb_at_cross, erule st_tcb_at_tcb_at; assumption)
  apply (simp add: possible_switch_to_def possibleSwitchTo_def cong: if_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF curDomain_corres], simp)
      apply (rule corres_split)
         apply (rule threadGet_corres[where r="(=)"])
         apply (clarsimp simp: tcb_relation_def)
        apply (rule corres_split[OF getSchedulerAction_corres])
          apply (rule corres_if, simp)
           apply (rule tcbSchedEnqueue_corres, simp)
          apply (rule corres_if, simp)
            apply (case_tac action; simp)
           apply (rule corres_split[OF rescheduleRequired_corres])
             apply (rule tcbSchedEnqueue_corres, simp)
            apply (wp reschedule_required_valid_queues | strengthen valid_objs'_valid_tcbs')+
          apply (rule setSchedulerAction_corres, simp)
         apply (wpsimp wp: hoare_drop_imps)+
   apply (clarsimp simp: st_tcb_at_tcb_at)
  apply fastforce
  done

end
end
