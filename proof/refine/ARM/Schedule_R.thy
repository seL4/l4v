(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_R
imports SchedContext_R InterruptAcc_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

declare static_imp_wp[wp_split del]

(* Levity: added (20090713 10:04:12) *)
declare sts_rel_idle [simp]

lemma invs_no_cicd'_queues:
  "invs_no_cicd' s \<Longrightarrow> valid_queues s"
  unfolding invs_no_cicd'_def
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
    by (wp alternative_wp | simp)+
  show ?thesis using p
    apply (induct xs)
     apply (simp add: y del: dc_simp)
    apply (simp only: findM.simps)
    apply (subst P)
    apply (rule corres_guard_imp)
      apply (rule corres_split_deprecated [OF _ x])
         apply (rule corres_if3)
           apply (case_tac ra, clarsimp+)[1]
          apply (rule corres_trivial, clarsimp)
          apply (case_tac ra, simp_all)[1]
         apply (erule(1) meta_mp [OF _ suffix_ConsD])
        apply assumption
       apply (rule Q)
      apply (rule hoare_post_imp [OF _ z])
      apply simp+
    done
qed

lemmas findM_awesome = findM_awesome' [OF _ _ _ suffix_order.order.refl]

lemma arch_switch_thread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
              and valid_vspace_objs and pspace_aligned and pspace_distinct
              and valid_vs_lookup and valid_global_objs
              and unique_table_refs o caps_of_state
              and st_tcb_at runnable t)
             (valid_arch_state' and valid_pspace' and st_tcb_at' runnable' t)
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  apply (simp add: arch_switch_to_thread_def ARM_H.switchToThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split' [OF set_vm_root_corres])
      apply (rule corres_machine_op[OF corres_rel_imp])
      apply (rule corres_underlying_trivial)
       apply (simp add: ARM.clearExMonitor_def | wp)+
   apply clarsimp
  apply (clarsimp simp: valid_pspace'_def)
  done

lemma schedule_choose_new_thread_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>rs s. scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by wp

lemma obj_at'_tcbQueued_cross:
  "(s,s') \<in> state_relation \<Longrightarrow> obj_at' tcbQueued t s' \<Longrightarrow> valid_queues' s' \<Longrightarrow>
    obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_priority tcb = p \<and> tcb_domain tcb = d) t s \<Longrightarrow>
    t \<in> set (ready_queues s d p)"
  apply (clarsimp simp: state_relation_def ready_queues_relation_def valid_queues'_def)
  apply (subgoal_tac "obj_at' (inQ d p) t s'", simp)
  apply (clarsimp simp: obj_at'_def inQ_def obj_at_def projectKO_eq projectKO_tcb)
  apply (frule (2) pspace_relation_tcb_domain_priority)
  apply clarsimp
  done

(* FIXME RT: It might be better to have tcb_at on the abstract side and lift it
             across the state relation *)
lemma tcbSchedAppend_corres:
  notes trans_state_update'[symmetric, simp del]
  shows
  "corres dc \<top> (tcb_at' t and valid_queues and valid_queues')
          (tcb_sched_action (tcb_sched_append) t) (tcbSchedAppend t)"
  apply (rule corres_cross_back[where P="tcb_at t" and P'="tcb_at' t"])
    apply (fastforce dest: pspace_relation_tcb_at
                     simp: state_relation_def opt_map_def obj_at'_def projectKOs
                    split: option.splits)
   apply simp
  apply (simp only: tcbSchedAppend_def tcb_sched_action_def)
  apply (rule corres_symb_exec_r [OF _ _ threadGet_inv,
                                  where Q'="\<lambda>rv. tcb_at' t and Invariants_H.valid_queues and
                                                 valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
    defer
    apply (wp threadGet_obj_at', simp, simp)
   apply (rule no_fail_pre, wp, simp)
  apply (case_tac queued)
   apply (simp add: unless_def when_def)
   apply (rule corres_no_failI)
    apply wp
   apply (clarsimp simp: in_monad gets_the_def bind_assoc thread_get_def tcb_at_def
                         assert_opt_def exec_gets get_tcb_queue_def
                         set_tcb_queue_def simpler_modify_def)
   apply (subgoal_tac "t \<in> set (ready_queues a (tcb_domain tcb) (tcb_priority tcb))")
    apply (subgoal_tac "tcb_sched_ready_q_update (tcb_domain tcb) (tcb_priority tcb)
                  (tcb_sched_append t) (ready_queues a) = ready_queues a", simp)
    apply (intro ext)
    apply (clarsimp simp: tcb_sched_append_def)
   apply (erule (2) obj_at'_tcbQueued_cross)
   apply (clarsimp simp: obj_at_def get_tcb_ko_at)
  apply (clarsimp simp: unless_def when_def cong: if_cong)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split_deprecated[where r'="(=)", OF _ threadget_corres])
       apply (rule corres_split_deprecated[where r'="(=)", OF _ threadget_corres])
          apply (rule corres_split_deprecated[where r'="(=)"])
             apply (rule corres_split_noop_rhs2)
                apply (rule corres_split_noop_rhs2)
                   apply (rule threadSet_corres_noop, simp_all add: tcb_relation_def )[1]
                  apply (rule addToBitmap_if_null_corres_noop)
                 apply wp+
               apply (simp add: tcb_sched_append_def)
               apply (intro conjI impI)
                apply (rule corres_guard_imp)
                  apply (rule setQueue_corres)
                 prefer 3
                 apply (rule_tac P=\<top> and Q="K (t \<notin> set queuea)" in corres_assume_pre)
                 apply (wp getQueue_corres getObject_tcb_wp  | simp add: tcb_relation_def threadGet_def)+
  apply (fastforce simp: valid_queues_def valid_queues_no_bitmap_def obj_at'_def inQ_def
                         projectKO_eq project_inject)
  done

crunches tcbSchedEnqueue, tcbSchedAppend, tcbSchedDequeue
  for valid_pspace'[wp]: valid_pspace'
  and valid_arch_state'[wp]: valid_arch_state'
  and pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: threadSet_pred_tcb_no_state simp: unless_def tcb_to_itcb'_def)

lemma removeFromBitmap_valid_queues_no_bitmap_except[wp]:
" \<lbrace> valid_queues_no_bitmap_except t \<rbrace>
     removeFromBitmap d p
  \<lbrace>\<lambda>_. valid_queues_no_bitmap_except t \<rbrace>"
  unfolding bitmapQ_defs valid_queues_no_bitmap_except_def
  by (wp| clarsimp simp: bitmap_fun_defs)+

lemma removeFromBitmap_bitmapQ:
  "\<lbrace> \<lambda>s. True \<rbrace> removeFromBitmap d p \<lbrace>\<lambda>_ s. \<not> bitmapQ d p s \<rbrace>"
  unfolding bitmapQ_defs bitmap_fun_defs
  apply (wp | clarsimp simp: bitmap_fun_defs wordRadix_def)+
  apply (subst (asm) complement_nth_w2p, simp_all)
  apply (fastforce intro!: order_less_le_trans[OF word_unat_mask_lt] simp: word_size)
  done

lemma removeFromBitmap_valid_bitmapQ[wp]:
" \<lbrace> valid_bitmapQ_except d p and bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans and
    (\<lambda>s. ksReadyQueues s (d,p) = []) \<rbrace>
     removeFromBitmap d p
  \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
proof -
  have "\<lbrace> valid_bitmapQ_except d p and bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans and
            (\<lambda>s. ksReadyQueues s (d,p) = []) \<rbrace>
         removeFromBitmap d p
         \<lbrace>\<lambda>_. valid_bitmapQ_except d p and  bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans and
              (\<lambda>s. \<not> bitmapQ d p s \<and> ksReadyQueues s (d,p) = []) \<rbrace>"
    by (rule hoare_pre)
       (wp removeFromBitmap_valid_queues_no_bitmap_except removeFromBitmap_valid_bitmapQ_except
           removeFromBitmap_bitmapQ, simp)
  thus ?thesis
    by - (erule hoare_strengthen_post; fastforce elim: valid_bitmap_valid_bitmapQ_exceptE)
qed

(* this should be the actual weakest precondition to establish valid_queues
   under tagging a thread as not queued *)
lemma threadSet_valid_queues_dequeue_wp:
 "\<lbrace> valid_queues_no_bitmap_except t and
        valid_bitmapQ and bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans and
        (\<lambda>s. \<forall>d p. t \<notin> set (ksReadyQueues s (d,p))) \<rbrace>
          threadSet (tcbQueued_update (\<lambda>_. False)) t
       \<lbrace>\<lambda>rv. valid_queues \<rbrace>"
  unfolding threadSet_def
  apply (rule hoare_seq_ext[OF _ getObject_tcb_sp])
  apply (rule hoare_pre)
   apply (simp add: valid_queues_def valid_queues_no_bitmap_except_def valid_queues_no_bitmap_def)
   apply (wp hoare_Ball_helper hoare_vcg_all_lift setObject_tcb_strongest)
  apply (clarsimp simp: valid_queues_no_bitmap_except_def obj_at'_def valid_queues_no_bitmap_def)
  done

(* FIXME move *)
lemmas obj_at'_conjI = obj_at_conj'

lemma setQueue_valid_queues_no_bitmap_except_dequeue_wp:
  "\<And>d p ts t.
   \<lbrace> \<lambda>s. valid_queues_no_bitmap_except t s \<and>
         (\<forall>t' \<in> set ts. obj_at' (inQ d p) t' s) \<and>
         t \<notin> set ts \<and> distinct ts \<and> p \<le> maxPriority \<and> d \<le> maxDomain \<rbrace>
       setQueue d p ts
   \<lbrace>\<lambda>rv. valid_queues_no_bitmap_except t \<rbrace>"
  unfolding setQueue_def valid_queues_no_bitmap_except_def null_def
  by wp force

definition (* if t is in a queue, it should be tagged with right priority and domain *)
  "correct_queue t s \<equiv> \<forall>d p. t \<in> set(ksReadyQueues s (d, p)) \<longrightarrow>
             (obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t s)"

lemma valid_queues_no_bitmap_correct_queueI[intro]:
  "valid_queues_no_bitmap s \<Longrightarrow> correct_queue t s"
  unfolding correct_queue_def valid_queues_no_bitmap_def
  by (fastforce simp: obj_at'_def inQ_def)


lemma tcbSchedDequeue_valid_queues_weak:
  "\<lbrace> valid_queues_no_bitmap_except t and valid_bitmapQ and
     bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans and
     correct_queue t and
     (\<lambda>s. tcb_at' t s
          \<longrightarrow> obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain \<and> tcbPriority tcb \<le> maxPriority) t s) \<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
proof -
  show ?thesis
  unfolding tcbSchedDequeue_def null_def valid_queues_def
  apply wp (* stops on threadSet *)
          apply (rule hoare_post_eq[OF _ threadSet_valid_queues_dequeue_wp],
                 simp add: valid_queues_def)
         apply (wp hoare_vcg_if_lift hoare_vcg_conj_lift hoare_vcg_imp_lift)+
             apply (wp hoare_vcg_imp_lift setQueue_valid_queues_no_bitmap_except_dequeue_wp
                       setQueue_valid_bitmapQ threadGet_wp)+
  (* wp done *)
  apply (clarsimp simp: correct_queue_def)
  apply (normalise_obj_at')
  apply (rule_tac x=ko in exI)
  apply (fastforce simp add: valid_queues_no_bitmap_except_def valid_queues_no_bitmap_def )+
  done
qed

lemma tcbSchedDequeue_valid_queues:
  "\<lbrace>Invariants_H.valid_queues and
    (\<lambda>s. tcb_at' t s \<longrightarrow> obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t s
                         \<and> obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t s)\<rbrace>
     tcbSchedDequeue t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (rule hoare_pre, rule tcbSchedDequeue_valid_queues_weak)
  apply (fastforce simp: valid_queues_def valid_queues_no_bitmap_def obj_at'_def inQ_def)
  done

lemma tcbSchedAppend_valid_queues'[wp]:
  (* most of this is identical to tcbSchedEnqueue_valid_queues' in TcbAcc_R *)
  "\<lbrace>valid_queues'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: tcbSchedAppend_def)
  apply (rule hoare_pre)
   apply (rule_tac B="\<lambda>rv. valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
           in hoare_seq_ext)
    apply (rename_tac queued)
    apply (case_tac queued; simp_all add: unless_def when_def)
     apply (wp threadSet_valid_queues' setQueue_valid_queues' | simp)+
         apply (subst conj_commute, wp)
         apply (rule hoare_pre_post, assumption)
         apply (clarsimp simp: addToBitmap_def modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
                               getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def)
         apply wp
         apply fastforce
        apply wp
       apply (subst conj_commute)
       apply clarsimp
       apply (rule_tac Q="\<lambda>rv. valid_queues'
                   and obj_at' (\<lambda>obj. \<not> tcbQueued obj) t
                   and obj_at' (\<lambda>obj. tcbPriority obj = prio) t
                   and obj_at' (\<lambda>obj. tcbDomain obj = tdom) t
                   and (\<lambda>s. t \<in> set (ksReadyQueues s (tdom, prio)))"
                   in hoare_post_imp)
        apply (clarsimp simp: valid_queues'_def obj_at'_def projectKOs inQ_def)
       apply (wp setQueue_valid_queues' | simp | simp add: setQueue_def)+
     apply (wp getObject_tcb_wp | simp add: threadGet_getObject)+
     apply (clarsimp simp: obj_at'_def inQ_def projectKOs valid_queues'_def)
    apply (wp getObject_tcb_wp | simp add: threadGet_getObject)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadSet_valid_queues'_dequeue: (* threadSet_valid_queues' is too weak for dequeue *)
  "\<lbrace>\<lambda>s. (\<forall>d p t'. obj_at' (inQ d p) t' s \<and> t' \<noteq> t \<longrightarrow> t' \<in> set (ksReadyQueues s (d, p))) \<and>
        obj_at' (inQ d p) t s \<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. False)) t
   \<lbrace>\<lambda>rv. valid_queues' \<rbrace>"
   unfolding valid_queues'_def
   apply (rule hoare_pre)
    apply (wp hoare_vcg_all_lift)
    apply (simp only: imp_conv_disj not_obj_at')
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
   apply (simp add: not_obj_at')
   apply (clarsimp simp: typ_at_tcb')
   apply normalise_obj_at'
   apply (fastforce elim: obj_at'_weaken simp: inQ_def)
   done

lemma setQueue_ksReadyQueues_lift:
  "\<lbrace> \<lambda>s. P (s\<lparr>ksReadyQueues := (ksReadyQueues s)((d, p) := ts)\<rparr>) ts \<rbrace>
   setQueue d p ts
   \<lbrace> \<lambda>_ s. P s (ksReadyQueues s (d,p))\<rbrace>"
  unfolding setQueue_def
  by (wp, clarsimp simp: fun_upd_def snd_def)

lemma tcbSchedDequeue_valid_queues'[wp]:
  "\<lbrace>valid_queues'\<rbrace>
    tcbSchedDequeue t \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (rule_tac B="\<lambda>rv. valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
   prefer 2
   apply (wp threadGet_wp)
   apply (fastforce simp: obj_at'_def)
  apply clarsimp
  apply (rename_tac queued)
  apply (case_tac queued, simp_all)
   apply wp
        apply (rule_tac d=tdom and p=prio in threadSet_valid_queues'_dequeue)
       apply (rule hoare_pre_post, assumption)
       apply (wp | clarsimp simp: bitmap_fun_defs)+
      apply (wp hoare_vcg_all_lift setQueue_ksReadyQueues_lift)
     apply clarsimp
     apply (wp threadGet_obj_at' threadGet_const_tcb_at)+
   apply clarsimp
   apply (rule context_conjI, clarsimp simp: obj_at'_def)
   apply (clarsimp simp: valid_queues'_def obj_at'_def projectKOs inQ_def|wp)+
  done

lemma tcbSchedDequeue_valid_release_queue[wp]:
  "\<lbrace>valid_release_queue\<rbrace>
    tcbSchedDequeue t \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (rule_tac B="\<lambda>rv. valid_release_queue and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
   prefer 2
   apply (wp threadGet_wp)
   apply (fastforce simp: obj_at'_def)
  apply clarsimp
  apply (rename_tac queued)
  apply (case_tac queued, simp_all)
   apply wp
        apply (rule threadSet_valid_release_queue)
       apply (rule hoare_pre_post, assumption)
       apply (wp | clarsimp simp: bitmap_fun_defs valid_release_queue_def)+
      apply (wp hoare_vcg_all_lift setQueue_ksReadyQueues_lift)
     apply clarsimp
     apply (wp threadGet_obj_at' threadGet_const_tcb_at)+
   apply clarsimp
   apply (rule context_conjI, clarsimp simp: obj_at'_def)
   apply (clarsimp simp: valid_release_queue_def obj_at'_def projectKOs inQ_def|wp)+
  done

lemma tcbSchedDequeue_valid_release_queue'[wp]:
  "\<lbrace>valid_release_queue'\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (rule_tac B="\<lambda>rv. valid_release_queue' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
   prefer 2
   apply (wp threadGet_wp)
   apply (fastforce simp: obj_at'_def)
  apply clarsimp
  apply (rename_tac queued)
  apply (case_tac queued, simp_all)
   apply wp
        apply (rule threadSet_valid_release_queue')
       apply (rule hoare_pre_post, assumption)
       apply (wp | clarsimp simp: bitmap_fun_defs valid_release_queue'_def)+
      apply (wp hoare_vcg_all_lift setQueue_ksReadyQueues_lift)
     apply clarsimp
     apply (wp threadGet_obj_at' threadGet_const_tcb_at)+
   apply clarsimp
   apply (rule context_conjI, clarsimp simp: obj_at'_def)
   apply (clarsimp simp: valid_release_queue'_def obj_at'_def projectKOs inQ_def|wp)+
  done

crunch tcb_at'[wp]: tcbSchedAppend "tcb_at' t"
  (simp: unless_def)

crunch state_refs_of'[wp]: tcbSchedAppend "\<lambda>s. P (state_refs_of' s)"
  (wp: refl simp: crunch_simps unless_def)
crunch state_refs_of'[wp]: tcbSchedDequeue "\<lambda>s. P (state_refs_of' s)"
  (wp: refl simp: crunch_simps)

crunch cap_to'[wp]: tcbSchedEnqueue "ex_nonz_cap_to' p"
  (simp: unless_def)
crunch cap_to'[wp]: tcbSchedAppend "ex_nonz_cap_to' p"
  (simp: unless_def)
crunch cap_to'[wp]: tcbSchedDequeue "ex_nonz_cap_to' p"

lemma tcbSchedAppend_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' tcb\<rbrace>
    tcbSchedAppend tcb \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedAppend_def unless_def)
  apply (wp threadSet_iflive' hoare_drop_imps | simp add: crunch_simps)+
  done

lemma tcbSchedDequeue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> tcbSchedDequeue tcb \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadSet_iflive' hoare_when_weak_wp | simp add: crunch_simps)+
       apply ((wp | clarsimp simp: bitmap_fun_defs)+)[1] (* deal with removeFromBitmap *)
      apply (wp threadSet_iflive' hoare_when_weak_wp | simp add: crunch_simps)+
      apply (rule_tac Q="\<lambda>rv. \<top>" in hoare_post_imp, fastforce)
      apply (wp | simp add: crunch_simps)+
  done

crunch ifunsafe'[wp]: tcbSchedEnqueue if_unsafe_then_cap'
  (simp: unless_def)
crunch ifunsafe'[wp]: tcbSchedAppend if_unsafe_then_cap'
  (simp: unless_def)
crunch ifunsafe'[wp]: tcbSchedDequeue if_unsafe_then_cap'

crunch idle'[wp]: tcbSchedAppend valid_idle'
  (simp: crunch_simps unless_def)

crunch global_refs'[wp]: tcbSchedEnqueue valid_global_refs'
  (wp: threadSet_global_refs simp: unless_def)
crunch global_refs'[wp]: tcbSchedAppend valid_global_refs'
  (wp: threadSet_global_refs simp: unless_def)
crunch global_refs'[wp]: tcbSchedDequeue valid_global_refs'
  (wp: threadSet_global_refs)

crunch irq_node'[wp]: tcbSchedAppend "\<lambda>s. P (irq_node' s)"
  (simp: unless_def)
crunch irq_node'[wp]: tcbSchedDequeue "\<lambda>s. P (irq_node' s)"

crunch typ_at'[wp]: tcbSchedAppend "\<lambda>s. P (typ_at' T p s)"
  (simp: unless_def)
crunch ctes_of[wp]: tcbSchedAppend "\<lambda>s. P (ctes_of s)"
  (simp: unless_def)

crunch ksInterrupt[wp]: tcbSchedAppend "\<lambda>s. P (ksInterruptState s)"
  (simp: unless_def)
crunch ksInterrupt[wp]: tcbSchedDequeue "\<lambda>s. P (ksInterruptState s)"

crunch irq_states[wp]: tcbSchedAppend valid_irq_states'
  (simp: unless_def)
crunch irq_states[wp]: tcbSchedDequeue valid_irq_states'

crunch ct'[wp]: tcbSchedAppend "\<lambda>s. P (ksCurThread s)"
  (simp: unless_def)
crunch pde_mappings'[wp]: tcbSchedAppend "valid_pde_mappings'"
  (simp: unless_def)
crunch pde_mappings'[wp]: tcbSchedDequeue "valid_pde_mappings'"

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
  apply (wp static_imp_wp hoare_vcg_disj_lift | assumption)+
  done

lemma tcbSchedEnqueue_invs'[wp]:
  "\<lbrace>invs'
    and st_tcb_at' runnable' t
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
     tcbSchedEnqueue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (wpsimp wp: tcbSchedEnqueue_ct_not_inQ valid_irq_node_lift irqs_masked_lift
                    valid_irq_handlers_lift' cur_tcb_lift untyped_ranges_zero_lift
              simp: cteCaps_of_def o_def)
  apply (auto elim!: st_tcb_ex_cap'')
  done

crunch ksMachine[wp]: tcbSchedAppend "\<lambda>s. P (ksMachineState s)"
  (simp: unless_def)

lemma tcbSchedAppend_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift tcbSchedAppend_ksMachine)
  done

crunch pspace_domain_valid[wp]: tcbSchedAppend "pspace_domain_valid"
  (simp: unless_def)

crunch ksCurDomain[wp]: tcbSchedAppend "\<lambda>s. P (ksCurDomain s)"
(simp: unless_def)

crunch ksIdleThread[wp]: tcbSchedAppend "\<lambda>s. P (ksIdleThread s)"
(simp: unless_def)

crunch ksDomSchedule[wp]: tcbSchedAppend "\<lambda>s. P (ksDomSchedule s)"
(simp: unless_def)

lemma tcbSchedAppend_tcbDomain[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>
     tcbSchedAppend t
   \<lbrace> \<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  apply (wpsimp simp: unless_def)+
  done

lemma tcbSchedAppend_tcbPriority[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>
     tcbSchedAppend t
   \<lbrace> \<lambda>_. obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  apply (wpsimp simp: unless_def)+
  done

lemma tcbSchedAppend_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

crunches tcbSchedAppend, tcbSchedDequeue
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (simp: unless_def)

lemma tcbSchedAppend_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace> tcbSchedAppend thread
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add:tcbSchedAppend_def bitmap_fun_defs)
  apply (wp hoare_unless_wp setQueue_sch_act threadGet_wp|simp)+
  apply (fastforce simp:typ_at'_def obj_at'_def)
  done

crunches tcbSchedAppend
  for list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"

lemma tcbSchedAppend_valid_release_queue[wp]:
  "tcbSchedAppend t \<lbrace>valid_release_queue\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp simp: valid_release_queue_def Ball_def addToBitmap_def
                      modifyReadyQueuesL2Bitmap_def getReadyQueuesL2Bitmap_def
                      modifyReadyQueuesL1Bitmap_def getReadyQueuesL1Bitmap_def
                  wp: hoare_vcg_all_lift hoare_vcg_imp_lift' threadGet_wp)
  by (auto simp: obj_at'_def)

crunches addToBitmap
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

lemma tcbSchedAppend_valid_release_queue'[wp]:
  "tcbSchedAppend t \<lbrace>valid_release_queue'\<rbrace>"
  unfolding tcbSchedAppend_def threadGet_def
  apply (wpsimp simp: valid_release_queue'_def
                  wp: threadSet_valid_release_queue' hoare_vcg_all_lift hoare_vcg_imp_lift'
                      getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbSchedAppend_invs'[wp]:
  "\<lbrace>invs'
    and st_tcb_at' runnable' t
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
     tcbSchedAppend t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (rule hoare_pre)
   apply (wp tcbSchedAppend_ct_not_inQ valid_irq_node_lift irqs_masked_lift hoare_vcg_disj_lift
             valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
             untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def
        | auto elim!: st_tcb_ex_cap'' valid_objs'_maxDomain valid_objs'_maxPriority split: thread_state.split_asm simp: valid_pspace'_def)+
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

lemma valid_queues'_ko_atD:
  "valid_queues' s \<Longrightarrow> ko_at' tcb t s \<Longrightarrow> tcbQueued tcb
    \<Longrightarrow> t \<in> set (ksReadyQueues s (tcbDomain tcb, tcbPriority tcb))"
  apply (simp add: valid_queues'_def)
  apply (elim allE, erule mp)
  apply normalise_obj_at'
  apply (simp add: inQ_def)
  done

lemma tcbSchedEnqueue_in_ksQ:
  "\<lbrace>valid_queues' and tcb_at' t\<rbrace> tcbSchedEnqueue t
   \<lbrace>\<lambda>r s. \<exists>domain priority. t \<in> set (ksReadyQueues s (domain, priority))\<rbrace>"
  apply (rule_tac Q="\<lambda>s. \<exists>d p. valid_queues' s \<and>
                             obj_at' (\<lambda>tcb. tcbPriority tcb = p) t s \<and>
                             obj_at' (\<lambda>tcb. tcbDomain tcb = d) t s"
           in hoare_pre_imp)
   apply (clarsimp simp: tcb_at'_has_tcbPriority tcb_at'_has_tcbDomain)
  apply (rule hoare_vcg_ex_lift)+
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wpsimp simp: if_apply_def2)
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
  apply (frule(1) valid_queues'_ko_atD, simp+)
  done

crunch ksMachine[wp]: tcbSchedDequeue "\<lambda>s. P (ksMachineState s)"
  (simp: unless_def)

lemma tcbSchedDequeue_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift tcbSchedDequeue_ksMachine)
  done

crunch pspace_domain_valid[wp]: tcbSchedDequeue "pspace_domain_valid"

crunch ksCurDomain[wp]: tcbSchedDequeue "\<lambda>s. P (ksCurDomain s)"
(simp: unless_def)

crunch ksIdleThread[wp]: tcbSchedDequeue "\<lambda>s. P (ksIdleThread s)"
(simp: unless_def)

crunch ksDomSchedule[wp]: tcbSchedDequeue "\<lambda>s. P (ksDomSchedule s)"
(simp: unless_def)

lemma tcbSchedDequeue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp
  apply (clarsimp simp: tcbSchedDequeue_def)
  apply (wp hoare_when_weak_wp | simp)+
  done

lemma tcbSchedDequeue_tcbDomain[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>
     tcbSchedDequeue t
   \<lbrace> \<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>"
  apply (clarsimp simp: tcbSchedDequeue_def)
  apply (wp hoare_when_weak_wp | simp)+
  done

lemma tcbSchedDequeue_tcbPriority[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>
     tcbSchedDequeue t
   \<lbrace> \<lambda>_. obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>"
  apply (clarsimp simp: tcbSchedDequeue_def)
  apply (wp hoare_when_weak_wp | simp)+
  done

lemma tcbSchedDequeue_invs'[wp]:
  "\<lbrace>invs'\<rbrace>
     tcbSchedDequeue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def
  apply (rule hoare_pre)
   apply (wp tcbSchedDequeue_ct_not_inQ sch_act_wf_lift valid_irq_node_lift irqs_masked_lift
             valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
             tcbSchedDequeue_valid_queues
             untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def valid_dom_schedule'_def)+
  apply (auto simp: valid_pspace'_def obj_at'_def
              dest: valid_objs'_maxDomain[where t=t] valid_objs'_maxPriority[where t=t])
  done

lemma cur_thread_update_corres:
  "corres dc (pspace_aligned and pspace_distinct and valid_ready_qs) \<top>
             (modify (cur_thread_update (\<lambda>_. t))) (setCurThread t)"
  apply add_ready_qs_runnable
  apply (unfold setCurThread_def)
  apply (rule corres_stateAssert_add_assertion[rotated]; clarsimp)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma arch_switch_thread_tcb_at' [wp]:
  "Arch.switchToThread t \<lbrace>\<lambda>s. P (tcb_at' t s)\<rbrace>"
  by (unfold ARM_H.switchToThread_def, wp typ_at_lifts)

crunch typ_at'[wp]: "switchToThread" "\<lambda>s. P (typ_at' T p s)"
  (ignore: clearExMonitor)

lemma Arch_switchToThread_pred_tcb'[wp]:
  "\<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>
   Arch.switchToThread t \<lbrace>\<lambda>rv s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P t t'. \<lbrace>pred_tcb_at' proj P t'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. pred_tcb_at' proj P t'\<rbrace>"
    apply (simp add:  pred_tcb_at'_def ARM_H.switchToThread_def)
    apply (rule hoare_seq_ext)+
       apply (rule doMachineOp_obj_at)
     apply (rule setVMRoot_obj_at)
    done
  show ?thesis
    apply (rule P_bool_lift [OF pos])
    by (rule lift_neg_pred_tcb_at' [OF ArchThreadDecls_H_ARM_H_switchToThread_typ_at' pos])
qed

crunches doMachineOp
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"

crunch ksQ[wp]: storeWordUser "\<lambda>s. P (ksReadyQueues s p)"
crunch ksQ[wp]: setVMRoot "\<lambda>s. P (ksReadyQueues s)"
(wp: crunch_wps simp: crunch_simps)
crunch ksIdleThread[wp]: storeWordUser "\<lambda>s. P (ksIdleThread s)"
crunch ksIdleThread[wp]: asUser "\<lambda>s. P (ksIdleThread s)"
(wp: crunch_wps simp: crunch_simps)
crunch ksQ[wp]: asUser "\<lambda>s. P (ksReadyQueues s p)"
(wp: crunch_wps simp: crunch_simps)

lemma arch_switch_thread_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s p)\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  apply (wp)
  done

crunch valid_queues[wp]: "Arch.switchToThread" "Invariants_H.valid_queues"
(wp: crunch_wps simp: crunch_simps ignore: clearExMonitor)

crunches arch_switch_to_thread
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct

lemma switch_thread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct and valid_ready_qs
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs o caps_of_state
                and st_tcb_at runnable t)
             (valid_arch_state' and valid_pspace' and Invariants_H.valid_queues
                and st_tcb_at' runnable' t and cur_tcb')
             (switch_to_thread t) (switchToThread t)"
  (is "corres _ ?PA ?PH _ _")

proof -
  have mainpart: "corres dc (?PA) (?PH)
     (do y \<leftarrow> arch_switch_to_thread t;
         y \<leftarrow> (tcb_sched_action tcb_sched_dequeue t);
         modify (cur_thread_update (\<lambda>_. t))
      od)
     (do y \<leftarrow> Arch.switchToThread t;
         y \<leftarrow> tcbSchedDequeue t;
         setCurThread t
      od)"
    apply (rule corres_guard_imp)
      apply (rule corres_split_deprecated [OF _ arch_switch_thread_corres])
        apply (rule corres_split_deprecated[OF cur_thread_update_corres tcbSchedDequeue_corres])
         apply (wpsimp wp: tcb_sched_dequeue_valid_ready_qs | clarsimp simp: st_tcb_at_tcb_at)+
    done

  show ?thesis
    apply -
    apply (simp add: switch_to_thread_def Thread_H.switchToThread_def)
    apply add_ready_qs_runnable
    apply (rule corres_stateAssert_add_assertion)
     apply (rule corres_symb_exec_l[where Q = "\<lambda> s rv. (?PA and (=) rv) s"])
        apply (rule corres_symb_exec_l)
           apply (rule corres_guard_imp[OF mainpart])
            apply (auto intro: no_fail_pre [OF no_fail_assert] no_fail_pre [OF no_fail_get]
                         dest: st_tcb_at_tcb_at [THEN get_tcb_at]
                   | simp add: assert_def
                   | wp)+
    done
qed

lemma arch_switch_idle_thread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map and unique_table_refs \<circ> caps_of_state and
      valid_vs_lookup and valid_global_objs and pspace_aligned and pspace_distinct and valid_vspace_objs and valid_idle)
     (valid_arch_state' and pspace_aligned' and pspace_distinct' and no_0_obj' and valid_idle')
        arch_switch_to_idle_thread
        Arch.switchToIdleThread"
  apply (simp add: arch_switch_to_idle_thread_def
                ARM_H.switchToIdleThread_def)
  apply (corressimp corres: git_corres set_vm_root_corres[@lift_corres_args])
  apply (clarsimp simp: valid_idle_def valid_idle'_def pred_tcb_at_def obj_at_def is_tcb obj_at'_def)
  done

crunches switchToIdleThread
  for ready_qs_runnable[wp]: "\<lambda>s. \<forall>d p. \<forall>t\<in>set (ksReadyQueues s (d, p)).
                       st_tcb_at' runnable' t s"

lemma switch_idle_thread_corres:
  "corres dc (invs and valid_sched) invs_no_cicd' switch_to_idle_thread switchToIdleThread"
  apply add_ready_qs_runnable
  apply (simp add: switch_to_idle_thread_def Thread_H.switchToIdleThread_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [OF _ git_corres])
      apply (rule corres_split_deprecated [OF _ arch_switch_idle_thread_corres])
        apply (unfold setCurThread_def)
        apply (rule corres_stateAssert_add_assertion)
         apply clarsimp
         apply (rule corres_modify)
        apply (simp add: state_relation_def cdt_relation_def)
        apply (simp only: ready_qs_runnable_def)
       apply wpsimp+
   apply (simp add: invs_unique_refs invs_valid_vs_lookup invs_valid_objs invs_valid_asid_map
                    invs_arch_state invs_valid_global_objs invs_psp_aligned invs_distinct
                    invs_valid_idle invs_vspace_objs)
  apply (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def
                   valid_pspace'_def ready_qs_runnable_def)
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
                              valid_state'_def  valid_queues_def valid_release_queue_def
                              valid_release_queue'_def sch_act_wf ct_in_state'_def
                              state_refs_of'_def ps_clear_def valid_irq_node'_def valid_queues'_def
                              ct_not_inQ_ct  ct_idle_or_in_cur_domain'_def
                              bitmapQ_defs valid_queues_no_bitmap_def valid_dom_schedule'_def
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

lemma valid_queues_not_runnable_not_queued:
  fixes s
  assumes  vq: "valid_queues s"
      and rqr: "\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s)"
      and vq': "valid_queues' s"
      and  st: "st_tcb_at' (Not \<circ> runnable') t s"
  shows "obj_at' (Not \<circ> tcbQueued) t s"
proof (rule ccontr)
  assume "\<not> obj_at' (Not \<circ> tcbQueued) t s"
  moreover from st have "typ_at' TCBT t s"
    by (rule pred_tcb_at' [THEN tcb_at_typ_at' [THEN iffD1]])
  ultimately have "obj_at' tcbQueued t s"
    by (clarsimp simp: not_obj_at' comp_def)

  moreover
  from st [THEN pred_tcb_at', THEN tcb_at'_has_tcbPriority]
  obtain p where tp: "obj_at' (\<lambda>tcb. tcbPriority tcb = p) t s"
    by clarsimp

  moreover
  from st [THEN pred_tcb_at', THEN tcb_at'_has_tcbDomain]
  obtain d where td: "obj_at' (\<lambda>tcb. tcbDomain tcb = d) t s"
    by clarsimp

  ultimately
  have "t \<in> set (ksReadyQueues s (d, p))" using vq'
    unfolding valid_queues'_def
    apply -
    apply (drule_tac x=d in spec)
    apply (drule_tac x=p in spec)
    apply (drule_tac x=t in spec)
    apply (erule impE)
     apply (fastforce simp add: inQ_def obj_at'_def)
    apply (assumption)
    done

  with vq rqr have "st_tcb_at' runnable' t s"
    unfolding Invariants_H.valid_queues_def valid_queues_no_bitmap_def
    apply -
    apply clarsimp
    done

  with st show False
    apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
    done
qed

(*
 * The idle thread is not part of any ready queues.
 *)
lemma idle'_not_tcbQueued':
 assumes   vq:  "Invariants_H.valid_queues s"
     and  rqr:  "\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s)"
     and  vq':  "valid_queues' s"
     and idle: "valid_idle' s"
 shows "obj_at' (Not \<circ> tcbQueued) (ksIdleThread s) s"
 proof -
   from idle have stidle: "st_tcb_at' (Not \<circ> runnable') (ksIdleThread s) s"
     by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs idle_tcb'_def)

   with vq rqr vq' show ?thesis
     by (rule valid_queues_not_runnable_not_queued)
 qed

lemma setCurThread_invs_no_cicd'_idle_thread:
  "\<lbrace>invs_no_cicd' and (\<lambda>s. t = ksIdleThread s) \<rbrace> setCurThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have ct_not_inQ_ct: "\<And>s t . \<lbrakk> ct_not_inQ s; obj_at' (\<lambda>x. \<not> tcbQueued x) t s\<rbrakk> \<Longrightarrow> ct_not_inQ (s\<lparr> ksCurThread := t \<rparr>)"
    apply (simp add: ct_not_inQ_def o_def)
    done
  have idle'_activatable': "\<And> s t. st_tcb_at' idle' t s \<Longrightarrow> st_tcb_at' activatable' t s"
    apply (clarsimp simp: st_tcb_at'_def o_def obj_at'_def)
  done
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (clarsimp simp add: ct_not_inQ_ct idle'_activatable' idle'_not_tcbQueued'[simplified o_def]
                              invs'_def cur_tcb'_def valid_state'_def
                              sch_act_wf ct_in_state'_def state_refs_of'_def
                              ps_clear_def valid_irq_node'_def
                              ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                              valid_queues_def bitmapQ_defs valid_queues_no_bitmap_def valid_queues'_def
                              valid_release_queue_def valid_release_queue'_def valid_dom_schedule'_def
                              all_invs_but_ct_idle_or_in_cur_domain'_def pred_tcb_at'_def
                              ready_qs_runnable_def
                        cong: option.case_cong
                       dest!: valid_idle'_tcb_at')
    apply (clarsimp simp: obj_at'_def projectKOs idle_tcb'_def)
    done
qed

lemma clearExMonitor_invs'[wp]:
  "doMachineOp ARM.clearExMonitor \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done

lemma Arch_switchToThread_invs[wp]:
  "\<lbrace>invs'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  apply (wp; auto)
  done

crunch ksCurDomain[wp]: "Arch.switchToThread" "\<lambda>s. P (ksCurDomain s)"
(simp: crunch_simps)

lemma Arch_swichToThread_tcbDomain_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>"
  apply (clarsimp simp: ARM_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_swichToThread_tcbPriority_triv[wp]:
  "\<lbrace> obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace> Arch.switchToThread t \<lbrace> \<lambda>_. obj_at'  (\<lambda>tcb. P (tcbPriority tcb)) t' \<rbrace>"
  apply (clarsimp simp: ARM_H.switchToThread_def storeWordUser_def)
  apply (wp hoare_drop_imp | simp)+
  done

lemma Arch_switchToThread_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

lemma tcbSchedDequeue_not_tcbQueued:
  "\<lbrace> tcb_at' t \<rbrace> tcbSchedDequeue t \<lbrace> \<lambda>_. obj_at' (\<lambda>x. \<not> tcbQueued x) t \<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp|clarsimp)+
  apply (rule_tac Q="\<lambda>queued. obj_at' (\<lambda>x. tcbQueued x = queued) t" in hoare_post_imp)
   apply (clarsimp simp: obj_at'_def)
  apply (wp threadGet_obj_at')
  apply (simp)
  done

lemma Arch_switchToThread_obj_at[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (P \<circ> tcbState) t\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def )
  apply (rule hoare_seq_ext)+
   apply (rule doMachineOp_obj_at)
  apply (rule setVMRoot_obj_at)
  done

declare doMachineOp_obj_at[wp]

lemma clearExMonitor_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp ARM.clearExMonitor \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wp dmo_invs_no_cicd' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done

crunch valid_arch_state'[wp]: asUser "valid_arch_state'"
(wp: crunch_wps simp: crunch_simps)

crunch valid_irq_states'[wp]: asUser "valid_irq_states'"
(wp: crunch_wps simp: crunch_simps)

crunch valid_machine_state'[wp]: asUser "valid_machine_state'"
(wp: crunch_wps simp: crunch_simps)

crunch valid_queues'[wp]: asUser "valid_queues'"
(wp: crunch_wps simp: crunch_simps)


crunch irq_masked'_helper: asUser "\<lambda>s. P (intStateIRQTable (ksInterruptState s))"
(wp: crunch_wps simp: crunch_simps)

crunch valid_pde_mappings'[wp]: asUser "valid_pde_mappings'"
(wp: crunch_wps simp: crunch_simps)

crunch pspace_domain_valid[wp]: asUser "pspace_domain_valid"
(wp: crunch_wps simp: crunch_simps)

crunch valid_dom_schedule'[wp]: asUser "valid_dom_schedule'"
(wp: crunch_wps simp: crunch_simps)

crunch gsUntypedZeroRanges[wp]: asUser "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: unless_def)

crunch ctes_of[wp]: asUser "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: unless_def)

lemmas asUser_cteCaps_of[wp] = cteCaps_of_ctes_of_lift[OF asUser_ctes_of]

lemma Arch_switchToThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  by (wp|rule setVMRoot_invs_no_cicd')+


lemma tcbSchedDequeue_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace>
     tcbSchedDequeue t
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_dom_schedule'_def
  apply (wp tcbSchedDequeue_ct_not_inQ sch_act_wf_lift valid_irq_node_lift irqs_masked_lift
            valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
            tcbSchedDequeue_valid_queues_weak
            untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def)+
  apply (fastforce simp: valid_pspace'_def valid_queues_def
                   elim: valid_objs'_maxDomain valid_objs'_maxPriority intro: obj_at'_conjI)
  done

lemma switchToThread_invs'_helper:
  "\<lbrace>invs_no_cicd' and st_tcb_at' runnable' t and tcb_in_cur_domain' t \<rbrace>
   do y <- ARM_H.switchToThread t;
      y <- tcbSchedDequeue t;
      setCurThread t
   od
   \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (wp setCurThread_invs_no_cicd' tcbSchedDequeue_not_tcbQueued
            Arch_switchToThread_invs_no_cicd' Arch_switchToThread_pred_tcb')
  apply (auto elim!: pred_tcb'_weakenE)
  done

lemma switchToThread_invs[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t and tcb_in_cur_domain' t \<rbrace> switchToThread t \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: Thread_H.switchToThread_def )
  apply (wp  setCurThread_invs
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
  apply (simp add: Thread_H.switchToThread_def tcbSchedEnqueue_def unless_def)
  apply (wp setCurThread_ct_in_state Arch_switchToThread_obj_at
         | simp add: o_def cong: if_cong)+
  done

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
  apply (wp ex_nonz_cap_to_pres')
   apply (clarsimp elim!: cte_wp_at'_pspaceI)+
  done


crunch cap_to'[wp]: "Arch.switchToThread" "ex_nonz_cap_to' p"
  (simp: crunch_simps ignore: ARM.clearExMonitor)

crunch cap_to'[wp]: switchToThread "ex_nonz_cap_to' p"
  (simp: crunch_simps ignore: ARM.clearExMonitor)

lemma iflive_inQ_nonz_cap_strg:
  "if_live_then_nonz_cap' s \<and> obj_at' (inQ d prio) t s
          \<longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: obj_at'_real_def projectKOs inQ_def
              elim!: if_live_then_nonz_capE' ko_wp_at'_weakenE)

lemmas iflive_inQ_nonz_cap[elim]
    = mp [OF iflive_inQ_nonz_cap_strg, OF conjI[rotated]]

declare Cons_eq_tails[simp]

crunch ksCurDomain[wp]: "ThreadDecls_H.switchToThread" "\<lambda>s. P (ksCurDomain s)"

(* FIXME move *)
lemma obj_tcb_at':
  "obj_at' (\<lambda>tcb::tcb. P tcb) t s \<Longrightarrow> tcb_at' t s"
  by (clarsimp simp: obj_at'_def)

lemma valid_queues_not_tcbQueued_not_ksQ:
  fixes s
  assumes   vq: "valid_queues s"
      and notq: "obj_at' (Not \<circ> tcbQueued) t s"
  shows "\<forall>d p. t \<notin> set (ksReadyQueues s (d, p))"
proof (rule ccontr, simp , erule exE, erule exE)
  fix d p
  assume "t \<in> set (ksReadyQueues s (d, p))"
  with vq have "obj_at' (inQ d p) t s"
    by (fastforce intro: valid_queues_obj_at'D)
  hence "obj_at' tcbQueued t s"
    apply (rule obj_at'_weakenE)
    apply (simp only: inQ_def)
    done
  with notq show "False"
    by (clarsimp simp: obj_at'_def)
qed

lemma not_tcbQueued_not_ksQ:
  fixes s
  assumes "invs' s"
      and "obj_at' (Not \<circ> tcbQueued) t s"
  shows "\<forall>d p. t \<notin> set (ksReadyQueues s (d, p))"
  apply (insert assms)
  apply (clarsimp simp add: invs'_def valid_state'_def)
  apply (drule(1) valid_queues_not_tcbQueued_not_ksQ)
  apply clarsimp
  done

lemma ct_not_ksQ:
  "\<lbrakk> invs' s; ksSchedulerAction s = ResumeCurrentThread \<rbrakk>
   \<Longrightarrow> \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p)"
  apply (clarsimp simp: invs'_def valid_state'_def ct_not_inQ_def)
  apply (frule(1) valid_queues_not_tcbQueued_not_ksQ)
  apply (fastforce)
  done

lemma scheduleTCB_rct:
  "\<lbrace>\<lambda>s. (t = ksCurThread s \<longrightarrow> isSchedulable_bool t s)
        \<and> ksSchedulerAction s = ResumeCurrentThread\<rbrace>
   scheduleTCB t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  unfolding scheduleTCB_def
  by (wpsimp wp: isSchedulable_wp | rule hoare_pre_cont)+

lemma setThreadState_rct:
  "\<lbrace>\<lambda>s. (t = ksCurThread s \<longrightarrow> runnable' st
      \<and> pred_map (\<lambda>tcb. \<not>(tcbInReleaseQueue tcb)) (tcbs_of' s) t
      \<and> pred_map (\<lambda>scPtr. isScActive scPtr s) (tcbSCs_of s) t)
        \<and> ksSchedulerAction s = ResumeCurrentThread\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  unfolding setThreadState_def
  by (wpsimp wp: scheduleTCB_rct hoare_vcg_all_lift hoare_vcg_imp_lift' threadSet_isSchedulable_bool)

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
   apply (fastforce intro: word_of_nat_less simp: wordRadix_def' unat_of_nat word_size)+
  apply (subst unat_of_nat_eq)
   apply (fastforce intro: word_log2_max[THEN order_less_le_trans] simp: word_size)+
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
  "\<lbrakk>ksReadyQueuesL1Bitmap s (ksCurDomain s) \<noteq> 0; valid_queues_no_bitmap s; valid_bitmapQ s;
    \<forall>d p. \<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s;
    bitmapQ_no_L1_orphans s\<rbrakk>
   \<Longrightarrow> obj_at' (inQ (ksCurDomain s) (lookupBitmapPriority (ksCurDomain s) s) and runnable' \<circ> tcbState)
               (hd (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s))) s"
  apply (drule (2) bitmapQ_from_bitmap_lookup)
  apply (simp add: valid_bitmapQ_bitmapQ_simp)
  apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)", simp)
  apply (clarsimp, rename_tac t ts)
  apply (drule cons_set_intro)
  apply (fastforce simp: valid_queues_no_bitmap_def inQ_def obj_at'_def projectKOs st_tcb_at'_def)
  done

lemma bitmapL1_zero_ksReadyQueues:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s \<rbrakk>
   \<Longrightarrow> (ksReadyQueuesL1Bitmap s d = 0) = (\<forall>p. ksReadyQueues s (d,p) = [])"
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
    apply (simp add: word_size)
    apply (drule (1) bitmapQ_no_L1_orphansD[where d=d and i="word_log2 _"])
    apply (simp add: numPriorities_def wordBits_def word_size l2BitmapSize_def')
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
                    simp: wordBits_def numPriorities_def word_size l2BitmapSize_def')
  apply (erule word_log2_highest)
  done

lemma bitmapQ_ksReadyQueuesI:
  "\<lbrakk> bitmapQ d p s ; valid_bitmapQ s \<rbrakk> \<Longrightarrow> ksReadyQueues s (d, p) \<noteq> []"
  unfolding valid_bitmapQ_def by simp

lemma getReadyQueuesL2Bitmap_inv[wp]:
  "\<lbrace> P \<rbrace> getReadyQueuesL2Bitmap d i \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding getReadyQueuesL2Bitmap_def by wp

lemma switchToThread_lookupBitmapPriority_wp:
  "\<lbrace>\<lambda>s. invs_no_cicd' s \<and> bitmapQ (ksCurDomain s) (lookupBitmapPriority (ksCurDomain s) s) s \<and>
        t = hd (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)) \<rbrace>
   ThreadDecls_H.switchToThread t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have switchToThread_pre:
    "\<And>s p t.\<lbrakk> valid_queues s ; \<forall>d p. \<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s;
              bitmapQ (ksCurDomain s) p s ; t = hd (ksReadyQueues s (ksCurDomain s, p)) \<rbrakk>
            \<Longrightarrow> st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s"
    unfolding valid_queues_def
    apply (clarsimp dest!: bitmapQ_ksReadyQueuesI)
    apply (case_tac "ksReadyQueues s (ksCurDomain s, p)", simp)
    apply (rename_tac t ts)
    apply (drule_tac t=t and p=p and d="ksCurDomain s" in valid_queues_no_bitmap_objD)
     apply simp
    apply (fastforce intro: cons_set_intro
                      elim: obj_at'_weaken
                      simp: inQ_def tcb_in_cur_domain'_def)
    done
  thus ?thesis
    apply (simp add: Thread_H.switchToThread_def)
    apply (rule hoare_seq_ext[OF _ stateAssert_sp])
    apply (wp switchToThread_invs'_helper)
    apply (fastforce simp: ready_qs_runnable_def dest: invs_no_cicd'_queues)
    done
qed

lemma switchToIdleThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (clarsimp simp: Thread_H.switchToIdleThread_def ARM_H.switchToIdleThread_def)
  apply (wp setCurThread_invs_no_cicd'_idle_thread setVMRoot_invs_no_cicd')
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_idle'_def)
  done

crunch obj_at'[wp]: "Arch.switchToIdleThread" "\<lambda>s. obj_at' P t s"


declare static_imp_conj_wp[wp_split del]

lemma setCurThread_const:
  "\<lbrace>\<lambda>_. P t \<rbrace> setCurThread t \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>"
  by (simp add: setCurThread_def | wp)+



crunches switchToIdleThread, switchToThread, chooseThread
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)

lemma switchToIdleThread_curr_is_idle:
  "\<lbrace>\<top>\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv s. ksCurThread s = ksIdleThread s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (wps switchToIdleThread_it)
   apply (simp add: Thread_H.switchToIdleThread_def)
   apply (wp setCurThread_const)
  apply (simp)
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

crunch cur[wp]: tcbSchedEnqueue cur_tcb'
  (simp: unless_def)

lemma is_schedulable_exs_valid[wp]:
  "active_sc_tcb_at t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> is_schedulable t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: is_schedulable_def exs_valid_def Bex_def pred_map_def vs_all_heap_simps
                 split: option.splits)
  apply (clarsimp simp: in_monad get_tcb_ko_at obj_at_def get_sched_context_def Option.is_none_def
                        get_object_def)
  done

lemma gts_exs_valid[wp]:
  "tcb_at t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_thread_state t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_thread_state_def  assert_opt_def fail_def
             thread_get_def gets_the_def exs_valid_def gets_def
             get_def bind_def return_def split: option.splits)
  apply (erule get_tcb_at)
  done

lemma guarded_switch_to_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs o caps_of_state
                and is_schedulable_bool t and valid_ready_qs)
             (valid_arch_state' and valid_pspace' and Invariants_H.valid_queues
                and st_tcb_at' runnable' t and cur_tcb')
             (guarded_switch_to t) (switchToThread t)"
  apply (simp add: guarded_switch_to_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l'[OF _ thread_get_exs_valid])
      apply (rule corres_assert_opt_assume_l)
      apply (rule corres_symb_exec_l'[OF _ is_schedulable_exs_valid])
        apply (rule corres_assert_assume_l)
        apply (rule switch_thread_corres)
       apply assumption
      apply (wpsimp wp: is_schedulable_wp)
     apply assumption
    apply (wpsimp wp: thread_get_wp')
   apply (clarsimp simp: is_schedulable_bool_def2 tcb_at_kh_simps pred_map_def vs_all_heap_simps
                         obj_at_def is_tcb)
  apply simp
  done

abbreviation "enumPrio \<equiv> [0.e.maxPriority]"

lemma curDomain_corres: "corres (=) \<top> \<top> (gets cur_domain) (curDomain)"
  by (simp add: curDomain_def state_relation_def)

lemma lookupBitmapPriority_Max_eqI:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s ; ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s = (Max {prio. ksReadyQueues s (d, prio) \<noteq> []})"
  apply (rule Max_eqI[simplified eq_commute]; simp)
   apply (fastforce simp: bitmapL1_highest_lookup valid_bitmapQ_bitmapQ_simp)
  apply (metis valid_bitmapQ_bitmapQ_simp bitmapQ_from_bitmap_lookup)
  done

lemma corres_gets_queues_getReadyQueuesL1Bitmap:
  "corres (\<lambda>qs l1. ((l1 = 0) = (\<forall>p. qs p = []))) \<top> valid_queues
    (gets (\<lambda>s. ready_queues s d)) (getReadyQueuesL1Bitmap d)"
  unfolding state_relation_def valid_queues_def getReadyQueuesL1Bitmap_def
  by (clarsimp simp: bitmapL1_zero_ksReadyQueues ready_queues_relation_def)

lemma tcb_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and tcb_at t) (tcb_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) tcb_at_cross)

lemma sc_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and sc_at t) (sc_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) sc_at_cross)

lemma ntfn_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and ntfn_at t) (ntfn_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) ntfn_at_cross)

lemma runnable_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and st_tcb_at runnable t)
             (\<lambda>s'. pred_map (\<lambda>tcb. runnable' (tcbState tcb)) (tcbs_of' s') t)"
  apply (rule cross_rel_imp[OF tcb_at'_cross_rel[where t=t]])
  apply (clarsimp simp: cross_rel_def)
  apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
  apply (clarsimp simp: tcb_at_kh_simps pred_map_def cross_rel_def obj_at'_def)
  apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
  apply (drule_tac x=t in bspec; clarsimp)
  apply (clarsimp simp: other_obj_relation_def split: option.splits)
  apply (case_tac "ko"; simp)
  apply (clarsimp simp: opt_map_def)
  apply (clarsimp simp: tcb_relation_def thread_state_relation_def)
  apply (case_tac "tcb_state b"; simp add: runnable_def)
  apply clarsimp
  apply clarsimp
  done

lemma tcbInReleaseQueue_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and tcb_at t and not_in_release_q t)
             (\<lambda>s'. valid_release_queue' s' \<longrightarrow> pred_map (\<lambda>tcb. \<not> tcbInReleaseQueue tcb) (tcbs_of' s') t)"
  apply (rule cross_rel_imp[OF tcb_at'_cross_rel[where t=t]])
  apply (clarsimp simp: cross_rel_def)
  apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
  apply (clarsimp simp: pred_map_def cross_rel_def obj_at'_def obj_at_def is_tcb)
  apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
  apply (drule_tac x=t in bspec; clarsimp)
  apply (clarsimp simp: other_obj_relation_def split: option.splits)
  apply (case_tac "koa"; simp)
  apply (clarsimp simp: opt_map_def)
  apply (subgoal_tac "obj_at' tcbInReleaseQueue t s'")
  apply (subgoal_tac "release_queue_relation (release_queue s) (ksReleaseQueue s')")
  apply (clarsimp simp: release_queue_relation_def not_in_release_q_def valid_release_queue'_def)
  apply (clarsimp simp: state_relation_def)
  apply (clarsimp simp: obj_at'_def projectKO_eq Bits_R.projectKO_tcb)
  apply clarsimp
  apply clarsimp
  done

lemma isScActive_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_objs and active_sc_tcb_at t)
             (\<lambda>s'. pred_map ((\<lambda>scPtr. isScActive scPtr s')) (tcbSCs_of s') t)"
  apply (rule cross_rel_imp[OF tcb_at'_cross_rel[where t=t]])
   apply (clarsimp simp: cross_rel_def)
   apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
    apply (clarsimp simp: pred_map_def obj_at'_real_def ko_wp_at'_def vs_all_heap_simps)
    apply (subgoal_tac "sc_at' ref' s'")
     apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
     apply (drule_tac x=t in bspec, clarsimp)
     apply (clarsimp simp: other_obj_relation_def split: option.splits)
     apply (rename_tac s s' scp ko' tcb sc n x)
     apply (case_tac "ko'"; simp)
     apply (subgoal_tac "pspace_relation (kheap s) (ksPSpace s')")
      apply (clarsimp simp: vs_all_heap_simps pspace_relation_def)
      apply (drule_tac x=scp in bspec, clarsimp)
      apply (subgoal_tac "valid_sched_context_size n")
       apply (clarsimp simp: other_obj_relation_def split: option.splits)
       apply (clarsimp simp: obj_at'_def projectKO_eq Bits_R.projectKO_sc)
       apply (clarsimp simp: opt_map_def tcb_relation_def)
       apply (rule_tac x=scp in exI, simp)
       apply (clarsimp simp: isScActive_def active_sc_def)
       apply (clarsimp simp: obj_at'_def projectKO_eq Bits_R.projectKO_sc pred_map_def opt_map_def)
       apply (clarsimp simp: sc_relation_def)
      apply (rule_tac sc=sc in  valid_objs_valid_sched_context_size, assumption)
      apply (fastforce)
     apply clarsimp
    apply (erule (2) sc_at_cross)
    apply (clarsimp simp: obj_at_def is_sc_obj_def)
    apply (rule_tac sc=ya in  valid_objs_valid_sched_context_size, assumption)
    apply (fastforce)
   apply clarsimp
  apply (clarsimp simp: obj_at_kh_kheap_simps pred_map_def vs_all_heap_simps is_tcb)
  done

lemma isSchedulable_bool_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_objs and is_schedulable_bool t) (\<lambda>s'. valid_release_queue' s' \<longrightarrow> isSchedulable_bool t s')"
  apply (rule cross_rel_imp[OF isScActive_cross_rel[where t=t]])
   apply (rule cross_rel_imp[OF tcbInReleaseQueue_cross_rel[where t=t]])
    apply (rule cross_rel_imp[OF runnable_cross_rel[where t=t]])
     apply (clarsimp simp: isSchedulable_bool_def pred_map_conj)
    apply (clarsimp simp: is_schedulable_bool_def2)+
  done

lemmas tcb_at'_example = corres_cross[where Q' = "tcb_at' t" for t, OF tcb_at'_cross_rel]

lemma guarded_switch_to_chooseThread_fragment_corres:
  "corres dc
    (P and is_schedulable_bool t and invs and valid_sched)
    (P' and invs_no_cicd' and tcb_at' t)
          (guarded_switch_to t)
          (do schedulable \<leftarrow> isSchedulable t;
              y \<leftarrow> assert schedulable;
              ThreadDecls_H.switchToThread t
           od)"
  apply (rule corres_cross'[OF isSchedulable_bool_cross_rel[where t=t], rotated])
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  unfolding guarded_switch_to_def
  apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l_Ex)
    apply (rule corres_symb_exec_l_Ex)
    apply (rule corres_split_deprecated[OF _ isSchedulable_corres])
      apply (rule corres_assert_assume_l)
      apply (rule corres_assert_assume_r)
      apply (rule switch_thread_corres)
    apply (wpsimp wp: is_schedulable_wp)
    apply (wpsimp wp: isSchedulable_wp)
   apply (prop_tac "st_tcb_at runnable t s \<and> bound_sc_tcb_at bound t s")
    apply (clarsimp simp: is_schedulable_bool_def2 tcb_at_kh_simps pred_map_def vs_all_heap_simps)
   apply (clarsimp simp: st_tcb_at_tcb_at invs_def valid_state_def valid_pspace_def valid_sched_def
                         invs_valid_vs_lookup invs_unique_refs)
   apply (clarsimp simp: thread_get_def in_monad pred_tcb_at_def obj_at_def get_tcb_ko_at)
  apply (prop_tac "st_tcb_at' runnable' t s")
   apply (clarsimp simp: pred_tcb_at'_def isSchedulable_bool_def pred_map_def obj_at'_def
                         projectKO_eq Bits_R.projectKO_tcb
                  split: kernel_object.splits)
  by (auto elim!: pred_tcb'_weakenE split: thread_state.splits
            simp: pred_tcb_at' runnable'_def all_invs_but_ct_idle_or_in_cur_domain'_def)

lemma bitmap_lookup_queue_is_max_non_empty:
  "\<lbrakk> valid_queues s'; (s, s') \<in> state_relation; invs s;
     ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s') =
        max_non_empty_queue (ready_queues s (cur_domain s))"
  unfolding all_invs_but_ct_idle_or_in_cur_domain'_def valid_queues_def
  by (clarsimp simp add: max_non_empty_queue_def lookupBitmapPriority_Max_eqI
                         state_relation_def ready_queues_relation_def)

lemma ksReadyQueuesL1Bitmap_return_wp:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s d) s \<rbrace> getReadyQueuesL1Bitmap d \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getReadyQueuesL1Bitmap_def
  by wp

lemma ksReadyQueuesL1Bitmap_st_tcb_at':
  "\<lbrakk> ksReadyQueuesL1Bitmap s (ksCurDomain s) \<noteq> 0; valid_queues s;
    (\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). st_tcb_at' runnable' t s))\<rbrakk>
   \<Longrightarrow> st_tcb_at' runnable' (hd (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s))) s"
  apply (drule bitmapQ_from_bitmap_lookup; clarsimp simp: valid_queues_def)
  apply (clarsimp simp add: valid_bitmapQ_bitmapQ_simp)
  apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)")
   apply simp
  apply (fastforce intro: cons_set_intro)
  done

lemma chooseThread_corres:
  "corres dc (invs and valid_sched) (invs_no_cicd')
     choose_thread chooseThread" (is "corres _ ?PREI ?PREH _ _")
  apply add_ready_qs_runnable
  unfolding choose_thread_def chooseThread_def numDomains_def
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: ready_qs_runnable_def)
  apply (simp only: numDomains_def return_bind Let_def)
  apply (simp cong: if_cong) (* clean up if 1 < numDomains *)
  apply (subst if_swap[where P="_ \<noteq> 0"]) (* put switchToIdleThread on first branch*)
  apply (rule corres_name_pre)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ curDomain_corres])
      apply clarsimp
      apply (rule corres_split_deprecated[OF _ corres_gets_queues_getReadyQueuesL1Bitmap])
        apply (erule corres_if2[OF sym])
         apply (rule switch_idle_thread_corres)
        apply (rule corres_symb_exec_r)
           apply (rule corres_symb_exec_r)
              apply (rule_tac
                       P="\<lambda>s. ?PREI s \<and> queues = ready_queues s (cur_domain s) \<and>
                              is_schedulable_bool (hd (max_non_empty_queue queues)) s" and
                       P'="\<lambda>s. (?PREH s ) \<and> st_tcb_at' runnable' (hd queue) s \<and>
                               l1 = ksReadyQueuesL1Bitmap s (ksCurDomain s) \<and>
                               l1 \<noteq> 0 \<and>
                               queue = ksReadyQueues s (ksCurDomain s,
                                         lookupBitmapPriority (ksCurDomain s) s)" and
                       F="hd queue = hd (max_non_empty_queue queues)" in corres_req)
               apply (fastforce dest!: invs_no_cicd'_queues simp: bitmap_lookup_queue_is_max_non_empty)
              apply clarsimp
              apply (rule corres_guard_imp)
                apply (rule_tac P=\<top> and P'=\<top> in guarded_switch_to_chooseThread_fragment_corres)
               apply (wp | clarsimp simp: getQueue_def getReadyQueuesL2Bitmap_def)+
      apply (wp hoare_vcg_conj_lift hoare_vcg_imp_lift ksReadyQueuesL1Bitmap_return_wp)
     apply (simp add: curDomain_def, wp)+
   apply (clarsimp simp: valid_sched_def DetSchedInvs_AI.valid_ready_qs_def max_non_empty_queue_def)
   apply (erule_tac x="cur_domain sa" in allE)
   apply (erule_tac x="Max {prio. ready_queues sa (cur_domain sa) prio \<noteq> []}" in allE)
   apply (case_tac "ready_queues sa (cur_domain sa) (Max {prio. ready_queues sa (cur_domain sa) prio \<noteq> []})")
    apply clarsimp
    apply (subgoal_tac
             "ready_queues sa (cur_domain sa) (Max {prio. ready_queues sa (cur_domain sa) prio \<noteq> []}) \<noteq> []")
     apply (fastforce elim!: setcomp_Max_has_prop)
    apply (fastforce elim!: setcomp_Max_has_prop)
   apply (clarsimp simp: tcb_at_kh_simps is_schedulable_bool_def2 released_sc_tcb_at_def)
   apply (subgoal_tac "in_ready_q a sa", fastforce simp: ready_or_release_def)
   apply (clarsimp simp: in_ready_q_def)
    apply (rule_tac x="cur_domain sa" in exI)
    apply (rule_tac x="Max {prio. ready_queues sa (cur_domain sa) prio \<noteq> []}" in exI)
    apply clarsimp
  apply (clarsimp dest!: invs_no_cicd'_queues simp: ready_qs_runnable_def)
  apply (fastforce intro: ksReadyQueuesL1Bitmap_st_tcb_at')
  done

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

lemma domain_time_corres:
  "corres (=) \<top> \<top> (gets domain_time) getDomainTime"
  by (simp add: getDomainTime_def state_relation_def)

lemma \<mu>s_to_ms_equiv:
  "\<mu>s_to_ms = usToMs"
  by (simp add: usToMs_def \<mu>s_to_ms_def)

lemma us_to_ticks_equiv:
  "us_to_ticks = usToTicks"
  by (simp add: usToTicks_def)

lemma reset_work_units_equiv:
  "do_extended_op (modify (work_units_completed_update (\<lambda>_. 0)))
   = (modify (work_units_completed_update (\<lambda>_. 0)))"
  by (clarsimp simp: reset_work_units_def[symmetric])

lemma next_domain_corres:
  "corres dc \<top> \<top> next_domain nextDomain"
  apply (clarsimp simp: next_domain_def nextDomain_def reset_work_units_equiv modify_modify)
  apply (rule corres_modify)
  apply (simp add: state_relation_def Let_def dschLength_def dschDomain_def cdt_relation_def
                   \<mu>s_to_ms_equiv us_to_ticks_equiv)
  done

lemma next_domain_valid_sched[wp]:
  "\<lbrace> valid_sched and (\<lambda>s. scheduler_action s  = choose_new_thread)\<rbrace> next_domain \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: next_domain_def Let_def)
  apply (wp, simp add: valid_sched_def valid_sched_action_2_def ct_not_in_q_2_def)
  apply (fastforce simp: valid_blocked_defs)
  done

lemma nextDomain_invs_no_cicd':
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread)\<rbrace> nextDomain \<lbrace> \<lambda>_. invs_no_cicd' \<rbrace>"
  apply (simp add: nextDomain_def Let_def dschLength_def dschDomain_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def
                        ct_not_inQ_def cur_tcb'_def ct_idle_or_in_cur_domain'_def dschDomain_def
                        all_invs_but_ct_idle_or_in_cur_domain'_def valid_dom_schedule'_def)
  done

lemma schedule_ChooseNewThread_fragment_corres:
  "corres dc (invs and valid_sched and (\<lambda>s. scheduler_action s = choose_new_thread)) (invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread))
     (do _ \<leftarrow> when (domainTime = 0) next_domain;
         choose_thread
      od)
     (do _ \<leftarrow> when (domainTime = 0) nextDomain;
          chooseThread
      od)"
  apply (subst bind_dummy_ret_val)
  apply (subst bind_dummy_ret_val)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ corres_when])
        apply simp
        apply (rule chooseThread_corres)
       apply simp
      apply (rule next_domain_corres)
     apply (wp nextDomain_invs_no_cicd')+
   apply (clarsimp simp: valid_sched_def invs'_def valid_state'_def all_invs_but_ct_idle_or_in_cur_domain'_def)+
  done

lemma schedule_switch_thread_fastfail_corres:
  "\<lbrakk> ct \<noteq> it \<longrightarrow> (tp = tp' \<and> cp = cp') ; ct = ct' ; it = it' \<rbrakk> \<Longrightarrow>
   corres ((=)) (tcb_at ct) (tcb_at' ct)
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
    "corres ((=)) \<top> valid_queues
      (gets (is_highest_prio d p))
      (isHighestPrio d' p')"
  using assms
  apply (clarsimp simp: gets_is_highest_prio_expand isHighestPrio_def)
  apply (subst getHighestPrio_def')
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ corres_gets_queues_getReadyQueuesL1Bitmap])
      apply (rule corres_if_r'[where P'="\<lambda>_. True",rotated])
       apply (rule_tac corres_symb_exec_r)
              apply (rule_tac
                       P="\<lambda>s. q = ready_queues s d
                              " and
                       P'="\<lambda>s. valid_queues s \<and>
                               l1 = ksReadyQueuesL1Bitmap s d \<and>
                               l1 \<noteq> 0 \<and> hprio = lookupBitmapPriority d s" and
                       F="hprio = Max {prio. q prio \<noteq> []}" in corres_req)
              apply (elim conjE)
              apply (clarsimp simp: valid_queues_def)
              apply (subst lookupBitmapPriority_Max_eqI; blast?)
              apply (fastforce simp: ready_queues_relation_def dest!: state_relationD)
             apply fastforce
         apply (wpsimp simp: if_apply_def2 wp: hoare_drop_imps ksReadyQueuesL1Bitmap_return_wp)+
  done

crunch inv[wp]: isHighestPrio P
crunch inv[wp]: curDomain P
crunch inv[wp]: scheduleSwitchThreadFastfail P

lemma setSchedulerAction_invs': (* not in wp set, clobbered by ssa_wp *)
  "\<lbrace>\<lambda>s. invs' s \<rbrace> setSchedulerAction ChooseNewThread \<lbrace>\<lambda>_. invs' \<rbrace>"
  by (wpsimp simp: invs'_def cur_tcb'_def valid_state'_def valid_irq_node'_def ct_not_inQ_def
                   valid_queues_def valid_release_queue_def valid_release_queue'_def
                   valid_queues_no_bitmap_def valid_queues'_def ct_idle_or_in_cur_domain'_def
                   valid_dom_schedule'_def)

lemma scheduleChooseNewThread_corres:
  "corres dc
    (\<lambda>s. invs s \<and> valid_sched s \<and> scheduler_action s = choose_new_thread)
    (\<lambda>s. invs' s \<and> ksSchedulerAction s = ChooseNewThread)
           schedule_choose_new_thread scheduleChooseNewThread"
  unfolding schedule_choose_new_thread_def scheduleChooseNewThread_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ domain_time_corres], clarsimp)
      apply (rule corres_split_deprecated[OF _ schedule_ChooseNewThread_fragment_corres, simplified bind_assoc])
        apply (rule set_sa_corres)
        apply (wp | simp)+
    apply (wp | simp add: getDomainTime_def)+
   apply auto
  done

lemma ssa_all_invs_but_ct_not_inQ':
  "\<lbrace>all_invs_but_ct_not_inQ' and sch_act_wf sa and
   (\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s)\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. all_invs_but_ct_not_inQ'\<rbrace>"
proof -
  show ?thesis
    apply (simp add: setSchedulerAction_def)
    apply wp
    apply (clarsimp simp add: invs'_def valid_state'_def cur_tcb'_def valid_dom_schedule'_def
                              Invariants_H.valid_queues_def
                              state_refs_of'_def ps_clear_def
                              valid_irq_node'_def valid_queues'_def valid_release_queue_def
                              valid_release_queue'_def tcb_in_cur_domain'_def
                              ct_idle_or_in_cur_domain'_def bitmapQ_defs valid_queues_no_bitmap_def
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
  apply clarsimp
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
  apply wp
    apply (simp add: ARM_H.switchToThread_def setCurThread_def)
    apply (wpsimp wp: tcbSchedDequeue_not_tcbQueued hoare_drop_imps)+
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
  "\<lbrace> invs_no_cicd' \<rbrace> switchToIdleThread \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def)
  apply (wp setCurThread_obj_at')
  apply (intro impI)
  apply (rule idle'_not_tcbQueued')
     apply (simp add: invs_no_cicd'_def ready_qs_runnable_def)+
  done

lemma switchToIdleThread_activatable_2[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv. ct_in_state' activatable'\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   ARM_H.switchToIdleThread_def)
  apply (wp setCurThread_ct_in_state)
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_idle'_def
                        pred_tcb_at'_def obj_at'_def idle_tcb'_def)
  done

lemma switchToThread_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' thread\<rbrace>
   ThreadDecls_H.switchToThread thread
   \<lbrace>\<lambda>_ s. tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def setCurThread_def)
  apply (wpsimp wp: tcbSchedDequeue_not_tcbQueued tcbSchedDequeue_tcbDomain
                    hoare_drop_imps)
  done

lemma chooseThread_invs_no_cicd'_posts: (* generic version *)
  "\<lbrace> invs_no_cicd' \<rbrace> chooseThread
   \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and>
           ct_in_state' activatable' s \<and>
           (ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s) \<rbrace>"
    (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
proof -
  note switchToThread_invs[wp del]
  note switchToThread_lookupBitmapPriority_wp[wp]
  note assert_wp[wp del]

  show ?thesis
    unfolding chooseThread_def Let_def numDomains_def curDomain_def
    apply (simp only: return_bind, simp)
    apply (rule hoare_seq_ext[OF _ stateAssert_sp])
    apply (rule hoare_seq_ext[where B="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s
                                              \<and> ready_qs_runnable s"])
     apply (rule_tac B="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                               rv = ksReadyQueuesL1Bitmap s curdom \<and> ready_qs_runnable s"
                  in hoare_seq_ext)
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
                switchToThread_tcb_in_cur_domain' isSchedulable_wp)
      apply clarsimp
      apply (clarsimp dest!: invs_no_cicd'_queues
                      simp: valid_queues_def lookupBitmapPriority_def[symmetric]
                            ready_qs_runnable_def)
      apply (drule (3) lookupBitmapPriority_obj_at')
      apply normalise_obj_at'
      apply (fastforce simp: tcb_in_cur_domain'_def inQ_def elim: obj_at'_weaken)
     apply (wp | simp add: bitmap_fun_defs curDomain_def)+
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
  note switchToThread_lookupBitmapPriority_wp[wp]
  note assert_wp[wp del]

  (* FIXME this is almost identical to the chooseThread_invs_no_cicd'_posts proof, can generalise? *)
  show ?thesis
    unfolding chooseThread_def Let_def numDomains_def curDomain_def
    apply (simp only: return_bind, simp)
    apply (rule hoare_seq_ext[OF _ stateAssert_sp])
    apply (rule hoare_seq_ext[where B="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s
                                              \<and> ready_qs_runnable s"])
     apply (rule_tac B="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                               rv = ksReadyQueuesL1Bitmap s curdom \<and> ready_qs_runnable s"
                  in hoare_seq_ext)
      apply (rename_tac l1)
      apply (case_tac "l1 = 0")
       (* switch to idle thread *)
       apply (simp, wp (once) switchToIdleThread_invs_no_cicd', simp)
      (* we have a thread to switch to *)
      apply (clarsimp simp: bitmap_fun_defs)
      apply (wp assert_inv isSchedulable_wp)
      apply (clarsimp dest!: invs_no_cicd'_queues simp: valid_queues_def)
      apply (fastforce elim: bitmapQ_from_bitmap_lookup simp: lookupBitmapPriority_def)
     apply (wp | simp add: bitmap_fun_defs curDomain_def)+
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

lemma setReprogramTimer_invs'[wp]:
  "setReprogramTimer v \<lbrace>invs'\<rbrace>"
  unfolding setReprogramTimer_def
  apply wpsimp
  by (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def cur_tcb'_def
                     ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_not_inQ_def
                     valid_dom_schedule'_def)

lemma machine_op_lift_underlying_memory_invar:
  "(x, b) \<in> fst (machine_op_lift a m) \<Longrightarrow> underlying_memory b = underlying_memory m"
  by (clarsimp simp: in_monad machine_op_lift_def machine_rest_lift_def select_f_def)

lemma setNextInterrupt_invs'[wp]:
  "setNextInterrupt \<lbrace>invs'\<rbrace>"
  unfolding setNextInterrupt_def
  apply (wpsimp wp: dmo_invs' ARM.setDeadline_irq_masks threadGet_wp getReleaseQueue_wp)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  by (auto simp: in_monad setDeadline_def machine_op_lift_underlying_memory_invar)

lemma setCurSc_invs'[wp]:
  "setCurSc v \<lbrace>invs'\<rbrace>"
  unfolding setCurSc_def
  apply wpsimp
  apply (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def cur_tcb'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_not_inQ_def
                        valid_queues_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                        bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def valid_irq_node'_def
                        valid_queues'_def valid_release_queue_def valid_release_queue'_def
                        valid_dom_schedule'_def)
  done

lemma setConsumedTime_invs'[wp]:
  "setConsumedTime v \<lbrace>invs'\<rbrace>"
  unfolding setConsumedTime_def
  apply wpsimp
  apply (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def cur_tcb'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_not_inQ_def
                        valid_queues_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                        bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def valid_irq_node'_def
                        valid_queues'_def valid_release_queue_def valid_release_queue'_def
                        valid_dom_schedule'_def)
  done

lemma setDomainTime_invs'[wp]:
  "setDomainTime v \<lbrace>invs'\<rbrace>"
  unfolding setDomainTime_def
  apply wpsimp
  done

lemma invs'_ko_at_idle_sc_is_idle':
  "\<lbrakk>invs' s; ko_at' ko scPtr s\<rbrakk> \<Longrightarrow> (scPtr = idle_sc_ptr \<longrightarrow> idle_sc' ko)"
  apply (drule invs_valid_idle')
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def)
  done

lemma refillTailIndex_bounded:
  "valid_sched_context' ko s \<Longrightarrow> 0 < scRefillMax ko \<longrightarrow> refillTailIndex ko < scRefillMax ko"
  apply (clarsimp simp: valid_sched_context'_def refillTailIndex_def Let_def split: if_split)
  by linarith

lemma refillAddTail_valid_objs'[wp]:
  "refillAddTail scPtr t \<lbrace>valid_objs'\<rbrace>"
  apply (simp add: refillAddTail_def)
  apply (wpsimp wp: set_sc_valid_objs' getRefillNext_wp getRefillSize_wp)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
  apply (intro conjI; intro allI impI)
   apply (intro conjI)
    apply (clarsimp simp: valid_sched_context'_def)
   apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def valid_sched_context'_def)
  apply (intro conjI)
   apply (drule ko_at'_inj, assumption, clarsimp)+
   apply (frule refillTailIndex_bounded)
   apply (clarsimp simp: valid_sched_context'_def)
  apply (drule ko_at'_inj, assumption, clarsimp)+
  apply (frule refillTailIndex_bounded)
  apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def valid_sched_context'_def)
  done

lemma refillAddTail_invs'[wp]:
  "refillAddTail scPtr t \<lbrace>invs'\<rbrace>"
  apply (simp add: refillAddTail_def)
  apply (wpsimp wp: setSchedContext_invs' getRefillNext_wp getRefillSize_wp)
  apply (frule (1) invs'_ko_at_idle_sc_is_idle')
  apply (frule (1) invs'_ko_at_valid_sched_context', clarsimp)
  apply (intro conjI; intro allI impI)
   apply (intro conjI)
     apply (fastforce dest: live_sc'_ko_ex_nonz_cap_to')
    apply (clarsimp simp: valid_sched_context'_def)
   apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def valid_sched_context'_def)
  apply (intro conjI)
    apply (fastforce dest: live_sc'_ko_ex_nonz_cap_to')
   apply (drule ko_at'_inj, assumption, clarsimp)+
   apply (frule refillTailIndex_bounded)
   apply (clarsimp simp: valid_sched_context'_def)
  apply (drule ko_at'_inj, assumption, clarsimp)+
  apply (frule refillTailIndex_bounded)
  apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def valid_sched_context'_def)
  done

lemma updateRefillTl_def2:
  "updateRefillTl scp f
   = updateSchedContext scp (\<lambda>sc. scRefills_update (\<lambda>_. replaceAt (refillTailIndex sc) (scRefills sc)
       (f (refillTl sc))) sc)"
  by (clarsimp simp: updateRefillTl_def updateSchedContext_def)

lemma updateRefillHd_def2:
  "updateRefillHd scp f
   = updateSchedContext scp (\<lambda>sc. scRefills_update (\<lambda>_. replaceAt (scRefillHead sc) (scRefills sc)
       (f (refillHd sc))) sc)"
  by (clarsimp simp: updateRefillHd_def updateSchedContext_def)

lemma refillBudgetCheckRoundRobin_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. active_sc_at' (ksCurSc s) s)\<rbrace>
   refillBudgetCheckRoundRobin consumed
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply if_split [split del]
  apply (simp add: refillBudgetCheckRoundRobin_def)
  apply (wpsimp simp: updateRefillTl_def2 updateRefillHd_def2 wp: updateSchedContext_refills_invs')
    apply (rule_tac Q="\<lambda>_. invs' and active_sc_at' scPtr" in hoare_strengthen_post[rotated])
     apply clarsimp
     apply (intro conjI)
      apply (fastforce dest: invs'_ko_at_idle_sc_is_idle')
     apply (intro allI impI)
     apply (frule (1) invs'_ko_at_valid_sched_context', clarsimp)
     apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def
                           ko_wp_at'_def valid_sched_context_size'_def objBits_def objBitsKO_def)
    apply (wpsimp wp: updateSchedContext_refills_invs' getCurTime_wp updateSchedContext_active_sc_at')
   apply (wpsimp wp: )
  apply clarsimp
  apply (intro conjI)
   apply (fastforce dest: invs'_ko_at_idle_sc_is_idle')
  apply (intro allI impI)
  apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

lemma scheduleUsed_valid_objs'[wp]:
  "scheduleUsed scPtr refill \<lbrace>valid_objs'\<rbrace>"
  apply (simp add: scheduleUsed_def)
  apply (rule hoare_seq_ext[OF _ get_sc_sp'])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext_skip, wpsimp simp: refillEmpty_def)
  apply (rule hoare_if)
   apply wpsimp
  apply (wpsimp simp: setRefillTl_def updateRefillTl_def2 updateSchedContext_def
                  wp: updateSchedContext_refills_invs' refillFull_wp refillEmpty_wp)+
  apply (intro conjI; intro allI impI)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
   apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def)
   apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

lemma scheduleUsed_invs'[wp]:
  "scheduleUsed scPtr refill \<lbrace>invs'\<rbrace>"
  apply (simp add: scheduleUsed_def)
  apply (wpsimp simp: setRefillTl_def updateRefillTl_def2
                  wp: updateSchedContext_refills_invs' refillFull_wp refillEmpty_wp)+
  apply (prop_tac "\<forall>ko. ko_at' ko idle_sc_ptr s \<longrightarrow> idle_sc' ko")
   apply (fastforce dest: invs'_ko_at_idle_sc_is_idle')
  apply (intro conjI; intro allI impI)
   apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
   apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def)
   apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def)
  apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)

  done

lemma refillPopHead_valid_objs'[wp]:
  "\<lbrace>valid_objs' and obj_at' (\<lambda>sc'. 1 < scRefillCount sc') scPtr \<rbrace>
   refillPopHead scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def getRefillNext_def)
  apply (wpsimp wp: set_sc_valid_objs')
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: readRefillNext_def readSchedContext_def)
  apply (fastforce simp: obj_at'_def projectKOs vs_all_heap_simps pred_map_simps scBits_simps
                         valid_sched_context'_def valid_sched_context_size'_def objBits_simps'
                  dest!: readObject_misc_ko_at')
  done

lemma refillPopHead_invs'[wp]:
  "\<lbrace>invs' and obj_at' (\<lambda>sc'. 1 < scRefillCount sc') scPtr\<rbrace>
   refillPopHead scPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_invs' getRefillNext_wp)
  apply (subgoal_tac "(\<forall>ko. ko_at' ko idle_sc_ptr s \<longrightarrow> idle_sc' ko)")
   apply (intro conjI; intro impI)
    apply (intro conjI; intro allI impI)
      apply (clarsimp simp: obj_at'_def)
     apply (rule if_live_then_nonz_capE')
     apply (erule invs_iflive')
     apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq projectKO_sc live_sc'_def)
    apply (drule ko_at'_inj, assumption, clarsimp)+
    apply (rename_tac sc)
    apply (intro conjI)
     apply (subgoal_tac "valid_sched_context' sc s")
      apply (fastforce simp: valid_sched_context'_def obj_at'_def dest!: readObject_misc_ko_at')
     apply (fastforce dest: invs'_ko_at_valid_sched_context')
    apply (subgoal_tac "valid_sched_context_size' sc")
     apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def)
    apply (fastforce dest: invs'_ko_at_valid_sched_context')
   apply (intro conjI; intro allI impI)
     apply (clarsimp simp: obj_at'_def)
    apply (rule if_live_then_nonz_capE')
     apply (erule invs_iflive')
    apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKO_eq projectKO_sc live_sc'_def)
   apply (drule ko_at'_inj, assumption, clarsimp)+
   apply (rename_tac sc)
   apply (intro conjI)
    apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
    apply (subgoal_tac "valid_sched_context' sc s")
     apply (clarsimp simp: valid_sched_context'_def obj_at'_def)
     apply linarith
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
   apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
   apply (subgoal_tac "valid_sched_context_size' sc")
    apply (clarsimp simp: valid_sched_context_size'_def objBits_def objBitsKO_def)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (clarsimp cong: if_cong simp: sym_refs_sc_trivial_update)
  apply (fastforce dest: invs'_ko_at_idle_sc_is_idle')
  done

lemma refillPopHead_active_sc_at'[wp]:
  "refillPopHead scPtr \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: refillPopHead_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at' getRefillNext_wp)
  done

lemma refillAddTail_active_sc_at'[wp]:
  "refillAddTail scPtr refill \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: refillAddTail_def getRefillSize_def)
  apply (wpsimp wp: setSchedContext_active_sc_at' hoare_drop_imps getRefillNext_wp)
  apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  done

lemma updateRefillTl_active_sc_at'[wp]:
  "updateRefillTl scPtr f \<lbrace>active_sc_at' scPtr'\<rbrace>"
  apply (simp add: updateRefillTl_def)
  apply (wpsimp wp: setSchedContext_active_sc_at' hoare_drop_imps getRefillNext_wp)
  apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  done

crunches scheduleUsed
  for active_sc_at'[wp]: "active_sc_at' scPtr"
  (wp: crunch_wps)

crunches refillPopHead
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' scPtr"

lemma updateRefillHd_invs':
  "\<lbrace>invs' and active_sc_at' scPtr\<rbrace> updateRefillHd scPtr f \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def2)
  apply (wpsimp wp: updateSchedContext_invs')
  apply (intro conjI; intro allI impI)
    apply (fastforce dest: invs'_ko_at_idle_sc_is_idle')
   apply (fastforce dest: live_sc'_ko_ex_nonz_cap_to')
  apply (frule invs'_ko_at_valid_sched_context', simp, clarsimp)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

lemma updateRefillHd_active_sc_at'[wp]:
  "updateRefillHd scPtr f \<lbrace>active_sc_at' scPr\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def2)
  apply (wpsimp wp: updateSchedContext_active_sc_at')
  done

lemma updateRefillHd_active_sc_at'_ksCurSc[wp]:
  "updateRefillHd scPtr f \<lbrace>\<lambda>s. active_sc_at' (ksCurSc s) s\<rbrace>"
  apply (rule_tac f=ksCurSc in hoare_lift_Pf)
   apply wpsimp
  apply (clarsimp simp: updateRefillHd_def2 updateSchedContext_def)
  apply wpsimp
  done

lemma setRefillHd_active_sc_at'[wp]:
  "setRefillHd scPtr f \<lbrace>active_sc_at' scPr\<rbrace>"
  apply (clarsimp simp: setRefillHd_def)
  apply (wpsimp wp: updateSchedContext_active_sc_at')
  done

lemma setReprogramTimer_obj_at'[wp]:
  "setReprogramTimer b \<lbrace>\<lambda>s. Q (obj_at' P t s)\<rbrace>"
  unfolding active_sc_at'_def
  by (wpsimp simp: setReprogramTimer_def)

lemma setReprogramTimer_active_sc_at'[wp]:
  "setReprogramTimer b \<lbrace>active_sc_at' scPtr\<rbrace>"
  unfolding active_sc_at'_def
  by wpsimp

(* FIXME RT: move these whileM lemmas, prove `whileM_*_inv` using `whileM_wp_gen`. *)
lemmas whileM_post_inv
  = hoare_strengthen_post[where R="\<lambda>_. Q" for Q, OF whileM_inv[where P=C for C], rotated -1]

lemma whileM_wp_gen:
  assumes termin:"\<And>s. I False s \<Longrightarrow> Q s"
  assumes [wp]: "\<lbrace>I'\<rbrace> C \<lbrace>I\<rbrace>"
  assumes [wp]: "\<lbrace>I True\<rbrace> f \<lbrace>\<lambda>_. I'\<rbrace>"
  shows "\<lbrace>I'\<rbrace> whileM C f \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding whileM_def
  using termin
  by (wpsimp wp: whileLoop_wp[where I=I])

crunches refillHeadOverlappingLoop, headInsufficientLoop
  for valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

lemma mergeRefills_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' scPtr s \<and> obj_at' (\<lambda>sc'. Suc 0 < scRefillCount sc') scPtr s\<rbrace>
   mergeRefills scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: mergeRefills_def updateRefillHd_def)
  apply (rule_tac B="\<lambda>_ s. valid_objs' s \<and> active_sc_at' scPtr s" in hoare_seq_ext[rotated])
   apply wpsimp
  apply (wpsimp wp: set_sc_valid_objs')
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: active_sc_at'_def)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

crunches mergeRefills, nonOverlappingMergeRefills
  for active_sc_at'[wp]: "active_sc_at' scPtr"

lemma no_ofail_refillHeadOverlapping:
  "no_ofail (sc_at' scp) (refillHeadOverlapping scp)"
  unfolding refillHeadOverlapping_def oreturn_def obind_def oliftM_def no_ofail_def
            readRefillSize_def readRefillNext_def
  by (clarsimp dest!: no_ofailD[OF no_ofail_readSchedContext])

lemma refillHeadOverlapping_implies_count_greater_than_one:
  "\<lbrakk>the (refillHeadOverlapping scPtr s); sc_at' scPtr s;
    \<forall>sc. ko_at' sc scPtr s \<longrightarrow> valid_sched_context' sc s\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>sc. 1 < scRefillCount sc) scPtr s"
  apply (clarsimp simp: refillHeadOverlapping_def readSchedContext_def oliftM_def
                        readRefillNext_def readRefillSize_def obind_def omonad_defs
                 split: option.splits dest!: readObject_misc_ko_at')
   apply (prop_tac "sc_at' scPtr s")
    apply (fastforce dest: no_ofail_sc_at'_readObject[unfolded no_ofail_def, rule_format])+
  apply (clarsimp simp: obj_at'_def projectKOs valid_sched_context'_def MIN_REFILLS_def)
  done

lemma refillHeadOverlappingLoop_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' scPtr s\<rbrace>
   refillHeadOverlappingLoop scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: refillHeadOverlappingLoop_def)
  apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_. ?pre"] mergeRefills_valid_objs')
  apply (clarsimp simp: runReaderT_def)
    apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                           refillHeadOverlapping_implies_count_greater_than_one
                     simp: obj_at'_def active_sc_at'_def projectKOs)
   apply simp
  apply simp
  done

lemma updateRefillHd_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' scPtr s\<rbrace>
   updateRefillHd scPtr f
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def)
  apply (wpsimp wp: set_sc_valid_objs')
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: active_sc_at'_def)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

lemma setRefillHd_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' scPtr s\<rbrace>
   setRefillHd scPtr f
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: setRefillHd_def
                  wp: updateRefillHd_valid_objs')
  done

lemma refillUnblockCheck_valid_objs'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def isRoundRobin_def refillReady_def)
  apply (wpsimp wp: updateRefillHd_valid_objs' refillHeadOverlappingLoop_valid_objs' scActive_wp)
  apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  done

crunches refillUnblockCheck, refillBudgetCheck
  for valid_queues[wp]: valid_queues
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  and pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and no_0_obj'[wp]: no_0_obj'
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and valid_irq_node[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_irq_states'[wp]: valid_irq_states'
  and irqs_masked'[wp]: irqs_masked'
  and valid_pde_mappings'[wp]: valid_pde_mappings'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksCurdomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and untyped_ranges_zero'[wp]: untyped_ranges_zero'
  and cur_tcb'[wp]: cur_tcb'
  and ct_not_inQ[wp]: ct_not_inQ
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  (wp: crunch_wps valid_dom_schedule'_lift simp: crunch_simps refillSingle_def)

lemma refillUnblockCheck_valid_mdb'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def valid_mdb'_def)
  apply (wpsimp wp: scActive_wp)
  done

lemma refillUnblockCheck_valid_machine_state'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def refillReady_def isRoundRobin_def
                        refillHeadOverlappingLoop_def mergeRefills_def updateRefillHd_def
                        refillPopHead_def updateSchedContext_def setReprogramTimer_def
                        valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wpsimp wp: whileLoop_wp' hoare_vcg_all_lift hoare_vcg_disj_lift scActive_wp
                    hoare_drop_imps getRefillNext_wp)
  apply fastforce
  done

lemma refillUnblockCheck_list_refs_of_replies'[wp]:
  "refillUnblockCheck scPtr \<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def valid_mdb'_def refillHeadOverlappingLoop_def
                        mergeRefills_def updateRefillHd_def refillPopHead_def updateSchedContext_def
                        setReprogramTimer_def refillReady_def isRoundRobin_def)
  apply (wpsimp wp: whileLoop_wp' hoare_drop_imps scActive_wp getRefillNext_wp
              simp: o_def)
  done

lemma refillPopHead_if_live_then_nonz_cap'[wp]:
  "refillPopHead scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def updateSchedContext_def getRefillNext_def)
  apply wpsimp
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

lemma mergeRefills_if_live_then_nonz_cap'[wp]:
  "mergeRefills scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: mergeRefills_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp simp: updateRefillHd_def)
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

lemma nonOverlappingMergeRefills_if_live_then_nonz_cap'[wp]:
  "nonOverlappingMergeRefills scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: nonOverlappingMergeRefills_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (wpsimp simp: updateRefillHd_def)
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

crunches refillHeadOverlappingLoop, headInsufficientLoop
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps)

lemma updateRefillHd_if_live_then_nonz_cap'[wp]:
  "updateRefillHd scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: updateRefillHd_def)
  apply wpsimp
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

lemma setRefillHd_if_live_then_nonz_cap'[wp]:
  "setRefillHd scPtr f \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: setRefillHd_def)
  done

lemma scheduleUsed_if_live_then_nonz_cap'[wp]:
  "scheduleUsed scPtr refill \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: scheduleUsed_def refillAddTail_def setRefillTl_def updateRefillTl_def
                  wp: getRefillSize_wp refillFull_wp refillEmpty_wp getRefillNext_wp)
  apply (fastforce intro: if_live_then_nonz_capE'
                    simp: ko_wp_at'_def obj_at'_real_def projectKO_sc live_sc'_def)
  done

crunches handleOverrunLoop
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps)

lemma refillUnblockCheck_if_live_then_nonz_cap'[wp]:
  "refillUnblockCheck scPtr \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def setReprogramTimer_def refillReady_def
                        isRoundRobin_def)
  apply (wpsimp wp: scActive_wp)
  done

lemma refillPopHead_valid_idle'[wp]:
  "refillPopHead scPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: refillPopHead_def  updateSchedContext_def getRefillNext_def)
  apply (wpsimp simp: valid_idle'_def obj_at'_def)
  done

lemma refillAddTail_valid_idle'[wp]:
  "refillAddTail scPtr refill \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: refillAddTail_def  updateSchedContext_def getRefillNext_def)
  apply (wpsimp wp: getRefillSize_wp)
  apply (wpsimp simp: valid_idle'_def obj_at'_def)
  done

lemma updateRefillHd_valid_idle'[wp]:
  "updateRefillHd scPtr f \<lbrace>valid_idle'\<rbrace>"
  apply (wpsimp simp: updateRefillHd_def)
  apply (fastforce simp: valid_idle'_def obj_at'_def)
  done

lemma scheduleUsed_valid_idle'[wp]:
  "scheduleUsed scPtr new \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: scheduleUsed_def  updateSchedContext_def getRefillNext_def)
  apply (wpsimp simp: setRefillTl_def updateRefillTl_def wp: refillFull_wp refillEmpty_wp)
  apply (fastforce simp: valid_idle'_def obj_at'_def projectKOs)
  done

lemma mergeRefills_valid_idle'[wp]:
  "mergeRefills scPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: mergeRefills_def updateRefillHd_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp simp: valid_idle'_def obj_at'_def)
  done

lemma nonOverlappingMergeRefills_valid_idle'[wp]:
  "nonOverlappingMergeRefills scPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: nonOverlappingMergeRefills_def updateRefillHd_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (repeat_unless \<open>rule hoare_seq_ext[OF _ get_sc_sp']\<close> \<open>rule hoare_seq_ext_skip, wpsimp\<close>)
  apply (wpsimp simp: valid_idle'_def obj_at'_def)
  done

crunches refillHeadOverlappingLoop, headInsufficientLoop, handleOverrunLoop
  for valid_idle'[wp]: valid_idle'
  (wp: crunch_wps)

lemma refillUnblockCheck_valid_idle'[wp]:
  "refillUnblockCheck scPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def)
  apply (wpsimp wp: scActive_wp)
  apply (clarsimp simp: valid_idle'_def obj_at'_def)
  done

crunches refillHeadOverlappingLoop, headInsufficientLoop, handleOverrunLoop
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  (wp: crunch_wps)

lemma refillUnblockCheck_ct_idle_or_in_cur_domain'[wp]:
  "refillUnblockCheck scPtr \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: refillUnblockCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def)
  apply (wpsimp wp: scActive_wp)
  done

crunches refillUnblockCheck, refillBudgetCheck
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and pred_tcb_at'[wp]: "pred_tcb_at' proj P p"
  and valid_replies'[wp]: valid_replies'
  (wp: crunch_wps valid_replies'_lift)

lemma refillUnblockCheck_invs':
  "refillUnblockCheck scPtr \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def pred_conj_def)
  apply wpsimp
  done

lemma nonOverlappingMergeRefills_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' scPtr s\<rbrace>
   nonOverlappingMergeRefills scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: nonOverlappingMergeRefills_def updateRefillHd_def)
  apply (rule hoare_seq_ext[OF _ get_sc_sp'])
  apply (rule_tac hoare_seq_ext[OF _ assert_sp])
  apply (rule_tac B="\<lambda>_ s. valid_objs' s \<and> active_sc_at' scPtr s" in hoare_seq_ext[rotated])
   apply wpsimp
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (wpsimp wp: set_sc_valid_objs')
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: active_sc_at'_def)
  apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_real_def ko_wp_at'_def
                        valid_sched_context_size'_def objBits_def objBitsKO_def)
  done

crunches refillHeadOverlappingLoop, headInsufficientLoop, handleOverrunLoop
  for active_sc_at'[wp]: "active_sc_at' scPtr"
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  (wp: crunch_wps)

lemma head_insufficient_length_cross:
  "\<lbrakk>(s,s') \<in> state_relation; valid_objs s; active_sc_valid_refills s; is_active_sc scPtr s;
    \<not> round_robin scPtr s; the (head_insufficient scPtr s); pspace_aligned s; pspace_distinct s;
    valid_objs' s'\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>sc'. Suc 0 < scRefillCount sc') scPtr s'"
  apply (frule head_insufficient_length_at_least_two[rotated])
  apply (frule (1) active_sc_valid_refillsE)
  apply (clarsimp simp: vs_all_heap_simps)
   apply (frule valid_refills_refills_unat_sum_equals_budget)
     apply (clarsimp simp: round_robin_def vs_all_heap_simps)
    apply (fastforce simp: sc_valid_refills_def round_robin_def vs_all_heap_simps)
   apply (fastforce simp: sc_valid_refills_def round_robin_def vs_all_heap_simps word_le_nat_alt)
  apply (clarsimp simp: vs_all_heap_simps)
  apply (rename_tac sc n)
  apply (prop_tac "valid_sched_context_size n")
   apply (fastforce intro: valid_sched_context_size_objsI)
  apply (prop_tac "sc_at' scPtr s'")
   apply (fastforce intro!: sc_at_cross
                      simp: vs_all_heap_simps obj_at_kh_kheap_simps is_sc_obj_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (rename_tac sc')
  apply (prop_tac "sc_relation sc n sc'")
   apply (frule state_relation_pspace_relation)
   apply (clarsimp simp: pspace_relation_def vs_all_heap_simps)
   apply (drule_tac x=scPtr in bspec, blast)
   apply clarsimp
  apply (prop_tac "valid_sched_context' sc' s'")
   apply (frule sc_ko_at_valid_objs_valid_sc'[rotated])
    apply (fastforce simp: obj_at'_def projectKOs)
   apply (fastforce dest!: sc_ko_at_valid_objs_valid_sc')
  apply (auto simp: sc_relation_def refills_map_def valid_sched_context'_def)
  done

lemma headInsufficientLoop_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' scPtr s\<rbrace>
   headInsufficientLoop scPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: headInsufficientLoop_def)
  apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_. ?pre"] nonOverlappingMergeRefills_valid_objs')
  done

lemma handleOverrunLoop_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> active_sc_at' (ksCurSc s) s\<rbrace>
   handleOverrunLoop usage
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: handleOverrunLoop_def)
  apply (wpsimp wp: valid_whileLoop[where I="\<lambda>_. ?pre"])
    apply (intro hoare_vcg_conj_lift_pre_fix)
     apply (clarsimp simp: handleOverrunLoopBody_def)
     apply (wpsimp wp: updateRefillHd_valid_objs' simp: refillSingle_def)
     apply (frule (1) sc_ko_at_valid_objs_valid_sc')
     apply (fastforce simp: valid_sched_context'_def active_sc_at'_def obj_at'_def projectKOs refillTailIndex_def Let_def
                     split: if_split_asm)
    apply (rule_tac f=ksCurSc in hoare_lift_Pf3)
     apply wpsimp+
  done

lemma refillBudgetCheck_valid_objs':
  "refillBudgetCheck usage \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def isRoundRobin_def refillReady_def getCurSc_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ scActive_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (wpsimp wp: headInsufficientLoop_valid_objs' handleOverrunLoop_valid_objs'
                    hoare_vcg_all_lift setRefillHd_valid_objs' hoare_vcg_if_lift2 hoare_drop_imps)
  apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  done

lemma refillBudgetCheck_valid_mdb'[wp]:
  "refillBudgetCheck usage \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: handleOverrunLoop_def valid_mdb'_def)
  apply (wpsimp wp: scActive_wp)
  done

lemma handleOverrunLoop_list_refs_of_replies'[wp]:
  "handleOverrunLoop usage \<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: handleOverrunLoop_def)
  apply (wpsimp wp: whileLoop_wp' hoare_drop_imps getRefillNext_wp
                    getRefillSize_wp refillFull_wp refillEmpty_wp
              simp: o_def handleOverrunLoopBody_def refillPopHead_def updateSchedContext_def
                    scheduleUsed_def refillAddTail_def  updateRefillHd_def setRefillTl_def
                    updateRefillTl_def refillSingle_def)
  done

lemma refillBudgetCheck_list_refs_of_replies'[wp]:
  "refillBudgetCheck usage \<lbrace>\<lambda>s. sym_refs (list_refs_of_replies' s)\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def refillPopHead_def updateSchedContext_def
                        setReprogramTimer_def refillReady_def isRoundRobin_def
                        headInsufficientLoop_def nonOverlappingMergeRefills_def)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (wpsimp wp: whileLoop_wp' hoare_drop_imps refillFull_wp refillEmpty_wp getRefillNext_wp
                     getRefillSize_wp hoare_vcg_all_lift hoare_vcg_if_lift2
              simp: o_def scheduleUsed_def refillAddTail_def setRefillHd_def updateRefillHd_def
                    setRefillTl_def updateRefillTl_def)
  done

lemma refillBudgetCheck_if_live_then_nonz_cap'[wp]:
  "refillBudgetCheck uage \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: refillBudgetCheck_def setReprogramTimer_def refillReady_def
                      isRoundRobin_def
                  wp: hoare_drop_imps)
  done

lemma refillBudgetCheck_valid_idle'[wp]:
  "refillBudgetCheck usage \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def setRefillHd_def)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply wpsimp
  apply (fastforce simp: valid_idle'_def obj_at'_def)
  done

lemma handleOverrunLoop_valid_machine_state'[wp]:
  "handleOverrunLoop usage \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: handleOverrunLoop_def)
  apply (wpsimp wp: whileLoop_wp' hoare_drop_imps getRefillNext_wp
                    getRefillSize_wp refillFull_wp refillEmpty_wp
              simp: handleOverrunLoopBody_def refillPopHead_def updateSchedContext_def
                    scheduleUsed_def refillAddTail_def  updateRefillHd_def setRefillTl_def
                    updateRefillTl_def refillSingle_def)
  done

lemma refillBudgetCheck_valid_machine_state'[wp]:
  "refillBudgetCheck usage \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def refillPopHead_def updateSchedContext_def
                        setReprogramTimer_def refillReady_def isRoundRobin_def
                        headInsufficientLoop_def nonOverlappingMergeRefills_def)
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (wpsimp wp: whileLoop_wp' hoare_vcg_all_lift hoare_vcg_disj_lift scActive_wp hoare_drop_imps
                    refillFull_wp refillEmpty_wp getRefillNext_wp  getRefillSize_wp
              simp: scheduleUsed_def refillAddTail_def setRefillTl_def updateRefillTl_def
                    setRefillHd_def updateRefillHd_def)
  done

lemma refillBudgetCheck_ct_idle_or_in_cur_domain'[wp]:
  "refillBudgetCheck usage \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: refillBudgetCheck_def isRoundRobin_def refillReady_def
                        setReprogramTimer_def updateRefillHd_def)
  apply (wpsimp wp: getRefillSize_wp refillFull_wp refillEmpty_wp hoare_vcg_all_lift hoare_drop_imps
                    hoare_vcg_if_lift2
              simp: scheduleUsed_def refillAddTail_def setRefillTl_def updateRefillTl_def
                    updateRefillHd_def setRefillHd_def)
  done

lemma refillBudgetCheck_invs'[wp]:
  "refillBudgetCheck usage \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def pred_conj_def)
  apply (wpsimp wp: refillBudgetCheck_valid_objs')
  done

lemma commitTime_invs':
  "commitTime \<lbrace>invs'\<rbrace>"
  apply (simp add: commitTime_def)
  apply wpsimp
       apply (wpsimp wp: updateSchedContext_invs'_indep)
      apply (clarsimp simp: valid_sched_context'_def valid_sched_context_size'_def objBits_def sc_size_bounds_def objBitsKO_def live_sc'_def)
      apply (rule_tac Q="\<lambda>_. invs'" in hoare_strengthen_post)
       apply (wpsimp wp: isRoundRobin_wp)
      apply (fastforce dest: invs'_ko_at_idle_sc_is_idle')
     apply (wpsimp wp: getConsumedTime_wp  getCurSc_wp)+
  by (clarsimp simp: active_sc_at'_def obj_at'_real_def ko_wp_at'_def)

lemma switchSchedContext_invs':
  "switchSchedContext \<lbrace>invs'\<rbrace>"
  apply (simp add: switchSchedContext_def)
  apply (wpsimp wp: commitTime_invs' getReprogramTimer_wp refillUnblockCheck_invs' threadGet_wp simp: getCurSc_def)
  apply (fastforce simp: obj_at'_def projectKO_eq projectKO_opt_tcb)
  done

(* FIXME RT: move, and shouldn't we have all of these? *)
lemma setSchedulerAction_ksSchedulerAction[wp]:
  "\<lbrace>\<lambda>_. P (schact)\<rbrace>
   setSchedulerAction schact
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (wpsimp simp: setSchedulerAction_def)

lemma isSchedulable_bool_runnableE:
  "isSchedulable_bool t s \<Longrightarrow> tcb_at' t s \<Longrightarrow> st_tcb_at' runnable' t s"
  unfolding isSchedulable_bool_def
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def pred_map_def projectKO_eq projectKO_opt_tcb)

lemma rescheduleRequired_invs'[wp]:
  "rescheduleRequired \<lbrace>invs'\<rbrace>"
  unfolding rescheduleRequired_def
  apply (wpsimp wp: ssa_invs' isSchedulable_wp)
  by (clarsimp simp: invs'_def valid_state'_def)

lemma rescheduleRequired_ksSchedulerAction[wp]:
  "\<lbrace>\<lambda>_. P ChooseNewThread\<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  unfolding rescheduleRequired_def by wpsimp

lemma inReleaseQueue_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko tcb_ptr s \<longrightarrow> P (tcbInReleaseQueue ko) s\<rbrace>
   inReleaseQueue tcb_ptr
   \<lbrace>P\<rbrace>"
  unfolding inReleaseQueue_def threadGet_getObject
  apply (wpsimp wp: getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma possibleSwitchTo_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding possibleSwitchTo_def
  apply (wpsimp wp: inReleaseQueue_wp threadGet_wp rescheduleRequired_weak_sch_act_wf)
  by (auto simp: obj_at'_def weak_sch_act_wf_def tcb_in_cur_domain'_def
                 projectKO_eq ps_clear_domE)

crunches possibleSwitchTo
  for valid_pspace'[wp]: valid_pspace'
  and valid_queues[wp]: valid_queues
  and valid_tcbs'[wp]: valid_tcbs'
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and ifunsafe'[wp]: "if_unsafe_then_cap'"
  and global_refs'[wp]: valid_global_refs'
  and valid_machine_state'[wp]: valid_machine_state'
  and cur[wp]: cur_tcb'
  and valid_queues'[wp]: valid_queues'
  and valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'
  and refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and idle'[wp]: "valid_idle'"
  and valid_arch'[wp]: valid_arch_state'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and irq_states' [wp]: valid_irq_states'
  and pde_mappings' [wp]: valid_pde_mappings'
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and valid_objs'[wp]: valid_objs'
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  (wp: crunch_wps cur_tcb_lift valid_irq_handlers_lift'' simp: crunch_simps)

lemmas possibleSwitchTo_typ_ats[wp] = typ_at_lifts[OF possibleSwitchTo_typ_at']

lemma possibleSwitchTo_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> st_tcb_at' runnable' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wpsimp simp: possibleSwitchTo_def wp: inReleaseQueue_wp threadGet_wp)
  by (fastforce simp: obj_at'_def tcb_in_cur_domain'_def)

lemma possibleSwitchTo_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' t
      and (\<lambda>s. \<forall>t. ksSchedulerAction s = SwitchToThread t
                   \<longrightarrow> st_tcb_at' runnable' t s)\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp simp: possibleSwitchTo_def inReleaseQueue_def
               wp: hoare_vcg_if_lift2 hoare_drop_imps)

lemma possibleSwitchTo_ct_idle_or_in_cur_domain'[wp]:
  "possibleSwitchTo t \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (wpsimp simp: possibleSwitchTo_def
                  wp: threadGet_wp inReleaseQueue_wp)
  apply (fastforce simp: obj_at'_def ct_idle_or_in_cur_domain'_def)
  done

lemma possibleSwitchTo_utr[wp]:
  "possibleSwitchTo t \<lbrace>untyped_ranges_zero'\<rbrace>"
  by (wpsimp simp: cteCaps_of_def o_def wp: untyped_ranges_zero_lift)

lemma possibleSwitchTo_all_invs_but_ct_not_inQ':
  "\<lbrace>\<lambda>s. all_invs_but_ct_not_inQ' s \<and> st_tcb_at' runnable' t s
        \<and> valid_objs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s
        \<and> sch_act_simple s \<and> ex_nonz_cap_to' t s\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. all_invs_but_ct_not_inQ'\<rbrace>"
  apply wp
   apply (rule hoare_use_eq_irq_node', wp)
   apply (wpsimp wp: typ_at_lift_valid_irq_node' valid_irq_handlers_lift' valid_dom_schedule'_lift
                     cteCaps_of_ctes_of_lift irqs_masked_lift)
  apply clarsimp
  apply (intro conjI; fastforce?)
  by (metis fold_list_refs_of_replies')

lemma possibleSwitchTo_invs'[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' tptr\<rbrace>
   possibleSwitchTo tptr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: possibleSwitchTo_def)
  apply (wpsimp wp: hoare_vcg_imp_lift threadGet_wp inReleaseQueue_wp ssa_invs')
  apply (clarsimp simp: invs'_def valid_state'_def valid_idle'_def
                        idle_tcb'_def pred_tcb_at'_def obj_at'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma possibleSwitchTo_sch_act_not_other:
  "\<lbrace>\<lambda>s. sch_act_not t' s \<and> t' \<noteq> t\<rbrace>
   possibleSwitchTo t
   \<lbrace>\<lambda>_. sch_act_not t'\<rbrace>"
  apply (clarsimp simp: possibleSwitchTo_def)
  apply (wpsimp wp: threadGet_wp inReleaseQueue_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma setReleaseQueue_tcb_at'[wp]:
 "setReleaseQueue qs \<lbrace>typ_at' T tcbPtr\<rbrace>"
  unfolding setReleaseQueue_def
  by wpsimp

lemma setReleaseQueue_ksReleaseQueue[wp]:
  "\<lbrace>\<lambda>_. P qs\<rbrace> setReleaseQueue qs \<lbrace>\<lambda>_ s. P (ksReleaseQueue s)\<rbrace>"
  by (wpsimp simp: setReleaseQueue_def)

lemma setReleaseQueue_pred_tcb_at'[wp]:
 "setReleaseQueue qs \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wpsimp simp: setReleaseQueue_def)

crunches tcbReleaseDequeue
  for valid_pspace'[wp]: valid_pspace'
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and list_refs_of_replies'[wp]: "\<lambda>s. P (list_refs_of_replies' s)"
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. Q (sc_at'_n n p s)"
  and valid_irq_states'[wp]: valid_irq_states'
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and valid_machine_state'[wp]: valid_machine_state'
  (simp: crunch_simps wp: crunch_wps)

end

global_interpretation tcbReleaseDequeue: typ_at_all_props' tcbReleaseDequeue
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

crunches tcbReleaseDequeue
  for cur_tcb'[wp]: cur_tcb'
  (simp: crunch_simps cur_tcb'_def wp: crunch_wps threadSet_cur ignore: threadSet)

lemma tcbInReleaseQueue_update_tcb_cte_cases:
  "(a, b) \<in> ran tcb_cte_cases \<Longrightarrow> a (tcbInReleaseQueue_update f tcb) = a tcb"
  unfolding tcb_cte_cases_def
  by (case_tac tcb; fastforce simp: tcbInReleaseQueue_update_def)

lemma tcbInReleaseQueue_update_ctes_of[wp]:
  "threadSet (tcbInReleaseQueue_update f) x \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_ofT simp: tcbInReleaseQueue_update_tcb_cte_cases)

crunches tcbReleaseDequeue
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and valid_idle'[wp]: valid_idle'
  and valid_irq_handlers'[wp]: valid_irq_handlers'
  and valid_pde_mappings'[wp]: valid_pde_mappings'
  and ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  and if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  (ignore: threadSet
     simp: crunch_simps tcbInReleaseQueue_update_tcb_cte_cases
       wp: crunch_wps threadSet_idle' threadSet_irq_handlers' threadSet_ct_idle_or_in_cur_domain'
           threadSet_ifunsafe'T)

lemma tcbReleaseDequeue_valid_objs'[wp]:
  "tcbReleaseDequeue \<lbrace>valid_objs'\<rbrace>"
  unfolding tcbReleaseDequeue_def
  by (wpsimp simp: setReprogramTimer_def setReleaseQueue_def wp: threadSet_valid_objs')

lemma tcbReleaseDequeue_sch_act_wf[wp]:
  "tcbReleaseDequeue \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding tcbReleaseDequeue_def
  by (wpsimp simp: setReprogramTimer_def setReleaseQueue_def wp: threadSet_sch_act)

lemma tcbReleaseDequeue_if_live_then_nonz_cap'[wp]:
  "tcbReleaseDequeue \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbReleaseDequeue_def
  apply (wpsimp simp: setReprogramTimer_def setReleaseQueue_def tcbInReleaseQueue_update_tcb_cte_cases wp: threadSet_iflive'T)
  by auto

lemma tcbReleaseDequeue_ct_not_inQ[wp]:
  "tcbReleaseDequeue \<lbrace>ct_not_inQ\<rbrace>"
  unfolding tcbReleaseDequeue_def
  by (wpsimp simp: setReprogramTimer_def setReleaseQueue_def wp: threadSet_not_inQ)

lemma tcbReleaseDequeue_valid_queues[wp]:
  "tcbReleaseDequeue \<lbrace>valid_queues\<rbrace>"
  unfolding tcbReleaseDequeue_def
  apply (wpsimp simp: setReprogramTimer_def setReleaseQueue_def wp: threadSet_valid_queues)
  by (auto simp: valid_queues_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                 bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def inQ_def)

lemma tcbReleaseDequeue_valid_queues'[wp]:
  "tcbReleaseDequeue \<lbrace>valid_queues'\<rbrace>"
  unfolding tcbReleaseDequeue_def
  apply (wpsimp simp: setReprogramTimer_def setReleaseQueue_def wp: threadSet_valid_queues')
  by (auto simp: valid_queues'_def valid_queues_no_bitmap_def valid_bitmapQ_def bitmapQ_def
                 bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def inQ_def)

lemma tcbReleaseDequeue_valid_release_queue[wp]:
  "\<lbrace>valid_release_queue and (\<lambda>s. distinct (ksReleaseQueue s))\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  unfolding tcbReleaseDequeue_def
  apply (wpsimp simp: setReprogramTimer_def setReleaseQueue_def wp: threadSet_valid_release_queue)
  apply (clarsimp simp: valid_release_queue_def)
  by (case_tac "ksReleaseQueue s"; simp)

lemma tcbReleaseDequeue_valid_release_queue'[wp]:
  "\<lbrace>valid_release_queue' and (\<lambda>s. ksReleaseQueue s \<noteq> [])\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  unfolding tcbReleaseDequeue_def
  apply (wpsimp simp: setReprogramTimer_def setReleaseQueue_def wp: threadSet_valid_release_queue')
  apply (clarsimp simp: valid_release_queue'_def split: list.splits)
  by (metis list.exhaust_sel set_ConsD)

lemma tcbReleaseDequeue_invs'[wp]:
  "\<lbrace>invs'
    and (\<lambda>s. ksReleaseQueue s \<noteq> [])
    and distinct_release_queue\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: invs'_def valid_state'_def
               wp: valid_irq_node_lift irqs_masked_lift untyped_ranges_zero_lift
                   cteCaps_of_ctes_of_lift)

lemma tcbReleaseDequeue_ksCurThread[wp]:
  "\<lbrace>\<lambda>s. P (hd (ksReleaseQueue s)) (ksCurThread s)\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>r s. P r (ksCurThread s)\<rbrace>"
  unfolding tcbReleaseDequeue_def
  by (wpsimp simp: setReprogramTimer_def setReleaseQueue_def)

lemma tcbReleaseDequeue_runnable'[wp]:
  "\<lbrace>\<lambda>s. st_tcb_at' runnable' (hd (ksReleaseQueue s)) s\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>r s. st_tcb_at' runnable' r s\<rbrace>"
  unfolding tcbReleaseDequeue_def
  by (wpsimp simp: setReprogramTimer_def wp: threadSet_pred_tcb_no_state)

crunches setReprogramTimer, possibleSwitchTo
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  (wp: crunch_wps simp: crunch_simps)

lemma tcbReleaseDequeue_distinct_release_queue[wp]:
  "tcbReleaseDequeue \<lbrace>distinct_release_queue\<rbrace>"
  unfolding tcbReleaseDequeue_def
  by (wpsimp simp: distinct_tl)

lemma getReleaseQueue_sp:
  "\<lbrace>Q\<rbrace> getReleaseQueue \<lbrace>\<lambda>r. (\<lambda>s. r = ksReleaseQueue s) and Q\<rbrace>"
  unfolding getReleaseQueue_def
  by wpsimp

lemma releaseQNonEmptyAndReady_implies_releaseQNonEmpty:
  "the (releaseQNonEmptyAndReady s) \<Longrightarrow> ksReleaseQueue s \<noteq> []"
  by (clarsimp simp: releaseQNonEmptyAndReady_def readTCBRefillReady_def readReleaseQueue_def
                     obind_def omonad_defs)

lemma awaken_invs':
  "awaken \<lbrace>invs'\<rbrace>"
  apply (clarsimp simp: awaken_def awakenBody_def)
  apply (rule_tac I="\<lambda>_. invs'" in valid_whileLoop; simp add: runReaderT_def)
  apply (rule hoare_seq_ext[OF _ getReleaseQueue_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply wpsimp
   apply (rule hoare_drop_imps)
   apply (rule tcbReleaseDequeue_invs')
  apply (fastforce intro!: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  done

lemma schedule_invs':
  "\<lbrace>invs'\<rbrace>
   ThreadDecls_H.schedule
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply ssa_wp[wp del]
  supply if_split [split del]
  apply (simp add: schedule_def)
  apply (rule_tac hoare_seq_ext, rename_tac t)
   apply (rule_tac Q="invs'" in hoare_weaken_pre)
    apply (rule_tac hoare_seq_ext[OF _ getCurThread_sp])
    apply (rule_tac hoare_seq_ext[OF _ isSchedulable_sp])
    apply (rule_tac hoare_seq_ext[OF _ getSchedulerAction_sp])
    apply (rule hoare_seq_ext)
     apply (wpsimp wp: switchSchedContext_invs')
    apply (wpsimp wp: scheduleChooseNewThread_invs' isSchedulable_wp setSchedulerAction_invs'
                      ssa_invs' switchToThread_invs hoare_vcg_disj_lift
                      switchToThread_tcb_in_cur_domain')
               apply (rule hoare_pre_cont)
              apply (wpsimp wp: switchToThread_invs hoare_vcg_disj_lift switchToThread_tcb_in_cur_domain')
             apply (rule_tac hoare_strengthen_post, rule switchToThread_ct_not_queued_2)
             apply (clarsimp simp: pred_neg_def o_def)
            apply clarsimp
            apply (wpsimp simp: isHighestPrio_def')
           apply (wpsimp wp: curDomain_wp)
          apply (wpsimp simp: scheduleSwitchThreadFastfail_def)
         apply (rename_tac tPtr x idleThread targetPrio)
         apply (rule_tac Q="\<lambda>_. invs' and st_tcb_at' runnable' tPtr and (\<lambda>s. action = ksSchedulerAction s)
                                and tcb_in_cur_domain' tPtr" in hoare_strengthen_post[rotated])
          apply (prop_tac "st_tcb_at' runnable' tPtr s \<Longrightarrow> obj_at' (\<lambda>a. activatable' (tcbState a)) tPtr s")
           apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
          apply (prop_tac "all_invs_but_ct_idle_or_in_cur_domain' s")
           apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def invs'_def valid_state'_def)
          apply fastforce
         apply (wpsimp wp: threadGet_wp hoare_drop_imp hoare_vcg_ex_lift)
        apply (rename_tac tPtr x idleThread)
        apply (rule_tac Q="\<lambda>_. invs'
                               and st_tcb_at' runnable' tPtr and (\<lambda>s. action = ksSchedulerAction s)
                               and tcb_in_cur_domain' tPtr" in hoare_strengthen_post[rotated])
         apply (subst obj_at_ko_at'_eq[symmetric], simp)
        apply (wpsimp wp: threadGet_wp hoare_drop_imp hoare_vcg_ex_lift)
       apply (rename_tac tPtr x)
       apply (rule_tac Q="\<lambda>_. invs'
                              and st_tcb_at' runnable' tPtr and (\<lambda>s. action = ksSchedulerAction s)
                              and tcb_in_cur_domain' tPtr" in hoare_strengthen_post[rotated])
        apply (subst obj_at_ko_at'_eq[symmetric], simp)
       apply (wpsimp wp: tcbSchedEnqueue_invs'_not_ResumeCurrentThread isSchedulable_wp)+
    apply (subgoal_tac "sch_act_wf (ksSchedulerAction s) s")
     apply (fastforce split: if_split dest: isSchedulable_bool_runnableE)
    apply clarsimp
   apply assumption
  apply (wpsimp wp: awaken_invs')
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
  apply (simp add: Thread_H.switchToThread_def ARM_H.switchToThread_def storeWordUser_def)
  apply (wp setCurThread_nosch hoare_drop_imp |simp)+
  done

lemma stit_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    switchToIdleThread
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: Thread_H.switchToIdleThread_def
                   ARM_H.switchToIdleThread_def  storeWordUser_def)
  apply (wp setCurThread_nosch | simp add: getIdleThread_def)+
  done

lemma chooseThread_nosch:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
  chooseThread
  \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  unfolding chooseThread_def Let_def numDomains_def curDomain_def
  apply (simp only: return_bind, simp)
  apply (wp findM_inv | simp)+
  apply (case_tac queue)
  apply (wp stt_nosch isSchedulable_wp | simp add: curDomain_def bitmap_fun_defs)+
  done

crunches switchSchedContext, setNextInterrupt
  for ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

lemma schedule_sch:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  unfolding schedule_def
  by (wpsimp wp: setSchedulerAction_direct simp: getReprogramTimer_def scheduleChooseNewThread_def)

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

\<comment>\<open>FIXME: maybe move this block\<close>

crunches getReprogramTimer, getCurTime, getRefills, getReleaseQueue, refillSufficient,
         refillReady, isRoundRobin
  for inv[wp]: P



\<comment>\<open>end: maybe move this block\<close>

lemma st_tcb_at_activatable_coerce_concrete:
  assumes t: "st_tcb_at activatable t s"
  assumes sr: "(s, s') \<in> state_relation"
  assumes tcb: "tcb_at' t s'"
  shows "st_tcb_at' activatable' t s'"
  using t
  apply -
  apply (rule ccontr)
  apply (drule pred_tcb_at'_Not[THEN iffD2, OF conjI, OF tcb])
  apply (drule st_tcb_at_coerce_abstract[OF _ sr])
  apply (clarsimp simp: st_tcb_def2)
  apply (case_tac "tcb_state tcb"; simp)
  done

lemma ct_in_state'_activatable_coerce_concrete:
  "\<lbrakk>ct_in_state activatable s; (s, s') \<in> state_relation; cur_tcb' s'\<rbrakk>
    \<Longrightarrow> ct_in_state' activatable' s'"
   unfolding ct_in_state'_def cur_tcb'_def ct_in_state_def
   apply (rule st_tcb_at_activatable_coerce_concrete[rotated], simp, simp)
   apply (frule curthread_relation, simp)
   done

lemma schedule_ct_activatable':
  "\<lbrace>invs'\<rbrace> ThreadDecls_H.schedule \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  supply ssa_wp[wp del]
  apply (simp add: schedule_def)
     apply wpsimp
  oops (* I believe that the coerce lemma above (ct_in_state'_activatable_coerce_concrete) can
           be used to avoid the need for this lemma. This should be confirmed at some point. *)

lemma threadSet_sch_act_sane[wp]:
  "\<lbrace>sch_act_sane\<rbrace> threadSet f t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  by (wp sch_act_sane_lift)

lemma rescheduleRequired_sch_act_sane[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: rescheduleRequired_def sch_act_sane_def
                   setSchedulerAction_def)
  by (wp isSchedulable_wp | wpc | clarsimp)+

crunch sch_act_sane[wp]: setThreadState, setBoundNotification "sch_act_sane"
  (simp: crunch_simps wp: crunch_wps)

lemma weak_sch_act_wf_at_cross:
  assumes sr: "(s,s') \<in> state_relation"
  assumes aligned: "pspace_aligned s"
  assumes distinct: "pspace_distinct s"
  assumes t: "valid_sched_action s"
  shows "weak_sch_act_wf (ksSchedulerAction s') s'"
  using assms
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def weak_sch_act_wf_def)
  apply (frule state_relation_sched_act_relation)
  apply (rename_tac t)
  apply (drule_tac x=t in spec)
  apply (prop_tac "scheduler_action s = switch_thread t")
   apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                scheduler_action.simps)
  apply (intro conjI impI)
   apply (rule st_tcb_at_runnable_cross; fastforce?)
   apply (clarsimp simp: vs_all_heap_simps pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: switch_in_cur_domain_def in_cur_domain_def etcb_at_def vs_all_heap_simps)
  apply (prop_tac "tcb_at t s")
   apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (frule state_relation_pspace_relation)
  apply (frule (3) tcb_at_cross)
  apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def projectKOs)
  apply (frule curdomain_relation)
  apply (frule (2) pspace_relation_tcb_domain_priority)
  apply simp
  done

lemma possibleSwitchTo_corres:
  "corres dc
    (valid_sched_action and tcb_at t and pspace_aligned and pspace_distinct and valid_tcbs)
    (valid_queues and valid_queues' and valid_release_queue_iff and valid_tcbs')
      (possible_switch_to t)
      (possibleSwitchTo t)"
  supply dc_simp [simp del]
  apply (rule corres_cross_add_guard[where Q="tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (simp add: possible_switch_to_def possibleSwitchTo_def cong: if_cong)
  apply (rule corres_guard_imp)
    apply (simp add: get_tcb_obj_ref_def)
    apply (rule corres_split_deprecated[OF _ threadget_corres], simp)
      apply (rule corres_split_deprecated[OF _ inReleaseQueue_corres], simp)
        apply (rule corres_when[rotated])
         apply (rule corres_split_deprecated[OF _ curDomain_corres], simp)
           apply (rule corres_split_deprecated[OF _ threadget_corres[where r="(=)"]])
              apply (rule corres_split_deprecated[OF _ get_sa_corres])
                apply (rule corres_if, simp)
                 apply (rule tcbSchedEnqueue_corres)
                apply (rule corres_if[rotated], simp)
                  apply (rule corres_split_deprecated[OF _ rescheduleRequired_corres])
                    apply (rule tcbSchedEnqueue_corres)
                   apply wp+
                 apply (rule set_sa_corres, simp)
                apply (case_tac rvb; simp)
               apply (wpsimp simp: tcb_relation_def if_apply_def2 valid_sched_action_def
                               wp: hoare_drop_imp inReleaseQueue_inv)+
  done

lemma ct_active_cross:
  "\<lbrakk> (s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; ct_active s \<rbrakk>
     \<Longrightarrow> ct_active' s'"
  by (clarsimp simp: state_relation_def ct_in_state_def ct_in_state'_def
                     st_tcb_at_runnable_cross runnable_eq_active runnable_eq_active'[symmetric])

\<comment> \<open>Strengthen the consequent as necessary, there's more that can be derived from the assumptions\<close>
lemma ct_released_cross_weak:
  "\<lbrakk> (s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; ct_released s; cur_tcb' s' \<rbrakk>
     \<Longrightarrow> bound_sc_tcb_at' bound (ksCurThread s') s'"
  apply (clarsimp simp: vs_all_heap_simps obj_at_kh_kheap_simps)
  apply (clarsimp simp: state_relation_def pspace_relation_def )
  apply (erule_tac x="ksCurThread s'" in ballE)
   apply (auto simp: vs_all_heap_simps other_obj_relation_def tcb_relation_def
                          cur_tcb'_def pred_tcb_at'_def obj_at'_def projectKOs
                   split: kernel_object.splits)
  done

lemma setReprogramTimer_corres[corres]:
  "corres dc \<top> \<top> (modify (reprogram_timer_update (\<lambda>_. b))) (setReprogramTimer b)"
  apply (unfold setReprogramTimer_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma getCurTime_corres[corres]:
  "corres (=) \<top> \<top> (gets cur_time) (getCurTime)"
  apply (clarsimp simp: getCurTime_def state_relation_def)
  done

lemma readRefillReady_simp:
  "readRefillReady scp s
   = (case readSchedContext scp s
        of None \<Rightarrow> None
         | Some sc' \<Rightarrow> Some (rTime (refillHd sc') \<le> (ksCurTime s) + kernelWCETTicks))"
  by (clarsimp simp: readRefillReady_def readCurTime_def readSchedContext_SomeD asks_def obind_def)

lemma readRefillReady_no_ofail[wp]:
  "no_ofail (sc_at' t) (readRefillReady t)"
  apply (clarsimp simp: readRefillReady_def readSchedContext_def)
  apply (rule no_ofail_pre_imp[rotated])
   apply (rule no_ofail_obind2[where R="\<lambda>_. \<top> and \<top>", rotated -1])
     apply (rule no_ofail_obind2[rotated -1])
       apply wp
      apply (rule no_ofail_readCurTime)
     apply (clarsimp simp: ovalid_def)
    apply wp
  by (simp add: ovalid_def)+

lemma refillReady_corres:
  "corres (=) (pspace_aligned and pspace_distinct and valid_objs
               and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr and is_active_sc sc_ptr)
              valid_objs'
              (get_sc_refill_ready sc_ptr)
              (refillReady sc_ptr)"
  apply (rule corres_cross[where Q' = "sc_at' sc_ptr", OF sc_at'_cross_rel])
   apply (fastforce dest: valid_objs_valid_sched_context_size
                    simp: vs_all_heap_simps obj_at_def is_sc_obj_def)
  apply (clarsimp simp: refill_ready_def refillReady_def get_sc_refill_ready_def)
  apply (subst gets_the_corres)
    apply (rule no_ofail_pre_imp[rotated])
     apply (rule no_ofail_read_sc_refill_ready)
    apply (clarsimp simp: vs_all_heap_simps obj_at_def)
   apply wpsimp
  apply (clarsimp simp: obj_at_def is_sc_obj dest!: no_ofailD[OF readRefillReady_no_ofail]
                 intro: no_ofailD[OF no_ofail_read_sc_refill_ready])
  apply (insert no_ofailD[OF no_ofail_read_sc_refill_ready, rule_format])
  apply (drule_tac x=s and y=sc_ptr in meta_spec2)
  apply (prop_tac "\<exists>sc n. kheap s sc_ptr = Some (kernel_object.SchedContext sc n)")
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  apply clarsimp
  apply (clarsimp simp: read_sc_refill_ready_simp readRefillReady_simp readSchedContext_def
                        read_sched_context_def
                 split: option.splits dest!: readObject_misc_ko_at')
  apply (rename_tac n sc' sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc'[rotated])
  apply (elim conjE)
  apply (frule state_relation_pspace_relation)
  apply (prop_tac "valid_sched_context_size n")
   apply (fastforce dest: valid_objs_valid_sched_context_size)
  apply (prop_tac "sc_relation sc n sc'")
   apply (clarsimp simp: pspace_relation_def)
   apply (drule_tac x=sc_ptr in bspec, blast)
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (frule refill_hd_relation2[rotated 2])
    apply simp
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  apply (clarsimp simp: kernelWCETTicks_def refill_ready_def state_relation_def)
  done

lemma readTCBRefillReady_no_ofail:
  "no_ofail (\<lambda>s'. obj_at' (\<lambda>tcb. \<exists>sc. tcbSchedContext tcb = Some sc \<and> sc_at' sc s') t s')
            (readTCBRefillReady t)"
  unfolding readTCBRefillReady_def
  apply (wpsimp simp: obj_at'_def)
  apply (wpsimp wp: ovalid_threadRead simp: obj_at'_def)
  done

lemma readTCBRefillReady_simp:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_objs s;
    active_sc_tcb_at t s; active_sc_valid_refills s; valid_objs' s'\<rbrakk>
   \<Longrightarrow> read_tcb_refill_ready t s = readTCBRefillReady t s'"
  apply (frule (1) active_implies_valid_refills_tcb_at)
  apply (clarsimp simp: obj_at_kh_kheap_simps vs_all_heap_simps)
  apply (rename_tac scp tcb sc n)
  apply (prop_tac "tcb_at' t s' \<and> sc_at' scp s'")
   apply (fastforce dest!: state_relationD intro!: sc_at_cross tcb_at_cross
                     simp: obj_at_def is_tcb is_sc_obj
                     elim: valid_sched_context_size_objsI)
  apply clarsimp
  apply (prop_tac "bound (read_tcb_refill_ready t s)")
   apply (clarsimp intro!: no_ofailD[OF no_ofail_read_tcb_refill_ready]
                     simp: pred_tcb_at_def obj_at_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=t in bspec, blast)
  apply (drule_tac x="(t, other_obj_relation)" in bspec, clarsimp)
  apply (clarsimp simp: other_obj_relation_def tcb_relation_def obj_at'_def projectKOs)
  apply (prop_tac "bound (readTCBRefillReady t s')")
   apply (clarsimp intro!: no_ofailD[OF readTCBRefillReady_no_ofail])
   apply (clarsimp simp: obj_at'_def projectKOs)
   apply (rule_tac x=scp in exI; clarsimp)
  apply clarsimp
  apply (clarsimp simp: read_tcb_refill_ready_def readTCBRefillReady_def oassert_opt_def
                        readRefillReady_simp read_sc_refill_ready_simp refill_ready'_def obj_at'_def
                        projectKOs
                 dest!: read_tcb_obj_ref_SomeD read_sched_context_SomeD readSchedContext_SomeD
                        threadRead_SomeD
                 split: option.split_asm)
  apply (rename_tac sc' sc_ptr tcbPtr)
  apply (prop_tac "valid_sched_context' sc' s' \<and> valid_sched_context_size' sc'")
   apply (frule_tac k=sc' and p=sc_ptr in sc_ko_at_valid_objs_valid_sc'[rotated])
    apply (clarsimp simp: obj_at'_def projectKOs)
   apply simp
  apply (frule state_relation_pspace_relation)
  apply (prop_tac "sc_relation sc n sc'")
   apply (clarsimp simp: pspace_relation_def)
   apply (drule_tac x=sc_ptr in bspec, blast)
   apply (fastforce simp: obj_at'_def projectKOs split: if_splits)
  apply (frule refill_hd_relation2)
    apply (clarsimp simp: vs_all_heap_simps valid_refills_def rr_valid_refills_def
                   split: if_splits)
   apply (fastforce dest!: sc_ko_at_valid_objs_valid_sc'
                     simp: obj_at'_def projectKOs)
  apply (clarsimp simp: kernelWCETTicks_def state_relation_def)
  done

lemma getReleaseQueue_corres[corres]:
  "corres (=) \<top> \<top> (gets release_queue) (getReleaseQueue)"
  unfolding getReleaseQueue_def
  apply (rule corres_gets_trivial)
  by (clarsimp simp: state_relation_def release_queue_relation_def)

lemma releaseQNonEmptyAndReady_simp:
  "releaseQNonEmptyAndReady s
    = (if ksReleaseQueue s = []
          then Some False
          else readTCBRefillReady (head (ksReleaseQueue s)) s)"
  by (clarsimp simp: releaseQNonEmptyAndReady_def readReleaseQueue_def asks_def obind_def)

lemma releaseQNonEmptyAndReady_eq:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s;
     valid_objs s; valid_release_q s;
     active_sc_valid_refills s; valid_objs' s'\<rbrakk>
   \<Longrightarrow> read_release_q_non_empty_and_ready s = releaseQNonEmptyAndReady s'"
  apply (clarsimp simp: read_release_q_non_empty_and_ready_simp releaseQNonEmptyAndReady_simp
                        readTCBRefillReady_simp release_queue_relation_def
                 dest!: state_relationD)
  by (fastforce simp: state_relation_def release_queue_relation_def
              intro!: readTCBRefillReady_simp valid_release_q_active_sc)

lemma ksReleaseQueue_length_well_founded:
  "wf {((r :: unit, s :: kernel_state), (r', s')). length (ksReleaseQueue s)
                                                    < length (ksReleaseQueue s')}"
  apply (insert wf_inv_image[where r="{(m, n). m < n}"
                               and f="\<lambda>(r :: unit, s :: kernel_state). length (ksReleaseQueue s)"])
  apply (clarsimp simp: inv_image_def)
  apply (prop_tac "wf {(m, n). m < n}")
   apply (fastforce intro: wf)
  apply (drule meta_mp)
   apply simp
  apply (prop_tac "{(x :: unit \<times> global.kernel_state, y ::  unit \<times> global.kernel_state).
                     (case x of (r, s) \<Rightarrow> length (ksReleaseQueue s))
                      < (case y of (r, s) \<Rightarrow> length (ksReleaseQueue s))}
                   = {((r, s), r', s'). length (ksReleaseQueue s) < length (ksReleaseQueue s')}")
   apply fastforce
  apply fastforce
  done

lemma tcbReleaseDequeue_ksReleaseQueue_length_helper:
  "\<lbrace>\<lambda>s'. ksReleaseQueue s' \<noteq> [] \<and> s' = s\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>r' s'. length (ksReleaseQueue s') < length (ksReleaseQueue s)\<rbrace>"
  apply (wpsimp simp: tcbReleaseDequeue_def getReleaseQueue_def setReleaseQueue_def)
  done

lemma tcbReleaseDequeue_ksReleaseQueue_length:
  "\<lbrace>\<lambda>s'. the (releaseQNonEmptyAndReady s') \<and> s' = s\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>r' s'. length (ksReleaseQueue s') < length (ksReleaseQueue s)\<rbrace>"
  apply (wpsimp wp: tcbReleaseDequeue_ksReleaseQueue_length_helper)
  apply (fastforce dest: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  done

lemma awakenBody_ksReleaseQueue_length:
  "\<lbrace>\<lambda>s'. the (releaseQNonEmptyAndReady s') \<and> s' = s\<rbrace>
   awakenBody
   \<lbrace>\<lambda>r' s'. length (ksReleaseQueue s') < length (ksReleaseQueue s)\<rbrace>"
  apply (clarsimp simp: awakenBody_def)
  apply (wpsimp wp: tcbReleaseDequeue_ksReleaseQueue_length hoare_drop_imps)
  done

lemma awaken_terminates:
  "whileLoop_terminates (\<lambda>_ s'. (the (releaseQNonEmptyAndReady s'))) (\<lambda>_. awakenBody) r' s'"
  apply (rule_tac R="{((r', s'), (r, s)). length (ksReleaseQueue s') < length (ksReleaseQueue s)}"
               in whileLoop_terminates_inv)
    apply simp
   apply clarsimp
   apply (rule awakenBody_ksReleaseQueue_length)
  apply (rule ksReleaseQueue_length_well_founded)
  done

lemma reprogram_timer_update_release_queue_update_monad_commute:
  "monad_commute \<top> (modify (reprogram_timer_update (\<lambda>_. b))) (modify (release_queue_update q))"
  apply (clarsimp simp: monad_commute_def modify_def get_def put_def bind_def return_def)
  done

(* FIXME RT: move? *)
lemma filter_hd_equals_tl:
  "\<lbrakk>distinct q; q \<noteq> []\<rbrakk> \<Longrightarrow> filter ((\<noteq>) (hd q)) q = tl q"
  apply (induct q rule: length_induct)
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (fastforce simp: filter_id_conv)
  done

lemma release_queue_modify_tl:
  "\<lbrakk>(s, s') \<in> state_relation; valid_release_q s; release_queue s \<noteq> []\<rbrakk>
   \<Longrightarrow> (s\<lparr>release_queue := filter ((\<noteq>) (hd (release_queue s))) (release_queue s)\<rparr>,
        s'\<lparr>ksReleaseQueue := tl (release_queue s)\<rparr>) \<in> state_relation"
  apply (clarsimp simp: state_relation_def cdt_relation_def)
  apply (clarsimp simp: release_queue_relation_def)
  apply (prop_tac "ksReleaseQueue s' \<noteq> []", fastforce)
  apply (rule filter_hd_equals_tl)
   apply (prop_tac "distinct (release_queue s)")
    apply (clarsimp simp: valid_release_q_def)
   apply simp+
  done

lemma ksReleaseQueue_runnable'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_release_q)
             (\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s')"
  apply (clarsimp simp: cross_rel_def)
  apply (clarsimp simp: valid_release_q_def release_queue_relation_def)
  apply (frule state_relation_release_queue_relation)
  apply (clarsimp simp: release_queue_relation_def)
  apply (prop_tac "st_tcb_at runnable t s")
   apply (fastforce simp: obj_at_kh_kheap_simps)
  apply (fastforce intro: sts_rel_runnable
                   dest!: st_tcb_at_coerce_concrete
                    simp: st_tcb_at'_def obj_at'_def)
  done

lemma tcbReleaseDequeue_corres:
  "corres (=) (pspace_aligned and pspace_distinct and valid_release_q and (\<lambda>s. release_queue s \<noteq> []))
              \<top>
              tcb_release_dequeue
              tcbReleaseDequeue"
   (is "corres _ _ ?conc _ _")
  apply (rule corres_cross[where Q'="\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s'"
                           , OF ksReleaseQueue_runnable'_cross_rel], blast)
  apply (clarsimp simp: tcb_release_dequeue_def tcb_release_remove_def tcbReleaseDequeue_def
                        setReleaseQueue_def tcb_sched_dequeue_def)
  apply (rule corres_symb_exec_l[rotated 2, OF gets_sp]; (solves wpsimp)?)
  apply (rename_tac rq)
  apply (simp add: bind_assoc)
  apply (rule corres_split'[rotated 2, OF gets_sp getReleaseQueue_sp])
   apply (corressimp corres: getReleaseQueue_corres)

  apply clarsimp
  apply (rename_tac rq')
  apply (rule_tac F="rq' \<noteq> [] \<and> rq' = rq" in corres_req)
   apply (clarsimp simp: state_relation_def release_queue_relation_def)
  apply clarsimp

  apply (subst monad_commute_simple'[OF reprogram_timer_update_release_queue_update_monad_commute])
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule_tac P="valid_release_q and (\<lambda>s. release_queue s \<noteq> [] \<and> release_queue s = rq)"
                   and P'="\<lambda>s'. ksReleaseQueue s' \<noteq> []"
                    in corres_inst)
       apply (rule corres_modify)
       apply (fastforce intro: release_queue_modify_tl)
      apply wpsimp
      apply (rule corres_add_noop_lhs)
      apply (rule corres_split[OF threadSet_corres_noop])
              apply (clarsimp simp: tcb_relation_def)+
        apply (rule corres_split[OF setReprogramTimer_corres])
          apply wpsimp+
  apply (fastforce simp: st_tcb_at'_def)
  done

lemma tcbInReleaseQueue_update_valid_tcbs'[wp]:
  "threadSet (tcbInReleaseQueue_update f) tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_tcbs')
  done

lemma tcbReleaseDequeue_valid_tcbs'[wp]:
  "tcbReleaseDequeue \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: tcbReleaseDequeue_def setReleaseQueue_def setReprogramTimer_def)
  apply ((rule hoare_seq_ext_skip, wpsimp simp: valid_tcbs'_def) | wpsimp)+
  done

lemma ksReleaseQueue_distinct_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and valid_release_q)
             (\<lambda>s'. distinct (ksReleaseQueue s'))"
  apply (clarsimp simp: cross_rel_def)
  apply (fastforce dest: state_relation_release_queue_relation
                 intro!: tcb_at_cross
                   simp: valid_release_q_def release_queue_relation_def vs_all_heap_simps
                         obj_at_def is_tcb_def)
  done

lemma ksReleaseQueue_nonempty_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and (\<lambda>s. release_queue s \<noteq> []))
             (\<lambda>s'. ksReleaseQueue s' \<noteq> [])"
  apply (clarsimp simp: cross_rel_def)
   apply (fastforce dest: state_relation_release_queue_relation
                  intro!: tcb_at_cross
                    simp: valid_release_q_def release_queue_relation_def vs_all_heap_simps
                          obj_at_def is_tcb_def)
  done

lemma isRunnable_no_fail[wp]:
  "no_fail (tcb_at' tcbPtr) (isRunnable tcbPtr)"
  apply (wpsimp simp: isRunnable_def)
  done

lemma awakenBody_corres:
  "corres dc ((pspace_aligned and pspace_distinct and valid_objs and valid_sched_action
               and valid_tcbs and valid_release_q)
              and (\<lambda>s. release_queue s \<noteq> []))
             (valid_objs' and valid_queues and valid_queues' and valid_release_queue_iff)
             awaken_body
             awakenBody"
  (is "corres _ (?pred and _) ?conc _ _")
  apply (rule corres_cross[where Q'="\<lambda>s'. distinct (ksReleaseQueue s')"
                           , OF ksReleaseQueue_distinct_cross_rel], blast)
  apply (rule corres_cross[where Q'="\<lambda>s'. ksReleaseQueue s' \<noteq> []"
                           , OF ksReleaseQueue_nonempty_cross_rel], blast)
  apply (rule corres_cross[where Q'="\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s'"
                           , OF ksReleaseQueue_runnable'_cross_rel], blast)

  apply (clarsimp simp: awaken_body_def awakenBody_def)
  apply (rule corres_symb_exec_r[rotated, OF getReleaseQueue_sp])
    apply (wpsimp wp: gets_sp simp: getReleaseQueue_def)
   apply (wpsimp wp: gets_exs_valid
               simp: getReleaseQueue_def)
  apply (rule corres_symb_exec_r[rotated, OF assert_inv]; (solves wpsimp)?)
  apply (rule_tac Q="\<lambda>rv. ?pred and tcb_at rv"
              and Q'="\<lambda>rv. ?conc and st_tcb_at' runnable' rv"
               in corres_split'[rotated 2])
     apply (wpsimp simp: tcb_release_dequeue_def)
     apply (force simp: valid_release_q_def vs_all_heap_simps obj_at_def is_tcb_def)
    apply wpsimp
   apply (corressimp corres: tcbReleaseDequeue_corres)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp, rotated]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def projectKOs objBitsKO_def)
   apply (case_tac "tcbState tcb'"; clarsimp)
  apply (corressimp corres: possibleSwitchTo_corres)
  done

lemma tcbReleaseDequeue_no_fail:
  "no_fail (\<lambda>s'. (\<forall>tcbPtr \<in> set (ksReleaseQueue s'). tcb_at' tcbPtr s') \<and> ksReleaseQueue s' \<noteq> [])
           tcbReleaseDequeue"
  apply (wpsimp simp: tcbReleaseDequeue_def getReleaseQueue_def setReleaseQueue_def
                      setReprogramTimer_def)
  done

lemma addToBitmap_no_fail[wp]:
  "no_fail \<top> (addToBitmap tdom tprio)"
  apply (wpsimp simp: bitmap_fun_defs)
  done

lemma tcbSchedEnqueue_no_fail[wp]:
  "no_fail (tcb_at' tcbPtr) (tcbSchedEnqueue tcbPtr)"
  apply (clarsimp simp: tcbSchedEnqueue_def)
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps)
  done

lemma inReleaseQueue_no_fail[wp]:
  "no_fail (tcb_at' tcbPtr) (inReleaseQueue tcbPtr)"
  apply (wpsimp simp: inReleaseQueue_def)
  done

lemma isSchedulable_no_fail:
  "no_fail (tcb_at' tcbPtr and valid_objs') (isSchedulable tcbPtr)"
  apply (clarsimp simp: isSchedulable_def isRunnable_def inReleaseQueue_def)
  apply (wpsimp wp: no_fail_bind hoare_vcg_imp_lift' hoare_vcg_conj_lift getTCB_wp)
  apply (fastforce dest: tcb_ko_at_valid_objs_valid_tcb'
                   simp: valid_tcb'_def)
  done

lemma rescheduleRequired_no_fail:
  "no_fail (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s') rescheduleRequired"
  apply (clarsimp simp: rescheduleRequired_def getSchedulerAction_def isSchedulable_def
                        setSchedulerAction_def)
  apply (wpsimp wp: isSchedulable_no_fail hoare_vcg_if_lift2 hoare_drop_imps)
  apply (clarsimp simp: weak_sch_act_wf_def)
  done

lemma possibleSwitchTo_no_fail:
  "no_fail (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s' \<and> tcb_at' tcbPtr s')
           (possibleSwitchTo tcbPtr)"
  apply (clarsimp simp: possibleSwitchTo_def inReleaseQueue_def curDomain_def getSchedulerAction_def
                        setSchedulerAction_def)
  apply (wpsimp wp: rescheduleRequired_no_fail threadGet_wp simp: setSchedulerAction_def)
  apply (fastforce simp: obj_at'_def projectKOs objBitsKO_def)
  done

lemma tcbReleaseDequeue_weak_sch_act_wf[wp]:
  "tcbReleaseDequeue \<lbrace>\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s'\<rbrace>"
  apply (clarsimp simp: tcbReleaseDequeue_def setReleaseQueue_def setReprogramTimer_def)
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: weak_sch_act_wf_def st_tcb_at'_def obj_at'_def projectKOs objBitsKO_def
                         tcb_in_cur_domain'_def ps_clear_def)
  done

lemma tcbReleaseQueue_tcb_at'_rv:
  "\<lbrace>\<lambda>s'. ksReleaseQueue s' \<noteq> [] \<and> tcb_at' (hd (ksReleaseQueue s')) s'\<rbrace>
   tcbReleaseDequeue
   \<lbrace>\<lambda>rv. tcb_at' rv\<rbrace>"
  apply (wpsimp simp: tcbReleaseDequeue_def setReleaseQueue_def)
  done

lemma awakenBody_no_fail:
  "no_fail (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s'
                 \<and> (\<forall>tcbPtr \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' tcbPtr s')
                 \<and> ksReleaseQueue s' \<noteq> [] \<and> distinct (ksReleaseQueue s'))
           awakenBody"
  apply (clarsimp simp: awakenBody_def setReprogramTimer_def)
  apply (wpsimp wp: possibleSwitchTo_no_fail tcbReleaseDequeue_no_fail tcbReleaseQueue_tcb_at'_rv
                    hoare_drop_imps
              simp: getReleaseQueue_def)
  apply fastforce
  done

lemma tcbReleaseDequeue_dequeue_inv:
  "tcbReleaseDequeue \<lbrace>\<lambda>s. tcbPtr \<notin> set (ksReleaseQueue s)\<rbrace>"
  apply (clarsimp simp: tcbReleaseDequeue_def)
  apply wpsimp
  apply (case_tac "ksReleaseQueue s = []"; simp add: list.set_sel(2))
  done

lemma tcbReleaseDequeue_st_tcb_at'[wp]:
  "tcbReleaseDequeue \<lbrace>st_tcb_at' st t\<rbrace>"
  apply (clarsimp simp: tcbReleaseDequeue_def setReprogramTimer_def setReleaseQueue_def)
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: st_tcb_at'_def obj_at'_def projectKOs objBitsKO_def)
  done

lemma awaken_corres:
  "corres dc (pspace_aligned and pspace_distinct and valid_objs and valid_release_q
              and valid_sched_action and valid_tcbs and active_sc_valid_refills)
             (\<lambda>s'. weak_sch_act_wf (ksSchedulerAction s') s' \<and> valid_objs' s' \<and> valid_queues s'
                   \<and> valid_queues' s' \<and> valid_release_queue_iff s')
             Schedule_A.awaken
             awaken"
  apply (rule corres_cross[where Q'="\<lambda>s'. \<forall>t \<in> set (ksReleaseQueue s'). st_tcb_at' runnable' t s'"
                           , OF ksReleaseQueue_runnable'_cross_rel], blast)
  apply (rule corres_cross[where Q'="\<lambda>s'. distinct (ksReleaseQueue s')"
                           , OF ksReleaseQueue_distinct_cross_rel], blast)
  apply (clarsimp simp: awaken_def Schedule_A.awaken_def runReaderT_def)
  apply (rule corres_whileLoop_inv; simp)
       apply (simp add: releaseQNonEmptyAndReady_eq)
      apply (rule corres_guard_imp)
        apply (rule awakenBody_corres)
       apply (fastforce simp: read_release_q_non_empty_and_ready_simp)
      apply simp
     apply (clarsimp simp: pred_conj_def)
     apply (intro hoare_vcg_conj_lift_pre_fix
            ; (solves \<open>wpsimp simp: Schedule_A.awaken_body_def tcb_release_dequeue_def\<close>)?)
     apply (wpsimp wp: awaken_body_valid_sched_action)
     apply (frule valid_release_q_read_release_q_non_empty_and_ready_bound)
     apply (fastforce dest: read_release_q_non_empty_and_ready_True_simp)
    apply (wpsimp simp: awakenBody_def runReaderT_def
                    wp: hoare_vcg_ball_lift2 tcbReleaseDequeue_dequeue_inv hoare_drop_imps)
    apply (fastforce dest: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
   apply (fastforce intro: no_fail_pre awakenBody_no_fail
                     dest: releaseQNonEmptyAndReady_implies_releaseQNonEmpty)
  apply (fastforce intro!: awaken_terminates)
  done

lemma setDeadline_corres:
  "dl = dl' \<Longrightarrow> corres_underlying Id False True dc \<top> \<top> (setDeadline dl) (setDeadline dl')"
  by (simp, rule corres_underlying_trivial_gen; wpsimp simp: setDeadline_def)

(* This is not particularly insightful, it just shortens setNextInterrupt_corres *)
lemma setNextInterrupt_corres_helper:
  "\<lbrakk>valid_objs' s'; (s, s') \<in> state_relation; active_sc_tcb_at t s;
    valid_objs s; active_sc_valid_refills s; pspace_aligned s; pspace_distinct s\<rbrakk>
    \<Longrightarrow> \<exists>tcb. ko_at' tcb t s' \<and> sc_at' (the (tcbSchedContext tcb)) s' \<and>
        (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)"
  apply (subgoal_tac "\<exists>tcb'. ko_at' (tcb'  :: tcb) t s'", clarsimp)
   apply (clarsimp simp: pred_map_def vs_all_heap_simps)
   apply (rename_tac tcb' scp tcb sc n)
   apply (frule_tac pspace_relation_absD, erule state_relation_pspace_relation)
   apply (clarsimp simp: other_obj_relation_def)
   apply (subgoal_tac "z = KOTCB tcb'", clarsimp)
    apply (rule_tac x=tcb' in exI, simp)
    apply (prop_tac "tcbSchedContext tcb' = Some scp", clarsimp simp: tcb_relation_def, simp)
    apply (subgoal_tac "sc_at' scp s'", clarsimp)
     apply (frule_tac x=scp in pspace_relation_absD, erule state_relation_pspace_relation)
     apply (frule (1) valid_sched_context_size_objsI, clarsimp)
     apply (subgoal_tac "z = KOSchedContext ko", clarsimp)
      apply (frule (1) sc_ko_at_valid_objs_valid_sc', clarsimp)
      apply (clarsimp simp: valid_sched_context'_def sc_relation_def active_sc_def)
     apply (case_tac z; clarsimp simp: obj_at'_def projectKOs)
    apply (erule cross_relF [OF _ sc_at'_cross_rel], clarsimp simp: obj_at_def is_sc_obj)
    apply (erule (1) valid_sched_context_size_objsI)
   apply (case_tac z; clarsimp simp: obj_at'_def projectKOs)
  apply (subgoal_tac "tcb_at t s")
   apply (frule cross_relF [OF _ tcb_at'_cross_rel], clarsimp, assumption)
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: obj_at_def vs_all_heap_simps pred_map_def is_tcb)
  done

lemma setNextInterrupt_corres:
  "corres dc ((\<lambda>s. active_sc_tcb_at (cur_thread s) s) and valid_release_q and valid_objs
              and active_sc_valid_refills and pspace_aligned and pspace_distinct)
             valid_objs'
             set_next_interrupt
             setNextInterrupt"
  unfolding setNextInterrupt_def set_next_interrupt_def
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split [OF getCurTime_corres])
      apply (rule corres_split [OF gct_corres], simp)
        apply (rule corres_split_eqr [OF _ get_tcb_obj_ref_corres])
           apply (rule corres_assert_opt_assume_l)
           apply (rule corres_split [OF get_sc_corres])
             apply (rule_tac F="sc_valid_refills' rv'" in corres_gen_asm2)
             apply (rule corres_split [OF corres_if])
                  apply (clarsimp simp: num_domains_def numDomains_def)
                 apply (rule corres_split [OF domain_time_corres])
                   apply (simp only: fun_app_def)
                   apply (rule corres_return_eq_same)
                   apply (clarsimp simp: refill_hd_relation refill_map_def)
                  apply wpsimp
                 apply wpsimp
                apply (rule corres_return_eq_same)
                apply (clarsimp simp: refill_hd_relation refill_map_def)
               apply (rule corres_split [OF getReleaseQueue_corres])
                 apply (rule corres_split [OF corres_if], simp)
                     apply (rule corres_return_eq_same, simp)
                    apply (rule corres_split_eqr)
                       apply (rule corres_assert_opt_assume_l)
                       apply simp
                       apply (rule corres_split [OF get_sc_corres])
                         apply (rule_tac F="sc_valid_refills' rv'c" in corres_gen_asm2)
                         apply (rule corres_return_eq_same)
                         apply (clarsimp simp: refill_hd_relation refill_map_def)
                        apply wpsimp
                       apply wpsimp
                      apply (simp, rule get_tcb_obj_ref_corres)
                      apply (clarsimp simp: tcb_relation_def)
                     apply (wpsimp wp: get_tcb_obj_ref_wp)
                    apply (wpsimp wp: threadGet_wp)
                   apply (rule corres_machine_op)
                   apply (simp del: dc_simp, rule setDeadline_corres, simp)
                  apply wpsimp+
          apply (clarsimp simp: tcb_relation_def)
         apply (wpsimp wp: get_tcb_obj_ref_wp)
        apply (wpsimp wp: threadGet_wp)
       apply wpsimp+
   apply (subgoal_tac "release_queue s \<noteq> [] \<longrightarrow> active_sc_tcb_at (hd (release_queue s)) s")
    apply (fastforce simp: cur_tcb_def pred_tcb_at_def vs_all_heap_simps obj_at_def is_sc_obj is_tcb
                     elim: valid_sched_context_size_objsI)
   apply (clarsimp simp: valid_release_q_def)
  apply simp
  apply (subgoal_tac "(\<exists>tcb. ko_at' tcb (ksCurThread s') s' \<and>
                    sc_at' (the (tcbSchedContext tcb)) s' \<and>
                    (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)) \<and> (ksReleaseQueue s' \<noteq> [] \<longrightarrow> (\<exists>tcb. ko_at' tcb (hd (ksReleaseQueue s')) s' \<and>
                    sc_at' (the (tcbSchedContext tcb)) s' \<and>
                    (\<forall>ko. ko_at' ko (the (tcbSchedContext tcb)) s' \<longrightarrow> sc_valid_refills' ko)))")
   apply (safe, blast, blast)[1]
   apply (rule_tac x=tcb in exI, simp, safe, blast)[1]
  apply (intro conjI; clarsimp)
   apply (prop_tac "ksCurThread s' = cur_thread s", clarsimp simp: state_relation_def, simp)
   apply (rule setNextInterrupt_corres_helper; simp)
  apply (subgoal_tac "(ksReleaseQueue s') = release_queue s", simp)
   apply (subgoal_tac "active_sc_tcb_at (hd (release_queue s)) s")
    apply (rule setNextInterrupt_corres_helper; simp)
   apply (clarsimp simp: valid_release_q_def)
  apply (clarsimp simp: state_relation_def release_queue_relation_def)
  done

lemma schedule_corres:
  "corres dc (invs and valid_sched and valid_list) invs' (Schedule_A.schedule) ThreadDecls_H.schedule"
  supply tcbSchedEnqueue_invs'[wp del]
  supply tcbSchedEnqueue_invs'_not_ResumeCurrentThread[wp del]
  supply setSchedulerAction_direct[wp]
  supply if_split[split del]
  apply (clarsimp simp: Schedule_A.schedule_def Thread_H.schedule_def)
  sorry (* schedule_corres *) (*
  apply (subst thread_get_test)
  apply (subst thread_get_comm)
  apply (subst schact_bind_inside)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ gct_corres[THEN corres_rel_imp[where r="\<lambda>x y. y = x"],simplified]])
        apply (rule corres_split[OF _ get_sa_corres])
          apply (rule corres_split_sched_act,assumption)
            apply (rule_tac P="tcb_at ct" in corres_symb_exec_l')
              apply (rule_tac corres_symb_exec_l)
                apply simp
                apply (rule corres_assert_ret)
               apply ((wpsimp wp: thread_get_wp' gets_exs_valid)+)
         prefer 2
         (* choose thread *)
         apply clarsimp
          apply (rule corres_split[OF _ thread_get_isRunnable_corres])
            apply (rule corres_split[OF _ corres_when])
             apply (rule scheduleChooseNewThread_corres, simp)
              apply (rule tcbSchedEnqueue_corres, simp)
           apply (wp thread_get_wp' tcbSchedEnqueue_invs' hoare_vcg_conj_lift hoare_drop_imps
                  | clarsimp)+
        (* switch to thread *)
        apply (rule corres_split[OF _ thread_get_isRunnable_corres],
                rename_tac was_running wasRunning)
          apply (rule corres_split[OF _ corres_when])
              apply (rule corres_split[OF _ git_corres], rename_tac it it')
                apply (rule_tac F="was_running \<longrightarrow> ct \<noteq> it" in corres_gen_asm)
                apply (rule corres_split[OF _ ethreadget_corres[where r="(=)"]],
                       rename_tac tp tp')
                   apply (rule corres_split[OF _ ethread_get_when_corres[where r="(=)"]],
                           rename_tac cp cp')
                      apply (rule corres_split[OF _ schedule_switch_thread_fastfail_corres])
                           apply (rule corres_split[OF _ curDomain_corres])
                             apply (rule corres_split[OF _ isHighestPrio_corres]; simp only:)
                               apply (rule corres_if, simp)
                                apply (rule corres_split[OF _ tcbSchedEnqueue_corres])
                                  apply (simp, fold dc_def)
                                  apply (rule corres_split[OF _ set_sa_corres])
                                     apply (rule scheduleChooseNewThread_corres, simp)

                                   apply (wp | simp)+
                                   apply (simp add: valid_sched_def)
                                   apply wp
                                   apply (rule hoare_vcg_conj_lift)
                                    apply (rule_tac t=t in set_scheduler_action_cnt_valid_blocked')
                                   apply (wpsimp wp: setSchedulerAction_invs')+
                                 apply (wp tcb_sched_action_enqueue_valid_blocked hoare_vcg_all_lift enqueue_thread_queued)
                                apply (wp tcbSchedEnqueue_invs'_not_ResumeCurrentThread)

                               apply (rule corres_if, fastforce)

                                apply (rule corres_split[OF _ tcbSchedAppend_corres])
                                  apply (simp, fold dc_def)
                                  apply (rule corres_split[OF _ set_sa_corres])
                                     apply (rule scheduleChooseNewThread_corres, simp)

                                   apply (wp | simp)+
                                   apply (simp add: valid_sched_def)
                                   apply wp
                                   apply (rule hoare_vcg_conj_lift)
                                    apply (rule_tac t=t in set_scheduler_action_cnt_valid_blocked')
                                   apply (wpsimp wp: setSchedulerAction_invs')+
                                 apply (wp tcb_sched_action_append_valid_blocked hoare_vcg_all_lift append_thread_queued)
                                apply (wp tcbSchedAppend_invs'_not_ResumeCurrentThread)

                               apply (rule corres_split[OF _ guarded_switch_to_corres], simp)
                                 apply (rule set_sa_corres[simplified dc_def])
                                 apply (wp | simp)+

                             (* isHighestPrio *)
                             apply (clarsimp simp: if_apply_def2)
                             apply ((wp (once) hoare_drop_imp)+)[1]
                            apply (simp add: if_apply_def2)
                             apply ((wp (once) hoare_drop_imp)+)[1]
                           apply wpsimp+
                     apply (wpsimp simp: etcb_relation_def)+
            apply (rule tcbSchedEnqueue_corres)
           apply wpsimp+

           apply (clarsimp simp: conj_ac cong: conj_cong)
           apply wp
           apply (rule_tac Q="\<lambda>_ s. valid_blocked_except t s \<and> scheduler_action s = switch_thread t"
                    in hoare_post_imp, fastforce)
           apply (wp add: tcb_sched_action_enqueue_valid_blocked_except
                          tcbSchedEnqueue_invs'_not_ResumeCurrentThread thread_get_wp
                     del: gets_wp)+
       apply (clarsimp simp: conj_ac if_apply_def2 cong: imp_cong conj_cong del: hoare_gets)
       apply (wp gets_wp)+

   (* abstract final subgoal *)
   apply clarsimp

   subgoal for s
     apply (clarsimp split: Deterministic_A.scheduler_action.splits
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
                               weak_valid_sched_action_def tcb_at_is_etcb_at
                               tcb_at_is_etcb_at[OF st_tcb_at_tcb_at[rotated]]
                               valid_blocked_except_def valid_blocked_def)
        apply (clarsimp simp add: pred_tcb_at_def obj_at_def is_tcb valid_idle_def)
        done
     (* choose new thread case *)
     apply (intro impI conjI allI tcb_at_invs
            | fastforce simp: invs_def cur_tcb_def valid_etcbs_def
                              valid_sched_def  st_tcb_at_def obj_at_def valid_state_def
                              weak_valid_sched_action_def not_cur_thread_def)+
     apply (simp add: valid_sched_def valid_blocked_def valid_blocked_except_def)
     done

  (* haskell final subgoal *)
  apply (clarsimp simp: if_apply_def2 invs'_def valid_state'_def
                  cong: imp_cong  split: scheduler_action.splits)
  apply (fastforce simp: cur_tcb'_def valid_pspace'_def)
  done *)

end

lemma schedContextDonate_valid_queues[wp]:
  "\<lbrace>valid_queues and valid_objs'\<rbrace> schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  (is "valid ?pre _ _")
  apply (clarsimp simp: schedContextDonate_def)
  apply (rule hoare_seq_ext[OF _ get_sc_sp'])
  apply (rule_tac B="\<lambda>_. ?pre" in hoare_seq_ext[rotated])
   apply (rule hoare_when_cases, clarsimp)
   apply (rule_tac B="\<lambda>_. ?pre" in hoare_seq_ext[rotated])
    apply (wpsimp wp: tcbSchedDequeue_valid_queues)
    apply (fastforce intro: valid_objs'_maxDomain valid_objs'_maxPriority)
   apply (rule hoare_seq_ext_skip)
    apply (wpsimp wp: tcbReleaseRemove_valid_queues)
   apply (rule hoare_seq_ext_skip)
    apply (wpsimp wp: threadSet_valid_queues_new threadSet_valid_objs')
    apply (clarsimp simp: obj_at'_def inQ_def valid_tcb'_def tcb_cte_cases_def)
   apply (wpsimp wp: rescheduleRequired_valid_queues)
   apply fastforce
  apply (wpsimp wp: threadSet_valid_queues_new hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: obj_at'_def inQ_def)
  done

lemma schedContextDonate_valid_queues'[wp]:
  "schedContextDonate sc t \<lbrace>valid_queues'\<rbrace>"
  apply (clarsimp simp: schedContextDonate_def)
  apply (rule hoare_seq_ext_skip, solves wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply (rule hoare_when_cases, simp)
   apply ((rule hoare_seq_ext_skip
           , wpsimp wp: threadSet_valid_queues' hoare_vcg_imp_lift' simp: inQ_def)
          | wpsimp wp: threadSet_valid_queues' hoare_vcg_imp_lift' simp: inQ_def)+
  done

crunches tcbSchedDequeue
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

crunches schedContextDonate
  for vrq[wp]: valid_release_queue
  and vrq'[wp]: valid_release_queue'
  (wp: threadSet_vrq_inv threadSet_vrq'_inv simp: crunch_simps)

crunches schedContextDonate
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' ptr"
  (wp: threadSet_cap_to simp: tcb_cte_cases_def)

crunches schedContextDonate
  for valid_irq_handlers'[wp]: "\<lambda>s. valid_irq_handlers' s"
  and valid_mdb'[wp]: valid_mdb'
  (ignore: threadSet
     simp: comp_def valid_mdb'_def crunch_simps
       wp: valid_irq_handlers_lift'' threadSet_ctes_of)

crunches schedContextDonate
  for sch_act_sane[wp]: sch_act_sane
  and sch_act_simple[wp]: sch_act_simple
  and sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps simp: crunch_simps rule: sch_act_sane_lift)

crunches schedContextDonate
  for no_0_obj'[wp]: no_0_obj'
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and if_unsafe_then_cap'[wp]: "if_unsafe_then_cap'"
  and valid_global_refs'[wp]: "valid_global_refs'"
  and valid_arch_state'[wp]: "valid_arch_state'"
  and valid_irq_node'[wp]: "\<lambda>s. valid_irq_node' (irq_node' s) s"
  and valid_irq_states'[wp]: "\<lambda>s. valid_irq_states' s"
  and valid_machine_state'[wp]: "\<lambda>s. valid_machine_state' s"
  and ct_not_inQ[wp]: "ct_not_inQ"
  and ct_idle_or_in_cur_domain'[wp]: "ct_idle_or_in_cur_domain'"
  and valid_pde_mappings'[wp]: "\<lambda>s. valid_pde_mappings' s"
  and pspace_domain_valid[wp]: "\<lambda>s. pspace_domain_valid s"
  and irqs_masked'[wp]: "\<lambda>s. irqs_masked' s"
  and cur_tcb'[wp]: "cur_tcb'"
  and urz[wp]: untyped_ranges_zero'
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies' [wp]: valid_replies'
  (simp: comp_def tcb_cte_cases_def crunch_simps
     wp: threadSet_not_inQ hoare_vcg_imp_lift' valid_irq_node_lift
         setQueue_cur threadSet_ifunsafe'T threadSet_cur crunch_wps
         cur_tcb_lift valid_dom_schedule'_lift valid_replies'_lift)

lemma schedContextDonate_valid_pspace':
  "\<lbrace>valid_pspace' and tcb_at' tcbPtr\<rbrace> schedContextDonate scPtr tcbPtr \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  by (wpsimp wp: schedContextDonate_valid_objs' simp: valid_pspace'_def)

lemma schedContextDonate_if_live_then_nonz_cap':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> valid_objs' s \<and>
        ex_nonz_cap_to' tcbPtr s \<and> ex_nonz_cap_to' scPtr s\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding schedContextDonate_def
  by (wpsimp wp: threadSet_iflive'T setSchedContext_iflive' hoare_vcg_all_lift threadSet_cap_to'
           simp: conj_ac cong: conj_cong | wp hoare_drop_imps | fastforce simp: tcb_cte_cases_def)+

(* `obj_at' (\<lambda>x. scTCB x \<noteq> Some idle_thread_ptr) scPtr s` is
   needed because sometimes sym_refs doesn't hold in its entirety here. *)
lemma schedContextDonate_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> bound_sc_tcb_at' ((=) None) tcbPtr s \<and>
        ex_nonz_cap_to' scPtr s \<and> ex_nonz_cap_to' tcbPtr s \<and>
        obj_at' (\<lambda>x. scTCB x \<noteq> Some idle_thread_ptr) scPtr s\<rbrace>
   schedContextDonate scPtr tcbPtr
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp only: invs'_def valid_state'_def)
  apply (rule_tac E="\<lambda>s. sc_at' scPtr s" in hoare_strengthen_pre_via_assert_backward)
   apply (simp only: schedContextDonate_def)
   apply (rule hoare_seq_ext[OF _ get_sc_sp'])
   apply (rule_tac hoare_weaken_pre[OF hoare_pre_cont])
   apply (clarsimp simp: obj_at'_def)
  apply (wp schedContextDonate_valid_pspace'
            schedContextDonate_valid_queues schedContextDonate_valid_queues'
            schedContextDonate_valid_idle' schedContextDonate_if_live_then_nonz_cap')
  apply clarsimp
  apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_sc)
  apply (auto dest!: global'_sc_no_ex_cap
              simp: ko_wp_at'_def obj_at'_def projectKO_eq projectKO_tcb
                    pred_tcb_at'_def valid_idle'_def idle_tcb'_def refs_of_rev')
  done

lemma tcbSchedDequeue_notksQ:
  "tcbSchedDequeue t \<lbrace>\<lambda>s. t' \<notin> set(ksReadyQueues s p)\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp hoare_when_weak_wp)
     apply (rule_tac Q="\<lambda>_ s. t' \<notin> set(ksReadyQueues s p)" in hoare_post_imp)
      apply wpsimp+
  done

lemma tcbSchedDequeue_nonq:
  "\<lbrace>\<lambda>s. if t=t' then valid_queues s else t' \<notin> set (ksReadyQueues s p)\<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s p)\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp wp: threadGet_wp)
  apply (case_tac p)
  apply (fastforce simp: valid_queues_def valid_queues_no_bitmap_def obj_at'_def inQ_def
                  split: if_splits)
  done

crunches tcbReleaseRemove
  for not_queued[wp]: "\<lambda>s. t' \<notin> set (ksReadyQueues s p)"
  (wp: crunch_wps simp: crunch_simps)

lemma reprogram_timer_corres:
   "corres dc \<top> \<top>
      (modify (reprogram_timer_update (\<lambda>_. True)))
      (setReprogramTimer True)"
  unfolding setReprogramTimer_def
  by (rule corres_modify) (simp add: state_relation_def swp_def)

lemma release_queue_corres:
  "corres (=) \<top> \<top> (gets release_queue) getReleaseQueue"
  by (simp add: getReleaseQueue_def state_relation_def release_queue_relation_def)

lemma tcb_release_remove_corres:
  "corres dc (pspace_aligned and pspace_distinct and tcb_at t) \<top>
             (tcb_release_remove t) (tcbReleaseRemove t)"
  unfolding tcb_release_remove_def tcbReleaseRemove_def tcb_sched_dequeue_def setReleaseQueue_def
  apply clarsimp
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac r'="(=)" in corres_split_deprecated)
       apply (rule corres_split_deprecated)
          apply (rule corres_add_noop_lhs2)
          apply (rule corres_split_deprecated)
             apply (rule threadSet_corres_noop; clarsimp simp: tcb_relation_def)
            apply (rule corres_modify)
            apply (auto simp: release_queue_relation_def state_relation_def swp_def)[1]
           apply wp
          apply wp
         apply (rule corres_rel_imp)
          apply (rule corres_when)
           apply clarsimp
          apply (rule reprogram_timer_corres)
         apply metis
        apply clarsimp
        apply wp
       apply (rule hoare_when_wp)
       apply clarsimp
       apply wp
      apply (rule release_queue_corres)
     apply wp
    apply clarsimp
    apply wpsimp
   apply simp
  apply (fastforce simp: state_relation_def tcb_at_cross)
  done

lemma threadSet_valid_queues_no_state:
  "\<lbrace>valid_queues and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: valid_queues_def valid_queues_no_bitmap_def' pred_tcb_at'_def)
   apply (wp hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_queues_def valid_queues_no_bitmap_def' pred_tcb_at'_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadSet_valid_queues'_no_state:
  "(\<And>tcb. tcbQueued tcb = tcbQueued (f tcb)) \<Longrightarrow>
   \<lbrace>valid_queues' and (\<lambda>s. \<forall>p. t \<notin> set (ksReadyQueues s p))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
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

lemma setQueue_valid_tcbs'[wp]:
  "setQueue qdom prio q \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
  done

lemma removeFromBitmap_valid_tcbs'[wp]:
  "removeFromBitmap tdom prio \<lbrace>valid_tcbs'\<rbrace>"
  apply (wpsimp simp: valid_tcbs'_def bitmap_fun_defs)
  done

lemma tcbSchedDequeue_valid_tcbs'[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: tcbSchedDequeue_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (clarsimp simp: when_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (wpsimp wp: threadSet_valid_tcbs')
  done

lemma schedContextDonate_corres_helper:
  "(case rv' of SwitchToThread x \<Rightarrow> when (x = t \<or> t = cur) rescheduleRequired
                             | _ \<Rightarrow> when (t = cur) rescheduleRequired) =
   (when (t = cur \<or> (case rv' of SwitchToThread x \<Rightarrow> t = x | _ \<Rightarrow> False)) rescheduleRequired)"
  by (case_tac rv'; clarsimp simp: when_def)

crunches tcbReleaseRemove
  for valid_tcbs'[wp]: valid_tcbs'
  (wp: crunch_wps)

lemma schedContextDonate_corres:
  "corres dc (sc_at scp and tcb_at thread and weak_valid_sched_action and pspace_aligned and
              pspace_distinct and valid_objs)
             (valid_objs' and valid_queues and valid_queues' and
              valid_release_queue and valid_release_queue')
             (sched_context_donate scp thread)
             (schedContextDonate scp thread)"
  apply (simp add: test_reschedule_def get_sc_obj_ref_def set_tcb_obj_ref_thread_set
                   schedContextDonate_def sched_context_donate_def schedContextDonate_corres_helper)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split [OF get_sc_corres])
       apply (rule corres_split [OF corres_when2])
                apply (clarsimp simp: sc_relation_def)
         apply (rule corres_assert_opt_assume_l)
         apply (rule corres_split_nor)
            apply (rule corres_split_nor)
               apply (rule corres_split_nor)
                  apply (rule corres_split_eqr)
                     apply (rule_tac r'=sched_act_relation in corres_split)
                       apply (rule get_sa_corres)
                        apply (rule corres_when)
                         apply (case_tac rv; clarsimp simp: sched_act_relation_def sc_relation_def)
                        apply (rule rescheduleRequired_corres_weak)
                      apply wpsimp
                     apply wpsimp
                    apply (rule gct_corres)
                   apply wpsimp
                  apply wpsimp
                 apply (rule_tac x="the (sc_tcb sc)" and x'="the (scTCB sca)" in lift_args_corres)
                  apply (rule threadset_corresT)
                    apply (clarsimp simp: tcb_relation_def)
                   apply (clarsimp simp: tcb_cap_cases_def)
                  apply (clarsimp simp: tcb_cte_cases_def)
                 apply (clarsimp simp: sc_relation_def)
                apply (wpsimp wp: hoare_drop_imps)
               apply (wpsimp wp: hoare_drop_imps
                                 threadSet_valid_release_queue threadSet_valid_release_queue'
                                 threadSet_valid_queues_no_state threadSet_valid_queues'_no_state)
              apply (rule_tac x="the (sc_tcb sc)" and x'="the (scTCB sca)" in lift_args_corres)
               apply (rule tcb_release_remove_corres)
              apply (clarsimp simp: sc_relation_def)
             apply (wpsimp | strengthen weak_valid_sched_action_strg)+
            apply (rule_tac Q="\<lambda>_. tcb_at' (the (scTCB sca)) and valid_tcbs' and
                                   valid_queues and valid_queues' and
                                   valid_release_queue and valid_release_queue' and
                                   (\<lambda>s. \<forall>d p. the (scTCB sca) \<notin> set (ksReadyQueues s (d, p)))"
                         in hoare_strengthen_post[rotated])
             apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
            apply (wpsimp wp: tcbReleaseRemove_valid_queues hoare_vcg_all_lift)
           apply (rule_tac x="the (sc_tcb sc)" and x'="the (scTCB sca)" in lift_args_corres)
            apply (rule tcbSchedDequeue_corres)
           apply (clarsimp simp: sc_relation_def)
          apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
         apply (wpsimp wp: tcbSchedDequeue_valid_queues hoare_vcg_all_lift tcbSchedDequeue_nonq)
           apply (rule corres_split_deprecated
                      [OF threadset_corresT
                          update_sc_no_reply_stack_update_ko_at'_corres
                            [where f'="scTCB_update (\<lambda>_. Some thread)"]])
                   apply (clarsimp simp: tcb_relation_def)
                  apply (clarsimp simp: tcb_cap_cases_def)
                 apply (clarsimp simp: tcb_cte_cases_def)
                apply (clarsimp simp: sc_relation_def)
               apply clarsimp
              apply (clarsimp simp: objBits_def objBitsKO_def)
             apply clarsimp
            apply wpsimp
           apply wpsimp
          apply (wpsimp wp: hoare_drop_imp)+
    apply (frule (1) valid_objs_ko_at)
    apply (fastforce simp: valid_obj_def valid_sched_context_def valid_bound_obj_def obj_at_def)
   apply (prop_tac "sc_at' scp s' \<and> tcb_at' thread s'")
    apply (fastforce elim: sc_at_cross tcb_at_cross simp: state_relation_def)
   apply clarsimp
   apply (frule valid_objs'_valid_tcbs')
   apply (rule valid_objsE', assumption)
    apply (fastforce simp: obj_at'_def projectKO_eq projectKO_sc)
   apply (clarsimp simp: valid_obj'_def valid_sched_context'_def obj_at'_def projectKOs)
   apply (frule valid_objs'_valid_tcbs')
   apply (fastforce simp: valid_obj'_def valid_tcb'_def)
  done

end
