(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_R
imports VSpace_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

declare static_imp_wp[wp_split del]

(* Levity: added (20090713 10:04:12) *)
declare sts_rel_idle [simp]

lemma invs_no_cicd'_queues:
  "invs_no_cicd' s \<Longrightarrow> valid_queues s"
  unfolding invs_no_cicd'_def
  by simp

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

lemma arch_switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
              and valid_vspace_objs and pspace_aligned and pspace_distinct
              and valid_vs_lookup and valid_global_objs
              and unique_table_refs o caps_of_state
              and st_tcb_at runnable t)
             (valid_arch_state' and valid_pspace' and st_tcb_at' runnable' t)
             (arch_switch_to_thread t) (Arch.switchToThread t)"
  apply (simp add: arch_switch_to_thread_def ARM_H.switchToThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_split [OF setVMRoot_corres])
      apply (rule corres_machine_op[OF corres_rel_imp])
      apply (rule corres_underlying_trivial)
       apply (simp add: ARM.clearExMonitor_def | wp)+
   apply clarsimp
   apply (erule st_tcb_at_tcb_at)
  apply (clarsimp simp: valid_pspace'_def)
  done

lemma schedule_choose_new_thread_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>rs s. scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by wp

lemma tcbSchedAppend_corres:
  notes trans_state_update'[symmetric, simp del]
  shows
  "corres dc (is_etcb_at t) (tcb_at' t and Invariants_H.valid_queues and valid_queues') (tcb_sched_action (tcb_sched_append) t) (tcbSchedAppend t)"
  apply (simp only: tcbSchedAppend_def tcb_sched_action_def)
  apply (rule corres_symb_exec_r [OF _ _ threadGet_inv, where Q'="\<lambda>rv. tcb_at' t and Invariants_H.valid_queues and valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
    defer
    apply (wp threadGet_obj_at', simp, simp)
   apply (rule no_fail_pre, wp, simp)
  apply (case_tac queued)
   apply (simp add: unless_def when_def)
   apply (rule corres_no_failI)
    apply wp+
   apply (clarsimp simp: in_monad ethread_get_def gets_the_def bind_assoc
                         assert_opt_def exec_gets is_etcb_at_def get_etcb_def get_tcb_queue_def
                         set_tcb_queue_def simpler_modify_def)

   apply (subgoal_tac "tcb_sched_append t (ready_queues a (tcb_domain y) (tcb_priority y))
                       = (ready_queues a (tcb_domain y) (tcb_priority y))")
    apply (simp add: state_relation_def ready_queues_relation_def)
   apply (clarsimp simp: tcb_sched_append_def state_relation_def
                         valid_queues'_def ready_queues_relation_def
                         ekheap_relation_def etcb_relation_def
                         obj_at'_def inQ_def projectKO_eq project_inject)
   apply (drule_tac x=t in bspec,clarsimp)
   apply clarsimp
  apply (clarsimp simp: unless_def when_def cong: if_cong)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[where r'="(=)"])
       apply (rule ethreadget_corres)
       apply (simp add: etcb_relation_def)
      apply (rule corres_split[where r'="(=)"])
         apply (rule ethreadget_corres)
         apply (simp add: etcb_relation_def)
        apply (rule corres_split[where r'="(=)"])
           apply simp
           apply (rule getQueue_corres)
          apply (rule corres_split_noop_rhs2)
             apply (simp add: tcb_sched_append_def)
             apply (intro conjI impI)
              apply (rule corres_guard_imp)
                apply (rule setQueue_corres)
               prefer 3
               apply (rule_tac P=\<top> and Q="K (t \<notin> set queuea)" in corres_assume_pre)
               apply simp
              apply simp
             apply simp
            apply (rule corres_split_noop_rhs2)
               apply (rule addToBitmap_if_null_noop_corres)
              apply (rule threadSet_corres_noop, simp_all add: tcb_relation_def exst_same_def)[1]
             apply wp+
          apply (wp getObject_tcb_wp | simp add: threadGet_def)+
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
  by (wp | clarsimp simp: bitmap_fun_defs)+

lemma removeFromBitmap_bitmapQ:
  "\<lbrace> \<lambda>s. True \<rbrace> removeFromBitmap d p \<lbrace>\<lambda>_ s. \<not> bitmapQ d p s \<rbrace>"
  unfolding bitmapQ_defs bitmap_fun_defs
  by (wpsimp simp: bitmap_fun_defs wordRadix_def)

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
   apply (wp setObject_queues_unchanged_tcb hoare_Ball_helper hoare_vcg_all_lift
             setObject_tcb_strongest)
  apply (clarsimp simp: valid_queues_no_bitmap_except_def obj_at'_def valid_queues_no_bitmap_def)
  done

(* FIXME move *)
lemmas obj_at'_conjI = obj_at_conj'

lemma setQueue_valid_queues_no_bitmap_except_dequeue_wp:
  "\<And>d p ts t.
   \<lbrace> \<lambda>s. valid_queues_no_bitmap_except t s \<and>
         (\<forall>t' \<in> set ts. obj_at' (inQ d p and runnable' \<circ> tcbState) t' s) \<and>
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
     obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain \<and> tcbPriority tcb \<le> maxPriority) t \<rbrace>
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
                       setQueue_valid_bitmapQ threadGet_const_tcb_at hoare_vcg_if_lift)+
  (* wp done *)
  apply (normalise_obj_at')
  apply (clarsimp simp: correct_queue_def)
  apply (normalise_obj_at')
  apply (fastforce simp add: valid_queues_no_bitmap_except_def valid_queues_no_bitmap_def elim: obj_at'_weaken)+
  done
qed

lemma tcbSchedDequeue_valid_queues:
  "\<lbrace>Invariants_H.valid_queues
    and obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t
    and obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t\<rbrace>
     tcbSchedDequeue t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (rule hoare_pre, rule tcbSchedDequeue_valid_queues_weak)
  apply (fastforce simp: valid_queues_def valid_queues_no_bitmap_def obj_at'_def inQ_def)
  done

lemma tcbSchedAppend_valid_queues'[wp]:
  (* most of this is identical to tcbSchedEnqueue_valid_queues' in TcbAcc_R *)
  "\<lbrace>valid_queues' and tcb_at' t\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
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
     apply (wp getObject_tcb_wp | simp add: threadGet_def)+
     apply (clarsimp simp: obj_at'_def inQ_def projectKOs valid_queues'_def)
    apply (wp getObject_tcb_wp | simp add: threadGet_def)+
  apply (clarsimp simp: obj_at'_def)
  done

crunch norq[wp]: threadSet "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def)

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
  "\<lbrace>valid_queues' and tcb_at' t\<rbrace>
    tcbSchedDequeue t \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (rule_tac B="\<lambda>rv. valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
   prefer 2
   apply (wp threadGet_const_tcb_at)
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

crunch tcb_at'[wp]: tcbSchedEnqueue "tcb_at' t"
  (simp: unless_def)
crunch tcb_at'[wp]: tcbSchedAppend "tcb_at' t"
  (simp: unless_def)
crunch tcb_at'[wp]: tcbSchedDequeue "tcb_at' t"

crunch state_refs_of'[wp]: tcbSchedEnqueue "\<lambda>s. P (state_refs_of' s)"
  (wp: refl simp: crunch_simps unless_def)
crunch state_refs_of'[wp]: tcbSchedAppend "\<lambda>s. P (state_refs_of' s)"
  (wp: refl simp: crunch_simps unless_def)
crunch state_refs_of'[wp]: tcbSchedDequeue "\<lambda>s. P (state_refs_of' s)"
  (wp: refl simp: crunch_simps)

crunch cap_to'[wp]: tcbSchedEnqueue "ex_nonz_cap_to' p"
  (simp: unless_def)
crunch cap_to'[wp]: tcbSchedAppend "ex_nonz_cap_to' p"
  (simp: unless_def)
crunch cap_to'[wp]: tcbSchedDequeue "ex_nonz_cap_to' p"

crunch iflive'[wp]: setQueue if_live_then_nonz_cap'

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

crunch idle'[wp]: tcbSchedEnqueue valid_idle'
  (simp: crunch_simps unless_def)
crunch idle'[wp]: tcbSchedAppend valid_idle'
  (simp: crunch_simps unless_def)
crunch idle'[wp]: tcbSchedDequeue valid_idle'
  (simp: crunch_simps)

crunch global_refs'[wp]: tcbSchedEnqueue valid_global_refs'
  (wp: threadSet_global_refs simp: unless_def)
crunch global_refs'[wp]: tcbSchedAppend valid_global_refs'
  (wp: threadSet_global_refs simp: unless_def)
crunch global_refs'[wp]: tcbSchedDequeue valid_global_refs'
  (wp: threadSet_global_refs)

crunch irq_node'[wp]: tcbSchedEnqueue "\<lambda>s. P (irq_node' s)"
  (simp: unless_def)
crunch irq_node'[wp]: tcbSchedAppend "\<lambda>s. P (irq_node' s)"
  (simp: unless_def)
crunch irq_node'[wp]: tcbSchedDequeue "\<lambda>s. P (irq_node' s)"

crunch typ_at'[wp]: tcbSchedEnqueue "\<lambda>s. P (typ_at' T p s)"
  (simp: unless_def)
crunch typ_at'[wp]: tcbSchedAppend "\<lambda>s. P (typ_at' T p s)"
  (simp: unless_def)
crunch typ_at'[wp]: tcbSchedDequeue "\<lambda>s. P (typ_at' T p s)"

crunch ctes_of[wp]: tcbSchedEnqueue "\<lambda>s. P (ctes_of s)"
  (simp: unless_def)
crunch ctes_of[wp]: tcbSchedAppend "\<lambda>s. P (ctes_of s)"
  (simp: unless_def)
crunch ctes_of[wp]: tcbSchedDequeue "\<lambda>s. P (ctes_of s)"

crunch ksInterrupt[wp]: tcbSchedEnqueue "\<lambda>s. P (ksInterruptState s)"
  (simp: unless_def)
crunch ksInterrupt[wp]: tcbSchedAppend "\<lambda>s. P (ksInterruptState s)"
  (simp: unless_def)
crunch ksInterrupt[wp]: tcbSchedDequeue "\<lambda>s. P (ksInterruptState s)"

crunch irq_states[wp]: tcbSchedEnqueue valid_irq_states'
  (simp: unless_def)
crunch irq_states[wp]: tcbSchedAppend valid_irq_states'
  (simp: unless_def)
crunch irq_states[wp]: tcbSchedDequeue valid_irq_states'

crunch ct'[wp]: tcbSchedEnqueue "\<lambda>s. P (ksCurThread s)"
  (simp: unless_def)
crunch ct'[wp]: tcbSchedAppend "\<lambda>s. P (ksCurThread s)"
  (simp: unless_def)
crunch ct'[wp]: tcbSchedDequeue "\<lambda>s. P (ksCurThread s)"

crunch pde_mappings'[wp]: tcbSchedEnqueue "valid_pde_mappings'"
  (simp: unless_def)
crunch pde_mappings'[wp]: tcbSchedAppend "valid_pde_mappings'"
  (simp: unless_def)
crunch pde_mappings'[wp]: tcbSchedDequeue "valid_pde_mappings'"

lemma tcbSchedEnqueue_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift tcbSchedEnqueue_ksMachine)
  done

crunch ksCurDomain[wp]: tcbSchedEnqueue "\<lambda>s. P (ksCurDomain s)"
(simp: unless_def)

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
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp tcbSchedEnqueue_ct_not_inQ valid_irq_node_lift irqs_masked_lift hoare_vcg_disj_lift
             valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
             untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def
        | auto elim!: st_tcb_ex_cap'' valid_objs'_maxDomain valid_objs'_maxPriority split: thread_state.split_asm simp: valid_pspace'_def)+
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
  apply (wp unless_wp setQueue_sch_act threadGet_wp|simp)+
  apply (fastforce simp:typ_at'_def obj_at'_def)
  done

lemma tcbSchedAppend_invs'[wp]:
  "\<lbrace>invs'
    and st_tcb_at' runnable' t
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
     tcbSchedAppend t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
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

crunch ksDomScheduleIdx[wp]: tcbSchedDequeue "\<lambda>s. P (ksDomScheduleIdx s)"
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
  "\<lbrace>invs' and tcb_at' t\<rbrace>
     tcbSchedDequeue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def
  apply (rule hoare_pre)
   apply (wp tcbSchedDequeue_ct_not_inQ sch_act_wf_lift valid_irq_node_lift irqs_masked_lift
             valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
             tcbSchedDequeue_valid_queues
             untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def)+
  apply (fastforce elim: valid_objs'_maxDomain valid_objs'_maxPriority simp: valid_pspace'_def)+
  done

lemma setCurThread_corres:
  "corres dc \<top> \<top> (modify (cur_thread_update (\<lambda>_. t))) (setCurThread t)"
  apply (unfold setCurThread_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma arch_switch_thread_tcb_at' [wp]: "\<lbrace>tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (unfold ARM_H.switchToThread_def, wp typ_at_lift_tcb')

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

lemma switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs o caps_of_state
                and st_tcb_at runnable t and valid_etcbs)
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
      apply (rule corres_split[OF arch_switchToThread_corres])
        apply (rule corres_split[OF tcbSchedDequeue_corres setCurThread_corres])
         apply (wp|clarsimp simp: tcb_at_is_etcb_at st_tcb_at_tcb_at)+
    done

  show ?thesis
    apply -
    apply (simp add: switch_to_thread_def Thread_H.switchToThread_def)
    apply (rule corres_symb_exec_l [where Q = "\<lambda> s rv. (?PA and (=) rv) s",
                                    OF corres_symb_exec_l [OF mainpart]])
    apply (auto intro: no_fail_pre [OF no_fail_assert]
                      no_fail_pre [OF no_fail_get]
                dest: st_tcb_at_tcb_at [THEN get_tcb_at] |
           simp add: assert_def | wp)+
    done
qed

lemma arch_switchToIdleThread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map and unique_table_refs \<circ> caps_of_state and
      valid_vs_lookup and valid_global_objs and pspace_aligned and pspace_distinct and valid_vspace_objs and valid_idle)
     (valid_arch_state' and pspace_aligned' and pspace_distinct' and no_0_obj' and valid_idle')
        arch_switch_to_idle_thread
        Arch.switchToIdleThread"
  apply (simp add: arch_switch_to_idle_thread_def
                ARM_H.switchToIdleThread_def)
  apply (corresKsimp corres: getIdleThread_corres setVMRoot_corres[@lift_corres_args])
  apply (clarsimp simp: valid_idle_def valid_idle'_def pred_tcb_at_def obj_at_def is_tcb obj_at'_def)
  done

lemma switchToIdleThread_corres:
  "corres dc invs invs_no_cicd' switch_to_idle_thread switchToIdleThread"
  apply (simp add: switch_to_idle_thread_def Thread_H.switchToIdleThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getIdleThread_corres])
      apply (rule corres_split[OF arch_switchToIdleThread_corres])
        apply (unfold setCurThread_def)
        apply (rule corres_trivial, rule corres_modify)
        apply (simp add: state_relation_def cdt_relation_def)
       apply (wp+, simp+)
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
                              valid_state'_def Invariants_H.valid_queues_def
                              sch_act_wf ct_in_state'_def state_refs_of'_def
                              ps_clear_def valid_irq_node'_def valid_queues'_def ct_not_inQ_ct
                              ct_idle_or_in_cur_domain'_def
                              bitmapQ_defs valid_queues_no_bitmap_def
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
  assumes vq:  "Invariants_H.valid_queues s"
      and vq': "valid_queues' s"
      and st: "st_tcb_at' (Not \<circ> runnable') t s"
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

  with vq have "st_tcb_at' runnable' t s"
    unfolding Invariants_H.valid_queues_def valid_queues_no_bitmap_def
    apply -
    apply clarsimp
    apply (drule_tac x=d in spec)
    apply (drule_tac x=p in spec)
    apply (clarsimp simp add: st_tcb_at'_def)
    apply (drule(1) bspec)
    apply (erule obj_at'_weakenE)
    apply (clarsimp)
    done

  with st show False
    apply -
    apply (drule(1) pred_tcb_at_conj')
    apply (clarsimp)
    done
qed

(*
 * The idle thread is not part of any ready queues.
 *)
lemma idle'_not_tcbQueued':
 assumes vq:   "Invariants_H.valid_queues s"
     and vq':  "valid_queues' s"
     and idle: "valid_idle' s"
 shows "obj_at' (Not \<circ> tcbQueued) (ksIdleThread s) s"
 proof -
   from idle have stidle: "st_tcb_at' (Not \<circ> runnable') (ksIdleThread s) s"
     by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs idle_tcb'_def)

   with vq vq' show ?thesis
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
    apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
    apply (frule (2) idle'_not_tcbQueued'[simplified o_def])
    apply (clarsimp simp add: ct_not_inQ_ct idle'_activatable'
                              invs'_def cur_tcb'_def valid_state'_def valid_idle'_def
                              sch_act_wf ct_in_state'_def state_refs_of'_def
                              ps_clear_def valid_irq_node'_def
                              ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                              valid_queues_def bitmapQ_defs valid_queues_no_bitmap_def valid_queues'_def
                              pred_tcb_at'_def
                        cong: option.case_cong)
    apply (clarsimp simp: obj_at'_def projectKOs idle_tcb'_def)
    done
qed

lemma clearExMonitor_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp ARM.clearExMonitor \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq)
   apply (simp add: no_irq_clearExMonitor)
  apply (clarsimp simp: ARM.clearExMonitor_def machine_op_lift_def
                        in_monad select_f_def)
  done

lemma Arch_switchToThread_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
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
  "\<lbrace>invs_no_cicd' and tcb_at' t\<rbrace>
     tcbSchedDequeue t
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def
  apply (wp tcbSchedDequeue_ct_not_inQ sch_act_wf_lift valid_irq_node_lift irqs_masked_lift
            valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
            tcbSchedDequeue_valid_queues_weak
            untyped_ranges_zero_lift
        | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  apply (fastforce simp: valid_pspace'_def valid_queues_def
                   elim: valid_objs'_maxDomain valid_objs'_maxPriority intro: obj_at'_conjI)
  done

lemma switchToThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd' and st_tcb_at' runnable' t and tcb_in_cur_domain' t \<rbrace> ThreadDecls_H.switchToThread t \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: Thread_H.switchToThread_def)
  apply (wp setCurThread_invs_no_cicd' tcbSchedDequeue_not_tcbQueued
            Arch_switchToThread_invs_no_cicd' Arch_switchToThread_pred_tcb')
  apply (auto elim!: pred_tcb'_weakenE)
  done

lemma switchToThread_invs[wp]:
  "\<lbrace>invs' and st_tcb_at' runnable' t and tcb_in_cur_domain' t \<rbrace> switchToThread t \<lbrace>\<lambda>rv. invs' \<rbrace>"
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

crunch cap_to'[wp]: setQueue "ex_nonz_cap_to' p"

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

crunch ksRQ[wp]: threadSet "\<lambda>s. P (ksReadyQueues s)"
  (wp: updateObject_default_inv)

declare Cons_eq_tails[simp]

crunch ksCurDomain[wp]: "ThreadDecls_H.switchToThread" "\<lambda>s. P (ksCurDomain s)"

(* FIXME move *)
lemma obj_tcb_at':
  "obj_at' (\<lambda>tcb::tcb. P tcb) t s \<Longrightarrow> tcb_at' t s"
  by (clarsimp simp: obj_at'_def)

lemma tcb_at_typ_at':
  "tcb_at' p s = typ_at' TCBT p s"
  unfolding typ_at'_def
  apply rule
  apply (clarsimp simp add: obj_at'_def ko_wp_at'_def projectKOs)
  apply (clarsimp simp add: obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko, simp_all)
  done


lemma invs'_not_runnable_not_queued:
  fixes s
  assumes inv: "invs' s"
      and st: "st_tcb_at' (Not \<circ> runnable') t s"
  shows "obj_at' (Not \<circ> tcbQueued) t s"
  apply (insert assms)
  apply (rule valid_queues_not_runnable_not_queued)
    apply (clarsimp simp add: invs'_def valid_state'_def)+
  done

lemma valid_queues_not_tcbQueued_not_ksQ:
  fixes s
  assumes   vq: "Invariants_H.valid_queues s"
      and notq: "obj_at' (Not \<circ> tcbQueued) t s"
  shows "\<forall>d p. t \<notin> set (ksReadyQueues s (d, p))"
proof (rule ccontr, simp , erule exE, erule exE)
  fix d p
  assume "t \<in> set (ksReadyQueues s (d, p))"
  with vq have "obj_at' (inQ d p) t s"
    unfolding Invariants_H.valid_queues_def valid_queues_no_bitmap_def
    apply clarify
    apply (drule_tac x=d in spec)
    apply (drule_tac x=p in spec)
    apply (clarsimp)
    apply (drule(1) bspec)
    apply (erule obj_at'_weakenE)
    apply (simp)
    done
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
  apply (clarsimp)
  done

lemma ct_not_ksQ:
  "\<lbrakk> invs' s; ksSchedulerAction s = ResumeCurrentThread \<rbrakk>
   \<Longrightarrow> \<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p)"
  apply (clarsimp simp: invs'_def valid_state'_def ct_not_inQ_def)
  apply (frule(1) valid_queues_not_tcbQueued_not_ksQ)
  apply (fastforce)
  done

crunch nosch[wp]: getCurThread "\<lambda>s. P (ksSchedulerAction s)"

lemma setThreadState_rct:
  "\<lbrace>\<lambda>s. (runnable' st \<or> ksCurThread s \<noteq> t)
        \<and> ksSchedulerAction s = ResumeCurrentThread\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (rule hoare_pre_disj')
   apply (rule hoare_seq_ext [OF _
                 hoare_vcg_conj_lift
                   [OF threadSet_tcbState_st_tcb_at' [where P=runnable']
                       threadSet_nosch]])
   apply (rule hoare_seq_ext [OF _
                 hoare_vcg_conj_lift [OF isRunnable_const isRunnable_inv]])
   apply (clarsimp simp: when_def)
   apply (case_tac x)
    apply (clarsimp, wp)[1]
   apply (clarsimp)
  apply (rule hoare_seq_ext [OF _
                hoare_vcg_conj_lift
                  [OF threadSet_ct threadSet_nosch]])
  apply (rule hoare_seq_ext [OF _ isRunnable_inv])
  apply (rule hoare_seq_ext [OF _
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
         bitmapQ_no_L1_orphans s\<rbrakk>
        \<Longrightarrow> obj_at' (inQ (ksCurDomain s) (lookupBitmapPriority (ksCurDomain s) s) and runnable' \<circ> tcbState)
             (hd (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s))) s"
  apply (drule (2) bitmapQ_from_bitmap_lookup)
  apply (simp add: valid_bitmapQ_bitmapQ_simp)
  apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)", simp)
  apply (clarsimp, rename_tac t ts)
  apply (drule cons_set_intro)
  apply (drule (2) valid_queues_no_bitmap_objD)
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
    "\<And>s p t.\<lbrakk> valid_queues s ; bitmapQ (ksCurDomain s) p s ; t = hd (ksReadyQueues s (ksCurDomain s,p)) \<rbrakk>
            \<Longrightarrow> st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s"
    unfolding valid_queues_def
    apply (clarsimp dest!: bitmapQ_ksReadyQueuesI)
    apply (case_tac "ksReadyQueues s (ksCurDomain s, p)", simp)
    apply (rename_tac t ts)
    apply (drule_tac t=t and p=p and d="ksCurDomain s" in valid_queues_no_bitmap_objD)
     apply simp
    apply (fastforce elim: obj_at'_weaken simp: inQ_def tcb_in_cur_domain'_def st_tcb_at'_def)
    done
  thus ?thesis
    by (wp switchToThread_invs_no_cicd') (fastforce dest: invs_no_cicd'_queues)
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



crunch it[wp]: switchToIdleThread "\<lambda>s. P (ksIdleThread s)"
crunch it[wp]: switchToThread "\<lambda>s. P (ksIdleThread s)"
    (ignore: clearExMonitor)

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

lemma corres_assert_assume_l:
  "corres dc P Q (f ()) g
  \<Longrightarrow> corres dc (P and (\<lambda>s. P')) Q (assert P' >>= f) g"
  by (force simp: corres_underlying_def assert_def return_def bind_def fail_def)

lemma corres_assert_assume_r:
  "corres dc P Q f (g ())
  \<Longrightarrow> corres dc P (Q and (\<lambda>s. Q')) f (assert Q' >>= g)"
  by (force simp: corres_underlying_def assert_def return_def bind_def fail_def)

crunch cur[wp]: tcbSchedEnqueue cur_tcb'
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
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_vs_lookup and valid_global_objs
                and unique_table_refs o caps_of_state
                and st_tcb_at runnable t and valid_etcbs)
             (valid_arch_state' and valid_pspace' and Invariants_H.valid_queues
                and st_tcb_at' runnable' t and cur_tcb')
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

lemma curDomain_corres: "corres (=) \<top> \<top> (gets cur_domain) (curDomain)"
  by (simp add: curDomain_def state_relation_def)

lemma curDomain_corres':
  "corres (=) \<top> (\<lambda>s. ksCurDomain s \<le> maxDomain)
    (gets cur_domain) (if 1 < numDomains then curDomain else return 0)"
  apply (case_tac "1 < numDomains"; simp)
   apply (rule corres_guard_imp[OF curDomain_corres]; solves simp)
  (* if we have only one domain, then we are in it *)
  apply (clarsimp simp: return_def simpler_gets_def bind_def maxDomain_def
                        state_relation_def corres_underlying_def)
  done

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

lemma guarded_switch_to_chooseThread_fragment_corres:
  "corres dc
    (P and st_tcb_at runnable t and invs and valid_sched)
    (P' and st_tcb_at' runnable' t and invs_no_cicd')
          (guarded_switch_to t)
          (do runnable \<leftarrow> isRunnable t;
              y \<leftarrow> assert runnable;
              ThreadDecls_H.switchToThread t
           od)"
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
  "\<lbrakk> ksReadyQueuesL1Bitmap s (ksCurDomain s) \<noteq> 0 ; valid_queues s \<rbrakk>
   \<Longrightarrow> st_tcb_at' runnable' (hd (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s))) s"
   apply (drule bitmapQ_from_bitmap_lookup; clarsimp simp: valid_queues_def)
   apply (clarsimp simp add: valid_bitmapQ_bitmapQ_simp)
   apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)")
    apply simp
   apply (simp add: valid_queues_no_bitmap_def)
   apply (erule_tac x="ksCurDomain s" in allE)
   apply (erule_tac x="lookupBitmapPriority (ksCurDomain s) s" in allE)
   apply (clarsimp simp: st_tcb_at'_def)
   apply (erule obj_at'_weaken)
   apply simp
   done

lemma curDomain_or_return_0:
  "\<lbrakk> \<lbrace>P\<rbrace> curDomain \<lbrace>\<lambda>rv s. Q rv s \<rbrace>; \<And>s. P s \<Longrightarrow> ksCurDomain s \<le> maxDomain \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> if 1 < numDomains then curDomain else return 0 \<lbrace>\<lambda>rv s. Q rv s \<rbrace>"
  apply (case_tac "1 < numDomains"; simp)
  apply (simp add: valid_def curDomain_def simpler_gets_def return_def maxDomain_def)
  done

lemma invs_no_cicd_ksCurDomain_maxDomain':
  "invs_no_cicd' s \<Longrightarrow> ksCurDomain s \<le> maxDomain"
  unfolding invs_no_cicd'_def by simp

lemma chooseThread_corres:
  "corres dc (invs and valid_sched) (invs_no_cicd')
     choose_thread chooseThread" (is "corres _ ?PREI ?PREH _ _")
proof -
  show ?thesis
  unfolding choose_thread_def chooseThread_def
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
              apply (rule_tac
                       P="\<lambda>s. ?PREI s \<and> queues = ready_queues s (cur_domain s) \<and>
                              st_tcb_at runnable (hd (max_non_empty_queue queues)) s" and
                       P'="\<lambda>s. (?PREH s \<and> st_tcb_at' runnable' (hd queue) s) \<and>
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
      apply (clarsimp simp: if_apply_def2)
      apply (wp hoare_vcg_conj_lift hoare_vcg_imp_lift ksReadyQueuesL1Bitmap_return_wp)
     apply (wpsimp wp: curDomain_or_return_0 simp: curDomain_def)+
    apply (fastforce simp: invs_no_cicd'_def)
   apply (clarsimp simp: valid_sched_def DetSchedInvs_AI.valid_queues_def max_non_empty_queue_def)
   apply (erule_tac x="cur_domain s" in allE)
   apply (erule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in allE)
   apply (case_tac "ready_queues s (cur_domain s) (Max {prio. ready_queues s (cur_domain s) prio \<noteq> []})")
    apply (clarsimp)
    apply (subgoal_tac
             "ready_queues s (cur_domain s) (Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}) \<noteq> []")
     apply (fastforce elim!: setcomp_Max_has_prop)+
  apply (simp add: invs_no_cicd_ksCurDomain_maxDomain')
  apply (clarsimp dest!: invs_no_cicd'_queues)
  apply (fastforce intro: ksReadyQueuesL1Bitmap_st_tcb_at')
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

interpretation tcb_sched_action_extended: is_extended' "tcb_sched_action f a"
  by (unfold_locales)

lemma getDomainTime_corres:
  "corres (=) \<top> \<top> (gets domain_time) getDomainTime"
  by (simp add: getDomainTime_def state_relation_def)

lemma nextDomain_corres:
  "corres dc \<top> \<top> next_domain nextDomain"
  apply (simp add: next_domain_def nextDomain_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def Let_def dschLength_def dschDomain_def)
  done

lemma next_domain_valid_sched[wp]:
  "\<lbrace> valid_sched and (\<lambda>s. scheduler_action s  = choose_new_thread)\<rbrace> next_domain \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: next_domain_def Let_def)
  apply (wp, simp add: valid_sched_def valid_sched_action_2_def ct_not_in_q_2_def)
  apply (simp add:valid_blocked_2_def)
  done

lemma nextDomain_invs_no_cicd':
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread)\<rbrace> nextDomain \<lbrace> \<lambda>_. invs_no_cicd' \<rbrace>"
  apply (simp add: nextDomain_def Let_def dschLength_def dschDomain_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def
                        ct_not_inQ_def cur_tcb'_def ct_idle_or_in_cur_domain'_def dschDomain_def
                        all_invs_but_ct_idle_or_in_cur_domain'_def)
  done

lemma scheduleChooseNewThread_fragment_corres:
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
    apply (rule corres_split)
       apply (rule corres_when, simp)
       apply (rule nextDomain_corres)
      apply simp
      apply (rule chooseThread_corres)
     apply (wp nextDomain_invs_no_cicd')+
   apply (clarsimp simp: valid_sched_def invs'_def valid_state'_def all_invs_but_ct_idle_or_in_cur_domain'_def)+
  done

lemma scheduleSwitchThreadFastfail_corres:
  "\<lbrakk> ct \<noteq> it \<longrightarrow> (tp = tp' \<and> cp = cp') ; ct = ct' ; it = it' \<rbrakk> \<Longrightarrow>
   corres ((=)) (is_etcb_at ct) (tcb_at' ct)
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
    apply (rule corres_split[OF corres_gets_queues_getReadyQueuesL1Bitmap])
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

crunch valid_idle_etcb[wp]: set_scheduler_action valid_idle_etcb

crunch inv[wp]: isHighestPrio P
crunch inv[wp]: curDomain P
crunch inv[wp]: schedule_switch_thread_fastfail P
crunch inv[wp]: scheduleSwitchThreadFastfail P

lemma setSchedulerAction_invs': (* not in wp set, clobbered by ssa_wp *)
  "\<lbrace>\<lambda>s. invs' s \<rbrace> setSchedulerAction ChooseNewThread \<lbrace>\<lambda>_. invs' \<rbrace>"
  by (wpsimp simp: invs'_def cur_tcb'_def valid_state'_def valid_irq_node'_def ct_not_inQ_def
                   valid_queues_def valid_queues_no_bitmap_def valid_queues'_def
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

crunch static_inv[wp]: guarded_switch_to "\<lambda>_. P"

lemma ethread_get_when_corres:
  assumes x: "\<And>etcb tcb'. etcb_relation etcb tcb' \<Longrightarrow> r (f etcb) (f' tcb')"
  shows      "corres (\<lambda>rv rv'. b \<longrightarrow> r rv rv') (is_etcb_at t) (tcb_at' t)
                (ethread_get_when b f t) (threadGet f' t)"
  apply (clarsimp simp: ethread_get_when_def)
  apply (rule conjI; clarsimp)
  apply (rule corres_guard_imp, rule ethreadget_corres; simp add: x)
  apply (clarsimp simp: threadGet_def)
  apply (rule corres_noop)
  apply wpsimp+
  done

lemma schedule_corres:
  "corres dc (invs and valid_sched and valid_list) invs' (Schedule_A.schedule) ThreadDecls_H.schedule"
  supply ethread_get_wp[wp del]
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
              apply (rule tcbSchedEnqueue_corres)
             apply (rule scheduleChooseNewThread_corres, simp)
            apply (wp thread_get_wp' tcbSchedEnqueue_invs' hoare_vcg_conj_lift hoare_drop_imps
                   | clarsimp)+
        (* switch to thread *)
        apply (rule corres_split[OF thread_get_isRunnable_corres],
                rename_tac was_running wasRunning)
          apply (rule corres_split)
             apply (rule corres_when, simp)
             apply (rule tcbSchedEnqueue_corres)
            apply (rule corres_split[OF getIdleThread_corres], rename_tac it it')
              apply (rule_tac F="was_running \<longrightarrow> ct \<noteq> it" in corres_gen_asm)
              apply (rule corres_split)
                 apply (rule ethreadget_corres[where r="(=)"])
                 apply (clarsimp simp: etcb_relation_def)
                apply (rename_tac tp tp')
                apply (rule corres_split)
                   apply (rule ethread_get_when_corres[where r="(=)"])
                   apply (clarsimp simp: etcb_relation_def)
                  apply (rename_tac cp cp')
                  apply (rule corres_split)
                     apply (rule scheduleSwitchThreadFastfail_corres; simp)
                    apply (rule corres_split[OF curDomain_corres])
                      apply (rule corres_split[OF isHighestPrio_corres]; simp only:)
                        apply (rule corres_if, simp)
                         apply (rule corres_split[OF tcbSchedEnqueue_corres])
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
                         apply (rule corres_split[OF tcbSchedAppend_corres])
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
                              Invariants_H.valid_queues_def
                              state_refs_of'_def ps_clear_def
                              valid_irq_node'_def valid_queues'_def
                              tcb_in_cur_domain'_def ct_idle_or_in_cur_domain'_def
                              bitmapQ_defs valid_queues_no_bitmap_def
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
    apply (simp add: ARM_H.switchToThread_def setCurThread_def)
    apply (wp tcbSchedDequeue_not_tcbQueued | simp )+
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
  apply (rule idle'_not_tcbQueued')
  apply (simp add: invs_no_cicd'_def)+
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
   \<lbrace>\<lambda>y s. tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def setCurThread_def)
  apply (wpsimp wp: tcbSchedDequeue_not_tcbQueued)
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
    unfolding chooseThread_def Let_def curDomain_def
    apply (simp only: return_bind, simp)
    apply (rule hoare_seq_ext[where B="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s"])
     apply (rule_tac B="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                               rv = ksReadyQueuesL1Bitmap s curdom" in hoare_seq_ext)
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
      apply clarsimp
      apply (clarsimp dest!: invs_no_cicd'_queues
                      simp: valid_queues_def lookupBitmapPriority_def[symmetric])
      apply (drule (3) lookupBitmapPriority_obj_at')
      apply normalise_obj_at'
      apply (fastforce simp: tcb_in_cur_domain'_def inQ_def elim: obj_at'_weaken)
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
    unfolding chooseThread_def Let_def curDomain_def
    apply (simp only: return_bind, simp)
    apply (rule hoare_seq_ext[where B="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s"])
     apply (rule_tac B="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                               rv = ksReadyQueuesL1Bitmap s curdom" in hoare_seq_ext)
      apply (rename_tac l1)
      apply (case_tac "l1 = 0")
       (* switch to idle thread *)
       apply (simp, wp (once) switchToIdleThread_invs_no_cicd', simp)
      (* we have a thread to switch to *)
      apply (clarsimp simp: bitmap_fun_defs)
      apply (wp assert_inv)
      apply (clarsimp dest!: invs_no_cicd'_queues simp: valid_queues_def)
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
  apply (rule_tac hoare_seq_ext, rename_tac t)
   apply (wp, wpc)
      \<comment> \<open>action = ResumeCurrentThread\<close>
      apply (wp)[1]
     \<comment> \<open>action = ChooseNewThread\<close>
     apply (wp scheduleChooseNewThread_invs')
    \<comment> \<open>action = SwitchToThread candidate\<close>
    apply (wpsimp wp: scheduleChooseNewThread_invs' ssa_invs'
                      chooseThread_invs_no_cicd' setSchedulerAction_invs' setSchedulerAction_direct
                      switchToThread_tcb_in_cur_domain' switchToThread_ct_not_queued_2
           | wp hoare_disjI2[where Q="\<lambda>_ s. tcb_in_cur_domain' (ksCurThread s) s"]
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
  unfolding chooseThread_def Let_def curDomain_def
  supply if_split[split del]
  apply (simp only: return_bind, simp)
  apply (wp findM_inv | simp)+
  apply (case_tac queue)
  apply (wp stt_nosch | simp add: curDomain_def bitmap_fun_defs)+
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
  apply (rule_tac hoare_seq_ext, rename_tac t)
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

crunch sch_act_sane: setThreadState, setBoundNotification "sch_act_sane"
  (simp: crunch_simps wp: crunch_wps)

lemma possibleSwitchTo_corres:
  "corres dc (valid_etcbs and weak_valid_sched_action and cur_tcb and st_tcb_at runnable t)
    (Invariants_H.valid_queues and valid_queues' and
    (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and cur_tcb' and tcb_at' t and st_tcb_at' runnable' t and valid_objs')
      (possible_switch_to t)
      (possibleSwitchTo t)"
  supply ethread_get_wp[wp del]
  apply (simp add: possible_switch_to_def possibleSwitchTo_def cong: if_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF curDomain_corres], simp)
      apply (rule corres_split)
         apply (rule ethreadget_corres[where r="(=)"])
         apply (clarsimp simp: etcb_relation_def)
        apply (rule corres_split[OF getSchedulerAction_corres])
          apply (rule corres_if, simp)
           apply (rule tcbSchedEnqueue_corres)
          apply (rule corres_if, simp)
            apply (case_tac action; simp)
           apply (rule corres_split[OF rescheduleRequired_corres])
             apply (rule tcbSchedEnqueue_corres)
            apply (wp rescheduleRequired_valid_queues'_weak)+
          apply (rule setSchedulerAction_corres, simp)
         apply (wpsimp simp: if_apply_def2
                       wp: hoare_drop_imp[where f="ethread_get a b" for a b])+
      apply (wp hoare_drop_imps)[1]
     apply wp+
   apply (fastforce simp: valid_sched_def invs_def valid_state_def cur_tcb_def
                          valid_sched_action_def weak_valid_sched_action_def
                          tcb_at_is_etcb_at[OF st_tcb_at_tcb_at[rotated]])
  apply (simp add: tcb_at_is_etcb_at)
  done

end
end
