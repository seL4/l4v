(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TcbAcc_R
imports CSpace_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

declare if_weak_cong [cong]
declare result_in_set_wp[wp]
declare hoare_in_monad_post[wp]
declare trans_state_update'[symmetric,simp]
declare empty_fail_sequence_x[simp]
declare storeWordUser_typ_at' [wp]

lemma threadRead_SomeD:
  "threadRead f t s = Some y \<Longrightarrow> \<exists>tcb. ko_at' tcb t s \<and> y = f tcb"
  by (fastforce simp: threadRead_def oliftM_def dest!: readObject_misc_ko_at')

(* Auxiliaries and basic properties of priority bitmap functions *)

lemma countLeadingZeros_word_clz[simp]:
  "countLeadingZeros w = word_clz w"
  unfolding countLeadingZeros_def word_clz_def
  by (simp add: to_bl_upt)

lemma wordLog2_word_log2[simp]:
  "wordLog2 = word_log2"
  apply (rule ext)
  unfolding wordLog2_def word_log2_def
  by (simp add: word_size wordBits_def)

lemmas bitmap_fun_defs = addToBitmap_def removeFromBitmap_def
                          modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
                          getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def

(* lookupBitmapPriority is a cleaner version of getHighestPrio *)
definition
  "lookupBitmapPriority d \<equiv> \<lambda>s.
     l1IndexToPrio (word_log2 (ksReadyQueuesL1Bitmap s d)) ||
       of_nat (word_log2 (ksReadyQueuesL2Bitmap s (d,
            invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d)))))"

lemma getHighestPrio_def'[simp]:
  "getHighestPrio d = gets (lookupBitmapPriority d)"
  unfolding getHighestPrio_def gets_def
  by (fastforce simp: gets_def get_bind_apply lookupBitmapPriority_def bitmap_fun_defs)

(* isHighestPrio_def' is a cleaner version of isHighestPrio_def *)
lemma isHighestPrio_def':
  "isHighestPrio d p = gets (\<lambda>s. ksReadyQueuesL1Bitmap s d = 0 \<or> lookupBitmapPriority d s \<le> p)"
  unfolding isHighestPrio_def bitmap_fun_defs getHighestPrio_def'
  apply (rule ext)
  apply (clarsimp simp: gets_def bind_assoc return_def NonDetMonad.bind_def get_def
                  split: if_splits)
  done

lemma getHighestPrio_inv[wp]:
  "\<lbrace> P \<rbrace> getHighestPrio d \<lbrace>\<lambda>_. P \<rbrace>"
  unfolding bitmap_fun_defs by simp

lemma valid_bitmapQ_bitmapQ_simp:
  "\<lbrakk> valid_bitmapQ s \<rbrakk> \<Longrightarrow>
   bitmapQ d p s = (ksReadyQueues s (d, p) \<noteq> [])"
   unfolding valid_bitmapQ_def
   by simp

lemma prioToL1Index_l1IndexToPrio_or_id:
  "\<lbrakk> unat (w'::priority) < 2 ^ wordRadix ; w < 2^(size w' - wordRadix) \<rbrakk>
   \<Longrightarrow> prioToL1Index ((l1IndexToPrio w) || w') = w"
  unfolding l1IndexToPrio_def prioToL1Index_def
  apply (simp add: shiftr_over_or_dist shiftr_le_0 wordRadix_def')
  apply (subst shiftl_shiftr_id, simp, simp add: word_size)
   apply (rule word_of_nat_less)
   apply simp
  apply (subst unat_of_nat_eq, simp_all add: word_size)
  done

lemma bitmapQ_no_L1_orphansD:
  "\<lbrakk> bitmapQ_no_L1_orphans s ; ksReadyQueuesL1Bitmap s d !! i \<rbrakk>
  \<Longrightarrow> ksReadyQueuesL2Bitmap s (d, invertL1Index i) \<noteq> 0 \<and> i < l2BitmapSize"
 unfolding bitmapQ_no_L1_orphans_def by simp

lemma l1IndexToPrio_wordRadix_mask[simp]:
  "l1IndexToPrio i && mask wordRadix = 0"
  unfolding l1IndexToPrio_def
  by (simp add: wordRadix_def')

definition
  (* when in the middle of updates, a particular queue might not be entirely valid *)
  valid_queues_no_bitmap_except :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "valid_queues_no_bitmap_except t' \<equiv> \<lambda>s.
   (\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). t \<noteq> t' \<longrightarrow> obj_at' (inQ d p) t s)
    \<and> (d > maxDomain \<or> p > maxPriority \<longrightarrow> ksReadyQueues s (d,p) = []))"

lemma valid_queues_no_bitmap_exceptI[intro]:
  "valid_queues_no_bitmap s \<Longrightarrow> valid_queues_no_bitmap_except t s"
  unfolding valid_queues_no_bitmap_except_def valid_queues_no_bitmap_def
  by simp

crunches setThreadState, threadSet
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and reply_at'[wp]: "\<lambda>s. P (reply_at' p s)"
  and tcb_at'[wp]: "\<lambda>s. P (tcb_at' p s)"
  and obj_at'_reply[wp]: "\<lambda>s. P (obj_at' (Q :: reply \<Rightarrow> bool) p s)"
  and obj_at'_ep[wp]: "\<lambda>s. P (obj_at' (Q :: endpoint \<Rightarrow> bool) p s)"
  and obj_at'_ntfn[wp]: "\<lambda>s. P (obj_at' (Q :: notification \<Rightarrow> bool) p s)"
  and obj_at'_sc[wp]: "\<lambda>s. Q (obj_at' (P :: sched_context \<Rightarrow> bool) p s)"
  (wp: crunch_wps set_tcb'.set_preserves_some_obj_at')

crunches tcbSchedDequeue, tcbSchedEnqueue
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"

crunches tcbSchedDequeue, tcbSchedEnqueue, tcbReleaseRemove
  for obj_at'_reply[wp]: "\<lambda>s. P (obj_at' (Q :: reply \<Rightarrow> bool) p s)"
  and obj_at'_ep[wp]: "\<lambda>s. P (obj_at' (Q :: endpoint \<Rightarrow> bool) p s)"
  and obj_at'_sc[wp]: "\<lambda>s. Q (obj_at' (P :: sched_context \<Rightarrow> bool) p s)"

lemma valid_objs_valid_tcbE':
  assumes "valid_objs' s"
          "tcb_at' t s"
          "\<And>tcb. ko_at' tcb t s \<Longrightarrow> valid_tcb' tcb s \<Longrightarrow> R s tcb"
  shows "obj_at' (R s) t s"
  using assms
  apply (clarsimp simp add: valid_objs'_def ran_def typ_at'_def
                            ko_wp_at'_def valid_obj'_def valid_tcb'_def obj_at'_def)
  apply (fastforce simp: projectKO_def projectKO_opt_tcb return_def valid_tcb'_def)
  done

lemma valid_tcb'_tcbDomain_update:
  "new_dom \<le> maxDomain \<Longrightarrow>
   \<forall>tcb. valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbDomain_update (\<lambda>_. new_dom) tcb) s"
  unfolding valid_tcb'_def
  apply (clarsimp simp: tcb_cte_cases_def objBits_simps')
  done

lemma valid_tcb'_tcbState_update:
  "\<lbrakk>valid_tcb_state' st s; valid_tcb' tcb s\<rbrakk> \<Longrightarrow>
   valid_tcb' (tcbState_update (\<lambda>_. st) tcb) s"
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def valid_tcb_state'_def objBits_simps')
  done

definition valid_tcbs' :: "kernel_state \<Rightarrow> bool" where
  "valid_tcbs' s' \<equiv> \<forall>ptr tcb. ksPSpace s' ptr = Some (KOTCB tcb) \<longrightarrow> valid_tcb' tcb s'"

lemma valid_objs'_valid_tcbs'[elim!]:
  "valid_objs' s \<Longrightarrow> valid_tcbs' s"
  by (auto simp: valid_objs'_def valid_tcbs'_def valid_obj'_def split: kernel_object.splits)

lemma invs'_valid_tcbs'[elim!]:
  "invs' s \<Longrightarrow> valid_tcbs' s"
  by (fastforce intro: valid_objs'_valid_tcbs')

lemma valid_tcbs'_maxDomain:
  "\<And>s t. \<lbrakk> valid_tcbs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t s"
  apply (clarsimp simp: valid_tcbs'_def obj_at'_def valid_tcb'_def)
  done

lemmas valid_objs'_maxDomain = valid_tcbs'_maxDomain[OF valid_objs'_valid_tcbs']

lemma valid_tcbs'_maxPriority:
  "\<And>s t. \<lbrakk> valid_tcbs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t s"
  apply (clarsimp simp: valid_tcbs'_def obj_at'_def valid_tcb'_def)
  done

lemmas valid_objs'_maxPriority = valid_tcbs'_maxPriority[OF valid_objs'_valid_tcbs']

lemma valid_tcbs'_obj_at':
  assumes "valid_tcbs' s"
          "tcb_at' t s"
          "\<And>tcb. ko_at' tcb t s \<Longrightarrow> valid_tcb' tcb s \<Longrightarrow> R s tcb"
  shows "obj_at' (R s) t s"
  using assms
  apply (clarsimp simp add: valid_tcbs'_def ran_def typ_at'_def
                            ko_wp_at'_def valid_obj'_def valid_tcb'_def obj_at'_def)
  done

lemma update_valid_tcb'[simp]:
  "\<And>f. valid_tcb' tcb (ksReleaseQueue_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReprogramTimer_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueuesL1Bitmap_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueuesL2Bitmap_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueues_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksSchedulerAction_update f s) = valid_tcb' tcb s"
  by (auto simp: valid_tcb'_def valid_tcb_state'_def valid_bound_obj'_def
          split: option.splits thread_state.splits)

lemma update_tcbInReleaseQueue_False_valid_tcb'[simp]:
  "valid_tcb' (tcbInReleaseQueue_update a tcb) s = valid_tcb' tcb s"
  by (auto simp: valid_tcb'_def tcb_cte_cases_def objBits_simps')

lemma update_valid_tcbs'[simp]:
  "\<And>f. valid_tcbs' (ksReleaseQueue_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReprogramTimer_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueuesL1Bitmap_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueuesL2Bitmap_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueues_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksSchedulerAction_update f s) = valid_tcbs' s"
  by (simp_all add: valid_tcbs'_def)

lemma doMachineOp_irq_states':
  assumes masks: "\<And>P. \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"
  shows "\<lbrace>valid_irq_states'\<rbrace> doMachineOp f \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (drule use_valid)
    apply (rule_tac P="\<lambda>m. m = irq_masks (ksMachineState s)" in masks)
   apply simp
  apply simp
  done

lemma dmo_invs':
  assumes masks: "\<And>P. \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"
  shows "\<lbrace>(\<lambda>s. \<forall>m. \<forall>(r,m')\<in>fst (f m). \<forall>p.
             pointerInUserData p s \<or> pointerInDeviceData p s \<or>
             underlying_memory m' p = underlying_memory m p) and
          invs'\<rbrace> doMachineOp f \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (subst invs'_machine)
    apply (drule use_valid)
      apply (rule_tac P="\<lambda>m. m = irq_masks (ksMachineState s)" in masks, simp+)
   apply (fastforce simp add: valid_machine_state'_def)
  apply assumption
  done

lemma dmo_lift':
  assumes f: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> doMachineOp f
         \<lbrace>\<lambda>rv s. Q rv (ksMachineState s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (erule (1) use_valid [OF _ f])
  done

lemma doMachineOp_getActiveIRQ_IRQ_active:
  "\<lbrace>valid_irq_states'\<rbrace>
     doMachineOp (getActiveIRQ in_kernel)
   \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive\<rbrace>"
  apply (rule hoare_lift_Pf3 [where f="ksInterruptState"])
   prefer 2
   apply wp
    apply (simp add: irq_state_independent_H_def)
   apply assumption
  apply (rule dmo_lift')
  apply (rule getActiveIRQ_masked)
  done

lemma doMachineOp_getActiveIRQ_IRQ_active':
  "\<lbrace>valid_irq_states'\<rbrace>
     doMachineOp (getActiveIRQ in_kernel)
   \<lbrace>\<lambda>rv s. rv = Some irq \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule doMachineOp_getActiveIRQ_IRQ_active)
  apply simp
  done

lemmas doMachineOp_obj_at = doMachineOp_obj_at'

lemma updateObject_tcb_inv:
  "\<lbrace>P\<rbrace> updateObject (obj::tcb) ko p q n \<lbrace>\<lambda>rv. P\<rbrace>"
  by simp (rule updateObject_default_inv)

lemma setObject_update_TCB_corres':
  assumes tcbs: "tcb_relation tcb tcb' \<Longrightarrow> tcb_relation tcbu tcbu'"
  assumes tables: "\<forall>(getF, v) \<in> ran tcb_cap_cases. getF tcbu = getF tcb"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF tcbu' = getF tcb'"
  assumes r: "r () ()"
  shows "corres r (ko_at (TCB tcb) add)
                  (ko_at' tcb' add)
                  (set_object add (TCB tcbu)) (setObject add tcbu')"
  apply (rule_tac F="tcb_relation tcb tcb'" in corres_req)
   apply (clarsimp simp: state_relation_def obj_at_def obj_at'_def)
   apply (frule(1) pspace_relation_absD)
   apply (clarsimp simp: other_obj_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_rel_imp)
     apply (rule setObject_other_corres[where P="(=) tcb'"])
           apply (rule ext)+
           apply simp
          defer
          apply (simp add: is_other_obj_relation_type_def
                           objBits_simps' other_obj_relation_def tcbs r)+
    apply (fastforce elim!: obj_at_weakenE dest: bspec[OF tables])
   apply (subst(asm) eq_commute, assumption)
  apply (clarsimp simp: obj_at'_def objBits_simps)
  apply (subst map_to_ctes_upd_tcb, assumption+)
   apply (simp add: ps_clear_def3 field_simps objBits_defs mask_def)
  apply (subst if_not_P)
   apply (fastforce dest: bspec [OF tables', OF ranI])
  apply simp
  done

lemma setObject_update_TCB_corres:
  "\<lbrakk> tcb_relation tcb tcb' \<Longrightarrow> tcb_relation tcbu tcbu';
     \<forall>(getF, v) \<in> ran tcb_cap_cases. getF tcbu = getF tcb;
     \<forall>(getF, v) \<in> ran tcb_cte_cases. getF tcbu' = getF tcb';
     r () ()\<rbrakk>
   \<Longrightarrow> corres r (\<lambda>s. get_tcb add s = Some tcb)
               (\<lambda>s'. (tcb', s') \<in> fst (getObject add s'))
               (set_object add (TCB tcbu)) (setObject add tcbu')"
  apply (rule corres_guard_imp)
    apply (erule (3) setObject_update_TCB_corres', force)
  apply (clarsimp simp: getObject_def in_monad split_def obj_at'_def
                        loadObject_default_def objBits_simps' in_magnitude_check
                 dest!: readObject_misc_ko_at')
  done

lemma getObject_TCB_corres:
  "corres tcb_relation (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (gets_the (get_tcb t)) (getObject t)"
  apply (rule corres_cross_over_guard[where Q="tcb_at' t"])
   apply (fastforce simp: tcb_at_cross state_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_gets_the)
    apply (rule corres_get_tcb)
   apply (simp add: tcb_at_def)
  apply assumption
  done

lemma threadGet_corres:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> r (f tcb) (f' tcb')"
  shows      "corres r (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                       (thread_get f t) (threadGet f' t)"
  apply (simp add: thread_get_def threadGet_getObject)
  apply (rule corres_split_skip)
     apply wpsimp+
   apply (rule getObject_TCB_corres)
  apply (simp add: x)
  done

lemmas get_tcb_obj_ref_corres
  = threadGet_corres[where 'a="obj_ref option", folded get_tcb_obj_ref_def]

lemma threadGet_inv [wp]: "\<lbrace>P\<rbrace> threadGet f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: threadGet_def getObject_tcb_inv | wp)+

lemma ball_tcb_cte_casesI:
  "\<lbrakk> P (tcbCTable, tcbCTable_update);
     P (tcbVTable, tcbVTable_update);
     P (tcbIPCBufferFrame, tcbIPCBufferFrame_update);
     P (tcbFaultHandler, tcbFaultHandler_update);
     P (tcbTimeoutHandler, tcbTimeoutHandler_update) \<rbrakk>
    \<Longrightarrow> \<forall>x \<in> ran tcb_cte_cases. P x"
  by (simp add: tcb_cte_cases_def cteSizeBits_def)

lemma all_tcbI:
  "\<lbrakk> \<And>a b c d e f g h i j k l m n p q r. P (Thread a b c d e f g h i j k l m n p q r) \<rbrakk> \<Longrightarrow> \<forall>tcb. P tcb"
  by (rule allI, case_tac tcb, simp)

lemma threadset_corresT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation (f tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  shows      "corres dc (tcb_at t and pspace_aligned and pspace_distinct)
                        \<top>
                        (thread_set f t) (threadSet f' t)"
  apply (simp add: thread_set_def threadSet_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getObject_TCB_corres])
      apply (rule setObject_update_TCB_corres')
         apply (erule x)
        apply (rule y)
       apply (clarsimp simp: bspec_split [OF spec [OF z]])
       apply fastforce
      apply simp
     apply wp+
   apply (clarsimp simp add: tcb_at_def obj_at_def)
   apply (drule get_tcb_SomeD)
   apply fastforce
  apply simp
  done

lemmas threadset_corres =
    threadset_corresT [OF _ _ all_tcbI, OF _ ball_tcb_cap_casesI ball_tcb_cte_casesI]

lemma threadSet_corres_noopT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation tcb (fn tcb')"
  assumes y: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (fn tcb) = getF tcb"
  shows      "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                        (return v) (threadSet fn t)"
proof -
  have S: "\<And>t s. tcb_at t s \<Longrightarrow> return v s = (thread_set id t >>= (\<lambda>x. return v)) s"
    apply (clarsimp simp: tcb_at_def)
    apply (clarsimp simp: return_def thread_set_def gets_the_def
                          assert_opt_def simpler_gets_def set_object_def get_object_def
                          put_def get_def bind_def assert_def a_type_def[split_simps kernel_object.split arch_kernel_obj.split]
                   dest!: get_tcb_SomeD)
    apply (subgoal_tac "kheap s(t \<mapsto> TCB tcb) = kheap s", simp)
     apply (simp add: map_upd_triv get_tcb_SomeD)+
    done
  show ?thesis
    apply (rule stronger_corres_guard_imp)
      apply (subst corres_cong [OF refl refl S refl refl])
       defer
       apply (subst bind_return [symmetric],
              rule corres_underlying_split [OF threadset_corresT])
            apply (simp add: x)
           apply simp
          apply (rule y)
         apply (rule corres_noop [where P=\<top> and P'=\<top>])
          apply simp
         apply (rule no_fail_pre, wpsimp+)[1]
        apply wpsimp+
    done
qed

lemmas threadSet_corres_noop =
    threadSet_corres_noopT [OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

lemma threadSet_corres_noop_splitT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation tcb (fn tcb')"
  assumes y: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (fn tcb) = getF tcb"
  assumes z: "corres r P Q' m m'"
  assumes w: "\<lbrace>P'\<rbrace> threadSet fn t \<lbrace>\<lambda>x. Q'\<rbrace>"
  assumes e: "\<And>tcb'. exst_same tcb' (fn tcb')"
  shows      "corres r (tcb_at t and pspace_aligned and pspace_distinct and P) P'
                           m (threadSet fn t >>= (\<lambda>rv. m'))"
  apply (rule corres_guard_imp)
    apply (subst return_bind[symmetric])
    apply (rule corres_split_nor[OF threadSet_corres_noopT])
        apply (simp add: x)
       apply (rule y)
      apply (rule z)
     apply (wp w)+
   apply simp
  apply simp
  done

lemmas threadSet_corres_noop_split =
    threadSet_corres_noop_splitT [OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

(* The function "thread_set f p" updates a TCB at p using function f.
   It should not be used to change capabilities, though. *)
lemma setObject_tcb_valid_objs:
  "\<lbrace>valid_objs' and (tcb_at' t and valid_obj' (injectKO v))\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (rule setObject_valid_objs')
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma setObject_queues_unchanged:
  assumes inv: "\<And>P p q n obj. \<lbrace>P\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>r. P\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject t v \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp inv | simp)+
  done

lemma setObject_tcb_ctes_of[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s) \<and>
     obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t s\<rbrace>
     setObject t v
   \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (rule setObject_ctes_of)
   apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                         obj_at'_def objBits_simps' in_magnitude_check)
   apply fastforce
  apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                        obj_at'_def objBits_simps in_magnitude_check bind_def)
  done

lemma setObject_tcb_mdb' [wp]:
  "\<lbrace> valid_mdb' and
     obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t\<rbrace>
  setObject t (v :: tcb)
  \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def pred_conj_def
  by (rule setObject_tcb_ctes_of)

lemma setObject_tcb_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' (tcbState v)
                                  \<union> tcb_bound_refs' (tcbBoundNotification v) (tcbSchedContext v)
                                                    (tcbYieldTo v)))\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp setObject_state_refs_of',
      simp_all add: objBits_simps' fun_upd_def)

lemma setObject_tcb_iflive':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and>
      (live' (injectKO v) \<longrightarrow> ex_nonz_cap_to' t s)
       \<and> obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t s\<rbrace>
     setObject t (v :: tcb)
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule setObject_iflive')
      apply (simp add: objBits_simps')+
   apply (clarsimp simp: updateObject_default_def in_monad obj_at'_def
                         in_magnitude_check objBits_simps' prod_eq_iff)
   apply fastforce
  apply (clarsimp simp: updateObject_default_def bind_def in_monad)
  done

lemma setObject_tcb_idle':
  "\<lbrace>\<lambda>s. valid_idle' s \<and> (t = ksIdleThread s \<longrightarrow> idle_tcb' v)\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_pre)
  apply (rule setObject_idle')
      apply (simp add: objBits_simps')+
   apply (simp add: updateObject_default_inv)
  apply (simp add: idle_tcb_ps_def idle_sc_ps_def)
  done

lemma setObject_sc_idle':
  "\<lbrace>\<lambda>s. valid_idle' s  \<and> (t = idle_sc_ptr \<longrightarrow> idle_sc' v)\<rbrace>
   setSchedContext t v
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (clarsimp simp: setSchedContext_def)
  apply (rule hoare_pre)
  apply (rule setObject_idle')
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps' scBits_pos_power2)
   apply (simp add: updateObject_default_inv)
  apply (simp add: idle_tcb_ps_def idle_sc_ps_def)
  done

lemma setObject_tcb_ifunsafe':
  "\<lbrace>if_unsafe_then_cap' and obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  unfolding pred_conj_def
  apply (rule setObject_ifunsafe')
    apply (clarsimp simp: updateObject_default_def in_monad obj_at'_def
                          in_magnitude_check objBits_simps' prod_eq_iff)
    apply fastforce
   apply (clarsimp simp: updateObject_default_def bind_def in_monad)
  apply wp
  done

lemma setObject_tcb_refs' [wp]:
  "\<lbrace>\<lambda>s. P (global_refs' s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (global_refs' s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def updateObject_default_def)
  apply wp
  apply (simp add: global_refs'_def)
  done

lemma setObject_tcb_valid_globals' [wp]:
  "\<lbrace>valid_global_refs' and
    obj_at' (\<lambda>tcb. (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb = getF v)) t\<rbrace>
  setObject t (v :: tcb)
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  unfolding pred_conj_def valid_global_refs'_def
  apply (rule hoare_lift_Pf2 [where f="global_refs'"])
   apply (rule hoare_lift_Pf2 [where f="gsMaxObjectSize"])
    apply (rule setObject_ctes_of)
     apply (clarsimp simp: updateObject_default_def in_monad obj_at'_def
                           in_magnitude_check objBits_simps' prod_eq_iff)
     apply fastforce
    apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                          obj_at'_def objBits_simps in_magnitude_check bind_def)
   apply (wp | wp setObject_ksPSpace_only updateObject_default_inv | simp)+
  done

lemma threadSet_pspace_no_overlap' [wp]:
  "\<lbrace>pspace_no_overlap' w s\<rbrace> threadSet f t \<lbrace>\<lambda>rv. pspace_no_overlap' w s\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_pspace_no_overlap' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadSet_global_refsT:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (F tcb) = getF tcb"
  shows "\<lbrace>valid_global_refs'\<rbrace> threadSet F t \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: threadSet_def)
   apply (wp setObject_tcb_valid_globals' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def bspec_split [OF spec [OF x]])
  done

lemmas threadSet_global_refs[wp] =
    threadSet_global_refsT [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma setObject_tcb_valid_replies':
  "\<lbrace>\<lambda>s. valid_replies' s \<and>
        (\<forall>rptr. st_tcb_at' ((=) (BlockedOnReply (Some rptr))) t s
                  \<longrightarrow> tcbState v = BlockedOnReply (Some rptr)
                      \<or> \<not> is_reply_linked rptr s)\<rbrace>
   setObject t (v :: tcb)
   \<lbrace>\<lambda>rv. valid_replies'\<rbrace>"
  unfolding valid_replies'_def pred_tcb_at'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_ex_lift
                    set_tcb'.setObject_obj_at'_strongest)
  apply (rename_tac rptr)
  apply (rule ccontr, clarsimp simp flip: imp_disjL)
  apply (drule_tac x=rptr in spec, drule mp, assumption)
  apply (auto simp: opt_map_def)
  done

lemma threadSet_valid_pspace'T_P:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  assumes z: "\<forall>tcb. (P \<longrightarrow> Q (tcbState tcb)) \<longrightarrow>
                     (\<forall>s. valid_tcb_state' (tcbState tcb) s
                              \<longrightarrow> valid_tcb_state' (tcbState (F tcb)) s)"
  assumes z': "\<forall>tcb. (P \<longrightarrow> Q (tcbState tcb)) \<longrightarrow>
                      (\<forall>rptr. (tcbState tcb = BlockedOnReply rptr)
                                 \<longrightarrow> (tcbState (F tcb) = BlockedOnReply rptr))"
  assumes v1: "\<forall>tcb. (P \<longrightarrow> Q' (tcbBoundNotification tcb)) \<longrightarrow>
                      (\<forall>s. valid_bound_ntfn' (tcbBoundNotification tcb) s
                              \<longrightarrow> valid_bound_ntfn' (tcbBoundNotification (F tcb)) s)"
  assumes v2: "\<forall>tcb. (P \<longrightarrow> Q'' (tcbSchedContext tcb)) \<longrightarrow>
                      (\<forall>s. valid_bound_sc' (tcbSchedContext tcb) s
                              \<longrightarrow> valid_bound_sc' (tcbSchedContext (F tcb)) s)"
  assumes v3: "\<forall>tcb. (P \<longrightarrow> Q''' (tcbYieldTo tcb)) \<longrightarrow>
                      (\<forall>s. valid_bound_sc' (tcbYieldTo tcb) s
                              \<longrightarrow> valid_bound_sc' (tcbYieldTo (F tcb)) s)"

  assumes y: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
                      \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes u: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes w: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  assumes w': "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  shows
  "\<lbrace>valid_pspace' and (\<lambda>s. P \<longrightarrow> st_tcb_at' Q t s \<and> bound_tcb_at' Q' t s \<and>
                                 bound_sc_tcb_at' Q'' t s \<and> bound_yt_tcb_at' Q''' t s)\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def threadSet_def)
  apply (rule hoare_pre,
         wpsimp wp: setObject_tcb_valid_objs setObject_tcb_valid_replies'
                    getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def pred_tcb_at'_def)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def
                            bspec_split [OF spec [OF x]] z
                            split_paired_Ball y u w v1 v2 v3 w')
  apply (drule sym, fastforce simp: z')
  done

lemmas threadSet_valid_pspace'T =
    threadSet_valid_pspace'T_P[where P=False, simplified]

lemmas threadSet_valid_pspace' =
    threadSet_valid_pspace'T [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_ifunsafe'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows      "\<lbrace>if_unsafe_then_cap'\<rbrace> threadSet F t \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_ifunsafe' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def bspec_split [OF spec [OF x]])
  done

lemmas threadSet_ifunsafe' =
    threadSet_ifunsafe'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_state_refs_of'_helper[simp]:
  "{r. (r \<in> tcb_st_refs_of' ts \<or> r \<in> tcb_bound_refs' ntfnptr sc_ptr yt_ptr)
       \<and> (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)}
   = tcb_bound_refs' ntfnptr sc_ptr yt_ptr"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_state_refs_of'_helper'[simp]:
  "{r. (r \<in> tcb_st_refs_of' ts \<or> r \<in> tcb_bound_refs' ntfnptr sc_ptr yt_ptr)
       \<and> (snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo)}
   = tcb_st_refs_of' ts"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_state_refs_of'_helper_TCBBound[simp]:
  "{r. (r \<in> tcb_st_refs_of' (tcbState obj)
        \<or> r \<in> tcb_bound_refs' (tcbBoundNotification obj)(tcbSchedContext obj) (tcbYieldTo obj))
          \<and> snd r = TCBBound}
  = get_refs TCBBound (tcbBoundNotification obj)"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_state_refs_of'_helper_TCBSchedContext[simp]:
  "{r. (r \<in> tcb_st_refs_of' (tcbState obj)
        \<or> r \<in> tcb_bound_refs' (tcbBoundNotification obj)(tcbSchedContext obj) (tcbYieldTo obj))
          \<and> snd r = TCBSchedContext}
  = get_refs TCBSchedContext (tcbSchedContext obj)"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_state_refs_of'_helper_TCBYieldTo[simp]:
  "{r. (r \<in> tcb_st_refs_of' (tcbState obj)
        \<or> r \<in> tcb_bound_refs' (tcbBoundNotification obj)(tcbSchedContext obj) (tcbYieldTo obj))
          \<and> snd r = TCBYieldTo}
  = get_refs TCBYieldTo (tcbYieldTo obj)"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_state_refs_of'T_P:
  assumes x: "\<forall>tcb. (P' \<longrightarrow> Q (tcbState tcb)) \<longrightarrow>
                     tcb_st_refs_of' (tcbState (F tcb))
                       = f' (tcb_st_refs_of' (tcbState tcb))"
  assumes y: "\<forall>tcb. (P' \<longrightarrow> Q' (tcbBoundNotification tcb)) \<longrightarrow>
                     (get_refs TCBBound (tcbBoundNotification (F tcb))
                      = (g' (get_refs TCBBound (tcbBoundNotification tcb))))"
  assumes z: "\<forall>tcb. (P' \<longrightarrow> Q'' (tcbSchedContext tcb)) \<longrightarrow>
                     (get_refs TCBSchedContext (tcbSchedContext (F tcb))
                      = (h' (get_refs TCBSchedContext (tcbSchedContext tcb))))"
  assumes w: "\<forall>tcb. (P' \<longrightarrow> Q''' (tcbYieldTo tcb)) \<longrightarrow>
                     (get_refs TCBYieldTo (tcbYieldTo (F tcb))
                      = (i' (get_refs TCBYieldTo (tcbYieldTo tcb))))"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := f' {r \<in> state_refs_of' s t. snd r \<notin> {TCBBound, TCBSchedContext, TCBYieldTo}}
                                    \<union> g' {r \<in> state_refs_of' s t. snd r = TCBBound}
                                    \<union> h' {r \<in> state_refs_of' s t. snd r = TCBSchedContext}
                                    \<union> i' {r \<in> state_refs_of' s t. snd r = TCBYieldTo}))
        \<and> (P' \<longrightarrow> st_tcb_at' Q t s \<and> bound_tcb_at' Q' t s \<and> bound_sc_tcb_at' Q'' t s
                  \<and> bound_yt_tcb_at' Q''' t s)\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def pred_tcb_at'_def tcb_bound_refs'_def
                 elim!: rsubst[where P=P] intro!: ext)
  apply (cut_tac s=s and p=t and 'a=tcb in ko_at_state_refs_ofD')
   apply (simp add: obj_at'_def)
  apply (fastforce simp: x y z w)
  done

lemmas threadSet_state_refs_of'T =
    threadSet_state_refs_of'T_P [where P'=False, simplified]

lemmas threadSet_state_refs_of' =
    threadSet_state_refs_of'T [OF all_tcbI all_tcbI all_tcbI all_tcbI]

lemma state_refs_of'_helper[simp]:
  "{r \<in> state_refs_of' s t. snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
   \<union> {r \<in> state_refs_of' s t. snd r = TCBBound}
   \<union> {r \<in> state_refs_of' s t. snd r = TCBSchedContext}
   \<union> {r \<in> state_refs_of' s t. snd r = TCBYieldTo}
   = state_refs_of' s t"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_iflive'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> ((\<exists>tcb. \<not> bound (tcbBoundNotification tcb) \<and> bound (tcbBoundNotification (F tcb))
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. \<not> bound (tcbYieldTo tcb) \<and> bound (tcbYieldTo (F tcb))
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. (\<not> bound (tcbSchedContext tcb) \<or> tcbSchedContext tcb = Some idle_sc_ptr)
              \<and> bound (tcbSchedContext (F tcb)) \<and> tcbSchedContext (F tcb) \<noteq> Some idle_sc_ptr
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. (tcbState tcb = Inactive \<or> tcbState tcb = IdleThreadState)
              \<and> tcbState (F tcb) \<noteq> Inactive
              \<and> tcbState (F tcb) \<noteq> IdleThreadState
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_iflive' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  apply (subst conj_assoc[symmetric], subst imp_disjL[symmetric])
  apply (subst conj_assoc[symmetric], subst imp_disjL[symmetric])
  apply (rule conjI)
   apply (rule impI, clarsimp)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def)
  apply (intro conjI)
    apply (metis if_live_then_nonz_capE' ko_wp_at'_def live'.simps(1))
   apply (metis if_live_then_nonz_capE' ko_wp_at'_def live'.simps(1))
  apply (clarsimp simp: bspec_split [OF spec [OF x]])
  done

lemmas threadSet_iflive' =
    threadSet_iflive'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_cte_wp_at'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (F tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. P' (cte_wp_at' P p s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P' (cte_wp_at' P p s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (rule hoare_seq_ext [where B="\<lambda>rv s. P' (cte_wp_at' P p s) \<and> obj_at' ((=) rv) t s"])
   apply (rename_tac tcb)
   apply (rule setObject_cte_wp_at2')
    apply (clarsimp simp: updateObject_default_def in_monad objBits_simps'
                          obj_at'_def in_magnitude_check prod_eq_iff)
    apply (case_tac tcb, clarsimp simp: bspec_split [OF spec [OF x]])
   apply (clarsimp simp: updateObject_default_def in_monad bind_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas threadSet_cte_wp_at' =
  threadSet_cte_wp_at'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemmas threadSet_cap_to' = ex_nonz_cap_to_pres' [OF threadSet_cte_wp_at']

lemma threadSet_cap_to:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cte_cases. getF (f tcb) = getF tcb)
  \<Longrightarrow> \<lbrace>ex_nonz_cap_to' p\<rbrace> threadSet f tptr \<lbrace>\<lambda>_. ex_nonz_cap_to' p\<rbrace>"
  by (wpsimp wp: hoare_ex_wp threadSet_cte_wp_at'
           simp: ex_nonz_cap_to'_def tcb_cte_cases_def objBits_simps')

lemma threadSet_ctes_ofT:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (F tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  apply (case_tac obj)
  apply (simp add: bspec_split [OF spec [OF x]])
  done

lemmas threadSet_ctes_of =
    threadSet_ctes_ofT [OF all_tcbI, OF ball_tcb_cte_casesI]

lemmas threadSet_cteCaps_of = ctes_of_cteCaps_of_lift [OF threadSet_ctes_of]

lemmas threadSet_urz = untyped_ranges_zero_lift[where f="cteCaps_of", OF _ threadSet_cteCaps_of]

lemma threadSet_idle'T:
  "\<lbrace>\<lambda>s. valid_idle' s
        \<and> (t = ksIdleThread s \<longrightarrow> (\<forall>tcb. ko_at' tcb t s \<and> idle_tcb' tcb \<longrightarrow> idle_tcb' (F tcb)))\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_idle' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def valid_idle'_def pred_tcb_at'_def)
  done

lemmas threadSet_idle' =
    (*threadSet_idle'T [OF all_tcbI, OF ball_tcb_cte_casesI]*)
    threadSet_idle'T

lemma threadSet_valid_queues_no_bitmap:
  "\<lbrace>valid_queues_no_bitmap and
    (\<lambda>s. \<forall>d p. (\<exists>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb)))
                \<longrightarrow> obj_at' (\<lambda>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb))) t s
                \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_queues_no_bitmap \<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: Invariants_H.valid_queues_no_bitmap_def' pred_tcb_at'_def)
   apply (wp hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_queues_no_bitmap_def' pred_tcb_at'_def)
  apply (fastforce simp: obj_at'_def)
  done

lemma threadSet_valid_queues_no_bitmap_new:
  "\<lbrace>valid_queues_no_bitmap
    and (\<lambda>s. \<forall>d p. obj_at' (\<lambda>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb))) t s
                    \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. valid_queues_no_bitmap \<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: Invariants_H.valid_queues_no_bitmap_def' pred_tcb_at'_def)

   apply (wp hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_queues_no_bitmap_def' pred_tcb_at'_def)
  apply (fastforce simp: obj_at'_def)
  done

lemma valid_release_queue_def':
  "valid_release_queue =
     (\<lambda>s. (\<forall>t\<in>set (ksReleaseQueue s). obj_at' (tcbInReleaseQueue) t s))"
  apply (rule ext, rule iffI)
  apply (clarsimp simp: valid_release_queue_def obj_at'_and pred_tcb_at'_def o_def
                  elim!: obj_at'_weakenE)+
  done

lemma threadSet_valid_release_queue:
  "\<lbrace>\<lambda>s. valid_release_queue s
        \<and> (obj_at' (\<lambda>tcb. (tcbInReleaseQueue tcb ) \<and> \<not>(tcbInReleaseQueue (f tcb))) t s
           \<longrightarrow> t \<notin> set (ksReleaseQueue s))\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: valid_release_queue_def' pred_tcb_at'_def)

   apply (wp hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_release_queue_def' pred_tcb_at'_def)
  apply (clarsimp simp: obj_at'_def)
  by fastforce

lemma threadSet_valid_bitmapQ[wp]:
  "\<lbrace> valid_bitmapQ \<rbrace> threadSet f t \<lbrace> \<lambda>rv. valid_bitmapQ \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def objBits_simps)+

lemma threadSet_valid_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> threadSet f t \<lbrace> \<lambda>rv. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def objBits_simps)+

lemma threadSet_valid_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> threadSet f t \<lbrace> \<lambda>rv. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def objBits_simps)+

lemma threadSet_valid_queues:
  "\<lbrace>Invariants_H.valid_queues and
    (\<lambda>s. \<forall>d p. (\<exists>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb)))
                \<longrightarrow> obj_at' (\<lambda>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb))) t s
                \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  unfolding valid_queues_def
  by (wp threadSet_valid_queues_no_bitmap;simp)

lemma threadSet_valid_queues_new:
  "\<lbrace>Invariants_H.valid_queues and
    (\<lambda>s. \<forall>d p. obj_at' (\<lambda>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb))) t s
                \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  unfolding valid_queues_def
  by (wp threadSet_valid_queues_no_bitmap;simp)

definition
  addToQs :: "(Structures_H.tcb \<Rightarrow> Structures_H.tcb)
                       \<Rightarrow> machine_word \<Rightarrow> (domain \<times> priority \<Rightarrow> machine_word list)
                       \<Rightarrow> (domain \<times> priority \<Rightarrow> machine_word list)"
where
 "addToQs F t \<equiv> \<lambda>qs (qdom, prio). if (\<forall>ko. \<not> inQ qdom prio (F ko))
                             then t # qs (qdom, prio)
                             else qs (qdom, prio)"

lemma addToQs_set_def:
  "(t' \<in> set (addToQs F t qs (qdom, prio))) = (t' \<in> set (qs (qdom, prio))
      \<or> (t' = t \<and> (\<forall>ko. \<not> inQ qdom prio (F ko))))"
  by (auto simp add: addToQs_def)

lemma threadSet_valid_queues_addToQs:
  "\<lbrace>\<lambda>s. (\<forall>ko qdom prio. ko_at' ko t s \<and> inQ qdom prio (F ko) \<and> \<not> inQ qdom prio ko
            \<longrightarrow> t \<in> set (ksReadyQueues s (qdom, prio)))
             \<and> valid_queues' (ksReadyQueues_update (addToQs F t) s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: valid_queues'_def threadSet_def obj_at'_real_def
                split del: if_split)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
     apply (wp setObject_ko_wp_at | simp add: objBits_simps')+
    apply (wp getObject_tcb_wp updateObject_default_inv
               | simp split del: if_split)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def objBits_simps addToQs_set_def
             split del: if_split cong: if_cong)
  apply (fastforce split: if_split_asm)
  done

lemma threadSet_valid_queues_Qf:
  "\<lbrace>\<lambda>s. (\<forall>ko qdom prio. ko_at' ko t s \<and> inQ qdom prio (F ko) \<and> \<not> inQ qdom prio ko
            \<longrightarrow> t \<in> set (ksReadyQueues s (qdom, prio)))
             \<and> valid_queues' (ksReadyQueues_update Qf s)
             \<and> (\<forall>prio. set (Qf (ksReadyQueues s) prio)
                        \<subseteq> set (addToQs F t (ksReadyQueues s) prio))\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (wp threadSet_valid_queues_addToQs)
  apply (clarsimp simp: valid_queues'_def subset_iff)
  done

lemma addToQs_subset:
  "set (qs p) \<subseteq> set (addToQs F t qs p)"
by (clarsimp simp: addToQs_def split_def)

lemmas threadSet_valid_queues'
  = threadSet_valid_queues_Qf
       [where Qf=id, simplified ksReadyQueues_update_id
                                id_apply addToQs_subset simp_thms]

lemma threadSet_valid_release_queue':
  "\<lbrace>\<lambda>s. (\<forall>ko. ko_at' ko t s \<and> tcbInReleaseQueue (F ko) \<longrightarrow> t \<in> set (ksReleaseQueue s))
        \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> obj_at' (tcbInReleaseQueue) t' s \<longrightarrow> t' \<in> set (ksReleaseQueue s))\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  apply (clarsimp simp: valid_release_queue'_def threadSet_def obj_at'_real_def)
  apply (wpsimp wp: hoare_vcg_all_lift setObject_tcb_wp getObject_tcb_wp)
  apply (rename_tac t')
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  apply (case_tac "t'=t"; clarsimp?)
  apply (clarsimp simp: ps_clear_def objBits_simps')
  done

lemma threadSet_cur:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. cur_tcb' s\<rbrace>"
  apply (wpsimp simp: threadSet_def cur_tcb'_def
                  wp: hoare_lift_Pf[OF setObject.typ_at_lifts'(1) setObject_ct_inv])
  done

lemma modifyReadyQueuesL1Bitmap_obj_at[wp]:
  "\<lbrace>obj_at' P t\<rbrace> modifyReadyQueuesL1Bitmap a b \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: modifyReadyQueuesL1Bitmap_def getReadyQueuesL1Bitmap_def)
  apply wp
  apply (fastforce intro: obj_at'_pspaceI)
  done

crunches setThreadState, setBoundNotification
  for valid_arch' [wp]: valid_arch_state'
  (simp: unless_def crunch_simps wp: crunch_wps)

lemma threadSet_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> threadSet t F \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: threadSet_def, wp setObject_typ_at')

lemmas threadSet_typ_at_lifts[wp] = typ_at_lifts [OF threadSet_typ_at']

crunch irq_states' [wp]: threadSet valid_irq_states'

crunch pspace_domain_valid [wp]: threadSet "pspace_domain_valid"

lemma threadSet_obj_at'_really_strongest:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> obj_at' (\<lambda>obj. if t = t' then P (f obj) else P obj)
    t' s\<rbrace> threadSet f t \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (rule hoare_wp_splits)
   apply (rule setObject_tcb_strongest)
  apply (simp only: imp_conv_disj)
  apply (subst simp_thms(32)[symmetric], rule hoare_vcg_disj_lift)
   apply (rule hoare_post_imp [where Q="\<lambda>rv s. \<not> tcb_at' t s \<and> tcb_at' t s"])
    apply simp
   apply (subst simp_thms(21)[symmetric], rule hoare_vcg_conj_lift)
    apply (rule getObject_tcb_inv)
   apply (rule hoare_strengthen_post [OF getObject_ko_at])
     apply simp
   apply (erule obj_at'_weakenE)
   apply simp
  apply (cases "t = t'", simp_all)
   apply (rule OMG_getObject_tcb)
  apply wp
  done

(* FIXME: move *)
lemma tcb_at_typ_at':
  "tcb_at' p s = typ_at' TCBT p s"
  unfolding typ_at'_def
  apply (rule iffI)
   apply (clarsimp simp add: obj_at'_def ko_wp_at'_def)
  apply (clarsimp simp add: obj_at'_def ko_wp_at'_def)
  apply (case_tac ko; simp)
  done

(* FIXME: move *)
lemma not_obj_at':
  "(\<not>obj_at' (\<lambda>tcb::tcb. P tcb) t s) = (\<not>typ_at' TCBT t s \<or> obj_at' (Not \<circ> P) t s)"
  apply (simp add: obj_at'_real_def typ_at'_def ko_wp_at'_def objBits_simps)
  apply (rule iffI)
   apply (clarsimp)
   apply (case_tac ko)
   apply (clarsimp)+
  done

(* FIXME: move *)
lemma not_obj_at_elim':
  assumes typat: "typ_at' TCBT t s"
      and nobj: "\<not>obj_at' (\<lambda>tcb::tcb. P tcb) t s"
    shows "obj_at' (Not \<circ> P) t s"
  using assms
  apply -
  apply (drule not_obj_at' [THEN iffD1])
  apply (clarsimp)
  done

(* FIXME: move *)
lemmas tcb_at_not_obj_at_elim' = not_obj_at_elim' [OF tcb_at_typ_at' [THEN iffD1]]

(* FIXME: move *)
lemma lift_neg_pred_tcb_at':
  assumes typat: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
      and sttcb: "\<And>S p. \<lbrace>pred_tcb_at' proj S p\<rbrace> f \<lbrace>\<lambda>_. pred_tcb_at' proj S p\<rbrace>"
    shows "\<lbrace>\<lambda>s. P (pred_tcb_at' proj S p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (pred_tcb_at' proj S p s)\<rbrace>"
  apply (rule_tac P=P in P_bool_lift)
   apply (rule sttcb)
  apply (simp add: pred_tcb_at'_def not_obj_at')
  apply (wp hoare_convert_imp)
    apply (rule typat)
   prefer 2
   apply assumption
  apply (rule hoare_chain [OF sttcb])
   apply (fastforce simp: pred_tcb_at'_def comp_def)
  apply (clarsimp simp: pred_tcb_at'_def elim!: obj_at'_weakenE)
  done

lemma threadSet_obj_at'_strongish[wp]:
  "\<lbrace>obj_at' (\<lambda>obj. if t = t' then P (f obj) else P obj) t'\<rbrace>
     threadSet f t \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  by (simp add: hoare_weaken_pre [OF threadSet_obj_at'_really_strongest])

lemma threadSet_pred_tcb_no_state:
  assumes "\<And>tcb. proj (tcb_to_itcb' (f tcb)) = proj (tcb_to_itcb' tcb)"
  shows   "\<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P' t' t.
            \<lbrace>pred_tcb_at' proj P' t'\<rbrace> threadSet f t \<lbrace>\<lambda>rv. pred_tcb_at' proj P' t'\<rbrace>"
    apply (simp add: pred_tcb_at'_def)
    apply (wp threadSet_obj_at'_strongish)
    apply clarsimp
    apply (erule obj_at'_weakenE)
    apply (insert assms)
    apply clarsimp
    done
  show ?thesis
    apply (rule_tac P=P in P_bool_lift)
     apply (rule pos)
    apply (rule_tac Q="\<lambda>_ s. \<not> tcb_at' t' s \<or> pred_tcb_at' proj (\<lambda>tcb. \<not> P' tcb) t' s"
             in hoare_post_imp)
     apply (erule disjE)
      apply (clarsimp dest!: pred_tcb_at')
     apply (clarsimp)
     apply (frule_tac P=P' and Q="\<lambda>tcb. \<not> P' tcb" in pred_tcb_at_conj')
     apply (clarsimp)+
    apply (wp hoare_convert_imp pos)
    apply (clarsimp simp: tcb_at_typ_at' pred_tcb_at'_def not_obj_at'
                   elim!: obj_at'_weakenE)
    done
qed

lemma threadSet_mdb':
  "\<lbrace>valid_mdb' and obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF (f t)) t\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (wpsimp wp: setObject_tcb_mdb' getTCB_wp simp: threadSet_def obj_at'_def)
  apply fastforce
  done

lemma threadSet_sch_act:
  "(\<And>tcb. tcbState (F tcb) = tcbState tcb \<and> tcbDomain (F tcb) = tcbDomain tcb) \<Longrightarrow>
  \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  threadSet F t
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp sch_act_wf_lift threadSet_pred_tcb_no_state | simp add: tcb_in_cur_domain'_def)+
    apply (rule_tac f="ksCurDomain" in hoare_lift_Pf)
     apply (wp threadSet_obj_at'_strongish | simp)+
  done

lemma threadSet_sch_actT_P:
  assumes z: "\<not> P \<Longrightarrow> (\<forall>tcb. tcbState (F tcb) = tcbState tcb
                         \<and> tcbDomain (F tcb) = tcbDomain tcb)"
  assumes z': "P \<Longrightarrow> (\<forall>tcb. tcbState (F tcb) = Inactive \<and> tcbDomain (F tcb) = tcbDomain tcb )
                      \<and> (\<forall>st. Q st \<longrightarrow> st = Inactive)"
  shows "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> (P \<longrightarrow> st_tcb_at' Q t s)\<rbrace>
          threadSet F t
         \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  using z z'
  apply (case_tac P, simp_all add: threadSet_sch_act)
  apply (clarsimp simp: valid_def)
  apply (frule_tac P1="\<lambda>sa. sch_act_wf sa s"
                in use_valid [OF _ threadSet.ksSchedulerAction], assumption)
  apply (frule_tac P1="(=) (ksCurThread s)"
                in use_valid [OF _ threadSet.ct], rule refl)
  apply (frule_tac P1="(=) (ksCurDomain s)"
                in use_valid [OF _ threadSet.cur_domain], rule refl)
  apply (case_tac "ksSchedulerAction b",
         simp_all add: ct_in_state'_def pred_tcb_at'_def)
   apply (subgoal_tac "t \<noteq> ksCurThread s")
    apply (drule_tac t'1="ksCurThread s"
                 and P1="activatable' \<circ> tcbState"
                  in use_valid [OF _ threadSet_obj_at'_really_strongest])
     apply (clarsimp simp: o_def)
    apply (clarsimp simp: o_def)
   apply (fastforce simp: obj_at'_def)
  apply (rename_tac word)
  apply (subgoal_tac "t \<noteq> word")
   apply (frule_tac t'1=word
                and P1="runnable' \<circ> tcbState"
                 in use_valid [OF _ threadSet_obj_at'_really_strongest])
    apply (clarsimp simp: o_def)
   apply (rule conjI)
    apply (clarsimp simp: o_def)
   apply (clarsimp simp: tcb_in_cur_domain'_def)
   apply (frule_tac t'1=word
                and P1="\<lambda>tcb. ksCurDomain b = tcbDomain tcb"
                 in use_valid [OF _ threadSet_obj_at'_really_strongest])
    apply (clarsimp simp: o_def)+
  apply (fastforce simp: obj_at'_def)
  done

lemma threadSet_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> threadSet F t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  by (intro hoare_vcg_all_lift hoare_vcg_disj_lift; wp)

lemma threadSet_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. (\<exists>tcb. tcbQueued (F tcb) \<and> \<not> tcbQueued tcb)
                          \<longrightarrow> ksSchedulerAction s = ResumeCurrentThread
                          \<longrightarrow> t \<noteq> ksCurThread s)\<rbrace>
   threadSet F t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: threadSet_def ct_not_inQ_def)
  apply (wp)
    apply (rule hoare_convert_imp [OF setObject_nosch])
     apply (wpsimp wp: updateObject_default_inv)
    apply (wps setObject_ct_inv)
    apply (wp setObject_tcb_strongest getObject_tcb_wp)+
  apply (case_tac "t = ksCurThread s")
   apply (clarsimp simp: obj_at'_def)+
  done

lemma threadSet_invs_trivial_helper[simp]:
  "{r \<in> state_refs_of' s t. snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
    \<union> {r \<in> state_refs_of' s t. (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)}
   = state_refs_of' s t"
  by auto

lemma threadSet_ct_idle_or_in_cur_domain':
  "(\<And>tcb. tcbDomain (F tcb) = tcbDomain tcb) \<Longrightarrow> \<lbrace>ct_idle_or_in_cur_domain'\<rbrace> threadSet F t \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
      apply (wp hoare_vcg_disj_lift| simp)+
  done

lemma threadSet_valid_dom_schedule':
  "\<lbrace> valid_dom_schedule'\<rbrace> threadSet F t \<lbrace>\<lambda>_. valid_dom_schedule'\<rbrace>"
  unfolding threadSet_def valid_dom_schedule'_def
  by (wp setObject_ksDomSchedule_inv hoare_Ball_helper)

lemma threadSet_invs_trivialT:
  assumes x: "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  assumes z: "\<forall>tcb. tcbState (F tcb) = tcbState tcb"
  assumes w: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes a1: "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
  assumes a2: "\<forall>tcb. tcbSchedContext (F tcb) = tcbSchedContext tcb"
  assumes a3: "\<forall>tcb. tcbYieldTo (F tcb) = tcbYieldTo tcb"
  assumes w: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes v: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes u: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  assumes b: "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  shows
  "\<lbrace>\<lambda>s. invs' s \<and>
       (\<forall>d p. (\<exists>tcb. inQ d p tcb \<and> \<not> inQ d p (F tcb)) \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p))) \<and>
       (\<forall>ko d p. ko_at' ko t s \<and> inQ d p (F ko) \<and> \<not> inQ d p ko \<longrightarrow> t \<in> set (ksReadyQueues s (d, p))) \<and>
       ((\<exists>tcb. tcbInReleaseQueue tcb \<and> \<not> tcbInReleaseQueue (F tcb)) \<longrightarrow> t \<notin> set (ksReleaseQueue s)) \<and>
       (\<forall>ko. ko_at' ko t s \<and> tcbInReleaseQueue (F ko) \<longrightarrow> t \<in> set (ksReleaseQueue s)) \<and>
       ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)) \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  note threadSet_sch_actT_P[where P=False, simplified]
  have y: "\<forall>tcb. tcb_st_refs_of' (tcbState (F tcb)) = tcb_st_refs_of' (tcbState tcb) \<and>
                 valid_tcb_state' (tcbState (F tcb)) = valid_tcb_state' (tcbState tcb)"
    by (auto simp: z)
  show ?thesis
    apply (simp add: invs'_def split del: if_split)
    apply (rule hoare_pre)
     apply (wp x w v u b
              threadSet_valid_pspace'T
              threadSet_sch_actT_P[where P=False, simplified]
              threadSet_valid_queues threadSet_valid_release_queue threadSet_valid_release_queue'
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
              threadSet_valid_queues'
              threadSet_cur
              untyped_ranges_zero_lift
           | clarsimp simp: y z a1 a2 a3 cteCaps_of_def | rule refl)+
   apply (clarsimp simp: cur_tcb'_def valid_irq_node'_def valid_queues'_def valid_release_queue_def
                         valid_release_queue'_def o_def)
   by (auto simp: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def z a1 a2 a3
                  valid_queues_def valid_queues_no_bitmap_def obj_at'_def)
qed

lemmas threadSet_invs_trivial =
    threadSet_invs_trivialT [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma zobj_refs'_capRange:
  "s \<turnstile>' cap \<Longrightarrow> zobj_refs' cap \<subseteq> capRange cap"
  by (cases cap; simp add: valid_cap'_def capAligned_def capRange_def is_aligned_no_overflow)

lemma global'_no_ex_cap:
  "\<lbrakk>valid_global_refs' s; valid_pspace' s\<rbrakk> \<Longrightarrow> \<not> ex_nonz_cap_to' (ksIdleThread s) s"
  apply (clarsimp simp: ex_nonz_cap_to'_def valid_global_refs'_def valid_refs'_def2 valid_pspace'_def)
  apply (drule cte_wp_at_norm', clarsimp)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap', clarsimp)
  apply (clarsimp simp: cte_wp_at'_def dest!: zobj_refs'_capRange, blast)
  done

lemma global'_sc_no_ex_cap:
  "\<lbrakk>valid_global_refs' s; valid_pspace' s\<rbrakk> \<Longrightarrow> \<not> ex_nonz_cap_to' idle_sc_ptr s"
  apply (clarsimp simp: ex_nonz_cap_to'_def valid_global_refs'_def valid_refs'_def2 valid_pspace'_def)
  apply (drule cte_wp_at_norm', clarsimp)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap', clarsimp)
  apply (clarsimp simp: cte_wp_at'_def dest!: zobj_refs'_capRange, blast)
  done

lemma getObject_tcb_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::tcb. P and ko_at' t r\<rbrace>"
  by (wp getObject_obj_at'; simp)

lemma threadGet_sp':
  "\<lbrace>P\<rbrace> threadGet f p \<lbrace>\<lambda>t. obj_at' (\<lambda>t'. f t' = t) p and P\<rbrace>"
  including no_pre
  apply (simp add: threadGet_getObject)
  apply wp
  apply (rule hoare_strengthen_post)
   apply (rule getObject_tcb_sp)
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply simp
  done

lemma threadSet_valid_objs':
  "\<lbrace>valid_objs' and (\<lambda>s. \<forall>tcb. valid_tcb' tcb s \<longrightarrow> valid_tcb' (f tcb) s)\<rbrace>
  threadSet f t
  \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
    prefer 2
    apply (rule getObject_tcb_sp)
   apply (rule hoare_weaken_pre)
    apply (rule setObject_tcb_valid_objs)
   prefer 2
   apply assumption
  apply (clarsimp simp: valid_obj'_def)
  apply (frule (1) ko_at_valid_objs')
   apply simp
  apply (simp add: valid_obj'_def)
  apply (clarsimp elim!: obj_at'_weakenE)
  done

lemmas typ_at'_valid_tcb'_lift =
  typ_at'_valid_obj'_lift[where obj="KOTCB tcb" for tcb, unfolded valid_obj'_def, simplified]

lemmas setObject_valid_tcb' = typ_at'_valid_tcb'_lift[OF setObject_typ_at' setObject_sc_at'_n]

lemma setObject_valid_tcbs':
  assumes preserve_valid_tcb': "\<And>s s' ko ko' x n tcb tcb'.
            \<lbrakk> (ko', s') \<in> fst (updateObject val ko ptr x n s); P s;
              lookupAround2 ptr (ksPSpace s) = (Some (x, ko), n);
              projectKO_opt ko = Some tcb; projectKO_opt ko' = Some tcb';
              valid_tcb' tcb s \<rbrakk> \<Longrightarrow> valid_tcb' tcb' s"
  shows "\<lbrace>valid_tcbs' and P\<rbrace> setObject ptr val \<lbrace>\<lambda>rv. valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  apply (clarsimp simp: valid_def)
  apply (rename_tac s s' ptr' tcb)
  apply (prop_tac "\<forall>tcb'. valid_tcb' tcb s \<longrightarrow> valid_tcb' tcb s'")
   apply clarsimp
   apply (erule (1) use_valid[OF _ setObject_valid_tcb'])
  apply (drule spec, erule mp)
  apply (clarsimp simp: setObject_def in_monad split_def lookupAround2_char1)
  apply (rename_tac s ptr' new_tcb' ptr'' old_tcb_ko' s' f)
  apply (case_tac "ptr'' = ptr'"; clarsimp)
  apply (prop_tac "\<exists>old_tcb' :: tcb. projectKO_opt old_tcb_ko' = Some old_tcb'")
   apply (frule updateObject_type)
   apply (case_tac old_tcb_ko'; clarsimp simp: project_inject)
  apply (erule exE)
  apply (rule preserve_valid_tcb', assumption+)
     apply (simp add: prod_eqI lookupAround2_char1)
    apply force
   apply (clarsimp simp: project_inject)
  apply (clarsimp simp: project_inject)
  done

lemma setObject_tcb_valid_tcbs':
  "\<lbrace>valid_tcbs' and (tcb_at' t and valid_tcb' v)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_tcbs'\<rbrace>"
  apply (rule setObject_valid_tcbs')
  apply (clarsimp simp: updateObject_default_def in_monad project_inject)
  done

lemma threadSet_valid_tcb':
  "\<lbrace>valid_tcb' tcb and (\<lambda>s. \<forall>tcb. valid_tcb' tcb s \<longrightarrow> valid_tcb' (f tcb) s)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. valid_tcb' tcb\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wpsimp wp: setObject_valid_tcb')
  done

lemma threadSet_valid_tcbs':
  "\<lbrace>valid_tcbs' and (\<lambda>s. \<forall>tcb. valid_tcb' tcb s \<longrightarrow> valid_tcb' (f tcb) s)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. valid_tcbs'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (rule hoare_seq_ext[OF _ get_tcb_sp'])
  apply (wpsimp wp: setObject_tcb_valid_tcbs')
  apply (clarsimp simp: obj_at'_def valid_tcbs'_def)
  done

lemma asUser_valid_tcbs'[wp]:
  "asUser t f \<lbrace>valid_tcbs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wpsimp wp: threadSet_valid_tcbs' hoare_drop_imps
              simp: valid_tcb'_def tcb_cte_cases_def objBits_simps')
  done

lemma asUser_corres':
  assumes y: "corres_underlying Id False True r \<top> \<top> f g"
  shows      "corres r (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                       (as_user t f) (asUser t g)"
proof -
  note arch_tcb_context_get_def[simp]
  note atcbContextGet_def[simp]
  note arch_tcb_context_set_def[simp]
  note atcbContextSet_def[simp]
  have L1: "corres (\<lambda>tcb con. (arch_tcb_context_get o tcb_arch) tcb = con)
              (tcb_at t and pspace_aligned and pspace_distinct) \<top>
              (gets_the (get_tcb t)) (threadGet (atcbContextGet o tcbArch) t)"
    apply (rule corres_cross_over_guard[where Q="tcb_at' t"])
     apply (fastforce simp: tcb_at_cross state_relation_def)
    apply (rule corres_guard_imp)
      apply (simp add: threadGet_getObject)
      apply (rule corres_bind_return)
      apply (rule corres_split[OF getObject_TCB_corres])
        apply (simp add: tcb_relation_def arch_tcb_relation_def)
       apply wpsimp+
    done
  have L2: "\<And>tcb tcb' con con'. \<lbrakk> tcb_relation tcb tcb'; con = con'\<rbrakk>
              \<Longrightarrow> tcb_relation (tcb \<lparr> tcb_arch := arch_tcb_context_set con (tcb_arch tcb) \<rparr>)
                               (tcb' \<lparr> tcbArch := atcbContextSet con' (tcbArch tcb') \<rparr>)"
    by (simp add: tcb_relation_def arch_tcb_relation_def)
  have L3: "\<And>r add tcb tcb' con con'. \<lbrakk> r () (); con = con'\<rbrakk> \<Longrightarrow>
            corres r (\<lambda>s. get_tcb add s = Some tcb)
                     (\<lambda>s'. (tcb', s') \<in> fst (getObject add s'))
                     (set_object add (TCB (tcb \<lparr> tcb_arch := arch_tcb_context_set con (tcb_arch tcb) \<rparr>)))
                     (setObject add (tcb' \<lparr> tcbArch := atcbContextSet con' (tcbArch tcb') \<rparr>))"
    by (rule setObject_update_TCB_corres [OF L2],
        (simp add: tcb_cte_cases_def tcb_cap_cases_def cteSizeBits_def)+)
  have L4: "\<And>con con'. con = con' \<Longrightarrow>
            corres (\<lambda>(irv, nc) (irv', nc'). r irv irv' \<and> nc = nc')
                   \<top> \<top> (select_f (f con)) (select_f (g con'))"
    using y
    by (fastforce simp: corres_underlying_def select_f_def split_def Id_def)
  show ?thesis
    apply (rule corres_cross_over_guard[where Q="tcb_at' t"])
     apply (fastforce simp: tcb_at_cross state_relation_def)
    apply (simp add: as_user_def asUser_def)
    apply (rule corres_guard_imp)
      apply (rule_tac r'="\<lambda>tcb con. (arch_tcb_context_get o tcb_arch) tcb = con"
              in corres_split)
         apply simp
         apply (rule L1[simplified])
        apply (rule corres_split[OF L4])
           apply simp
          apply clarsimp
          apply (rule corres_split_nor)
             apply (simp add: threadSet_def)
             apply (rule corres_symb_exec_r)
                apply (rule L3[simplified])
                 prefer 5
                 apply (rule no_fail_pre_and, wp)
                apply (wp select_f_inv | simp)+
    done
qed

lemma asUser_corres:
  assumes y: "corres_underlying Id False True r \<top> \<top> f g"
  shows      "corres r (tcb_at t and invs) (tcb_at' t and invs') (as_user t f) (asUser t g)"
  apply (rule corres_guard_imp)
    apply (rule asUser_corres' [OF y])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (simp add: invs'_def valid_pspace'_def)
  done

lemma asUser_inv:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> asUser t f \<lbrace>\<lambda>x. P\<rbrace>"
proof -
  have P: "\<And>a b input. (a, b) \<in> fst (f input) \<Longrightarrow> b = input"
    by (rule use_valid [OF _ x], assumption, rule refl)
  have R: "\<And>x. tcbArch_update (\<lambda>_. tcbArch x) x = x"
    by (case_tac x, simp)
  show ?thesis
    apply (simp add: asUser_def split_def threadGet_getObject threadSet_def
                     liftM_def bind_assoc)
    apply (clarsimp simp: valid_def in_monad getObject_def readObject_def setObject_def
                          loadObject_default_def objBits_simps'
                          modify_def split_def updateObject_default_def
                          in_magnitude_check select_f_def omonad_defs obind_def
               split del: if_split
                   split: option.split_asm if_split_asm
                    dest!: P)
    apply (simp add: R map_upd_triv)
    done
qed

lemma asUser_getRegister_corres:
 "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
        (as_user t (getRegister r)) (asUser t (getRegister r))"
  apply (rule asUser_corres')
  apply (clarsimp simp: getRegister_def)
  done

lemma user_getreg_inv'[wp]:
  "\<lbrace>P\<rbrace> asUser t (getRegister r) \<lbrace>\<lambda>x. P\<rbrace>"
  apply (rule asUser_inv)
   apply (simp_all add: getRegister_def)
  done

end

crunches asUser
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation asUser: typ_at_all_props' "asUser tptr f"
  by typ_at_props'

lemma threadGet_wp:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (\<exists>tcb. ko_at' tcb t s \<and> P (f tcb) s)\<rbrace>
   threadGet f t
   \<lbrace>P\<rbrace>"
  apply (simp add: threadGet_getObject)
  apply (wp getObject_tcb_wp)
  done

lemma threadGet_sp:
  "\<lbrace>P\<rbrace> threadGet f ptr \<lbrace>\<lambda>rv s. \<exists>tcb :: tcb. ko_at' tcb ptr s \<and> f tcb = rv \<and> P s\<rbrace>"
  apply (wpsimp wp: threadGet_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma inReleaseQueue_wp:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (\<exists>tcb. ko_at' tcb t s \<and> P (tcbInReleaseQueue tcb) s)\<rbrace>
   inReleaseQueue t
   \<lbrace>P\<rbrace>"
  apply (simp add: inReleaseQueue_def)
  apply (wp threadGet_wp)
  done

lemma asUser_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> asUser t m \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wpsimp wp: threadSet_invs_trivial threadGet_wp)
  apply (fastforce dest!: invs_valid_release_queue'
                    simp: obj_at'_def valid_release_queue'_def)
  done

lemma asUser_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> asUser t m \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  done

crunch aligned'[wp]: asUser pspace_aligned'
  (simp: crunch_simps wp: crunch_wps)
crunch distinct'[wp]: asUser pspace_distinct'
  (simp: crunch_simps wp: crunch_wps)

lemma asUser_valid_objs [wp]:
  "\<lbrace>valid_objs'\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_valid_objs' hoare_drop_imps
             | simp add: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)+
  done

lemma asUser_valid_pspace'[wp]:
  "\<lbrace>valid_pspace'\<rbrace> asUser t m \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_valid_pspace' hoare_drop_imps | simp)+
  done

lemma asUser_valid_queues[wp]:
  "asUser t m \<lbrace>valid_queues\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  apply (wp threadSet_valid_queues hoare_drop_imps | simp)+
  done

lemma asUser_valid_release_queue[wp]:
  "asUser t m \<lbrace>valid_release_queue\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  apply (wp threadSet_valid_release_queue hoare_drop_imps | simp)+
  done

lemma asUser_ifunsafe'[wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> asUser t m \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_ifunsafe' hoare_drop_imps | simp)+
  done

lemma asUser_st_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     asUser t m
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_state_refs_of'[where h'=id and i'=id] hoare_drop_imps | simp)+
  done

lemma asUser_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> asUser t m \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_iflive' hoare_drop_imps | clarsimp | auto)+
  done

lemma asUser_cur_tcb[wp]:
  "\<lbrace>cur_tcb'\<rbrace> asUser t m \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_cur hoare_drop_imps | simp)+
  done

lemma asUser_cte_wp_at'[wp]:
  "\<lbrace>cte_wp_at' P p\<rbrace> asUser t m \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_cte_wp_at' hoare_drop_imps | simp)+
  done

lemma asUser_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> asUser t m \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma asUser_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> asUser t' f \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_pred_tcb_no_state)
     apply (case_tac tcb)
     apply (simp add: tcb_to_itcb'_def)
    apply (wpsimp wp: select_f_inv)+
  done

crunches asUser
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"
  and cur_domain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (simp: crunch_simps wp: hoare_drop_imps getObject_tcb_inv setObject_ct_inv)

lemma asUser_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> asUser t m \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
  apply (wp | wpc | simp)+
     apply (rule_tac f="ksCurDomain" in hoare_lift_Pf)
      apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | simp)+
  done

lemma asUser_tcbDomain_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace> asUser t m \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
  apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | wpc | simp | clarsimp simp: obj_at'_def)+
  done

lemma asUser_tcbPriority_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace> asUser t m \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
  apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | wpc | simp | clarsimp simp: obj_at'_def)+
  done

lemma asUser_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    asUser t m \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift)

lemma asUser_idle'[wp]:
  "\<lbrace>valid_idle'\<rbrace> asUser t m \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wpsimp wp: threadSet_idle' select_f_inv)
  done

lemma no_fail_asUser [wp]:
  "no_fail \<top> f \<Longrightarrow> no_fail (tcb_at' t) (asUser t f)"
  apply (simp add: asUser_def split_def)
  apply wp
   apply (simp add: no_fail_def)
   apply (wp hoare_drop_imps)
  apply simp
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma asUser_setRegister_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
             (as_user t (setRegister r v))
             (asUser t (setRegister r v))"
  apply (simp add: setRegister_def)
  apply (rule asUser_corres')
  apply (rule corres_modify'; simp)
  done

end

lemma getThreadState_corres':
  "t = t' \<Longrightarrow>
   corres thread_state_relation (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (get_thread_state t) (getThreadState t')"
  apply (simp add: get_thread_state_def getThreadState_def)
  apply (rule threadGet_corres)
  apply (simp add: tcb_relation_def)
  done

lemmas getThreadState_corres = getThreadState_corres'[OF refl]

lemma is_blocked_corres:
  "corres (=) (pspace_aligned and pspace_distinct and tcb_at tcb_ptr)  \<top>
              (is_blocked tcb_ptr) (isBlocked tcb_ptr)"
  apply (rule_tac Q="tcb_at' tcb_ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  unfolding is_blocked_def isBlocked_def
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_split[where b=return and Q="\<top>\<top>" and Q'="\<top>\<top>", simplified,
                                        OF getThreadState_corres ])
      apply (rename_tac st st')
      apply (case_tac st; clarsimp)
     apply wpsimp+
  done

lemma gts_wf'[wp]:
  "\<lbrace>valid_objs'\<rbrace> getThreadState t \<lbrace>valid_tcb_state'\<rbrace>"
  apply (simp add: getThreadState_def threadGet_getObject liftM_def)
  apply (wp getObject_tcb_wp)
  apply clarsimp
  apply (drule obj_at_ko_at', clarsimp)
  apply (frule ko_at_valid_objs', fastforce, simp)
  apply (fastforce simp: valid_obj'_def valid_tcb'_def)
  done

lemma gts_st_tcb_at'[wp]: "\<lbrace>st_tcb_at' P t\<rbrace> getThreadState t \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: getThreadState_def threadGet_getObject)
  apply wp
   apply (rule hoare_chain)
     apply (rule obj_at_getObject)
     apply (clarsimp simp: loadObject_default_def in_monad)
    apply assumption
   apply simp
  apply (simp add: pred_tcb_at'_def)
  done

lemma gts_inv'[wp]: "\<lbrace>P\<rbrace> getThreadState t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getThreadState_def) wp

lemma getBoundNotification_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (get_tcb_obj_ref tcb_bound_notification t) (getBoundNotification t)"
  apply (simp add: get_tcb_obj_ref_def getBoundNotification_def)
  apply (rule threadGet_corres)
  apply (simp add: tcb_relation_def)
  done

lemma gbn_bound_tcb_at'[wp]: "\<lbrace>bound_tcb_at' P t\<rbrace> getBoundNotification t \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: getBoundNotification_def threadGet_getObject)
  apply wp
   apply (rule hoare_strengthen_post)
    apply (rule obj_at_getObject)
    apply (clarsimp simp: loadObject_default_def in_monad)
   apply simp
  apply (simp add: pred_tcb_at'_def)
  done

lemma gbn_inv'[wp]: "\<lbrace>P\<rbrace> getBoundNotification t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getBoundNotification_def) wp

lemma isStopped_def2:
  "isStopped t = liftM (Not \<circ> activatable') (getThreadState t)"
  apply (unfold isStopped_def fun_app_def)
  apply (fold liftM_def)
  apply (rule arg_cong [where f="\<lambda>f. liftM f (getThreadState t)"])
  apply (rule ext)
  apply (simp split: Structures_H.thread_state.split)
  done

lemma isRunnable_def2:
  "isRunnable t = liftM runnable' (getThreadState t)"
  apply (simp add: isRunnable_def liftM_def)
  apply (rule bind_eqI, rule ext, rule arg_cong)
  apply (case_tac state)
  apply (clarsimp)+
  done

lemma isBlocked_inv[wp]:
  "\<lbrace>P\<rbrace> isBlocked t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: isBlocked_def | wp gts_inv')+

lemma isStopped_inv[wp]:
  "\<lbrace>P\<rbrace> isStopped t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: isStopped_def | wp gts_inv')+

lemma isRunnable_inv[wp]:
  "\<lbrace>P\<rbrace> isRunnable t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: isRunnable_def2 | wp gts_inv')+

lemma isRunnable_wp[wp]:
  "\<lbrace>\<lambda>s. Q (st_tcb_at' (runnable') t s) s\<rbrace> isRunnable t \<lbrace>Q\<rbrace>"
  apply (simp add: isRunnable_def2)
  apply (wpsimp simp: getThreadState_def threadGet_getObject wp: getObject_tcb_wp)
  apply (clarsimp simp: getObject_def valid_def in_monad st_tcb_at'_def
                        loadObject_default_def obj_at'_def
                        split_def objBits_simps in_magnitude_check)
  done

lemma setQueue_obj_at[wp]:
  "setQueue d p q \<lbrace>\<lambda>s. Q (obj_at' P t s)\<rbrace>"
  apply (simp add: setQueue_def)
  apply wp
  apply (fastforce intro: obj_at'_pspaceI)
  done

lemma setQueue_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    setQueue d p ts
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setQueue_def)
  apply wp
  apply simp
  done

lemma gq_wp[wp]: "\<lbrace>\<lambda>s. Q (ksReadyQueues s (d, p)) s\<rbrace> getQueue d p \<lbrace>Q\<rbrace>"
  by (simp add: getQueue_def, wp)

lemma no_fail_getQueue [wp]:
  "no_fail \<top> (getQueue d p)"
  by (simp add: getQueue_def)

lemma no_fail_setQueue [wp]:
  "no_fail \<top> (setQueue d p xs)"
  by (simp add: setQueue_def)

lemma in_magnitude_check':
  "\<lbrakk> is_aligned x n; (1 :: machine_word) < 2 ^ n; ksPSpace s x = Some y; ps = ksPSpace s \<rbrakk>
     \<Longrightarrow> ((v, s') \<in> fst (magnitudeCheck x (snd (lookupAround2 x ps)) n s)) =
        (s' = s \<and> ps_clear x n s)"
  by (simp add: in_magnitude_check)

lemma cdt_relation_trans_state[simp]:
  "cdt_relation (swp cte_at (trans_state f s)) m m' = cdt_relation (swp cte_at s) m m'"
  by (simp add: cdt_relation_def)


lemma getObject_obj_at_tcb:
  "\<lbrace>obj_at' (\<lambda>t. P t t) p\<rbrace> getObject p \<lbrace>\<lambda>t::tcb. obj_at' (P t) p\<rbrace>"
  apply (wp getObject_tcb_wp)
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply (erule obj_at'_weakenE)
  apply simp
  done

lemma threadGet_obj_at':
  "\<lbrace>obj_at' (\<lambda>t. P (f t) t) t\<rbrace> threadGet f t \<lbrace>\<lambda>rv. obj_at' (P rv) t\<rbrace>"
  by (simp add: threadGet_getObject | wp getObject_obj_at_tcb)+

lemma fun_if_triv[simp]:
  "(\<lambda>x. if x = y then f y else f x) = f"
  by (force)

lemma setQueue_corres:
  "corres dc \<top> \<top> (set_tcb_queue d p q) (setQueue d p q)"
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp: setQueue_def in_monad set_tcb_queue_def return_def simpler_modify_def)
  apply (fastforce simp: state_relation_def ready_queues_relation_def swp_def)
  done

lemma getQueue_corres: "corres (=) \<top> \<top> (get_tcb_queue qdom prio) (getQueue qdom prio)"
  apply (clarsimp simp add: getQueue_def state_relation_def ready_queues_relation_def get_tcb_queue_def gets_def)
  apply (fold gets_def)
  apply simp
  done

lemma no_fail_return:
  "no_fail x (return y)"
  by wp

lemma addToBitmap_noop_corres:
  "corres dc \<top> \<top> (return ()) (addToBitmap d p)"
  unfolding addToBitmap_def modifyReadyQueuesL1Bitmap_def getReadyQueuesL1Bitmap_def
            modifyReadyQueuesL2Bitmap_def getReadyQueuesL2Bitmap_def
  by (rule corres_noop)
     (wp | simp add: state_relation_def | rule no_fail_pre)+

lemma addToBitmap_if_null_noop_corres: (* used this way in Haskell code *)
  "corres dc \<top> \<top> (return ()) (if null queue then addToBitmap d p else return ())"
  by (cases "null queue", simp_all add: addToBitmap_noop_corres)

lemma removeFromBitmap_corres_noop:
  "corres dc \<top> \<top> (return ()) (removeFromBitmap tdom prioa)"
  unfolding removeFromBitmap_def
  by (rule corres_noop)
     (wp | simp add: bitmap_fun_defs state_relation_def | rule no_fail_pre)+

crunches addToBitmap, removeFromBitmap
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation addToBitmap: typ_at_all_props' "addToBitmap tdom prio"
  by typ_at_props'

global_interpretation removeFromBitmap: typ_at_all_props' "removeFromBitmap tdom prio"
  by typ_at_props'

lemma pspace_relation_tcb_domain_priority:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); kheap s t = Some (TCB tcb);
    ksPSpace s' t = Some (KOTCB tcb')\<rbrakk>
   \<Longrightarrow> tcb_domain tcb = tcbDomain tcb' \<and> tcb_priority tcb = tcbPriority tcb'"
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=t in bspec, blast)
  apply (drule_tac x="(t, other_obj_relation)" in bspec, simp)
  apply (clarsimp simp: other_obj_relation_def tcb_relation_def)
  done

lemma tcbSchedEnqueue_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct)
             (Invariants_H.valid_queues and valid_queues')
          (tcb_sched_action (tcb_sched_enqueue) t) (tcbSchedEnqueue t)"
    (is "corres _ _ ?conc_guard _ _")
proof -

  have ready_queues_helper:
    "\<And>t tcb s s'. \<lbrakk> obj_at' tcbQueued t s';  valid_queues' s'; kheap s t = Some (TCB tcb);
                   pspace_relation (kheap s) (ksPSpace s') \<rbrakk>
                   \<Longrightarrow> t \<in> set (ksReadyQueues s' (tcb_domain tcb, tcb_priority tcb))"
    unfolding valid_queues'_def
    apply  (clarsimp dest:  simp: obj_at'_def inQ_def tcb_relation_def)
    using pspace_relation_tcb_domain_priority by fastforce

  show ?thesis
    apply (rule corres_cross_over_guard[where Q="?conc_guard and tcb_at' t"])
     apply (fastforce intro: tcb_at_cross)
    unfolding tcbSchedEnqueue_def tcb_sched_action_def
    apply (rule corres_symb_exec_r[where Q'="\<lambda>rv. tcb_at' t and Invariants_H.valid_queues
                                                  and valid_queues'
                                                  and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
       defer
       apply (wp threadGet_obj_at'; simp_all)
      apply (wpsimp wp: threadGet_inv)
     apply (rule no_fail_pre, wp, blast)
    apply (case_tac queued; simp_all)
     apply (rule corres_no_failI)
      apply (simp add: no_fail_return)
     apply (clarsimp simp: in_monad gets_the_def bind_assoc
                           assert_opt_def exec_gets get_tcb_queue_def
                           set_tcb_queue_def simpler_modify_def ready_queues_relation_def
                           state_relation_def tcb_sched_enqueue_def thread_get_def get_tcb_def
                           gets_def get_def return_def fail_def bind_def tcb_at_def cdt_relation_def
                    split: option.splits Structures_A.kernel_object.splits)
    using ready_queues_helper apply blast

    apply (clarsimp simp: when_def)
    apply (rule stronger_corres_guard_imp)
      apply (rule corres_split[where r'="(=)", OF threadGet_corres])
         apply (clarsimp simp: tcb_relation_def)
        apply (rule corres_split[where r'="(=)", OF threadGet_corres])
           apply (clarsimp simp: tcb_relation_def)
          apply (rule corres_split[where r'="(=)"])
             apply (simp, rule getQueue_corres)
            apply (rule corres_split_noop_rhs2)
               apply (simp add: tcb_sched_enqueue_def split del: if_split)
               apply (rule_tac P=\<top> and Q="K (t \<notin> set queuea)" in corres_assume_pre)
               apply simp
               apply (rule setQueue_corres[unfolded dc_def])
              apply (rule corres_split_noop_rhs2)
                 apply (fastforce intro: addToBitmap_noop_corres)
                apply (fastforce intro: threadSet_corres_noop simp: tcb_relation_def)
               apply wp+
        apply (wp  getObject_tcb_wp | simp add: threadGet_def)+
    apply (fastforce simp: valid_queues_def valid_queues_no_bitmap_def obj_at'_def inQ_def
                           project_inject)
    done
qed

definition
  weak_sch_act_wf :: "scheduler_action \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "weak_sch_act_wf sa = (\<lambda>s. \<forall>t. sa = SwitchToThread t \<longrightarrow> st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s)"

lemma weak_sch_act_wf_updates[simp]:
  "\<And>f. weak_sch_act_wf sa (ksDomainTime_update f s) = weak_sch_act_wf sa s"
  "\<And>f. weak_sch_act_wf sa (ksReprogramTimer_update f s) = weak_sch_act_wf sa s"
  "\<And>f. weak_sch_act_wf sa (ksReleaseQueue_update f s) = weak_sch_act_wf sa s"
  by (auto simp: weak_sch_act_wf_def tcb_in_cur_domain'_def)

lemma setSchedulerAction_corres:
  "sched_act_relation sa sa'
    \<Longrightarrow> corres dc \<top> \<top> (set_scheduler_action sa) (setSchedulerAction sa')"
  apply (simp add: setSchedulerAction_def set_scheduler_action_def)
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp: in_monad simpler_modify_def state_relation_def swp_def)
  done

lemma getSchedulerAction_corres:
  "corres sched_act_relation \<top> \<top> (gets scheduler_action) getSchedulerAction"
  apply (simp add: getSchedulerAction_def)
  apply (clarsimp simp: state_relation_def)
  done


\<comment>\<open>
  State-preservation lemmas: lemmas of the form @{term "m \<lbrace>P\<rbrace>"}.
\<close>
lemmas tcb_inv_collection =
  getObject_tcb_inv
  threadGet_inv

\<comment>\<open>
  State preservation lowered through @{thm use_valid}. Results are of
  the form @{term "(rv, s') \<in> fst (m s) \<Longrightarrow> P s \<Longrightarrow> P s'"}.
\<close>
lemmas tcb_inv_use_valid =
  tcb_inv_collection[THEN use_valid[rotated], rotated]

\<comment>\<open>
  Low-level monadic state preservation. Results are of the form
  @{term "(rv, s') \<in> fst (m s) \<Longrightarrow> s = s'"}.
\<close>
lemmas tcb_inv_state_eq =
  tcb_inv_use_valid[where s=s and P="(=) s" for s, OF _ refl]

\<comment>\<open>
  For when you want an obj_at' goal instead of the ko_at' that @{thm threadGet_wp}
  gives you.
\<close>
lemma threadGet_obj_at'_field:
  "\<lbrace>\<lambda>s. tcb_at' ptr s \<longrightarrow> obj_at' (\<lambda>tcb. P (field tcb) s) ptr s\<rbrace>
   threadGet field ptr
   \<lbrace>P\<rbrace>"
  by (wpsimp wp: threadGet_wp
           simp: obj_at_ko_at')

\<comment>\<open>
  Getting a boolean field of a thread is the same as the thread
  "satisfying" the "predicate" which the field represents.
\<close>
lemma threadGet_obj_at'_bool_field:
  "\<lbrace>tcb_at' ptr\<rbrace>
   threadGet field ptr
   \<lbrace>\<lambda>rv s. obj_at' field ptr s = rv\<rbrace>"
   by (wpsimp wp: threadGet_wp
            simp: obj_at'_def)

lemma inReleaseQueue_corres:
  shows "corres (=)
          (tcb_at ptr)
          (tcb_at' ptr and valid_release_queue_iff)
          (gets (in_release_queue ptr))
          (inReleaseQueue ptr)"
  apply (simp add: gets_def)
  apply (rule corres_bind_return_l)
  apply (clarsimp simp: corres_underlying_def inReleaseQueue_def
                        valid_release_queue_def valid_release_queue'_def
                        no_fail_threadGet[unfolded no_fail_def])
  apply (rename_tac s s' rv t')
  apply (prop_tac "ksReleaseQueue s' = release_queue s")
   subgoal by (clarsimp simp: state_relation_def release_queue_relation_def)
  apply (frule tcb_inv_state_eq)
  apply (clarsimp simp: split_paired_Bex in_get)
  apply (frule tcb_inv_state_eq)
  apply (erule allE[where x=ptr])+
  apply (frule use_valid[OF _ threadGet_obj_at'_bool_field], assumption)
  apply (fastforce simp: in_release_q_def)
  done

lemma isRunnable_corres:
  "tcb_relation tcb_abs tcb_conc \<Longrightarrow>
   corres (=)
          (tcb_at t)
          (ko_at' tcb_conc t)
          (return (runnable (tcb_state tcb_abs)))
          (isRunnable t)"
  unfolding isRunnable_def getThreadState_def
  apply (rule corres_symb_exec_r[where Q'="\<lambda>rv s. tcbState tcb_conc = rv"])
     apply (case_tac "tcb_state tcb_abs"; clarsimp simp: tcb_relation_def)
    apply (wpsimp wp: threadGet_wp)
    apply (rule exI, fastforce)
   apply (rule tcb_inv_collection)
  apply (rule no_fail_pre[OF no_fail_threadGet])
  apply (clarsimp simp: obj_at'_weaken)
  done

lemma isSchedulable_corres:
  "corres (=)
          (valid_tcbs and pspace_aligned and pspace_distinct and tcb_at t)
          (valid_tcbs' and valid_release_queue_iff)
          (is_schedulable t)
          (isSchedulable t)"
    (is "corres _ _ ?conc_guard _ _")
  apply (rule corres_cross_over_guard[where Q="?conc_guard and tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  unfolding is_schedulable_def isSchedulable_def fun_app_def
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getObject_TCB_corres])
      apply (rename_tac tcb_abs tcb_conc)
      apply (rule corres_if[OF _ corres_return_eq_same])
        apply (clarsimp simp: tcb_relation_def Option.is_none_def)
       apply simp
      apply (rule corres_split[OF get_sc_corres[THEN equify]])
         apply (clarsimp simp: tcb_relation_def)
        apply (rename_tac sc_abs sc_conc)
        apply (rule corres_split[OF isRunnable_corres])
           apply assumption
          apply (rule corres_split[OF inReleaseQueue_corres])
            apply (clarsimp simp: sc_relation_def active_sc_def)
           apply blast
          apply wp+
    apply (wpsimp simp: pred_conj_def
                    wp: hoare_vcg_if_lift2 getObject_tcb_wp)
   apply (clarsimp simp: pred_conj_def)
   apply (frule (1) valid_tcbs_valid_tcb)
   apply (fastforce simp: valid_tcb_def valid_bound_obj_def obj_at_def split: option.splits)
  apply (fastforce simp: valid_tcbs'_def valid_tcb'_def obj_at'_def)
  done

lemma get_simple_ko_exs_valid:
  "\<lbrakk>inj C; \<exists>ko. ko_at (C ko) p s \<and> is_simple_type (C ko)\<rbrakk> \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_simple_ko C p \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (fastforce simp: get_simple_ko_def get_object_def gets_def return_def get_def
                      partial_inv_def exs_valid_def bind_def obj_at_def is_reply fail_def inj_def
                      gets_the_def assert_def)

lemmas get_notification_exs_valid[wp] =
  get_simple_ko_exs_valid[where C=kernel_object.Notification, simplified]
lemmas get_reply_exs_valid[wp] =
  get_simple_ko_exs_valid[where C=kernel_object.Reply, simplified]
lemmas get_endpoint_exs_valid[wp] =
  get_simple_ko_exs_valid[where C=kernel_object.Endpoint, simplified]

lemma thread_get_exs_valid:
  "tcb_at tcb_ptr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> thread_get f tcb_ptr \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (clarsimp simp: thread_get_def get_tcb_def gets_the_def gets_def return_def get_def
                     exs_valid_def tcb_at_def bind_def)

lemma isRunnable_sp:
  "\<lbrace>P\<rbrace>
   isRunnable tcb_ptr
   \<lbrace>\<lambda>rv s. \<exists>tcb'. ko_at' tcb' tcb_ptr s
                  \<and> (rv = (tcbState tcb' = Running \<or> tcbState tcb' = Restart))
           \<and> P s\<rbrace>"
  unfolding isRunnable_def getThreadState_def
  apply (wpsimp wp: hoare_case_option_wp getObject_tcb_wp simp: threadGet_getObject)
  apply (fastforce simp: obj_at'_def split: Structures_H.thread_state.splits)
  done

lemma isRunnable_sp':
  "\<lbrace>P\<rbrace>
   isRunnable tcb_ptr
   \<lbrace>\<lambda>rv s. (rv = st_tcb_at' active' tcb_ptr s) \<and> P s\<rbrace>"
  apply (clarsimp simp: isRunnable_def getThreadState_def)
  apply (wpsimp wp: hoare_case_option_wp getObject_tcb_wp
              simp: threadGet_getObject)
  apply (fastforce simp: obj_at'_def st_tcb_at'_def
                  split: Structures_H.thread_state.splits)
  done

lemma inReleaseQueue_sp:
  "\<lbrace>P\<rbrace>
   inReleaseQueue tcb_ptr
   \<lbrace>\<lambda>rv s. \<exists>tcb'. ko_at' tcb' tcb_ptr s \<and> (rv = (tcbInReleaseQueue tcb')) \<and> P s\<rbrace>"
  unfolding inReleaseQueue_def
  apply (wpsimp wp: hoare_case_option_wp getObject_tcb_wp simp: threadGet_getObject)
  apply (clarsimp simp: obj_at'_def)
  done

lemma inReleaseQueue_inv[wp]:
  "inReleaseQueue t \<lbrace>P\<rbrace>"
  by (simp add: inReleaseQueue_def | wp gts_inv')+

lemma conjunct_rewrite:
  "P = P' \<and> Q = Q' \<and> R = R' \<Longrightarrow> (P \<and> Q \<and> R) = (P' \<and> Q' \<and> R')"
  by simp

lemma isSchedulable_inv[wp]:
  "isSchedulable tcbPtr \<lbrace>P\<rbrace>"
  apply (clarsimp simp: isSchedulable_def inReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ getObject_tcb_inv])
  by (wpsimp wp: inReleaseQueue_inv)

lemma get_sc_refill_sufficient_sp:
  "\<lbrace>P\<rbrace>
   get_sc_refill_sufficient sc_ptr usage
   \<lbrace>\<lambda>rv s. (\<exists>sc n. ko_at (kernel_object.SchedContext sc n) sc_ptr s
                   \<and> (rv = sc_refill_sufficient usage sc))
           \<and> P s\<rbrace>"
  by (wpsimp simp: get_sc_refill_sufficient_def obj_at_def)

lemma get_sc_refill_ready_sp:
  "\<lbrace>P\<rbrace>
   get_sc_refill_ready sc_ptr
   \<lbrace>\<lambda>rv s. (\<exists>sc n. ko_at (kernel_object.SchedContext sc n) sc_ptr s
                   \<and> (rv = sc_refill_ready (cur_time s) sc))
           \<and> P s\<rbrace>"
  by (wpsimp simp: obj_at_def)

\<comment> \<open>In sched_context_donate, weak_valid_sched_action does not propagate backwards over the statement
    where from_tptr's sched context is set to None because it requires the thread associated with a
    switch_thread action to have a sched context. For this instance, we introduce a weaker version
    of weak_valid_sched_action that is sufficient to prove refinement for reschedule_required\<close>
definition weaker_valid_sched_action :: "det_state \<Rightarrow> bool" where
  "weaker_valid_sched_action s \<equiv>
   \<forall>t. scheduler_action s = switch_thread t \<longrightarrow>
       tcb_at t s \<and> (bound_sc_tcb_at ((\<noteq>) None) t s \<longrightarrow> released_sc_tcb_at t s)"

lemma weak_valid_sched_action_strg:
  "weak_valid_sched_action s \<longrightarrow> weaker_valid_sched_action s"
  by (fastforce simp: weak_valid_sched_action_def weaker_valid_sched_action_def
                      obj_at_kh_kheap_simps vs_all_heap_simps is_tcb_def
               split: Structures_A.kernel_object.splits)

lemma no_ofail_get_tcb[wp]:
  "no_ofail (tcb_at tp) (get_tcb tp)"
  unfolding get_tcb_def no_ofail_def
  by (clarsimp simp: obj_at_def is_tcb split: option.splits)

lemma no_ofail_read_sched_context[wp]:
  "no_ofail (\<lambda>s. \<exists>sc n. kheap s scp = Some (Structures_A.SchedContext sc n)) (read_sched_context scp)"
  unfolding read_sched_context_def no_ofail_def
  by (clarsimp simp: obj_at_def is_sc_obj obind_def)

lemma no_ofail_read_sc_refill_ready:
  "no_ofail (\<lambda>s. \<exists>sc n. kheap s scp = Some (Structures_A.SchedContext sc n)) (read_sc_refill_ready scp)"
  unfolding read_sc_refill_ready_def no_ofail_def
  by (clarsimp simp: omonad_defs obind_def dest!: no_ofailD[OF no_ofail_read_sched_context])

lemma rescheduleRequired_corres_weak:
  "corres dc (valid_tcbs and weaker_valid_sched_action and pspace_aligned and pspace_distinct
              and active_sc_valid_refills)
             (valid_tcbs' and Invariants_H.valid_queues and valid_queues' and valid_release_queue_iff)
             reschedule_required rescheduleRequired"
  apply (simp add: rescheduleRequired_def reschedule_required_def)
  apply (rule corres_underlying_split[OF _ _ gets_sp, rotated 2])
    apply (clarsimp simp: getSchedulerAction_def)
    apply (rule gets_sp)
   apply (corressimp corres: getSchedulerAction_corres)
  apply (rule corres_underlying_split[where r'=dc, rotated]; (solves \<open>wpsimp\<close>)?)
   apply (corressimp corres: setSchedulerAction_corres)
  apply (case_tac action; clarsimp?)
  apply (rename_tac tp)
  apply (rule corres_underlying_split[OF _ _ is_schedulable_sp isSchedulable_inv, rotated 2])
   apply (corressimp corres: isSchedulable_corres)
   apply (clarsimp simp: weaker_valid_sched_action_def obj_at_def vs_all_heap_simps is_tcb_def)
  apply (clarsimp simp: when_def)

  apply (rule corres_symb_exec_l[OF _ thread_get_exs_valid thread_get_sp , rotated])
    apply (clarsimp simp: weaker_valid_sched_action_def vs_all_heap_simps obj_at_def is_tcb_def)
   apply (wpsimp simp: thread_get_def get_tcb_def weaker_valid_sched_action_def vs_all_heap_simps)
   apply (clarsimp simp: obj_at_def is_tcb_def)
   apply (clarsimp split: Structures_A.kernel_object.splits)
  apply (rule corres_symb_exec_l[OF _ _ assert_opt_sp, rotated])
    apply (clarsimp simp: exs_valid_def obj_at_def return_def is_schedulable_opt_def get_tcb_def
                   split: option.splits)
   apply (clarsimp simp: no_fail_def obj_at_def return_def is_schedulable_opt_def get_tcb_def
                  split: Structures_A.kernel_object.splits option.splits)

  apply (rule corres_symb_exec_l[OF _ _ get_sc_refill_sufficient_sp, rotated])
    apply (wpsimp wp: get_sched_context_exs_valid exs_valid_bind
                simp: get_sc_refill_sufficient_def is_schedulable_opt_def get_tcb_def obj_at_def
                      is_sc_active_def
               split: Structures_A.kernel_object.splits option.splits)
   apply (wpsimp wp: get_sched_context_no_fail simp: get_sc_refill_sufficient_def)
   apply (fastforce simp: valid_tcbs_def valid_tcb_def obj_at_def is_schedulable_opt_def get_tcb_def
                          is_sc_active_def is_sc_obj_def
                   split: option.splits Structures_A.kernel_object.splits)

  apply (rule corres_symb_exec_l[OF _ _ get_sc_refill_ready_sp, rotated])
    apply (wpsimp wp: get_sched_context_exs_valid gets_the_exs_valid
                simp: get_sc_refill_ready_def)
     apply (clarsimp intro!: no_ofailD[OF no_ofail_read_sc_refill_ready] simp: obj_at_def is_sc_obj)
    apply simp
   apply (wpsimp wp: get_sched_context_no_fail simp: get_sc_refill_ready_def)
   apply (clarsimp intro!: no_ofailD[OF no_ofail_read_sc_refill_ready] simp: obj_at_def is_sc_obj)
  apply (rule_tac F=sufficient in corres_req)
   apply (clarsimp simp: obj_at_def is_schedulable_opt_def get_tcb_def)
   apply (drule_tac tp=tp in active_valid_budget_sufficient)
    apply (clarsimp simp: vs_all_heap_simps is_sc_active_def)
   apply (clarsimp simp: return_def vs_all_heap_simps
                         obj_at_def pred_tcb_at_def weaker_valid_sched_action_def)
  apply (rule corres_symb_exec_l[OF _ _ assert_sp, rotated])
    apply (clarsimp simp: exs_valid_def return_def vs_all_heap_simps
                          obj_at_def pred_tcb_at_def weaker_valid_sched_action_def)
   apply (clarsimp simp: no_fail_def return_def vs_all_heap_simps
                         obj_at_def pred_tcb_at_def weaker_valid_sched_action_def)
  apply (corressimp corres: tcbSchedEnqueue_corres
                      simp: obj_at_def is_tcb_def weak_sch_act_wf_def)
  done

lemma rescheduleRequired_corres:
  "corres dc (valid_tcbs and weak_valid_sched_action and pspace_aligned and pspace_distinct
              and active_sc_valid_refills)
             (valid_tcbs' and valid_queues and valid_queues' and valid_release_queue_iff)
             reschedule_required rescheduleRequired"
  by (rule corres_guard_imp[OF rescheduleRequired_corres_weak])
     (auto simp: weak_valid_sched_action_strg)

lemma rescheduleRequired_corres_simple:
  "corres dc \<top> sch_act_simple
     (set_scheduler_action choose_new_thread) rescheduleRequired"
  apply (simp add: rescheduleRequired_def)
  apply (rule corres_symb_exec_r[where Q'="\<lambda>rv s. rv = ResumeCurrentThread \<or> rv = ChooseNewThread"])
     apply (rule corres_symb_exec_r)
        apply (rule setSchedulerAction_corres, simp)
       apply (wp | clarsimp split: scheduler_action.split)+
    apply (wp | clarsimp simp: sch_act_simple_def split: scheduler_action.split)+
  apply (simp add: getSchedulerAction_def)
  done

lemma weak_sch_act_wf_lift:
  assumes pre: "\<And>P. \<lbrace>\<lambda>s. P (sa s)\<rbrace> f \<lbrace>\<lambda>rv s. P (sa s)\<rbrace>"
               "\<And>t. \<lbrace>st_tcb_at' runnable' t\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
               "\<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_in_cur_domain' t\<rbrace>"
  shows "\<lbrace>\<lambda>s. weak_sch_act_wf (sa s) s\<rbrace> f \<lbrace>\<lambda>rv s. weak_sch_act_wf (sa s) s\<rbrace>"
  apply (simp only: weak_sch_act_wf_def imp_conv_disj)
  apply (intro hoare_vcg_all_lift hoare_vcg_conj_lift hoare_vcg_disj_lift pre | simp)+
  done

lemma asUser_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    asUser t m \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift)

lemma doMachineOp_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     doMachineOp m \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (simp add: doMachineOp_def split_def tcb_in_cur_domain'_def | wp weak_sch_act_wf_lift)+

lemma weak_sch_act_wf_setQueue[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>
    setQueue qdom prio queue
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  by (simp add: setQueue_def weak_sch_act_wf_def tcb_in_cur_domain'_def | wp)+

lemma threadSet_tcbDomain_triv:
  assumes "\<And>tcb. tcbDomain (f tcb) = tcbDomain tcb"
  shows   "\<lbrace>tcb_in_cur_domain' t'\<rbrace> threadSet f t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule_tac f="ksCurDomain" in hoare_lift_Pf)
   apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | simp add: assms)+
  done

lemmas threadSet_weak_sch_act_wf
  = weak_sch_act_wf_lift[OF threadSet.ksSchedulerAction threadSet_pred_tcb_no_state threadSet_tcbDomain_triv, simplified]

lemma removeFromBitmap_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> removeFromBitmap d p \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  unfolding removeFromBitmap_def
  by (simp add: bitmap_fun_defs|wp setObject_nosch)+

lemma addToBitmap_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> addToBitmap d p \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  unfolding addToBitmap_def
  by (simp add: bitmap_fun_defs|wp setObject_nosch)+

lemmas removeFromBitmap_weak_sch_act_wf[wp]
  = weak_sch_act_wf_lift[OF removeFromBitmap_nosch]

lemmas addToBitmap_weak_sch_act_wf[wp]
  = weak_sch_act_wf_lift[OF addToBitmap_nosch]

crunches removeFromBitmap, addToBitmap
  for obj_at'[wp]: "\<lambda>s. Q (obj_at' P t s)"
  and pred_tcb_at'[wp]: "\<lambda>s. Q (pred_tcb_at' proj P' t s)"

lemma removeFromBitmap_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> removeFromBitmap tdom prio \<lbrace>\<lambda>ya. tcb_in_cur_domain' t\<rbrace>"
  unfolding tcb_in_cur_domain'_def removeFromBitmap_def
  apply (rule_tac f="\<lambda>s. ksCurDomain s" in hoare_lift_Pf)
  apply (wp setObject_cte_obj_at_tcb' | simp add: bitmap_fun_defs)+
  done

lemma addToBitmap_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> addToBitmap tdom prio \<lbrace>\<lambda>ya. tcb_in_cur_domain' t\<rbrace>"
  unfolding tcb_in_cur_domain'_def addToBitmap_def
  apply (rule_tac f="\<lambda>s. ksCurDomain s" in hoare_lift_Pf)
  apply (wp setObject_cte_obj_at_tcb' | simp add: bitmap_fun_defs)+
  done

lemma tcbSchedDequeue_weak_sch_act_wf[wp]:
  "\<lbrace> \<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace> tcbSchedDequeue a \<lbrace> \<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadSet_weak_sch_act_wf removeFromBitmap_weak_sch_act_wf | simp add: crunch_simps)+
  done

lemma dequeue_nothing_eq[simp]:
  "t \<notin> set list \<Longrightarrow> tcb_sched_dequeue t list = list"
  apply (clarsimp simp: tcb_sched_dequeue_def)
  apply (induct list)
   apply simp
  apply clarsimp
  done

lemma gets_the_exec: "f s \<noteq> None \<Longrightarrow>  (do x \<leftarrow> gets_the f; g x od) s = g (the (f s)) s"
  apply (clarsimp simp add: gets_the_def bind_def gets_def get_def
                   return_def assert_opt_def)
  done

lemma tcbSchedDequeue_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) valid_queues
             (tcb_sched_action tcb_sched_dequeue t) (tcbSchedDequeue t)"
  apply (rule_tac Q="tcb_at' t" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (simp only: tcbSchedDequeue_def tcb_sched_action_def)
  apply (rule corres_symb_exec_r[OF _ _ threadGet_inv, where Q'="\<lambda>rv. tcb_at' t and Invariants_H.valid_queues and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
    defer
    apply (wp threadGet_obj_at', simp, simp)
   apply (rule no_fail_pre, wp, simp)
  apply (case_tac queued)
   defer
   apply (simp add: when_def)
   apply (rule corres_no_failI)
    apply (wp)
   apply (clarsimp simp: in_monad thread_get_def set_tcb_queue_def state_relation_def tcb_at_def
                         get_tcb_def
                  split: Structures_A.kernel_object.split option.splits)
   apply (rename_tac tcb s')
   apply (prop_tac "t \<notin> set (ready_queues a (tcb_domain tcb) (tcb_priority tcb))")
    apply (clarsimp simp: tcb_sched_dequeue_def Invariants_H.valid_queues_def
                          valid_queues_no_bitmap_def ready_queues_relation_def obj_at'_def inQ_def
                          projectKO_eq project_inject)
    apply (drule spec, clarsimp)+
    apply (drule(1) bspec)
    subgoal by force
   apply (subst gets_the_exec)
    apply (simp add: get_tcb_def)
   apply (subst gets_the_exec)
    apply (simp add: get_tcb_def)
   apply (simp add: exec_gets simpler_modify_def get_tcb_def ready_queues_relation_def
                    cdt_relation_def
              cong: if_cong get_tcb_queue_def)
  apply (simp add: when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)", OF threadGet_corres], simp add: tcb_relation_def)
      apply (rule corres_split[where r'="(=)", OF threadGet_corres], simp add: tcb_relation_def)
        apply (rule corres_split[where r'="(=)"])
           apply (simp, rule getQueue_corres)
          apply (rule corres_split_noop_rhs2)
             apply (simp add: tcb_sched_dequeue_def
                              [[@\<open>prove_prop \<open>(\<lambda>x. x \<noteq> t) = (\<noteq>) t\<close>\<close>]])
             apply (rule setQueue_corres)
            apply (rule corres_split_noop_rhs)
              apply (clarsimp, rule removeFromBitmap_corres_noop)
             apply (rule threadSet_corres_noop; simp_all add: tcb_relation_def)
            apply (wp | simp)+
  done

lemma thread_get_test: "do cur_ts \<leftarrow> get_thread_state cur; g (test cur_ts) od =
       do t \<leftarrow> (thread_get (\<lambda>tcb. test (tcb_state tcb)) cur); g t od"
  apply (simp add: get_thread_state_def thread_get_def)
  done

lemma thread_get_isRunnable_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
              (thread_get (\<lambda>tcb. runnable (tcb_state tcb)) t) (isRunnable t)"
  apply (simp add: isRunnable_def getThreadState_def threadGet_getObject thread_get_def)
  apply (fold liftM_def)
  apply simp
  apply (rule corres_rel_imp)
   apply (rule getObject_TCB_corres)
  apply (clarsimp simp add: tcb_relation_def thread_state_relation_def)
  apply (case_tac "tcb_state x",simp_all)
  done

lemma setObject_tcbState_update_corres:
  "\<lbrakk>thread_state_relation ts ts'; tcb_relation tcb tcb'\<rbrakk> \<Longrightarrow>
   corres dc
          (ko_at (TCB tcb) t)
          (ko_at' tcb' t)
          (set_object t (TCB (tcb\<lparr>tcb_state := ts\<rparr>)))
          (setObject t (tcbState_update (\<lambda>_. ts') tcb'))"
  apply (rule setObject_update_TCB_corres')
     apply (simp add: tcb_relation_def)
    apply (rule ball_tcb_cap_casesI; clarsimp)
   apply (rule ball_tcb_cte_casesI; clarsimp)
  apply simp
  done

lemma threadSet_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb :: tcb. ko_at' tcb t s \<longrightarrow> P (set_obj' t (f tcb) s)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: setObject_tcb_wp set_tcb'.getObject_wp)
  done

\<comment>\<open>
  If we don't change the @{term tcbInReleaseQueue} flag of a TCB,
  then the release queues stay valid.
\<close>
lemma setObject_valid_release_queue:
  "\<lbrace>valid_release_queue
      and obj_at' (\<lambda>old_tcb. tcbInReleaseQueue old_tcb \<longrightarrow> tcbInReleaseQueue tcb) ptr\<rbrace>
   setObject ptr tcb
   \<lbrace>\<lambda>rv. valid_release_queue\<rbrace>"
  unfolding valid_release_queue_def
  apply (rule hoare_allI)
  apply (wpsimp wp: setObject_tcb_obj_at'_strongest hoare_vcg_imp_lift)
  apply (clarsimp simp: obj_at'_imp obj_at'_def)
  done

lemma setObject_valid_release_queue':
  "\<lbrace>valid_release_queue'
      and obj_at' (\<lambda>old_tcb. tcbInReleaseQueue tcb \<longrightarrow> tcbInReleaseQueue old_tcb) ptr\<rbrace>
   setObject ptr tcb
   \<lbrace>\<lambda>rv. valid_release_queue'\<rbrace>"
  unfolding valid_release_queue'_def
  apply (rule hoare_allI)
  apply (wpsimp wp: setObject_tcb_obj_at'_strongest hoare_vcg_imp_lift)
  apply (rename_tac t s)
  apply (case_tac "ptr = t"; clarsimp)
  done

lemma setThreadState_corres:
  assumes "thread_state_relation ts ts'"
  shows "corres dc
          (valid_tcbs and pspace_aligned and pspace_distinct and tcb_at t and valid_tcb_state ts)
          (valid_tcbs' and valid_release_queue_iff)
          (set_thread_state t ts) (setThreadState ts' t)"
    (is "corres _ _ ?conc_guard _ _")
  using assms
  apply -
  apply (rule corres_cross_over_guard
                  [where Q="?conc_guard and tcb_at' t and valid_tcb_state' ts'"])
   apply (solves \<open>auto simp: state_relation_def intro: valid_tcb_state_cross tcb_at_cross\<close>)[1]
  apply (simp add: set_thread_state_def setThreadState_def threadSet_def)
  apply (rule corres_guard_imp)
    apply (subst bind_assoc)
    apply (rule corres_split[OF getObject_TCB_corres])
      apply (rule corres_split[OF setObject_tcbState_update_corres])
          apply assumption
         apply assumption
        apply (simp add: set_thread_state_act_def scheduleTCB_def)
        apply (rule corres_split[OF getCurThread_corres])
          apply (rule corres_split[OF getSchedulerAction_corres])
            apply (rule corres_split[OF isSchedulable_corres])
              apply (rule corres_split corres_when)+
               apply (rename_tac sched_act sched_act' dont_care dont_care')
               apply (case_tac sched_act; clarsimp)
              apply (rule rescheduleRequired_corres_simple)
             apply wpsimp
            apply (wpsimp simp: isSchedulable_def inReleaseQueue_def
                            wp: threadGet_obj_at'_field getObject_tcb_wp)
           apply wp
          apply wp
         apply wp
        apply wp
       apply wpsimp
      apply (wpsimp simp: pred_conj_def sch_act_simple_def obj_at_ko_at'_eq
                      wp: setObject_tcb_valid_tcbs' setObject_tcb_obj_at'_strongest
                          setObject_valid_release_queue setObject_valid_release_queue')
     apply wp
    apply (wpsimp wp: getObject_tcb_wp)
   apply (fastforce intro: valid_tcb_state_update valid_tcbs_valid_tcb
                     simp: obj_at_def is_tcb_def)
  apply (fastforce intro: valid_tcb'_tcbState_update
                    simp: valid_tcbs'_def obj_at'_def)+
  done

lemma set_tcb_obj_ref_corresT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation (f (\<lambda>_. new) tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f (\<lambda>_. new) tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  shows      "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                     (set_tcb_obj_ref f t new) (threadSet f' t)"
  by (clarsimp simp: set_tcb_obj_ref_thread_set threadset_corresT x y z)

lemmas set_tcb_obj_ref_corres =
    set_tcb_obj_ref_corresT [OF _ _ all_tcbI, OF _ ball_tcb_cap_casesI ball_tcb_cte_casesI]

lemma setBoundNotification_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (set_tcb_obj_ref tcb_bound_notification_update t ntfn) (setBoundNotification ntfn t)"
  apply (simp add: setBoundNotification_def)
  apply (rule set_tcb_obj_ref_corres; simp add: tcb_relation_def)
  done

crunches rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps)

global_interpretation rescheduleRequired: typ_at_all_props' "rescheduleRequired"
  by typ_at_props'

global_interpretation tcbSchedDequeue: typ_at_all_props' "tcbSchedDequeue thread"
  by typ_at_props'

global_interpretation threadSet: typ_at_all_props' "threadSet f p"
  by typ_at_props'

global_interpretation setThreadState: typ_at_all_props' "setThreadState st p"
  by typ_at_props'

global_interpretation setBoundNotification: typ_at_all_props' "setBoundNotification v p"
  by typ_at_props'

global_interpretation scheduleTCB: typ_at_all_props' "scheduleTCB tcbPtr"
  by typ_at_props'

lemma sts'_valid_mdb'[wp]:
  "setThreadState st t \<lbrace>valid_mdb'\<rbrace>"
  by (wpsimp simp: valid_mdb'_def)

crunches rescheduleRequired, removeFromBitmap, scheduleTCB
  for valid_objs'[wp]: valid_objs'
  (simp: unless_def crunch_simps)


lemma tcbSchedDequeue_valid_objs' [wp]: "\<lbrace> valid_objs' \<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_objs' \<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wp threadSet_valid_objs')
        apply (clarsimp simp add: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
        apply wp
       apply (simp add: if_apply_def2)
       apply (wp hoare_drop_imps)
       apply (wp | simp cong: if_cong add: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def if_apply_def2)+
  done

lemma sts_valid_objs':
  "\<lbrace>valid_objs' and valid_tcb_state' st\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: setThreadState_def wp: threadSet_valid_objs')
  by (simp add: valid_tcb'_def tcb_cte_cases_def objBits_simps')

lemma sbn_valid_objs':
  "\<lbrace>valid_objs' and valid_bound_ntfn' ntfn\<rbrace>
  setBoundNotification ntfn t
  \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_objs')
     apply (simp add: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

crunches setBoundNotification
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and st_tcb_at'[wp]: "st_tcb_at' P p"
  and valid_replies' [wp]: valid_replies'
  (wp: valid_replies'_lift threadSet_pred_tcb_no_state)

lemma ssa_wp[wp]:
  "\<lbrace>\<lambda>s. P (s \<lparr>ksSchedulerAction := sa\<rparr>)\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: setSchedulerAction_def)

crunches removeFromBitmap
  for pspace_aligned'[wp]: "pspace_aligned'"
  and pspace_distinct'[wp]: "pspace_distinct'"
  and pspace_bounded'[wp]: "pspace_bounded'"
  and no_0_obj[wp]: "no_0_obj'"
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and valid_replies'[wp]: "valid_replies'"
  (wp: valid_replies'_lift)

crunches rescheduleRequired, tcbSchedDequeue, scheduleTCB
  for st_tcb_at'[wp]: "st_tcb_at' P p"
  and valid_replies' [wp]: valid_replies'
  (wp: crunch_wps threadSet_pred_tcb_no_state valid_replies'_lift ignore: threadSet)

crunches rescheduleRequired, tcbSchedDequeue, setThreadState
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and bounded'[wp]: pspace_bounded'
  and canonical'[wp]: pspace_canonical'
  and no_0_obj'[wp]: no_0_obj'
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps)

lemma threadSet_valid_replies':
  "\<lbrace>\<lambda>s. valid_replies' s  \<and>
        (\<forall>tcb. ko_at' tcb t s
           \<longrightarrow> (\<forall>rptr. tcbState tcb = BlockedOnReply (Some rptr)
                       \<longrightarrow> is_reply_linked rptr s \<longrightarrow> tcbState (f tcb) = BlockedOnReply (Some rptr)))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (clarsimp simp: threadSet_def)
  apply (wpsimp wp: setObject_tcb_valid_replies' getObject_tcb_wp)
  by (force simp: pred_tcb_at'_def obj_at'_def)

lemma sts'_valid_replies':
  "\<lbrace>\<lambda>s. valid_replies' s \<and>
        (\<forall>rptr. st_tcb_at' ((=) (BlockedOnReply (Some rptr))) t s
                  \<longrightarrow> is_reply_linked rptr s \<longrightarrow> st = BlockedOnReply (Some rptr))\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_valid_replies')
  by (auto simp: pred_tcb_at'_def obj_at'_def opt_map_def)

lemma sts'_valid_pspace'_inv[wp]:
  "\<lbrace> valid_pspace' and tcb_at' t and valid_tcb_state' st
     and (\<lambda>s. \<forall>rptr. st_tcb_at' ((=) (BlockedOnReply (Some rptr))) t s
                      \<longrightarrow> st = BlockedOnReply (Some rptr) \<or> \<not> is_reply_linked rptr s)\<rbrace>
   setThreadState st t
   \<lbrace> \<lambda>rv. valid_pspace' \<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wpsimp wp: sts_valid_objs' sts'_valid_replies')
  by (auto simp: opt_map_def)

abbreviation is_replyState :: "thread_state \<Rightarrow> bool" where
  "is_replyState st \<equiv> is_BlockedOnReply st \<or> is_BlockedOnReceive st"

lemma setObject_tcb_valid_replies'_except_Blocked:
  "\<lbrace>\<lambda>s. valid_replies'_except {rptr} s \<and> replyTCBs_of s rptr = Some t
        \<and> st_tcb_at' (\<lambda>st. is_replyState st \<longrightarrow> replyObject st = None) t s
        \<and> (tcbState v = BlockedOnReply (Some rptr))\<rbrace>
   setObject t (v :: tcb)
   \<lbrace>\<lambda>rv. valid_replies'\<rbrace>"
  unfolding valid_replies'_def valid_replies'_except_def
  apply (subst pred_tcb_at'_eq_commute)+
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_ex_lift
                    set_tcb'.setObject_obj_at'_strongest
                simp: pred_tcb_at'_def simp_del: imp_disjL)
  apply (rename_tac rptr' rp)
  apply (case_tac "rptr' = rptr")
   apply (fastforce simp: opt_map_def)
  apply (drule_tac x=rptr' in spec, drule mp, clarsimp)
  apply (auto simp: opt_map_def obj_at'_def split: option.splits)
  done

lemma threadSet_valid_replies'_except_Blocked:
  "\<lbrace>\<lambda>s. valid_replies'_except {rptr} s \<and> replyTCBs_of s rptr = Some t
        \<and> st_tcb_at' (\<lambda>st. is_replyState st \<longrightarrow> replyObject st = None) t s
        \<and> (\<forall>tcb. tcbState (f tcb) = BlockedOnReply (Some rptr))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (clarsimp simp: threadSet_def)
  apply (wpsimp wp: setObject_tcb_valid_replies'_except_Blocked[where rptr=rptr] getObject_tcb_wp)
  by (auto simp: pred_tcb_at'_def obj_at'_def)

lemma sts'_valid_replies'_except_Blocked:
  "\<lbrace>\<lambda>s. valid_replies'_except {rptr} s \<and> replyTCBs_of s rptr = Some t
        \<and> st_tcb_at' (\<lambda>st. is_replyState st \<longrightarrow> replyObject st = None) t s\<rbrace>
   setThreadState (BlockedOnReply (Some rptr)) t
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_valid_replies'_except_Blocked)
  by (auto simp: pred_tcb_at'_def obj_at'_def opt_map_def)

crunch ct[wp]: setQueue "\<lambda>s. P (ksCurThread s)"

crunch cur_domain[wp]: setQueue "\<lambda>s. P (ksCurDomain s)"

crunch ct'[wp]: addToBitmap "\<lambda>s. P (ksCurThread s)"
crunch ct'[wp]: removeFromBitmap "\<lambda>s. P (ksCurThread s)"

lemma setQueue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setQueue d p xs \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  apply (simp add: setQueue_def tcb_in_cur_domain'_def)
  apply wp
  apply (simp add: ps_clear_def obj_at'_def)
  done

lemma sbn'_valid_pspace'_inv[wp]:
  "\<lbrace> valid_pspace' and tcb_at' t and valid_bound_ntfn' ntfn \<rbrace>
  setBoundNotification ntfn t
  \<lbrace> \<lambda>rv. valid_pspace' \<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sbn_valid_objs')
   apply (simp add: setBoundNotification_def threadSet_def bind_assoc valid_mdb'_def)
   apply (wp getObject_obj_at_tcb)
  apply (clarsimp simp: valid_mdb'_def)
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply (simp add: tcb_cte_cases_def cteSizeBits_def)
  done

crunch pred_tcb_at'[wp]: setQueue "\<lambda>s. P (pred_tcb_at' proj P' t s)"

lemma setQueue_sch_act:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  setQueue d p xs
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift)

lemma setQueue_valid_bitmapQ_except[wp]:
  "\<lbrace> valid_bitmapQ_except d p \<rbrace>
  setQueue d p ts
  \<lbrace>\<lambda>_. valid_bitmapQ_except d p \<rbrace>"
  unfolding setQueue_def bitmapQ_defs
  by (wp, clarsimp simp: bitmapQ_def)

lemma setQueue_valid_bitmapQ: (* enqueue only *)
  "\<lbrace> valid_bitmapQ and (\<lambda>s. (ksReadyQueues s (d, p) = []) = (ts = [])) \<rbrace>
  setQueue d p ts
  \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  unfolding setQueue_def bitmapQ_defs
  by (wp, clarsimp simp: bitmapQ_def)

lemma setQueue_valid_queues':
  "\<lbrace>valid_queues' and (\<lambda>s. \<forall>t. obj_at' (inQ d p) t s \<longrightarrow> t \<in> set ts)\<rbrace>
    setQueue d p ts \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp | simp add: valid_queues'_def setQueue_def)+

lemma setQueue_cur:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setQueue d p ts \<lbrace>\<lambda>rv s. cur_tcb' s\<rbrace>"
  unfolding setQueue_def cur_tcb'_def
  by (wp, clarsimp)

lemma ssa_sch_act[wp]:
  "\<lbrace>sch_act_wf sa\<rbrace> setSchedulerAction sa
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (simp add: setSchedulerAction_def | wp)+

lemma threadSet_runnable_sch_act:
  "(\<And>tcb. runnable' (tcbState (F tcb)) \<and> tcbDomain (F tcb) = tcbDomain tcb \<and> tcbPriority (F tcb) = tcbPriority tcb) \<Longrightarrow>
   \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    threadSet F t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule_tac P1="(=) (ksSchedulerAction s)"
                in use_valid [OF _ threadSet.ksSchedulerAction],
         rule refl)
  apply (frule_tac P1="(=) (ksCurThread s)"
                in use_valid [OF _ threadSet.ct],
         rule refl)
  apply (frule_tac P1="(=) (ksCurDomain s)"
                in use_valid [OF _ threadSet.cur_domain],
         rule refl)
  apply (case_tac "ksSchedulerAction b",
         simp_all add: sch_act_simple_def ct_in_state'_def pred_tcb_at'_def)
   apply (drule_tac t'1="ksCurThread s"
                and P1="activatable' \<circ> tcbState"
                 in use_valid [OF _ threadSet_obj_at'_really_strongest])
    apply (clarsimp elim!: obj_at'_weakenE)
   apply (simp add: o_def)
  apply (rename_tac word)
  apply (rule conjI)
   apply (frule_tac t'1=word
               and P1="runnable' \<circ> tcbState"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
    apply (clarsimp elim!: obj_at'_weakenE, clarsimp simp: obj_at'_def)
  apply (simp add: tcb_in_cur_domain'_def)
  apply (frule_tac t'1=word
               and P1="\<lambda>tcb. ksCurDomain b = tcbDomain tcb"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
   apply (clarsimp simp: o_def tcb_in_cur_domain'_def)
  apply clarsimp
  done

lemma threadSet_pred_tcb_at_state:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow>
         (p = t \<longrightarrow> obj_at' (\<lambda>tcb. P (Q (proj (tcb_to_itcb' (f tcb))))) t s) \<and>
         (p \<noteq> t \<longrightarrow>  P (pred_tcb_at' proj Q p s))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_ s. P (pred_tcb_at' proj Q p s)\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: set_tcb'.setObject_wp set_tcb'.getObject_wp)
  apply (case_tac "p = t"; clarsimp)
   apply (subst pred_tcb_at'_set_obj'_iff, assumption)
   apply (clarsimp simp: obj_at'_def)
  apply (subst pred_tcb_at'_set_obj'_distinct, assumption, assumption)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadSet_tcbDomain_triv':
  "\<lbrace>tcb_in_cur_domain' t' and K (t \<noteq> t')\<rbrace> threadSet f t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_assume_pre)
  apply simp
  apply (rule_tac f="ksCurDomain" in hoare_lift_Pf)
   apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | simp)+
  done

lemma threadSet_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> sch_act_not t s \<and>
        (ksCurThread s = t \<longrightarrow> \<not>(\<forall>tcb. activatable' (tcbState (F tcb))) \<longrightarrow>
                              ksSchedulerAction s \<noteq> ResumeCurrentThread) \<rbrace>
  threadSet F t
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (rule hoare_lift_Pf2 [where f=ksSchedulerAction])
   prefer 2
   apply wp
  apply (case_tac x, simp_all)
   apply (simp add: ct_in_state'_def)
   apply (rule hoare_lift_Pf2 [where f=ksCurThread])
    prefer 2
    apply wp[1]
   apply (wp threadSet_pred_tcb_at_state)
   apply clarsimp
  apply wp
  apply (clarsimp)
  apply (wp threadSet_pred_tcb_at_state threadSet_tcbDomain_triv' | clarsimp)+
  done

definition isScActive :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "isScActive scPtr s' \<equiv> pred_map (\<lambda>sc. 0 < scRefillMax sc) (scs_of' s') scPtr"

abbreviation ct_isSchedulable :: "kernel_state \<Rightarrow> bool" where
  "ct_isSchedulable \<equiv> ct_active'
                       and (\<lambda>s. pred_map (\<lambda>tcb. \<not> tcbInReleaseQueue tcb) (tcbs_of' s) (ksCurThread s))
                       and (\<lambda>s. pred_map (\<lambda>scPtr. isScActive scPtr s) (tcbSCs_of s) (ksCurThread s))"

definition isSchedulable_bool :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "isSchedulable_bool tcbPtr s'
    \<equiv> pred_map (\<lambda>tcb. runnable' (tcbState tcb) \<and> \<not>(tcbInReleaseQueue tcb)) (tcbs_of' s') tcbPtr
      \<and> pred_map (\<lambda>scPtr. isScActive scPtr s') (tcbSCs_of s') tcbPtr"

lemma isSchedulable_wp:
  "\<lbrace>\<lambda>s. \<forall>t. isSchedulable_bool tcbPtr s = t \<and> tcb_at' tcbPtr s \<longrightarrow> P t s\<rbrace> isSchedulable tcbPtr \<lbrace>P\<rbrace>"
  apply (clarsimp simp: isSchedulable_def)
  apply (rule hoare_seq_ext[OF _ getObject_tcb_sp])
  apply (wpsimp simp: hoare_vcg_if_lift2 obj_at_def is_tcb inReleaseQueue_def wp: threadGet_wp)
  apply (rule conjI)
   apply (fastforce simp: isSchedulable_bool_def isScActive_def obj_at'_def
                          pred_tcb_at'_def pred_map_simps in_opt_map_eq
                   split: option.splits)
  apply (clarsimp simp: isSchedulable_bool_def isScActive_def obj_at'_def
                         pred_tcb_at'_def pred_map_simps in_opt_map_eq vs_all_heap_simps
                 split: option.splits)
  by argo

lemma isSchedulable_sp:
  "\<lbrace>P\<rbrace> isSchedulable tcbPtr \<lbrace>\<lambda>rv. (\<lambda>s. rv = isSchedulable_bool tcbPtr s) and P\<rbrace>"
  by (wpsimp wp: isSchedulable_wp)
lemma rescheduleRequired_sch_act'[wp]:
  "\<lbrace>\<top>\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wpsimp simp: rescheduleRequired_def wp: isSchedulable_wp)

lemma rescheduleRequired_weak_sch_act_wf[wp]:
  "\<lbrace>\<top>\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: rescheduleRequired_def setSchedulerAction_def)
  apply (wp hoare_post_taut | simp add: weak_sch_act_wf_def)+
  done

lemma sts_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s
        \<and> (ksSchedulerAction s = SwitchToThread t \<longrightarrow> runnable' st)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding setThreadState_def scheduleTCB_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift hoare_vcg_all_lift
                    threadSet_pred_tcb_at_state threadSet_tcbDomain_triv
                    isSchedulable_inv
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. rv" for x]
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. \<not>rv" for x]
              simp: weak_sch_act_wf_def)
  done

lemma threadSet_isSchedulable_bool_nochange:
  "\<lbrace>\<lambda>s. runnable' st \<and> isSchedulable_bool t s\<rbrace>
   threadSet (tcbState_update (\<lambda>_. st)) t
   \<lbrace>\<lambda>_. isSchedulable_bool t\<rbrace>"
  unfolding isSchedulable_bool_def threadSet_def
  apply (rule hoare_seq_ext[OF _ getObject_tcb_sp])
  apply (wpsimp wp: setObject_tcb_wp simp: pred_map_def obj_at'_def opt_map_def)
  apply (fastforce simp: pred_map_def isScActive_def)
  done

lemma threadSet_isSchedulable_bool:
  "\<lbrace>\<lambda>s. runnable' st
      \<and> pred_map (\<lambda>tcb. \<not>(tcbInReleaseQueue tcb)) (tcbs_of' s) t
      \<and> pred_map (\<lambda>scPtr. isScActive scPtr s) (tcbSCs_of s) t\<rbrace>
   threadSet (tcbState_update (\<lambda>_. st)) t
   \<lbrace>\<lambda>_. isSchedulable_bool t\<rbrace>"
  unfolding isSchedulable_bool_def threadSet_def
  apply (rule hoare_seq_ext[OF _ getObject_tcb_sp])
  apply (wpsimp wp: setObject_tcb_wp simp: pred_map_def obj_at'_def opt_map_def)
  apply (fastforce simp: pred_map_def isScActive_def)
  done

lemma setObject_queued_pred_tcb_at'[wp]:
  "\<lbrace>pred_tcb_at' proj P t' and obj_at' ((=) tcb) t\<rbrace>
    setObject t (tcbQueued_update f tcb)
   \<lbrace>\<lambda>_. pred_tcb_at' proj P t'\<rbrace>"
  apply (simp add: pred_tcb_at'_def)
  apply (rule hoare_pre)
  apply (wp setObject_tcb_strongest)
  apply (clarsimp simp: obj_at'_def tcb_to_itcb'_def)
  done

lemma setObject_queued_ct_activatable'[wp]:
  "\<lbrace>ct_in_state' activatable' and obj_at' ((=) tcb) t\<rbrace>
    setObject t (tcbQueued_update f tcb)
   \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  apply (clarsimp simp: ct_in_state'_def pred_tcb_at'_def)
  apply (rule hoare_pre)
   apply (wps setObject_ct_inv)
   apply (wp setObject_tcb_strongest)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadSet_queued_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    threadSet (tcbQueued_update f) t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  including no_pre
  apply (simp add: sch_act_wf_cases
              split: scheduler_action.split)
  apply (wp hoare_vcg_conj_lift)
   apply (simp add: threadSet_def)
   apply (wp static_imp_wp)
    apply wps
    apply (wp static_imp_wp getObject_tcb_wp)+
   apply (clarsimp simp: obj_at'_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_conj_lift hoare_convert_imp)+
   apply (simp add: threadSet_def)
   apply (wp getObject_tcb_wp)
   apply (clarsimp simp: obj_at'_def)
  apply (wp tcb_in_cur_domain'_lift | simp add: obj_at'_def)+
  done

lemma tcbSchedEnqueue_pred_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s) \<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def when_def unless_def)
  apply (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+
  done

lemma tcbSchedDequeue_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding tcbSchedDequeue_def
  by (wp setQueue_sch_act | wp sch_act_wf_lift | simp add: if_apply_def2)+

lemma scheduleTCB_sch_act_wf:
  "\<lbrace>\<lambda>s. \<not>(t = ksCurThread s \<and> ksSchedulerAction s = ResumeCurrentThread
        \<and> \<not> pred_map (\<lambda>tcb. runnable' (tcbState tcb)) (tcbs_of' s) t)
        \<longrightarrow> (sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   scheduleTCB t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: scheduleTCB_def)
  by (wpsimp wp: isSchedulable_wp  simp: isSchedulable_bool_def pred_map_def opt_map_Some)

lemma sts_sch_act':
  "\<lbrace>\<lambda>s. (\<not> runnable' st \<longrightarrow> sch_act_not t s) \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
  setThreadState st t  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp scheduleTCB_sch_act_wf)
   prefer 2
   apply assumption
  apply (case_tac "runnable' st")
   apply (wpsimp wp: hoare_drop_imps threadSet_runnable_sch_act)
  apply (rule_tac Q="\<lambda>rv s. st_tcb_at' (Not \<circ> runnable') t s \<and>
                            (ksCurThread s \<noteq> t \<or> ksSchedulerAction s \<noteq> ResumeCurrentThread \<longrightarrow>
                               sch_act_wf (ksSchedulerAction s) s)"
           in hoare_post_imp)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def pred_map_def)
  apply (simp only: imp_conv_disj)
  apply (wpsimp wp: threadSet_pred_tcb_at_state threadSet_sch_act_wf hoare_vcg_disj_lift)
  done

(* FIXME: sts_sch_act' (above) is stronger, and should be the wp rule. VER-1366 *)
lemma sts_sch_act[wp]:
  "\<lbrace>\<lambda>s. (\<not> runnable' st \<longrightarrow> sch_act_simple s) \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp scheduleTCB_sch_act_wf)
   prefer 2
   apply assumption
  apply (case_tac "runnable' st")
   apply (wpsimp wp: hoare_drop_imps threadSet_runnable_sch_act)
  apply (rule_tac Q="\<lambda>rv s. st_tcb_at' (Not \<circ> runnable') t s \<and>
                            (ksCurThread s \<noteq> t \<or> ksSchedulerAction s \<noteq> ResumeCurrentThread \<longrightarrow>
                               sch_act_wf (ksSchedulerAction s) s)"
           in hoare_post_imp)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def pred_map_def)
  apply (simp only: imp_conv_disj)
  apply (wpsimp wp: threadSet_pred_tcb_at_state threadSet_sch_act_wf hoare_vcg_disj_lift)
  apply (fastforce simp: sch_act_simple_def)
  done

lemma sbn_sch_act':
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  setBoundNotification ntfn t  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_sch_act | simp)+
  done

lemma ssa_sch_act_simple[wp]:
  "sa = ResumeCurrentThread \<or> sa = ChooseNewThread \<Longrightarrow>
   \<lbrace>\<top>\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  unfolding setSchedulerAction_def sch_act_simple_def
  by (wp | simp)+

lemma sch_act_simple_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>) \<Longrightarrow>
   \<lbrace>sch_act_simple\<rbrace> f \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  by (simp add: sch_act_simple_def) assumption

lemma rescheduleRequired_sch_act_simple_True[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  by (wpsimp simp: rescheduleRequired_def)

crunches scheduleTCB
  for sch_act_simple[wp]: sch_act_simple
  (wp: crunch_wps hoare_vcg_if_lift2)

crunch no_sa[wp]: tcbSchedDequeue "\<lambda>s. P (ksSchedulerAction s)"

lemma sts_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  by (wpsimp simp: sch_act_simple_def)

lemma setQueue_after:
  "(setQueue d p q >>= (\<lambda>rv. threadSet f t)) =
   (threadSet f t >>= (\<lambda>rv. setQueue d p q))"
  apply (simp add: setQueue_def)
  apply (rule oblivious_modify_swap)
  apply (simp add: threadSet_def getObject_def setObject_def obind_def
                   loadObject_default_def gets_the_def omonad_defs read_magnitudeCheck_assert
                   split_def projectKO_def alignCheck_assert readObject_def
                   magnitudeCheck_assert updateObject_default_def
            split: option.splits if_splits)
  apply (intro oblivious_bind, simp_all split: option.splits)
  done

lemma tcbSchedEnqueue_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (simp add: tcbSchedEnqueue_def unless_def)
     (wp setQueue_sch_act | wp sch_act_wf_lift  | clarsimp)+

lemma tcbSchedEnqueue_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp setQueue_sch_act threadSet_weak_sch_act_wf | clarsimp)+
  done

lemma threadGet_const:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> obj_at' (P \<circ> f) t s\<rbrace> threadGet f t \<lbrace>\<lambda>rv s. P (rv)\<rbrace>"
  apply (simp add: threadGet_getObject)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

schematic_goal l2BitmapSize_def': (* arch specific consequence *)
  "l2BitmapSize = numeral ?X"
  by (simp add: l2BitmapSize_def wordBits_def word_size numPriorities_def)

lemma prioToL1Index_size [simp]:
  "prioToL1Index w < l2BitmapSize"
  unfolding prioToL1Index_def wordRadix_def l2BitmapSize_def'
  by (fastforce simp: shiftr_div_2n' nat_divide_less_eq
                intro: order_less_le_trans[OF unat_lt2p])

lemma prioToL1Index_max:
  "prioToL1Index p < 2 ^ wordRadix"
  unfolding prioToL1Index_def wordRadix_def
  by (insert unat_lt2p[where x=p], simp add: shiftr_div_2n')

lemma prioToL1Index_bit_set:
  "((2 :: machine_word) ^ prioToL1Index p) !! prioToL1Index p"
  using l2BitmapSize_def'
  by (fastforce simp: nth_w2p_same intro: order_less_le_trans[OF prioToL1Index_size])

lemma prioL2Index_bit_set:
  fixes p :: priority
  shows "((2::machine_word) ^ unat (ucast p && (mask wordRadix :: machine_word))) !! unat (p && mask wordRadix)"
  apply (simp add: nth_w2p wordRadix_def ucast_and_mask[symmetric] unat_ucast_upcast is_up)
  apply (rule unat_less_helper)
  apply (insert and_mask_less'[where w=p and n=wordRadix], simp add: wordRadix_def)
  done

lemma addToBitmap_bitmapQ:
  "\<lbrace> \<lambda>s. True \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. bitmapQ d p \<rbrace>"
  unfolding addToBitmap_def
             modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
             getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def
  by (wpsimp simp: bitmap_fun_defs bitmapQ_def prioToL1Index_bit_set prioL2Index_bit_set
             simp_del: bit_exp_iff)

lemma addToBitmap_valid_queues_no_bitmap_except:
" \<lbrace> valid_queues_no_bitmap_except t \<rbrace>
     addToBitmap d p
  \<lbrace>\<lambda>_. valid_queues_no_bitmap_except t \<rbrace>"
  unfolding addToBitmap_def modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
             getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def valid_queues_no_bitmap_except_def
  by (wp, clarsimp)

crunch norq[wp]: addToBitmap "\<lambda>s. P (ksReadyQueues s)"
  (wp: updateObject_cte_inv hoare_drop_imps)
crunch norq[wp]: removeFromBitmap "\<lambda>s. P (ksReadyQueues s)"
  (wp: updateObject_cte_inv hoare_drop_imps)

lemma prioToL1Index_lt:
  "2 ^ wordRadix \<le> x \<Longrightarrow> prioToL1Index p < x"
  unfolding prioToL1Index_def wordRadix_def
  by (insert unat_lt2p[where x=p], simp add: shiftr_div_2n')

lemma prioToL1Index_bits_low_high_eq:
  "\<lbrakk> pa \<noteq> p; prioToL1Index pa = prioToL1Index (p::priority) \<rbrakk>
   \<Longrightarrow>  unat (pa && mask wordRadix) \<noteq> unat (p && mask wordRadix)"
  unfolding prioToL1Index_def
  by (fastforce simp: nth_w2p wordRadix_def is_up bits_low_high_eq)

lemma prioToL1Index_bit_not_set:
  "\<not> (~~ ((2 :: machine_word) ^ prioToL1Index p)) !! prioToL1Index p"
  apply (subst word_ops_nth_size, simp_all add: prioToL1Index_bit_set del: bit_exp_iff)
  apply (fastforce simp: prioToL1Index_def wordRadix_def word_size
                  intro: order_less_le_trans[OF word_shiftr_lt])
  done

lemma prioToL1Index_complement_nth_w2p:
  fixes p pa :: priority
  shows "(~~ ((2 :: machine_word) ^ prioToL1Index p)) !! prioToL1Index p'
          = (prioToL1Index p \<noteq> prioToL1Index p')"
  by (fastforce simp: complement_nth_w2p prioToL1Index_lt wordRadix_def word_size)+

lemma valid_bitmapQ_exceptE:
  "\<lbrakk> valid_bitmapQ_except d' p' s ; d \<noteq> d' \<or> p \<noteq> p' \<rbrakk>
   \<Longrightarrow> bitmapQ d p s = (ksReadyQueues s (d, p) \<noteq> [])"
   unfolding valid_bitmapQ_except_def
   by blast

lemma invertL1Index_eq_cancelD:
  "\<lbrakk>  invertL1Index i = invertL1Index j ; i < l2BitmapSize ; j < l2BitmapSize \<rbrakk>
   \<Longrightarrow> i = j"
   by (simp add: invertL1Index_def l2BitmapSize_def')

lemma invertL1Index_eq_cancel:
  "\<lbrakk> i < l2BitmapSize ; j < l2BitmapSize \<rbrakk>
   \<Longrightarrow> (invertL1Index i = invertL1Index j) = (i = j)"
   by (rule iffI, simp_all add: invertL1Index_eq_cancelD)

lemma removeFromBitmap_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> removeFromBitmap d p \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmap_fun_defs
  apply (wp | simp add: bitmap_fun_defs bitmapQ_no_L1_orphans_def)+
  apply (fastforce simp: invertL1Index_eq_cancel prioToL1Index_bit_not_set
                         prioToL1Index_complement_nth_w2p)
  done

lemma removeFromBitmap_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans \<rbrace>
   removeFromBitmap d p
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmap_fun_defs
  apply (wp, clarsimp simp: bitmap_fun_defs bitmapQ_no_L2_orphans_def)+
  apply (rule conjI, clarsimp)
   apply (clarsimp simp: complement_nth_w2p l2BitmapSize_def')
  apply clarsimp
  apply metis
  done

lemma removeFromBitmap_valid_bitmapQ_except:
  "\<lbrace> valid_bitmapQ_except d p \<rbrace>
   removeFromBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ_except d p \<rbrace>"
proof -
  have unat_ucast_mask[simp]:
   "\<And>x. unat ((ucast (p::priority) :: machine_word) && mask x) = unat (p && mask x)"
   by (simp add: ucast_and_mask[symmetric] unat_ucast_upcast is_up)

  note bit_exp_iff[simp del] bit_not_iff[simp del] bit_not_exp_iff[simp del]
  show ?thesis
  unfolding removeFromBitmap_def
  apply (simp add: let_into_return[symmetric])
  unfolding bitmap_fun_defs when_def
  apply wp
  apply clarsimp
  apply (rule conjI)
   (* after clearing bit in L2, all bits in L2 field are clear *)
   apply clarsimp
   apply (subst valid_bitmapQ_except_def, clarsimp)+
   apply (clarsimp simp: bitmapQ_def)
   apply (rule conjI; clarsimp)
    apply (rename_tac p')
    apply (rule conjI; clarsimp simp: invertL1Index_eq_cancel)
     apply (drule_tac p=p' in valid_bitmapQ_exceptE[where d=d], clarsimp)
     apply (clarsimp simp: bitmapQ_def)
     apply (drule_tac n'="unat (p' && mask wordRadix)" in no_other_bits_set)
        apply (erule (1) prioToL1Index_bits_low_high_eq)
       apply (rule order_less_le_trans[OF word_unat_mask_lt])
        apply ((simp add: wordRadix_def' word_size)+)[2]
      apply (rule order_less_le_trans[OF word_unat_mask_lt])
       apply ((simp add: wordRadix_def' word_size)+)[3]
    apply (drule_tac p=p' and d=d in valid_bitmapQ_exceptE, simp)
    apply (clarsimp simp: bitmapQ_def prioToL1Index_complement_nth_w2p)
   apply (drule_tac p=pa and d=da in valid_bitmapQ_exceptE, simp)
   apply (clarsimp simp: bitmapQ_def prioToL1Index_complement_nth_w2p)
  (* after clearing bit in L2, some bits in L2 field are still set *)
  apply clarsimp
  apply (subst valid_bitmapQ_except_def, clarsimp)+
  apply (clarsimp simp: bitmapQ_def invertL1Index_eq_cancel)
  apply (rule conjI; clarsimp)
   apply (frule (1) prioToL1Index_bits_low_high_eq)
   apply (drule_tac d=d and p=pa in valid_bitmapQ_exceptE, simp)
   apply (clarsimp simp: bitmapQ_def)
   apply (subst complement_nth_w2p)
    apply (rule order_less_le_trans[OF word_unat_mask_lt])
     apply ((simp add: wordRadix_def' word_size)+)[3]
  apply (clarsimp simp: valid_bitmapQ_except_def bitmapQ_def)
  done
qed

lemma addToBitmap_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmap_fun_defs bitmapQ_defs
  using word_unat_mask_lt[where w=p and m=wordRadix]
  apply wp
  apply (clarsimp simp: word_or_zero prioToL1Index_bit_set ucast_and_mask[symmetric]
                        unat_ucast_upcast is_up wordRadix_def' word_size nth_w2p
                        wordBits_def numPriorities_def)
  done

lemma addToBitmap_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmap_fun_defs bitmapQ_defs
  supply bit_exp_iff[simp del]
  apply wp
  apply clarsimp
  apply (fastforce simp: invertL1Index_eq_cancel prioToL1Index_bit_set)
  done

lemma addToBitmap_valid_bitmapQ_except:
  "\<lbrace> valid_bitmapQ_except d p and bitmapQ_no_L2_orphans \<rbrace>
     addToBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ_except d p \<rbrace>"
  unfolding bitmap_fun_defs bitmapQ_defs
  apply wp
  apply (clarsimp simp: bitmapQ_def invertL1Index_eq_cancel
                        ucast_and_mask[symmetric] unat_ucast_upcast is_up nth_w2p)
  apply (fastforce simp: priority_mask_wordRadix_size[simplified wordBits_def']
                   dest: prioToL1Index_bits_low_high_eq)
  done

lemma addToBitmap_valid_bitmapQ:
" \<lbrace> valid_bitmapQ_except d p and bitmapQ_no_L2_orphans and
    (\<lambda>s. ksReadyQueues s (d,p) \<noteq> []) \<rbrace>
     addToBitmap d p
  \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
proof -
  have "\<lbrace> valid_bitmapQ_except d p and bitmapQ_no_L2_orphans and
            (\<lambda>s. ksReadyQueues s (d,p) \<noteq> []) \<rbrace>
         addToBitmap d p
         \<lbrace>\<lambda>_. valid_bitmapQ_except d p and
              bitmapQ_no_L2_orphans and (\<lambda>s. bitmapQ d p s \<and> ksReadyQueues s (d,p) \<noteq> []) \<rbrace>"
  by (wp addToBitmap_valid_queues_no_bitmap_except addToBitmap_valid_bitmapQ_except
            addToBitmap_bitmapQ_no_L2_orphans addToBitmap_bitmapQ; simp)

  thus ?thesis
    by - (erule hoare_strengthen_post; fastforce elim: valid_bitmap_valid_bitmapQ_exceptE)
qed

lemma threadGet_const_tcb_at:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> obj_at' (P s \<circ> f) t s\<rbrace> threadGet f t \<lbrace>\<lambda>rv s. P s rv \<rbrace>"
  apply (simp add: threadGet_getObject)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadGet_const_tcb_at_imp_lift:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> obj_at' (P s \<circ> f) t s \<longrightarrow>  obj_at' (Q s \<circ> f) t s \<rbrace>
   threadGet f t
   \<lbrace>\<lambda>rv s. P s rv \<longrightarrow> Q s rv \<rbrace>"
  apply (simp add: threadGet_getObject)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma valid_queues_no_bitmap_objD:
  "\<lbrakk> valid_queues_no_bitmap s; t \<in> set (ksReadyQueues s (d, p))\<rbrakk>
   \<Longrightarrow> obj_at' (inQ d p) t s"
   unfolding valid_queues_no_bitmap_def
   by metis

lemma setQueue_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace>
       setQueue d p ts
   \<lbrace>\<lambda>rv. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding setQueue_def bitmapQ_no_L1_orphans_def null_def
  by (wp, auto)

lemma setQueue_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace>
       setQueue d p ts
   \<lbrace>\<lambda>rv. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding setQueue_def bitmapQ_no_L2_orphans_def null_def
  by (wp, auto)

lemma setQueue_sets_queue[wp]:
  "\<And>d p ts P. \<lbrace> \<lambda>s. P ts \<rbrace> setQueue d p ts \<lbrace>\<lambda>rv s. P (ksReadyQueues s (d, p)) \<rbrace>"
  unfolding setQueue_def
  by (wp, simp)

crunches setQueue
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

lemma tcbSchedEnqueueOrAppend_valid_queues:
  (* f is either (t#ts) or (ts @ [t]), so we define its properties generally *)
  assumes f_set[simp]: "\<And>ts. t \<in> set (f ts)"
  assumes f_set_insert[simp]: "\<And>ts. set (f ts) = insert t (set ts)"
  assumes f_not_empty[simp]: "\<And>ts. f ts \<noteq> []"
  shows "\<lbrace>Invariants_H.valid_queues and valid_tcbs' \<rbrace>
    do queued \<leftarrow> threadGet tcbQueued t;
       unless queued $
       do tdom \<leftarrow> threadGet tcbDomain t;
          prio \<leftarrow> threadGet tcbPriority t;
          queue \<leftarrow> getQueue tdom prio;
          setQueue tdom prio $ f queue;
          when (null queue) $ addToBitmap tdom prio;
          threadSet (tcbQueued_update (\<lambda>_. True)) t
       od
    od
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
proof -

  define could_run where "could_run ==
    \<lambda>d p t. obj_at' (\<lambda>tcb. inQ d p (tcbQueued_update (\<lambda>_. True) tcb)) t"

  have addToBitmap_could_run:
  "\<And>d p. \<lbrace>\<lambda>s. \<forall>d p. t \<in> set (ksReadyQueues s (d, p)) \<longrightarrow> could_run d p t s\<rbrace>
         addToBitmap d p
         \<lbrace>\<lambda>_ s. \<forall>d p. t \<in> set (ksReadyQueues s (d, p)) \<longrightarrow> could_run d p t s\<rbrace>"
    unfolding bitmap_fun_defs
    by (wp, clarsimp simp: could_run_def)

  have setQueue_valid_queues_no_bitmap_except:
    "\<And>d p ts.
     \<lbrace> valid_queues_no_bitmap_except t and
       (\<lambda>s. ksReadyQueues s (d, p) = ts \<and> p \<le> maxPriority \<and> d \<le> maxDomain \<and> t \<notin> set ts) \<rbrace>
         setQueue d p (f ts)
     \<lbrace>\<lambda>rv. valid_queues_no_bitmap_except t\<rbrace>"
    unfolding setQueue_def valid_queues_no_bitmap_except_def null_def
    by (wp, auto)

  have threadSet_valid_queues_could_run:
   "\<And>f. \<lbrace> valid_queues_no_bitmap_except t and
          (\<lambda>s. \<forall>d p. t \<in> set (ksReadyQueues s (d,p)) \<longrightarrow> could_run d p t s) and
          valid_bitmapQ and bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans \<rbrace>
            threadSet (tcbQueued_update (\<lambda>_. True)) t
         \<lbrace>\<lambda>rv. Invariants_H.valid_queues \<rbrace>"
    unfolding threadSet_def could_run_def
    apply (rule hoare_seq_ext[OF _ getObject_tcb_sp])
    apply (rule hoare_pre)
     apply (simp add: valid_queues_def valid_queues_no_bitmap_def)
     apply (wp hoare_Ball_helper hoare_vcg_all_lift setObject_tcb_strongest)
    apply (clarsimp simp: valid_queues_no_bitmap_except_def obj_at'_def)
    done

  have setQueue_could_run: "\<And>d p ts.
    \<lbrace> valid_queues and (\<lambda>_. t \<in> set ts) and
      (\<lambda>s. could_run d p t s) \<rbrace>
    setQueue d p ts
    \<lbrace>\<lambda>rv s. (\<forall>d p. t \<in> set (ksReadyQueues s (d, p)) \<longrightarrow> could_run d p t s)\<rbrace>"
    unfolding setQueue_def valid_queues_def could_run_def
    by wp (fastforce dest: valid_queues_no_bitmap_objD simp: obj_at'_def inQ_def)

  note hoare_vcg_if_lift[wp] hoare_vcg_conj_lift[wp] hoare_vcg_const_imp_lift[wp]

  show ?thesis
  unfolding tcbSchedEnqueue_def null_def
  apply (rule hoare_pre)
   apply (rule hoare_seq_ext)
    apply (simp add: unless_def)
    apply (wp threadSet_valid_queues_could_run)
        apply (wp addToBitmap_could_run addToBitmap_valid_bitmapQ
                  addToBitmap_valid_queues_no_bitmap_except addToBitmap_bitmapQ_no_L2_orphans)+
       apply (wp setQueue_valid_queues_no_bitmap_except setQueue_could_run
                 setQueue_valid_bitmapQ_except setQueue_sets_queue setQueue_valid_bitmapQ)+
      apply (wp threadGet_const_tcb_at_imp_lift | simp add: if_apply_def2)+
  apply clarsimp
  apply (frule (1) valid_tcbs'_maxDomain)
  apply (frule (1) valid_tcbs'_maxPriority)
  apply (clarsimp simp: valid_queues_def st_tcb_at'_def obj_at'_def valid_queues_no_bitmap_exceptI)
  apply (fastforce dest!: valid_queues_no_bitmap_objD simp: obj_at'_def inQ_def could_run_def)
  done
qed

lemma tcbSchedEnqueue_valid_queues[wp]:
  "\<lbrace>valid_queues and valid_tcbs'\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
   unfolding tcbSchedEnqueue_def
   by (fastforce intro:  tcbSchedEnqueueOrAppend_valid_queues)

lemma tcbSchedEnqueue_valid_release_queue[wp]:
  "\<lbrace>Invariants_H.valid_release_queue\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. Invariants_H.valid_release_queue\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def unless_def when_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>)?)+
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' simp: valid_release_queue_def)
  apply (rule hoare_seq_ext_skip, wpsimp simp: bitmap_fun_defs valid_release_queue_def)
  apply (wpsimp wp: threadSet_valid_release_queue)
  done

lemma tcbSchedEnqueue_valid_release_queue'[wp]:
  "\<lbrace>Invariants_H.valid_release_queue'\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. Invariants_H.valid_release_queue'\<rbrace>"
   unfolding tcbSchedEnqueue_def
  apply (clarsimp simp: tcbSchedEnqueue_def unless_def when_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_if; (solves \<open>wpsimp\<close>)?)
  apply (rule hoare_seq_ext_skip, (solves \<open>wpsimp\<close>)?)+
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'
               simp: valid_release_queue'_def setQueue_def)
  apply (rule hoare_seq_ext_skip, wpsimp simp: bitmap_fun_defs valid_release_queue'_def)
  apply (wpsimp wp: threadSet_valid_release_queue')
  apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
  done

crunches tcbSchedEnqueue
  for valid_dom_schedule'_misc[wp]: "\<lambda>s. P (ksDomScheduleIdx s) (ksDomSchedule s)"

lemma tcbSchedEnqueue_valid_dom_schedule'[wp]:
  "tcbSchedEnqueue t \<lbrace>valid_dom_schedule'\<rbrace>"
  by (wpsimp wp: valid_dom_schedule'_lift)

lemma tcbSchedAppend_valid_queues[wp]:
  "\<lbrace>valid_queues and valid_tcbs'\<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
   unfolding tcbSchedAppend_def
   by (fastforce intro: tcbSchedEnqueueOrAppend_valid_queues)

lemma rescheduleRequired_valid_queues[wp]:
  "\<lbrace>\<lambda>s. valid_queues s \<and> valid_tcbs' s\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wpsimp wp: isSchedulable_inv hoare_vcg_if_lift2 hoare_drop_imps)
  done

lemma rescheduleRequired_valid_queues_sch_act_simple:
  "\<lbrace>Invariants_H.valid_queues and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wpsimp wp: isSchedulable_inv hoare_vcg_if_lift2 hoare_drop_imps)
  apply (fastforce simp: Invariants_H.valid_queues_def sch_act_simple_def)
  done

lemma rescheduleRequired_valid_bitmapQ_sch_act_simple:
  "\<lbrace> valid_bitmapQ and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  including no_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. valid_bitmapQ s \<and>
                            (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)" in hoare_seq_ext)
   apply wpsimp
   apply (case_tac x; simp)
  apply (wp, fastforce)
  done

lemma rescheduleRequired_bitmapQ_no_L1_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L1_orphans and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  including no_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. bitmapQ_no_L1_orphans s \<and>
                            (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)" in hoare_seq_ext)
   apply wpsimp
   apply (case_tac x; simp)
  apply (wp, fastforce)
  done

lemma rescheduleRequired_bitmapQ_no_L2_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L2_orphans and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  including no_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. bitmapQ_no_L2_orphans s \<and>
                            (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)" in hoare_seq_ext)
   apply wpsimp
   apply (case_tac x; simp)
  apply (wp, fastforce)
  done

lemma scheduleTCB_bitmapQ_sch_act_simple:
  "\<lbrace>valid_bitmapQ and sch_act_simple\<rbrace>
   scheduleTCB tcbPtr
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  by (wpsimp simp: scheduleTCB_def
               wp: rescheduleRequired_valid_bitmapQ_sch_act_simple isSchedulable_inv
                   hoare_vcg_if_lift2 hoare_drop_imps)

lemma sts_valid_bitmapQ_sch_act_simple:
  "\<lbrace>valid_bitmapQ and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  by (wpsimp wp: threadSet_valid_bitmapQ scheduleTCB_bitmapQ_sch_act_simple)

lemma scheduleTCB_bitmapQ_no_L2_orphans_sch_act_simple:
  "\<lbrace>bitmapQ_no_L2_orphans and sch_act_simple\<rbrace>
   scheduleTCB tcbPtr
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  by (wpsimp simp: scheduleTCB_def
               wp: rescheduleRequired_bitmapQ_no_L2_orphans_sch_act_simple isSchedulable_inv
                   hoare_vcg_if_lift2 hoare_drop_imps)

lemma sts_valid_bitmapQ_no_L2_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L2_orphans and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  by (wpsimp wp: threadSet_valid_bitmapQ_no_L2_orphans
                 scheduleTCB_bitmapQ_no_L2_orphans_sch_act_simple)

lemma scheduleTCB_bitmapQ_no_L1_orphans_sch_act_simple:
  "\<lbrace>bitmapQ_no_L1_orphans and sch_act_simple\<rbrace>
   scheduleTCB tcbPtr
   \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  by (wpsimp simp: scheduleTCB_def
               wp: rescheduleRequired_bitmapQ_no_L1_orphans_sch_act_simple isSchedulable_inv
                   hoare_vcg_if_lift2 hoare_drop_imps)

lemma sts_valid_bitmapQ_no_L1_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L1_orphans and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  by (wpsimp wp: threadSet_valid_bitmapQ_no_L1_orphans
                 scheduleTCB_bitmapQ_no_L1_orphans_sch_act_simple)

lemma scheduleTCB_valid_queues:
  "\<lbrace>Invariants_H.valid_queues\<rbrace>
   scheduleTCB tcbPtr
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (clarsimp simp: scheduleTCB_def getCurThread_def getSchedulerAction_def)
  apply (intro hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp wp: isSchedulable_inv)
  apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
  by (wpsimp simp: scheduleTCB_def sch_act_simple_def
               wp: rescheduleRequired_valid_queues_sch_act_simple hoare_vcg_if_lift2
                   hoare_drop_imps)

lemma sts_valid_queues[wp]:
  "setThreadState st t \<lbrace>valid_queues\<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  apply (wpsimp wp: threadSet_valid_queues scheduleTCB_valid_queues)
  apply (clarsimp simp: inQ_def)
  done

lemma sbn_valid_queues:
  "setBoundNotification ntfn t \<lbrace>Invariants_H.valid_queues\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_queues)
  by (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def valid_queues_no_bitmap_def
                     inQ_def)+

lemma addToBitmap_valid_queues'[wp]:
  "\<lbrace> valid_queues' \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. valid_queues' \<rbrace>"
  unfolding valid_queues'_def addToBitmap_def
            modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
            getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def
  by (wp, simp)

lemma tcbSchedEnqueue_valid_queues'[wp]:
  "tcbSchedEnqueue t \<lbrace>valid_queues'\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def)
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
        apply (clarsimp simp: valid_queues'_def obj_at'_def inQ_def)
       apply (wp setQueue_valid_queues' | simp | simp add: setQueue_def)+
     apply (wp getObject_tcb_wp | simp add: threadGet_getObject)+
     apply (clarsimp simp: obj_at'_def inQ_def valid_queues'_def)
    apply (wp getObject_tcb_wp | simp add: threadGet_getObject)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma rescheduleRequired_valid_queues'[wp]:
  "rescheduleRequired \<lbrace>valid_queues'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wpsimp wp: isSchedulable_inv hoare_vcg_if_lift2)
  done

lemma tcbSchedEnqueue_sch_act_sane[wp]:
  "tcbSchedEnqueue t \<lbrace>sch_act_sane\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def sch_act_sane_def)
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma rescheduleRequired_valid_release_queue[wp]:
  "rescheduleRequired \<lbrace>valid_release_queue\<rbrace>"
  apply (simp add: rescheduleRequired_def getSchedulerAction_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac B="\<lambda>_. valid_release_queue" in hoare_seq_ext[rotated];
         (solves \<open>wpsimp simp: valid_release_queue_def\<close>)?)
  done

lemma rescheduleRequired_valid_release_queue'[wp]:
  "rescheduleRequired \<lbrace>valid_release_queue'\<rbrace>"
  apply (simp add: rescheduleRequired_def getSchedulerAction_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac B="\<lambda>_. valid_release_queue'" in hoare_seq_ext[rotated];
         (solves \<open>wpsimp simp: valid_release_queue'_def\<close>)?)
  done

lemma setThreadState_valid_queues'[wp]:
  "setThreadState st t \<lbrace>valid_queues'\<rbrace>"
  apply (simp add: setThreadState_def scheduleTCB_def)
  apply (rule hoare_seq_ext_skip)
   apply (wp threadSet_valid_queues')
   apply (clarsimp simp: inQ_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (clarsimp simp: getSchedulerAction_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp wp: isSchedulable_inv)
  apply (rule hoare_when_cases; wpsimp simp: weak_sch_act_wf_def)
  done

lemma setThreadState_valid_release_queue[wp]:
  "setThreadState st t \<lbrace>valid_release_queue\<rbrace>"
  apply (simp add: setThreadState_def scheduleTCB_def)
  apply (rule hoare_seq_ext_skip)
   apply (wp threadSet_valid_release_queue)
   using valid_release_queue_def apply simp
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (clarsimp simp: getSchedulerAction_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp wp: isSchedulable_inv)
  apply (rule hoare_when_cases)
   apply clarsimp
  apply wpsimp
  done

lemma setThreadState_valid_release_queue'[wp]:
  "setThreadState st t \<lbrace>valid_release_queue'\<rbrace>"
  apply (simp add: setThreadState_def scheduleTCB_def)
  apply (rule hoare_seq_ext_skip)
   apply (wp threadSet_valid_release_queue')
   apply (fastforce simp: obj_at'_def valid_release_queue'_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (clarsimp simp: getSchedulerAction_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp wp: isSchedulable_inv)
  apply (rule hoare_when_cases)
   apply clarsimp
  apply wpsimp
  done

lemma setBoundNotification_valid_queues'[wp]:
  "\<lbrace>\<lambda>s. valid_queues' s\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_queues')
  apply (fastforce simp: inQ_def obj_at'_def pred_tcb_at'_def)
  done

lemma setBoundNotification_valid_release_queue[wp]:
  "setBoundNotification ntfn t \<lbrace>valid_release_queue\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_release_queue)
  apply (fastforce simp: inQ_def obj_at'_def pred_tcb_at'_def)
  done

lemma setBoundNotification_valid_release_queues[wp]:
  "setBoundNotification ntfn t \<lbrace>valid_release_queue'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_release_queue')
  apply (fastforce simp: inQ_def obj_at'_def pred_tcb_at'_def valid_release_queue'_def)
  done

lemma setThreadState_valid_objs'[wp]:
  "\<lbrace> valid_tcb_state' st and valid_objs' \<rbrace> setThreadState st t \<lbrace> \<lambda>_. valid_objs' \<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_tcbState_update)
  done

crunches addToBitmap
  for ksPSpace[wp]: "\<lambda>s. P (ksPSpace s ptr = opt)"

lemma addToBitmap_valid_tcb'[wp]:
  "addToBitmap tdom prio \<lbrace>valid_tcb' tcb\<rbrace>"
  by (wpsimp simp: addToBitmap_def getReadyQueuesL2Bitmap_def getReadyQueuesL1Bitmap_def
                   modifyReadyQueuesL2Bitmap_def modifyReadyQueuesL1Bitmap_def
                   update_valid_tcb')

lemma addToBitmap_valid_tcbs'[wp]:
  "addToBitmap tdom prio \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
  done

crunches setQueue
  for valid_tcb'[wp]: "\<lambda>s. valid_tcb' tcb s"
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s ptr = opt)"

lemma tcbSchedEnqueue_valid_tcb'[wp]:
  "tcbSchedEnqueue thread \<lbrace>valid_tcb' tcb\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (clarsimp simp: unless_def when_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (wpsimp wp: threadSet_valid_tcb')
  done

lemma tcbSchedEnqueue_valid_tcbs'[wp]:
  "tcbSchedEnqueue thread \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def setQueue_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (clarsimp simp: unless_def when_def)
  apply (rule hoare_seq_ext_skip, wpsimp simp: valid_tcbs'_def wp: update_valid_tcb')+
  apply (wpsimp wp: threadSet_valid_tcbs')
  done

lemma setSchedulerAction_valid_tcbs'[wp]:
  "setSchedulerAction sa \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  apply (wpsimp wp: hoare_vcg_all_lift update_valid_tcb')
  done

lemma rescheduleRequired_valid_tcbs'[wp]:
  "rescheduleRequired \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: rescheduleRequired_def)
  apply (rule hoare_seq_ext_skip, wpsimp wp: update_valid_tcb' isSchedulable_wp)+
  apply (wpsimp wp: update_valid_tcb')
  done

crunches scheduleTCB
  for valid_tcbs'[wp]: valid_tcbs'
  (wp: crunch_wps simp: crunch_simps)

lemma setThreadState_valid_tcbs'[wp]:
  "\<lbrace> valid_tcb_state' st and valid_tcbs' \<rbrace> setThreadState st t \<lbrace> \<lambda>_. valid_tcbs' \<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  apply (wpsimp wp: threadSet_valid_tcbs')
  apply (clarsimp simp: valid_tcb'_tcbState_update)
  done

lemma rescheduleRequired_ksQ:
  "\<lbrace>\<lambda>s. sch_act_simple s \<and> P (ksReadyQueues s)\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  including no_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)
                            \<and> P (ksReadyQueues s)" in hoare_seq_ext)
   apply wpsimp
   apply (case_tac x; simp)
  apply wp
  done

lemma scheduleTCB_ksQ:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace>
   scheduleTCB tcbPtr
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wpsimp simp: scheduleTCB_def sch_act_simple_def
               wp: isSchedulable_inv rescheduleRequired_ksQ hoare_vcg_if_lift2 isSchedulable_wp)

lemma setSchedulerAction_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setSchedulerAction act \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wp, simp)

lemma sts_ksQ:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wpsimp wp: scheduleTCB_ksQ)
  done

lemma setQueue_ksQ[wp]:
  "\<lbrace>\<lambda>s. P ((ksReadyQueues s)((d, p) := q))\<rbrace>
     setQueue d p q
   \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (simp add: setQueue_def fun_upd_def[symmetric]
           | wp)+

lemma tcbSchedEnqueue_ksQ:
  "\<lbrace>\<lambda>s. t' \<notin> set (ksReadyQueues s p) \<and> t' \<noteq> t \<rbrace>
   tcbSchedEnqueue t \<lbrace>\<lambda>_ s. t' \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wpsimp wp: hoare_vcg_imp_lift threadGet_wp)
  apply (drule obj_at_ko_at')
  apply fastforce
  done

lemma rescheduleRequired_ksQ':
  "\<lbrace>\<lambda>s. t \<notin> set (ksReadyQueues s p) \<and> sch_act_not t s \<rbrace>
   rescheduleRequired \<lbrace>\<lambda>_ s. t \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  by (wpsimp wp: tcbSchedEnqueue_ksQ isSchedulable_inv hoare_vcg_if_lift2 hoare_drop_imps)

lemma threadSet_tcbState_st_tcb_at':
  "\<lbrace>\<lambda>s. P st \<rbrace> threadSet (tcbState_update (\<lambda>_. st)) t \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: threadSet_def pred_tcb_at'_def)
  apply (wpsimp wp: setObject_tcb_strongest)
  done

lemma isRunnable_const:
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> isRunnable t \<lbrace>\<lambda>runnable _. runnable \<rbrace>"
  by (rule isRunnable_wp)

lemma sts_ksQ':
  "\<lbrace>\<lambda>s. ((runnable' st \<and> isSchedulable_bool t s) \<or> ksCurThread s \<noteq> t) \<and> P (ksReadyQueues s)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  apply (simp add: setThreadState_def scheduleTCB_def getCurThread_def getSchedulerAction_def)
  apply (rule hoare_pre_disj')
   apply (rule hoare_seq_ext_skip, wpsimp wp: threadSet_isSchedulable_bool_nochange)
   apply (intro hoare_seq_ext[OF _ gets_sp]
                hoare_seq_ext[OF _ isSchedulable_sp])
   apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
   apply (fastforce simp: pred_conj_def valid_def)
  apply (rule hoare_seq_ext_skip, wpsimp wp: threadSet_isSchedulable_bool_nochange)
  apply (intro hoare_seq_ext[OF _ gets_sp]
               hoare_seq_ext[OF _ isSchedulable_sp])
  apply (rule hoare_when_cases; (solves \<open>wpsimp\<close>)?)
  apply (fastforce simp: pred_conj_def valid_def)
  done

lemma valid_ipc_buffer_ptr'D:
  assumes yv: "y < unat max_ipc_words"
  and    buf: "valid_ipc_buffer_ptr' a s"
  shows "pointerInUserData (a + of_nat y * 8) s"
  using buf unfolding valid_ipc_buffer_ptr'_def pointerInUserData_def
  apply clarsimp
  apply (subgoal_tac
         "(a + of_nat y * 8) && ~~ mask pageBits = a  && ~~ mask pageBits")
   apply simp
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (erule is_aligned_add_helper [THEN conjunct2])
   apply (rule word_less_power_trans_ofnat [where k = 3, simplified])
     apply (rule order_less_le_trans [OF yv])
     apply (simp add: msg_align_bits max_ipc_words)
    apply (simp add: msg_align_bits)
   apply (simp_all add: msg_align_bits pageBits_def)
  done

lemma in_user_frame_eq:
  assumes y: "y < unat max_ipc_words"
  and    al: "is_aligned a msg_align_bits"
  shows "in_user_frame (a + of_nat y * 8) s = in_user_frame a s"
proof -
  have "\<And>sz. (a + of_nat y * 8) && ~~ mask (pageBitsForSize sz) =
             a && ~~ mask (pageBitsForSize sz)"
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (rule is_aligned_add_helper [OF al, THEN conjunct2])
   apply (rule word_less_power_trans_ofnat [where k = 3, simplified])
     apply (rule order_less_le_trans [OF y])
     apply (simp add: msg_align_bits max_ipc_words)
    apply (simp add: msg_align_bits)
   apply (simp add: msg_align_bits pageBits_def)
  apply (case_tac sz, simp_all add: msg_align_bits bit_simps)
  done

  thus ?thesis by (simp add: in_user_frame_def)
qed

lemma loadWordUser_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres (=) \<top> (valid_ipc_buffer_ptr' a) (load_word_offs a y) (loadWordUser (a + of_nat y * 8))"
  unfolding loadWordUser_def
  apply (rule corres_stateAssert_assume [rotated])
   apply (erule valid_ipc_buffer_ptr'D[OF y])
  apply (rule corres_guard_imp)
    apply (simp add: load_word_offs_def word_size_def)
    apply (rule_tac F = "is_aligned a msg_align_bits" in corres_gen_asm2)
    apply (rule corres_machine_op)
    apply (rule corres_Id [OF refl refl])
    apply (rule no_fail_pre)
     apply wp
    apply (erule aligned_add_aligned)
      apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
      apply (simp add: word_bits_conv msg_align_bits)+
  apply (simp add: valid_ipc_buffer_ptr'_def msg_align_bits)
  done

lemma storeWordUser_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres dc (in_user_frame a) (valid_ipc_buffer_ptr' a)
                   (store_word_offs a y w) (storeWordUser (a + of_nat y * 8) w)"
  apply (simp add: storeWordUser_def bind_assoc[symmetric]
                   store_word_offs_def word_size_def)
  apply (rule corres_guard2_imp)
   apply (rule_tac F = "is_aligned a msg_align_bits" in corres_gen_asm2)
   apply (rule corres_guard1_imp)
    apply (rule_tac r'=dc in corres_split)
       apply (simp add: stateAssert_def)
       apply (rule_tac r'=dc in corres_split)
          apply (rule corres_trivial)
          apply simp
         apply (rule corres_assert)
        apply wp+
      apply (rule corres_machine_op)
      apply (rule corres_Id [OF refl])
       apply simp
      apply (rule no_fail_pre)
       apply (wp no_fail_storeWord)
      apply (erule_tac n=msg_align_bits in aligned_add_aligned)
       apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
      apply (simp add: word_bits_conv msg_align_bits)+
     apply wp+
   apply (simp add: in_user_frame_eq[OF y])
  apply simp
  apply (rule conjI)
   apply (frule (1) valid_ipc_buffer_ptr'D [OF y])
  apply (simp add: valid_ipc_buffer_ptr'_def)
  done

lemma load_word_corres:
  "corres (=) \<top>
     (typ_at' UserDataT (a && ~~ mask pageBits) and (\<lambda>s. is_aligned a word_size_bits))
     (do_machine_op (loadWord a)) (loadWordUser a)"
  unfolding loadWordUser_def
  apply (rule corres_gen_asm2)
  apply (rule corres_stateAssert_assume [rotated])
   apply (simp add: pointerInUserData_def)
  apply (rule corres_guard_imp)
    apply simp
    apply (rule corres_machine_op)
    apply (rule corres_Id [OF refl refl])
    apply (rule no_fail_pre)
     apply (wpsimp simp: word_size_bits_def)+
  done

lemmas msgRegisters_unfold
  = RISCV64_H.msgRegisters_def
    msg_registers_def
    RISCV64.msgRegisters_def
        [unfolded upto_enum_def, simplified,
         unfolded fromEnum_def enum_register, simplified,
         unfolded toEnum_def enum_register, simplified]

lemma thread_get_registers:
  "thread_get (arch_tcb_get_registers \<circ> tcb_arch) t = as_user t (gets user_regs)"
  apply (simp add: thread_get_def as_user_def arch_tcb_get_registers_def
                   arch_tcb_context_get_def arch_tcb_context_set_def)
  apply (rule bind_cong [OF refl])
  apply (clarsimp simp: gets_the_member)
  apply (simp add: get_def the_run_state_def set_object_def get_object_def
                   put_def bind_def return_def gets_def swp_def assert_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: map_upd_triv select_f_def image_def return_def gets_the_def gets_def get_def
                        bind_def')
  done

lemma getMRs_corres:
  assumes mirel: "mi' = message_info_map mi" shows
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct)
              (case_option \<top> valid_ipc_buffer_ptr' buf)
              (get_mrs t buf mi) (getMRs t buf mi')"
  proof -
  have S: "get = gets id"
    by (simp add: gets_def)
  have T: "corres (\<lambda>con regs. regs = map con msg_registers)
                  (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                  (thread_get (arch_tcb_get_registers o tcb_arch) t)
                  (asUser t (mapM getRegister RISCV64_H.msgRegisters))"
   apply (subst thread_get_registers)
    apply (rule asUser_corres')
    apply (subst mapM_gets)
     apply (simp add: getRegister_def)
    apply (simp add: S RISCV64_H.msgRegisters_def msg_registers_def)
    done
  show ?thesis
  apply (case_tac mi, simp add: get_mrs_def getMRs_def mirel split del: if_split)
  apply (case_tac buf)
   apply (rule corres_guard_imp)
     apply (rule corres_split [where R = "\<lambda>_. \<top>" and R' =  "\<lambda>_. \<top>", OF T])
       apply simp
      apply wp+
    apply simp
   apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF T])
      apply (simp only: option.simps return_bind fun_app_def
                        load_word_offs_def doMachineOp_mapM ef_loadWord)
      apply (rule corres_split_eqr)
         apply (simp only: mapM_map_simp msgMaxLength_def msgLengthBits_def
                           msg_max_length_def o_def upto_enum_word)
         apply (rule corres_mapM [where r'="(=)" and S="{a. fst a = snd a \<and> fst a < unat max_ipc_words}"])
               apply simp
              apply simp
             apply (simp add: word_size wordSize_def wordBits_def)
             apply (rule loadWordUser_corres)
             apply simp
            apply wp+
          apply simp
          apply (unfold msgRegisters_unfold)[1]
          apply simp
         apply (clarsimp simp: set_zip)
         apply (simp add: msgRegisters_unfold max_ipc_words nth_append)
        apply (rule corres_trivial, simp)
       apply (wp hoare_vcg_all_lift | simp add: valid_ipc_buffer_ptr'_def)+
  done
qed

lemmas doMachineOp_return = submonad_doMachineOp.return

lemma doMachineOp_bind:
 "\<lbrakk> empty_fail a; \<And>x. empty_fail (b x) \<rbrakk> \<Longrightarrow> doMachineOp (a >>= b) = (doMachineOp a >>= (\<lambda>rv. doMachineOp (b rv)))"
  by (blast intro: submonad_bind submonad_doMachineOp)

lemma zipWithM_x_corres:
  assumes x: "\<And>x x' y y'. ((x, y), (x', y')) \<in> S \<Longrightarrow> corres dc P P' (f x y) (f' x' y')"
  assumes y: "\<And>x x' y y'. ((x, y), (x', y')) \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x y \<lbrace>\<lambda>rv. P\<rbrace>"
      and z: "\<And>x x' y y'. ((x, y), (x', y')) \<in> S \<Longrightarrow> \<lbrace>P'\<rbrace> f' x' y' \<lbrace>\<lambda>rv. P'\<rbrace>"
      and a: "set (zip (zip xs ys) (zip xs' ys')) \<subseteq> S"
      and b: "length (zip xs ys) = length (zip xs' ys')"
  shows      "corres dc P P' (zipWithM_x f xs ys) (zipWithM_x f' xs' ys')"
  apply (simp add: zipWithM_x_mapM)
  apply (rule corres_underlying_split)
     apply (rule corres_mapM)
           apply (rule dc_simp)+
         apply clarsimp
         apply (rule x)
         apply assumption
        apply (clarsimp simp: y)
       apply (clarsimp simp: z)
      apply (rule b)
     apply (rule a)
    apply (rule corres_trivial, simp)
   apply (rule hoare_post_taut)+
  done


lemma valid_ipc_buffer_ptr'_def2:
  "valid_ipc_buffer_ptr' = (\<lambda>p s. (is_aligned p msg_align_bits \<and> typ_at' UserDataT (p && ~~ mask pageBits) s))"
  apply (rule ext, rule ext)
  apply (simp add: valid_ipc_buffer_ptr'_def)
  done

lemma storeWordUser_valid_ipc_buffer_ptr' [wp]:
  "\<lbrace>valid_ipc_buffer_ptr' p\<rbrace> storeWordUser p' w \<lbrace>\<lambda>_. valid_ipc_buffer_ptr' p\<rbrace>"
  unfolding valid_ipc_buffer_ptr'_def2
  by (wp hoare_vcg_all_lift storeWordUser_typ_at')

lemma thread_set_as_user_registers:
  "thread_set (\<lambda>tcb. tcb \<lparr> tcb_arch := arch_tcb_set_registers (f (arch_tcb_get_registers (tcb_arch tcb)))
                          (tcb_arch tcb) \<rparr>) t
    = as_user t (modify (modify_registers f))"
proof -
  have P: "\<And>f. det (modify f)"
    by (simp add: modify_def)
  thus ?thesis
    apply (simp add: as_user_def P thread_set_def)
    apply (clarsimp simp: select_f_def simpler_modify_def bind_def image_def modify_registers_def
                          arch_tcb_set_registers_def arch_tcb_get_registers_def
                          arch_tcb_context_set_def arch_tcb_context_get_def)
    done
qed

lemma UserContext_fold:
  "UserContext (foldl (\<lambda>s (x, y). s(x := y)) (user_regs s) xs) =
   foldl (\<lambda>s (r, v). UserContext ((user_regs s)(r := v))) s xs"
  apply (induct xs arbitrary: s; simp)
  apply (clarsimp split: prod.splits)
  by (metis user_context.sel(1))

lemma setMRs_corres:
  assumes m: "mrs' = mrs"
  shows
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct and case_option \<top> in_user_frame buf)
              (case_option \<top> valid_ipc_buffer_ptr' buf)
              (set_mrs t buf mrs) (setMRs t buf mrs')"
proof -
  have setRegister_def2:
    "setRegister = (\<lambda>r v.  modify (\<lambda>s. UserContext ((user_regs s)(r := v))))"
    by ((rule ext)+, simp add: setRegister_def)

  have S: "\<And>xs ys n m. m - n \<ge> length xs \<Longrightarrow> (zip xs (drop n (take m ys))) = zip xs (drop n ys)"
    by (simp add: zip_take_triv2 drop_take)

  note upt.simps[simp del] upt_rec_numeral[simp del]

  show ?thesis using m
    unfolding setMRs_def set_mrs_def
    apply (clarsimp  cong: option.case_cong split del: if_split)
    apply (subst bind_assoc[symmetric])
    apply (fold thread_set_def[simplified])
    apply (subst thread_set_as_user_registers)
    apply (cases buf)
     apply (clarsimp simp: msgRegisters_unfold setRegister_def2 zipWithM_x_Nil zipWithM_x_modify
                           take_min_len zip_take_triv2 min.commute)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor[OF asUser_corres'])
         apply (rule corres_modify')
          apply (fastforce simp: fold_fun_upd[symmetric] msgRegisters_unfold UserContext_fold
                                 modify_registers_def
                           cong: if_cong simp del: the_index.simps)
          apply simp
         apply (rule corres_trivial, simp)
         apply ((wp |simp)+)[4]
    \<comment> \<open>buf = Some a\<close>
    using if_split[split del]
    apply (clarsimp simp: msgRegisters_unfold setRegister_def2 zipWithM_x_Nil zipWithM_x_modify
                          take_min_len zip_take_triv2 min.commute
                          msgMaxLength_def msgLengthBits_def)
    apply (simp add: msg_max_length_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_nor[OF asUser_corres'])
         apply (rule corres_modify')
          apply (simp only: msgRegisters_unfold cong: if_cong)
          apply (fastforce simp: fold_fun_upd[symmetric] modify_registers_def UserContext_fold)
         apply simp
        apply (rule corres_split_nor)
           apply (rule_tac S="{((x, y), (x', y')). y = y' \<and> x' = (a + (of_nat x * 8)) \<and> x < unat max_ipc_words}"
                         in zipWithM_x_corres)
               apply (fastforce intro: storeWordUser_corres)
              apply wp+
            apply (clarsimp simp add: S msgMaxLength_def msg_max_length_def set_zip)
            apply (simp add: wordSize_def wordBits_def word_size max_ipc_words
                              upt_Suc_append[symmetric] upto_enum_word)
           apply simp
          apply (rule corres_trivial, clarsimp simp: min.commute)
         apply wp+
      apply (wp | clarsimp simp: valid_ipc_buffer_ptr'_def)+
    done
qed

lemma copyMRs_corres:
  "corres (=) (tcb_at s and tcb_at r and pspace_aligned and pspace_distinct
               and case_option \<top> in_user_frame sb
               and case_option \<top> in_user_frame rb
               and K (unat n \<le> msg_max_length))
              (case_option \<top> valid_ipc_buffer_ptr' sb
               and case_option \<top> valid_ipc_buffer_ptr' rb)
              (copy_mrs s sb r rb n) (copyMRs s sb r rb n)"
proof -
  have U: "unat n \<le> msg_max_length \<Longrightarrow>
           map (toEnum :: nat \<Rightarrow> machine_word) [7 ..< Suc (unat n)] = map of_nat [7 ..< Suc (unat n)]"
    unfolding msg_max_length_def by auto
  note R'=msgRegisters_unfold[THEN meta_eq_to_obj_eq, THEN arg_cong[where f=length]]
  note R=R'[simplified]

  have as_user_bit:
    "\<And>v :: machine_word.
       corres dc (tcb_at s and tcb_at r and pspace_aligned and pspace_distinct)
                 \<top>
           (mapM
             (\<lambda>ra. do v \<leftarrow> as_user s (getRegister ra);
                      as_user r (setRegister ra v)
                   od)
             (take (unat n) msg_registers))
           (mapM
             (\<lambda>ra. do v \<leftarrow> asUser s (getRegister ra);
                      asUser r (setRegister ra v)
                   od)
             (take (unat n) msgRegisters))"
    apply (rule corres_guard_imp)
      apply (rule_tac S=Id in corres_mapM, simp+)
          apply (rule corres_split_eqr[OF asUser_getRegister_corres asUser_setRegister_corres])
           apply (wp | clarsimp simp: msg_registers_def msgRegisters_def)+
    done

  have wordSize[simp]: "of_nat wordSize = 8"
    by (simp add: wordSize_def wordBits_def word_size)

  show ?thesis
    apply (rule corres_assume_pre)
    apply (simp add: copy_mrs_def copyMRs_def word_size
               cong: option.case_cong
          split del: if_split del: upt.simps)
    apply (cases sb)
     apply (simp add: R)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor[OF as_user_bit])
         apply (rule corres_trivial, simp)
        apply wp+
      apply simp
     apply simp
    apply (cases rb)
     apply (simp add: R)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor[OF as_user_bit])
         apply (rule corres_trivial, simp)
        apply wp+
      apply simp
     apply simp
    apply (simp add: R del: upt.simps)
    apply (rule corres_guard_imp)
      apply (rename_tac sb_ptr rb_ptr)
      apply (rule corres_split_nor[OF as_user_bit])
        apply (rule corres_split_eqr)
           apply (rule_tac S="{(x, y). y = of_nat x \<and> x < unat max_ipc_words}"
                   in corres_mapM, simp+)
               apply (rule corres_split_eqr)
                  apply (rule loadWordUser_corres)
                  apply simp
                 apply (rule storeWordUser_corres)
                 apply simp
                apply (wp hoare_vcg_all_lift | simp)+
            apply (clarsimp simp: upto_enum_def)
            apply arith
           apply (subst set_zip)
           apply (simp add: upto_enum_def U del: upt.simps)
           apply (clarsimp simp del: upt.simps)
           apply (clarsimp simp: msg_max_length_def word_le_nat_alt nth_append
                                 max_ipc_words)
           apply (erule order_less_trans)
           apply simp
          apply (rule corres_trivial, simp)
         apply (wp hoare_vcg_all_lift mapM_wp'
                | simp add: valid_ipc_buffer_ptr'_def)+
    done
qed

lemma cte_at_tcb_at_32':
  "tcb_at' t s \<Longrightarrow> cte_at' (t + 32) s"
  apply (simp add: cte_at'_obj_at')
  apply (rule disjI2, rule bexI[where x=32])
   apply simp
  apply fastforce
  done

lemma get_tcb_cap_corres:
  "tcb_cap_cases ref = Some (getF, v) \<Longrightarrow>
   corres cap_relation (tcb_at t and valid_objs) (tcb_at' t and pspace_aligned' and pspace_distinct')
                       (liftM getF (gets_the (get_tcb t)))
                       (getSlotCap (cte_map (t, ref)))"
  apply (simp add: getSlotCap_def liftM_def[symmetric])
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (cases v, simp)
   apply (frule tcb_cases_related)
   apply (clarsimp simp: cte_at'_obj_at')
   apply (drule spec[where x=t])
   apply (drule bspec, erule domI)
   apply simp
  apply clarsimp
  apply (clarsimp simp: gets_the_def simpler_gets_def
                        bind_def assert_opt_def tcb_at_def
                        return_def
                 dest!: get_tcb_SomeD)
  apply (drule use_valid [OF _ getCTE_sp[where P="(=) s'" for s'], OF _ refl])
  apply (clarsimp simp: get_tcb_def return_def)
  apply (drule pspace_relation_ctes_ofI[OF state_relation_pspace_relation])
     apply (rule cte_wp_at_tcbI[where t="(t, ref)"], fastforce+)[1]
    apply assumption+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemmas get_vtable_cap_corres =
  get_tcb_cap_corres[where ref="tcb_cnode_index 1", simplified, OF conjI [OF refl refl]]

lemma pspace_dom_dom:
  "dom ps \<subseteq> pspace_dom ps"
  unfolding pspace_dom_def
  apply clarsimp
  apply (rule rev_bexI [OF domI], assumption)
  apply (simp add: obj_relation_cuts_def2 image_Collect cte_map_def range_composition [symmetric]
    split: Structures_A.kernel_object.splits arch_kernel_obj.splits cong: arch_kernel_obj.case_cong)
  apply safe
     apply (drule wf_cs_0)
     apply clarsimp
     apply (rule_tac x = n in exI)
     apply (clarsimp simp: of_bl_def)
    apply (rule range_eqI [where x = 0], simp)+
  apply (rename_tac vmpage_size)
  apply (rule exI [where x = 0])
  apply (case_tac vmpage_size, simp_all add: bit_simps)
  done

lemma no_0_obj_kheap:
  assumes no0: "no_0_obj' s'"
  and     psr: "pspace_relation (kheap s) (ksPSpace s')"
  shows   "kheap s 0 = None"
proof (rule ccontr)
  assume "kheap s 0 \<noteq> None"
  hence "0 \<in> dom (kheap s)" ..
  hence "0 \<in> pspace_dom (kheap s)" by (rule set_mp [OF pspace_dom_dom])
  moreover
  from no0 have "0 \<notin> dom (ksPSpace s')"
    unfolding no_0_obj'_def by clarsimp
  ultimately show False using psr
    by (clarsimp simp: pspace_relation_def)
qed

lemmas valid_ipc_buffer_cap_simps = valid_ipc_buffer_cap_def [split_simps cap.split arch_cap.split]

lemma lookupIPCBuffer_corres':
  "corres (=) (tcb_at t and valid_objs and pspace_aligned and pspace_distinct)
              (no_0_obj')
              (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  apply (rule corres_cross_over_guard[where P'=Q and
                                            Q="pspace_aligned' and pspace_distinct' and Q" for Q])
   apply (fastforce simp: pspace_aligned_cross pspace_distinct_cross state_relation_def)
  apply (simp add: lookup_ipc_buffer_def RISCV64_H.lookupIPCBuffer_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF threadGet_corres])
       apply (simp add: tcb_relation_def)
      apply (simp add: getThreadBufferSlot_def locateSlot_conv)
      apply (rule corres_split[OF getSlotCap_corres])
         apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def tcbIPCBufferSlot_def)
        apply (rule_tac F="valid_ipc_buffer_cap rv buffer_ptr"
                    in corres_gen_asm)
        apply (rule_tac P="valid_cap rv" and Q="no_0_obj'"
                    in corres_assume_pre)
        apply (simp add: Let_def split: cap.split arch_cap.split
              split del: if_split cong: if_cong)
        apply (safe, simp_all add: isCap_simps valid_ipc_buffer_cap_simps split:bool.split_asm)[1]
        apply (rename_tac word rights vmpage_size d option)
        apply (subgoal_tac "word + (buffer_ptr &&
                                    mask (pageBitsForSize vmpage_size)) \<noteq> 0")
         apply (simp add: cap_aligned_def
                          valid_ipc_buffer_cap_def
                          vmrights_map_def vm_read_only_def vm_read_write_def)
        apply auto[1]
        apply (subgoal_tac "word \<noteq> 0")
         apply (subgoal_tac "word \<le> word + (buffer_ptr &&
                               mask (pageBitsForSize vmpage_size))")
          apply fastforce
         apply (rule_tac b="2 ^ (pageBitsForSize vmpage_size) - 1"
                   in word_plus_mono_right2)
          apply (clarsimp simp: valid_cap_def cap_aligned_def
                        intro!: is_aligned_no_overflow')
         apply (clarsimp simp: word_bits_def bit_simps
                       intro!: word_less_sub_1 and_mask_less')
         apply (case_tac vmpage_size, simp_all add: bit_simps)[1]
        apply (drule state_relation_pspace_relation)
        apply (clarsimp simp: valid_cap_def obj_at_def no_0_obj_kheap
                              obj_relation_cuts_def3 no_0_obj'_def
                       split: if_split_asm)
       apply (wp get_cap_valid_ipc get_cap_aligned)+
     apply (wp thread_get_obj_at_eq)+
   apply (clarsimp elim!: tcb_at_cte_at)
  apply clarsimp
  done

lemma lookupIPCBuffer_corres:
  "corres (=) (tcb_at t and invs) (no_0_obj') (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  using lookupIPCBuffer_corres'
  by (rule corres_guard_imp, auto simp: invs'_def)

crunch inv[wp]: lookupIPCBuffer P
  (wp: crunch_wps simp: crunch_simps)

end

crunches scheduleTCB, possibleSwitchTo
  for pred_tcb_at'[wp]: "\<lambda>s. P' (pred_tcb_at' proj P t s)"
  (wp: crunch_wps simp: crunch_simps)

lemma setThreadState_st_tcb':
  "\<lbrace>\<top>\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>s. s = st) t\<rbrace>"
  apply (simp add: setThreadState_def)
  by (wpsimp wp: threadSet_pred_tcb_at_state)

lemma setThreadState_st_tcb:
  "\<lbrace>\<lambda>s. P st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (cases "P st")
   apply simp
   apply (rule hoare_post_imp [OF _ setThreadState_st_tcb'])
   apply (erule pred_tcb'_weakenE, simp)
  apply simp
  done

lemma setBoundNotification_bound_tcb':
  "\<lbrace>\<top>\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. bound_tcb_at' (\<lambda>s. s = ntfn) t\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_pred_tcb_at_state | simp add: if_apply_def2)+
  done

lemma setBoundNotification_bound_tcb:
  "\<lbrace>\<lambda>s. P ntfn\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. bound_tcb_at' P t\<rbrace>"
  apply (cases "P ntfn")
   apply simp
   apply (rule hoare_post_imp [OF _ setBoundNotification_bound_tcb'])
   apply (erule pred_tcb'_weakenE, simp)
  apply simp
  done

crunches rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma ct_in_state'_decomp:
  assumes x: "\<lbrace>\<lambda>s. t = (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv s. t = (ksCurThread s)\<rbrace>"
  assumes y: "\<lbrace>Pre\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' Prop t\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Pre s \<and> t = (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv. ct_in_state' Prop\<rbrace>"
  apply (rule hoare_post_imp [where Q="\<lambda>rv s. t = ksCurThread s \<and> st_tcb_at' Prop t s"])
   apply (clarsimp simp add: ct_in_state'_def)
  apply (rule hoare_vcg_precond_imp)
   apply (wp x y)
  apply simp
  done

lemma ct_in_state'_set:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> P st \<and> t = ksCurThread s\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
  apply (rule hoare_vcg_precond_imp)
   apply (rule ct_in_state'_decomp[where t=t])
    apply (wp setThreadState_ct')
   apply (wp setThreadState_st_tcb)
  apply clarsimp
  done

crunches setQueue, scheduleTCB, tcbSchedDequeue
  for idle'[wp]: "valid_idle'"
  (simp: crunch_simps wp: crunch_wps)

lemma sts_valid_idle'[wp]:
  "\<lbrace>valid_idle' and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' ts)\<rbrace>
   setThreadState ts t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: setThreadState_def)
  by (wpsimp wp: threadSet_idle' simp: idle_tcb'_def)

lemma sbn_valid_idle'[wp]:
  "\<lbrace>valid_idle' and (\<lambda>s. t = ksIdleThread s \<longrightarrow> \<not>bound ntfn)\<rbrace>
   setBoundNotification ntfn t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wpsimp wp: threadSet_idle' simp: idle_tcb'_def)
  done

lemma gts_sp':
  "\<lbrace>P\<rbrace> getThreadState t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>st. st = rv) t and P\<rbrace>"
  apply (simp add: getThreadState_def threadGet_getObject)
  apply wp
  apply (simp add: o_def pred_tcb_at'_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma gbn_sp':
  "\<lbrace>P\<rbrace> getBoundNotification t \<lbrace>\<lambda>rv. bound_tcb_at' (\<lambda>st. st = rv) t and P\<rbrace>"
  apply (simp add: getBoundNotification_def threadGet_getObject)
  apply wp
  apply (simp add: o_def pred_tcb_at'_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbSchedDequeue_tcbState_obj_at'[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>rv. obj_at' (P \<circ> tcbState) t'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp | simp add: o_def split del: if_split cong: if_cong)+
  done

lemma tcbSchedDequeue_pred_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. P' (pred_tcb_at' proj P t' s)\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_ s. P' (pred_tcb_at' proj P t' s)\<rbrace>"
  apply (rule_tac P=P' in P_bool_lift)
   apply (simp add: tcbSchedDequeue_def)
   apply (wp threadSet_pred_tcb_no_state | clarsimp simp: tcb_to_itcb'_def)+
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadSet_pred_tcb_no_state | clarsimp simp: tcb_to_itcb'_def)+
  done

lemma tcbReleaseRemove_pred_tcb_at'[wp]:
  "tcbReleaseRemove t \<lbrace>\<lambda>s. P' (pred_tcb_at' proj P t' s)\<rbrace>"
  apply (rule_tac P=P' in P_bool_lift)
  unfolding tcbReleaseRemove_def
   apply (wp threadSet_pred_tcb_no_state
          | clarsimp simp: tcb_to_itcb'_def setReleaseQueue_def
                           setReprogramTimer_def getReleaseQueue_def)+
  done

crunches tcbReleaseRemove
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"

lemma sts_st_tcb':
  "\<lbrace>if t = t' then K (P st) else st_tcb_at' P t\<rbrace>
  setThreadState st t'
  \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  by (cases "t = t'"; wpsimp wp: threadSet_pred_tcb_at_state simp: setThreadState_def)

lemma sts_bound_tcb_at'[wp]:
  "setThreadState st t' \<lbrace>bound_tcb_at' P t\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  by (cases "t = t'"; wpsimp wp: threadSet_pred_tcb_at_state simp: pred_tcb_at'_def)+

lemma sts_bound_sc_tcb_at'[wp]:
  "setThreadState st t' \<lbrace>bound_sc_tcb_at' P t\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  by (cases "t = t'"; wpsimp wp: threadSet_pred_tcb_at_state simp: pred_tcb_at'_def)+

lemma sts_bound_yt_tcb_at'[wp]:
  "setThreadState st t' \<lbrace>bound_yt_tcb_at' P t\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  by (cases "t = t'";
      wpsimp wp: threadSet_pred_tcb_at_state
           simp: pred_tcb_at'_def)

lemma sbn_st_tcb'[wp]:
  "setBoundNotification ntfn t' \<lbrace>st_tcb_at' P t\<rbrace>"
  apply (cases "t = t'",
         simp_all add: setBoundNotification_def
                  split del: if_split)
   apply ((wp threadSet_pred_tcb_at_state | simp)+)[1]
  apply (wp threadSet_obj_at'_really_strongest | simp add: pred_tcb_at'_def)+
  done

context begin interpretation Arch .

crunches scheduleTCB, setThreadState
  for cte_wp_at'[wp]: "\<lambda>s. Q (cte_wp_at' P p s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  (wp: hoare_when_weak_wp crunch_wps)

lemmas setThreadState_cap_to'[wp]
  = ex_cte_cap_to'_pres [OF setThreadState_cte_wp_at' setThreadState_ksInterruptState]

crunches setThreadState, setBoundNotification
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and cte_wp_at'[wp]: "\<lambda>s. Q (cte_wp_at' P p s)"
  (wp: hoare_when_weak_wp crunch_wps)

crunch refs_of'[wp]: rescheduleRequired "\<lambda>s. P (state_refs_of' s)"
  (wp: threadSet_state_refs_of' crunch_wps)

crunches scheduleTCB
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"

abbreviation tcb_non_st_state_refs_of' ::
  "kernel_state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
  where
  "tcb_non_st_state_refs_of' s t \<equiv>
    {r \<in> state_refs_of' s t. snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo}"

lemma state_refs_of'_helper2[simp]:
  "tcb_non_st_state_refs_of' s t
   = {r \<in> state_refs_of' s t. snd r = TCBBound}
     \<union> {r \<in> state_refs_of' s t. snd r = TCBSchedContext}
     \<union> {r \<in> state_refs_of' s t. snd r = TCBYieldTo}"
  by fastforce

lemma setThreadState_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' st
                                    \<union> tcb_non_st_state_refs_of' s t))\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_state_refs_of')
      apply simp
     apply force+
  by (metis Un_assoc)

lemma setBoundNotification_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := (case ntfn of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, TCBBound)})
                                    \<union> {r \<in> state_refs_of' s t. snd r \<noteq> TCBBound}))\<rbrace>
   setBoundNotification ntfn t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setBoundNotification_def)
  apply (wpsimp wp: threadSet_state_refs_of'
                     [where f'=id and h'=id and i'=id and F="tcbBoundNotification_update (\<lambda>_. ntfn)"]
              simp: get_refs_def)
     apply simp
    apply simp
   apply simp
  apply (prop_tac "{r \<in> state_refs_of' s t. snd r \<noteq> TCBBound}
                    = {r \<in> state_refs_of' s t. snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext
                                               \<and> snd r \<noteq> TCBYieldTo}
                      \<union> {r \<in> state_refs_of' s t. snd r = TCBSchedContext}
                      \<union> {r \<in> state_refs_of' s t. snd r = TCBYieldTo}")
   apply fastforce
  by (metis id_def Un_ac(1) Un_ac(4))

lemma setBoundNotification_list_refs_of_replies'[wp]:
  "setBoundNotification ntfn t \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  unfolding setBoundNotification_def
  by wpsimp

lemma sts_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

lemma sbn_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

crunches setQueue, addToBitmap, removeFromBitmap
  for iflive'[wp]: if_live_then_nonz_cap'
  and nonz_cap[wp]: "ex_nonz_cap_to' t"

crunches rescheduleRequired
  for valid_pspace'[wp]: valid_pspace'
  and cap_to'[wp]: "ex_nonz_cap_to' p"

lemma tcbSchedEnqueue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' tcb\<rbrace>
   tcbSchedEnqueue tcb
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp threadSet_iflive' hoare_drop_imps | simp add: crunch_simps)+
  done

lemma rescheduleRequired_iflive'[wp]:
  "rescheduleRequired \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wpsimp wp: isSchedulable_wp)
  apply (erule if_live_then_nonz_capE')
  apply (fastforce simp: isSchedulable_bool_def pred_map_def ko_wp_at'_def obj_at'_def opt_map_def)
  done

crunches scheduleTCB
  for if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  (wp: crunch_wps isSchedulable_inv hoare_vcg_if_lift2)

lemma sts_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setThreadState_def setQueue_def)
  apply (rule hoare_pre)
   apply (wp | simp)+
      apply (rule_tac Q="\<lambda>rv. if_live_then_nonz_cap'" in hoare_post_imp)
       apply clarsimp
      apply (wp threadSet_iflive' | simp)+
   apply auto
 done

lemma sbn_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (bound ntfn \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
   setBoundNotification ntfn t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (rule hoare_pre)
   apply (wp threadSet_iflive' | simp)+
  apply auto
  done

crunches addToBitmap
  for if_unsafe_then_cap'[wp]: if_unsafe_then_cap'

lemma setThreadState_if_unsafe_then_cap'[wp]:
  "setThreadState st p \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (clarsimp simp: setThreadState_def scheduleTCB_def rescheduleRequired_def when_def)
  apply (rule hoare_seq_ext_skip)
   apply (rule threadSet_ifunsafe'T)
   apply (clarsimp simp: tcb_cte_cases_def objBits_simps')
  apply (wpsimp simp: tcbSchedEnqueue_def)
               apply (rule threadSet_ifunsafe'T)
               apply (clarsimp simp: tcb_cte_cases_def objBits_simps')
              apply (wpsimp simp: setQueue_def
                              wp: isSchedulable_inv hoare_vcg_if_lift2 hoare_drop_imps)+
  done

crunches setBoundNotification
  for ifunsafe'[wp]: "if_unsafe_then_cap'"

lemma st_tcb_ex_cap'':
  "\<lbrakk> st_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>st. P st \<Longrightarrow> st \<noteq> Inactive \<and> \<not> idle' st \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

lemma bound_tcb_ex_cap'':
  "\<lbrakk> bound_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>ntfn. P ntfn \<Longrightarrow> bound ntfn \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

crunches setThreadState, setBoundNotification
  for arch' [wp]: "\<lambda>s. P (ksArchState s)"
  (simp: unless_def crunch_simps)

crunches setThreadState
  for it' [wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: getObject_tcb_inv crunch_wps
   simp: updateObject_default_def unless_def crunch_simps)

crunch it' [wp]: removeFromBitmap "\<lambda>s. P (ksIdleThread s)"

crunches setThreadState, setBoundNotification
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (simp: unless_def crunch_simps wp: setObject_ksPSpace_only updateObject_default_inv)

lemmas setThreadState_irq_handlers[wp]
    = valid_irq_handlers_lift'' [OF setThreadState_ctes_of setThreadState_ksInterruptState]

lemmas setBoundNotification_irq_handlers[wp]
    = valid_irq_handlers_lift'' [OF setBoundNotification_ctes_of setBoundNotification.ksInterruptState]

lemma sts_global_reds' [wp]:
  "\<lbrace>valid_global_refs'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

lemma sbn_global_reds' [wp]:
  "\<lbrace>valid_global_refs'\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

crunches setThreadState, setBoundNotification
  for irq_states' [wp]: valid_irq_states'
  (simp: unless_def crunch_simps)

lemma addToBitmap_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> addToBitmap d p \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  unfolding bitmap_fun_defs
  by (wp, simp)

lemma removeFromBitmap_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> removeFromBitmap d p \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  unfolding bitmap_fun_defs
  by (wp|simp add: bitmap_fun_defs)+

lemma tcbSchedEnqueue_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> tcbSchedEnqueue x \<lbrace>\<lambda>_ s. P (ksMachineState s)\<rbrace>"
  by (simp add: tcbSchedEnqueue_def unless_def setQueue_def | wp)+

crunches setThreadState, setBoundNotification
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps)

lemma setThreadState_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setThreadState F t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift; wp)
  done

lemma ct_not_inQ_addToBitmap[wp]:
  "\<lbrace> ct_not_inQ \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. ct_not_inQ \<rbrace>"
  unfolding bitmap_fun_defs
  by (wp, clarsimp simp: ct_not_inQ_def)

lemma ct_not_inQ_removeFromBitmap[wp]:
  "\<lbrace> ct_not_inQ \<rbrace> removeFromBitmap d p \<lbrace>\<lambda>_. ct_not_inQ \<rbrace>"
  unfolding bitmap_fun_defs
  by (wp|simp add: bitmap_fun_defs ct_not_inQ_def comp_def)+

lemma setBoundNotification_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift; wp)
  done

lemma tcbSchedEnqueue_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
    tcbSchedEnqueue t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  proof -
    have ts: "\<lbrace>?PRE\<rbrace> threadSet (tcbQueued_update (\<lambda>_. True)) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
      apply (simp add: ct_not_inQ_def)
      apply (rule_tac Q="\<lambda>s. ksSchedulerAction s = ResumeCurrentThread
                  \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and> ksCurThread s \<noteq> t"
                  in hoare_pre_imp, clarsimp)
      apply (rule hoare_convert_imp [OF threadSet.ksSchedulerAction])
      apply (rule hoare_weaken_pre)
       apply (wps setObject_ct_inv)
       apply (rule threadSet_obj_at'_strongish)
      apply (clarsimp simp: comp_def)
      done
    have sq: "\<And>d p q. \<lbrace>ct_not_inQ\<rbrace> setQueue d p q \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
      apply (simp add: ct_not_inQ_def setQueue_def)
      apply (wp)
      apply (clarsimp)
      done
    show ?thesis
      apply (simp add: tcbSchedEnqueue_def unless_def null_def)
      apply (wp ts sq hoare_convert_imp [OF addToBitmap_nosch addToBitmap_ct'])+
           apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
           apply (wp sq hoare_convert_imp [OF setQueue_nosch setQueue_ct])+
       apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
       apply wp
      apply assumption
      done
  qed

lemma tcbSchedAppend_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
    tcbSchedAppend t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  proof -
    have ts: "\<lbrace>?PRE\<rbrace> threadSet (tcbQueued_update (\<lambda>_. True)) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
      apply (simp add: ct_not_inQ_def)
      apply (rule_tac Q="\<lambda>s. ksSchedulerAction s = ResumeCurrentThread
                  \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and> ksCurThread s \<noteq> t"
                  in hoare_pre_imp, clarsimp)
      apply (rule hoare_convert_imp [OF threadSet.ksSchedulerAction])
      apply (rule hoare_weaken_pre)
       apply (wps setObject_ct_inv)
       apply (rule threadSet_obj_at'_strongish)
      apply (clarsimp simp: comp_def)
      done
    have sq: "\<And>d p q. \<lbrace>ct_not_inQ\<rbrace> setQueue d p q \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
      apply (simp add: ct_not_inQ_def setQueue_def)
      apply (wp)
      apply (clarsimp)
      done
    show ?thesis
      apply (simp add: tcbSchedAppend_def unless_def null_def)
      apply (wp ts sq hoare_convert_imp [OF addToBitmap_nosch addToBitmap_ct'])+
           apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
           apply (wp sq hoare_convert_imp [OF setQueue_nosch setQueue_ct])+
       apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
       apply wp
      apply assumption
      done
  qed

lemma setSchedulerAction_direct[wp]:
  "\<lbrace>\<top>\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_ s. ksSchedulerAction s = sa\<rbrace>"
  by (wpsimp simp: setSchedulerAction_def)

lemma rescheduleRequired_ct_not_inQ[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: rescheduleRequired_def ct_not_inQ_def)
  apply (rule_tac Q="\<lambda>_ s. ksSchedulerAction s = ChooseNewThread"
           in hoare_post_imp, clarsimp)
  apply (wp setSchedulerAction_direct)
  done

lemma scheduleTCB_ct_not_inQ[wp]:
  "scheduleTCB tcbPtr \<lbrace>ct_not_inQ\<rbrace>"
  apply (clarsimp simp: scheduleTCB_def getCurThread_def getSchedulerAction_def)
  by (wpsimp wp: rescheduleRequired_ct_not_inQ isSchedulable_inv hoare_vcg_if_lift2 hoare_drop_imps)

crunches tcbSchedEnqueue, tcbSchedAppend, tcbSchedDequeue
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: unless_def)

lemma rescheduleRequired_sa_cnt[wp]:
  "\<lbrace>\<lambda>s. True \<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread \<rbrace>"
  unfolding rescheduleRequired_def setSchedulerAction_def
  by (wpsimp wp: hoare_vcg_if_lift2)

lemma possibleSwitchTo_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
    possibleSwitchTo t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wpsimp wp: rescheduleRequired_ct_not_inQ tcbSchedEnqueue_ct_not_inQ threadGet_wp
              simp: inReleaseQueue_def
         | (rule hoare_post_imp[OF _ rescheduleRequired_sa_cnt], fastforce))+
  apply (fastforce simp: obj_at'_def)
  done

lemma threadSet_tcbState_update_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> threadSet (tcbState_update f) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: ct_not_inQ_def)
  apply (rule hoare_convert_imp [OF threadSet.ksSchedulerAction])
  apply (simp add: threadSet_def)
  apply (wp)
    apply (wps setObject_ct_inv)
    apply (rule setObject_tcb_strongest)
   prefer 2
   apply assumption
  apply (clarsimp)
  apply (rule hoare_conjI)
   apply (rule hoare_weaken_pre)
   apply (wps, wp static_imp_wp)
   apply (wp OMG_getObject_tcb)+
   apply (clarsimp simp: comp_def)
  apply (wp hoare_drop_imp)
  done

lemma threadSet_tcbBoundNotification_update_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> threadSet (tcbBoundNotification_update f) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: ct_not_inQ_def)
  apply (rule hoare_convert_imp [OF threadSet.ksSchedulerAction])
  apply (simp add: threadSet_def)
  apply (wp)
    apply (wps setObject_ct_inv)
    apply (rule setObject_tcb_strongest)
   prefer 2
   apply assumption
  apply (clarsimp)
  apply (rule hoare_conjI)
   apply (rule hoare_weaken_pre)
   apply wps
   apply (wp static_imp_wp)
   apply (wp OMG_getObject_tcb)
   apply (clarsimp simp: comp_def)
  apply (wp hoare_drop_imp)
  done

lemma setThreadState_ct_not_inQ:
  "\<lbrace>ct_not_inQ\<rbrace> setThreadState st t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  including no_pre
  apply (simp add: setThreadState_def)
  by (wpsimp wp: threadSet_tcbState_update_ct_not_inQ)

lemma setBoundNotification_ct_not_inQ:
  "\<lbrace>ct_not_inQ\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  by (simp add: setBoundNotification_def, wp)

crunch ct_not_inQ[wp]: setQueue "ct_not_inQ"

lemma tcbSchedDequeue_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  proof -
    have TSNIQ: "\<And>F t.
      \<lbrace>ct_not_inQ and (\<lambda>_. \<forall>tcb. \<not>tcbQueued (F tcb))\<rbrace>
      threadSet F t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
      apply (simp add: ct_not_inQ_def)
      apply (wp hoare_convert_imp [OF threadSet.ksSchedulerAction])
       apply (simp add: threadSet_def)
       apply (wp)
        apply (wps setObject_ct_inv)
        apply (wp setObject_tcb_strongest getObject_tcb_wp)+
      apply (case_tac "t = ksCurThread s")
       apply (clarsimp simp: obj_at'_def)+
      done
    show ?thesis
      apply (simp add: tcbSchedDequeue_def)
      apply (wp TSNIQ | simp cong: if_cong)+
      done
  qed

lemma tcbSchedEnqueue_not_st:
  "(\<And>tcb st qd. P (tcb\<lparr>tcbState := st, tcbQueued := qd\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> \<lbrace>obj_at' P t'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. obj_at' P t'\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp threadGet_wp | simp)+
  apply (clarsimp simp: obj_at'_def)
  apply (case_tac obja)
  apply fastforce
  done

lemma setThreadState_not_st:
  "(\<And>tcb st qd. P (tcb\<lparr>tcbState := st, tcbQueued := qd\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> \<lbrace>obj_at' P t'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. obj_at' P t'\<rbrace>"
  apply (simp add: setThreadState_def scheduleTCB_def rescheduleRequired_def)
  apply (rule_tac B="\<lambda>_. obj_at' P t'" in hoare_seq_ext[rotated])
   apply (wpsimp wp: threadSet_obj_at'_really_strongest)
   apply (clarsimp simp: obj_at'_def)
   apply (rename_tac tcb')
   apply (case_tac tcb'; fastforce)
  apply (wpsimp wp: isSchedulable_inv hoare_vcg_conj_lift tcbSchedEnqueue_not_st hoare_vcg_if_lift2
                    hoare_drop_imps)
  done

crunch ct_idle_or_in_cur_domain'[wp]: setQueue ct_idle_or_in_cur_domain'
  (simp: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

crunch ksDomSchedule[wp]: setQueue "\<lambda>s. P (ksDomSchedule s)"

crunch ksCurDomain[wp]: addToBitmap "\<lambda>s. P (ksCurDomain s)"
  (wp:  crunch_wps )
crunch ksDomSchedule[wp]: addToBitmap "\<lambda>s. P (ksDomSchedule s)"
  (wp:  crunch_wps )
crunch ksCurDomain[wp]: removeFromBitmap "\<lambda>s. P (ksCurDomain s)"
  (wp:  crunch_wps )
crunch ksDomSchedule[wp]: removeFromBitmap "\<lambda>s. P (ksDomSchedule s)"
  (wp:  crunch_wps )

lemma addToBitmap_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace> ct_idle_or_in_cur_domain' \<rbrace> addToBitmap d p \<lbrace> \<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
  apply (wp hoare_vcg_disj_lift| rule obj_at_setObject2
           | clarsimp simp: updateObject_default_def in_monad setNotification_def)+
  done

lemma removeFromBitmap_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace> ct_idle_or_in_cur_domain' \<rbrace> removeFromBitmap d p \<lbrace> \<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
  apply (wp hoare_vcg_disj_lift| rule obj_at_setObject2
           | clarsimp simp: updateObject_default_def in_monad setNotification_def)+
  done

lemma tcbSchedEnqueue_ksCurDomain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s)\<rbrace> tcbSchedEnqueue tptr \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply wpsimp
  done

lemma tcbSchedEnqueue_ksDomSchedule[wp]:
  "\<lbrace> \<lambda>s. P (ksDomSchedule s)\<rbrace> tcbSchedEnqueue tptr \<lbrace>\<lambda>_ s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply wpsimp
  done

lemma tcbSchedEnqueue_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> tcbSchedEnqueue tptr \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp threadSet_ct_idle_or_in_cur_domain' | simp)+
  done

lemma setSchedulerAction_spec:
  "\<lbrace>\<top>\<rbrace>setSchedulerAction ChooseNewThread
  \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add:setSchedulerAction_def)
  apply wp
  apply (simp add:ct_idle_or_in_cur_domain'_def)
  done

crunches rescheduleRequired, setThreadState, setBoundNotification
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps)

lemma rescheduleRequired_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp setSchedulerAction_spec)
  done

crunches scheduleTCB
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'
  (wp: crunch_wps hoare_vcg_if_lift2)

lemma setThreadState_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setThreadState st tptr \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_ct_idle_or_in_cur_domain' hoare_drop_imps | simp)+
  done

lemma setBoundNotification_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setBoundNotification t a \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_ct_idle_or_in_cur_domain' hoare_drop_imps | simp)+
  done

crunches rescheduleRequired, setBoundNotification, setThreadState
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps)

lemma sts_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp untyped_ranges_zero_lift)
  done

lemma pair_inject:
  "{a,b} = {c,d} \<and> a \<noteq> d \<and> b \<noteq> c \<Longrightarrow> a = c \<and> b = d"
  by blast

lemma tcb_bound_refs'_helper:
  "tcb_bound_refs' ntfnptr sc_ptr yieldto_ptr
   = {r. (r \<in> tcb_st_refs_of' st \<or> r \<in> tcb_bound_refs' ntfnptr sc_ptr yieldto_ptr) \<and> snd r = TCBBound}
     \<union> {r. (r \<in> tcb_st_refs_of' st \<or> r \<in> tcb_bound_refs' ntfnptr sc_ptr yieldto_ptr) \<and> snd r = TCBSchedContext}
     \<union> {r. (r \<in> tcb_st_refs_of' st \<or> r \<in> tcb_bound_refs' ntfnptr sc_ptr yieldto_ptr) \<and> snd r = TCBYieldTo}"
  apply (clarsimp simp: tcb_bound_refs'_def get_refs_def tcb_st_refs_of'_def
                 split: option.splits thread_state.splits reftype.splits)
  apply (intro conjI impI allI; fastforce?)
  done

lemma valid_tcb_state'_same_tcb_st_refs_of':
  "\<lbrakk>tcb_st_refs_of' st = tcb_st_refs_of' st'; valid_tcb_state' st s\<rbrakk>
   \<Longrightarrow> valid_tcb_state' st' s"
  apply (cases st';
         clarsimp simp: valid_tcb_state'_def tcb_st_refs_of'_def
                 split: Structures_H.thread_state.splits if_splits)
  by (metis pair_inject reftype.distinct prod.inject)

lemma sts_invs_minor':
  "\<lbrace>st_tcb_at' (\<lambda>st'. (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                       st' \<noteq> Inactive \<and> \<not> idle' st')
                   \<and> (\<forall>rptr. st' = BlockedOnReply rptr \<longrightarrow>
                             st = BlockedOnReply rptr)) t
      and valid_tcb_state' st
      and invs'\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: sts_sch_act' valid_irq_node_lift irqs_masked_lift setThreadState_ct_not_inQ
              simp: cteCaps_of_def o_def pred_tcb_at'_eq_commute)
  apply (intro conjI impI)
    apply clarsimp
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  apply (erule if_live_then_nonz_capE')
  apply (clarsimp simp: pred_tcb_at'_def ko_wp_at'_def obj_at'_def projectKO_eq projectKO_tcb)
  done

lemma sts_invs':
  "\<lbrace>(\<lambda>s. st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow> ex_nonz_cap_to' t s)
      and (\<lambda>s. \<forall>rptr. st_tcb_at' ((=) (BlockedOnReply (Some rptr))) t s \<longrightarrow> (is_reply_linked rptr s) \<longrightarrow> st = BlockedOnReply (Some rptr))
      and tcb_at' t
      and valid_tcb_state' st
      and invs'\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: sts_sch_act' valid_irq_node_lift irqs_masked_lift setThreadState_ct_not_inQ
              simp: cteCaps_of_def o_def)
  by metis

lemma sts_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma sts_pred_tcb_neq':
  "\<lbrace>pred_tcb_at' proj P t and K (t \<noteq> t')\<rbrace>
  setThreadState st t'
  \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_pred_tcb_at_state | simp)+
  done

lemma sbn_pred_tcb_neq':
  "\<lbrace>pred_tcb_at' proj P t and K (t \<noteq> t')\<rbrace>
  setBoundNotification ntfn t'
  \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_pred_tcb_at_state | simp)+
  done

lemmas isTS_defs =
  isRunning_def isBlockedOnSend_def isBlockedOnReceive_def
  isBlockedOnNotification_def isBlockedOnReply_def
  isRestart_def isInactive_def
  isIdleThreadState_def

(* FIXME: replace `sts_st_tcb_at'_cases`, which is missing the `tcb_at'` precondition. *)
lemma setThreadState_st_tcb_at'_cases:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow>
          (t = t' \<longrightarrow> P st) \<and>
          (t \<noteq> t' \<longrightarrow> st_tcb_at' P t' s)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  unfolding setThreadState_def
  apply (wpsimp wp: scheduleTCB_pred_tcb_at' threadSet_pred_tcb_at_state)
  done

lemma sts_st_tcb_at'_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> (P ts \<and> tcb_at' t' s)) \<and> ((t \<noteq> t') \<longrightarrow> st_tcb_at' P t' s)\<rbrace>
     setThreadState ts t
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  apply (wp sts_st_tcb')
  apply fastforce
  done

lemma sts_st_tcb_at'_cases_strong:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (t = t' \<longrightarrow> P (P' ts)) \<and> (t \<noteq> t' \<longrightarrow> P (st_tcb_at' P' t' s))\<rbrace>
   setThreadState ts t
   \<lbrace>\<lambda>rv s. P (st_tcb_at' P' t' s) \<rbrace>"
  unfolding setThreadState_def
  by (wpsimp wp: scheduleTCB_pred_tcb_at' threadSet_pred_tcb_at_state)

lemma threadSet_ct_running':
  "(\<And>tcb. tcbState (f tcb) = tcbState tcb) \<Longrightarrow>
  \<lbrace>ct_running'\<rbrace> threadSet f t \<lbrace>\<lambda>rv. ct_running'\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply (wp threadSet_pred_tcb_no_state; simp)
  apply wp
  done

lemma setThreadState_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_pre)
   apply wps
   apply (wp setThreadState_not_st | simp)+
  done

lemma asUser_global_refs':   "\<lbrace>valid_global_refs'\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wpsimp wp: threadSet_global_refs select_f_inv)
  done

lemma sch_act_sane_lift:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  shows "\<lbrace>sch_act_sane\<rbrace> f \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: sch_act_sane_def)
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply (wp assms)+
  done

lemma storeWord_invs'[wp]:
  "\<lbrace>pointerInUserData p and invs'\<rbrace> doMachineOp (storeWord p w) \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l. l<8 \<Longrightarrow> p && mask word_size_bits = 0 \<Longrightarrow> p + l && ~~ mask 12 = p && ~~ mask 12"
  proof -
    fix l
    assume al: "p && mask word_size_bits = 0"
    assume "(l::machine_word) < 8" hence less: "l<2^word_size_bits" by (simp add: word_size_bits_def)
    have le: "(word_size_bits::nat) \<le> 12" by (simp add: word_size_bits_def)
    show "?thesis l"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs' no_irq_storeWord no_irq)
    apply (clarsimp simp: storeWord_def invs'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
                          assert_def simpler_modify_def fail_def bind_def return_def
                          aligned_offset_ignore bit_simps upto0_7_def
            split: if_split_asm)
  done
qed

lemma storeWordUser_invs[wp]:
  "\<lbrace>invs'\<rbrace> storeWordUser p w \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: storeWordUser_def | wp)+

lemma hoare_valid_ipc_buffer_ptr_typ_at':
  "(\<And>q. \<lbrace>typ_at' UserDataT q\<rbrace> a \<lbrace>\<lambda>_. typ_at' UserDataT q\<rbrace>)
   \<Longrightarrow> \<lbrace>valid_ipc_buffer_ptr' p\<rbrace> a \<lbrace>\<lambda>_. valid_ipc_buffer_ptr' p\<rbrace>"
  unfolding valid_ipc_buffer_ptr'_def2 including no_pre
  apply wp
  apply assumption
  done

lemma gts_wp':
  "\<lbrace>\<lambda>s. \<forall>st. st_tcb_at' ((=) st) t s \<longrightarrow> P st s\<rbrace> getThreadState t \<lbrace>P\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule gts_sp')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemma gbn_wp':
  "\<lbrace>\<lambda>s. \<forall>ntfn. bound_tcb_at' ((=) ntfn) t s \<longrightarrow> P ntfn s\<rbrace> getBoundNotification t \<lbrace>P\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule gbn_sp')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemmas threadSet_irq_handlers' = valid_irq_handlers_lift'' [OF threadSet_ctes_ofT]

lemma get_cap_corres_all_rights_P:
  "cte_ptr' = cte_map cte_ptr \<Longrightarrow>
  corres (\<lambda>x y. cap_relation x y \<and> P x)
         (cte_wp_at P cte_ptr) (pspace_aligned' and pspace_distinct')
         (get_cap cte_ptr) (getSlotCap cte_ptr')"
  apply (simp add: getSlotCap_def mask_cap_def)
  apply (subst bind_return [symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres_P [where P=P]])
      apply (insert cap_relation_masks, simp)
     apply (wp getCTE_wp')+
   apply simp
  apply fastforce
  done

lemma asUser_irq_handlers':
  "\<lbrace>valid_irq_handlers'\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wpsimp wp: threadSet_irq_handlers' [OF all_tcbI, OF ball_tcb_cte_casesI] select_f_inv)
  done

lemma archTcbUpdate_aux2: "(\<lambda>tcb. tcb\<lparr> tcbArch := f (tcbArch tcb)\<rparr>) = tcbArch_update f"
  by (rule ext, case_tac tcb, simp)

(* FIXME: rename. VER-1331 *)
lemma threadSet_obj_at'_simple_strongest:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow>
          (t = t' \<longrightarrow> P (obj_at' (\<lambda>tcb. Q (f tcb)) t s)) \<and>
          (t \<noteq> t' \<longrightarrow> P (obj_at' Q t' s))\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_ s. P (obj_at' (Q :: tcb \<Rightarrow> bool) t' s)\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: set_tcb'.setObject_obj_at'_strongest set_tcb'.getObject_wp)
  apply (case_tac "t = t'"; clarsimp simp: obj_at'_def)
  done

(* Used as the "side condition template" for the `*_obj_at'_only_st_qd_ft` family of
   `crunch`-able lemmas. Needs to keep the assumption about `f` separate from the hoare
   triple so as to not pollute the side conditions that `crunch` will add to the final
   lemma. *)
lemma threadSet_obj_at'_only_st_qd_ft:
  assumes "(\<forall>upd tcb. Q (tcbState_update upd tcb) = Q tcb) \<and>
           (\<forall>upd tcb. Q (tcbQueued_update upd tcb) = Q tcb) \<and>
           (\<forall>upd tcb. Q (tcbFault_update upd tcb) = Q tcb) \<longrightarrow>
             (\<forall>tcb. Q (f tcb) = Q tcb)"
  shows
  "\<lbrace>\<lambda>s. P (obj_at' Q t' s) \<and>
        (\<forall>upd tcb. Q (tcbState_update upd tcb) = Q tcb) \<and>
        (\<forall>upd tcb. Q (tcbQueued_update upd tcb) = Q tcb) \<and>
        (\<forall>upd tcb. Q (tcbFault_update upd tcb) = Q tcb)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_ s. P (obj_at' Q t' s)\<rbrace>"
  apply (wpsimp wp: threadSet_obj_at'_simple_strongest simp: assms)
  done

crunches scheduleTCB
  for obj_at'_only_st_qd_ft: "\<lambda>s. P (obj_at' (Q :: tcb \<Rightarrow> bool) t s)"
  (simp: crunch_simps wp: crunch_wps)

(* FIXME: Proved outside of `crunch` because without the `[where P=P]` constraint, the
   postcondition unifies with the precondition in a wonderfully exponential way. VER-1337 *)
lemma setThreadState_obj_at'_only_st_qd_ft:
  "\<lbrace>\<lambda>s. P (obj_at' Q t' s) \<and>
        (\<forall>upd tcb. Q (tcbState_update upd tcb) = Q tcb) \<and>
        (\<forall>upd tcb. Q (tcbQueued_update upd tcb) = Q tcb) \<and>
        (\<forall>upd tcb. Q (tcbFault_update upd tcb) = Q tcb)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. P (obj_at' Q t' s)\<rbrace>"
  unfolding setThreadState_def
  apply (wpsimp wp: scheduleTCB_obj_at'_only_st_qd_ft threadSet_obj_at'_only_st_qd_ft[where P=P])
  done

crunches addToBitmap, setQueue
  for ko_wp_at'[wp]: "\<lambda>s. P (ko_wp_at' Q p s)"

lemma tcbSchedEnqueue_tcb_obj_at'_no_change:
  assumes [simp]: "\<And>tcb. Q (tcbQueued_update (\<lambda>_. True) tcb) = Q tcb"
  shows "tcbSchedEnqueue t \<lbrace>\<lambda>s. P (obj_at' Q t' s)\<rbrace>"
  unfolding tcbSchedEnqueue_def
  apply (wpsimp wp: threadSet_obj_at'_simple_strongest hoare_vcg_imp_lift threadGet_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma setThreadState_tcb_obj_at'_no_change:
  assumes [simp]: "\<And>tcb. Q (tcbState_update (\<lambda>_. st) tcb) = Q tcb"
                  "\<And>tcb. Q (tcbQueued_update (\<lambda>_. True) tcb) = Q tcb"
  shows "setThreadState st t \<lbrace>\<lambda>s. P (obj_at' Q t' s)\<rbrace>"
  unfolding setThreadState_def scheduleTCB_def rescheduleRequired_def
  apply (wpsimp wp: tcbSchedEnqueue_tcb_obj_at'_no_change hoare_vcg_if_lift2 isSchedulable_inv
                    hoare_vcg_imp_lift threadSet_obj_at'_simple_strongest
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. rv" for x]
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. \<not>rv" for x])
  done

lemma setThreadState_oa:
  "setThreadState st t
   \<lbrace>\<lambda>s. P (obj_at' (\<lambda>tcb. Q (tcbCTable tcb) (tcbVTable tcb) (tcbIPCBufferFrame tcb)
                            (tcbFaultHandler tcb) (tcbTimeoutHandler tcb) (tcbDomain tcb)
                            (tcbMCP tcb) (tcbPriority tcb) (tcbQueued tcb) (tcbInReleaseQueue tcb)
                            (tcbFault tcb))
                   t' s) \<rbrace>"
  unfolding setThreadState_def scheduleTCB_def rescheduleRequired_def tcbSchedEnqueue_def
  apply (wpsimp wp: threadSet_obj_at'_simple_strongest hoare_vcg_imp_lift hoare_vcg_if_lift2
                    threadGet_obj_at'_field isSchedulable_inv
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. rv" for x]
                    hoare_pre_cont[where a="isSchedulable x" and P="\<lambda>rv _. \<not>rv" for x])
  done

lemma getThreadState_only_rv_wp[wp]:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> st_tcb_at' P t s\<rbrace>
   getThreadState t
   \<lbrace>\<lambda>rv _. P rv\<rbrace>"
  apply (wpsimp wp: gts_wp')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemma getThreadState_only_state_wp[wp]:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> P s\<rbrace>
   getThreadState t
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp wp: gts_wp')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

(* FIXME: replace tcbSchedEnqueue_not_st. VER-1333 *)
lemma tcbSchedEnqueue_obj_at':
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow>
          (t = t' \<longrightarrow> P (obj_at' (\<lambda>tcb. Q (tcb\<lparr>tcbQueued := True\<rparr>)) t' s)) \<and>
          (t \<noteq> t' \<longrightarrow> P (obj_at' Q t' s))\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. P (obj_at' Q t' s)\<rbrace>"
  unfolding tcbSchedEnqueue_def
  apply (wpsimp wp: threadSet_obj_at'_simple_strongest hoare_vcg_imp_lift hoare_vcg_if_lift2
                    threadGet_obj_at'_field)
  apply (case_tac "t = t'"; clarsimp)
  apply normalise_obj_at'
  apply (case_tac "tcbQueued ko"; clarsimp)
  apply (prop_tac "tcbQueued_update (\<lambda>_. True) ko = ko")
   apply (case_tac ko; clarsimp)
  apply simp
  done

lemma getCurSc_corres[corres]:
  "corres (=) \<top> \<top> (gets cur_sc) (getCurSc)"
  unfolding getCurSc_def
  apply (rule corres_gets_trivial)
  by (clarsimp simp: state_relation_def)

crunches getScTime, scActive
  for inv[wp]: P
  (wp: crunch_wps)

lemma threadSet_empty_tcbSchedContext_valid_tcbs'[wp]:
  "threadSet (tcbSchedContext_update Map.empty) t \<lbrace>valid_tcbs'\<rbrace>"
  by (wp threadSet_valid_tcbs')
     (simp add: valid_tcb'_def valid_tcbs'_def tcb_cte_cases_def objBits_simps')

lemma threadSet_vrq_wp:
  "\<lbrace>valid_release_queue and
    (\<lambda>s. tptr \<in> set (ksReleaseQueue s) \<longrightarrow> obj_at' (\<lambda>obj. tcbInReleaseQueue (f obj)) tptr s)\<rbrace>
   threadSet f tptr
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  apply (clarsimp simp: valid_release_queue_def)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
  by (case_tac "x=tptr"; simp)

lemma threadSet_vrq_inv:
  "\<lbrace>valid_release_queue and
    (\<lambda>s. (\<forall>obj. tcbInReleaseQueue (f obj) = tcbInReleaseQueue obj))\<rbrace>
   threadSet f tptr
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  apply (clarsimp simp: valid_release_queue_def)
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)

lemma threadSet_vrq'_inv:
  "\<lbrace>valid_release_queue' and
    (\<lambda>s. (\<forall>obj. tcbInReleaseQueue (f obj) = tcbInReleaseQueue obj))\<rbrace>
   threadSet f tptr
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  apply (clarsimp simp: valid_release_queue'_def)
  by (wpsimp wp: threadSet_obj_at'_simple_strongest hoare_vcg_imp_lift' hoare_vcg_all_lift)

lemma threadSet_enqueue_vrq:
  "\<lbrace>(\<lambda>s. \<forall>a. a \<in> set (ksReleaseQueue s) \<longrightarrow> a\<noteq>t \<longrightarrow> obj_at' tcbInReleaseQueue a s)
    and tcb_at' t\<rbrace>
   threadSet (tcbInReleaseQueue_update (\<lambda>_. True)) t
   \<lbrace>\<lambda>_. valid_release_queue\<rbrace>"
  apply (clarsimp simp: valid_release_queue_def)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
  by (case_tac "x=t"; simp)

lemma threadSet_enqueue_vrq':
  "\<lbrace>(\<lambda>s. \<forall>a. obj_at' tcbInReleaseQueue a s \<longrightarrow> a\<noteq>t \<longrightarrow> a \<in> set (ksReleaseQueue s))
    and tcb_at' t
    and (\<lambda>s. t \<in> set (ksReleaseQueue s))\<rbrace>
   threadSet (tcbInReleaseQueue_update (\<lambda>_. True)) t
   \<lbrace>\<lambda>_. valid_release_queue'\<rbrace>"
  apply (clarsimp simp: valid_release_queue'_def)
  apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift threadSet_obj_at'_simple_strongest)
  by (case_tac "x=t"; fastforce)

lemma thread_set_empty_tcb_sched_context_weaker_valid_sched_action[wp]:
  "thread_set (tcb_sched_context_update Map.empty) tcbPtr \<lbrace>weaker_valid_sched_action\<rbrace>"
  apply (simp only: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: weaker_valid_sched_action_def pred_tcb_at_def)
  apply (auto simp: is_tcb_def get_tcb_def obj_at_def  map_project_def tcbs_of_kh_def opt_map_def
                    pred_map_def map_join_def tcb_scps_of_tcbs_def sc_refill_cfgs_of_scs_def
             split: option.splits Structures_A.kernel_object.splits)
  done

end

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
  and valid_irq_states'[wp]: valid_irq_states'
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and valid_machine_state'[wp]: valid_machine_state'
  (simp: crunch_simps wp: crunch_wps)

crunches tcbReleaseDequeue
  for cur_tcb'[wp]: cur_tcb'
  (simp: crunch_simps cur_tcb'_def wp: crunch_wps threadSet_cur ignore: threadSet)

crunches tcbReleaseRemove
  for pspace_aligned'[wp]: pspace_aligned'
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and no_0_obj'[wp]: no_0_obj'
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and list_refs_of_replies[wp]: "\<lambda>s. sym_refs (list_refs_of_replies' s)"
  and state_refs_of'[wp]: "\<lambda>s. sym_refs (state_refs_of' s)"
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  and interrupt_state[wp]: "\<lambda>s. P (ksInterruptState s)"
  and valid_irq_state'[wp]: valid_irq_states'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  (wp: crunch_wps simp: crunch_simps tcb_cte_cases_def)

global_interpretation tcbReleaseRemove: typ_at_all_props' "tcbReleaseRemove tptr"
  by typ_at_props'

lemma tcbInReleaseQueue_update_tcb_cte_cases:
  "(a, b) \<in> ran tcb_cte_cases \<Longrightarrow> a (tcbInReleaseQueue_update f tcb) = a tcb"
  unfolding tcb_cte_cases_def
  by (case_tac tcb; fastforce simp: tcbInReleaseQueue_update_def objBits_simps')

lemma tcbInReleaseQueue_update_ctes_of[wp]:
  "threadSet (tcbInReleaseQueue_update f) x \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_ofT simp: tcbInReleaseQueue_update_tcb_cte_cases)

crunches tcbReleaseDequeue
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and valid_idle'[wp]: valid_idle'
  and valid_irq_handlers'[wp]: valid_irq_handlers'
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
  apply (wpsimp simp: setReprogramTimer_def setReleaseQueue_def tcbInReleaseQueue_update_tcb_cte_cases
                  wp: threadSet_iflive'T)
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
  by (wpsimp simp: invs'_def valid_dom_schedule'_def
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

lemma tcbReleaseRemove_if_unsafe_then_cap'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_ifunsafe')
  done

lemma tcbReleaseRemove_valid_machine_state'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_machine_state'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma tcbReleaseRemove_ct_idle_or_in_cur_domain'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>ct_idle_or_in_cur_domain'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def)
  apply (wpsimp wp: threadSet_ct_idle_or_in_cur_domain' hoare_vcg_imp_lift' hoare_vcg_disj_lift)
  done

crunches setReprogramTimer
  for valid_queues[wp]: valid_queues
  and ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

lemma tcbReleaseRemove_valid_queues_no_bitmap:
  "\<lbrace>valid_queues\<rbrace>
   tcbReleaseRemove tcbPtr
   \<lbrace>\<lambda>_. valid_queues_no_bitmap\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_queues_no_bitmap_new)
  apply (clarsimp simp: valid_queues_no_bitmap_def valid_queues_def)
  apply (fastforce simp: obj_at'_def inQ_def)
  done

crunches setReleaseQueue, setReprogramTimer
  for valid_bitmapQ[wp]: valid_bitmapQ
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans
  and bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans
  (simp: crunch_simps valid_bitmapQ_def bitmapQ_def bitmapQ_no_L2_orphans_def
         bitmapQ_no_L1_orphans_def)

crunches tcbReleaseRemove
  for valid_bitmapQ[wp]: valid_bitmapQ
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans
  and bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans

lemma setReleaseQueue_obj_at'[wp]:
  "setReleaseQueue Q \<lbrace>\<lambda>s. R (obj_at' P t s)\<rbrace>"
  unfolding setReleaseQueue_def by wpsimp

crunches setReleaseQueue
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"

lemma setReleaseQueue_valid_queues_no_bitmap[wp]:
  "setReleaseQueue Q \<lbrace>valid_queues_no_bitmap\<rbrace>"
  unfolding valid_queues_no_bitmap_def
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift hoare_vcg_ball_lift2)

crunches tcbReleaseRemove
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' p"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: threadSet_cap_to simp: tcb_cte_cases_def objBits_simps')

lemma tcbReleaseRemove_valid_queues:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_queues\<rbrace>"
  apply (wpsimp wp: tcbReleaseRemove_valid_queues_no_bitmap tcbReleaseRemove_valid_bitmapQ
              simp: valid_queues_def)
  done

crunches setReleaseQueue, setReprogramTimer
  for valid_queues'[wp]: valid_queues'
  (simp: valid_queues'_def)

lemma tcbReleaseRemove_valid_queues'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_queues'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_queues')
  apply (clarsimp simp: valid_queues'_def inQ_def)
  done

crunches setReprogramTimer
  for valid_release_queue[wp]: valid_release_queue
  and valid_release_queue'[wp]: valid_release_queue'

lemma tcbReleaseRemove_valid_release_queue[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_release_queue\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_release_queue)
  apply (clarsimp simp: valid_release_queue_def)
  done

lemma tcbReleaseRemove_valid_release_queue'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_release_queue'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_release_queue')
  apply (clarsimp simp: valid_release_queue'_def obj_at'_def)
  done

crunches setReprogramTimer
  for valid_objs'[wp]: valid_objs'
  and sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and if_live_then_nonz_cap'[wp]: if_live_then_nonz_cap'
  and valid_mdb'[wp]: valid_mdb'
  and ct_not_inQ[wp]: ct_not_inQ
  (simp: valid_mdb'_def)

lemma tcbReleaseRemove_valid_objs'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_valid_objs')
  done

lemma tcbReleaseRemove_valid_mdb'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule_tac B="\<lambda>_. valid_mdb'" in hoare_seq_ext[rotated])
   apply wpsimp
   apply (clarsimp simp: valid_mdb'_def)
  apply (wpsimp wp: setObject_tcb_mdb' getObject_tcb_wp simp: threadSet_def)
  apply (fastforce simp: obj_at'_def tcb_cte_cases_def objBits_simps')
  done

lemma tcbReleaseRemove_sch_act_wf[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (wpsimp wp: threadSet_sch_act)
  done

lemma tcbReleaseRemove_if_live_then_nonz_cap'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s\<rbrace>
   tcbReleaseRemove tptr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_iflive' setSchedContext_iflive' threadGet_wp)
  apply (fastforce simp: obj_at'_def)
  done

lemma tcbReleaseRemove_valid_idle'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_idle'\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (wpsimp wp: threadSet_idle')
  done

lemma tcbReleaseRemove_ct_not_inQ[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>ct_not_inQ\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def getReleaseQueue_def setReleaseQueue_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: threadSet_not_inQ)
  done

lemma tcbReleaseRemove_invs':
  "tcbReleaseRemove tcbPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift cur_tcb_lift
                    untyped_ranges_zero_lift tcbReleaseRemove_valid_queues valid_replies'_lift
              simp: cteCaps_of_def o_def)
  done

crunches tcbReleaseRemove, tcbSchedDequeue
  for sch_act_simple[wp]: sch_act_simple
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps sch_act_simple_def)

lemma tcbInReleaseQueue_update_st_tcb_at'[wp]:
  "threadSet (tcbInReleaseQueue_update b) t \<lbrace>\<lambda>s. Q (st_tcb_at' P t' s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (cases "t=t'")
   apply (fastforce simp: obj_at_simps st_tcb_at'_def ps_clear_def)
  apply (erule back_subst[where P=Q])
  apply (fastforce simp: obj_at_simps st_tcb_at'_def ps_clear_def)
  done

crunches tcbReleaseEnqueue
  for st_tcb_at'[wp]: "\<lambda>s. Q (st_tcb_at' P tptr s)"
  (wp: mapM_wp_inv ignore: threadSet)

end
