(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TcbAcc_R
imports ArchCSpace_R
begin

crunch orderedInsert, tcbQueueRemove
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation tcbQueuePrepend: typ_at_all_props' "tcbQueuePrepend q tcbPtr"
  by typ_at_props'

global_interpretation tcbQueueAppend: typ_at_all_props' "tcbQueueAppend q tcbPtr"
  by typ_at_props'

global_interpretation tcbQueueInsert: typ_at_all_props' "tcbQueueInsert tcbPtr afterPtr"
  by typ_at_props'

global_interpretation orderedInsert: typ_at_all_props' "orderedInsert t q f r"
  by typ_at_props'

lemma threadRead_SomeD:
  "threadRead f t s = Some y \<Longrightarrow> \<exists>tcb. ko_at' tcb t s \<and> y = f tcb"
  by (fastforce simp: threadRead_def oliftM_def dest!: readObject_misc_ko_at')

lemma threadGet_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at' tcb t s \<longrightarrow> P (f tcb) s\<rbrace> threadGet f t \<lbrace>P\<rbrace>"
  apply (simp add: threadGet_getObject)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadGet_return_rewrite:
  "monadic_rewrite False True (ko_at' ko t) (threadGet f t) (return (f ko))"
  apply (rule monadic_rewrite_add_return_l)
  apply monadic_rewrite_symb_exec_l
     apply (rule monadic_rewrite_guard_arg_cong)
     apply fastforce
    apply (wpsimp wp: threadGet_wp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma ko_at'_threadRead:
  "ko_at' ko tcbPtr s \<Longrightarrow> threadRead f tcbPtr s = Some (f ko)"
  apply (frule threadGet_return_rewrite[
                 simplified monadic_rewrite_def threadGet_def, simplified, rule_format])
  apply (fastforce simp: monad_simps split: option.splits)
  done

(* Auxiliaries and basic properties of priority bitmap functions *)

lemma countLeadingZeros_word_clz[simp]:
  "countLeadingZeros w = word_clz w"
  unfolding countLeadingZeros_def word_clz_def
  by (simp add: to_bl_upt)

(* same derivation on all architectures for arbitrary 'a, i.e. can't become locale assumption *)
lemma (in Arch) wordLog2_word_log2:
  "wordLog2 = word_log2"
  unfolding wordLog2_def word_log2_def
  by (simp add: word_size wordBits_def)

requalify_facts Arch.wordLog2_word_log2
lemmas [simp] = wordLog2_word_log2

lemmas bitmap_fun_defs = addToBitmap_def removeFromBitmap_def
                          modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
                          getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def

lemmas tcbQueueEmpty_def = headEndPtrsEmpty_def

(* lookupBitmapPriority is a cleaner version of getHighestPrio *)
definition
  "lookupBitmapPriority d \<equiv> \<lambda>s.
     l1IndexToPrio (word_log2 (ksReadyQueuesL1Bitmap s d)) ||
       of_nat (word_log2 (ksReadyQueuesL2Bitmap s (d,
            invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d)))))"

lemma getHighestPrio_def'[simp]:
  "getHighestPrio d = gets (lookupBitmapPriority d)"
  unfolding getHighestPrio_def
  by (fastforce simp: gets_def get_bind_apply lookupBitmapPriority_def bitmap_fun_defs)

locale TcbAcc_R =
  (* these versions use word_size_bits and can be made generic *)
  assumes no_fail_loadWord_bits[wp]:
    "\<And>p. no_fail (\<lambda>_. is_aligned p word_size_bits) (loadWord p)"
  assumes no_fail_storeWord_bits:
    "\<And>p w. no_fail (\<lambda>_. is_aligned p word_size_bits) (storeWord p w)"
  assumes prioToL1Index_l1IndexToPrio_or_id:
    "\<And>w w'.
     \<lbrakk> unat (w'::priority) < 2 ^ wordRadix ; w < 2^(size w' - wordRadix) \<rbrakk>
     \<Longrightarrow> prioToL1Index ((l1IndexToPrio w) || w') = w"
  assumes l1IndexToPrio_wordRadix_mask[simp]:
    "\<And>i. l1IndexToPrio i && mask wordRadix = 0"
  assumes dmo_getirq_inv[wp]:
    "\<And>P in_kernel. irq_state_independent_H P \<Longrightarrow> doMachineOp (getActiveIRQ in_kernel) \<lbrace>P\<rbrace>"
  assumes getActiveIRQ_masked:
    "\<And>table in_kernel.
     \<lbrace>\<lambda>s. valid_irq_masks' table (irq_masks s)\<rbrace>
     getActiveIRQ in_kernel
     \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> table irq \<noteq> irqstate.IRQInactive\<rbrace>"
  assumes setObject_update_TCB_corres':
    "\<And>tcb tcb' new_tcb new_tcb' ptr r.
     \<lbrakk>tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb';
      \<forall>(getF, v)\<in>ran tcb_cap_cases. getF new_tcb = getF tcb;
      \<forall>(getF, v)\<in>ran tcb_cte_cases. getF new_tcb' = getF tcb';
      tcbSchedPrev new_tcb' = tcbSchedPrev tcb';
      tcbSchedNext new_tcb' = tcbSchedNext tcb'; \<And>d p. inQ d p new_tcb' = inQ d p tcb';
      tcbInReleaseQueue new_tcb' = tcbInReleaseQueue tcb'; r () ()\<rbrakk>
     \<Longrightarrow> corres r (ko_at (TCB tcb) ptr) (ko_at' tcb' ptr)
               (set_object ptr (TCB new_tcb)) (setObject ptr new_tcb')"
  assumes tcb_at'_cross:
    "\<And>(s::det_state) s' ptr. \<lbrakk>pspace_relation (kheap s) (ksPSpace s'); tcb_at' ptr s'\<rbrakk> \<Longrightarrow> tcb_at ptr s"
  assumes setObject_tcb_refs'[wp]:
    "\<And>P (s::det_state) t v.
     \<lbrace>\<lambda>s. P (global_refs' s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (global_refs' s)\<rbrace>"
  assumes zobj_refs'_capRange:
    "\<And>s cap. s \<turnstile>' cap \<Longrightarrow> zobj_refs' cap \<subseteq> capRange cap"
  assumes pspace_relation_update_tcbs:
    "\<And>s s' x tcb tcb' otcb otcb'.
     \<lbrakk> pspace_relation s s'; s x = Some (TCB otcb); s' x = Some (KOTCB otcb');
       tcb_relation tcb tcb' \<rbrakk>
     \<Longrightarrow> pspace_relation (s(x \<mapsto> TCB tcb)) (s'(x \<mapsto> KOTCB tcb'))"
  assumes prioToL1Index_bit_set: (* (* FIXME arch-split: artificially fixed to machine_word *) *)
    "\<And>p::priority. (2 ^ prioToL1Index p :: machine_word) !! prioToL1Index p"
  assumes prioL2Index_bit_set:
    "\<And>p::priority. ((2::machine_word) ^ unat (ucast p && (mask wordRadix :: machine_word)))
                   !! unat (p && mask wordRadix)"
  assumes invertL1Index_eq_cancelD:
    "\<And>i j. \<lbrakk>invertL1Index i = invertL1Index j; i < l2BitmapSize; j < l2BitmapSize\<rbrakk> \<Longrightarrow> i = j"
  assumes prioToL1Index_bit_not_set: (* (* FIXME arch-split: artificially fixed to machine_word *) *)
    "\<And>p::priority. \<not> (~~ 2 ^ prioToL1Index p :: machine_word) !! prioToL1Index p"
  assumes prioToL1Index_complement_nth_w2p:
    "\<And>(p::priority) (p'::priority).
     (~~ 2 ^ prioToL1Index p :: machine_word) !! prioToL1Index p'
     = (prioToL1Index p \<noteq> prioToL1Index p')"
  assumes prioToL1Index_size[simp]:
    "\<And>w. prioToL1Index w < l2BitmapSize"
  assumes pspace_dom_dom:
    "\<And>ps. dom ps \<subseteq> pspace_dom ps"

(* isHighestPrio_def' is a cleaner version of isHighestPrio_def *)
lemma isHighestPrio_def':
  "isHighestPrio d p = gets (\<lambda>s. ksReadyQueuesL1Bitmap s d = 0 \<or> lookupBitmapPriority d s \<le> p)"
  unfolding isHighestPrio_def bitmap_fun_defs getHighestPrio_def'
  by monad_eq

lemma getHighestPrio_inv[wp]:
  "\<lbrace> P \<rbrace> getHighestPrio d \<lbrace>\<lambda>_. P \<rbrace>"
  unfolding bitmap_fun_defs by simp

lemma valid_bitmapQ_bitmapQ_simp:
  "valid_bitmapQ s \<Longrightarrow> bitmapQ d p s = (\<not> tcbQueueEmpty (ksReadyQueues s (d, p)))"
  by (simp add: valid_bitmapQ_def)

lemma bitmapQ_no_L1_orphansD:
  "\<lbrakk> bitmapQ_no_L1_orphans s ; ksReadyQueuesL1Bitmap s d !! i \<rbrakk>
  \<Longrightarrow> ksReadyQueuesL2Bitmap s (d, invertL1Index i) \<noteq> 0 \<and> i < l2BitmapSize"
 unfolding bitmapQ_no_L1_orphans_def by simp

crunch setThreadState, threadSet
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and reply_at'[wp]: "\<lambda>s. P (reply_at' p s)"
  and tcb_at'[wp]: "\<lambda>s. P (tcb_at' p s)"
  and obj_at'_reply[wp]: "\<lambda>s. P (obj_at' (Q :: reply \<Rightarrow> bool) p s)"
  and obj_at'_ep[wp]: "\<lambda>s. P (obj_at' (Q :: endpoint \<Rightarrow> bool) p s)"
  and obj_at'_ntfn[wp]: "\<lambda>s. P (obj_at' (Q :: notification \<Rightarrow> bool) p s)"
  and obj_at'_sc[wp]: "\<lambda>s. Q (obj_at' (P :: sched_context \<Rightarrow> bool) p s)"
  (wp: crunch_wps set_tcb'.set_preserves_some_obj_at')

crunch tcbSchedDequeue, tcbSchedEnqueue
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  (wp: crunch_wps)

crunch tcbSchedDequeue, tcbSchedEnqueue, tcbReleaseRemove
  for obj_at'_reply[wp]: "\<lambda>s. P (obj_at' (Q :: reply \<Rightarrow> bool) p s)"
  and obj_at'_ep[wp]: "\<lambda>s. P (obj_at' (Q :: endpoint \<Rightarrow> bool) p s)"
  and obj_at'_ntfn[wp]: "\<lambda>s. P (obj_at' (Q :: notification \<Rightarrow> bool) p s)"
  and obj_at'_sc[wp]: "\<lambda>s. Q (obj_at' (P :: sched_context \<Rightarrow> bool) p s)"
  (wp: crunch_wps)

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
  by (clarsimp simp: tcb_cte_cases_def gen_objBits_simps tcb_cte_cases_neqs)

lemma valid_tcb'_tcbState_update:
  "valid_tcb' tcb s \<Longrightarrow> valid_tcb' (tcbState_update (\<lambda>_. st) tcb) s"
  by (clarsimp simp: valid_tcb'_def tcb_cte_cases_def gen_objBits_simps
                     tcb_cte_cases_neqs)

definition valid_tcbs' :: "kernel_state \<Rightarrow> bool" where
  "valid_tcbs' s' \<equiv> \<forall>ptr tcb. ksPSpace s' ptr = Some (KOTCB tcb) \<longrightarrow> valid_tcb' tcb s'"

lemma valid_objs'_valid_tcbs'[elim!]:
  "valid_objs' s \<Longrightarrow> valid_tcbs' s"
  by (auto simp: valid_objs'_def valid_tcbs'_def valid_obj'_def split: kernel_object.splits)

lemma invs'_valid_tcbs'[elim!]:
  "invs' s \<Longrightarrow> valid_tcbs' s"
  by (fastforce del: valid_objs'_valid_tcbs' intro: valid_objs'_valid_tcbs')

lemma valid_tcbs'_maxDomain:
  "\<And>s t. \<lbrakk> valid_tcbs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t s"
  by (clarsimp simp: valid_tcbs'_def obj_at'_def valid_tcb'_def)

lemmas valid_objs'_maxDomain = valid_tcbs'_maxDomain[OF valid_objs'_valid_tcbs']

lemma valid_tcbs'_maxPriority:
  "\<And>s t. \<lbrakk> valid_tcbs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t s"
  by (clarsimp simp: valid_tcbs'_def obj_at'_def valid_tcb'_def)

lemmas valid_objs'_maxPriority = valid_tcbs'_maxPriority[OF valid_objs'_valid_tcbs']

lemma valid_tcbs'_obj_at':
  assumes "valid_tcbs' s"
          "tcb_at' t s"
          "\<And>tcb. ko_at' tcb t s \<Longrightarrow> valid_tcb' tcb s \<Longrightarrow> R s tcb"
  shows "obj_at' (R s) t s"
  using assms
  by (clarsimp simp add: valid_tcbs'_def ran_def typ_at'_def
                         ko_wp_at'_def valid_obj'_def valid_tcb'_def obj_at'_def)

(* same derivation on all architectures *)
lemma (in Arch) update_valid_tcb'[simp]:
  "\<And>f. valid_tcb' tcb (ksReleaseQueue_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReprogramTimer_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueuesL1Bitmap_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueuesL2Bitmap_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueues_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksSchedulerAction_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksDomainTime_update f s) = valid_tcb' tcb s"
  by (auto simp: valid_tcb'_def valid_bound_obj'_def opt_tcb_at'_def valid_arch_tcb'_def
          split: option.splits thread_state.splits none_top_split)

lemma update_tcbInReleaseQueue_False_valid_tcb'[simp]:
  "valid_tcb' (tcbInReleaseQueue_update a tcb) s = valid_tcb' tcb s"
  by (auto simp: valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs gen_objBits_simps)

requalify_facts Arch.update_valid_tcb'
lemmas [simp] = update_valid_tcb'

lemma update_valid_tcbs'[simp]:
  "\<And>f. valid_tcbs' (ksReleaseQueue_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReprogramTimer_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueuesL1Bitmap_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueuesL2Bitmap_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueues_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksSchedulerAction_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksDomainTime_update f s) = valid_tcbs' s"
  by (simp_all add: valid_tcbs'_def)

lemma doMachineOp_irq_states':
  assumes masks: "\<And>P. \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"
  shows "\<lbrace>valid_irq_states'\<rbrace> doMachineOp f \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wpsimp
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

context TcbAcc_R begin

lemma doMachineOp_getActiveIRQ_IRQ_active:
  "\<lbrace>valid_irq_states'\<rbrace>
   doMachineOp (getActiveIRQ in_kernel)
   \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive\<rbrace>"
  apply (rule hoare_lift_Pf3[where f="ksInterruptState"])
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

end (* TcbAcc_R *)

lemmas doMachineOp_obj_at = doMachineOp_obj_at'

lemma updateObject_tcb_inv:
  "\<lbrace>P\<rbrace> updateObject (obj::tcb) ko p q n \<lbrace>\<lambda>rv. P\<rbrace>"
  by simp (rule updateObject_default_inv)

lemma (in TcbAcc_R) setObject_update_TCB_corres:
  "\<lbrakk>tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb';
     \<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb;
     \<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb';
     tcbSchedPrev new_tcb' = tcbSchedPrev tcb'; tcbSchedNext new_tcb' = tcbSchedNext tcb';
     \<And>d p. inQ d p new_tcb' = inQ d p tcb'; tcbInReleaseQueue new_tcb' = tcbInReleaseQueue tcb';
     r () ()\<rbrakk> \<Longrightarrow>
   corres r
     (\<lambda>s. get_tcb ptr s = Some tcb) (\<lambda>s'. (tcb', s') \<in> fst (getObject ptr s'))
     (set_object ptr (TCB new_tcb)) (setObject ptr new_tcb')"
  apply (rule corres_guard_imp)
    apply (erule (4) setObject_update_TCB_corres'; fastforce)
   apply (clarsimp simp: getObject_def in_monad split_def obj_at'_def
                         loadObject_default_def gen_objBits_simps in_magnitude_check
                  dest!: readObject_misc_ko_at')+
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

lemma threadGet_corres':
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> r (f tcb) (f' tcb')"
  shows
    "t = t' \<Longrightarrow>
     corres r (tcb_at t and pspace_aligned and pspace_distinct) \<top>
       (thread_get f t) (threadGet f' t')"
  apply (simp add: thread_get_def threadGet_getObject)
  apply (rule corres_split_skip)
     apply wpsimp+
   apply (rule getObject_TCB_corres)
  apply (simp add: x)
  done

lemmas threadGet_corres = threadGet_corres'[OF _ refl]

lemmas get_tcb_obj_ref_corres'
  = threadGet_corres'[where 'a="obj_ref option", folded get_tcb_obj_ref_def]

lemmas get_tcb_obj_ref_corres = get_tcb_obj_ref_corres'[OF _ refl]

lemma threadGet_inv [wp]: "\<lbrace>P\<rbrace> threadGet f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: threadGet_def getObject_tcb_inv | wp)+

lemma ball_tcb_cte_casesI:
  "\<lbrakk> P (tcbCTable, tcbCTable_update);
     P (tcbVTable, tcbVTable_update);
     P (tcbIPCBufferFrame, tcbIPCBufferFrame_update);
     P (tcbFaultHandler, tcbFaultHandler_update);
     P (tcbTimeoutHandler, tcbTimeoutHandler_update) \<rbrakk>
    \<Longrightarrow> \<forall>x \<in> ran tcb_cte_cases. P x"
  by (simp add: tcb_cte_cases_def tcb_cte_cases_neqs)

lemma all_tcbI:
  "\<lbrakk> \<And>a b c d e f g h i j k l m n p q r s t u. P (Thread a b c d e f g h i j k l m n p q r s t u) \<rbrakk>
   \<Longrightarrow> \<forall>tcb. P tcb"
  by (rule allI, case_tac tcb, simp)

context TcbAcc_R begin

lemma threadset_corresT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> tcb_relation (f tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (f' tcb) = getF tcb"
  assumes sched_pointers: "\<And>tcb. tcbSchedPrev (f' tcb) = tcbSchedPrev tcb"
                          "\<And>tcb. tcbSchedNext (f' tcb) = tcbSchedNext tcb"
  assumes flags: "\<And>d p tcb'. inQ d p (f' tcb') = inQ d p tcb'"
                 "\<And>tcb'. tcbInReleaseQueue (f' tcb') = tcbInReleaseQueue tcb'"
  shows
    "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
       (thread_set f t) (threadSet f' t)"
  apply (simp add: thread_set_def threadSet_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getObject_TCB_corres])
      apply (rule setObject_update_TCB_corres')
              apply (erule x)
             apply (rule y)
            apply (fastforce simp: bspec_split [OF spec [OF z]])
           apply (fastforce simp: sched_pointers)
          apply (fastforce simp: sched_pointers)
         apply (fastforce simp: flags)
        apply (fastforce simp: flags)
       apply fastforce
      apply wp+
   apply (fastforce dest: get_tcb_SomeD simp: tcb_at_def obj_at_def)
  apply simp
  done

lemmas threadset_corres =
    threadset_corresT[OF _ _ all_tcbI, OF _ ball_tcb_cap_casesI ball_tcb_cte_casesI]

lemma threadSet_corres_noopT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> tcb_relation tcb (fn tcb')"
  assumes y: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (fn tcb) = getF tcb"
  assumes s: "\<forall>tcb'. tcbSchedPrev (fn tcb') = tcbSchedPrev tcb'"
             "\<forall>tcb'. tcbSchedNext (fn tcb') = tcbSchedNext tcb'"
  assumes f: "\<And>d p tcb'. inQ d p (fn tcb') = inQ d p tcb'"
             "\<And>tcb'. tcbInReleaseQueue (fn tcb') = tcbInReleaseQueue tcb'"
  shows
    "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
       (return v) (threadSet fn t)"
proof -
  have S: "\<And>t s. tcb_at t s \<Longrightarrow> return v s = (thread_set id t >>= (\<lambda>x. return v)) s"
    apply (clarsimp simp: tcb_at_def)
    apply (clarsimp simp: return_def thread_set_def gets_the_def assert_def
                          assert_opt_def simpler_gets_def set_object_def get_object_def
                          put_def get_def bind_def
                   dest!: get_tcb_SomeD)
    apply (subgoal_tac "(kheap s)(t \<mapsto> TCB tcb) = kheap s", simp)
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
             apply (fastforce simp: s)
            apply (fastforce simp: s)
           apply (fastforce simp: f)
          apply (fastforce simp: f)
         apply wpsimp+
    done
qed

lemmas threadSet_corres_noop =
    threadSet_corres_noopT[OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

lemma threadSet_corres_noop_splitT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> tcb_relation tcb (fn tcb')"
  assumes y: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (fn tcb) = getF tcb"
  assumes s: "\<forall>tcb'. tcbSchedPrev (fn tcb') = tcbSchedPrev tcb'"
             "\<forall>tcb'. tcbSchedNext (fn tcb') = tcbSchedNext tcb'"
  assumes f: "\<And>d p tcb'. inQ d p (fn tcb') = inQ d p tcb'"
             "\<And>tcb'. tcbInReleaseQueue (fn tcb') = tcbInReleaseQueue tcb'"
  assumes z: "corres r P Q' m m'"
  assumes w: "\<lbrace>P'\<rbrace> threadSet fn t \<lbrace>\<lambda>x. Q'\<rbrace>"
  shows
    "corres r (tcb_at t and pspace_aligned and pspace_distinct and P) P'
       m (threadSet fn t >>= (\<lambda>rv. m'))"
  apply (rule corres_guard_imp)
    apply (subst return_bind[symmetric])
    apply (rule corres_split_nor[OF threadSet_corres_noopT])
            apply (simp add: x)
           apply (rule y)
          apply (fastforce simp: s)
         apply (fastforce simp: s)
        apply (fastforce simp: f)
       apply (fastforce simp: f)
      apply (rule z)
     apply (wp w)+
   apply simp
  apply simp
  done

lemmas threadSet_corres_noop_split =
    threadSet_corres_noop_splitT [OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

end (* TcbAcc_R *)

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
                         obj_at'_def gen_objBits_simps in_magnitude_check)
   apply fastforce
  apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                        obj_at'_def gen_objBits_simps in_magnitude_check bind_def)
  done

lemma setObject_tcb_mdb'[wp]:
  "\<lbrace> valid_mdb' and
     obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t\<rbrace>
  setObject t (v :: tcb)
  \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def pred_conj_def
  by (rule setObject_tcb_ctes_of)

lemma setObject_tcb_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' (tcbState v) \<union> tcb_bound_refs' v))\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp setObject_state_refs_of',
      simp_all add: gen_objBits_simps fun_upd_def)

lemma setObject_tcb_ifunsafe':
  "\<lbrace>if_unsafe_then_cap' and obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t\<rbrace>
   setObject t (v :: tcb)
   \<lbrace>\<lambda>_. if_unsafe_then_cap'\<rbrace>"
  unfolding pred_conj_def
  apply (rule setObject_ifunsafe')
    apply (clarsimp simp: updateObject_default_def in_monad obj_at'_def
                          in_magnitude_check gen_objBits_simps prod_eq_iff)
    apply fastforce
   apply (clarsimp simp: updateObject_default_def bind_def in_monad)
  apply wp
  done

lemma (in TcbAcc_R) setObject_tcb_valid_globals'[wp]:
  "\<lbrace>valid_global_refs' and
    obj_at' (\<lambda>tcb. (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb = getF v)) t\<rbrace>
   setObject t (v :: tcb)
   \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  unfolding pred_conj_def valid_global_refs'_def
  apply (rule hoare_lift_Pf2 [where f="global_refs'"])
   apply (rule hoare_lift_Pf2 [where f="gsMaxObjectSize"])
    apply (rule setObject_ctes_of)
     apply (clarsimp simp: updateObject_default_def in_monad obj_at'_def
                           in_magnitude_check gen_objBits_simps prod_eq_iff)
     apply fastforce
    apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                          obj_at'_def gen_objBits_simps in_magnitude_check bind_def)
   apply (wp | wp setObject_ksPSpace_only updateObject_default_inv | simp)+
  done

lemma threadSet_pspace_no_overlap' [wp]:
  "\<lbrace>pspace_no_overlap' w s\<rbrace> threadSet f t \<lbrace>\<lambda>rv. pspace_no_overlap' w s\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_pspace_no_overlap' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

context TcbAcc_R begin

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

end

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
  assumes z': "\<forall>tcb. (P \<longrightarrow> Q1 (tcbState tcb)) \<longrightarrow>
                      (\<forall>rptr. (tcbState tcb = BlockedOnReply rptr)
                                 \<longrightarrow> (tcbState (F tcb) = BlockedOnReply rptr))"
  assumes v1: "\<forall>tcb. (P \<longrightarrow> Q2 (tcbBoundNotification tcb)) \<longrightarrow>
                      (\<forall>s. valid_bound_ntfn' (tcbBoundNotification tcb) s
                              \<longrightarrow> valid_bound_ntfn' (tcbBoundNotification (F tcb)) s)"
  assumes v2: "\<forall>tcb. (P \<longrightarrow> Q3 (tcbSchedContext tcb)) \<longrightarrow>
                      (\<forall>s. valid_bound_sc' (tcbSchedContext tcb) s
                              \<longrightarrow> valid_bound_sc' (tcbSchedContext (F tcb)) s)"
  assumes v3: "\<forall>tcb. (P \<longrightarrow> Q4 (tcbYieldTo tcb)) \<longrightarrow>
                      (\<forall>s. valid_bound_sc' (tcbYieldTo tcb) s
                              \<longrightarrow> valid_bound_sc' (tcbYieldTo (F tcb)) s)"
  assumes v4: "\<forall>tcb. (P \<longrightarrow> Q5 (tcbSchedPrev tcb)) \<longrightarrow>
                      (\<forall>s. opt_tcb_at' (tcbSchedPrev tcb) s
                              \<longrightarrow> opt_tcb_at' (tcbSchedPrev (F tcb)) s)"
  assumes v5: "\<forall>tcb. (P \<longrightarrow> Q6 (tcbSchedNext tcb)) \<longrightarrow>
                      (\<forall>s. opt_tcb_at' (tcbSchedNext tcb) s
                              \<longrightarrow> opt_tcb_at' (tcbSchedNext (F tcb)) s)"
  assumes y: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
                      \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes u: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes w: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  assumes w': "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  assumes f: "\<forall>tcb. tcbFlags tcb && ~~ tcbFlagMask = 0 \<longrightarrow> tcbFlags (F tcb) && ~~ tcbFlagMask = 0"
  assumes v': "\<forall>tcb s. valid_arch_tcb' (tcbArch tcb) s \<longrightarrow> valid_arch_tcb' (tcbArch (F tcb)) s"
  shows
  "\<lbrace>valid_pspace' and (\<lambda>s. P \<longrightarrow> st_tcb_at' Q1 t s \<and> bound_tcb_at' Q2 t s \<and>
                                 bound_sc_tcb_at' Q3 t s \<and> bound_yt_tcb_at' Q4 t s \<and>
                                 obj_at' (\<lambda>tcb. Q5 (tcbSchedPrev tcb)) t s \<and>
                                 obj_at' (\<lambda>tcb. Q6 (tcbSchedNext tcb)) t s)\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def threadSet_def)
  apply (rule hoare_pre,
         wpsimp wp: setObject_tcb_valid_objs setObject_tcb_valid_replies'
                    getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def pred_tcb_at'_def)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def
                            bspec_split [OF spec [OF x]]
                            split_paired_Ball y u w v1 v2 v3 v4 v5 w' v' f)
  apply (fastforce simp: eq_commute[where b="tcbState obj" for obj] z')
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
  "{r. (r \<in> tcb_st_refs_of' (tcbState tcb) \<or> r \<in> tcb_bound_refs' tcb)
       \<and> (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)}
   = tcb_bound_refs' tcb"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits tcb.splits)

lemma threadSet_state_refs_of'_helper'[simp]:
  "{r. (r \<in> tcb_st_refs_of' (tcbState tcb) \<or> r \<in> tcb_bound_refs' tcb)
       \<and> (snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo)}
   = tcb_st_refs_of' (tcbState tcb)"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits tcb.splits)

lemma threadSet_state_refs_of'_helper_TCBBound[simp]:
  "{r. (r \<in> tcb_st_refs_of' (tcbState obj) \<or> r \<in> tcb_bound_refs' obj) \<and> snd r = TCBBound}
  = get_refs TCBBound (tcbBoundNotification obj)"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_state_refs_of'_helper_TCBSchedContext[simp]:
  "{r. (r \<in> tcb_st_refs_of' (tcbState obj) \<or> r \<in> tcb_bound_refs' obj) \<and> snd r = TCBSchedContext}
  = get_refs TCBSchedContext (tcbSchedContext obj)"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_state_refs_of'_helper_TCBYieldTo[simp]:
  "{r. (r \<in> tcb_st_refs_of' (tcbState obj) \<or> r \<in> tcb_bound_refs' obj) \<and> snd r = TCBYieldTo}
  = get_refs TCBYieldTo (tcbYieldTo obj)"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma state_refs_of'_upd_helper[simp]:
  "(state_refs_of' s)
   (ptr :=
     {r \<in> state_refs_of' s ptr. snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
     \<union> ({r \<in> state_refs_of' s ptr. snd r = TCBBound}
        \<union> {r \<in> state_refs_of' s ptr. snd r = TCBSchedContext}
        \<union> {r \<in> state_refs_of' s ptr. snd r = TCBYieldTo}))
   = state_refs_of' s"
  by (force simp: state_refs_of'_def split: option.splits intro!: ext)

lemma threadSet_state_refs_of'T_P:
  assumes x: "\<forall>tcb. (P' \<longrightarrow> Q (tcbState tcb)) \<longrightarrow>
                     tcb_st_refs_of' (tcbState (F tcb))
                       = f' (tcb_st_refs_of' (tcbState tcb))"
  assumes y: "\<forall>tcb. (P' \<longrightarrow> Q' tcb) \<longrightarrow>
                     tcb_bound_refs' (F tcb)
                       = g' (tcb_bound_refs' tcb)"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := f' {r \<in> state_refs_of' s t. snd r \<notin> {TCBBound, TCBSchedContext, TCBYieldTo}}
                                    \<union> g' {r \<in> state_refs_of' s t. snd r \<in> {TCBBound, TCBSchedContext, TCBYieldTo}}))
              \<and> (P' \<longrightarrow> st_tcb_at' Q t s \<and> obj_at' Q' t s)  \<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def pred_tcb_at'_def
                 elim!: rsubst[where P=P] del: ext intro!: ext)
  apply (cut_tac s=s and p=t and 'a=tcb in ko_at_state_refs_ofD')
   apply (simp add: obj_at'_def)
  apply (clarsimp simp: x y)
  done

lemmas threadSet_state_refs_of'T =
    threadSet_state_refs_of'T_P [where P'=False, simplified]

lemmas threadSet_state_refs_of' =
    threadSet_state_refs_of'T [OF all_tcbI all_tcbI]

lemma state_refs_of'_helper[simp]:
  "{r \<in> state_refs_of' s t. snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
   \<union> {r \<in> state_refs_of' s t. snd r = TCBBound}
   \<union> {r \<in> state_refs_of' s t. snd r = TCBSchedContext}
   \<union> {r \<in> state_refs_of' s t. snd r = TCBYieldTo}
   = state_refs_of' s t"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
          split: thread_state.splits reftype.splits option.splits)

lemma threadSet_cte_wp_at'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (F tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. P' (cte_wp_at' P p s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P' (cte_wp_at' P p s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (rule bind_wp [where Q'="\<lambda>rv s. P' (cte_wp_at' P p s) \<and> obj_at' ((=) rv) t s"])
   apply (rename_tac tcb)
   apply (rule setObject_cte_wp_at2')
    apply (clarsimp simp: updateObject_default_def in_monad gen_objBits_simps
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
  \<Longrightarrow> threadSet f tptr \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wpsimp wp: hoare_vcg_ex_lift threadSet_cte_wp_at'
           simp: ex_nonz_cap_to'_def tcb_cte_cases_def tcb_cte_cases_neqs)

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

lemma threadSet_valid_bitmapQ[wp]:
  "\<lbrace> valid_bitmapQ \<rbrace> threadSet f t \<lbrace> \<lambda>rv. valid_bitmapQ \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def gen_objBits_simps)+

lemma threadSet_valid_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> threadSet f t \<lbrace> \<lambda>rv. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def gen_objBits_simps)+

lemma threadSet_valid_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> threadSet f t \<lbrace> \<lambda>rv. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def gen_objBits_simps)+

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

context TcbAcc_R begin

crunch setThreadState, setBoundNotification
  for valid_arch' [wp]: valid_arch_state'
  (simp: unless_def crunch_simps wp: crunch_wps)

end (* TcbAcc_R *)

crunch threadSet
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation threadSet: typ_at_all_props' "threadSet tptr f"
  by typ_at_props'

crunch threadSet
  for irq_states'[wp]: valid_irq_states'

crunch threadSet
  for pspace_domain_valid[wp]: "pspace_domain_valid"

lemma threadSet_obj_at'_really_strongest:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> obj_at' (\<lambda>obj. if t = t' then P (f obj) else P obj)
    t' s\<rbrace> threadSet f t \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_strongest)
   apply (subst simp_thms(32)[symmetric], rule hoare_vcg_disj_lift)
    apply (rule hoare_post_imp[where Q'="\<lambda>rv s. \<not> tcb_at' t s \<and> tcb_at' t s"])
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
  apply (simp add: obj_at'_real_def typ_at'_def ko_wp_at'_def gen_objBits_simps)
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

lemma threadSet_obj_at'_no_state:
  assumes "\<And>tcb. P' (f tcb) = P' tcb"
  shows   "threadSet f t \<lbrace>\<lambda>s. P (obj_at' P' t' s)\<rbrace>"
proof -
  have pos: "\<And>t' t. threadSet f t \<lbrace>obj_at' P' t'\<rbrace>"
    apply (wpsimp wp: threadSet_obj_at'_strongish)
    apply (insert assms)
    apply clarsimp
    done
  show ?thesis
    apply (rule_tac P=P in P_bool_lift)
     apply (rule pos)
    apply (rule_tac Q'="\<lambda>_ s. \<not> tcb_at' t' s \<or> obj_at' (\<lambda>tcb. \<not> P' tcb) t' s"
                 in hoare_post_imp)
     apply (clarsimp simp: obj_at'_def)
    apply (simp add: typ_at_tcb'[symmetric])
    apply (wpsimp wp: hoare_convert_imp)
    apply (clarsimp simp: not_obj_at' assms elim!: obj_at'_weakenE)
    done
qed

lemma threadSet_pred_tcb_no_state:
  assumes "\<And>tcb. proj (tcb_to_itcb' (f tcb)) = proj (tcb_to_itcb' tcb)"
  shows   "threadSet f t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wpsimp wp: threadSet_obj_at'_no_state simp: pred_tcb_at'_def assms)

lemma threadSet_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s
        \<and> (tcb_at' t s \<longrightarrow> obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF (f t)) t s)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (wpsimp wp: setObject_tcb_mdb' getTCB_wp simp: threadSet_def obj_at'_def)
  apply fastforce
  done

lemma threadSet_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> threadSet F t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  by (intro hoare_vcg_all_lift hoare_vcg_disj_lift; wp)

lemma threadSet_invs_trivial_helper[simp]:
  "{r \<in> state_refs_of' s t. snd r \<noteq> TCBBound \<and> snd r \<noteq> TCBSchedContext \<and> snd r \<noteq> TCBYieldTo}
    \<union> {r \<in> state_refs_of' s t. (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)}
   = state_refs_of' s t"
  by auto

lemma threadSet_valid_dom_schedule':
  "\<lbrace> valid_dom_schedule'\<rbrace> threadSet F t \<lbrace>\<lambda>_. valid_dom_schedule'\<rbrace>"
  unfolding threadSet_def valid_dom_schedule'_def
  by (wp setObject_ksDomSchedule_inv hoare_Ball_helper)

lemma threadSet_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb :: tcb. ko_at' tcb t s \<longrightarrow> P (set_obj' t (f tcb) s)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: setObject_tcb_wp set_tcb'.getObject_wp)
  done

lemma threadSet_sched_pointers:
  "\<lbrakk>\<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb; \<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb\<rbrakk>
   \<Longrightarrow> threadSet F tcbPtr \<lbrace>\<lambda>s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: opt_map_def obj_at'_def elim: rsubst2[where P=P])
  done

lemma threadSet_valid_sched_pointers:
  "\<lbrakk>\<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb; \<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb;
    \<And>tcb. tcbInReleaseQueue (F tcb) = tcbInReleaseQueue tcb;
    \<And>tcb. tcbQueued (F tcb) = tcbQueued tcb; \<And>tcb. tcbState (F tcb) = tcbState tcb\<rbrakk>
   \<Longrightarrow> threadSet F tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding valid_sched_pointers_def
  apply (wpsimp wp: hoare_vcg_all_lift threadSet_wp)
  apply (clarsimp simp: opt_pred_def opt_map_def obj_at'_def split: option.splits)
  apply (fastforce dest: spec[where x=tcbPtr])
  done

lemma threadSet_field_inv:
  "(\<And>tcb. f (F tcb) = f tcb) \<Longrightarrow> threadSet F t \<lbrace>\<lambda>s. P (tcbs_of' s |> f)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (fastforce elim!: rsubst[where P=P] simp: opt_map_def obj_at'_def)

lemma threadSet_field_opt_pred:
  "(\<And>tcb. f (F tcb) = f tcb) \<Longrightarrow> threadSet F t \<lbrace>\<lambda>s. P (f |< tcbs_of' s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (erule rsubst[where P=P])
  apply (fastforce simp: opt_pred_def opt_map_def obj_at'_def)
  done

lemma (in TcbAcc_R) global'_no_ex_cap:
  "\<lbrakk>valid_global_refs' s; valid_pspace' s\<rbrakk> \<Longrightarrow> \<not> ex_nonz_cap_to' (ksIdleThread s) s"
  apply (clarsimp simp: ex_nonz_cap_to'_def valid_global_refs'_def valid_refs'_def2 valid_pspace'_def)
  apply (drule cte_wp_at_norm', clarsimp)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap', clarsimp)
  apply (clarsimp simp: cte_wp_at'_def dest!: zobj_refs'_capRange, blast)
  done

lemma (in TcbAcc_R) global'_sc_no_ex_cap:
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

(*FIXME arch-split RT*)
lemmas typ_at'_valid_tcb'_lift =
  RISCV64.typ_at'_valid_obj'_lift[where obj="KOTCB tcb" for tcb, unfolded valid_obj'_def, simplified]

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
  apply (rule bind_wp[OF _ get_tcb_sp'])
  apply (wpsimp wp: setObject_tcb_valid_tcbs')
  apply (clarsimp simp: obj_at'_def valid_tcbs'_def)
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
                          loadObject_default_def gen_objBits_simps
                          modify_def split_def updateObject_default_def
                          in_magnitude_check select_f_def omonad_defs obind_def
               split del: if_split
                   split: option.split_asm if_split_asm
                    dest!: P)
    apply (simp add: R map_upd_triv)
    done
qed

crunch asUser
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps)

global_interpretation asUser: typ_at_all_props' "asUser tptr f"
  by typ_at_props'

lemma threadGet_sp:
  "\<lbrace>P\<rbrace> threadGet f ptr \<lbrace>\<lambda>rv s. \<exists>tcb :: tcb. ko_at' tcb ptr s \<and> f tcb = rv \<and> P s\<rbrace>"
  apply (wpsimp wp: threadGet_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma inReleaseQueue_wp:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (\<exists>tcb. ko_at' tcb t s \<and> P (tcbInReleaseQueue tcb) s)\<rbrace>
   inReleaseQueue t
   \<lbrace>P\<rbrace>"
  unfolding inReleaseQueue_def readInReleaseQueue_def
  apply (wpsimp wp: threadGet_wp)
  by (fastforce dest!: threadRead_SomeD simp: obj_at'_def)

lemma asUser_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> asUser t m \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  done

crunch asUser
  for aligned'[wp]: pspace_aligned'
  (simp: crunch_simps wp: crunch_wps)
crunch asUser
  for distinct'[wp]: pspace_distinct'
  (simp: crunch_simps wp: crunch_wps)

crunch asUser
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  (wp: crunch_wps)

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
  by (wp threadSet_state_refs_of'[where g'=id] hoare_drop_imps | simp add: tcb_bound_refs'_def)+


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

crunch asUser
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

lemma asUser_tcbState_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbState tcb)) t'\<rbrace> asUser t m \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbState tcb)) t'\<rbrace>"
  apply (simp add: asUser_def threadGet_def)
  apply (wpsimp wp: getObject_tcb_wp simp: obj_at'_def)
  done

lemma no_fail_asUser[wp]:
  "no_fail \<top> f \<Longrightarrow> no_fail (tcb_at' t) (asUser t f)"
  apply (simp add: asUser_def split_def)
  apply wp
    apply (simp add: no_fail_def)
    apply (wpsimp wp: hoare_drop_imps no_fail_threadGet)+
  done

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
  apply (rule_tac Q'="tcb_at' tcb_ptr" in corres_cross_add_guard)
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
  apply (simp add: isRunnable_def readRunnable_def liftM_def getThreadState_def
             flip: threadGet_def)
  apply (rule bind_eqI, rule ext, rule arg_cong)
  apply (rename_tac state, case_tac state; clarsimp)
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
                        split_def gen_objBits_simps in_magnitude_check)
  done

lemma readRunnable_SomeD:
  "readRunnable t s = Some y \<Longrightarrow> \<exists>tcb. ko_at' tcb t s \<and> y = runnable' (tcbState tcb)"
  apply (clarsimp simp: readRunnable_def)
  apply (drule threadRead_SomeD)
  apply clarsimp
  apply (case_tac "tcbState tcb"; fastforce)
  done

lemmas isRunnable_sp' =
  gets_the_sp[where f="readRunnable tcb_ptr" for tcb_ptr, simplified isRunnable_def[symmetric]]

lemma isRunnable_sp:
  "\<lbrace>Q\<rbrace> isRunnable t \<lbrace>\<lambda>rv s. st_tcb_at' runnable' t s = rv \<and> Q s\<rbrace>"
  by wpsimp

lemma no_ofail_readRunnable[wp]:
  "no_ofail (tcb_at' tcbPtr) (readRunnable tcbPtr)"
  unfolding readRunnable_def
  by wpsimp

lemmas no_fail_isRunnable[wp] =
  no_ofail_gets_the[OF no_ofail_readRunnable, simplified isRunnable_def[symmetric]]

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

lemma getQueue_corres:
  "corres (\<lambda>ls q. (ls = [] \<longleftrightarrow> tcbQueueEmpty q) \<and> (ls \<noteq> [] \<longrightarrow> tcbQueueHead q = Some (hd ls))
                  \<and> queue_end_valid ls q)
     \<top> \<top> (get_tcb_queue qdom prio) (getQueue qdom prio)"
  apply (clarsimp simp: get_tcb_queue_def getQueue_def tcbQueueEmpty_def)
  apply (rule corres_bind_return2)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp])
    apply (rule corres_symb_exec_r[OF _ gets_sp])
      apply clarsimp
      apply (drule state_relation_ready_queues_relation)
      apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                            list_queue_relation_def)
      apply (drule_tac x=qdom in spec)
      apply (drule_tac x=prio in spec)
      apply (fastforce dest: heap_path_head)
     apply wpsimp+
  done

context TcbAcc_R begin

lemma addToBitmap_noop_corres:
  "corres dc \<top> \<top> (return ()) (addToBitmap d p)"
  unfolding addToBitmap_def modifyReadyQueuesL1Bitmap_def getReadyQueuesL1Bitmap_def
            modifyReadyQueuesL2Bitmap_def getReadyQueuesL2Bitmap_def
  by (rule corres_noop)
     (wpsimp simp: state_relation_def)+

lemma addToBitmap_if_null_noop_corres: (* used this way in Haskell code *)
  "corres dc \<top> \<top> (return ()) (if tcbQueueEmpty queue then addToBitmap d p else return ())"
  by (cases "tcbQueueHead queue", simp_all add: addToBitmap_noop_corres)

lemma removeFromBitmap_corres_noop:
  "corres dc \<top> \<top> (return ()) (removeFromBitmap tdom prioa)"
  unfolding removeFromBitmap_def
  by (rule corres_noop)
     (wpsimp simp: bitmap_fun_defs state_relation_def)+

end (* TcbAcc_R *)

crunch addToBitmap, removeFromBitmap
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation addToBitmap: typ_at_all_props' "addToBitmap tdom prio"
  by typ_at_props'

global_interpretation removeFromBitmap: typ_at_all_props' "removeFromBitmap tdom prio"
  by typ_at_props'

lemma pspace_relation_tcb_domain_priority:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); kheap s t = Some (TCB tcb);
    ksPSpace s' t = Some (KOTCB tcb')\<rbrakk>
   \<Longrightarrow> tcbDomain tcb' = tcb_domain tcb \<and> tcbPriority tcb' = tcb_priority tcb"
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=t in bspec, blast)
  apply (clarsimp simp: tcb_relation_cut_def tcb_relation_def)
  done

lemma pspace_relation_tcb_relation:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); kheap s ptr = Some (TCB tcb);
    ksPSpace s' ptr = Some (KOTCB tcb')\<rbrakk>
   \<Longrightarrow> tcb_relation tcb tcb'"
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=ptr in bspec)
   apply (fastforce simp: obj_at_def)
  apply (clarsimp simp: obj_at_def obj_at'_def tcb_relation_cut_def)
  done

lemma threadSet_ksIdleSc[wp]:
  "threadSet f tcbPtr \<lbrace>\<lambda>s. P (ksIdleSC s)\<rbrace>"
  by (wpsimp wp: threadSet_wp)

lemma tcbQueued_update_ctes_of[wp]:
  "threadSet (tcbQueued_update f) t \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_of)

lemma tcbInReleaseQueue_update_ctes_of[wp]:
  "threadSet (tcbInReleaseQueue_update f) t \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_of)

lemma tcbYieldTo_update_ctes_of[wp]:
  "threadSet (tcbYieldTo_update f) t \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_of)

lemma removeFromBitmap_ctes_of[wp]:
  "removeFromBitmap tdom prio \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp simp: bitmap_fun_defs)

crunch tcbQueueRemove, tcbQueuePrepend, tcbQueueAppend, tcbQueueInsert, orderedInsert,
       setReleaseQueue, setQueue, removeFromBitmap
  for sc_replies_relation_projs[wp]: "\<lambda>s. P (scReplies_of s) (replyPrevs_of s)"
  and ghost_relation_projs[wp]: "\<lambda>s. P (gsUserPages s) (gsCNodes s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and ksIdleSC[wp]: "\<lambda>s. P (ksIdleSC s)"
  and ksWorkUnitsCompleted[wp]: "\<lambda>s. P (ksWorkUnitsCompleted s)"
  and ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
  and ksConsumedTime[wp]: "\<lambda>s. P (ksConsumedTime s)"
  and ksCurTime[wp]: "\<lambda>s. P (ksCurTime s)"
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  and ksReprogramTimer[wp]: "\<lambda>s. P (ksReprogramTimer s)"
  (wp: crunch_wps)

lemma set_release_queue_cte_at:
  "set_release_queue queue \<lbrace>\<lambda>s. P (swp cte_at s)\<rbrace>"
  apply wpsimp
  by (clarsimp simp: swp_def cte_wp_at_def)

lemma set_release_queue_new_state:
  "(rv, t) \<in> fst (set_release_queue queue s) \<Longrightarrow> t = s\<lparr>release_queue := queue\<rparr>"
  by (clarsimp simp: in_monad)

lemma set_tcb_queue_projs:
  "set_tcb_queue d p queue
   \<lbrace>\<lambda>s. P (kheap s) (cdt s) (is_original_cap s) (cur_thread s) (idle_thread s) (consumed_time s)
          (cur_time s) (cur_sc s) (reprogram_timer s) (scheduler_action s) (domain_list s)
          (domain_index s) (cur_domain s) (domain_time s) (release_queue s) (machine_state s)
          (interrupt_irq_node s) (interrupt_states s) (arch_state s) (caps_of_state s)
          (work_units_completed s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: set_tcb_queue_def)

lemma set_tcb_queue_cte_at:
  "set_tcb_queue d p queue \<lbrace>\<lambda>s. P (swp cte_at s)\<rbrace>"
  unfolding set_tcb_queue_def
  apply wpsimp
  apply (clarsimp simp: swp_def cte_wp_at_def)
  done

crunch setReprogramTimer, setReleaseQueue, setQueue, removeFromBitmap
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
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"
  (wp: crunch_wps
   simp: crunch_simps tcb_cte_cases_def tcb_bound_refs'_def cur_tcb'_def threadSet_cur
         bitmap_fun_defs valid_machine_state'_def)

context TcbAcc_R begin

crunch tcbReleaseRemove, tcbReleaseEnqueue,
       tcbSchedEnqueue, tcbSchedAppend, tcbSchedDequeue, setQueue
  for pspace_aligned'[wp]: pspace_aligned'
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_bounded'[wp]: pspace_bounded'
  and pspace_canonical'[wp]: pspace_canonical'
  and no_0_obj'[wp]: no_0_obj'
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
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
  and valid_dom_schedule'[wp]: valid_dom_schedule'
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps threadSet_state_refs_of'[where f'=id and g'=id] valid_dom_schedule'_lift
   simp: crunch_simps tcb_cte_cases_def tcb_bound_refs'_def bitmap_fun_defs)

crunch tcbReleaseRemove, tcbReleaseEnqueue
  for valid_machine_state'[wp]: valid_machine_state'
  (wp: crunch_wps)

end (* TcbAcc_R *)

crunch setQueue
  for ksReleaseQueue[wp]: "\<lambda>s'. P (ksReleaseQueue s')"
  (simp: release_queue_relation_def)

lemma ready_queues_disjoint:
  "\<lbrakk>in_correct_ready_q s; ready_qs_distinct s; d \<noteq> d' \<or> p \<noteq> p'\<rbrakk>
   \<Longrightarrow> set (ready_queues s d p) \<inter> set (ready_queues s d' p') = {}"
  apply (clarsimp simp: ready_qs_distinct_def in_correct_ready_q_def)
  apply (rule disjointI)
  apply (frule_tac x=d in spec)
  apply (drule_tac x=d' in spec)
  apply (fastforce simp: vs_all_heap_simps valid_ready_qs_2_def)
  done

defs ksReadyQueues_asrt_def:
  "ksReadyQueues_asrt
     \<equiv> \<lambda>s'. \<forall>d p. \<exists>ts. ready_queue_relation d p ts (ksReadyQueues s' (d, p))
                                            (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                            (inQ d p |< tcbs_of' s')
                       \<and> (\<forall>t \<in> set ts. (tcbQueued |< tcbs_of' s') t \<and> tcb_at' t s')"

lemma ksReadyQueues_asrt_cross:
  "\<lbrakk>ready_queues_relation s s'; pspace_relation (kheap s) (ksPSpace s');
    pspace_aligned s; pspace_distinct s\<rbrakk>
   \<Longrightarrow> ksReadyQueues_asrt s'"
  apply (frule (1) pspace_aligned_cross)
  apply (frule (2) pspace_distinct_cross)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        ksReadyQueues_asrt_def)
  apply (rule_tac x="ready_queues s d p" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule in_ready_q_tcbQueued_eq[THEN iffD1])
    apply (fastforce simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (fastforce simp: in_ready_q_def)
  apply (fastforce intro: aligned'_distinct'_obj_at'I
                    simp: inQ_def opt_pred_def opt_map_def split: option.splits)
  done

defs ksReleaseQueue_asrt_def':
  "ksReleaseQueue_asrt
     \<equiv> \<lambda>s'. \<exists>ts. release_queue_relation_2 ts (ksReleaseQueue s' )
                                          (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                          (tcbInReleaseQueue |< tcbs_of' s')
                 \<and> (\<forall>t \<in> set ts. (tcbInReleaseQueue |< tcbs_of' s') t \<and> tcb_at' t s')"

lemmas ksReleaseQueue_asrt_def = ksReleaseQueue_asrt_def'[simplified release_queue_relation_def]

lemma ksReleaseQueue_asrt_cross:
  "\<lbrakk>release_queue_relation s s'; pspace_relation (kheap s) (ksPSpace s');
    pspace_aligned s; pspace_distinct s\<rbrakk>
   \<Longrightarrow> ksReleaseQueue_asrt s'"
  apply (frule (1) pspace_aligned_cross)
  apply (frule (2) pspace_distinct_cross)
  apply (clarsimp simp: release_queue_relation_def ksReleaseQueue_asrt_def)
  apply (rule_tac x="release_queue s" in exI)
  apply (fastforce intro: aligned'_distinct'_obj_at'I
                    simp: opt_pred_def opt_map_def split: option.splits)
  done

crunch addToBitmap
  for ko_at'[wp]: "\<lambda>s. P (ko_at' ko ptr s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and tcbQueued[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  and ksReadyQueues_asrt[wp]: ksReadyQueues_asrt
  and ksReleaseQueue_asrt[wp]: ksReleaseQueue_asrt
  and st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' Q tcbPtr s)"
  and ready_or_release'[wp]: ready_or_release'
  and valid_tcbs'[wp]: valid_tcbs'
  (simp: bitmap_fun_defs ready_or_release'_def ksReadyQueues_asrt_def ksReleaseQueue_asrt_def)

lemma tcbQueueHead_ksReadyQueues:
  "\<lbrakk>list_queue_relation ts queue nexts prevs;
    \<forall>t. (inQ d p |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty queue \<longrightarrow> (inQ d p |< tcbs_of' s') (the (tcbQueueHead queue))"
  by (fastforce dest: heap_path_head
                simp: tcbQueueEmpty_def list_queue_relation_def queue_end_valid_def)

lemma obj_at'_tcbQueueHead_ksReadyQueues:
  "\<lbrakk>list_queue_relation ts queue nexts prevs;
    \<forall>t. (inQ d p |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts;
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty queue \<longrightarrow> obj_at' (inQ d p) (the (tcbQueueHead queue)) s'"
  by (fastforce dest!: tcbQueueHead_ksReadyQueues intro: aligned'_distinct'_ko_wp_at'I
                 simp: obj_at'_real_def opt_map_def opt_pred_def split: option.splits)

lemma tcbQueueEnd_ksReadyQueues:
  "\<lbrakk>list_queue_relation ts queue nexts prevs;
    \<forall>t. (inQ d p |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty queue \<longrightarrow> (inQ d p |< tcbs_of' s') (the (tcbQueueEnd queue))"
  apply (frule he_ptrs_head_iff_he_ptrs_end)
  by (clarsimp simp: tcbQueueEmpty_def list_queue_relation_def queue_end_valid_def)

lemma obj_at'_tcbQueueEnd_ksReadyQueues:
  "\<lbrakk>list_queue_relation ts queue nexts prevs;
    \<forall>t. (inQ d p |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts;
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty queue \<longrightarrow> obj_at' (inQ d p) (the (tcbQueueEnd queue)) s'"
  by (fastforce dest!: tcbQueueEnd_ksReadyQueues intro: aligned'_distinct'_ko_wp_at'I
                 simp: obj_at'_real_def opt_map_def opt_pred_def split: option.splits)

lemma tcbQueueHead_ksReleaseQueue:
  "\<lbrakk>list_queue_relation ts (ksReleaseQueue s') nexts prevs;
    \<forall>t. (tcbInReleaseQueue |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty (ksReleaseQueue s')
       \<longrightarrow> (tcbInReleaseQueue |< tcbs_of' s') (the (tcbQueueHead (ksReleaseQueue s')))"
  apply (clarsimp simp: tcbQueueEmpty_def list_queue_relation_def)
  apply (prop_tac "ts \<noteq> []"; fastforce dest: heap_path_head simp: obj_at'_real_def)
  done

lemma obj_at'_tcbQueueHead_ksReleaseQueue:
  "\<lbrakk>list_queue_relation ts (ksReleaseQueue s') nexts prevs;
    \<forall>t. (tcbInReleaseQueue |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts;
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty (ksReleaseQueue s')
       \<longrightarrow> obj_at' tcbInReleaseQueue (the (tcbQueueHead (ksReleaseQueue s'))) s'"
  by (fastforce dest!: tcbQueueHead_ksReleaseQueue intro: aligned'_distinct'_ko_wp_at'I
                 simp: obj_at'_real_def inQ_def opt_map_def opt_pred_def split: option.splits)

lemma tcbQueueEnd_ksReleaseQueue:
  "\<lbrakk>list_queue_relation ts (ksReleaseQueue s') nexts prevs;
    \<forall>t. (tcbInReleaseQueue |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty (ksReleaseQueue s')
       \<longrightarrow> (tcbInReleaseQueue |< tcbs_of' s') (the (tcbQueueEnd (ksReleaseQueue s')))"
  apply (frule he_ptrs_head_iff_he_ptrs_end)
  by (clarsimp simp: tcbQueueEmpty_def list_queue_relation_def queue_end_valid_def)

lemma obj_at'_tcbQueueEnd_ksReleaseQueue:
  "\<lbrakk>list_queue_relation ts (ksReleaseQueue s') nexts prevs;
    \<forall>t. (tcbInReleaseQueue |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts;
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty (ksReleaseQueue s')
       \<longrightarrow> obj_at' tcbInReleaseQueue (the (tcbQueueEnd (ksReleaseQueue s'))) s'"
  by (fastforce dest!: tcbQueueEnd_ksReleaseQueue intro: aligned'_distinct'_ko_wp_at'I
                 simp: obj_at'_real_def inQ_def opt_map_def opt_pred_def split: option.splits)

lemma thread_get_exs_valid[wp]:
  "tcb_at tcb_ptr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> thread_get f tcb_ptr \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (clarsimp simp: thread_get_def get_tcb_def gets_the_def gets_def return_def get_def
                     exs_valid_def tcb_at_def bind_def)

lemma threadSet_heap_ls_other:
  "\<lbrace>\<lambda>s. heap_ls (tcbSchedNexts_of s) st ls \<and> t \<notin> set ls\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>_ s. heap_ls (tcbSchedNexts_of s) st ls\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (fastforce dest: heap_path_heap_upd_not_in)

lemma threadSet_prev_queue_head_other:
  "\<lbrace>\<lambda>s. prev_queue_head q (tcbSchedPrevs_of s)
        \<and> (\<exists>ls. heap_ls (tcbSchedNexts_of s) (tcbQueueHead q) ls \<and> t \<notin> set ls)\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>_ s. prev_queue_head q (tcbSchedPrevs_of s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (frule heap_path_head')
  apply (fastforce simp: prev_queue_head_def dest: heap_path_not_Nil hd_in_set)
  done

lemma tcbQueuePrepend_rcorres:
  "rcorres
     (\<lambda>_ s'. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                   \<and> ts' = t # ts \<and> t \<notin> set ts)
             \<and> \<not> is_sched_linked t s')
     (return ts') (tcbQueuePrepend q t)
     (\<lambda>ts' q' _ s'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  supply if_split[split del]
  apply (clarsimp simp: tcbQueuePrepend_def tcbQueueEmpty_def bind_if_distribR)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rule rcorres_if_r_fwd)
   apply clarsimp
   apply (rule rcorres_return)
   apply (clarsimp simp: list_queue_relation_def queue_end_valid_def prev_queue_head_def)
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (clarsimp simp: list_queue_relation_def)
  apply (frule heap_path_not_Nil)
  apply (frule (1) heap_path_head)
  apply (drule (2) heap_ls_prepend[where new=t])
  apply (rule conjI)
   apply (fastforce elim: heap_ls_cong
                    simp: opt_map_upd_triv opt_map_def obj_at'_def return_def split: if_splits)
  apply (clarsimp simp: queue_end_valid_def prev_queue_head_def opt_map_def obj_at'_def return_def
                 split: if_splits)
  done

lemma tcbQueueAppend_rcorres:
  "rcorres
     (\<lambda>_ s'. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                   \<and> t \<notin> set ts \<and> ts' = ts @ [t])
             \<and> \<not> is_sched_linked t s')
     (return ts') (tcbQueueAppend q t)
     (\<lambda>ts' q' _ s'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  supply if_split[split del]
  apply (clarsimp simp: tcbQueueAppend_def tcbQueueEmpty_def bind_if_distribR)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rule rcorres_if_r_fwd)
   apply clarsimp
   apply (rule rcorres_return)
   apply (clarsimp simp: list_queue_relation_def queue_end_valid_def prev_queue_head_def)
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (clarsimp simp: list_queue_relation_def)
  apply (frule heap_path_not_Nil)
  apply (frule (1) heap_path_head)
  apply (drule (2) heap_ls_append[where new=t])
  apply (rule conjI)
   apply (erule heap_ls_cong)
     apply (subst opt_map_upd_triv)
      apply (fastforce simp: opt_map_def obj_at'_def)
     apply (clarsimp simp: queue_end_valid_def)
     apply (subst fun_upd_swap)
      apply fastforce
     apply (simp add: opt_map_upd_triv_None opt_map_upd_triv obj_at'_def)
    apply simp
   apply simp
   apply (force simp: queue_end_valid_def prev_queue_head_def opt_map_def obj_at'_def return_def)
  apply (force simp: queue_end_valid_def prev_queue_head_def opt_map_def obj_at'_def return_def
              split: if_splits)
  done

defs sym_heap_sched_pointers_asrt_def:
  "sym_heap_sched_pointers_asrt \<equiv> sym_heap_sched_pointers"

declare sym_heap_sched_pointers_asrt_def[simp]

lemma tcbQueueInsert_rcorres:
  "rcorres
     (\<lambda>_ s'. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                   \<and> t \<notin> set ts \<and> afterPtr \<in> set ts \<and> afterPtr \<noteq> hd ts
                   \<and> ts' = list_insert_before ts afterPtr t)
             \<and> sym_heap_sched_pointers s')
     (return ts') (do _ \<leftarrow> tcbQueueInsert t afterPtr; return q od)
     (\<lambda>ts' q' _ s'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  supply heap_path_append[simp del]
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  apply (clarsimp simp: tcbQueueInsert_def bind_assoc)
  apply (rule bind_wp[OF _ stateAssert_sp])+
  apply (rule bind_wp[OF _ get_tcb_sp'], rename_tac after_tcb)
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule hoare_ex_pre_conj[simplified conj_commute], rename_tac beforePtr)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (clarsimp simp: list_queue_relation_def return_def)
  apply normalise_obj_at'
  apply (frule heap_ls_distinct)
  apply (frule heap_path_head')
  apply (clarsimp simp: in_set_conv_decomp)
  apply (rename_tac xs ys)
  apply (frule (1) heap_path_sym_heap_non_nil_lookup_prev)
   apply fastforce
  apply (cut_tac xs=xs and ys="afterPtr # ys" and new=t in list_insert_before_distinct)
    apply (fastforce dest: heap_ls_distinct)
   apply fastforce
  apply (drule heap_ls_list_insert_before[where new=t])
     apply (fastforce dest!: split_list)
    apply (fastforce dest: heap_ls_distinct)
   apply fastforce
  apply (drule obj_at'_prop)+
  apply clarsimp
  apply (prop_tac "t \<notin> set xs")
   apply (fastforce dest: heap_ls_distinct simp: opt_map_red split: if_splits)
  apply (prop_tac "beforePtr = last xs", clarsimp simp: obj_at'_def opt_map_def)
  apply clarsimp
  apply (prop_tac "last xs \<noteq> t")
   apply (frule heap_ls_distinct)
   apply (case_tac xs; clarsimp split: if_splits)
  apply clarsimp
  apply (rule conjI)
   apply (fastforce elim!: rsubst3[where P=heap_ls] simp: opt_map_red)
  apply (rule conjI)
   apply (case_tac ys; fastforce simp: queue_end_valid_def)
  apply (case_tac xs; fastforce simp: prev_queue_head_def opt_map_def split: if_splits)
  done

lemma takeWhile_dropWhile_enqueue:
  "\<lbrakk>sorted_wrt (img_ord (\<lambda>t. f t s) (opt_ord_rel R)) ts; \<forall>t \<in> set ts. \<exists>v. f t s = Some v;
    ts \<noteq> []; f (hd ts) s = Some head_val; R val head_val; val \<noteq> head_val; antisymp R; reflp R\<rbrakk>
   \<Longrightarrow> takeWhile (\<lambda>val'. R (the (f val' s)) val) ts
         @ t # dropWhile (\<lambda>val'. R (the (f val' s)) val) ts
       = t # ts"
  apply (prop_tac "\<forall>x \<in> set ts. R head_val (the (f x s))")
   apply (clarsimp, rename_tac x)
   apply (case_tac "x = hd ts")
    apply (fastforce dest: reflpD)
   apply (clarsimp simp: in_set_conv_nth)
   apply (rename_tac i)
   apply (frule_tac i=0 and j=i in sorted_wrt_nth_less)
     apply (fastforce intro: gr0I simp: hd_conv_nth)
    apply fastforce
   apply (drule_tac x="ts ! i" in bspec, fastforce)
   apply (fastforce simp: img_ord_Some' hd_conv_nth)
  apply (subst takeWhile_eq_Nil_iff[THEN iffD2], fastforce simp: antisympD)
  apply (subst dropWhile_eq_self_iff[THEN iffD2], fastforce simp: antisympD)
  apply simp
  done

lemma takeWhile_dropWhile_append:
  "\<lbrakk>sorted_wrt (img_ord (\<lambda>t. f t s) (opt_ord_rel R)) ts; \<forall>t \<in> set ts. \<exists>v. f t s = Some v;
    ts \<noteq> []; R (the (f (last ts) s)) val; transp R; reflp R\<rbrakk>
   \<Longrightarrow> takeWhile (\<lambda>val'. R (the (f val' s)) val) ts
         @ t # dropWhile (\<lambda>val'. R (the (f val' s)) val) ts
       = ts @ [t]"
  apply (prop_tac "\<forall>x \<in> set ts. R (the (f x s)) (the (f (last ts) s))")
   apply (clarsimp, rename_tac x)
   apply (case_tac "x = last ts")
    apply (fastforce dest!: reflpD last_in_set)
   apply (clarsimp simp: in_set_conv_nth last_conv_nth, rename_tac i)
   apply (frule_tac i=i and j="length ts - 1" in sorted_wrt_nth_less)
     apply (fastforce dest: le_neq_implies_less nat_le_Suc_less_imp)
    apply fastforce
   apply (frule_tac x="ts ! (length ts - Suc 0)" in bspec, fastforce)
   apply (drule_tac x="ts ! i" in bspec, fastforce)
   apply (fastforce simp: img_ord_Some')
  apply (subst takeWhile_eq_all_conv[THEN iffD2], fastforce elim: transpE)
  apply (fastforce elim: transpE)
  done

lemma findInsertionPoint_rv_in_set:
  "\<lbrace>\<lambda>s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
         \<and> ts \<noteq> [] \<and> (\<forall>t \<in> set ts. \<exists>v. f t s' = Some v)
         \<and> (\<exists>v. f (hd ts) s' = Some v \<and> R v val) \<and> (\<exists>v. f (last ts) s' = Some v \<and> \<not> R v val)\<rbrace>
   findInsertionPoint val (tcbQueueHead q) f R
   \<lbrace>\<lambda>ptrOpt _. \<exists>ptr. ptrOpt = Some ptr \<and> ptr \<in> set ts \<and> ptr \<noteq> hd ts\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: findInsertionPoint_def)
  apply (rule hoare_pre)
   apply (rule_tac Q4="\<lambda>ptrOpt s'. ?pre s' \<and> (\<exists>ptr. ptrOpt = Some ptr \<and> ptr \<in> set ts)"
                in valid_whileLoop[where P=Q and I=Q for Q, simplified])
     apply clarsimp
    apply (wpsimp wp: hoare_vcg_ex_lift getTCB_wp)
    apply (clarsimp simp: list_queue_relation_def compareVals_def runReaderT_def obind_def)
    apply (prop_tac "ptr \<noteq> last ts")
     apply fastforce
    apply (frule (2) not_last_next_not_None)
    apply (fastforce dest!: heap_ls_next_in_list simp: obj_at'_def opt_map_def)
   apply (clarsimp simp: compareVals_def runReaderT_def obind_def)
  apply (fastforce dest: heap_path_head simp: list_queue_relation_def)
  done

lemma compareVals_not_None:
  "the (runReaderT (compareVals val r f R) s) \<Longrightarrow> \<exists>ptr. r = Some ptr"
  by (fastforce simp: compareVals_def runReaderT_def split: if_splits)

lemma findInsertionPoint_rv_rel:
  "\<lbrakk>reflp R; transp R; totalp R\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
         \<and> sym_heap_sched_pointers s'
         \<and> sorted_wrt (img_ord (\<lambda>t. f t s') (opt_ord_rel R)) ts
         \<and> ts \<noteq> [] \<and> (\<forall>t \<in> set ts. \<exists>v. f t s' = Some v) \<and> (\<forall>t \<in> set ts. tcb_at' t s')
         \<and> (\<exists>v. f (hd ts) s' = Some v \<and> R v val) \<and> (\<exists>v. f (last ts) s' = Some v \<and> \<not> R v val)
         \<and> val' = val\<rbrace>
   findInsertionPoint val (tcbQueueHead q) f R
   \<lbrace>\<lambda>ptrOpt s'. \<exists>ptr. (ptrOpt = Some ptr \<and> ptr \<in> set ts \<and> ptr \<noteq> hd ts)
                      \<and> (\<exists>val'. f ptr s' = Some val' \<and> R val val' \<and> val \<noteq> val')
                      \<and> (\<forall>pfx. (\<exists>sfx. pfx @ ptr # sfx = ts)
                                \<longrightarrow> (\<forall>p \<in> set pfx. R (the (f p s')) val'))\<rbrace>"
  (is "\<lbrakk>_; _; _\<rbrakk> \<Longrightarrow> \<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  supply heap_path_append[simp del]
  apply (rule hoeare_ex_context_conj)
   apply (wpsimp wp: findInsertionPoint_rv_in_set)
  apply (clarsimp simp: findInsertionPoint_def)
  apply (rule hoare_pre)
   apply (rule_tac Q4="\<lambda>ptrOpt s'. ?pre s'
                                   \<and> (\<forall>ptr. (ptrOpt = Some ptr \<and> ptr \<in> set ts)
                                            \<longrightarrow> (\<forall>pfx sfx. pfx @ ptr # sfx = ts
                                                           \<longrightarrow> (\<forall>p \<in> set pfx. R (the (f p s')) val')))"
                in valid_whileLoop[where P=Q and I=Q for Q, simplified])
     apply fastforce
    apply (clarsimp simp: no_ofail_def)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
    apply (wp hoare_vcg_ex_lift getTCB_wp)
    apply (intro impI allI ballI)
    apply (rename_tac tcb ptr pfx p)
    apply (elim conjE)
    apply (frule compareVals_not_None)
    apply simp
    apply (elim exE)
    apply (rename_tac prev_ptr)
    apply (prop_tac "prev_ptr = last pfx")
     apply (clarsimp simp: list_queue_relation_def)
     apply (frule (1) heap_path_sym_heap_non_nil_lookup_prev)
      apply fastforce
     apply (frule_tac p=prev_ptr and p'=ptr in sym_heapD1)
      apply (clarsimp simp: obj_at'_def opt_map_def)
     apply clarsimp
    apply (drule_tac x="last pfx" in spec)
    apply (elim impE)
     apply (case_tac pfx; clarsimp)
    apply (case_tac "p = last pfx")
     apply (force dest!: bspec simp: compareVals_def runReaderT_def obind_def)
    apply (drule_tac x="butlast pfx" in spec)
    apply (elim impE)
     apply (rule_tac x="ptr # sfx" in exI)
     apply (fastforce intro: append_butlast_last_id)
    apply (fastforce simp: not_last_in_set_butlast)
   apply (intro conjI impI allI)
    apply (clarsimp simp: compareVals_def runReaderT_def obind_def split: option.splits)
     apply fastforce
    apply (metis reflpD totalpD)
   apply fastforce
  apply (fastforce dest!: heap_path_sym_heap_non_nil_lookup_prev
                    simp: list_queue_relation_def prev_queue_head_def)
  done

crunch findInsertionPoint
  for inv[wp]: P
  (wp: crunch_wps)

lemma orderedInsert_rcorres:
  assumes rcorres: "\<And>t. rcorres (P t) (gets_the (f t)) (gets_the (f' t)) (\<lambda>rv rv' _ _. rv = rv')"
  assumes nf: "\<And>t. no_ofail (Q t) (f t)"
  assumes nf': "\<And>t s. no_ofail (\<lambda>s'. Q' t s s') (f' t)"
  assumes ord: "reflp R" "totalp R" "transp R" "antisymp R"
  shows
  "rcorres
     (\<lambda>s s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> sorted_wrt (img_ord (\<lambda>t. f t s) (opt_ord_rel R)) ts
             \<and> sym_heap_sched_pointers s' \<and> \<not> is_sched_linked t s'
             \<and> (\<forall>t \<in> set ts. Q t s) \<and> Q t s \<and> t \<notin> set ts \<and> (\<forall>t \<in> set ts. tcb_at' t s')
             \<and> (\<forall>t \<in> set ts. P t s s' \<and> Q' t s s') \<and> P t s s' \<and> Q' t s s')
     (ordered_insert t ts f R) (orderedInsert t q f' R)
     (\<lambda>ts' q' s s'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (insert assms)
  apply (clarsimp simp: ordered_insert_def orderedInsert_def)
  apply (rule rcorres_symb_exec_r[OF stateAssert_inv])
  apply (rule rcorres_split_gets_the_fwd[where rrel="(=)"])
    apply (fastforce intro: rcorres_weaken_pre[OF rcorres])
   apply (fastforce simp: no_ofail_def)
  apply (rename_tac val val')
  apply (rule rcorres_symb_exec_l)
    apply (rule mapM_gets_the_sp')
   apply (rule_tac P="\<lambda>s. \<forall>t \<in> set ts. Q t s" in exs_valid_state_inv)
      apply (wpsimp wp: mapM_wp_inv)
     apply (wpsimp wp: no_fail_mapM_wp)
     apply (fastforce intro: no_ofailD)
    apply (fastforce intro: no_ofailD)
   apply (wpsimp wp: empty_fail_mapM)
  apply (rename_tac vals)
  apply (cases "tcbQueueEmpty q")
   apply clarsimp
   apply (rcorres rcorres: tcbQueuePrepend_rcorres)
   apply (force intro!: exI[where x=ts] dest: list_queue_relation_Nil)
  apply (rule_tac Q="\<lambda>s s'. (\<forall>t \<in> set ts. f t s = f' t s') \<and> vals = map (\<lambda>t. the (f' t s')) ts"
               in rcorres_add_to_pre)
   apply (fastforce dest: rcorres_rrel')
  apply (simp only: if_False bind_assoc haskell_assert_def)
  apply (rule rcorres_assert_r_fwd)
  apply (simp only: K_bind_def bind_assoc fun_app_def)
  apply (rule rcorres_symb_exec_r[OF return_sp]; (solves \<open>wpsimp simp: tcbQueueEmpty_def\<close>)?)
  apply (rule rcorres_symb_exec_r[OF gets_the_sp]; (solves wpsimp)?)
  apply (rule rcorres_symb_exec_r[OF return_sp]; (solves wpsimp)?)
  apply (rule rcorres_if_r_fwd)
   apply (rcorres rcorres: tcbQueuePrepend_rcorres)
   apply clarsimp
   apply (frule list_queue_relation_Nil)
   apply (clarsimp simp: list_queue_relation_def)
   apply (frule (1) heap_path_head)
   apply (fastforce elim!: takeWhile_dropWhile_enqueue)
  apply (rule rcorres_assert_r_fwd)
  apply clarsimp
  apply (rule rcorres_symb_exec_r[OF gets_the_sp]; (solves wpsimp)?)
  apply (rule rcorres_if_r_fwd)
   apply (rcorres rcorres: tcbQueueAppend_rcorres)
   apply clarsimp
   apply (frule list_queue_relation_Nil)
   apply (clarsimp simp: list_queue_relation_def queue_end_valid_def)
   apply (fastforce elim!: takeWhile_dropWhile_append)
  apply (rule_tac Q="\<lambda>_ s'. sorted_wrt (img_ord (\<lambda>t. f' t s') (opt_ord_rel R)) ts"
               in rcorres_add_to_pre)
   apply (rule sorted_wrt_img_ord_eq_lift[THEN iffD1, rotated])
    apply fastforce
   apply (fastforce dest: rcorres_rrel')
  apply (rule_tac F="val' = val" in rcorres_req)
   apply fastforce
  apply clarsimp
  apply (rule_tac Q="\<lambda>ptrOpt s s'. list_queue_relation
                                     ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                   \<and> sym_heap_sched_pointers s' \<and> t \<notin> set ts
                                   \<and> (\<forall>t\<in>set ts. Q' t s s')
                                   \<and> vals = map (\<lambda>t. the (f' t s')) ts
                                   \<and> (\<exists>ptr. ptrOpt = Some ptr \<and> ptr \<in> set ts \<and> ptr \<noteq> hd ts
                                            \<and> (\<exists>v. f' ptr s'= Some v \<and> R val v \<and> val \<noteq> v)
                                            \<and> (\<forall>pfx. (\<exists>sfx. pfx @ ptr # sfx = ts)
                                                      \<longrightarrow> (\<forall>p\<in>set pfx. R (the (f' p s')) val)))"
               in rcorres_symb_exec_r)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
    apply (wpsimp wp: findInsertionPoint_rv_rel[simplified])
    apply (frule list_queue_relation_Nil)
    apply (clarsimp dest!: heap_path_head simp: list_queue_relation_def queue_end_valid_def)
    apply (metis reflpD totalpD)
  apply (rule rcorres_assert_r_fwd)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rcorres rcorres: tcbQueueInsert_rcorres)
  supply map_fst_dropWhile_zip[simp del] map_fst_takeWhile_zip[simp del]
  apply (clarsimp simp: list_queue_relation_def)
  apply (blast intro: takeWhile_dropWhile_insert_list_before no_ofailD dest: heap_ls_distinct)
  done

lemma in_queue_not_head_or_not_tail_length_gt_1:
  "\<lbrakk>tcbPtr \<in> set ls; tcbQueueHead q \<noteq> Some tcbPtr \<or> tcbQueueEnd q \<noteq> Some tcbPtr;
    list_queue_relation ls q nexts prevs\<rbrakk>
   \<Longrightarrow> Suc 0 < length ls"
  by (cases ls; fastforce simp: list_queue_relation_def queue_end_valid_def)

lemma tcbQueueRemove_rcorres:
  "rcorres
     (\<lambda>_ s'. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                   \<and> t \<in> set ts \<and> ts' = removeAll t ts)
             \<and> sym_heap_sched_pointers s')
     (return ts') (tcbQueueRemove q t)
     (\<lambda>ts' q' _ s'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  supply heap_path_append[simp del] distinct_append[simp del] filter_append[simp del]
         if_split[split del]
  apply (clarsimp simp: tcbQueueRemove_def removeAll_filter_not_eq)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rule rcorres_symb_exec_r[OF get_tcb_sp'])
   apply wpsimp
  apply (rule rcorres_if_r_fwd)
     \<comment> \<open>ts is the singleton list containing tcbPtr\<close>
   apply (rule rcorres_return)
   apply (clarsimp simp: list_queue_relation_def queue_end_valid_def prev_queue_head_def
                         emptyHeadEndPtrs_def)
   apply (rename_tac ts)
   apply (frule heap_ls_distinct)
   apply (case_tac ts; clarsimp split: if_splits)
  apply (rule rcorres_if_r_fwd)
    \<comment> \<open>tcbPtr is the head of ts\<close>
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (wpsimp wp: threadSet_wp getTCB_wp)
   apply (rename_tac ts nextPtr tcb tcb')
   apply (clarsimp simp: list_queue_relation_def)
   apply (frule heap_path_head')
   apply (frule set_list_mem_nonempty)
   apply (frule in_queue_not_head_or_not_tail_length_gt_1)
     apply fastforce
    apply (force simp: list_queue_relation_def)
   apply (clarsimp simp: return_def)
   apply (frule length_tail_nonempty)
   apply (frule heap_ls_distinct)
   apply (frule (1) filter_hd_equals_tl)
   apply (frule (2) heap_ls_next_of_hd)
   apply (intro conjI)
     apply (drule (1) heap_ls_remove_head_not_singleton)
     apply (clarsimp simp: return_def)
     apply (erule heap_ls_cong; simp?)
      apply (clarsimp simp: opt_map_red opt_map_upd_triv obj_at'_def)
     apply (clarsimp simp: prev_queue_head_def opt_map_def obj_at'_def)
    apply (case_tac ts; clarsimp simp: queue_end_valid_def)
   apply (clarsimp simp: prev_queue_head_def obj_at'_def split: if_splits)
  apply (rule rcorres_if_r_fwd)
   \<comment> \<open>tcbPtr is the last element of ts\<close>
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (wpsimp wp: threadSet_wp getTCB_wp)
   apply (rename_tac ts prevPtr tcb tcb')
   apply (clarsimp simp: list_queue_relation_def return_def)
   apply (frule in_queue_not_head_or_not_tail_length_gt_1)
     apply fast
    apply (force dest!: spec simp: list_queue_relation_def)
   apply (frule length_gt_1_imp_butlast_nonempty)
   apply (frule heap_ls_distinct)
   apply (frule filter_last_equals_butlast, fastforce)
   apply (prop_tac "t = last ts")
    apply (clarsimp simp: queue_end_valid_def)
   apply (frule (2) heap_path_prev_of_last)
   apply (intro conjI)
     apply (drule (1) heap_ls_remove_last_not_singleton)
     apply (erule heap_ls_cong; simp?)
     apply (fastforce simp: opt_map_def obj_at'_def intro: butlast_nonempty_length split: if_splits)
    apply (clarsimp simp: queue_end_valid_def opt_map_def obj_at'_def)
   apply (clarsimp simp: prev_queue_head_def opt_map_def obj_at'_def split: if_splits)
  \<comment> \<open>tcbPtr is in the middle of ts\<close>
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (clarsimp simp: list_queue_relation_def return_def)
  apply (rename_tac ts nextPtr prevPtr tcb tcb' tcb'' tcb''')
  apply (frule heap_ls_distinct)
  apply (frule split_list)
  apply (elim exE)
  apply (rename_tac xs ys)
  apply (frule_tac q=ts in filter_middle_distinct, assumption)
  apply (prop_tac "xs \<noteq> [] \<and> ys \<noteq> []", fastforce simp: queue_end_valid_def)
  apply clarsimp
  apply (frule (3) ptr_in_middle_prev_next[where ptr=t])
  apply clarsimp
  apply (intro conjI)
    apply (drule (2) heap_ls_remove_middle)
    apply (fastforce elim!: heap_ls_cong simp: opt_map_def obj_at'_def split: if_splits)
   apply (simp add: queue_end_valid_def)
  apply (subst opt_map_upd_triv)
   apply (clarsimp simp: prev_queue_head_def opt_map_def obj_at'_def)
  apply (intro prev_queue_head_heap_upd)
    apply assumption
   apply (frule heap_path_head')
   apply (prop_tac "the (tcbQueueHead q) \<in> set xs")
    apply (fastforce simp: hd_append)
   apply (fastforce simp: distinct_append opt_map_def obj_at'_def)
  apply fastforce
  done

lemma tcbQueuePrepend_rcorres_other:
  "rcorres
     (\<lambda>_ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> (\<exists>ts'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                      \<and> t' \<notin> set ts \<and> set ts \<inter> set ts' = {}))
     (return ts') (tcbQueuePrepend q' t')
     (\<lambda>ts' q' _ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  unfolding tcbQueuePrepend_def list_queue_relation_def
  apply (wpsimp wp: threadSet_prev_queue_head_other threadSet_heap_ls_other hoare_vcg_ex_lift)
  by (fastforce dest: list_queue_relation_Nil[THEN arg_cong_Not, THEN iffD2, rotated] heap_path_head
                simp: list_queue_relation_def return_def)

lemma tcbQueueAppend_rcorres_other:
  "rcorres
     (\<lambda>_ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> (\<exists>ts'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                      \<and> t' \<notin> set ts \<and> set ts \<inter> set ts' = {}))
     (return ts') (tcbQueueAppend q' t')
     (\<lambda>ts' q' _ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  unfolding tcbQueueAppend_def list_queue_relation_def
  apply (wpsimp wp: threadSet_prev_queue_head_other threadSet_heap_ls_other hoare_vcg_ex_lift)
  by (fastforce dest: list_queue_relation_Nil[THEN arg_cong_Not, THEN iffD2, rotated] heap_path_head
                simp: list_queue_relation_def queue_end_valid_def return_def)

lemma tcbQueueInsert_rcorres_other:
  "rcorres
     (\<lambda>_ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> sym_heap_sched_pointers s' \<and> t' \<notin> set ts
             \<and> (\<exists>ts' q'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                         \<and> afterPtr \<in> set ts' \<and> set ts \<inter> set ts' = {}))
     (return ts') (do _ \<leftarrow> tcbQueueInsert t' afterPtr; return q' od)
     (\<lambda>ts' q' _ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  unfolding tcbQueueInsert_def list_queue_relation_def
  apply (wpsimp wp: threadSet_prev_queue_head_other threadSet_heap_ls_other getTCB_wp
                    hoare_vcg_ex_lift)
  by (force dest: heap_ls_neighbour_in_set[where p=afterPtr] intro!: exI[where x=ts]
            simp: prev_queue_head_def opt_map_def obj_at'_def return_def)

lemma orderedInsert_rcorres_other:
  assumes rcorres: "\<And>t. rcorres (P t) (gets_the (f t)) (gets_the (f' t)) (\<lambda>rv rv' _ _. rv = rv')"
  assumes nf: "\<And>t. no_ofail (Q t) (f t)"
  assumes nf': "\<And>t s. no_ofail (\<lambda>s'. Q' t s s') (f' t)"
  assumes ord: "reflp R" "totalp R"
  shows
  "rcorres
     (\<lambda>s s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> sym_heap_sched_pointers s'
             \<and> t' \<notin> set ts \<and> set ts \<inter> set ts' = {}
             \<and> (\<forall>t \<in> set ts'. Q t s) \<and> Q t' s \<and> (\<forall>t \<in> set ts'. tcb_at' t s')
             \<and> (\<forall>t \<in> set ts'. P t s s' \<and> Q' t s s') \<and> P t' s s' \<and> Q' t' s s')
     (ordered_insert t' ts' f R) (orderedInsert t' q' f' R)
     (\<lambda>_ _ _ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (insert assms)
  apply (simp only: ordered_insert_def orderedInsert_def)
  apply (rule rcorres_stateAssert_r_fwd)
  apply clarsimp
  apply (rule rcorres_split_gets_the_fwd[where rrel="(=)"])
    apply (fastforce intro: rcorres_weaken_pre[OF rcorres])
   apply (fastforce intro: no_ofail_pre_imp)
  apply (rule rcorres_symb_exec_l)
    apply (rule mapM_gets_the_sp')
   apply (rule_tac P="\<lambda>s. \<forall>t \<in> set ts'. Q t s" in exs_valid_state_inv)
      apply (wpsimp wp: mapM_wp_inv)
     apply (wpsimp wp: no_fail_mapM_wp)
     apply (fastforce intro: no_ofailD)
    apply fastforce
   apply (wpsimp wp: empty_fail_mapM)
  apply (rename_tac vals)
  apply (rule_tac Q="\<lambda>s s'. \<forall>t \<in> set ts'. f t s = f' t s'" in rcorres_add_to_pre)
   apply (fastforce dest: rcorres_rrel')
  apply (cases "tcbQueueEmpty q'")
   apply clarsimp
   apply (rcorres rcorres: tcbQueuePrepend_rcorres_other)
   apply fastforce
  apply (simp only: if_False bind_assoc haskell_assert_def)
  apply (rule rcorres_assert_r_fwd)
  apply (clarsimp simp: bind_assoc)
  apply (rule rcorres_symb_exec_r[OF gets_the_sp]; (solves wpsimp)?)
  apply (rule rcorres_if_r_fwd)
   apply (rcorres rcorres: tcbQueuePrepend_rcorres_other)
   apply fastforce
  apply (rule rcorres_assert_r_fwd)
  apply clarsimp
  apply (rule rcorres_symb_exec_r[OF gets_the_sp]; (solves wpsimp)?)
  apply (rule rcorres_if_r_fwd)
   apply (rcorres rcorres: tcbQueueAppend_rcorres_other)
   apply fast
  apply (rule_tac Q="\<lambda>ptrOpt s s'. list_queue_relation
                                     ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                   \<and> list_queue_relation
                                       ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                   \<and> sym_heap_sched_pointers s'
                                   \<and> t' \<notin> set ts \<and> set ts \<inter> set ts' = {}
                                   \<and> vals = map (\<lambda>t. the (f' t s')) ts'
                                   \<and> (\<exists>ptr. ptrOpt = Some ptr \<and> ptr \<in> set ts' \<and> ptr \<noteq> hd ts')"
               in rcorres_symb_exec_r)
    apply (wpsimp wp: findInsertionPoint_rv_in_set)
    apply (frule list_queue_relation_Nil[where ts=ts'])
    apply (clarsimp dest!: heap_path_head simp: list_queue_relation_def queue_end_valid_def)
    apply (metis reflpD totalpD)
   apply wpsimp
  apply (rule rcorres_assert_r_fwd)
  apply (rule rcorres_stateAssert_r_fwd)
  apply (rcorres rcorres: tcbQueueInsert_rcorres_other)
  apply fastforce
  done

lemma tcbQueueRemove_rcorres_other:
  "rcorres
     (\<lambda>_ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
             \<and> sym_heap_sched_pointers s'
             \<and> (\<exists>ts'. list_queue_relation ts' q' (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                      \<and> t \<in> set ts' \<and> set ts \<inter> set ts' = {}))
     (return ts') (tcbQueueRemove q' t)
     (\<lambda>_ _ _ s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  unfolding tcbQueueRemove_def list_queue_relation_def
  apply (wpsimp wp: threadSet_prev_queue_head_other threadSet_heap_ls_other getTCB_wp
                    hoare_vcg_ex_lift)
  by (fastforce dest: list_queue_relation_neighbour_in_set[where p=t, rotated 2]
                simp: list_queue_relation_def opt_map_def obj_at'_def return_def)

defs insertionPoint_asrt_def:
  "insertionPoint_asrt \<equiv>
     \<lambda>q ptr s. \<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                    \<and> ptr \<in> set ts"

declare insertionPoint_asrt_def[simp]

lemma det_wp_ordered_insert[wp]:
  "(\<And>t. no_ofail (P t) (f t))
   \<Longrightarrow> det_wp (\<lambda>s. P t s \<and> (\<forall>t \<in> set ts. P t s)) (ordered_insert t ts f R)"
  unfolding ordered_insert_def
  apply wpsimp
  apply (clarsimp simp: no_ofail_def)
  done

abbreviation (input) ls_opt_rel :: "'a list \<Rightarrow> 'a option \<Rightarrow> bool" where
  "ls_opt_rel ls opt \<equiv> if ls = [] then opt = None else \<exists>ptr. opt = Some ptr \<and> hd ls = ptr"

lemma return_tl_return_next_corres_underlying:
  "ls_opt_rel ts ptrOpt \<Longrightarrow>
   corres_underlying {(s, s'). s = s'} False True ls_opt_rel
     (\<lambda>_. ts \<noteq> [])
     (\<lambda>s'. \<exists>ptr. ptrOpt = Some ptr \<and> heap_ls (tcbSchedNexts_of s') ptrOpt ts \<and> tcb_at' ptr s')
     (return (tl ts))
     (do tcb \<leftarrow> getObject (the ptrOpt); return (tcbSchedNext tcb) od)"
  apply (rule corres_symb_exec_r[OF _ get_tcb_sp']; (solves wpsimp)?)
  apply clarsimp
  apply (cases ts; fastforce dest: heap_ls_next_of_hd[rotated] simp: opt_map_def obj_at'_def)
  done

defs tcbQueueAdd_asrt_def:
  "tcbQueueAdd_asrt \<equiv>
     \<lambda>q tcbPtr s. \<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                       \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> sched_flag_set s t)"

declare tcbQueueAdd_asrt_def[simp]

lemma no_fail_tcbQueuePrepend:
  "no_fail
     (\<lambda>s. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> sched_flag_set s t))
          \<and> tcb_at' t s)
     (tcbQueuePrepend q t)"
  supply if_split[split del]
  unfolding tcbQueuePrepend_def
  apply (wpsimp wp: no_fail_stateAssert)
  apply (frule list_queue_relation_Nil)
  apply (fastforce dest: heap_path_head simp: list_queue_relation_def)
  done

lemma no_fail_tcbQueueAppend:
  "no_fail
     (\<lambda>s. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> sched_flag_set s t))
          \<and> tcb_at' t s)
     (tcbQueueAppend q t)"
  supply if_split[split del]
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: no_fail_stateAssert)
  apply (frule list_queue_relation_Nil)
  apply (fastforce simp: list_queue_relation_def queue_end_valid_def)
  done

defs tcbQueueInsert_asrt_def:
  "tcbQueueInsert_asrt \<equiv>
     \<lambda>tcbPtr ptr s.
       \<exists>ts q. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
              \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> sched_flag_set s t)
              \<and> tcbPtr \<notin> set ts \<and> ptr \<in> set ts"

declare tcbQueueInsert_asrt_def[simp]

lemma no_fail_tcbQueueInsert:
  "no_fail
     (\<lambda>s. (\<exists>ts q. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                  \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> sched_flag_set s t)
                  \<and> tcbPtr \<notin> set ts \<and> afterPtr \<in> set ts \<and> afterPtr \<noteq> hd ts)
          \<and> sym_heap_sched_pointers s \<and> tcb_at' tcbPtr s)
     (tcbQueueInsert tcbPtr afterPtr)"
  supply heap_path_append[simp del] if_split[split del]
  apply (wpsimp wp: getTCB_wp no_fail_stateAssert simp: tcbQueueInsert_def)
  apply (clarsimp simp: list_queue_relation_def)
  apply (frule split_list)
  apply (clarsimp, rename_tac ys zs)
  apply (intro context_conjI impI)
   apply (rule_tac x="ys @ afterPtr # zs" in exI)
   apply force
  apply clarsimp
  apply (intro context_conjI impI)
    apply (force dest: heap_path_sym_heap_non_nil_lookup_prev simp: opt_map_def obj_at'_def)
   apply (force dest: heap_ls_prev_no_loops simp: opt_map_def obj_at'_def)
  apply (prop_tac "ys \<noteq> []", fastforce dest: last_in_set)
  apply (fastforce dest!: heap_path_sym_heap_non_nil_lookup_prev simp: opt_map_def obj_at'_def)
  done

lemma no_fail_findInsertionPoint:
  "\<lbrakk>reflp R; totalp R; transp R\<rbrakk> \<Longrightarrow>
   no_fail
     (\<lambda>s. (\<exists>ts q. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                  \<and> (\<forall>t\<in>set ts. (\<exists>v. f t s = Some v) \<and> tcb_at' t s)
                  \<and> (\<forall>ptr. ptrOpt = Some ptr \<longrightarrow> ptr \<in> set ts))
          \<and> sym_heap_sched_pointers s)
     (findInsertionPoint val ptrOpt f R)"
  apply (simp add: findInsertionPoint_def no_fail_def)
  apply (intro impI allI)
  apply (elim exE conjE)+
  apply (rename_tac ts q)
  apply (rule_tac P="\<lambda>ptrOpt s. (\<forall>t \<in> set ts. f t s \<noteq> None \<and> tcb_at' t s)
                                \<and> list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                                \<and> (\<forall>ptr. ptrOpt = Some ptr \<longrightarrow> ptr \<in> set ts)"
               in no_fail_whileLoop)
     apply wpsimp
     apply (fastforce dest: compareVals_not_None)
    apply (rule_tac C'="\<lambda>r _. r \<noteq> None" in whileLoop_terminates_weaken_cond)
     apply (clarsimp simp: compareVals_def runReaderT_def obind_def
                           queue_end_valid_def list_queue_relation_def
                    split: option.splits if_splits)
      apply fastforce
     apply (rename_tac new_s r r_val)
     apply (frule_tac x=r in split_list)
     apply clarsimp
     apply (rename_tac ys zs v)
     apply (rule_tac P'="\<lambda>r r' s'. heap_ls (tcbSchedNexts_of s') r' r
                                   \<and> (r' \<noteq> None \<longrightarrow> tcb_at' (the r') s')
                                   \<and> (\<forall>t \<in> set r. tcb_at' t s')"
                 and P="\<lambda>r' s. suffix r' (r # zs)"
                 and r="r # zs"
                  in whileLoop_terminates_cross_ret[where rrel=ls_opt_rel and C="\<lambda>r _. r \<noteq> []"])
             apply (rule stronger_corres_guard_imp)
               apply (fastforce intro!: return_tl_return_next_corres_underlying)
              apply simp
             apply simp
            apply fastforce
           apply wpsimp
           apply (fastforce dest: suffix_tl)
          apply (wpsimp wp: getTCB_wp)
          apply (clarsimp simp: return_def split: if_splits)
           apply (rename_tac r' s' ko)
           apply (frule_tac xs=r' in hd_in_set)
           apply (frule_tac x="hd r'" in split_list)
           apply clarsimp
           apply (rule conjI)
            apply (case_tac r'; fastforce dest!: prefix_of_hd_nil simp: opt_map_def obj_at'_def)
           apply (intro conjI impI)
            apply (clarsimp, rename_tac next_ptr)
            apply (frule_tac p="hd r'" and np=next_ptr in heap_ls_next_in_list)
              apply force
             apply (clarsimp simp: opt_map_def obj_at'_def split: option.splits)
            apply fastforce
           apply (force dest: list.set_sel(2))
          apply (rename_tac r' s' ko)
          apply (intro conjI impI)
            apply (case_tac r'; clarsimp simp: opt_map_def obj_at'_def split: option.splits)
           apply (clarsimp, rename_tac next_ptr)
           apply (frule_tac p="hd r'" and np=next_ptr in heap_ls_next_in_list)
             apply force
            apply (clarsimp simp: opt_map_def obj_at'_def split: option.splits)
           apply fastforce
          apply (force dest: list.set_sel(2))
         apply (rule whileLoop_terminates_inv[
                       OF _ _ list_length_wf_helper, where I="\<top>\<top>", simplified])
         apply wpsimp
        apply (clarsimp simp: ex_abs_underlying_def)
       apply (clarsimp split: if_splits)
      apply clarsimp
     apply wpsimp
    apply (fastforce intro!: compareVals_not_None)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' getTCB_wp)
   apply (force dest!: compareVals_not_None heap_ls_next_in_list
                 simp: list_queue_relation_def opt_map_def obj_at'_def)
  apply (force dest: heap_path_head simp: list_queue_relation_def queue_end_valid_def)
  done

lemma no_fail_orderedInsert:
  "\<lbrakk>reflp R; totalp R; transp R\<rbrakk> \<Longrightarrow>
   no_fail
     (\<lambda>s. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                \<and> (\<forall>t \<in> set ts. \<exists>v. f t s = Some v \<and> tcb_at' t s \<and> sched_flag_set s t)
                \<and> t \<notin> set ts)
          \<and> sym_heap_sched_pointers s \<and> (\<exists>val. f t s = Some val) \<and> tcb_at' t s)
     (orderedInsert t q f R)"
  apply (clarsimp simp: orderedInsert_def)
  apply (wpsimp wp: no_fail_tcbQueueInsert no_fail_tcbQueueAppend no_fail_tcbQueuePrepend
                    no_fail_stateAssert)
            apply (rule_tac Q'="\<lambda>ptrOpt s. \<exists>ts. list_queue_relation ts q
                                                  (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                                                \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> sched_flag_set s t)
                                                \<and> (\<exists>ptr. ptrOpt = Some ptr \<and> ptr \<in> set ts
                                                         \<and> ptr \<noteq> hd ts)
                                                \<and> t \<notin> set ts
                                           \<and> sym_heap_sched_pointers s \<and> tcb_at' t s"
                         in hoare_post_imp)
             apply fastforce
            apply (wpsimp wp: findInsertionPoint_rv_in_set no_fail_findInsertionPoint
                              hoare_vcg_ex_lift no_fail_stateAssert)+
  apply (rename_tac ts val)
  apply (frule list_queue_relation_Nil)
  apply (frule he_ptrs_head_iff_he_ptrs_end)
  apply (clarsimp simp: list_queue_relation_def queue_end_valid_def tcbQueueEmpty_def)
  apply (frule heap_path_head')
  apply (intro conjI impI allI; clarsimp)
      apply fastforce
     apply fastforce
    apply fastforce
   apply (rule_tac x=ts in exI)
   apply clarsimp
   apply (rule_tac x=q in exI)
   apply clarsimp
  apply (rule_tac x=ts in exI)
  apply clarsimp
  apply (intro conjI impI allI)
   apply (drule_tac x="hd ts" in bspec, simp)
   apply (metis Some_to_the reflpE totalpD)
  apply (drule_tac x="last ts" in bspec, simp)
  apply (clarsimp split: option.splits)
  done

text \<open>Work towards showing a @{const monadic_rewrite} rule for part of @{const orderedInsert}\<close>

lemma findInsertionPoint_beforePtr_afterPtr:
  assumes sorted: "sorted_wrt (img_ord (\<lambda>t. f t s) (opt_ord_rel R)) ts"
  assumes nf: "\<forall>t \<in> set ts. \<exists>v. f t s = Some v"
  assumes after: "afterPtr \<in> set ts"
                 "\<exists>afterVal. f afterPtr s = Some afterVal \<and> R val afterVal \<and> val \<noteq> afterVal"
                 "\<forall>pfx. (\<exists>sfx. pfx @ afterPtr # sfx = ts) \<longrightarrow> (\<forall>x \<in> set pfx. R (the (f x s)) val)"
  assumes before: "beforePtr \<in> set ts"
                  "\<exists>beforeVal. f beforePtr s = Some beforeVal \<and> R beforeVal val"
                  "\<forall>sfx. (\<exists>pfx. pfx @ beforePtr # sfx = ts)
                         \<longrightarrow> (\<forall>x \<in> set sfx. R val (the (f x s)) \<and> the (f x s) \<noteq> val)"
  assumes ord: "transp R" "antisymp R"
  shows "\<exists>pfx sfx. ts = pfx @ beforePtr # afterPtr # sfx"
  apply (insert nf ord before(1) before(2))
  apply (frule split_list[where x=beforePtr])
  apply clarsimp
  apply (rename_tac beforeVal ys zs)
  apply (rule_tac x=ys in exI)
  apply (rule_tac x="tl zs" in exI)
  apply (insert after)
  apply clarsimp
  apply (rename_tac afterVal)
  apply (prop_tac "R beforeVal afterVal \<and> beforeVal \<noteq> afterVal")
   apply (metis antisympD transpD)
  apply (prop_tac "afterPtr \<notin> set ys")
   apply clarsimp
   apply (frule split_list[where x=afterPtr])
   apply (insert sorted)
   apply (prop_tac "R afterVal beforeVal")
    apply (force simp: img_ord_Some' sorted_wrt_append)
   apply (fastforce dest: antisympD)
  apply (prop_tac "afterPtr \<in> set zs")
   apply (fastforce simp: after)
  apply (frule split_list[where x=afterPtr])
  apply clarsimp
  apply (rename_tac ys' zs')
  apply (drule_tac x="ys @ beforePtr # ys'" in spec)
  apply (insert before(3))
  by (case_tac ys'; force dest!: spec antisympD)

definition compareValsBackwards where
  "compareValsBackwards val ptrOpt f R \<equiv>
     if ptrOpt \<noteq> Nothing
     then do { ptr \<leftarrow> oreturn $ fromJust ptrOpt;
               val' \<leftarrow> f ptr;
               oreturn $ R val val' \<and> val' \<noteq> val }
     else oreturn False"

definition findInsertionPointBackwards where
  "findInsertionPointBackwards val ptrOpt f R \<equiv>
     whileLoop (\<lambda>ptrOpt. fromJust \<circ> runReaderT (compareValsBackwards val ptrOpt f R))
               (\<lambda>ptrOpt. do tcb \<leftarrow> getObject (fromJust ptrOpt);
                            return (tcbSchedPrev tcb)
                         od)
               ptrOpt"

crunch findInsertionPointBackwards
  for inv[wp]: P
  (wp: crunch_wps)

lemma compareValsBackwards_not_None:
  "the (runReaderT (compareValsBackwards val r f R) s) \<Longrightarrow> r \<noteq> None"
  by (fastforce simp: compareValsBackwards_def runReaderT_def split: if_splits)

lemma findInsertionPointBackwards_rv_rel:
  "\<lbrakk>reflp R; totalp R; antisymp R\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s'. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
         \<and> sym_heap_sched_pointers s'
         \<and> sorted_wrt (img_ord (\<lambda>t. f t s') (opt_ord_rel R)) ts
         \<and> ts \<noteq> [] \<and> (\<forall>t \<in> set ts. \<exists>v. f t s' = Some v) \<and> (\<forall>t \<in> set ts. tcb_at' t s')
         \<and> (\<exists>v. f (hd ts) s' = Some v \<and> R v val) \<and> (\<exists>v. f (last ts) s' = Some v \<and> \<not> R v val)\<rbrace>
   findInsertionPointBackwards val (tcbQueueEnd q) f R
   \<lbrace>\<lambda>ptrOpt s'. \<exists>ptr. (ptrOpt = Some ptr \<and> ptr \<in> set ts \<and> ptr \<noteq> last ts)
                      \<and> (\<exists>val'. f ptr s'= Some val' \<and> R val' val)
                      \<and> (\<forall>sfx. (\<exists>pfx. pfx @ ptr # sfx = ts)
                                \<longrightarrow> (\<forall>p \<in> set sfx. R val (the (f p s')) \<and> the (f p s') \<noteq> val))\<rbrace>"
  (is "\<lbrakk>_;  _; _\<rbrakk> \<Longrightarrow> \<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  supply heap_path_append[simp del]
  apply (clarsimp simp: findInsertionPointBackwards_def)
  apply (rule hoare_pre)
   apply (rule_tac Q4="\<lambda>ptrOpt s'. ?pre s'
                                   \<and> (\<exists>ptr. ptrOpt = Some ptr \<and> ptr \<in> set ts
                                            \<and> (\<forall>sfx. (\<exists>pfx. pfx @ ptr # sfx = ts)
                                                      \<longrightarrow> (\<forall>p \<in> set sfx. R val (the (f p s'))
                                                                         \<and> the (f p s') \<noteq> val)))"
                in valid_whileLoop[where P=Q and I=Q for Q, simplified])
     apply fastforce
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
    apply (wpsimp wp: hoare_vcg_ex_lift getTCB_wp)
    apply (clarsimp simp: list_queue_relation_def compareValsBackwards_def runReaderT_def obind_def
                   split: option.splits)
     apply fastforce
    apply (rename_tac ptr ptrVal)
    apply (frule (1) heap_path_head)
    apply (drule_tac x=ptr in bspec, fastforce)+
    apply normalise_obj_at'
    apply (prop_tac "ptr \<noteq> hd ts")
     apply (fastforce dest!: antisympD)
    apply (frule_tac p=ptr in not_head_prev_not_None, fastforce+)
    apply clarsimp
    apply (rename_tac prev_ptr)
    apply (rule_tac x=prev_ptr in exI)
    apply (intro conjI)
      apply (clarsimp simp: opt_map_def obj_at'_def split: option.splits)
     apply (fastforce dest: heap_ls_prev_cases intro: sym_heapD2)
    apply (intro impI allI ballI)
    apply (rename_tac sfx p)
    apply (elim exE)
    apply (rename_tac pfx)
    apply (prop_tac "ptr = hd sfx")
     subgoal by (auto dest!: heap_path_non_nil_lookup_next sym_heapD2 split: list.splits)
    apply (drule_tac x="tl sfx" in spec)
    apply (case_tac "p = hd sfx")
     apply simp
    apply (case_tac sfx; clarsimp)
   apply (clarsimp simp: compareValsBackwards_def runReaderT_def obind_def split: option.splits)
    apply fastforce
   apply (metis Some_to_the reflpD totalpD)
  apply (clarsimp simp: list_queue_relation_def queue_end_valid_def)
  apply (fastforce dest!: heap_ls_distinct suffix_last_nil[rotated, OF _ sym])
  done

definition tcbQueueInsertAfter where
  "tcbQueueInsertAfter tcbPtr beforePtr \<equiv> do
     tcb \<leftarrow> getObject beforePtr;
     afterPtrOpt \<leftarrow> return $ tcbSchedNext tcb;
     assert (afterPtrOpt \<noteq> None);
     afterPtr \<leftarrow> return $ fromJust afterPtrOpt;
     threadSet (tcbSchedPrev_update (\<lambda>_. Some beforePtr)) tcbPtr;
     threadSet (tcbSchedNext_update (\<lambda>_. Some afterPtr)) tcbPtr;
     threadSet (tcbSchedPrev_update (\<lambda>_. Some tcbPtr)) afterPtr;
     threadSet (tcbSchedNext_update (\<lambda>_. Some tcbPtr)) beforePtr
   od"

lemma setObject_rewrite:
  "monadic_rewrite F E (\<lambda>s. ptr' = ptr \<and> val' = val) (setObject ptr val) (setObject ptr' val')"
  by (clarsimp simp: monadic_rewrite_def)

lemma threadSet_rewrite:
  "monadic_rewrite F E (\<lambda>s. t' = t \<and> (\<forall>tcb. f tcb = f' tcb) \<and> tcb_at' t s)
     (threadSet f t) (threadSet f' t')"
  apply (clarsimp simp: threadSet_def)
  apply monadic_rewrite_symb_exec_l
    apply monadic_rewrite_symb_exec_r
     apply (rule setObject_rewrite)
    apply (wpsimp wp: getTCB_wp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbQueueInsert_rewrite:
  "monadic_rewrite True True
     (\<lambda>s. tcbSchedNexts_of s beforePtr = Some afterPtr \<and> sym_heap_sched_pointers s
          \<and> tcb_at' beforePtr s \<and> tcb_at' t s)
     (tcbQueueInsert t afterPtr) (tcbQueueInsertAfter t beforePtr)"
  apply (clarsimp simp: tcbQueueInsert_def tcbQueueInsertAfter_def)
  apply monadic_rewrite_symb_exec_l
    apply monadic_rewrite_symb_exec_l
     apply monadic_rewrite_symb_exec_l
      apply monadic_rewrite_symb_exec_r
        apply monadic_rewrite_symb_exec_l
        apply monadic_rewrite_symb_exec_r
         apply monadic_rewrite_symb_exec_l
          apply (rule monadic_rewrite_bind)
            apply (rule threadSet_rewrite)
           apply (rule monadic_rewrite_bind)
             apply (rule threadSet_rewrite)
            apply (rule monadic_rewrite_bind)
              apply (rule threadSet_rewrite)
             apply (rule threadSet_rewrite)
            apply (wpsimp wp: getTCB_wp no_fail_stateAssert)+
  apply (fastforce dest!: sym_heapD1 simp: opt_map_def obj_at'_def)
  done

crunch findInsertionPoint, findInsertionPointBackwards
  for (empty_fail) empty_fail[intro!, wp, simp]

abbreviation (input) last_ls_opt_rel :: "'a list \<Rightarrow> 'a option \<Rightarrow> bool" where
  "last_ls_opt_rel ls opt \<equiv> if ls = [] then opt = None else \<exists>ptr. opt = Some ptr \<and> last ls = ptr"

lemma return_butlast_return_prev_corres_underlying:
  "last_ls_opt_rel ts ptrOpt \<Longrightarrow>
   corres_underlying {(s, s'). s = s'} False True last_ls_opt_rel
     (\<lambda>_. ts \<noteq> [])
     (\<lambda>s'. \<exists>ptr. ptrOpt = Some ptr \<and> tcb_at' ptr s'
                 \<and> (\<exists>end. heap_path (tcbSchedNexts_of s') (Some (hd ts)) ts end) \<and> ptr = last ts
           \<and> tcbSchedPrevs_of s' (hd ts) = None \<and> sym_heap_sched_pointers s' \<and> distinct ts)
     (return (butlast ts))
     (do tcb \<leftarrow> getObject (the ptrOpt); return (tcbSchedPrev tcb) od)"
  apply (rule corres_symb_exec_r[OF _ get_tcb_sp']; (solves wpsimp)?)
  apply clarsimp
  apply (intro conjI)
   apply (case_tac ts; clarsimp simp: opt_map_def obj_at'_def)
  apply clarsimp
  apply (frule last_in_set[where as=ts])
  apply (frule split_list)
  apply clarsimp
  apply (rename_tac xs ys)
  apply (frule (1) suffix_last_nil)
  apply (cut_tac xs=xs and z="last ts" and ys=ys in heap_path_sym_heap_non_nil_lookup_prev)
     apply fastforce
    apply fastforce
   apply (metis butlast_snoc)
  apply (prop_tac "last xs = last (butlast ts)")
   apply (metis butlast_snoc)
  apply (fastforce simp: opt_map_def obj_at'_def)
  done

lemma no_fail_findInsertionPointBackwards:
  "no_fail
     (\<lambda>s. (\<exists>ts q. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s) \<and> ts \<noteq> []
                  \<and> (\<forall>t\<in>set ts. \<exists>v. f t s = Some v \<and> tcb_at' t s)
                  \<and> (\<forall>ptr. ptrOpt = Some ptr \<longrightarrow> ptr \<in> set ts))
          \<and> sym_heap_sched_pointers s)
     (findInsertionPointBackwards val ptrOpt f R)"
  apply (simp add: findInsertionPointBackwards_def no_fail_def)
  apply (intro impI allI)
  apply (elim exE conjE)+
  apply (rename_tac ts q)
  apply (rule_tac P="\<lambda>ptrOpt s. (\<forall>t \<in> set ts. f t s \<noteq> None \<and> tcb_at' t s)
                                \<and> list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                                \<and> sym_heap_sched_pointers s
                                \<and> (\<forall>ptr. ptrOpt = Some ptr \<longrightarrow> (ptr \<in> set ts \<and> tcb_at' ptr s))"
               in no_fail_whileLoop)
     apply wpsimp
     apply (fastforce dest: compareValsBackwards_not_None)
    apply (rule_tac C'="\<lambda>r _. r \<noteq> None" in whileLoop_terminates_weaken_cond)
     apply (clarsimp simp: compareValsBackwards_def runReaderT_def obind_def
                           queue_end_valid_def list_queue_relation_def
                    split: option.splits if_splits)
      apply (force dest: bspec)
     apply (rename_tac r r_val)
     apply (frule_tac x=r in split_list')
     apply (elim exE)
     apply (rename_tac ys zs)
     apply (rule_tac P'="\<lambda>r r' s'. (\<exists>end. heap_path (tcbSchedNexts_of s') (Some (hd ts)) r end
                                   \<and> (r \<noteq> [] \<longrightarrow> the r' = last r))
                                   \<and> tcbSchedPrevs_of s' (hd ts) = None
                                   \<and> (\<forall>t \<in> set r. tcb_at' t s') \<and> sym_heap_sched_pointers s'"
                 and P="\<lambda>r' s. prefix r' (ys @ [r])"
                 and r="ys @ [r]"
                  in whileLoop_terminates_cross_ret[where rrel=last_ls_opt_rel and C="\<lambda>r _. r \<noteq> []"])
             apply (rule stronger_corres_guard_imp)
               apply (erule return_butlast_return_prev_corres_underlying)
              apply fastforce
             apply (frule heap_ls_distinct)
             apply clarsimp
             apply (frule (1) heap_path_head)
             apply (intro conjI impI allI)
               apply (clarsimp simp: prefix_def)
               apply blast
              apply force
             apply (force intro: distinct_prefix' elim!: prefix_order.trans)
            apply force
           apply wpsimp
           apply (elim disjE)
            apply (force simp: prefixeq_butlast)
           apply (metis prefix_order.order_trans prefixeq_butlast)
          apply (wpsimp wp: getTCB_wp)
          apply (clarsimp simp: return_def)
          apply (intro conjI impI allI)
            apply (metis heap_path_butlast if_option_eq)
           apply (rename_tac r' s' tcb v "end" ptr)
           apply (clarsimp simp: prefix_def return_def)
           apply (frule_tac ls=r' in heap_path_prev_of_last)
             apply fastforce
            apply (fastforce intro!: butlast_nonempty_length)
           apply (prop_tac "r' \<noteq> []", force)
           apply (clarsimp simp: opt_map_def obj_at'_def)
          apply (clarsimp simp: prefix_def)
          apply (metis in_set_butlastD)
         apply (rule whileLoop_terminates_inv[OF _ _ list_length_wf_helper, where I="\<top>\<top>", simplified])
         apply wpsimp
        apply (clarsimp simp: ex_abs_underlying_def)
       apply (clarsimp split: if_splits)
      apply (frule (1) heap_path_head)
      apply (intro conjI impI allI)
         apply (case_tac zs; clarsimp)
        apply (clarsimp simp: prev_queue_head_def heap_path_head')
       apply simp
      apply fastforce
     apply wpsimp
    apply (fastforce dest: compareValsBackwards_not_None)
   apply (wpsimp wp: hoare_vcg_all_lift getTCB_wp)
   apply (rule context_conjI)
    apply (frule compareValsBackwards_not_None)
    apply (clarsimp simp: list_queue_relation_def)
    apply (rename_tac new_s tcb prev_ptr ptr)
    apply (frule_tac np=ptr and p=prev_ptr and hp="tcbSchedNexts_of new_s" in heap_ls_prev_cases)
       apply simp
      apply (erule sym_heapD2)
      apply (fastforce simp: opt_map_def obj_at'_def)
     apply fastforce
    apply (fastforce simp: opt_map_def obj_at'_def prev_queue_head_def)
   apply force
  apply (clarsimp simp: list_queue_relation_def)
  done

defs orderedInsertBackwards_asrt_def:
  "orderedInsertBackwards_asrt \<equiv>
     \<lambda>t q f R s.
       (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
             \<and> sorted_wrt (img_ord (\<lambda>t. f t s) (opt_ord_rel R)) ts
             \<and> (\<forall>t \<in> set ts. \<exists>v. f t s = Some v \<and> tcb_at' t s))
       \<and> (\<exists>val. f t s = Some val) \<and> tcb_at' t s
       \<and> sym_heap_sched_pointers s"

declare orderedInsertBackwards_asrt_def[simp]

lemma findInsertionPointBackwards_rewrite:
  "\<lbrakk>reflp R; transp R; totalp R; antisymp R\<rbrakk> \<Longrightarrow>
   monadic_rewrite True True
     (\<lambda>s'. (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                 \<and> sorted_wrt (img_ord (\<lambda>t. f t s') (opt_ord_rel R)) ts
                 \<and> (\<forall>t \<in> set ts. \<exists>v. f t s' = Some v \<and> tcb_at' t s')
                 \<and> ts \<noteq> []
                 \<and> (\<exists>v. f (hd ts) s' = Some v \<and> R v val)
                 \<and> (\<exists>v. f (last ts) s' = Some v \<and> \<not> R v val))
           \<and> (\<exists>val. f t s' = Some val) \<and> tcb_at' t s'
           \<and> sym_heap_sched_pointers s')
     (do ptrOpt \<leftarrow> findInsertionPoint val (tcbQueueHead q) f R;
         assert (\<exists>y. ptrOpt = Some y);
         ptr \<leftarrow> return (the ptrOpt);
         stateAssert (insertionPoint_asrt q ptr) [];
         tcbQueueInsert t ptr
      od)
     (do ptrOpt \<leftarrow> findInsertionPointBackwards val (tcbQueueEnd q) f R;
         assert (\<exists>y. ptrOpt = Some y);
         ptr \<leftarrow> return (the ptrOpt);
         stateAssert (insertionPoint_asrt q ptr) [];
         tcbQueueInsertAfter t (the ptrOpt)
      od)"
  apply monadic_rewrite_symb_exec_l
    apply monadic_rewrite_symb_exec_r
      apply monadic_rewrite_symb_exec_l
       apply monadic_rewrite_symb_exec_r
        apply clarsimp
        apply monadic_rewrite_symb_exec_l
         apply monadic_rewrite_symb_exec_r
           apply (rule tcbQueueInsert_rewrite)
          apply (wpsimp wp: no_fail_stateAssert)+
     apply (rule no_fail_findInsertionPointBackwards)
    apply (rename_tac ptrOpt)
    apply (rule_tac Q'="\<lambda>rv s'. \<exists>ts. list_queue_relation ts q
                                       (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                     \<and> (\<forall>t \<in> set ts. \<exists>v. f t s' = Some v \<and> tcb_at' t s')
                                     \<and> sorted_wrt (img_ord (\<lambda>t. f t s') (opt_ord_rel R)) ts
                                     \<and> (\<exists>beforePtr. (rv = Some beforePtr \<and> beforePtr \<in> set ts
                                                     \<and> beforePtr \<noteq> last ts)
                                                    \<and> (\<exists>val'. f beforePtr s'= Some val' \<and> R val' val)
                                                    \<and> (\<forall>sfx. (\<exists>pfx. pfx @ beforePtr # sfx = ts)
                                                              \<longrightarrow> (\<forall>p \<in> set sfx. R val (the (f p s'))
                                                                                 \<and> the (f p s') \<noteq> val)))
                                     \<and> (\<exists>afterPtr. (ptrOpt = Some afterPtr \<and> afterPtr \<in> set ts
                                                    \<and> afterPtr \<noteq> hd ts)
                                                   \<and> (\<exists>val'. f afterPtr s' = Some val'
                                                   \<and> R val val' \<and> val \<noteq> val')
                                                   \<and> (\<forall>pfx. (\<exists>sfx. pfx @ afterPtr # sfx = ts)
                                                             \<longrightarrow> (\<forall>p \<in> set pfx. R (the (f p s')) val)))
                                \<and> tcb_at' t s' \<and> sym_heap_sched_pointers s'"
                 in hoare_post_imp)
     apply (clarsimp simp: list_queue_relation_def)
     apply (intro conjI impI)
     subgoal for \<dots> beforePtr _ _ afterPtr _
       by (frule_tac afterPtr=afterPtr and beforePtr=beforePtr
                  in findInsertionPoint_beforePtr_afterPtr[where val=val];
           force?)
     apply fastforce
    apply (rule hoare_vcg_ex_lift)
    apply (wpsimp wp: hoare_vcg_conj_lift findInsertionPointBackwards_rv_rel)
   apply (wpsimp wp: findInsertionPoint_rv_rel hoare_vcg_conj_lift hoare_vcg_ex_lift)
  apply (fastforce simp: list_queue_relation_def queue_end_valid_def)
  done

lemma tcbQueued_update_tcbInReleaseQueue[wp]:
  "threadSet (tcbQueued_update f) tcbPtr \<lbrace>\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)\<rbrace>"
  by (wpsimp wp: threadSet_field_opt_pred)

lemma ready_or_release_disjoint:
  "ready_or_release s \<Longrightarrow> set (ready_queues s d p) \<inter> set (release_queue s) = {}"
  by (fastforce simp: ready_or_release_def in_ready_q_def not_in_release_q_def)

lemma setQueue_ksReadyQueues_other:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s (d, p)) \<and> (domain \<noteq> d \<or> priority \<noteq> p)\<rbrace>
   setQueue domain priority ts
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s (d, p))\<rbrace>"
  by (wpsimp simp: setQueue_def)

lemma tcbQueued_update_inQ_other:
  "\<lbrace>\<lambda>s. P (inQ d p |< tcbs_of' s)
        \<and> ((\<lambda>tcb. tcbDomain tcb \<noteq> d \<or> tcbPriority tcb \<noteq> p) |< tcbs_of' s) tcbPtr\<rbrace>
   threadSet (tcbQueued_update f) tcbPtr
   \<lbrace>\<lambda>_ s. P (inQ d p |< tcbs_of' s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (fastforce elim: rsubst[where P=P] simp: inQ_def opt_pred_def opt_map_def obj_at'_def)

lemma threadSet_inQ:
  "\<lbrakk>\<And>tcb. tcbPriority (F tcb) = tcbPriority tcb; \<And>tcb. tcbDomain (F tcb) = tcbDomain tcb;
    \<And>tcb. tcbQueued (F tcb) = tcbQueued tcb\<rbrakk>
   \<Longrightarrow> threadSet F tcbPtr \<lbrace>\<lambda>s. P (inQ d p |< tcbs_of' s)\<rbrace>"
  apply (wpsimp wp: threadSet_field_opt_pred)
   apply (clarsimp simp: inQ_def)
  apply fastforce
  done

crunch tcbQueueRemove, tcbQueuePrepend, tcbQueueAppend, tcbQueueInsert
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and tcbInReleaseQueue_opt_pred[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and tcbQueued_opt_pred[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  and tcbPriority_opt_pred[wp]: "\<lambda>s. P ((\<lambda>tcb. Q (tcbPriority tcb)) |< tcbs_of' s)"
  and tcbDomain_opt_pred[wp]: "\<lambda>s. P ((\<lambda>tcb. Q (tcbDomain tcb)) |< tcbs_of' s)"
  and inQ_opt_pred[wp]: "\<lambda>s. P (inQ d p |< tcbs_of' s)"
  (wp: crunch_wps threadSet_inQ threadSet_field_inv threadSet_field_opt_pred)

lemma set_butlast:
  "distinct list \<Longrightarrow> set (butlast list) = (set list) - {last list}"
  by (induct list, simp+, fastforce)

lemma setQueue_sets_queue[wp]:
  "\<And>d p ts P. \<lbrace> \<lambda>s. P ts \<rbrace> setQueue d p ts \<lbrace>\<lambda>rv s. P (ksReadyQueues s (d, p)) \<rbrace>"
  unfolding setQueue_def
  by (wp, simp)

lemma threadSet_opt_pred_other:
  "\<lbrace>\<lambda>s. P ((prop |< tcbs_of' s) t) \<and> t' \<noteq> t\<rbrace>
   threadSet F t'
   \<lbrace>\<lambda>_ s. P ((prop |< tcbs_of' s) t)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (clarsimp simp: obj_at'_def opt_pred_def)

lemma tcbQueued_True_makes_inQ:
  "\<lbrace>\<lambda>s. ((\<lambda>tcb. tcbPriority tcb = priority) |< tcbs_of' s) tcbPtr
        \<and> ((\<lambda>tcb. tcbDomain tcb = domain) |< tcbs_of' s) tcbPtr\<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. True)) tcbPtr
   \<lbrace>\<lambda>_ s. (inQ domain priority |< tcbs_of' s) tcbPtr\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (clarsimp simp: inQ_def opt_pred_def opt_map_def obj_at'_def)

lemma tcbQueued_False_makes_not_inQ:
  "\<lbrace>\<top>\<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. False)) tcbPtr
   \<lbrace>\<lambda>_ s. \<not> (inQ domain priority |< tcbs_of' s) tcbPtr\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (clarsimp simp: inQ_def opt_pred_def opt_map_def obj_at'_def)

defs valid_tcbs'_asrt_def:
  "valid_tcbs'_asrt \<equiv> valid_tcbs'"

declare valid_tcbs'_asrt_def[simp]

defs valid_objs'_asrt_def:
  "valid_objs'_asrt \<equiv> valid_objs'"

declare valid_objs'_asrt_def[simp]

lemma threadSet_eps_of'[wp]:
  "threadSet F tcbPtr \<lbrace>\<lambda>s. P (eps_of' s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (erule rsubst[where P=P])
  apply (drule obj_at'_prop)
  apply (fastforce simp: opt_map_def projectKO_opts_defs split: kernel_object.splits)
  done

lemma threadSet_ntfns_of'[wp]:
  "threadSet F tcbPtr \<lbrace>\<lambda>s. P (ntfns_of' s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (erule rsubst[where P=P])
  apply (drule obj_at'_prop)
  apply (fastforce simp: opt_map_def projectKO_opts_defs split: kernel_object.splits)
  done

crunch orderedInsert, tcbQueueRemove
  for eps_of'[wp]: "\<lambda>s. P (eps_of' s)"
  and ntfns_of'[wp]: "\<lambda>s. P (ntfns_of' s)"
  (wp: crunch_wps)

definition ep_queues_blocked :: "'z::state_ext state \<Rightarrow> bool" where
  "ep_queues_blocked s \<equiv>
     \<forall>p q. ep_queues_of s p = Some q \<longrightarrow> (\<forall>t \<in> set q. st_tcb_at (\<lambda>st. ep_blocked st = Some p) t s)"

lemma ep_queues_blocked_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ep_queues_of s)\<rbrace>"
  assumes "\<And>P t. f \<lbrace>\<lambda>s. st_tcb_at P t s\<rbrace>"
  shows "f \<lbrace>ep_queues_blocked\<rbrace>"
  unfolding ep_queues_blocked_def
  apply (rule hoare_pre)
   apply (wps | wp assms | wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift hoare_vcg_imp_lift')+
  done

lemma sym_refs_ep_queues_blocked[elim!]:
  "sym_refs (state_refs_of s) \<Longrightarrow> ep_queues_blocked s"
  by (fastforce elim: st_tcb_weakenE dest: in_ep_queue_st_tcb_at
                simp: ep_queues_blocked_def ep_blocked_def)

definition ntfn_queues_blocked :: "'z::state_ext state \<Rightarrow> bool" where
  "ntfn_queues_blocked s \<equiv>
     \<forall>p q. ntfn_queues_of s p = Some q
           \<longrightarrow> (\<forall>t \<in> set q. st_tcb_at (\<lambda>st. ntfn_blocked st = Some p) t s)"

lemma ntfn_queues_blocked_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ntfn_queues_of s)\<rbrace>"
  assumes "\<And>P t. f \<lbrace>\<lambda>s. st_tcb_at P t s\<rbrace>"
  shows "f \<lbrace>ntfn_queues_blocked\<rbrace>"
  unfolding ntfn_queues_blocked_def
  apply (rule hoare_pre)
   apply (wps | wp assms | wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift hoare_vcg_imp_lift')+
  done

lemma sym_refs_ntfn_queues_blocked[elim!]:
  "sym_refs (state_refs_of s) \<Longrightarrow> ntfn_queues_blocked s"
  by (fastforce elim: st_tcb_weakenE dest: in_ntfn_queue_st_tcb_at
                simp: ntfn_queues_blocked_def ntfn_blocked_def)

lemma ready_qs_distinct_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  shows "f \<lbrace>ready_qs_distinct\<rbrace>"
  unfolding ready_qs_distinct_def
  apply (rule hoare_pre)
   apply (wps assms | wpsimp)+
  done

lemma ready_queues_runnable_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  assumes "\<And>P t. f \<lbrace>\<lambda>s. st_tcb_at P t s\<rbrace>"
  shows "f \<lbrace>ready_queues_runnable\<rbrace>"
  unfolding ready_queues_runnable_def
  apply (rule hoare_pre)
   apply (wps assms | wp assms | wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift)+
  done

lemma release_q_runnable_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (release_queue s)\<rbrace>"
  assumes "\<And>P t. f \<lbrace>\<lambda>s. st_tcb_at P t s\<rbrace>"
  shows "f \<lbrace>release_q_runnable\<rbrace>"
  unfolding release_q_runnable_def
  apply (rule hoare_pre)
   apply (wps | wp assms | wpsimp wp: hoare_vcg_ball_lift2_pre_conj)+
  done

lemma valid_ready_qs_in_correct_ready_q[elim!]:
  "valid_ready_qs s \<Longrightarrow> in_correct_ready_q s"
  by (simp add: valid_ready_qs_def in_correct_ready_q_def)

lemma valid_ready_qs_ready_qs_distinct[elim!]:
  "valid_ready_qs s \<Longrightarrow> ready_qs_distinct s"
  by (simp add: valid_ready_qs_def ready_qs_distinct_def)

lemma valid_ready_qs_ready_queues_runnable[elim!]:
  "valid_ready_qs s \<Longrightarrow> ready_queues_runnable s"
  by (simp add: valid_ready_qs_def ready_queues_runnable_def obj_at_kh_kheap_simps)

lemma valid_release_q_release_q_runnable[elim!]:
  "valid_release_q s \<Longrightarrow> release_q_runnable s"
  by (fastforce simp: valid_release_q_def release_q_runnable_def vs_all_heap_simps pred_tcb_at_def
                      obj_at_def)

lemma disjoint_via_tcb_state:
  "\<lbrakk>\<forall>t \<in> set q. st_tcb_at P t s; \<forall>t \<in> set q'. st_tcb_at P' t s; \<And>st. P st \<Longrightarrow> \<not> P' st\<rbrakk>
   \<Longrightarrow> set q \<inter> set q' = {}"
  by (fastforce simp: pred_tcb_at_def obj_at_def)

lemma not_in_set_via_tcb_state:
  "\<lbrakk>\<forall>t \<in> set q. st_tcb_at P t s; st_tcb_at P' t s; \<And>st. P st \<Longrightarrow> \<not> P' st\<rbrakk> \<Longrightarrow> t \<notin> set q"
  by (fastforce simp: pred_tcb_at_def obj_at_def)

lemma ep_queues_disjoint:
  "\<lbrakk>ep_queues_blocked s; ep_queues_of s p = Some q; ep_queues_of s p' = Some q'; p \<noteq> p'\<rbrakk>
   \<Longrightarrow> set q \<inter> set q' = {}"
  apply (simp add: ep_queues_blocked_def)
  apply (rule disjoint_via_tcb_state)
    apply (fastforce dest!: spec[where x=p])
   apply (fastforce dest!: spec[where x=p'])
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma ntfn_queues_disjoint:
  "\<lbrakk>ntfn_queues_blocked s; ntfn_queues_of s p = Some q; ntfn_queues_of s p' = Some q'; p \<noteq> p'\<rbrakk>
   \<Longrightarrow> set q \<inter> set q' = {}"
  apply (simp add: ntfn_queues_blocked_def)
  apply (rule disjoint_via_tcb_state)
    apply (fastforce dest!: spec[where x=p])
   apply (fastforce dest!: spec[where x=p'])
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma ep_queues_ntfn_queues_disjoint:
  "\<lbrakk>ep_queues_blocked s; ntfn_queues_blocked s;
    ep_queues_of s p = Some q; ntfn_queues_of s p' = Some q'\<rbrakk>
   \<Longrightarrow> set q \<inter> set q' = {}"
  apply (simp add: ep_queues_blocked_def ntfn_queues_blocked_def ep_blocked_def ntfn_blocked_def)
  apply (rule disjoint_via_tcb_state)
    apply (fastforce dest!: spec[where x=p])
   apply (fastforce dest!: spec[where x=p'])
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma ep_queues_ready_queues_disjoint:
  "\<lbrakk>ep_queues_blocked s; ready_queues_runnable s; ep_queues_of s p = Some q\<rbrakk>
   \<Longrightarrow> set q \<inter> set (ready_queues s domain priority) = {}"
  apply (simp add: ep_queues_blocked_def ready_queues_runnable_def ep_blocked_def)
  apply (rule disjoint_via_tcb_state[where P'=runnable])
    apply (fastforce dest!: spec[where x=p])
   apply fastforce
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma ntfn_queues_ready_queues_disjoint:
  "\<lbrakk>ntfn_queues_blocked s; ready_queues_runnable s; ntfn_queues_of s p = Some q\<rbrakk>
   \<Longrightarrow> set q \<inter> set (ready_queues s domain priority) = {}"
  apply (simp add: ntfn_queues_blocked_def ready_queues_runnable_def ntfn_blocked_def)
  apply (rule disjoint_via_tcb_state[where P'=runnable])
    apply (fastforce dest!: spec[where x=p])
   apply fastforce
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma ep_queues_release_queue_disjoint:
  "\<lbrakk>ep_queues_blocked s; release_q_runnable s; ep_queues_of s p = Some q\<rbrakk>
   \<Longrightarrow> set q \<inter> set (release_queue s) = {}"
  apply (simp add: ep_queues_blocked_def release_q_runnable_def ep_blocked_def)
  apply (rule disjoint_via_tcb_state[where P'=runnable])
    apply (fastforce dest!: spec[where x=p])
   apply fastforce
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma ntfn_queues_release_queue_disjoint:
  "\<lbrakk>ntfn_queues_blocked s; release_q_runnable s; ntfn_queues_of s p = Some q\<rbrakk>
   \<Longrightarrow> set q \<inter> set (release_queue s) = {}"
  apply (simp add: ntfn_queues_blocked_def release_q_runnable_def ntfn_blocked_def)
  apply (rule disjoint_via_tcb_state[where P'=runnable])
    apply (fastforce dest!: spec[where x=p])
   apply fastforce
  apply (rename_tac st, case_tac st; clarsimp)
  done

lemma runnable_not_in_ep_queue:
  "\<lbrakk>st_tcb_at runnable tcbPtr s; ep_queues_of s p = Some q; ep_queues_blocked s\<rbrakk>
   \<Longrightarrow> tcbPtr \<notin> set q"
  apply (rule_tac P="\<lambda>st. ep_blocked st = Some p" and s=s in not_in_set_via_tcb_state)
    apply (fastforce simp: ep_queues_blocked_def opt_map_def ep_blocked_def)
   apply fastforce
  apply (rename_tac st, case_tac st; clarsimp simp: ep_blocked_def)
  done

lemma runnable_not_in_ntfn_queue:
  "\<lbrakk>st_tcb_at runnable tcbPtr s; ntfn_queues_of s p = Some q; ntfn_queues_blocked s\<rbrakk>
   \<Longrightarrow> tcbPtr \<notin> set q"
  apply (rule_tac P="\<lambda>st. ntfn_blocked st = Some p" and s=s in not_in_set_via_tcb_state)
    apply (force simp: ntfn_queues_blocked_def)
   apply simp
  apply (rename_tac st, case_tac st; clarsimp simp: ntfn_blocked_def)
  done

lemma runnable'_not_inIPCQueueThreadState:
  "st_tcb_at' runnable' t s \<Longrightarrow> \<not> (inIPCQueueThreadState |< tcbStates_of' s) t"
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def opt_pred_def opt_map_red
                        inIPCQueueThreadState_def)
  by (rename_tac tcb, case_tac "tcbState tcb"; clarsimp)

crunch set_tcb_queue
  for ep_queues_blocked[wp]: ep_queues_blocked
  and ntfn_queues_blocked[wp]: ntfn_queues_blocked
  (wp: ep_queues_blocked_lift ntfn_queues_blocked_lift)

lemma set_endpoint_ep_queues_of_other:
  "\<lbrace>\<lambda>s. P (ep_queues_of s p) \<and> p \<noteq> ep_ptr\<rbrace>
   set_endpoint ep_ptr ep
   \<lbrace>\<lambda>_ s. P (ep_queues_of s p)\<rbrace>"
  apply (wpsimp wp: set_simple_ko_wp)
  by (clarsimp simp: eps_of_kh_def opt_map_def)

lemma threadSet_dom_tcbs_of'[wp]:
  "threadSet f tcbPtr \<lbrace>\<lambda>s. P (dom (tcbs_of' s))\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (fastforce elim: rsubst[where P=P] simp: opt_map_def obj_at'_def)

crunch tcbQueueRemove, orderedInsert
  for dom_tcbs_of'[wp]: "\<lambda>s. P (dom (tcbs_of' s))"
  (wp: crunch_wps)

crunch tcbQueueRemove, orderedInsert, updateEndpoint, updateNotification
  for tcbIPCBuffers_of[wp]: "\<lambda>s. P (tcbIPCBuffers_of s)"
  and tcbArches_of[wp]: "\<lambda>s. P (tcbArches_of s)"
  and tcbStates_of'[wp]: "\<lambda>s. P (tcbStates_of' s)"
  and tcbFaults_of[wp]: "\<lambda>s. P (tcbFaults_of s)"
  and tcbCTables_of[wp]: "\<lambda>s. P (tcbCTables_of s)"
  and tcbVTables_of[wp]: "\<lambda>s. P (tcbVTables_of s)"
  and tcbFaultHandlers_of[wp]: "\<lambda>s. P (tcbFaultHandlers_of s)"
  and tcbTimeoutHandlers_of[wp]: "\<lambda>s. P (tcbTimeoutHandlers_of s)"
  and tcbIPCBufferFrames_of[wp]: "\<lambda>s. P (tcbIPCBufferFrames_of s)"
  and tcbBoundNotifications_of[wp]: "\<lambda>s. P (tcbBoundNotifications_of s)"
  and tcbSchedContexts_of[wp]: "\<lambda>s. P (tcbSchedContexts_of s)"
  and tcbYieldTos_of[wp]: "\<lambda>s. P (tcbYieldTos_of s)"
  and tcbMCPs_of[wp]: "\<lambda>s. P (tcbMCPs_of s)"
  and tcbPriorities_of[wp]: "\<lambda>s. P (tcbPriorities_of s)"
  and tcbDomains_of[wp]: "\<lambda>s. P (tcbDomains_of s)"
  and tcbFlags_of[wp]: "\<lambda>s. P (tcbFlags_of s)"
  (wp: crunch_wps threadSet_field_inv)

lemma set_tcb_queue_det_wp[wp]:
  "det_wp \<top> (set_tcb_queue d p queue)"
  by (wpsimp simp: set_tcb_queue_def)

lemmas set_tcb_queue_no_fail[wp] = det_wp_no_fail[OF set_tcb_queue_det_wp]

lemma set_tcb_queue_ready_queues_other:
  "\<lbrace>\<lambda>s. P (ready_queues s d p) \<and> (domain \<noteq> d \<or> priority \<noteq> p)\<rbrace>
   set_tcb_queue domain priority q
   \<lbrace>\<lambda>_ s. P (ready_queues s d p)\<rbrace>"
  by (wpsimp simp: set_tcb_queue_def)

lemma rcorres_threadSet_list_queue_relation:
  "\<lbrakk>\<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb;
    \<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb\<rbrakk> \<Longrightarrow>
   rcorres
     (\<lambda>_ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
     (return rv) (threadSet F t)
     (\<lambda>_ _ _ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule rcorres_from_valid_det; wpsimp wp: threadSet_wp)
  apply (fastforce elim: list_queue_relation_cong simp: opt_map_def obj_at'_def)
  done

lemma rcorres_setQueue_list_queue_relation_other:
  "rcorres
     (\<lambda>_ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
     (set_tcb_queue d p ls') (setQueue d p q')
     (\<lambda>_ _ _ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  by (rule rcorres_from_valid_det; wpsimp)

lemma rcorres_setQueue_list_queue_relation[rcorres]:
  "\<lbrakk>domain = d; priority = p\<rbrakk> \<Longrightarrow>
   rcorres
     (\<lambda>_ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
     (set_tcb_queue domain priority ls) (setQueue domain priority q)
     (\<lambda>_ _ s s'. list_queue_relation (ready_queues s d p) (ksReadyQueues s' (d, p))
                                     (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  apply (wpsimp simp: setQueue_def set_tcb_queue_def)
  apply (clarsimp simp: in_monad)
  done

lemma rcorres_threadSet_ready_queues_list_queue_relation:
  "\<lbrakk>\<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb;
    \<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb\<rbrakk> \<Longrightarrow>
   rcorres
     (\<lambda>s s'. list_queue_relation (ready_queues s d p) (ksReadyQueues s' (d, p))
                                 (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
     (return ls) (threadSet F t)
     (\<lambda>_ _ s s'. list_queue_relation (ready_queues s d p) (ksReadyQueues s' (d, p))
                                     (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc[where Q="\<top>\<top>", simplified])
  apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs[where Q="\<top>\<top>", simplified])
    apply (rule rcorres_weaken_pre[OF rcorres_threadSet_list_queue_relation])
    apply wpsimp+
  done

lemma rcorres_threadSet_release_queue_list_queue_relation:
  "\<lbrakk>\<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb;
    \<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb\<rbrakk> \<Longrightarrow>
   rcorres
     (\<lambda>s s'. list_queue_relation (release_queue s) (ksReleaseQueue s')
                                 (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
     (return ls) (threadSet F t)
     (\<lambda>_ _ s s'. list_queue_relation (release_queue s) (ksReleaseQueue s')
                                     (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule_tac p="\<lambda>s'. ksReleaseQueue s'" in rcorres_lift_conc[where Q="\<top>\<top>", simplified])
  apply (rule_tac p="\<lambda>s. release_queue s" in rcorres_lift_abs[where Q="\<top>\<top>", simplified])
    apply (rule rcorres_weaken_pre[OF rcorres_threadSet_list_queue_relation])
    apply wpsimp+
  done

lemma rcorres_setReleaseQueue_list_queue_relation_other:
  "rcorres
     (\<lambda>_ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
     (set_release_queue ls') (setReleaseQueue q')
     (\<lambda>_ _ _ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  by (rule rcorres_from_valid_det; wpsimp wp: threadSet_wp)

lemma rcorres_setReleaseQueue_list_queue_relation[rcorres]:
  "rcorres
     (\<lambda>_ s'. list_queue_relation ls q (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
     (set_release_queue ls) (setReleaseQueue q)
     (\<lambda>_ _ s s'. list_queue_relation (release_queue s) (ksReleaseQueue s')
                                     (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))"
  apply (rule rcorres_from_valid_det; (solves wpsimp)?)
  apply (wpsimp simp: setReleaseQueue_def)
  apply (clarsimp simp: in_monad)
  done

crunch tcbQueueRemove, orderedInsert, updateEndpoint, updateNotification
  for ctes_of'[wp]: "\<lambda>s. P (ctes_of' s)"
  and replies_of[wp]: "\<lambda>s. P (replies_of' s)"
  and scs_of'[wp]: "\<lambda>s. P (scs_of' s)"
  and userDataDevice_at[wp]: "\<lambda>s. P (userDataDevice_at s)"
  and userData_at[wp]: "\<lambda>s. P (userData_at s)"
  and kernelData_at[wp]: "\<lambda>s. P (kernelData_at s)"
  and aobjs_of'[wp]: "\<lambda>s. P (aobjs_of' s)"
  (wp: crunch_wps)

locale TcbAcc_R_2 = TcbAcc_R +
  assumes removeFromBitmap_valid_bitmapQ_except:
    "\<And>d p. removeFromBitmap d p \<lbrace>valid_bitmapQ_except d p \<rbrace>"
  assumes removeFromBitmap_bitmapQ_no_L2_orphans[wp]:
    "\<And>d p.
     \<lbrace> bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans \<rbrace>
     removeFromBitmap d p
     \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  assumes removeFromBitmap_bitmapQ_no_L1_orphans[wp]:
    "\<And>d p. removeFromBitmap d p \<lbrace> bitmapQ_no_L1_orphans \<rbrace>"
  assumes addToBitmap_bitmapQ_no_L1_orphans[wp]:
    "\<And>d p. \<lbrace> bitmapQ_no_L1_orphans \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  assumes addToBitmap_valid_bitmapQ_except:
    "\<And>d p.
     \<lbrace> valid_bitmapQ_except d p and bitmapQ_no_L2_orphans \<rbrace>
       addToBitmap d p
     \<lbrace>\<lambda>_. valid_bitmapQ_except d p \<rbrace>"
  assumes lookupIPCBuffer_corres':
    "\<And>w t.
     corres (=)
       (tcb_at t and valid_objs and pspace_aligned and pspace_distinct)
       (valid_objs' and no_0_obj')
       (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  assumes setThreadState_state_hyp_refs_of'[wp]:
    "\<And>st t P. setThreadState st t \<lbrace>\<lambda>s. P ((state_hyp_refs_of' s))\<rbrace>"
  assumes storeWord_invs'[wp]:
    "\<And>p w. \<lbrace>pointerInUserData p and invs'\<rbrace> doMachineOp (storeWord p w) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  assumes user_getreg_inv'[wp]:
    "\<And>t r P. asUser t (getRegister r) \<lbrace>P\<rbrace>"
  assumes lookupIPCBuffer_inv[wp]:
    "\<And>w t P. lookupIPCBuffer w t \<lbrace>P\<rbrace>"
  assumes asUser_getRegister_corres:
    "\<And>t r.
     corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
            (as_user t (getRegister r)) (asUser t (getRegister r))"
  assumes rescheduleRequired_hyp_refs_of'[wp]:
    "\<And>P. rescheduleRequired \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  assumes tcbSchedEnqueue_hyp_refs_of'[wp]:
    "\<And>P t. tcbSchedEnqueue t \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  assumes asUser_setRegister_corres:
    "\<And>t r v.
     corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
               (as_user t (setRegister r v))
               (asUser t (setRegister r v))"
begin

lemma tcbSchedEnqueue_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (ep_queues_blocked and ntfn_queues_blocked
      and in_correct_ready_q and ready_qs_distinct and ready_queues_runnable
      and st_tcb_at runnable tcb_ptr and not_in_release_q tcb_ptr and ready_or_release
      and pspace_aligned and pspace_distinct)
     (valid_sched_pointers and valid_tcbs')
     (tcb_sched_action tcb_sched_enqueue tcb_ptr) (tcbSchedEnqueue tcbPtr)"
  supply if_split[split del] bind_return[simp del] return_bind[simp del]
  apply (rule_tac Q'="st_tcb_at' runnable' tcbPtr" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: vs_all_heap_simps obj_at_def is_tcb_def)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (clarsimp simp: tcb_sched_action_def tcb_sched_enqueue_def get_tcb_queue_def
                        tcbSchedEnqueue_def getQueue_def unless_def when_def)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac domain)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac priority)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce intro: ready_or_release_cross)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce dest: state_relation_release_queue_relation in_release_q_tcbInReleaseQueue_eq)
  apply (rule corres_stateAssert_ignore, fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_stateAssert_ignore, fastforce intro: ksReleaseQueue_asrt_cross)
  apply (rule corres_stateAssert_ignore, fastforce)+
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule_tac F="tcbPtr \<in> set (queues domain priority) \<longleftrightarrow> queued" in corres_req)
   subgoal
     by (fastforce dest!: state_relation_ready_queues_relation
                          in_ready_q_tcbQueued_eq[THEN arg_cong_Not, where t1=tcbPtr]
                    simp: obj_at'_def opt_pred_def opt_map_def in_correct_ready_q_def
                          vs_all_heap_simps obj_at_def in_ready_q_def)
  apply (case_tac queued; clarsimp)
  apply (clarsimp simp: return_bind)
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
  apply (rule corres_split_skip)
     apply wpsimp
    apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_ex_lift hoare_vcg_imp_lift')
   apply (corres corres: addToBitmap_if_null_noop_corres)
  apply (rule_tac F="tdom = domain \<and> prio = priority" in corres_req)
   apply (fastforce dest: pspace_relation_tcb_domain_priority state_relation_pspace_relation
                    simp: obj_at_def obj_at'_def)
  \<comment> \<open>set the ready queue\<close>
  apply clarsimp
  apply (rule corres_underlying_from_rcorres)
   apply (wpsimp wp: no_fail_tcbQueuePrepend hoare_vcg_imp_lift' hoare_vcg_if_lift2)
   apply (clarsimp simp: ex_abs_def obj_at_def split: if_splits)
   apply normalise_obj_at'
   apply (rename_tac s tcb tcb')
   apply (frule state_relation_ready_queues_relation)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (rule_tac x="ready_queues s (tcbDomain tcb) (tcbPriority tcb)" in exI)
   apply clarsimp
   apply (rule conjI)
    apply (fastforce intro!: tcb_at_cross simp: ready_queues_runnable_def)
   apply (force dest!: state_relation_ready_queues_relation in_ready_q_tcbQueued_eq[THEN iffD1]
                 simp: in_ready_q_def)
  apply (clarsimp simp: state_relation_def pspace_relation_heap_pspace_relation
                        ghost_relation_heap_ghost_relation heap_pspace_relation_def)
  apply (rcorres_conj_lift \<open>fastforce\<close> simp: set_tcb_queue_def wp: threadSet_field_inv)+
  apply (rule rcorres_add_return_l)
  apply (subst bind_assoc[symmetric])
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ep_queues_relation\<close>
   apply (simp only: ep_queues_relation_def)
   apply (rcorres rcorres: tcbQueuePrepend_rcorres_other rcorres_threadSet_list_queue_relation
                           rcorres_op_lifts)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def obj_at_def)
   apply (thin_tac "valid_sched_pointers _")
   apply (metis runnable_not_in_ep_queue ep_queues_ready_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ntfn_queues_relation\<close>
   apply (simp only: ntfn_queues_relation_def)
   apply (rcorres rcorres: tcbQueuePrepend_rcorres_other rcorres_threadSet_list_queue_relation
                           rcorres_op_lifts)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def obj_at_def)
   apply (thin_tac "valid_sched_pointers _")
   apply (metis runnable_not_in_ntfn_queue ntfn_queues_ready_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ready_queues_relation\<close>
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (intro rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac d p)
   apply (case_tac "d \<noteq> domain \<or> p \<noteq> priority")
    apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
     apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs)
      apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc)
       apply (rcorres rcorres: rcorres_threadSet_list_queue_relation tcbQueuePrepend_rcorres_other)
       apply (clarsimp simp: obj_at_def)
       apply (thin_tac "valid_sched_pointers _")
       apply (metis in_correct_ready_qD ready_queues_disjoint)
      apply (wpsimp wp: setQueue_ksReadyQueues_other)
     apply (wpsimp wp: set_tcb_queue_ready_queues_other)
    apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
     apply (intro rcorres_allI_fwd; (solves wpsimp)?)
     apply (rename_tac t)
     apply (rule_tac p="\<lambda>s. t \<in> set (ready_queues s d p)" in rcorres_lift_abs)
      apply (rule_tac p="\<lambda>s'. (inQ d p |< tcbs_of' s') t" in rcorres_lift_conc)
       apply (rcorres rcorres: rcorres_prop)
       apply force
      apply (wpsimp wp: tcbQueued_update_inQ_other hoare_vcg_disj_lift
                  simp: opt_pred_disj[simplified pred_disj_def, symmetric] simp_del: disj_not1)
      apply (clarsimp simp: opt_pred_def opt_map_red obj_at'_def)
     apply (wpsimp wp: set_tcb_queue_ready_queues_other)
    apply (rule rcorres_lift_conc_only; wpsimp wp: setQueue_ksReadyQueues_other)
   \<comment> \<open>d = domain \<and> p = priority\<close>
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rcorres rcorres: tcbQueuePrepend_rcorres
                            rcorres_threadSet_ready_queues_list_queue_relation)
    apply clarsimp
    apply (frule valid_sched_pointersD[where t=tcbPtr])
       apply (clarsimp simp: opt_pred_def opt_map_red obj_at'_def)
      apply (clarsimp simp: opt_pred_def opt_map_red obj_at'_def)
     apply (elim runnable'_not_inIPCQueueThreadState)
    apply (clarsimp simp: opt_pred_def opt_map_red obj_at'_def)
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (intro rcorres_allI_fwd; (solves wpsimp)?)
    apply (rename_tac t)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (clarsimp simp: set_tcb_queue_def in_monad)
    apply (case_tac "t \<noteq> tcbPtr")
     apply (wpsimp wp: threadSet_opt_pred_other)
    apply (wpsimp wp: tcbQueued_True_makes_inQ)
    apply (force simp: obj_at'_def opt_pred_def opt_map_red)
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rule rcorres_imp_lift_fwd; (solves wpsimp)?)
     apply (rule rcorres_prop_fwd; wpsimp)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (wpsimp wp: setQueue_ksReadyQueues_other)
    apply (force dest!: valid_tcbs'_maxDomain[where t=tcbPtr] simp: obj_at'_def)
   apply (rule rcorres_imp_lift_fwd; (solves wpsimp)?)
    apply (rule rcorres_prop_fwd; wpsimp)
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (wpsimp wp: setQueue_ksReadyQueues_other)
   apply (force dest!: valid_tcbs'_maxPriority[where t=tcbPtr] simp: obj_at'_def)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>release_queue_relation\<close>
   apply (clarsimp simp: release_queue_relation_def)
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rule_tac p=release_queue in rcorres_lift_abs)
     apply (rule_tac p=ksReleaseQueue in rcorres_lift_conc)
      apply (rcorres rcorres: tcbQueuePrepend_rcorres_other rcorres_threadSet_list_queue_relation)
      apply normalise_obj_at'
      apply (subst Int_commute)
      apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def obj_at_def)
      apply (thin_tac "valid_sched_pointers_2 _ _ _")
      apply (metis ready_or_release_disjoint)
     apply wpsimp
    apply wpsimp
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (wpsimp wp: hoare_vcg_all_lift)
   apply (clarsimp simp: set_tcb_queue_def in_monad)
  by (rcorres_conj_lift \<open>fastforce\<close> simp: set_tcb_queue_def wp: threadSet_field_inv)+

end (* TcbAcc_R_2 *)

definition weak_sch_act_wf :: "scheduler_action \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "weak_sch_act_wf sa s \<equiv> \<forall>t. sa = SwitchToThread t \<longrightarrow> tcb_at' t s"

defs weak_sch_act_wf_asrt_def:
  "weak_sch_act_wf_asrt \<equiv> \<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"

declare weak_sch_act_wf_asrt_def[simp]

lemma weak_sch_act_wf_updates[simp]:
  "\<And>f. weak_sch_act_wf sa (ksDomainTime_update f s) = weak_sch_act_wf sa s"
  "\<And>f. weak_sch_act_wf sa (ksReprogramTimer_update f s) = weak_sch_act_wf sa s"
  "\<And>f. weak_sch_act_wf sa (ksReleaseQueue_update f s) = weak_sch_act_wf sa s"
  by (auto simp: weak_sch_act_wf_def tcb_in_cur_domain'_def)

lemma (in TcbAcc_R) setSchedulerAction_corres:
  "sched_act_relation sa sa'
    \<Longrightarrow> corres dc \<top> \<top> (set_scheduler_action sa) (setSchedulerAction sa')"
  apply (simp add: setSchedulerAction_def set_scheduler_action_def)
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp: in_monad simpler_modify_def state_relation_def
                        ready_queues_relation_def release_queue_relation_def swp_def)
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
  apply (wpsimp wp: threadGet_wp)
  apply (clarsimp simp: obj_at'_def)
  done

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

crunch getReleaseQueue, setReleaseQueue
 for (no_fail) no_fail[wp]

lemma no_ofail_readInReleaseQueue[wp]:
  "no_ofail (tcb_at' tcbPtr) (readInReleaseQueue tcbPtr)"
  unfolding readInReleaseQueue_def
  by wpsimp

lemmas no_fail_inReleaseQueue[wp] =
  no_ofail_gets_the[OF no_ofail_readInReleaseQueue, simplified inReleaseQueue_def[symmetric]]

lemma inReleaseQueue_sp:
  "\<lbrace>P\<rbrace>
   inReleaseQueue tcb_ptr
   \<lbrace>\<lambda>rv s. \<exists>tcb'. ko_at' tcb' tcb_ptr s \<and> rv = (tcbInReleaseQueue tcb') \<and> P s\<rbrace>"
  unfolding inReleaseQueue_def readInReleaseQueue_def
  apply (wpsimp wp: hoare_case_option_wp getObject_tcb_wp simp: threadGet_getObject)
  apply (clarsimp dest!: threadRead_SomeD simp: obj_at'_def)
  done

lemma inReleaseQueue_corres:
  "corres (\<longleftrightarrow>)
     (tcb_at tcbPtr and pspace_aligned and pspace_distinct) \<top>
     (gets (in_release_queue tcbPtr)) (inReleaseQueue tcbPtr)"
  apply (rule_tac Q'="tcb_at' tcbPtr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD elim!: tcb_at_cross)
  apply (rule corres_bind_return)
  apply (rule corres_bind_return2)
  apply (rule corres_symb_exec_l[rotated, OF _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[rotated, OF inReleaseQueue_sp]; (solves \<open>wpsimp\<close>)?)
   apply (wpsimp wp: inReleaseQueue_wp)
   apply normalise_obj_at'
  apply (drule state_relation_release_queue_relation)
  apply (clarsimp simp: release_queue_relation_def list_queue_relation_def)
  apply (force simp: in_queue_2_def obj_at'_def opt_pred_def opt_map_def)
  done

lemma isRunnable_corres:
  "tcb_relation tcb_abs tcb_conc \<Longrightarrow>
   corres (=)
          (tcb_at t)
          (ko_at' tcb_conc t)
          (return (runnable (tcb_state tcb_abs)))
          (isRunnable t)"
  apply (clarsimp simp: isRunnable_def readRunnable_def getThreadState_def
             simp flip: threadGet_def)
  apply (rule corres_symb_exec_r[where Q'="\<lambda>rv s. tcbState tcb_conc = rv"])
     apply (case_tac "tcb_state tcb_abs"; clarsimp simp: tcb_relation_def)
    apply (wpsimp wp: threadGet_wp)
    apply (fastforce simp: obj_at'_def)
   apply (rule tcb_inv_collection)
  apply (rule no_fail_pre[OF no_fail_threadGet])
  apply (clarsimp simp: obj_at'_weaken)
  done

lemma scActive_sp:
  "\<lbrace>P\<rbrace> scActive scPtr \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. ko_at' sc scPtr s \<and> rv = (0 < scRefillMax sc))\<rbrace>"
  apply wpsimp
  apply (clarsimp simp: obj_at'_def)
  done

lemma pspace_relation_sc_relation:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); kheap s ptr = Some (Structures_A.SchedContext sc n);
    ksPSpace s' ptr = Some (KOSchedContext sc')\<rbrakk>
   \<Longrightarrow> sc_relation sc n sc'"
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=ptr in bspec)
   apply (fastforce simp: obj_at_def)
  apply (clarsimp simp: obj_at_def obj_at'_def split: if_splits)
  done

lemma no_ofail_readScActive[wp]:
  "no_ofail (sc_at' scPtr) (readScActive scPtr)"
  unfolding readScActive_def readSchedContext_def
  by (wpsimp wp_del: ovalid_readObject)

lemmas no_fail_scActive[wp] =
  no_ofail_gets_the[OF no_ofail_readScActive, simplified scActive_def[symmetric]]

crunch inReleaseQueue
  for inv[wp]: P

defs active_sc_at'_asrt_def:
  "active_sc_at'_asrt \<equiv> active_sc_at'"

declare active_sc_at'_asrt_def[simp]

lemma ko_at'_valid_tcbs'_valid_tcb':
  "\<lbrakk>ko_at' ko ptr s; valid_tcbs' s\<rbrakk> \<Longrightarrow> valid_tcb' ko s"
  by (fastforce simp: valid_tcbs'_def obj_at'_def)

definition schedulable' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "schedulable' tcbPtr s' \<equiv>
   (runnable' |< (tcbs_of' s' ||> tcbState)) tcbPtr
   \<and> active_sc_tcb_at' tcbPtr s'
   \<and> \<not> (tcbInReleaseQueue |< tcbs_of' s') tcbPtr"

lemma getSchedulable_wp:
  "\<lbrace>\<lambda>s. \<forall>t. schedulable' tcbPtr s = t \<and> tcb_at' tcbPtr s \<longrightarrow> P t s\<rbrace> getSchedulable tcbPtr \<lbrace>P\<rbrace>"
  apply (clarsimp simp: getSchedulable_def readSchedulable_def
                        ohaskell_state_assert_def gets_the_if_distrib)
  apply (subst gets_the_obind inReleaseQueue_def[symmetric] scActive_def[symmetric]
               isRunnable_def[symmetric] threadGet_def[symmetric] gets_the_ostate_assert)+
  apply (wpsimp wp: inReleaseQueue_wp threadGet_wp)
  apply normalise_obj_at'
  apply (fastforce elim!: rsubst2[where P=P]
                    simp: schedulable'_def opt_pred_def opt_map_def obj_at'_def
                          active_sc_tcb_at'_def)
  done

lemma getSchedulable_sp:
  "\<lbrace>P\<rbrace> getSchedulable tcbPtr \<lbrace>\<lambda>rv s. rv = schedulable' tcbPtr s \<and> P s\<rbrace>"
  by (wpsimp wp: getSchedulable_wp)

lemma isSchedulable_inv[wp]:
  "getSchedulable tcbPtr \<lbrace>P\<rbrace>"
  by (wpsimp wp: getSchedulable_wp)

lemma no_ofail_readSchedulable:
  "no_ofail (tcb_at' tcbPtr and valid_tcbs') (readSchedulable tcbPtr)"
  unfolding readSchedulable_def ohaskell_state_assert_def
  apply (wpsimp wp: ovalid_threadRead)
  apply normalise_obj_at'
  apply (fastforce dest: ko_at'_valid_tcbs'_valid_tcb' simp: valid_tcb'_def)
  done

lemmas no_fail_getSchedulable =
  no_ofail_gets_the[OF no_ofail_readSchedulable, simplified getSchedulable_def[symmetric]]

lemma threadSet_schedulable'_fields_inv:
  "\<lbrakk>\<And>tcb. tcbState (f tcb) = tcbState tcb; \<And>tcb. tcbSchedContext (f tcb) = tcbSchedContext tcb;
    \<And>tcb. tcbInReleaseQueue (f tcb) = tcbInReleaseQueue tcb\<rbrakk>
   \<Longrightarrow> threadSet f tcbPtr \<lbrace>\<lambda>s. P (schedulable' tcbPtr' s)\<rbrace>"
  unfolding schedulable'_def threadSet_def
  apply (wpsimp wp: setObject_tcb_wp getTCB_wp)
  apply (erule rsubst[where P=P])
  apply (wpsimp wp: setObject_tcb_wp simp: obj_at'_def)
  apply (clarsimp simp: opt_pred_def opt_map_def active_sc_tcb_at'_def split: option.splits)
  done

lemma updateSchedContext_schedulable':
  "(\<And>sc. scRefillMax (f sc) = scRefillMax sc)
   \<Longrightarrow> updateSchedContext scPtr f \<lbrace>\<lambda>s. P (schedulable' tcbPtr s)\<rbrace>"
  apply (wpsimp wp: updateSchedContext_wp)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: schedulable'_def)
  by (fastforce simp: opt_pred_def opt_map_def obj_at'_def active_sc_tcb_at'_def
               split: option.splits if_splits)

lemma runnable_tsr:
  "thread_state_relation ts ts' \<Longrightarrow> runnable' ts' = runnable ts"
  by (case_tac ts, auto)

lemma runnable_runnable'_eq:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; tcb_at t s\<rbrakk>
   \<Longrightarrow> (runnable |< (tcbs_of s ||> tcb_state)) t = (runnable' |< (tcbs_of' s' ||> tcbState)) t"
  apply (frule state_relation_pspace_relation)
  apply (frule (3) tcb_at_cross)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  by (fastforce dest: pspace_relation_tcb_relation[where ptr=t] runnable_tsr
                simp: obj_at'_def tcb_relation_def opt_pred_def opt_map_def tcbs_of_kh_def
               split: Structures_A.kernel_object.splits)

lemma sc_active_cross_eq:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; tcb_at t s; valid_tcbs s\<rbrakk>
   \<Longrightarrow> (sc_active |< (tcbs_of s |> tcb_sched_context |> scs_of s)) t = active_sc_tcb_at' t s'"
  apply (clarsimp simp: active_sc_tcb_at'_def)
  apply (frule state_relation_pspace_relation)
  apply (frule (3) tcb_at_cross)
  apply normalise_obj_at'
  apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
  apply (rename_tac tcb)
  apply (clarsimp simp: obj_at'_def)
  apply (frule (2) pspace_relation_tcb_relation[where ptr=t])
  apply (case_tac "tcb_sched_context tcb = None")
   apply (clarsimp simp: tcb_relation_def opt_pred_def opt_map_def tcbs_of_kh_def)
  apply clarsimp
  apply (rename_tac scPtr)
  apply (prop_tac "sc_at' scPtr s'")
   apply (fastforce elim!: sc_at_cross dest: valid_tcbs_valid_tcb
                     simp: valid_tcb_def get_tcb_def split: option.splits)
  apply (frule (1) sc_at'_cross)
  apply (clarsimp simp: obj_at_def is_sc_obj_def)
  by (auto dest: pspace_relation_sc_relation
           simp: tcb_relation_def opt_pred_def opt_map_def tcbs_of_kh_def scs_of_kh_def
                 sc_relation_def active_sc_def obj_at'_def
          split: Structures_A.kernel_object.splits option.splits)

lemma schedulable_schedulable'_eq:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; tcb_at t s; valid_tcbs s\<rbrakk>
   \<Longrightarrow> schedulable t s = schedulable' t s'"
  apply (clarsimp simp: schedulable_def schedulable'_def)
  apply (intro conj_cong)
    apply (fastforce dest: runnable_runnable'_eq)
   apply (fastforce dest: sc_active_cross_eq)
  apply (frule state_relation_release_queue_relation)
  apply (force dest!: in_release_q_tcbInReleaseQueue_eq simp: in_release_q_def)
  done

lemma getSchedulable_corres:
  "corres (=)
     (valid_tcbs and pspace_aligned and pspace_distinct and tcb_at t) valid_tcbs'
     (gets (schedulable t)) (getSchedulable t)"
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (fastforce intro: tcb_at_cross)
  apply (rule corres_bind_return2)
  apply (rule corres_symb_exec_r_conj_ex_abs_forwards[OF _ getSchedulable_sp, rotated]; (solves wpsimp)?)
   apply (wpsimp wp: no_fail_getSchedulable)
  apply (rule corres_gets_return_trivial)
  apply (fastforce dest: schedulable_schedulable'_eq)
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

context TcbAcc_R_2 begin

lemma rescheduleRequired_corres_weak:
  "corres dc
     (ep_queues_blocked and ntfn_queues_blocked and valid_tcbs and in_correct_ready_q
      and weaker_valid_sched_action and pspace_aligned and pspace_distinct
      and active_scs_valid and ready_or_release and ready_qs_distinct and ready_queues_runnable)
     (valid_tcbs' and valid_sched_pointers)
     reschedule_required rescheduleRequired"
  apply (simp add: rescheduleRequired_def reschedule_required_def)
  apply (rule corres_underlying_split[OF _ _ gets_sp, rotated 2])
    apply (clarsimp simp: getSchedulerAction_def)
    apply (rule gets_sp)
   apply (corresKsimp corres: getSchedulerAction_corres)
  apply (rule corres_underlying_split[where r'=dc, rotated]; (solves \<open>wpsimp\<close>)?)
   apply (corresKsimp corres: setSchedulerAction_corres)
  apply (case_tac action; clarsimp?)
  apply (rename_tac tp)
  apply (rule corres_underlying_split[OF _ _ gets_sp isSchedulable_inv, rotated 2])
   apply (corresKsimp corres: getSchedulable_corres)
   apply (clarsimp simp: weaker_valid_sched_action_def obj_at_def vs_all_heap_simps is_tcb_def)
  apply (clarsimp simp: when_def)

  apply (rule corres_symb_exec_l[OF _ thread_get_exs_valid thread_get_sp , rotated])
    apply (clarsimp simp: weaker_valid_sched_action_def vs_all_heap_simps obj_at_def is_tcb_def)
   apply (wpsimp simp: thread_get_def get_tcb_def weaker_valid_sched_action_def vs_all_heap_simps)
  apply (rule corres_assert_opt_assume_lhs[rotated])
    apply (clarsimp simp: obj_at_def schedulable_def opt_pred_def opt_map_def tcbs_of_kh_def
                   split: option.splits)

  apply (rule corres_symb_exec_l[OF _ _ get_sc_refill_sufficient_sp, rotated])
    apply (rule get_sc_refill_sufficient_exs_valid)
    apply (fastforce intro: valid_refills_nonempty_refills active_scs_validE
                      simp: obj_at_def vs_all_heap_simps schedulable_def2)
   apply wpsimp
    apply (fastforce intro: valid_refills_nonempty_refills active_scs_validE
                      simp: obj_at_def vs_all_heap_simps schedulable_def2)

  apply (rule corres_symb_exec_l[OF _ _ get_sc_refill_ready_sp, rotated])
    apply (wpsimp wp: get_sched_context_exs_valid gets_the_exs_valid
                simp: get_sc_refill_ready_def)
    apply (clarsimp intro!: no_ofailD[OF no_ofail_read_sc_refill_ready] simp: obj_at_def is_sc_obj)
    apply (fastforce intro: valid_refills_nonempty_refills active_scs_validE
                      simp: obj_at_def vs_all_heap_simps schedulable_def2)

   apply (wpsimp wp: get_sched_context_no_fail simp: get_sc_refill_ready_def)
    apply (fastforce intro: valid_refills_nonempty_refills active_scs_validE
                      simp: obj_at_def vs_all_heap_simps schedulable_def2)

  apply (rule stronger_corres_guard_imp)
    apply (rule corres_assert_assume_l)
    apply (rule tcbSchedEnqueue_corres)
    apply simp
   apply (clarsimp simp: schedulable_def2 get_tcb_def obj_at_def pred_tcb_at_def)
   apply (rule conjI)
    apply (fastforce dest: active_scs_validE[rotated]
                     simp: valid_refills_def rr_valid_refills_def vs_all_heap_simps
                           refill_sufficient_def refill_capacity_def
                    split: if_splits)
   apply (clarsimp simp: vs_all_heap_simps obj_at_def pred_tcb_at_def weaker_valid_sched_action_def)
  apply simp
  done

lemma rescheduleRequired_corres:
  "corres dc
     (ep_queues_blocked and ntfn_queues_blocked and valid_tcbs and weak_valid_sched_action
      and pspace_aligned and pspace_distinct and active_scs_valid
      and in_correct_ready_q and ready_or_release  and ready_qs_distinct and ready_queues_runnable)
     (valid_tcbs' and valid_sched_pointers)
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

end (* TcbAcc_R_2 *)

lemma weak_sch_act_wf_lift:
  assumes pre: "\<And>P. f \<lbrace>\<lambda>s. P (sa s)\<rbrace>"
               "\<And>t. f \<lbrace>tcb_at' t\<rbrace>"
  shows "f \<lbrace>\<lambda>s. weak_sch_act_wf (sa s) s\<rbrace>"
  apply (simp only: weak_sch_act_wf_def imp_conv_disj)
  apply (intro hoare_vcg_all_lift hoare_vcg_conj_lift hoare_vcg_disj_lift pre | simp)+
  done

crunch (in TcbAcc_R) tcbSchedEnqueue
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: weak_sch_act_wf_lift)

lemma rescheduleRequired_weak_sch_act_wf[wp]:
  "\<lbrace>\<top>\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp | simp add: rescheduleRequired_def setSchedulerAction_def weak_sch_act_wf_def)+

lemma (in TcbAcc_R) possibleSwitchTo_weak_sch_act_wf[wp]:
  "possibleSwitchTo target \<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding possibleSwitchTo_def
  apply (wpsimp wp: threadGet_wp inReleaseQueue_wp simp: setSchedulerAction_def)
  by (fastforce simp: weak_sch_act_wf_def obj_at'_def ps_clear_def)

lemma asUser_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    asUser t m \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift)

lemma doMachineOp_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     doMachineOp m \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (simp add: doMachineOp_def split_def tcb_in_cur_domain'_def | wp weak_sch_act_wf_lift)+

crunch removeFromBitmap, addToBitmap
  for pred_tcb_at'[wp]: "\<lambda>s. Q (pred_tcb_at' proj P' t s)"
  and obj_at'[wp]: "\<lambda>s. Q (obj_at' P t s)"

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

crunch removeFromBitmap
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"

lemma thread_get_test: "do cur_ts \<leftarrow> get_thread_state cur; g (test cur_ts) od =
       do t \<leftarrow> (thread_get (\<lambda>tcb. test (tcb_state tcb)) cur); g t od"
  apply (simp add: get_thread_state_def thread_get_def)
  done

context TcbAcc_R_2 begin

lemma set_thread_state_act_corres:
  "corres dc
     (valid_tcbs and pspace_aligned and pspace_distinct and tcb_at tcbPtr)
     valid_tcbs'
     (set_thread_state_act tcbPtr) (scheduleTCB tcbPtr)"
  apply (clarsimp simp: set_thread_state_act_def scheduleTCB_def)
  apply (rule corres_split_forwards'[OF _ gets_sp getCurThread_sp])
   apply (corres corres: getCurThread_corres)
  apply (rule corres_split_forwards'[OF _ gets_sp getSchedulerAction_sp])
   apply (corres corres: getSchedulerAction_corres)
  apply (rule corres_split_forwards'[OF _ gets_sp getSchedulable_sp])
   apply (corres corres: getSchedulable_corres)
  apply (clarsimp simp: scheduleTCB_def when_def split del: if_split)
  apply (rename_tac sched_act action schedulable)
  apply (rule corres_if_split)
    apply (case_tac sched_act; clarsimp)
   apply (corres corres: setSchedulerAction_corres)
  apply fastforce
  done

lemma setThreadState_corres:
  "thread_state_relation ts ts' \<Longrightarrow>
   corres dc
     (valid_tcbs and pspace_aligned and pspace_distinct and tcb_at t and valid_tcb_state ts)
     valid_tcbs'
     (set_thread_state t ts) (setThreadState ts' t)"
  apply (rule corres_cross_add_guard[where Q'="tcb_at' t"])
   apply (solves \<open>fastforce simp: state_relation_def intro: tcb_at_cross\<close>)
  apply (simp add: set_thread_state_def setThreadState_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF threadset_corresT]; simp?)
          apply (clarsimp simp: tcb_relation_def)
         apply (clarsimp simp: tcb_cap_cases_def)
        apply (clarsimp simp: tcb_cte_cases_def gen_objBits_simps tcb_cte_cases_neqs)
       apply (clarsimp simp: inQ_def)
      apply (rule set_thread_state_act_corres)
     apply (wpsimp wp: thread_set_valid_tcbs)
    apply (wpsimp wp: threadSet_valid_tcbs')
   apply wpsimp
   apply (fastforce intro: valid_tcb_state_update)
  apply (clarsimp simp: valid_tcb'_tcbState_update)
  done

lemma set_tcb_obj_ref_corresT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation (f (\<lambda>_. new) tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f (\<lambda>_. new) tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  assumes s: "\<forall>tcb'. tcbSchedPrev (f' tcb') = tcbSchedPrev tcb'"
             "\<forall>tcb'. tcbSchedNext (f' tcb') = tcbSchedNext tcb'"
  assumes f: "\<And>d p tcb'. inQ d p (f' tcb') = inQ d p tcb'"
             "\<And>tcb'. tcbInReleaseQueue (f' tcb') = tcbInReleaseQueue tcb'"
  shows
    "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
       (set_tcb_obj_ref f t new) (threadSet f' t)"
  using assms
  unfolding set_tcb_obj_ref_thread_set
  apply -
  by (corres corres: threadset_corresT simp: inQ_def)

lemmas set_tcb_obj_ref_corres =
    set_tcb_obj_ref_corresT [OF _ _ all_tcbI, OF _ ball_tcb_cap_casesI ball_tcb_cte_casesI]

lemma setBoundNotification_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (set_tcb_obj_ref tcb_bound_notification_update t ntfn) (setBoundNotification ntfn t)"
  apply (simp add: setBoundNotification_def)
  apply (rule set_tcb_obj_ref_corres; simp add: tcb_relation_def inQ_def)
  done

end (* TcbAcc_R_2 *)

crunch rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
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

context begin interpretation Arch . (* FIXME: arch-split RT *)

lemma tcbSchedNext_update_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_bound_tcb' ptrOpt\<rbrace>
   threadSet (tcbSchedNext_update (\<lambda>_. ptrOpt)) tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)
  done

lemma tcbSchedPrev_update_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_bound_tcb' ptrOpt\<rbrace>
   threadSet (tcbSchedPrev_update (\<lambda>_. ptrOpt)) tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)
  done

lemma tcbQueuePrepend_valid_objs'[wp]:
  "\<lbrace>valid_objs' and tcb_at' tcbPtr\<rbrace>
   tcbQueuePrepend queue tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbQueuePrepend_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (clarsimp simp: list_queue_relation_def tcbQueueEmpty_def)
  apply (rename_tac ts head)
  apply (prop_tac "ts \<noteq> []", fastforce)
  apply (fastforce dest: heap_path_head)
  done

crunch addToBitmap
  for valid_objs'[wp]: valid_objs'
  (simp: unless_def crunch_simps wp: crunch_wps)

lemma tcbSchedEnqueue_valid_objs'[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>valid_objs'\<rbrace>"
  unfolding tcbSchedEnqueue_def setQueue_def
  by (wpsimp wp: threadSet_valid_objs' threadGet_wp)

crunch rescheduleRequired, removeFromBitmap, scheduleTCB
  for valid_objs'[wp]: valid_objs'
  (simp: unless_def crunch_simps wp: crunch_wps)

lemma tcbQueueRemove_valid_objs'[wp]:
  "tcbQueueRemove queue tcbPtr \<lbrace>valid_objs'\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: hoare_vcg_imp_lift' getTCB_wp)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (clarsimp simp: valid_tcb'_def valid_bound_tcb'_def obj_at'_def split: none_top_split)
  done

lemma tcbSchedDequeue_valid_objs'[wp]:
  "tcbSchedDequeue t \<lbrace>valid_objs'\<rbrace>"
  unfolding tcbSchedDequeue_def setQueue_def
  by (wpsimp wp: threadSet_valid_objs' threadGet_wp)

lemma setThreadState_valid_objs'[wp]:
  "setThreadState st t \<lbrace>valid_objs'\<rbrace>"
  apply (wpsimp simp: setThreadState_def wp: threadSet_valid_objs')
  apply (simp add: valid_tcb'_def tcb_cte_cases_def objBits_simps')
  done

lemma sbn_valid_objs':
  "\<lbrace>valid_objs' and valid_bound_ntfn' ntfn\<rbrace>
  setBoundNotification ntfn t
  \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)
  done

crunch setBoundNotification
  for reply_projs[wp]: "\<lambda>s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)"
  and st_tcb_at'[wp]: "st_tcb_at' P p"
  and valid_replies' [wp]: valid_replies'
  (wp: valid_replies'_lift threadSet_pred_tcb_no_state)

lemma ssa_wp[wp]:
  "\<lbrace>\<lambda>s. P (s \<lparr>ksSchedulerAction := sa\<rparr>)\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: setSchedulerAction_def)

crunch removeFromBitmap
  for valid_replies'[wp]: "valid_replies'"
  (wp: valid_replies'_lift)

crunch rescheduleRequired, tcbSchedDequeue, scheduleTCB
  for st_tcb_at'[wp]: "st_tcb_at' P p"
  and valid_replies' [wp]: valid_replies'
  (wp: crunch_wps threadSet_pred_tcb_no_state valid_replies'_lift simp: crunch_simps)

crunch rescheduleRequired, tcbSchedDequeue, setThreadState
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and bounded'[wp]: pspace_bounded'
  and no_0_obj'[wp]: no_0_obj'
  and pspace_canonical'[wp]: pspace_canonical'
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps simp: crunch_simps)

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
  "\<lbrace>valid_pspace' and tcb_at' t
    and (\<lambda>s. \<forall>rptr. st_tcb_at' ((=) (BlockedOnReply (Some rptr))) t s
                    \<longrightarrow> st = BlockedOnReply (Some rptr) \<or> \<not> is_reply_linked rptr s)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wpsimp wp: sts'_valid_replies')
  by (auto simp: opt_map_def)

abbreviation is_replyState :: "thread_state \<Rightarrow> bool" where
  "is_replyState st \<equiv> is_BlockedOnReply st \<or> is_BlockedOnReceive st"

lemma setObject_tcb_valid_replies'_except_Blocked:
  "\<lbrace>\<lambda>s. valid_replies'_except {rptr} s \<and> replyTCBs_of s rptr = Some t
        \<and> st_tcb_at' (\<lambda>st. is_replyState st \<longrightarrow> replyObject st = None) t s
        \<and> (tcbState v = BlockedOnReply (Some rptr))\<rbrace>
   setObject t (v :: tcb)
   \<lbrace>\<lambda>rv. valid_replies'\<rbrace>"
  supply opt_mapE[elim!]
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

lemma sbn'_valid_pspace'_inv[wp]:
  "\<lbrace>valid_pspace' and valid_bound_ntfn' ntfn\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  apply (clarsimp simp: setBoundNotification_def valid_pspace'_def)
  apply (wpsimp wp: threadSet_valid_replies' threadSet_valid_objs' threadSet_mdb')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

end

crunch setQueue
  for pred_tcb_at'[wp]: "\<lambda>s. P (pred_tcb_at' proj P' t s)"

lemma setQueue_valid_bitmapQ_except[wp]:
  "\<lbrace> valid_bitmapQ_except d p \<rbrace>
  setQueue d p ts
  \<lbrace>\<lambda>_. valid_bitmapQ_except d p \<rbrace>"
  unfolding setQueue_def bitmapQ_defs
  by (wp, clarsimp simp: bitmapQ_def)

lemma ssa_sch_act[wp]:
  "\<lbrace>sch_act_wf sa\<rbrace> setSchedulerAction sa
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (simp add: setSchedulerAction_def | wp)+

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

lemma rescheduleRequired_sch_act'[wp]:
  "\<lbrace>\<top>\<rbrace>
   rescheduleRequired
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wpsimp simp: rescheduleRequired_def wp: getSchedulable_wp)

lemma sts_weak_sch_act_wf[wp]:
  "setThreadState st t \<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding setThreadState_def scheduleTCB_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift hoare_vcg_all_lift
                    hoare_pre_cont[where f="getSchedulable x" and P="\<lambda>rv _. rv" for x]
                    hoare_pre_cont[where f="getSchedulable x" and P="\<lambda>rv _. \<not>rv" for x]
              simp: weak_sch_act_wf_def)
  done

lemma threadSet_schedulable':
  "\<lbrace>\<lambda>s. runnable' st \<and> active_sc_tcb_at' t s \<and> (Not \<circ> tcbInReleaseQueue |< tcbs_of' s) t\<rbrace>
   threadSet (tcbState_update (\<lambda>_. st)) t
   \<lbrace>\<lambda>_. schedulable' t\<rbrace>"
  unfolding schedulable'_def threadSet_def
  apply (rule bind_wp[OF _ getObject_tcb_sp])
  apply (wpsimp wp: setObject_tcb_wp)
  apply (fastforce simp: opt_pred_def opt_map_def obj_at'_def active_sc_tcb_at'_def
                  split: option.splits)
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

lemma tcbSchedNext_update_pred_tcb_at'[wp]:
  "threadSet (tcbSchedNext_update f) t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+

lemma tcbSchedPrev_update_pred_tcb_at'[wp]:
  "threadSet (tcbSchedPrev_update f) t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+

lemma tcbSchedEnqueue_pred_tcb_at'[wp]:
  "tcbSchedEnqueue t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def tcbQueuePrepend_def when_def unless_def)
  apply (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+
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

crunch scheduleTCB
  for sch_act_simple[wp]: sch_act_simple
  (wp: crunch_wps hoare_vcg_if_lift2)

lemma sts_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  by (wpsimp simp: sch_act_simple_def)

context TcbAcc_R begin

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

end (* TcbAcc_R *)

lemma threadGet_const:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> obj_at' (P \<circ> f) t s\<rbrace> threadGet f t \<lbrace>\<lambda>rv s. P (rv)\<rbrace>"
  apply (simp add: threadGet_getObject)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma (in TcbAcc_R) addToBitmap_bitmapQ:
  "\<lbrace> \<top> \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. bitmapQ d p \<rbrace>"
  unfolding addToBitmap_def
             modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
             getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def
  by (wpsimp simp: bitmap_fun_defs bitmapQ_def prioToL1Index_bit_set prioL2Index_bit_set
             simp_del: bit_exp_iff)

lemma valid_bitmapQ_exceptE:
  "\<lbrakk> valid_bitmapQ_except d' p' s ; d \<noteq> d' \<or> p \<noteq> p' \<rbrakk>
   \<Longrightarrow> bitmapQ d p s = (\<not> tcbQueueEmpty (ksReadyQueues s (d, p)))"
  by (fastforce simp: valid_bitmapQ_except_def)

context TcbAcc_R begin

lemma invertL1Index_eq_cancel:
  "\<lbrakk> i < l2BitmapSize ; j < l2BitmapSize \<rbrakk>
   \<Longrightarrow> (invertL1Index i = invertL1Index j) = (i = j)"
   by (rule iffI, simp_all add: invertL1Index_eq_cancelD)

lemma addToBitmap_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmap_fun_defs bitmapQ_defs
  supply bit_exp_iff[simp del]
  apply wp
  apply clarsimp
  apply (fastforce simp: invertL1Index_eq_cancel prioToL1Index_bit_set)
  done

end (* TcbAcc_R *)

lemma (in TcbAcc_R_2) addToBitmap_valid_bitmapQ:
  "\<lbrace>valid_bitmapQ_except d p and bitmapQ_no_L2_orphans
    and (\<lambda>s. \<not> tcbQueueEmpty (ksReadyQueues s (d,p)))\<rbrace>
   addToBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q'="\<lambda>_ s. ?pre s \<and> bitmapQ d p s" in hoare_strengthen_post)
   apply (wpsimp wp: addToBitmap_valid_bitmapQ_except addToBitmap_bitmapQ)
  apply (fastforce elim: valid_bitmap_valid_bitmapQ_exceptE)
  done

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

crunch orderedInsert, tcbQueueRemove, tcbSchedEnqueue, tcbSchedAppend, tcbSchedDequeue
  for tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  (wp: threadSet_field_opt_pred crunch_wps)

crunch tcbSchedEnqueue
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

lemma tcbSchedPrev_update_tcbInReleaseQueues[wp]:
  "threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)\<rbrace>"
  by (wpsimp wp: threadSet_field_opt_pred)

lemma tcbSchedNext_update_tcbInReleaseQueue[wp]:
  "threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)\<rbrace>"
  by (wpsimp wp: threadSet_field_opt_pred)

lemma rescheduleRequired_valid_bitmapQ_sch_act_simple:
  "\<lbrace> valid_bitmapQ and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  including classic_wp_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac Q'="\<lambda>rv s. valid_bitmapQ s \<and> (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)"
               in bind_wp)
   apply wpsimp
   apply (case_tac rv; simp)
  apply (wp, fastforce)
  done

lemma rescheduleRequired_bitmapQ_no_L1_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L1_orphans and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  including classic_wp_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac Q'="\<lambda>rv s. bitmapQ_no_L1_orphans s \<and> (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)"
               in bind_wp)
   apply wpsimp
   apply (case_tac rv; simp)
  apply (wp, fastforce)
  done

lemma rescheduleRequired_bitmapQ_no_L2_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L2_orphans and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  including classic_wp_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac Q'="\<lambda>rv s. bitmapQ_no_L2_orphans s \<and> (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)"
               in bind_wp)
   apply wpsimp
   apply (case_tac rv; simp)
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
  "\<lbrace>bitmapQ_no_L2_orphans and sch_act_simple\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans\<rbrace>"
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
  "\<lbrace>bitmapQ_no_L1_orphans and sch_act_simple\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans\<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  by (wpsimp wp: threadSet_valid_bitmapQ_no_L1_orphans
                 scheduleTCB_bitmapQ_no_L1_orphans_sch_act_simple)

crunch addToBitmap
  for ksPSpace[wp]: "\<lambda>s. P (ksPSpace s ptr = opt)"

crunch setQueue
  for valid_tcb'[wp]: "\<lambda>s. P (valid_tcb' tcb s)"

lemma tcbSchedNext_update_valid_tcbs'[wp]:
  "\<lbrace>valid_tcbs' and none_top tcb_at' ptrOpt\<rbrace>
   threadSet (tcbSchedNext_update (\<lambda>_. ptrOpt)) tcbPtr
   \<lbrace>\<lambda>_. valid_tcbs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_tcbs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)
  done

lemma tcbSchedPrev_update_valid_tcbs'[wp]:
  "\<lbrace>valid_tcbs' and none_top tcb_at' ptrOpt\<rbrace>
   threadSet (tcbSchedPrev_update (\<lambda>_. ptrOpt)) tcbPtr
   \<lbrace>\<lambda>_. valid_tcbs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_tcbs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)
  done

lemma tcbQueued_update_valid_tcbs'[wp]:
  "threadSet (tcbQueued_update bool) tcbPtr \<lbrace>valid_tcbs'\<rbrace>"
  by (wpsimp wp: threadSet_valid_tcbs')

lemma tcbQueuePrepend_valid_tcbs'[wp]:
  "\<lbrace>\<lambda>s. valid_tcbs' s \<and> tcb_at' tcbPtr s\<rbrace>
   tcbQueuePrepend queue tcbPtr
   \<lbrace>\<lambda>_. valid_tcbs'\<rbrace>"
  unfolding tcbQueuePrepend_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (clarsimp simp: list_queue_relation_def tcbQueueEmpty_def)
  apply (rename_tac ts)
  apply (prop_tac "ts \<noteq> []", fastforce)
  apply (fastforce dest: heap_path_head)
  done

lemma tcbSchedEnqueue_valid_tcbs'[wp]:
  "tcbSchedEnqueue thread \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def setQueue_def bitmap_fun_defs)
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' threadGet_wp hoare_vcg_all_lift)
  apply (clarsimp simp: obj_at'_def)
  done

lemma setSchedulerAction_valid_tcbs'[wp]:
  "setSchedulerAction sa \<lbrace>valid_tcbs'\<rbrace>"
  unfolding valid_tcbs'_def
  by (wpsimp wp: hoare_vcg_all_lift update_valid_tcb')

lemma rescheduleRequired_valid_tcbs'[wp]:
  "rescheduleRequired \<lbrace>valid_tcbs'\<rbrace>"
  apply (clarsimp simp: rescheduleRequired_def)
  apply (rule bind_wp_fwd_skip,
         wpsimp wp: tcbSchedEnqueue_valid_tcbs' update_valid_tcb' getSchedulable_wp)+
  apply (wpsimp wp: update_valid_tcb')
  done

crunch scheduleTCB
  for valid_tcbs'[wp]: valid_tcbs'
  (wp: crunch_wps simp: crunch_simps)

lemma setThreadState_valid_tcbs'[wp]:
  "setThreadState st t \<lbrace>valid_tcbs'\<rbrace>"
  apply (simp add: setThreadState_def pred_conj_def)
  apply (wpsimp wp: threadSet_valid_tcbs')
  apply (clarsimp simp: valid_tcb'_tcbState_update)
  done

crunch rescheduleRequired
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  (simp_del: comp_apply)

crunch setThreadState, setBoundNotification
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (wp: crunch_wps sym_heap_sched_pointers_lift threadSet_field_inv threadSet_field_opt_pred
   simp: crunch_simps)

lemma setSchedulerAction_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setSchedulerAction act \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wp, simp)

lemma threadSet_tcbState_st_tcb_at':
  "\<lbrace>\<lambda>s. P st \<rbrace> threadSet (tcbState_update (\<lambda>_. st)) t \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: threadSet_def pred_tcb_at'_def)
  apply (wpsimp wp: setObject_tcb_strongest)
  done

lemma isRunnable_const:
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> isRunnable t \<lbrace>\<lambda>runnable _. runnable \<rbrace>"
  by (rule isRunnable_wp)

lemma (in TcbAcc_R) load_word_corres:
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
     apply wpsimp+
  done

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
   apply (rule hoare_TrueI)+
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

lemma (in TcbAcc_R_2) lookupIPCBuffer_corres:
  "corres (=) (tcb_at t and invs) (valid_objs' and no_0_obj')
     (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  using lookupIPCBuffer_corres'
  by (rule corres_guard_imp, auto simp: invs'_def)

crunch scheduleTCB, possibleSwitchTo
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

context TcbAcc_R_2 begin

crunch rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for ct'[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: crunch_simps)

crunch rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for typ_at'[wp]:  "\<lambda>s. P (typ_at' T p s)"

end (* TcbAcc_R_2 *)

lemma ct_in_state'_decomp:
  assumes x: "\<lbrace>\<lambda>s. t = (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv s. t = (ksCurThread s)\<rbrace>"
  assumes y: "\<lbrace>Pre\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' Prop t\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Pre s \<and> t = (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv. ct_in_state' Prop\<rbrace>"
  apply (rule hoare_post_imp[where Q'="\<lambda>rv s. t = ksCurThread s \<and> st_tcb_at' Prop t s"])
   apply (clarsimp simp add: ct_in_state'_def)
  apply (rule hoare_weaken_pre)
   apply (wp x y)
  apply simp
  done

lemma (in TcbAcc_R_2) ct_in_state'_set:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> P st \<and> t = ksCurThread s\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule ct_in_state'_decomp[where t=t])
    apply (wp setThreadState_ct')
   apply (wp setThreadState_st_tcb)
  apply clarsimp
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
  apply (simp add: tcbSchedDequeue_def tcbQueueRemove_def)
  by (wpsimp wp: hoare_drop_imps simp: o_def cong: if_cong)

lemma tcbSchedDequeue_pred_tcb_at'[wp]:
  "tcbSchedDequeue t \<lbrace>\<lambda>s. Q (pred_tcb_at' proj P t' s)\<rbrace>"
  by (rule_tac P=Q in P_bool_lift;
      simp add: tcbSchedDequeue_def tcbQueueRemove_def,
      (wp threadSet_pred_tcb_no_state getTCB_wp threadGet_wp hoare_vcg_all_lift hoare_drop_imps
       | clarsimp simp: tcb_to_itcb'_def)+)

crunch tcbQueueRemove
  for pred_tcb_at'[wp]: "\<lambda>s. P' (pred_tcb_at' proj P t' s)"
  (wp: threadSet_pred_tcb_no_state crunch_wps simp: tcb_to_itcb'_def)

lemma tcbReleaseRemove_pred_tcb_at'[wp]:
  "tcbReleaseRemove t \<lbrace>\<lambda>s. P' (pred_tcb_at' proj P t' s)\<rbrace>"
  apply (rule_tac P=P' in P_bool_lift)
   unfolding tcbReleaseRemove_def
   apply (wp threadSet_pred_tcb_no_state inReleaseQueue_wp
          | clarsimp simp: tcb_to_itcb'_def setReleaseQueue_def
                           setReprogramTimer_def getReleaseQueue_def
          | fastforce simp: obj_at'_def)+
  done

crunch (in TcbAcc_R) tcbReleaseRemove
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps)

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

crunch scheduleTCB, setThreadState
  for cte_wp_at'[wp]: "\<lambda>s. Q (cte_wp_at' P p s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas setThreadState_cap_to'[wp]
  = ex_cte_cap_to'_pres [OF setThreadState_cte_wp_at' setThreadState_ksInterruptState]

crunch setThreadState, setBoundNotification
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and cte_wp_at'[wp]: "\<lambda>s. Q (cte_wp_at' P p s)"
  (wp: hoare_when_weak_wp crunch_wps)

crunch rescheduleRequired
 for refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  (wp: threadSet_state_refs_of'[where g'=id] crunch_wps simp: tcb_bound_refs'_def)

crunch scheduleTCB
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps simp: crunch_simps)

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

lemma setThreadState_state_refs_of':
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' st \<union> tcb_non_st_state_refs_of' s t))\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setThreadState_def)
  apply (wpsimp wp: threadSet_state_refs_of')
      apply simp
     apply (force simp: tcb_bound_refs'_def)+
  apply (subst state_refs_of'_helper2)
  by fastforce

lemma setBoundNotification_list_refs_of_replies'[wp]:
  "setBoundNotification ntfn t \<lbrace>\<lambda>s. P (list_refs_of_replies' s)\<rbrace>"
  unfolding setBoundNotification_def
  by wpsimp

lemma update_tcb_cte_cases:
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbInReleaseQueue_update f tcb) = getF tcb"
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbQueued_update f tcb) = getF tcb"
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbSchedNext_update f tcb) = getF tcb"
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbSchedPrev_update f tcb) = getF tcb"
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbYieldTo_update f tcb) = getF tcb"
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbSchedContext_update f tcb) = getF tcb"
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbBoundNotification_update f tcb) = getF tcb"
  "\<And>f. (getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbPriority_update f tcb) = getF tcb"
  unfolding tcb_cte_cases_def
  by (case_tac tcb; fastforce simp: gen_objBits_simps tcb_cte_cases_def tcb_cte_cases_neqs)+

lemma tcbSchedNext_update_ctes_of[wp]:
  "threadSet (tcbSchedNext_update f) tptr \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_ofT simp: update_tcb_cte_cases)

lemma tcbSchedPrev_update_ctes_of[wp]:
  "threadSet (tcbSchedPrev_update f) tptr \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_ofT simp: update_tcb_cte_cases)

defs tcbQueueRemove_asrt_def:
  "tcbQueueRemove_asrt \<equiv>
     \<lambda>q tcbPtr s. \<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                       \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> (t \<noteq> tcbPtr \<longrightarrow> sched_flag_set s t))
                       \<and> tcbPtr \<in> set ts"

declare tcbQueueRemove_asrt_def[simp]

crunch addToBitmap
  for if_unsafe_then_cap'[wp]: if_unsafe_then_cap'

lemma tcbQueuePrepend_if_unsafe_then_cap'[wp]:
  "tcbQueuePrepend queue tcbPtr \<lbrace>if_unsafe_then_cap'\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps threadSet_ifunsafe'T
           simp: update_tcb_cte_cases)

lemma tcbSchedEnqueue_if_unsafe_then_cap'[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>if_unsafe_then_cap'\<rbrace>"
  unfolding tcbSchedEnqueue_def setQueue_def
  by (wpsimp wp: threadSet_ifunsafe'T simp: update_tcb_cte_cases)

lemma setThreadState_if_unsafe_then_cap'[wp]:
  "setThreadState st p \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (clarsimp simp: setThreadState_def scheduleTCB_def rescheduleRequired_def when_def)
  apply (rule bind_wp_fwd_skip)
   apply (rule threadSet_ifunsafe'T)
   apply (clarsimp simp: tcb_cte_cases_def tcb_cte_cases_neqs)
  apply (wpsimp wp: getSchedulable_wp)
  done

crunch setBoundNotification
  for ifunsafe'[wp]: "if_unsafe_then_cap'"

lemma st_tcb_ex_cap'':
  "\<lbrakk> st_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>st. P st \<Longrightarrow> st \<noteq> Inactive \<and> \<not> idle' st \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def live'_def
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

lemma bound_tcb_ex_cap'':
  "\<lbrakk> bound_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>ntfn. P ntfn \<Longrightarrow> bound ntfn \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def live'_def
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

crunch setThreadState, setBoundNotification
  for arch' [wp]: "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps simp: crunch_simps)

crunch setThreadState
  for it' [wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: getObject_tcb_inv crunch_wps
   simp: updateObject_default_def unless_def crunch_simps)

crunch setThreadState, setBoundNotification
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps simp: crunch_simps)

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

crunch setThreadState, setBoundNotification
  for irq_states' [wp]: valid_irq_states'
  (wp: crunch_wps simp: crunch_simps)

crunch setThreadState, setBoundNotification
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps simp: crunch_simps)

lemma (in TcbAcc_R_2) setThreadState_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setThreadState F t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift; wp)
  done

lemma (in TcbAcc_R_2) setBoundNotification_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift; wp)
  done

lemma setSchedulerAction_direct[wp]:
  "\<lbrace>\<top>\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_ s. ksSchedulerAction s = sa\<rbrace>"
  by (wpsimp simp: setSchedulerAction_def)

lemma rescheduleRequired_sa_cnt[wp]:
  "\<lbrace>\<lambda>s. True \<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread \<rbrace>"
  unfolding rescheduleRequired_def setSchedulerAction_def
  by (wpsimp wp: hoare_vcg_if_lift2)

crunch rescheduleRequired, setThreadState, setBoundNotification
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps simp: crunch_simps)

crunch rescheduleRequired, setBoundNotification, setThreadState
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: crunch_simps)

lemma sts_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp untyped_ranges_zero_lift)
  done

lemma pair_inject:
  "{a,b} = {c,d} \<and> a \<noteq> d \<and> b \<noteq> c \<Longrightarrow> a = c \<and> b = d"
  by blast

lemma tcb_bound_refs'_helper:
  "tcb_bound_refs' tcb
   = {r. (r \<in> tcb_st_refs_of' st \<or> r \<in> tcb_bound_refs' tcb) \<and> snd r = TCBBound}
     \<union> {r. (r \<in> tcb_st_refs_of' st \<or> r \<in> tcb_bound_refs' tcb) \<and> snd r = TCBSchedContext}
     \<union> {r. (r \<in> tcb_st_refs_of' st \<or> r \<in> tcb_bound_refs' tcb) \<and> snd r = TCBYieldTo}"
  apply (clarsimp simp: tcb_bound_refs'_def get_refs_def tcb_st_refs_of'_def
                 split: option.splits thread_state.splits reftype.splits)
  apply (intro conjI impI allI; fastforce?)
  done

lemma removeFromBitmap_bitmapQ:
  "\<lbrace>\<top>\<rbrace> removeFromBitmap d p \<lbrace>\<lambda>_ s. \<not> bitmapQ d p s \<rbrace>"
  unfolding bitmapQ_defs bitmap_fun_defs
  by (wpsimp simp: bitmap_fun_defs)

lemma setQueue_nonempty_valid_bitmapQ':
  "\<lbrace>\<lambda>s. valid_bitmapQ s \<and> \<not> tcbQueueEmpty (ksReadyQueues s (d, p))\<rbrace>
   setQueue d p queue
   \<lbrace>\<lambda>_ s. \<not> tcbQueueEmpty queue \<longrightarrow> valid_bitmapQ s\<rbrace>"
  apply (wpsimp simp: setQueue_def)
  apply (fastforce simp: valid_bitmapQ_def bitmapQ_def)
  done

lemma threadSet_valid_bitmapQ_except[wp]:
  "threadSet f tcbPtr \<lbrace>valid_bitmapQ_except d p\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_bitmapQ_except_def bitmapQ_def)
  done

lemma threadSet_bitmapQ:
  "threadSet F t \<lbrace>bitmapQ domain priority\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  by (clarsimp simp: bitmapQ_def)

crunch tcbQueueRemove, tcbQueuePrepend, tcbQueueAppend
  for valid_bitmapQ_except[wp]: "valid_bitmapQ_except d p"
  and valid_bitmapQ[wp]: valid_bitmapQ
  and bitmapQ[wp]: "bitmapQ tdom prio"
  (wp: crunch_wps)

crunch tcbReleaseRemove
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReadyQueuesL1Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksReadyQueuesL2Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: crunch_wps)

lemma tcbQueued_imp_queue_nonempty:
  "\<lbrakk>list_queue_relation ts (ksReadyQueues s (tcbDomain tcb, tcbPriority tcb)) nexts prevs;
    \<forall>t. t \<in> set ts \<longleftrightarrow> (inQ (tcbDomain tcb) (tcbPriority tcb) |< tcbs_of' s) t;
    ko_at' tcb tcbPtr s; tcbQueued tcb\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (tcbDomain tcb, tcbPriority tcb))"
  apply (clarsimp simp: list_queue_relation_def tcbQueueEmpty_def)
  apply (drule_tac x=tcbPtr in spec)
  apply (fastforce dest: heap_path_head simp: inQ_def opt_map_def opt_pred_def obj_at'_def)
  done

lemma setQueue_valid_bitmapQ': (* enqueue only *)
  "\<lbrace>valid_bitmapQ_except d p and bitmapQ d p and K (\<not> tcbQueueEmpty q)\<rbrace>
   setQueue d p q
   \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  unfolding setQueue_def bitmapQ_defs
  by (wpsimp simp: bitmapQ_def)

context TcbAcc_R_2 begin

lemma removeFromBitmap_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmapQ_except d p and bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans
    and (\<lambda>s. tcbQueueEmpty (ksReadyQueues s (d,p)))\<rbrace>
   removeFromBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q'="\<lambda>_ s. ?pre s \<and> \<not> bitmapQ d p s" in hoare_strengthen_post)
   apply (wpsimp wp: removeFromBitmap_valid_bitmapQ_except removeFromBitmap_bitmapQ)
  apply (fastforce elim: valid_bitmap_valid_bitmapQ_exceptE)
  done

crunch tcbSchedDequeue
  for bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans
  (wp: crunch_wps simp: crunch_simps)

lemma tcbSchedDequeue_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmaps\<rbrace> tcbSchedDequeue tcbPtr \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  unfolding tcbSchedDequeue_def tcbQueueRemove_def
  apply (wpsimp wp: setQueue_nonempty_valid_bitmapQ' hoare_vcg_conj_lift
                    hoare_vcg_if_lift2 hoare_vcg_const_imp_lift threadGet_wp
         | wp (once) hoare_drop_imps)+
  by (fastforce dest!: tcbQueued_imp_queue_nonempty
                 simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def)

lemma tcbSchedDequeue_valid_bitmaps[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  by (wpsimp simp: valid_bitmaps_def)

lemma tcbSchedEnqueue_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmaps\<rbrace> tcbSchedEnqueue tcbPtr \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  supply if_split[split del]
  unfolding tcbSchedEnqueue_def
  apply (wpsimp simp: tcbQueuePrepend_def
                  wp: stateAssert_inv setQueue_valid_bitmapQ' addToBitmap_valid_bitmapQ_except
                      addToBitmap_bitmapQ threadGet_wp)
  apply (fastforce simp: valid_bitmaps_def valid_bitmapQ_def tcbQueueEmpty_def split: if_splits)
  done

crunch tcbSchedEnqueue, tcbSchedAppend
  for bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans

lemma tcbSchedEnqueue_valid_bitmaps[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  unfolding valid_bitmaps_def
  apply wpsimp
  apply (clarsimp simp: valid_bitmaps_def)
  done

crunch rescheduleRequired, threadSet, setThreadState
  for valid_bitmaps[wp]: valid_bitmaps
  (rule: valid_bitmaps_lift simp: crunch_simps wp: crunch_wps)

end (* TcbAcc_R_2 *)

lemma tcbQueueRemove_valid_sched_pointers:
  "\<lbrace>valid_sched_pointers_except tcbPtr\<rbrace>
   tcbQueueRemove q tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (clarsimp simp: tcbQueueRemove_def valid_sched_pointers_def)
  apply (rule bind_wp[OF _ stateAssert_sp])+
  apply (rule bind_wp[OF _ get_tcb_sp'])
  apply (rule hoare_if)
   \<comment>\<open>q is the singleton containing tcbPtr\<close>
   apply wpsimp
   apply (clarsimp simp: list_queue_relation_def)
   apply (rename_tac ptr ts)
   apply (intro conjI impI allI)
    apply (drule_tac x=ptr in spec)
    apply (force simp: prev_queue_head_def queue_end_valid_def opt_map_def)
   apply (drule_tac x=ptr in spec)
   apply (force dest: heap_ls_last_None simp: queue_end_valid_def opt_map_def)
  apply (rule hoare_if)
   \<comment>\<open>tcbPtr is the head of q\<close>
   apply (wpsimp wp: threadSet_wp getTCB_wp)
   apply (clarsimp simp: list_queue_relation_def)
   apply (drule obj_at'_prop)+
   subgoal
     by (fastforce simp: prev_queue_head_def queue_end_valid_def opt_pred_def opt_map_def)
  apply (rule hoare_if)
   \<comment>\<open>tcbPtr is the end of q\<close>
   apply (wpsimp wp: threadSet_wp getTCB_wp)
   apply (drule obj_at'_prop)+
   subgoal
     by (fastforce dest: heap_ls_last_None
                   simp: list_queue_relation_def queue_end_valid_def opt_pred_def opt_map_def)
  \<comment>\<open>tcbPtr occurs in the middle of q\<close>
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (frule (2) list_queue_relation_neighbour_in_set)
  by (auto simp: list_queue_relation_def obj_at'_def opt_pred_def opt_map_def
          split: if_splits option.splits)

lemma tcbSchedPrev_update_None_valid_sched_pointers[wp]:
  "threadSet (tcbSchedPrev_update (\<lambda>_. None)) tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: valid_sched_pointers_def obj_at'_def opt_map_def in_opt_pred
                  split: option.splits)
  done

lemma tcbSchedNext_update_None_valid_sched_pointers[wp]:
  "threadSet (tcbSchedNext_update (\<lambda>_. None)) tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: valid_sched_pointers_def obj_at'_def opt_map_def in_opt_pred
                  split: option.splits)
  done

lemma tcbSchedPrev_update_Some_valid_sched_pointers[wp]:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> sched_flag_set s tcbPtr\<rbrace>
   threadSet (tcbSchedPrev_update (\<lambda>_. Some ptr)) tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: valid_sched_pointers_def obj_at'_def opt_map_def in_opt_pred)
  done

lemma tcbSchedNext_update_Some_valid_sched_pointers[wp]:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> sched_flag_set s tcbPtr\<rbrace>
   threadSet (tcbSchedNext_update (\<lambda>_. Some ptr)) tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: valid_sched_pointers_def obj_at'_def opt_map_def in_opt_pred)
  done

lemma threadSet_sched_flag_set:
  "\<lbrakk>\<And>tcb. tcbInReleaseQueue (F tcb) = tcbInReleaseQueue tcb;
    \<And>tcb. tcbQueued (F tcb) = tcbQueued tcb; \<And>tcb. tcbState (F tcb) = tcbState tcb\<rbrakk>
   \<Longrightarrow> threadSet F t \<lbrace>\<lambda>s. P (sched_flag_set s tcbPtr)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: opt_pred_def opt_map_def obj_at'_def)
  done

lemma tcbSchedNext_update_sched_flag_set[wp]:
  "threadSet (tcbSchedNext_update f) t \<lbrace>\<lambda>s. P (sched_flag_set s tcbPtr)\<rbrace>"
  by (wpsimp wp: threadSet_sched_flag_set)

lemma tcbSchedPrev_update_sched_flag_set[wp]:
  "threadSet (tcbSchedPrev_update f) t \<lbrace>\<lambda>s. P (sched_flag_set s tcbPtr)\<rbrace>"
  by (wpsimp wp: threadSet_sched_flag_set)

lemma tcbQueuePrepend_valid_sched_pointers_except:
  "\<lbrace>valid_sched_pointers\<rbrace>
   tcbQueuePrepend q tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers_except tcbPtr\<rbrace>"
  unfolding tcbQueuePrepend_def
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  by (force dest!: bspec[where x="the (tcbQueueHead q)"] dest: heap_path_head
             simp: valid_sched_pointers_def list_queue_relation_def tcbQueueEmpty_def
                   opt_pred_def opt_map_def obj_at'_def queue_end_valid_def)

lemma tcbQueuePrepend_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> sched_flag_set s tcbPtr\<rbrace>
   tcbQueuePrepend q tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (rule_tac Q'="\<lambda>_ s. valid_sched_pointers_except tcbPtr s \<and> sched_flag_set s tcbPtr"
               in hoare_post_imp)
   apply (fastforce simp: valid_sched_pointers_def list_queue_relation_def)
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (wpsimp wp: tcbQueuePrepend_valid_sched_pointers_except)
  apply (clarsimp simp: tcbQueuePrepend_def bind_if_distribR split del: if_split)
  apply wpsimp
  done

lemma tcbQueueAppend_valid_sched_pointers_except:
  "\<lbrace>valid_sched_pointers\<rbrace>
   tcbQueueAppend q tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers_except tcbPtr\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  by (force dest!: bspec[where x="the (tcbQueueEnd q)"]
             simp: valid_sched_pointers_def list_queue_relation_def tcbQueueEmpty_def
                   opt_pred_def opt_map_def obj_at'_def queue_end_valid_def)

lemma tcbQueueAppend_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> sched_flag_set s tcbPtr\<rbrace>
   tcbQueueAppend q tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (rule_tac Q'="\<lambda>_ s. valid_sched_pointers_except tcbPtr s \<and> sched_flag_set s tcbPtr"
               in hoare_post_imp)
   apply (fastforce simp: valid_sched_pointers_def list_queue_relation_def)
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (wpsimp wp: tcbQueueAppend_valid_sched_pointers_except)
  apply (clarsimp simp: tcbQueueAppend_def split del: if_split)
  apply wpsimp
  done

lemma tcbQueueInsert_valid_sched_pointers_except:
  "\<lbrace>valid_sched_pointers\<rbrace>
   tcbQueueInsert tcbPtr afterPtr
   \<lbrace>\<lambda>_. valid_sched_pointers_except tcbPtr\<rbrace>"
  apply (clarsimp simp: tcbQueueInsert_def)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (drule obj_at'_prop)+
  apply clarsimp
  apply (rename_tac beforePtr tcb tcb' tcb'')
  apply (prop_tac "tcbPtr \<noteq> afterPtr", fastforce)
  apply (clarsimp simp: valid_sched_pointers_def list_queue_relation_def)
  apply (prop_tac "beforePtr \<in> set ts")
   apply (force dest!: heap_ls_prev_cases intro: sym_heapD2 simp: prev_queue_head_def opt_map_def)
  apply (clarsimp simp: opt_pred_def opt_map_def split: option.splits)
  done

lemma tcbQueueInsert_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> sched_flag_set s tcbPtr\<rbrace>
   tcbQueueInsert tcbPtr afterPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (rule_tac Q'="\<lambda>_ s. valid_sched_pointers_except tcbPtr s \<and> sched_flag_set s tcbPtr"
               in hoare_post_imp)
   apply (fastforce simp: valid_sched_pointers_def list_queue_relation_def)
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (wpsimp wp: tcbQueueInsert_valid_sched_pointers_except)
  apply (clarsimp simp: tcbQueueInsert_def)
  apply (wpsimp wp: getTCB_wp)
  done

lemma orderedInsert_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> sched_flag_set s t\<rbrace>
   orderedInsert t q f R
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding orderedInsert_def
  by (wpsimp wp: tcbQueuePrepend_valid_sched_pointers tcbQueueAppend_valid_sched_pointers
                 tcbQueueInsert_valid_sched_pointers hoare_drop_imps)

crunch addToBitmap
  for valid_sched_pointers_except_set[wp]: "valid_sched_pointers_except_set S"
  and sched_flag_set[wp]: "\<lambda>s. sched_flag_set s t"
  and tcbStates_of'[wp]: "\<lambda>s. P (tcbStates_of' s)"

lemma threadSet_valid_sched_pointers_except_inv[wp]:
  "threadSet F tcbPtr \<lbrace>valid_sched_pointers_except tcbPtr\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_sched_pointers_except_def opt_pred_def)
  done

lemma tcbQueued_update_True_sched_flag_set[wp]:
  "\<lbrace>\<top>\<rbrace> threadSet (tcbQueued_update (\<lambda>_. True)) tcbPtr \<lbrace>\<lambda>_ s. sched_flag_set s tcbPtr\<rbrace>"
  by (wpsimp wp: threadSet_wp)

lemma tcbInReleaseQueue_update_True_sched_flag_set[wp]:
  "\<lbrace>\<top>\<rbrace> threadSet (tcbInReleaseQueue_update (\<lambda>_. True)) tcbPtr \<lbrace>\<lambda>_ s. sched_flag_set s tcbPtr\<rbrace>"
  by (wpsimp wp: threadSet_wp)

lemma tcbQueued_True_valid_sched_pointers[wp]:
  "\<lbrace>valid_sched_pointers_except tcbPtr\<rbrace>
   threadSet (tcbQueued_update \<top>) tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_sched_pointers_def opt_pred_def)
  done

lemma tcbSchedEnqueue_valid_sched_pointers[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding tcbSchedEnqueue_def
  by (wpsimp wp: tcbQueuePrepend_valid_sched_pointers_except)

lemma tcbSchedAppend_valid_sched_pointers[wp]:
  "tcbSchedAppend tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding tcbSchedAppend_def
  by (wpsimp wp: tcbQueueAppend_valid_sched_pointers_except)

lemma monadic_rewrite_threadSet_same:
  "monadic_rewrite F E (obj_at' (\<lambda>tcb :: tcb. f tcb = tcb) tcbPtr)
     (threadSet f tcbPtr) (return ())"
  apply (clarsimp simp: threadSet_def)
  apply (rule monadic_rewrite_guard_imp)
   apply monadic_rewrite_symb_exec_l
    apply (rule_tac P="obj_at' (\<lambda>tcb' :: tcb. f tcb' = tcb' \<and> tcb' = tcb) tcbPtr"
                 in monadic_rewrite_pre_imp_eq)
    apply (subst setObject_modify; (fastforce simp: gen_objBits_simps)?)
    apply (clarsimp simp: modify_def return_def get_def bind_def put_def obj_at'_def)
    apply (prop_tac "ksPSpace (ksPSpace_update (\<lambda>ps. ps(tcbPtr \<mapsto> KOTCB tcb)) s) = ksPSpace s")
     apply fastforce
    apply (wpsimp wp: getTCB_wp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbQueued_False_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> \<not> is_sched_linked tcbPtr s\<rbrace>
   threadSet (tcbQueued_update (\<lambda>_. False)) tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_sched_pointers_def obj_at'_def opt_map_red opt_pred_def)
  done

lemma tcbQueueRemove_tcbSchedPrev_tcbSchedNext_None[wp]:
  "\<lbrace>\<top>\<rbrace>
   tcbQueueRemove q t
   \<lbrace>\<lambda>_ s. obj_at' (\<lambda>tcb. tcbSchedPrev tcb = None \<and> tcbSchedNext tcb = None) t s\<rbrace>"
  apply (clarsimp simp: tcbQueueRemove_def)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  by (force dest!: heap_ls_last_None
             simp: list_queue_relation_def prev_queue_head_def queue_end_valid_def
                   obj_at'_def opt_map_def ps_clear_def gen_objBits_simps)

lemma tcbQueueRemove_not_sched_linked[wp]:
  "\<lbrace>\<top>\<rbrace> tcbQueueRemove q t \<lbrace>\<lambda>_ s. \<not> is_sched_linked t s\<rbrace>"
  apply (rule hoare_strengthen_post[OF tcbQueueRemove_tcbSchedPrev_tcbSchedNext_None])
  apply (clarsimp simp: obj_at'_def opt_map_def)
  done

lemma tcbSchedDequeue_valid_sched_pointers[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp wp: tcbQueued_False_valid_sched_pointers
                    tcbQueueRemove_valid_sched_pointers threadGet_wp)
  apply (clarsimp simp: valid_sched_pointers_def)
  done

lemma tcbQueueRemove_sym_heap_sched_pointers[wp]:
  "\<lbrace>\<top>\<rbrace> tcbQueueRemove q tcbPtr \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  supply heap_path_append[simp del]
  apply (clarsimp simp: tcbQueueRemove_def)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (rename_tac ts tcb)

  \<comment> \<open>tcbPtr is the head of q, which is not a singleton\<close>
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: list_queue_relation_def Let_def)
   apply (prop_tac "tcbSchedNext tcb \<noteq> Some tcbPtr")
    apply (fastforce dest: heap_ls_no_loops[where p=tcbPtr] simp: opt_map_def obj_at'_def)
   apply (fastforce intro: sym_heap_remove_only'
                     simp: prev_queue_head_def opt_map_red opt_map_upd_triv obj_at'_def)

  \<comment> \<open>tcbPtr is the end of q, which is not a singleton\<close>
  apply (intro impI)
  apply (rule conjI)
   apply clarsimp
   apply (prop_tac "tcbSchedPrev tcb \<noteq> Some tcbPtr")
    apply (fastforce dest!: heap_ls_prev_no_loops[where p=tcbPtr]
                      simp: list_queue_relation_def opt_map_def obj_at'_def)
   apply (subst fun_upd_swap, fastforce)
   apply (fastforce intro: sym_heap_remove_only simp: opt_map_red opt_map_upd_triv obj_at'_def)

  \<comment> \<open>tcbPtr is in the middle of q\<close>
  apply (intro conjI impI allI)
  apply (frule (2) list_queue_relation_neighbour_in_set[where p=tcbPtr])
  apply (frule split_list)
  apply clarsimp
  apply (rename_tac xs ys)
  apply (prop_tac "xs \<noteq> [] \<and> ys \<noteq> []")
   apply (fastforce simp: list_queue_relation_def queue_end_valid_def)
  apply (clarsimp simp: list_queue_relation_def)
  apply (frule (3) ptr_in_middle_prev_next)
  apply (frule heap_ls_distinct)
  apply (rename_tac afterPtr beforePtr xs ys)
  apply (frule_tac before=beforePtr and middle=tcbPtr and after=afterPtr
                in sym_heap_remove_middle_from_chain)
      apply (fastforce dest: last_in_set simp: opt_map_def obj_at'_def)
     apply (fastforce dest: hd_in_set simp: opt_map_def obj_at'_def)
    apply (rule_tac hp="tcbSchedNexts_of s" in sym_heapD2)
     apply fastforce
    apply (fastforce simp: opt_map_def obj_at'_def)
   apply (fastforce simp: opt_map_def obj_at'_def)
  by (fastforce simp: fun_upd_swap opt_map_red opt_map_upd_triv obj_at'_def split: if_splits)

lemma tcbQueuePrepend_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. sym_heap_sched_pointers s \<and> \<not> is_sched_linked tcbPtr s\<rbrace>
   tcbQueuePrepend q tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: tcbQueuePrepend_def bind_if_distribR)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule hoare_if)
   \<comment> \<open>q was originally empty\<close>
   apply (wpsimp wp: threadSet_wp)
  \<comment> \<open>q was not originally empty\<close>
  apply (wpsimp wp: threadSet_wp)
  apply (drule obj_at'_prop)+
  apply (clarsimp simp: list_queue_relation_def prev_queue_head_def tcbQueueEmpty_def)
  apply (clarsimp split: if_splits)
   apply (fastforce dest: sym_heap_connect)
  apply (drule_tac a=tcbPtr and b="the (tcbQueueHead q)" in sym_heap_connect)
    apply assumption
   apply (clarsimp simp: list_queue_relation_def prev_queue_head_def tcbQueueEmpty_def)
  apply (fastforce simp: fun_upd_swap opt_map_red opt_map_upd_triv)
  done

lemma tcbQueueAppend_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. sym_heap_sched_pointers s \<and> \<not> is_sched_linked tcbPtr s\<rbrace>
   tcbQueueAppend q tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  supply if_split[split del]
  apply (clarsimp simp: tcbQueueAppend_def bind_if_distribR)
  apply (rule bind_wp[OF _ stateAssert_sp])
  apply (rule hoare_if)
   \<comment> \<open>q was originally empty\<close>
   apply (wpsimp wp: threadSet_wp)
  \<comment> \<open>q was not originally empty\<close>
  apply (wpsimp wp: threadSet_wp)
  apply (drule obj_at'_prop)+
  apply (clarsimp simp: tcbQueueEmpty_def list_queue_relation_def queue_end_valid_def obj_at'_def
                 split: if_splits)
   apply (drule_tac a="last ts" and b=tcbPtr in sym_heap_connect)
     apply (fastforce dest: heap_ls_last_None)
    apply fastforce
   apply fastforce
  apply (drule_tac a="last ts" and b=tcbPtr in sym_heap_connect)
    apply (fastforce dest: heap_ls_last_None)
   apply fastforce
  apply (simp add: opt_map_red tcbQueueEmpty_def)
  apply (subst fun_upd_swap, simp)
  apply (fastforce simp: opt_map_red opt_map_upd_triv)
  done

lemma tcbQueueInsert_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. \<not> is_sched_linked tcbPtr s\<rbrace>
   tcbQueueInsert tcbPtr afterPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  apply (clarsimp simp: tcbQueueInsert_def)
  \<comment> \<open>forwards step in order to name beforePtr below\<close>
  apply (rule bind_wp[OF _ stateAssert_sp])+
  apply (rule bind_wp[OF _ getObject_tcb_sp])
  apply (rule bind_wp[OF _ assert_sp])
  apply (rule hoare_ex_pre_conj[simplified conj_commute], rename_tac beforePtr)
  apply (rule bind_wp[OF _ assert_sp])
  apply (wpsimp wp: threadSet_wp)
  apply normalise_obj_at'
  apply (prop_tac "tcbPtr \<noteq> afterPtr")
   apply (clarsimp simp: list_queue_relation_def opt_map_red obj_at'_def)
  apply (prop_tac "tcbPtr \<noteq> beforePtr")
   apply (fastforce dest: sym_heap_None simp: opt_map_def obj_at'_def split: option.splits)
  apply (prop_tac "tcbSchedNexts_of s beforePtr = Some afterPtr")
   apply (fastforce intro: sym_heapD2 simp: opt_map_def obj_at'_def)
  apply (fastforce dest: sym_heap_insert_into_middle_of_chain
                   simp: fun_upd_swap opt_map_red opt_map_upd_triv obj_at'_def)
  done

lemma tcbInReleaseQueue_update_sym_heap_sched_pointers[wp]:
  "threadSet (tcbInReleaseQueue_update f) tcbPtr \<lbrace>sym_heap_sched_pointers\<rbrace>"
  by (rule sym_heap_sched_pointers_lift; wpsimp wp: threadSet_field_inv)

lemma tcbQueued_update_sym_heap_sched_pointers[wp]:
  "threadSet (tcbQueued_update f) tcbPtr \<lbrace>sym_heap_sched_pointers\<rbrace>"
  by (rule sym_heap_sched_pointers_lift; wpsimp wp: threadSet_field_inv)

lemma tcbSchedEnqueue_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbSchedEnqueue_def
  apply (wpsimp wp: tcbQueuePrepend_sym_heap_sched_pointers threadGet_wp threadSet_sched_pointers
              simp: addToBitmap_def bitmap_fun_defs)
  apply (frule runnable'_not_inIPCQueueThreadState)
  apply (fastforce dest!: valid_sched_pointersD[where t=tcbPtr]
                    simp: opt_pred_def opt_map_def obj_at'_def)
  done

lemma tcbSchedAppend_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp wp: tcbQueueAppend_sym_heap_sched_pointers threadGet_wp threadSet_sched_pointers
              simp: addToBitmap_def bitmap_fun_defs)
  apply (frule runnable'_not_inIPCQueueThreadState)
  apply (fastforce dest!: valid_sched_pointersD[where t=tcbPtr]
                    simp: opt_pred_def opt_map_def obj_at'_def)
  done

crunch tcbSchedDequeue
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (wp: tcbQueueRemove_sym_heap_sched_pointers crunch_wps ignore: threadSet simp: crunch_simps)

crunch scheduleTCB
  for valid_sched_pointers[wp]: valid_sched_pointers
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (simp: crunch_simps wp: crunch_wps)

lemma tcbState_update_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s
        \<and> (is_sched_linked t s \<and> (inIPCQueueThreadState |< tcbStates_of' s) t
           \<longrightarrow> inIPCQueueThreadState st)\<rbrace>
   threadSet (tcbState_update (\<lambda>_. st)) t
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_sched_pointers_def)
  apply (intro conjI impI allI;
         clarsimp dest!: spec[where x=t] simp: obj_at'_def opt_pred_def opt_map_def)
  done

lemma setThreadState_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s
        \<and> (is_sched_linked t s \<and> (inIPCQueueThreadState |< tcbStates_of' s) t
           \<longrightarrow> inIPCQueueThreadState st)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding setThreadState_def
  by (wpsimp wp: tcbState_update_valid_sched_pointers)

lemma sts_sym_refs':
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of' s)
        \<and> st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st) t s\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. sym_refs (state_refs_of' s)\<rbrace>"
  apply (wpsimp wp: setThreadState_state_refs_of')
  apply (clarsimp dest!: st_tcb_at_state_refs_ofD'
                  elim!: rsubst[where P=sym_refs]
                 intro!: ext)
  by (fastforce simp: tcb_bound_refs'_def get_refs_def2)

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

lemma (in TcbAcc_R_2) asUser_global_refs':
  "\<lbrace>valid_global_refs'\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
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

lemma (in TcbAcc_R_2) storeWordUser_invs[wp]:
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

crunch addToBitmap, setQueue
  for ko_wp_at'[wp]: "\<lambda>s. P (ko_wp_at' Q p s)"

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

lemma getCurSc_corres[corres]:
  "corres (=) \<top> \<top> (gets cur_sc) (getCurSc)"
  unfolding getCurSc_def
  apply (rule corres_gets_trivial)
  by (clarsimp simp: state_relation_def)

crunch scActive
  for inv[wp]: P
  (wp: crunch_wps)

lemma threadSet_empty_tcbSchedContext_valid_tcbs'[wp]:
  "threadSet (tcbSchedContext_update Map.empty) t \<lbrace>valid_tcbs'\<rbrace>"
  by (wp threadSet_valid_tcbs')
     (simp add: valid_tcb'_def valid_tcbs'_def tcb_cte_cases_def tcb_cte_cases_neqs)

lemma thread_set_empty_tcb_sched_context_weaker_valid_sched_action[wp]:
  "thread_set (tcb_sched_context_update Map.empty) tcbPtr \<lbrace>weaker_valid_sched_action\<rbrace>"
  apply (simp only: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: weaker_valid_sched_action_def pred_tcb_at_def)
  apply (auto simp: is_tcb_def get_tcb_def obj_at_def  map_project_def tcbs_of_kh_def opt_map_def
                    pred_map_def map_join_def tcb_scps_of_tcbs_def sc_refill_cfgs_of_scs_def
             split: option.splits Structures_A.kernel_object.splits)
  done

lemma (in TcbAcc_R_2) sts_invs_minor':
  "\<lbrace>invs'
    and st_tcb_at' (\<lambda>st'. (\<forall>rptr. st' = BlockedOnReply rptr \<longrightarrow> st = BlockedOnReply rptr)
                          \<and> \<not> inIPCQueueThreadState st') t\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift irqs_masked_lift
                    setThreadState_valid_sched_pointers
                    setThreadState_sym_heap_sched_pointers
              simp: cteCaps_of_def o_def pred_tcb_at'_eq_commute)
  apply (intro conjI impI; fastforce?)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: pred_tcb_at'_def ko_wp_at'_def obj_at'_def opt_pred_def opt_map_def)
  done

lemma (in TcbAcc_R_2) sts_invs':
  "\<lbrace>(\<lambda>s. \<forall>rptr. st_tcb_at' ((=) (BlockedOnReply (Some rptr))) t s
                      \<longrightarrow> (is_reply_linked rptr s) \<longrightarrow> st = BlockedOnReply (Some rptr))
    and (\<lambda>s. is_sched_linked t s \<and> (inIPCQueueThreadState |< tcbStates_of' s) t
             \<longrightarrow> inIPCQueueThreadState st)
    and tcb_at' t
    and invs'\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_dom_schedule'_def)
  apply (wpsimp wp: valid_irq_node_lift irqs_masked_lift
                    setThreadState_valid_sched_pointers setThreadState_sym_heap_sched_pointers
              simp: cteCaps_of_def o_def)
  apply (clarsimp simp: valid_pspace'_def)
  apply fast
  done

lemma setReleaseQueue_ksReleaseQueue[wp]:
  "\<lbrace>\<lambda>_. P qs\<rbrace> setReleaseQueue qs \<lbrace>\<lambda>_ s. P (ksReleaseQueue s)\<rbrace>"
  by (wpsimp simp: setReleaseQueue_def)

lemma setReleaseQueue_pred_tcb_at'[wp]:
 "setReleaseQueue qs \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wpsimp simp: setReleaseQueue_def)

context TcbAcc_R begin

sublocale tcbReleaseRemove: typ_at_all_props' "tcbReleaseRemove tptr"
  by typ_at_props'

crunch tcbReleaseRemove, tcbQueueRemove, tcbReleaseEnqueue
  for valid_irq_handlers'[wp]: valid_irq_handlers'
  (wp: valid_irq_handlers_lift'')

crunch tcbReleaseRemove, tcbQueueRemove, tcbReleaseEnqueue
  for if_unsafe_then_cap'[wp]: if_unsafe_then_cap'
  (wp: crunch_wps threadSet_ifunsafe'T simp: update_tcb_cte_cases)

crunch setReleaseQueue, tcbQueueRemove, setReprogramTimer
  for valid_objs'[wp]: valid_objs'
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

crunch tcbReleaseRemove
  for valid_objs'[wp]: valid_objs'
  (simp: crunch_simps)

crunch tcbReleaseRemove, tcbQueueRemove, tcbReleaseEnqueue
  for pred_tcb_at'[wp]: "\<lambda>s. P' (pred_tcb_at' P obj t s)"
  (wp: crunch_wps threadSet_pred_tcb_no_state simp: tcb_to_itcb'_def)

crunch tcbReleaseRemove, tcbQueueRemove, tcbReleaseEnqueue
  for tcbDomain[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: crunch_wps threadSet_obj_at'_no_state)

end (* TcbAcc_R *)

crunch setReleaseQueue
  for obj_at'[wp]: "\<lambda>s. Q (obj_at' P ptr s)"

lemma getReleaseQueue_sp:
  "\<lbrace>P\<rbrace> getReleaseQueue \<lbrace>\<lambda>rv s. P s \<and> rv = ksReleaseQueue s\<rbrace>"
  by wpsimp

crunch setReprogramTimer
  for ksReleaseQueue[wp]: "\<lambda>s. P (ksReleaseQueue s)"

lemma tcbSchedPrev_update_tcbQueueds_of[wp]:
  "threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>\<lambda>s. P (tcbQueued |< tcbs_of' s)\<rbrace>"
  by (wpsimp wp: threadSet_field_opt_pred)

lemma tcbSchedNext_update_tcbQueueds_of[wp]:
  "threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>\<lambda>s. P (tcbQueued |< tcbs_of' s)\<rbrace>"
  by (wpsimp wp: threadSet_field_opt_pred)

lemma setReprogramTimer_ready_or_release'[wp]:
  "setReprogramTimer reprogramTimer \<lbrace>ready_or_release'\<rbrace>"
  unfolding setReprogramTimer_def
  apply wpsimp
  apply (clarsimp simp: ready_or_release'_def)
  done

lemma tcbQueueRemove_no_fail:
  "no_fail (\<lambda>s. (\<exists>ts. list_queue_relation ts queue (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                      \<and> (\<forall>t \<in> set ts. tcb_at' t s \<and> (t \<noteq> tcbPtr \<longrightarrow> sched_flag_set s t))
                      \<and> tcbPtr \<in> set ts)
                \<and> sym_heap_sched_pointers s \<and> valid_objs' s)
           (tcbQueueRemove queue tcbPtr)"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getTCB_wp no_fail_stateAssert)
  apply (frule (2) list_queue_relation_neighbour_in_set)
  apply (clarsimp simp: list_queue_relation_def)
  apply (prop_tac "tcbQueueHead queue \<noteq> Some tcbPtr \<longrightarrow> tcbSchedPrevs_of s tcbPtr \<noteq> None")
   apply (rule impI)
   apply (frule not_head_prev_not_None[where p=tcbPtr])
      apply (fastforce simp: inQ_def opt_pred_def opt_map_def obj_at'_def)
     apply (fastforce dest: heap_path_head)
    apply fastforce
   apply (fastforce simp: opt_map_def obj_at'_def valid_tcb'_def valid_bound_tcb'_def)
  apply (force dest!: not_last_next_not_None[where p=tcbPtr]
                simp: queue_end_valid_def opt_map_def obj_at'_def valid_tcb'_def)
  done

crunch removeFromBitmap
 for (no_fail) no_fail[wp]

lemma ready_or_release'_inQ:
  "ready_or_release' s \<Longrightarrow>
   \<forall>t. \<not> ((inQ domain prio |< tcbs_of' s) t \<and> (tcbInReleaseQueue |< tcbs_of' s) t)"
  by (clarsimp simp: ready_or_release'_def inQ_def opt_pred_def opt_map_def split: option.splits)

context TcbAcc_R_2 begin

lemma set_tcb_queue_not_queued_rewrite:
  "monadic_rewrite False True (\<lambda>s. ready_queues s = queues \<and> tcbPtr \<notin> set (queues d p))
     (set_tcb_queue d p (tcb_sched_dequeue tcbPtr (queues d p))) (return ())"
  unfolding set_tcb_queue_def
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_modify_noop)
  apply (rename_tac s)
  apply (case_tac s; fastforce)
  done

lemma setQueue_gets_rewrite:
  "(\<And>P. h \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace>) \<Longrightarrow>
   monadic_rewrite F E \<top>
     (do queue \<leftarrow> f;
         setQueue d p queue;
         h;
         g queue od)
     (do queue \<leftarrow> f;
         setQueue d p queue;
         h;
         queue' \<leftarrow> gets (\<lambda>s. ksReadyQueues s (d, p));
         g queue'
      od)"
  apply (intro monadic_rewrite_bind_tail)
    apply simp
    apply (intro monadic_rewrite_bind_tail)
     apply monadic_rewrite_symb_exec_r
      apply (rule monadic_rewrite_guard_arg_cong)
      apply assumption
     apply (wpsimp simp: setQueue_def | rule hoare_lift_Pf2[where f=ksReadyQueues])+
  done

lemma tcbSchedDequeue_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (ep_queues_blocked and ntfn_queues_blocked
      and in_correct_ready_q and ready_qs_distinct and ready_queues_runnable
      and ready_or_release and tcb_at tcb_ptr and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_objs')
     (tcb_sched_action tcb_sched_dequeue tcb_ptr) (tcbSchedDequeue tcbPtr)"
  supply if_split[split del] bind_return[simp del] return_bind[simp del]
  apply (rule_tac Q'="tcb_at' tcbPtr" in corres_cross_add_guard)
   apply (fastforce intro!: tcb_at_cross simp: vs_all_heap_simps obj_at_def is_tcb_def)
  apply (clarsimp simp: tcb_sched_action_def get_tcb_queue_def
                        tcbSchedDequeue_def getQueue_def unless_def)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; wpsimp?)
  apply (rename_tac domain)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; wpsimp?)
  apply (rename_tac priority)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (fastforce intro: ready_or_release_cross)
  apply (rule corres_stateAssert_implied[where P=P and P'=P for P, simplified, rotated])
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_stateAssert_ignore, fastforce)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rename_tac queued)
  apply (rule_tac Q="\<lambda>s. queued = in_ready_q tcbPtr s" in corres_cross_add_abs_guard)
   apply (fastforce dest: state_relation_ready_queues_relation in_ready_q_tcbQueued_eq[where t=tcbPtr]
                    simp: opt_pred_def opt_map_red obj_at'_def)
  apply (case_tac "\<not> queued"; clarsimp)
   apply (clarsimp simp: return_bind)
   apply (rule monadic_rewrite_corres_l[where P=P and Q=P for P, simplified])
    apply (rule monadic_rewrite_guard_imp[OF set_tcb_queue_not_queued_rewrite])
    apply (clarsimp simp: not_queued_def)
   apply clarsimp
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; wpsimp?)
  apply (rename_tac domain')
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; wpsimp?)
  apply (rename_tac priority')
  apply (rule_tac F="domain' = domain \<and> priority' = priority" in corres_req)
   apply (fastforce dest: pspace_relation_tcb_domain_priority state_relation_pspace_relation
                    simp: obj_at_def obj_at'_def)
  apply clarsimp
  apply (rule corres_symb_exec_r[OF _ gets_sp]; wpsimp?)
  apply (rule monadic_rewrite_corres_r[where P'=P' and Q=P' for P', simplified])
   apply (subst bind_dummy_ret_val)+
   apply (rule monadic_rewrite_guard_imp)
     apply (rule setQueue_gets_rewrite)
    apply wpsimp
   apply wpsimp
  apply (rule corres_underlying_from_rcorres)
   apply ((wpsimp wp: tcbQueueRemove_no_fail hoare_vcg_ex_lift
                      threadSet_sched_pointers threadSet_valid_objs' hoare_vcg_ball_lift
                      hoare_vcg_const_imp_lift hoare_disjI1 threadSet_opt_pred_other
           | wps)+)[1]
   apply (clarsimp simp: ex_abs_def obj_at_def in_ready_q_def)
   apply normalise_obj_at'
   apply (rename_tac s tcb d p tcb')
   apply (rule_tac x="ready_queues s d p" in exI)
   apply (rule conjI)
    apply (force dest!: in_correct_ready_qD state_relation_ready_queues_relation
                  simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply clarsimp
   apply (rule conjI)
    subgoal by (force intro!: tcb_at_cross simp: ready_queues_runnable_def)
   apply (force intro: in_ready_q_tcbQueued_eq[THEN iffD1] simp: in_ready_q_def)
  \<comment> \<open>break off the call to removeFromBitmap\<close>
  apply (rule rcorres_add_return_l)
  apply (rule rcorres_add_return_l)
  apply (subst bind_assoc[symmetric])
  apply clarsimp
  apply (subst bind_assoc[symmetric])
  apply (rule rcorres_split)
   apply clarsimp
   apply (rule rcorres_from_corres[where P=\<top> and P'=\<top> and r=dc, simplified])
   apply (rule corres_symb_exec_r[OF _ gets_sp]; (solves wpsimp)?)
   apply (clarsimp simp: when_def split: if_splits)
   apply (corres corres: removeFromBitmap_corres_noop)
  apply (rule rcorres_add_return_l)
  \<comment> \<open>set the ready queue\<close>
  apply (clarsimp simp: state_relation_def pspace_relation_heap_pspace_relation
                        ghost_relation_heap_ghost_relation heap_pspace_relation_def)
  apply (rcorres_conj_lift \<open>fastforce\<close> simp: set_tcb_queue_def wp: threadSet_field_inv)+
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ep_queues_relation\<close>
   apply (simp only: ep_queues_relation_def)
   apply (rcorres rcorres: rcorres_threadSet_list_queue_relation
                           tcbQueueRemove_rcorres_other rcorres_op_lifts)
   apply normalise_obj_at'
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def obj_at_def
                         in_ready_q_def)
   apply (metis in_correct_ready_qD ep_queues_ready_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ntfn_queues_relation\<close>
   apply (simp only: ntfn_queues_relation_def)
   apply (rcorres rcorres: rcorres_threadSet_list_queue_relation
                           tcbQueueRemove_rcorres_other rcorres_op_lifts)
   apply normalise_obj_at'
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def obj_at_def
                         in_ready_q_def)
   apply (metis in_correct_ready_qD ntfn_queues_ready_queues_disjoint)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>ready_queues_relation\<close>
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (intro rcorres_allI_fwd; (solves wpsimp)?)
   apply (rename_tac d p)
   apply (case_tac "d \<noteq> domain \<or> p \<noteq> priority")
    apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
     apply (rule_tac p="\<lambda>s. ready_queues s d p" in rcorres_lift_abs)
      apply (rule_tac p="\<lambda>s'. ksReadyQueues s' (d, p)" in rcorres_lift_conc)
      apply (rcorres rcorres: rcorres_threadSet_list_queue_relation tcbQueueRemove_rcorres_other)
       apply normalise_obj_at'
       apply (clarsimp simp: obj_at_def in_ready_q_def)
       apply (metis in_correct_ready_qD ready_queues_disjoint)
      apply (wpsimp wp: setQueue_ksReadyQueues_other)
     apply (wpsimp wp: set_tcb_queue_ready_queues_other)
    apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
     apply (intro rcorres_allI_fwd; (solves wpsimp)?)
     apply (rename_tac t)
     apply (rule_tac p="\<lambda>s. t \<in> set (ready_queues s d p)" in rcorres_lift_abs)
      apply (rule_tac p="\<lambda>s'. (inQ d p |< tcbs_of' s') t" in rcorres_lift_conc)
       apply (rule rcorres_prop_fwd; wpsimp)
      apply (wpsimp wp: tcbQueued_update_inQ_other hoare_vcg_disj_lift
                  simp: opt_pred_disj[simplified pred_disj_def, symmetric] simp_del: disj_not1)
      apply (clarsimp simp: opt_pred_def opt_map_red obj_at'_def)
     apply (wpsimp wp: set_tcb_queue_ready_queues_other)
    apply (rule rcorres_lift_conc_only; wpsimp wp: setQueue_ksReadyQueues_other)
   \<comment> \<open>d = domain \<and> p = priority\<close>
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rcorres rcorres: rcorres_threadSet_ready_queues_list_queue_relation
                            tcbQueueRemove_rcorres)
    apply (clarsimp simp: obj_at_def in_ready_q_def tcb_sched_dequeue_def removeAll_filter_not_eq)
    apply (metis in_correct_ready_qD)
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (intro rcorres_allI_fwd; (solves wpsimp)?)
    apply (rename_tac t)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (case_tac "t \<noteq> tcbPtr")
     apply (wpsimp wp: threadSet_opt_pred_other)
     apply (clarsimp simp: set_tcb_queue_def tcb_sched_dequeue_def in_monad)
    apply (clarsimp simp: set_tcb_queue_def tcb_sched_dequeue_def in_monad)
    apply (wpsimp wp: tcbQueued_False_makes_not_inQ)
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rule rcorres_imp_lift_fwd; (solves wpsimp)?)
     apply (rule rcorres_prop_fwd; wpsimp)
    apply (rule rcorres_from_valid_det; (solves wpsimp)?)
    apply (wpsimp wp: setQueue_ksReadyQueues_other)
    apply (force dest!: valid_objs'_valid_tcbs' valid_tcbs'_maxDomain[where t=tcbPtr]
                  simp: obj_at'_def)
   apply (rule rcorres_imp_lift_fwd; (solves wpsimp)?)
    apply (rule rcorres_prop_fwd; wpsimp)
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (wpsimp wp: setQueue_ksReadyQueues_other)
   apply (force dest!: valid_objs'_valid_tcbs' valid_tcbs'_maxPriority[where t=tcbPtr]
                 simp: obj_at'_def)
  apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
   \<comment> \<open>release_queue_relation\<close>
   apply (clarsimp simp: release_queue_relation_def)
   apply (rule rcorres_conj_lift_fwd; (solves wpsimp)?)
    apply (rule_tac p=release_queue in rcorres_lift_abs)
     apply (rule_tac p=ksReleaseQueue in rcorres_lift_conc)
      apply (rcorres rcorres: rcorres_threadSet_list_queue_relation tcbQueueRemove_rcorres_other)
      apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def obj_at_def
                            in_ready_q_def)
      apply (metis in_correct_ready_qD Int_commute ready_or_release_disjoint)
     apply wpsimp
    apply wpsimp
   apply (rule rcorres_from_valid_det; (solves wpsimp)?)
   apply (wpsimp wp: hoare_vcg_all_lift)
   apply (clarsimp simp: set_tcb_queue_def in_monad)
  by (rcorres_conj_lift \<open>fastforce\<close> simp: set_tcb_queue_def wp: threadSet_field_inv)+

end (* TcbAcc_R_2 *)

lemma tcbReleaseRemove_sym_heap_sched_pointers[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>sym_heap_sched_pointers\<rbrace>"
  unfolding tcbReleaseRemove_def
  apply (wpsimp wp: inReleaseQueue_wp)
  apply (fastforce simp: obj_at'_def)
  done

crunch setReprogramTimer
  for valid_mdb'[wp]: valid_mdb'
  (simp: valid_mdb'_def)

lemma tcbSchedNext_update_valid_mdb'[wp]:
  "threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (clarsimp simp: obj_at'_def update_tcb_cte_cases)
  done

lemma tcbSchedPrev_update_valid_mdb'[wp]:
  "threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (clarsimp simp: obj_at'_def update_tcb_cte_cases)
  done

lemma tcbInReleaseQueue_update_valid_mdb'[wp]:
  "threadSet (tcbInReleaseQueue_update f) tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  apply (wpsimp wp: threadSet_mdb')
  apply (clarsimp simp: obj_at'_def update_tcb_cte_cases)
  done

lemma tcbQueueRemove_valid_mdb'[wp]:
  "tcbQueueRemove q tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  unfolding tcbQueueRemove_def
  by (wpsimp wp: getTCB_wp)

crunch setReleaseQueue
  for valid_mdb'[wp]: valid_mdb'
  (simp: valid_mdb'_def)

lemma tcbInReleaseQueue_update_valid_objs'[wp]:
  "threadSet (tcbInReleaseQueue_update f) tcbPtr \<lbrace>valid_objs'\<rbrace>"
  by (wpsimp wp: threadSet_valid_objs')

lemma tcbQueued_update_valid_objs'[wp]:
  "threadSet (tcbQueued_update f) tcbPtr \<lbrace>valid_objs'\<rbrace>"
  by (wpsimp wp: threadSet_valid_objs')

lemma tcbReleaseRemove_valid_mdb'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_mdb'\<rbrace>"
  unfolding tcbReleaseRemove_def
  by (wpsimp wp: tcbQueueRemove_valid_mdb')

crunch setReprogramTimer
  for obj_at'[wp]: "\<lambda>s. Q (obj_at' P ptr s)"
  and valid_tcbs'[wp]: valid_tcbs'

lemma tcbInReleaseQueue_False_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s \<and> \<not> is_sched_linked tcbPtr s\<rbrace>
   threadSet (tcbInReleaseQueue_update (\<lambda>_. False)) tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: valid_sched_pointers_def obj_at'_def opt_map_red opt_pred_def)
  done

lemma tcbReleaseRemove_valid_sched_pointers[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def)
  apply (wpsimp wp: tcbInReleaseQueue_False_valid_sched_pointers tcbQueueRemove_valid_sched_pointers
                    inReleaseQueue_wp)
  apply normalise_obj_at'
  apply (clarsimp simp: valid_sched_pointers_except_def)
  done

lemma tcbReleaseRemove_valid_bitmaps[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  by (wpsimp wp: valid_bitmaps_lift)

lemma (in TcbAcc_R_2) tcbReleaseRemove_invs':
  "tcbReleaseRemove tcbPtr \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift irqs_masked_lift untyped_ranges_zero_lift
                    valid_replies'_lift
              simp: cteCaps_of_def o_def)
  done

crunch setReleaseQueue, setReprogramTimer
  for valid_bitmapQ[wp]: valid_bitmapQ
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans
  and bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans
  (simp: crunch_simps valid_bitmapQ_def bitmapQ_def bitmapQ_no_L2_orphans_def
         bitmapQ_no_L1_orphans_def)

lemma tcbInReleaseQueue_update_st_tcb_at'[wp]:
  "threadSet (tcbInReleaseQueue_update b) t \<lbrace>\<lambda>s. Q (st_tcb_at' P t' s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (cases "t=t'")
   apply (fastforce simp: gen_obj_at_simps st_tcb_at'_def ps_clear_def)
  apply (erule back_subst[where P=Q])
  apply (fastforce simp: gen_obj_at_simps st_tcb_at'_def ps_clear_def)
  done

declare hoare_in_monad_post[wp]
declare trans_state_update'[symmetric,simp]
declare storeWordUser_typ_at'[wp]

end
