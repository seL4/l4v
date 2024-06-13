(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TcbAcc_R
imports CSpace_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

declare if_weak_cong [cong]
declare hoare_in_monad_post[wp]
declare trans_state_update'[symmetric,simp]
declare storeWordUser_typ_at' [wp]

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
  apply (clarsimp simp: gets_def bind_assoc return_def Nondet_Monad.bind_def get_def
                  split: if_splits)
  done

lemma getHighestPrio_inv[wp]:
  "\<lbrace> P \<rbrace> getHighestPrio d \<lbrace>\<lambda>_. P \<rbrace>"
  unfolding bitmap_fun_defs by simp

lemma valid_bitmapQ_bitmapQ_simp:
  "valid_bitmapQ s \<Longrightarrow> bitmapQ d p s = (\<not> tcbQueueEmpty (ksReadyQueues s (d, p)))"
  by (simp add: valid_bitmapQ_def)

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

lemma st_tcb_at_coerce_abstract:
  assumes t: "st_tcb_at' P t c"
  assumes sr: "(a, c) \<in> state_relation"
  shows "st_tcb_at (\<lambda>st. \<exists>st'. thread_state_relation st st' \<and> P st') t a"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def
                        projectKOs)
  apply (erule (1) pspace_dom_relatedE)
  apply (erule (1) obj_relation_cutsE, simp_all)
  by (fastforce simp: st_tcb_at_def obj_at_def other_obj_relation_def tcb_relation_def
               split: Structures_A.kernel_object.split_asm if_split_asm
                      arch_kernel_obj.split_asm)+

lemma st_tcb_at_runnable_coerce_concrete:
  assumes t: "st_tcb_at runnable t a"
  assumes sr: "(a, c) \<in> state_relation"
  assumes tcb: "tcb_at' t c"
  shows "st_tcb_at' runnable' t c"
  using t
  apply -
  apply (rule ccontr)
  apply (drule pred_tcb_at'_Not[THEN iffD2, OF conjI, OF tcb])
  apply (drule st_tcb_at_coerce_abstract[OF _ sr])
  apply (clarsimp simp: st_tcb_def2)
  apply (case_tac "tcb_state tcb"; simp)
  done

lemma valid_objs_valid_tcbE:
  "\<And>s t.\<lbrakk> valid_objs' s; tcb_at' t s; \<And>tcb. valid_tcb' tcb s \<Longrightarrow> R s tcb \<rbrakk> \<Longrightarrow> obj_at' (R s) t s"
  apply (clarsimp simp add: projectKOs valid_objs'_def ran_def typ_at'_def
                            ko_wp_at'_def valid_obj'_def valid_tcb'_def obj_at'_def)
  apply (fastforce simp: projectKO_def projectKO_opt_tcb return_def valid_tcb'_def)
  done

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

lemma dmo_invs_no_cicd':
  assumes masks: "\<And>P. \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"
  shows "\<lbrace>(\<lambda>s. \<forall>m. \<forall>(r,m')\<in>fst (f m). \<forall>p.
             pointerInUserData p s \<or> pointerInDeviceData p s \<or>
             underlying_memory m' p = underlying_memory m p) and
          invs_no_cicd'\<rbrace> doMachineOp f \<lbrace>\<lambda>r. invs_no_cicd'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (subst invs_no_cicd'_machine)
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

lemma preemptionPoint_irq [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> preemptionPoint -,
   \<lbrace>\<lambda>irq s. intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive\<rbrace>"
  apply (simp add: preemptionPoint_def setWorkUnits_def modifyWorkUnits_def getWorkUnits_def)
  apply (wp whenE_wp|wpc)+
     apply (rule hoare_post_imp)
      prefer 2
     apply (rule doMachineOp_getActiveIRQ_IRQ_active)
    apply clarsimp
   apply wp+
  apply clarsimp
  done

lemmas doMachineOp_obj_at = doMachineOp_obj_at'

lemma updateObject_tcb_inv:
  "\<lbrace>P\<rbrace> updateObject (obj::tcb) ko p q n \<lbrace>\<lambda>rv. P\<rbrace>"
  by simp (rule updateObject_default_inv)

lemma st_tcb_at_runnable_cross:
  "\<lbrakk> st_tcb_at runnable t s; pspace_aligned s; pspace_distinct s; (s, s') \<in> state_relation \<rbrakk>
  \<Longrightarrow> st_tcb_at' runnable' t s'"
  apply (frule (1) pspace_distinct_cross, fastforce simp: state_relation_def)
  apply (frule pspace_aligned_cross, fastforce simp: state_relation_def)
  apply (prop_tac "tcb_at t s", clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
  apply (drule (2) tcb_at_cross, fastforce simp: state_relation_def)
  apply (erule (2) st_tcb_at_runnable_coerce_concrete)
  done

lemma cur_tcb_cross:
  "\<lbrakk> cur_tcb s; pspace_aligned s; pspace_distinct s; (s,s') \<in> state_relation \<rbrakk> \<Longrightarrow> cur_tcb' s'"
  apply (clarsimp simp: cur_tcb'_def cur_tcb_def state_relation_def)
  apply (erule (3) tcb_at_cross)
  done

lemma valid_objs_valid_tcbE':
  assumes "valid_objs' s"
          "tcb_at' t s"
          "\<And>tcb. ko_at' tcb t s \<Longrightarrow> valid_tcb' tcb s \<Longrightarrow> R s tcb"
  shows "obj_at' (R s) t s"
  using assms
  apply (clarsimp simp add: projectKOs valid_objs'_def ran_def typ_at'_def
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
  by (fastforce del: valid_objs'_valid_tcbs' intro: valid_objs'_valid_tcbs')

lemma valid_tcbs'_maxDomain:
  "\<And>s t. \<lbrakk> valid_tcbs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t s"
  by (clarsimp simp: valid_tcbs'_def obj_at'_def valid_tcb'_def projectKOs)

lemmas valid_objs'_maxDomain = valid_tcbs'_maxDomain[OF valid_objs'_valid_tcbs']

lemma valid_tcbs'_maxPriority:
  "\<And>s t. \<lbrakk> valid_tcbs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t s"
  by (clarsimp simp: valid_tcbs'_def obj_at'_def valid_tcb'_def projectKOs)

lemmas valid_objs'_maxPriority = valid_tcbs'_maxPriority[OF valid_objs'_valid_tcbs']

lemma valid_tcbs'_obj_at':
  assumes "valid_tcbs' s"
          "tcb_at' t s"
          "\<And>tcb. ko_at' tcb t s \<Longrightarrow> valid_tcb' tcb s \<Longrightarrow> R s tcb"
  shows "obj_at' (R s) t s"
  using assms
  apply (clarsimp simp add: valid_tcbs'_def ran_def typ_at'_def projectKOs
                            ko_wp_at'_def valid_obj'_def valid_tcb'_def obj_at'_def)
  done

lemma update_valid_tcb'[simp]:
  "\<And>f. valid_tcb' tcb (ksReadyQueuesL1Bitmap_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueuesL2Bitmap_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksReadyQueues_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksSchedulerAction_update f s) = valid_tcb' tcb s"
  "\<And>f. valid_tcb' tcb (ksDomainTime_update f s) = valid_tcb' tcb s"
  by (auto simp: valid_tcb'_def valid_tcb_state'_def valid_bound_tcb'_def valid_bound_ntfn'_def
          split: option.splits thread_state.splits)

lemma update_valid_tcbs'[simp]:
  "\<And>f. valid_tcbs' (ksReadyQueuesL1Bitmap_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueuesL2Bitmap_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksReadyQueues_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksSchedulerAction_update f s) = valid_tcbs' s"
  "\<And>f. valid_tcbs' (ksDomainTime_update f s) = valid_tcbs' s"
  by (simp_all add: valid_tcbs'_def)

lemma setObject_update_TCB_corres':
  assumes tcbs: "tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb'"
  assumes tables: "\<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb'"
  assumes sched_pointers: "tcbSchedPrev new_tcb' = tcbSchedPrev tcb'"
                          "tcbSchedNext new_tcb' = tcbSchedNext tcb'"
  assumes flag: "tcbQueued new_tcb' = tcbQueued tcb'"
  assumes r: "r () ()"
  assumes exst: "exst_same tcb' new_tcb'"
  shows "corres r (ko_at (TCB tcb) ptr) (ko_at' tcb' ptr)
                  (set_object ptr (TCB new_tcb)) (setObject ptr new_tcb')"
  apply (rule_tac F="tcb_relation tcb tcb' \<and> exst_same tcb' new_tcb'" in corres_req)
   apply (clarsimp simp: state_relation_def obj_at_def obj_at'_def)
   apply (frule(1) pspace_relation_absD)
   apply (clarsimp simp: tcb_relation_cut_def exst)
   apply (clarsimp simp: projectKOs tcb_relation_cut_def exst)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
   apply (clarsimp simp: obj_at'_def)
  apply (unfold set_object_def setObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def projectKOs obj_at_def
                        updateObject_default_def in_magnitude_check obj_at'_def)
  apply (rename_tac s s' t')
  apply (prop_tac "t' = s'")
   apply (clarsimp simp: magnitudeCheck_def in_monad split: option.splits)
  apply (drule singleton_in_magnitude_check)
  apply (prop_tac "map_to_ctes ((ksPSpace s') (ptr \<mapsto> injectKO new_tcb'))
                   = map_to_ctes (ksPSpace s')")
   apply (frule_tac tcb=new_tcb' and tcb=tcb' in map_to_ctes_upd_tcb)
     apply (clarsimp simp: objBits_simps)
    apply (clarsimp simp: objBits_simps ps_clear_def3 field_simps objBits_defs mask_def)
   apply (insert tables')[1]
   apply (rule ext)
   apply (clarsimp split: if_splits)
   apply blast
  apply (prop_tac "obj_at (same_caps (TCB new_tcb)) ptr s")
   using tables
   apply (fastforce simp: obj_at_def)
  apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update swp_def
                        obj_at_def assms)
  apply (clarsimp simp add: state_relation_def)
  apply (subst conj_assoc[symmetric])
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x=ptr in allE)+
   apply clarsimp
  apply (simp only: pspace_relation_def pspace_dom_update dom_fun_upd2 simp_thms)
  apply (elim conjE)
  apply (frule bspec, erule domI)
  apply clarsimp
  apply (rule conjI)
   apply (simp only: pspace_relation_def simp_thms
                     pspace_dom_update[where x="kernel_object.TCB _"
                                         and v="kernel_object.TCB _",
                                       simplified a_type_def, simplified])
  apply (rule conjI)
   using assms
   apply (simp only: dom_fun_upd2 simp_thms)
   apply (frule bspec, erule domI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: tcb_relation_cut_def split: if_split_asm kernel_object.split_asm)
   apply (rename_tac aa ba)
   apply (drule_tac x="(aa, ba)" in bspec, simp)
   apply clarsimp
   apply (frule_tac ko'="kernel_object.TCB tcb" and x'=ptr in obj_relation_cut_same_type)
      apply (simp add: tcb_relation_cut_def)+
   apply clarsimp
  apply (extract_conjunct \<open>match conclusion in "ekheap_relation _ _" \<Rightarrow> -\<close>)
   apply (simp only: ekheap_relation_def)
   apply (rule ballI, drule (1) bspec)
   apply (insert exst)
   apply (clarsimp simp: etcb_relation_def exst_same_def)
  apply (extract_conjunct \<open>match conclusion in "ready_queues_relation_2 _ _ _ _ _" \<Rightarrow> -\<close>)
   apply (insert sched_pointers flag exst)
   apply (clarsimp simp: ready_queues_relation_def Let_def)
   apply (prop_tac "(tcbSchedNexts_of s')(ptr := tcbSchedNext new_tcb') = tcbSchedNexts_of s'")
    apply (fastforce simp: opt_map_def)
   apply (prop_tac "(tcbSchedPrevs_of s')(ptr := tcbSchedPrev new_tcb') = tcbSchedPrevs_of s'")
    apply (fastforce simp: opt_map_def)
   apply (clarsimp simp: ready_queue_relation_def opt_pred_def opt_map_def exst_same_def inQ_def
                  split: option.splits)
   apply (metis (no_types, lifting) tcb_of'_TCB)
  apply (clarsimp simp: fun_upd_def caps_of_state_after_update cte_wp_at_after_update swp_def
                        obj_at_def)
  done

lemma setObject_update_TCB_corres:
  "\<lbrakk>tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb';
     \<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb;
     \<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb';
     tcbSchedPrev new_tcb' = tcbSchedPrev tcb'; tcbSchedNext new_tcb' = tcbSchedNext tcb';
     tcbQueued new_tcb' = tcbQueued tcb'; exst_same tcb' new_tcb';
     r () ()\<rbrakk> \<Longrightarrow>
   corres r
     (\<lambda>s. get_tcb ptr s = Some tcb) (\<lambda>s'. (tcb', s') \<in> fst (getObject ptr s'))
     (set_object ptr (TCB new_tcb)) (setObject ptr new_tcb')"
  apply (rule corres_guard_imp)
    apply (erule (7) setObject_update_TCB_corres')
   apply (clarsimp simp: getObject_def in_monad split_def obj_at'_def projectKOs
                         loadObject_default_def objBits_simps' in_magnitude_check)+
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
  apply simp
  done

lemma threadGet_corres:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> r (f tcb) (f' tcb')"
  shows      "corres r (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                       (thread_get f t) (threadGet f' t)"
  apply (simp add: thread_get_def threadGet_def)
  apply (fold liftM_def)
  apply simp
  apply (rule corres_rel_imp)
   apply (rule getObject_TCB_corres)
  apply (simp add: x)
  done

lemma threadGet_inv [wp]: "\<lbrace>P\<rbrace> threadGet f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: threadGet_def getObject_inv_tcb | wp)+

lemma ball_tcb_cte_casesI:
  "\<lbrakk> P (tcbCTable, tcbCTable_update);
     P (tcbVTable, tcbVTable_update);
     P (tcbReply, tcbReply_update);
     P (tcbCaller, tcbCaller_update);
     P (tcbIPCBufferFrame, tcbIPCBufferFrame_update) \<rbrakk>
    \<Longrightarrow> \<forall>x \<in> ran tcb_cte_cases. P x"
  by (simp add: tcb_cte_cases_def)

lemma all_tcbI:
  "\<lbrakk> \<And>a b c d e f g h i j k l m n p q r s. P (Thread a b c d e f g h i j k l m n p q r s) \<rbrakk>
   \<Longrightarrow> \<forall>tcb. P tcb"
  by (rule allI, case_tac tcb, simp)

lemma threadset_corresT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation (f tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  assumes sched_pointers: "\<And>tcb. tcbSchedPrev (f' tcb) = tcbSchedPrev tcb"
                          "\<And>tcb. tcbSchedNext (f' tcb) = tcbSchedNext tcb"
  assumes flag: "\<And>tcb. tcbQueued (f' tcb) = tcbQueued tcb"
  assumes e: "\<And>tcb'. exst_same tcb' (f' tcb')"
  shows      "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                     (thread_set f t) (threadSet f' t)"
  apply (simp add: thread_set_def threadSet_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getObject_TCB_corres])
      apply (rule setObject_update_TCB_corres')
             apply (erule x)
            apply (rule y)
           apply (clarsimp simp: bspec_split [OF spec [OF z]])
           apply fastforce
          apply (rule sched_pointers)
         apply (rule sched_pointers)
        apply (rule flag)
       apply simp
      apply (rule e)
     apply wp+
   apply (clarsimp simp add: tcb_at_def obj_at_def)
   apply (drule get_tcb_SomeD)
   apply fastforce
  apply simp
  done

lemmas threadset_corres =
    threadset_corresT [OF _ _ all_tcbI, OF _ ball_tcb_cap_casesI ball_tcb_cte_casesI]

lemmas pspace_relation_tcb_at = tcb_at'_cross

lemma threadSet_corres_noopT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation tcb (fn tcb')"
  assumes y: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (fn tcb) = getF tcb"
  assumes s: "\<forall>tcb'. tcbSchedPrev (fn tcb') = tcbSchedPrev tcb'"
             "\<forall>tcb'. tcbSchedNext (fn tcb') = tcbSchedNext tcb'"
  assumes f: "\<And>tcb'. tcbQueued (fn tcb') = tcbQueued tcb'"
  assumes e: "\<And>tcb'. exst_same tcb' (fn tcb')"
  shows      "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                        (return v) (threadSet fn t)"
proof -
  have S: "\<And>t s. tcb_at t s \<Longrightarrow> return v s = (thread_set id t >>= (\<lambda>x. return v)) s"
    apply (clarsimp simp: tcb_at_def)
    apply (simp add: return_def thread_set_def gets_the_def assert_def
                     assert_opt_def simpler_gets_def set_object_def get_object_def
                     put_def get_def bind_def)
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
          apply (rule e)
         apply (rule corres_noop [where P=\<top> and P'=\<top>])
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
  assumes s: "\<forall>tcb'. tcbSchedPrev (fn tcb') = tcbSchedPrev tcb'"
             "\<forall>tcb'. tcbSchedNext (fn tcb') = tcbSchedNext tcb'"
  assumes f: "\<And>tcb'. tcbQueued (fn tcb') = tcbQueued tcb'"
  assumes e: "\<And>tcb'. exst_same tcb' (fn tcb')"
  shows      "corres r (tcb_at t and pspace_aligned and pspace_distinct and P) P'
                     m (threadSet fn t >>= (\<lambda>rv. m'))"
  apply (rule corres_guard_imp)
    apply (subst return_bind[symmetric])
    apply (rule corres_split_nor[OF threadSet_corres_noopT])
            apply (simp add: x)
           apply (rule y)
          apply (fastforce simp: s)
         apply (fastforce simp: s)
        apply (fastforce simp: f)
       apply (rule e)
      apply (rule z)
     apply (wp w)+
   apply simp
  apply simp
  done

lemmas threadSet_corres_noop_split =
    threadSet_corres_noop_splitT [OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

lemma threadSet_tcb' [wp]:
  "\<lbrace>tcb_at' t\<rbrace> threadSet f t' \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  by (simp add: threadSet_def) wp

lemma threadSet_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  unfolding threadSet_def
  by (simp add: updateObject_default_def | wp setObject_nosch)+

(* The function "thread_set f p" updates a TCB at p using function f.
   It should not be used to change capabilities, though. *)
lemma setObject_tcb_valid_objs:
  "\<lbrace>valid_objs' and (tcb_at' t and valid_obj' (injectKO v))\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (rule setObject_valid_objs')
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma setObject_tcb_at':
  "\<lbrace>tcb_at' t'\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv. tcb_at' t'\<rbrace>"
  apply (rule obj_at_setObject1)
   apply (clarsimp simp: updateObject_default_def return_def in_monad)
  apply (simp add: objBits_simps)
  done

lemma setObject_sa_unchanged:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv s.  P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp | simp add: updateObject_default_def)+
  done

lemma setObject_queues_unchanged:
  assumes inv: "\<And>P p q n obj. \<lbrace>P\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>r. P\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject t v \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp inv | simp)+
  done

lemma setObject_queues_unchanged_tcb[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  apply (rule setObject_queues_unchanged)
  apply (wp|simp add: updateObject_default_def)+
  done

lemma setObject_queuesL1_unchanged_tcb[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def)+

lemma setObject_queuesL2_unchanged_tcb[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def)+

lemma setObject_tcb_ctes_of[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s) \<and>
     obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t s\<rbrace>
     setObject t v
   \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (rule setObject_ctes_of)
   apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                         obj_at'_def objBits_simps' in_magnitude_check
                         projectKOs)
   apply fastforce
  apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                        obj_at'_def objBits_simps in_magnitude_check
                        projectKOs bind_def)
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
                                  \<union> tcb_bound_refs' (tcbBoundNotification v)))\<rbrace>
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
   apply (clarsimp simp: updateObject_default_def in_monad projectKOs
                         in_magnitude_check objBits_simps' prod_eq_iff
                         obj_at'_def)
   apply fastforce
  apply (clarsimp simp: updateObject_default_def bind_def projectKOs)
  done

lemma setObject_tcb_idle':
  "\<lbrace>\<lambda>s. valid_idle' s \<and>
     (t = ksIdleThread s \<longrightarrow> idle' (tcbState v) \<and> tcbBoundNotification v = None)\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_pre)
  apply (rule setObject_idle')
      apply (simp add: objBits_simps')+
   apply (simp add: updateObject_default_inv)
  apply (simp add: projectKOs idle_tcb_ps_def idle_tcb'_def)
  done

lemma setObject_tcb_irq_node'[wp]:
  "\<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_tcb_ifunsafe':
  "\<lbrace>if_unsafe_then_cap' and obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  unfolding pred_conj_def
  apply (rule setObject_ifunsafe')
    apply (clarsimp simp: updateObject_default_def in_monad projectKOs
                          in_magnitude_check objBits_simps' prod_eq_iff
                          obj_at'_def)
    apply fastforce
   apply (clarsimp simp: updateObject_default_def bind_def projectKOs)
  apply wp
  done

lemma setObject_tcb_arch' [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  apply (simp add: setObject_def split_def updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_tcb_valid_arch' [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (wp valid_arch_state_lift' setObject_typ_at')

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
     apply (clarsimp simp: updateObject_default_def in_monad projectKOs
                           in_magnitude_check objBits_simps' prod_eq_iff
                           obj_at'_def)
     apply fastforce
    apply (clarsimp simp: updateObject_default_def in_monad prod_eq_iff
                          obj_at'_def objBits_simps in_magnitude_check
                          projectKOs bind_def)
   apply (wp | wp setObject_ksPSpace_only updateObject_default_inv | simp)+
  done

lemma setObject_tcb_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF setObject_ksInterrupt])
    apply (simp, rule updateObject_default_inv)
   apply (rule hoare_use_eq [where f=ksMachineState, OF setObject_ksMachine])
    apply (simp, rule updateObject_default_inv)
   apply wp
  apply assumption
  done

lemma getObject_tcb_wp:
  "\<lbrace>\<lambda>s. tcb_at' p s \<longrightarrow> (\<exists>t::tcb. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def objBits_simps' loadObject_default_def
                     projectKOs obj_at'_def in_magnitude_check)

lemma setObject_tcb_pspace_no_overlap':
  "\<lbrace>pspace_no_overlap' w s and tcb_at' t\<rbrace>
  setObject t (tcb::tcb)
  \<lbrace>\<lambda>rv. pspace_no_overlap' w s\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule (1) ps_clear_lookupAround2)
    apply (rule order_refl)
   apply (erule is_aligned_no_overflow)
   apply simp
  apply (clarsimp simp: updateObject_default_def in_monad projectKOs objBits_simps in_magnitude_check)
  apply (fastforce simp: pspace_no_overlap'_def objBits_simps)
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
  apply (clarsimp simp: obj_at'_def projectKOs bspec_split [OF spec [OF x]])
  done

lemmas threadSet_global_refs[wp] =
    threadSet_global_refsT [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_valid_pspace'T_P:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  assumes z: "\<forall>tcb. (P \<longrightarrow> Q (tcbState tcb)) \<longrightarrow>
                     (\<forall>s. valid_tcb_state' (tcbState tcb) s
                              \<longrightarrow> valid_tcb_state' (tcbState (F tcb)) s)"
  assumes v: "\<forall>tcb. (P \<longrightarrow> Q' (tcbBoundNotification tcb)) \<longrightarrow>
                     (\<forall>s. valid_bound_ntfn' (tcbBoundNotification tcb) s
                              \<longrightarrow> valid_bound_ntfn' (tcbBoundNotification (F tcb)) s)"
  assumes p: "\<forall>tcb. (P \<longrightarrow> Q'' (tcbSchedPrev tcb)) \<longrightarrow>
                      (\<forall>s. none_top tcb_at' (tcbSchedPrev tcb) s
                              \<longrightarrow> none_top tcb_at' (tcbSchedPrev (F tcb)) s)"
  assumes n: "\<forall>tcb. (P \<longrightarrow> Q''' (tcbSchedNext tcb)) \<longrightarrow>
                      (\<forall>s. none_top tcb_at' (tcbSchedNext tcb) s
                              \<longrightarrow> none_top tcb_at' (tcbSchedNext (F tcb)) s)"
  assumes y: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
                      \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes u: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes w: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  assumes w': "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  shows
  "\<lbrace>valid_pspace' and (\<lambda>s. P \<longrightarrow> st_tcb_at' Q t s \<and> bound_tcb_at' Q' t s
                                 \<and> obj_at' (\<lambda>tcb. Q'' (tcbSchedPrev tcb)) t s
                                 \<and> obj_at' (\<lambda>tcb. Q''' (tcbSchedNext tcb)) t s)\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def threadSet_def)
  apply (rule hoare_pre,
         wp setObject_tcb_valid_objs getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def
                            bspec_split [OF spec [OF x]] z
                            split_paired_Ball y u w v w' p n)
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
  "{r. (r \<in> tcb_st_refs_of' ts \<or>
       r \<in> tcb_bound_refs' ntfnptr) \<and>
      snd r = TCBBound} =
   tcb_bound_refs' ntfnptr"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def
          split: thread_state.splits)

lemma threadSet_state_refs_of'_helper'[simp]:
  "{r. (r \<in> tcb_st_refs_of' ts \<or>
        r \<in> tcb_bound_refs' ntfnptr) \<and>
       snd r \<noteq> TCBBound} =
   tcb_st_refs_of' ts"
  by (auto simp: tcb_st_refs_of'_def tcb_bound_refs'_def
          split: thread_state.splits)

lemma threadSet_state_refs_of'T_P:
  assumes x: "\<forall>tcb. (P' \<longrightarrow> Q (tcbState tcb)) \<longrightarrow>
                     tcb_st_refs_of' (tcbState (F tcb))
                       = f' (tcb_st_refs_of' (tcbState tcb))"
  assumes y: "\<forall>tcb. (P' \<longrightarrow> Q' (tcbBoundNotification tcb)) \<longrightarrow>
                     tcb_bound_refs' (tcbBoundNotification (F tcb))
                       = g' (tcb_bound_refs' (tcbBoundNotification tcb))"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := f' {r \<in> state_refs_of' s t. snd r \<noteq> TCBBound}
                                  \<union> g' {r \<in> state_refs_of' s t. snd r = TCBBound}))
              \<and> (P' \<longrightarrow> st_tcb_at' Q t s \<and> bound_tcb_at' Q' t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def
                 elim!: rsubst[where P=P] intro!: ext)
  apply (cut_tac s=s and p=t and 'a=tcb in ko_at_state_refs_ofD')
   apply (simp add: obj_at'_def projectKOs)
  apply (clarsimp simp: x y)
  done

lemmas threadSet_state_refs_of'T =
    threadSet_state_refs_of'T_P [where P'=False, simplified]

lemmas threadSet_state_refs_of' =
    threadSet_state_refs_of'T [OF all_tcbI all_tcbI]

lemma threadSet_iflive'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> ((\<exists>tcb. \<not> bound (tcbBoundNotification tcb) \<and> bound (tcbBoundNotification (F tcb))
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. (tcbState tcb = Inactive \<or> tcbState tcb = IdleThreadState)
              \<and> tcbState (F tcb) \<noteq> Inactive
              \<and> tcbState (F tcb) \<noteq> IdleThreadState
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. tcbSchedNext tcb = None \<and> tcbSchedNext (F tcb) \<noteq> None
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. tcbSchedPrev tcb = None \<and> tcbSchedPrev (F tcb) \<noteq> None
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_iflive' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (subst conj_assoc[symmetric], subst imp_disjL[symmetric])+
  apply (rule conjI)
   apply (rule impI, clarsimp)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def)
  apply (clarsimp simp: bspec_split [OF spec [OF x]])
  done

lemmas threadSet_iflive' =
    threadSet_iflive'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_cte_wp_at'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (F tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. P' (cte_wp_at' P p s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P' (cte_wp_at' P p s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (rule bind_wp[where Q'="\<lambda>rv s. P' (cte_wp_at' P p s) \<and> obj_at' ((=) rv) t s"])
   apply (rule setObject_cte_wp_at2')
    apply (clarsimp simp: updateObject_default_def projectKOs in_monad objBits_simps'
                          obj_at'_def in_magnitude_check prod_eq_iff)
    apply (case_tac tcb, clarsimp simp: bspec_split [OF spec [OF x]])
   apply (clarsimp simp: updateObject_default_def in_monad bind_def
                         projectKOs)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas threadSet_cte_wp_at' =
  threadSet_cte_wp_at'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_ctes_ofT:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (F tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (case_tac obj)
  apply (simp add: bspec_split [OF spec [OF x]])
  done

lemmas threadSet_ctes_of =
    threadSet_ctes_ofT [OF all_tcbI, OF ball_tcb_cte_casesI]

lemmas threadSet_cap_to' = ex_nonz_cap_to_pres' [OF threadSet_cte_wp_at']

lemma threadSet_cap_to:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cte_cases. getF (f tcb) = getF tcb)
  \<Longrightarrow> threadSet f tptr \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wpsimp wp: hoare_vcg_ex_lift threadSet_cte_wp_at'
           simp: ex_nonz_cap_to'_def tcb_cte_cases_def objBits_simps')

lemma threadSet_idle'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows
  "\<lbrace>\<lambda>s. valid_idle' s
      \<and> (t = ksIdleThread s \<longrightarrow>
          (\<forall>tcb. ko_at' tcb t s \<and> idle_tcb' tcb \<longrightarrow> idle_tcb' (F tcb)))\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_idle' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs idle_tcb'_def)
  done

lemmas threadSet_idle' =
    threadSet_idle'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma set_tcb_valid_bitmapQ[wp]:
  "\<lbrace> valid_bitmapQ \<rbrace> setObject t (f tcb :: tcb) \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  apply (rule setObject_tcb_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp add: bitmapQ_def)+
  done

lemma set_tcb_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> setObject t (f tcb :: tcb) \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  apply (rule setObject_tcb_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp add: bitmapQ_def)+
  done

lemma set_tcb_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> setObject t (f tcb :: tcb) \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  apply (rule setObject_tcb_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp add: bitmapQ_def)+
  done

lemma threadSet_valid_bitmapQ[wp]:
  "\<lbrace> valid_bitmapQ \<rbrace> threadSet f t \<lbrace> \<lambda>rv. valid_bitmapQ \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def)+

lemma threadSet_valid_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> threadSet f t \<lbrace> \<lambda>rv. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def)+

lemma threadSet_valid_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> threadSet f t \<lbrace> \<lambda>rv. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmapQ_defs threadSet_def
  by (clarsimp simp: setObject_def split_def)
     (wp | simp add: updateObject_default_def)+

lemma threadSet_cur:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. cur_tcb' s\<rbrace>"
  apply (simp add: threadSet_def cur_tcb'_def)
  apply (wp hoare_lift_Pf [OF setObject_tcb_at'] setObject_ct_inv)
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

crunch ksInterrupt'[wp]: threadSet "\<lambda>s. P (ksInterruptState s)"
  (wp: setObject_ksInterrupt updateObject_default_inv)

crunch ksArchState[wp]: threadSet "\<lambda>s. P (ksArchState s)"

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
  apply (wp setObject_tcb_strongest)
   apply (subst simp_thms(32)[symmetric], rule hoare_vcg_disj_lift)
    apply (rule hoare_post_imp [where Q="\<lambda>rv s. \<not> tcb_at' t s \<and> tcb_at' t s"])
     apply simp
    apply (subst simp_thms(21)[symmetric], rule hoare_vcg_conj_lift)
     apply (rule getObject_inv_tcb)
    apply (rule hoare_strengthen_post [OF getObject_ko_at])
      apply simp
     apply (simp add: objBits_simps')
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
  apply rule
  apply (clarsimp simp add: obj_at'_def ko_wp_at'_def projectKOs)
  apply (clarsimp simp add: obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko, simp_all)
  done

(* FIXME: move *)
lemma not_obj_at':
  "(\<not>obj_at' (\<lambda>tcb::tcb. P tcb) t s) = (\<not>typ_at' TCBT t s \<or> obj_at' (Not \<circ> P) t s)"
  apply (simp add: obj_at'_real_def projectKOs
                   typ_at'_def ko_wp_at'_def objBits_simps)
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
    apply (wp hoare_convert_imp)
      apply (simp add: typ_at_tcb' [symmetric])
      apply (wp pos)+
    apply (clarsimp simp: pred_tcb_at'_def not_obj_at' elim!: obj_at'_weakenE)
    done
qed

lemma threadSet_ct[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_ct_inv)
  done

lemma threadSet_cd[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_cd_inv)
  done


lemma threadSet_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_ksDomSchedule_inv)
  done

lemma threadSet_it[wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_it_inv)
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
                in use_valid [OF _ threadSet_nosch], assumption)
  apply (frule_tac P1="(=) (ksCurThread s)"
                in use_valid [OF _ threadSet_ct], rule refl)
  apply (frule_tac P1="(=) (ksCurDomain s)"
                in use_valid [OF _ threadSet_cd], rule refl)
  apply (case_tac "ksSchedulerAction b",
         simp_all add: ct_in_state'_def pred_tcb_at'_def)
   apply (subgoal_tac "t \<noteq> ksCurThread s")
    apply (drule_tac t'1="ksCurThread s"
                 and P1="activatable' \<circ> tcbState"
                  in use_valid [OF _ threadSet_obj_at'_really_strongest])
     apply (clarsimp simp: o_def)
    apply (clarsimp simp: o_def)
   apply (fastforce simp: obj_at'_def projectKOs)
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
  apply (fastforce simp: obj_at'_def projectKOs)
  done

lemma threadSet_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> threadSet F t \<lbrace>\<lambda>_ s. P (ksMachineState s)\<rbrace>"
  apply (simp add: threadSet_def)
  by (wp setObject_ksMachine updateObject_default_inv |
      simp)+

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
     apply (rule updateObject_tcb_inv)
    apply (wps setObject_ct_inv)
    apply (wp setObject_tcb_strongest getObject_tcb_wp)+
  apply (case_tac "t = ksCurThread s")
   apply (clarsimp simp: obj_at'_def)+
  done

lemma threadSet_invs_trivial_helper[simp]:
  "{r \<in> state_refs_of' s t. snd r \<noteq> TCBBound}
   \<union> {r \<in> state_refs_of' s t. snd r = TCBBound} = state_refs_of' s t"
  by auto

lemma threadSet_ct_idle_or_in_cur_domain':
  "(\<And>tcb. tcbDomain (F tcb) = tcbDomain tcb) \<Longrightarrow> \<lbrace>ct_idle_or_in_cur_domain'\<rbrace> threadSet F t \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
      apply (wp hoare_vcg_disj_lift| simp)+
  done

crunch ksDomScheduleIdx[wp]: threadSet "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)
crunch gsUntypedZeroRanges[wp]: threadSet "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)

lemma setObject_tcb_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s) \<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>_ s. P (ksDomScheduleIdx s)\<rbrace>"
  apply (simp add:setObject_def)
  apply (simp add: updateObject_default_def in_monad)
  apply (wp|wpc)+
  apply (simp add: projectKOs)
  done

lemma threadSet_valid_dom_schedule':
  "\<lbrace> valid_dom_schedule'\<rbrace> threadSet F t \<lbrace>\<lambda>_. valid_dom_schedule'\<rbrace>"
  unfolding threadSet_def
  by (wp setObject_ksDomSchedule_inv hoare_Ball_helper)

lemma threadSet_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at' tcb t s \<longrightarrow> P (s\<lparr>ksPSpace := (ksPSpace s)(t \<mapsto> injectKO (f tcb))\<rparr>)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding threadSet_def setObject_def
  apply (wpsimp wp: getObject_tcb_wp simp: updateObject_default_def)
  apply (auto simp: obj_at'_def split: if_splits)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: fun_upd_def)
  apply (prop_tac "\<forall>ptr. psMap (ksPSpace s) ptr = ksPSpace s ptr")
   apply fastforce
  apply metis
  done

lemma threadSet_sched_pointers:
  "\<lbrakk>\<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb; \<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb\<rbrakk>
   \<Longrightarrow> threadSet F tcbPtr \<lbrace>\<lambda>s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp getObject_tcb_wp)
  apply (erule rsubst2[where P=P])
   apply (fastforce simp: opt_map_def obj_at'_def projectKOs)
  apply (fastforce simp: opt_map_def obj_at'_def projectKOs)
  done

lemma threadSet_valid_sched_pointers:
  "\<lbrakk>\<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb; \<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb;
    \<And>tcb. tcbQueued (F tcb) = tcbQueued tcb\<rbrakk>
   \<Longrightarrow> threadSet F tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  unfolding valid_sched_pointers_def
  apply (wpsimp wp: threadSet_wp getObject_tcb_wp)
  by (fastforce simp: opt_pred_def opt_map_def obj_at'_def projectKOs split: option.splits if_splits)

lemma threadSet_tcbSchedNexts_of:
  "(\<And>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb) \<Longrightarrow>
   threadSet F t \<lbrace>\<lambda>s. P (tcbSchedNexts_of s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp getObject_tcb_wp)
  apply (erule rsubst[where P=P])
  apply (fastforce simp: opt_map_def obj_at'_def projectKOs)
  done

lemma threadSet_tcbSchedPrevs_of:
  "(\<And>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb) \<Longrightarrow>
   threadSet F t \<lbrace>\<lambda>s. P (tcbSchedPrevs_of s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp getObject_tcb_wp)
  apply (erule rsubst[where P=P])
  apply (fastforce simp: opt_map_def obj_at'_def projectKOs)
  done

lemma threadSet_tcbQueued:
  "(\<And>tcb. tcbQueued (F tcb) = tcbQueued tcb) \<Longrightarrow>
   threadSet F t \<lbrace>\<lambda>s. P (tcbQueued |< tcbs_of' s)\<rbrace>"
  apply (wpsimp wp: threadSet_wp getObject_tcb_wp)
  apply (erule rsubst[where P=P])
  apply (fastforce simp: opt_pred_def opt_map_def obj_at'_def projectKOs)
  done

crunches threadSet
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReadyQueuesL1Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksReadyQueuesL2Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"

lemma threadSet_invs_trivialT:
  assumes
    "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
    "\<forall>tcb. tcbState (F tcb) = tcbState tcb"
    "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
           \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
    "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
    "\<forall>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb"
    "\<forall>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb"
    "\<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb"
    "\<forall>tcb. tcbDomain (F tcb) = tcbDomain tcb"
    "\<forall>tcb. tcbPriority (F tcb) = tcbPriority tcb"
    "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  shows "threadSet F t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def split del: if_split)
  apply (wp threadSet_valid_pspace'T
            threadSet_sch_actT_P[where P=False, simplified]
            threadSet_state_refs_of'T[where f'=id]
            threadSet_iflive'T
            threadSet_ifunsafe'T
            threadSet_idle'T
            threadSet_global_refsT
            irqs_masked_lift
            valid_irq_node_lift
            valid_irq_handlers_lift'' valid_ioports_lift''
            threadSet_ctes_ofT
            threadSet_not_inQ
            threadSet_ct_idle_or_in_cur_domain'
            threadSet_valid_dom_schedule'
            threadSet_cur
            untyped_ranges_zero_lift
            sym_heap_sched_pointers_lift threadSet_valid_sched_pointers
            threadSet_tcbQueued
            threadSet_tcbSchedPrevs_of threadSet_tcbSchedNexts_of valid_bitmaps_lift
         | clarsimp simp: assms cteCaps_of_def | rule refl)+
  apply (clarsimp simp: o_def)
  by (auto simp: assms obj_at'_def)

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

lemma getObject_tcb_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::tcb. P and ko_at' t r\<rbrace>"
  by (wp getObject_obj_at'; simp)

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
   apply (simp add: projectKOs)
  apply (simp add: valid_obj'_def)
  apply (clarsimp elim!: obj_at'_weakenE)
  done

lemmas typ_at'_valid_tcb'_lift =
  typ_at'_valid_obj'_lift[where obj="KOTCB tcb" for tcb, unfolded valid_obj'_def, simplified]

lemmas setObject_valid_tcb' = typ_at'_valid_tcb'_lift[OF setObject_typ_at']

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
   \<lbrace>\<lambda>_. valid_tcb' tcb\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wpsimp wp: setObject_valid_tcb')
  done

lemma threadSet_valid_tcbs':
  "\<lbrace>valid_tcbs' and (\<lambda>s. \<forall>tcb. valid_tcb' tcb s \<longrightarrow> valid_tcb' (f tcb) s)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. valid_tcbs'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (rule bind_wp[OF _ getObject_tcb_sp])
  apply (wpsimp wp: setObject_tcb_valid_tcbs')
  apply (clarsimp simp: obj_at'_def valid_tcbs'_def projectKOs)
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
    apply (rule corres_guard_imp)
      apply (rule corres_gets_the)
      apply (simp add: threadGet_def)
      apply (rule corres_rel_imp [OF corres_get_tcb])
      apply (simp add: tcb_relation_def arch_tcb_relation_def)
     apply (simp add: tcb_at_def)+
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
        (simp add: tcb_cte_cases_def tcb_cap_cases_def exst_same_def)+)
  have L4: "\<And>con con'. con = con' \<Longrightarrow>
            corres (\<lambda>(irv, nc) (irv', nc'). r irv irv' \<and> nc = nc')
                   \<top> \<top> (select_f (f con)) (select_f (g con'))"
    using y
    by (fastforce simp: corres_underlying_def select_f_def split_def Id_def)
  show ?thesis
  apply (rule corres_cross_over_guard[where Q="tcb_at' t"])
   apply (fastforce elim: tcb_at_cross)
  apply (simp add: as_user_def asUser_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>tcb con. (arch_tcb_context_get o tcb_arch) tcb = con"
           in corres_split)
       apply simp
       apply (rule L1[simplified])
      apply (rule corres_split)
         apply (rule L4; simp)
        apply clarsimp
        apply (rule corres_split_nor)
           apply (simp add: threadSet_def)
           apply (rule corres_symb_exec_r)
              prefer 4
              apply (rule no_fail_pre_and, wp)
             apply (rule L3[simplified])
              apply simp
             apply simp
            apply (wp select_f_inv | simp)+
  done
qed

lemma asUser_corres:
  assumes y: "corres_underlying Id False True r \<top> \<top> f g"
  shows      "corres r (tcb_at t and invs) invs' (as_user t f) (asUser t g)"
  apply (rule corres_guard_imp)
    apply (rule asUser_corres' [OF y])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
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
    apply (simp add: asUser_def split_def threadGet_def threadSet_def
                     liftM_def bind_assoc)
    apply (clarsimp simp: valid_def in_monad getObject_def setObject_def
                          loadObject_default_def projectKOs objBits_simps'
                          modify_def split_def updateObject_default_def
                          in_magnitude_check select_f_def
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
  by (wp asUser_inv)

lemma asUser_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> asUser t' f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: asUser_def bind_assoc split_def, wp select_f_inv)

lemmas asUser_typ_ats[wp] = typ_at_lifts [OF asUser_typ_at']

lemma asUser_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> asUser t m \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  apply (wp threadSet_invs_trivial hoare_drop_imps | simp)+
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
             | simp add: valid_tcb'_def tcb_cte_cases_def)+
  done

lemma asUser_valid_pspace'[wp]:
  "\<lbrace>valid_pspace'\<rbrace> asUser t m \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_valid_pspace' hoare_drop_imps | simp)+
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
  apply (wp threadSet_state_refs_of' hoare_drop_imps | simp)+
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
  (simp: crunch_simps wp: hoare_drop_imps getObject_inv_tcb setObject_ct_inv)

lemma asUser_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> asUser t m \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
  apply (wp | wpc | simp)+
     apply (rule_tac f="ksCurDomain" in hoare_lift_Pf)
      apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | simp)+
  apply (clarsimp simp: obj_at'_def)
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
    apply (wpsimp wp: hoare_drop_imps no_fail_threadGet)+
  done

lemma asUser_setRegister_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct)
             \<top>
             (as_user t (setRegister r v))
             (asUser t (setRegister r v))"
  apply (simp add: setRegister_def)
  apply (rule asUser_corres')
  apply (rule corres_modify'; simp)
  done

lemma getThreadState_corres:
  "corres thread_state_relation (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (get_thread_state t) (getThreadState t)"
  apply (simp add: get_thread_state_def getThreadState_def)
  apply (rule threadGet_corres)
  apply (simp add: tcb_relation_def)
  done

lemma gts_wf'[wp]: "\<lbrace>tcb_at' t and invs'\<rbrace> getThreadState t \<lbrace>valid_tcb_state'\<rbrace>"
  apply (simp add: getThreadState_def threadGet_def liftM_def)
  apply (wp getObject_tcb_wp)
  apply clarsimp
  apply (drule obj_at_ko_at', clarsimp)
  apply (frule ko_at_valid_objs', fastforce, simp add: projectKOs)
  apply (fastforce simp: valid_obj'_def valid_tcb'_def)
  done

lemma gts_st_tcb_at'[wp]: "\<lbrace>st_tcb_at' P t\<rbrace> getThreadState t \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: getThreadState_def threadGet_def liftM_def)
  apply wp
   apply (rule hoare_chain)
     apply (rule obj_at_getObject)
     apply (clarsimp simp: loadObject_default_def projectKOs in_monad)
    apply assumption
   apply simp
  apply (simp add: pred_tcb_at'_def)
  done

lemma gts_inv'[wp]: "\<lbrace>P\<rbrace> getThreadState t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getThreadState_def) wp

lemma getBoundNotification_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (get_bound_notification t) (getBoundNotification t)"
  apply (simp add: get_bound_notification_def getBoundNotification_def)
  apply (rule threadGet_corres)
  apply (simp add: tcb_relation_def)
  done

lemma gbn_bound_tcb_at'[wp]: "\<lbrace>bound_tcb_at' P t\<rbrace> getBoundNotification t \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: getBoundNotification_def threadGet_def liftM_def)
  apply wp
   apply (rule hoare_strengthen_post)
    apply (rule obj_at_getObject)
    apply (clarsimp simp: loadObject_default_def projectKOs in_monad)
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
  apply (simp add: isRunnable_def isStopped_def2 liftM_def)
  apply (rule bind_eqI, rule ext, rule arg_cong)
  apply (case_tac state)
  apply (clarsimp)+
  done

lemma isStopped_inv[wp]:
  "\<lbrace>P\<rbrace> isStopped t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: isStopped_def2 | wp gts_inv')+

lemma isRunnable_inv[wp]:
  "\<lbrace>P\<rbrace> isRunnable t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: isRunnable_def2 | wp gts_inv')+

lemma isRunnable_wp[wp]:
  "\<lbrace>\<lambda>s. Q (st_tcb_at' (runnable') t s) s\<rbrace> isRunnable t \<lbrace>Q\<rbrace>"
  apply (simp add: isRunnable_def2)
  apply (wpsimp simp: getThreadState_def threadGet_def wp: getObject_tcb_wp)
  apply (clarsimp simp: getObject_def valid_def in_monad st_tcb_at'_def
                        loadObject_default_def projectKOs obj_at'_def
                        split_def objBits_simps in_magnitude_check)
  done

lemma setQueue_obj_at[wp]:
  "\<lbrace>obj_at' P t\<rbrace> setQueue d p q \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
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
  by (simp add: threadGet_def o_def | wp getObject_obj_at_tcb)+

lemma fun_if_triv[simp]:
  "(\<lambda>x. if x = y then f y else f x) = f"
  by (force)

lemma corres_get_etcb:
  "corres (etcb_relation) (is_etcb_at t) (tcb_at' t)
                    (gets_the (get_etcb t)) (getObject t)"
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp add: get_etcb_def gets_the_def gets_def
                            get_def assert_opt_def bind_def
                            return_def fail_def
                            split: option.splits
                            )
  apply (frule in_inv_by_hoareD [OF getObject_inv_tcb])
  apply (clarsimp simp add: is_etcb_at_def obj_at'_def projectKO_def
                            projectKO_opt_tcb split_def
                            getObject_def loadObject_default_def in_monad)
  apply (case_tac bb)
        apply (simp_all add: fail_def return_def)
  apply (clarsimp simp add: state_relation_def ekheap_relation_def)
  apply (drule bspec)
   apply clarsimp
   apply blast
  apply (clarsimp simp add: other_obj_relation_def lookupAround2_known1)
  done


lemma ethreadget_corres:
  assumes x: "\<And>etcb tcb'. etcb_relation etcb tcb' \<Longrightarrow> r (f etcb) (f' tcb')"
  shows      "corres r (is_etcb_at t) (tcb_at' t) (ethread_get f t) (threadGet f' t)"
  apply (simp add: ethread_get_def threadGet_def)
  apply (fold liftM_def)
  apply simp
  apply (rule corres_rel_imp)
   apply (rule corres_get_etcb)
  apply (simp add: x)
  done

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
  "corres dc \<top> \<top> (return ()) (if tcbQueueEmpty queue then addToBitmap d p else return ())"
  by (cases "tcbQueueHead queue", simp_all add: addToBitmap_noop_corres)

lemma removeFromBitmap_corres_noop:
  "corres dc \<top> \<top> (return ()) (removeFromBitmap tdom prioa)"
  unfolding removeFromBitmap_def
  by (rule corres_noop)
     (wp | simp add: bitmap_fun_defs state_relation_def | rule no_fail_pre)+

crunch typ_at'[wp]: addToBitmap "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps setCTE_typ_at')

crunch typ_at'[wp]: removeFromBitmap "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps setCTE_typ_at')

lemmas addToBitmap_typ_ats [wp] = typ_at_lifts [OF addToBitmap_typ_at']
lemmas removeFromBitmap_typ_ats [wp] = typ_at_lifts [OF removeFromBitmap_typ_at']

lemma ekheap_relation_tcb_domain_priority:
  "\<lbrakk>ekheap_relation (ekheap s) (ksPSpace s'); ekheap s t = Some (tcb);
    ksPSpace s' t = Some (KOTCB tcb')\<rbrakk>
   \<Longrightarrow> tcbDomain tcb' = tcb_domain tcb \<and> tcbPriority tcb' = tcb_priority tcb"
  apply (clarsimp simp: ekheap_relation_def)
  apply (drule_tac x=t in bspec, blast)
  apply (clarsimp simp: other_obj_relation_def etcb_relation_def)
  done

lemma no_fail_thread_get[wp]:
  "no_fail (tcb_at tcb_ptr) (thread_get f tcb_ptr)"
  unfolding thread_get_def
  apply wpsimp
  apply (clarsimp simp: tcb_at_def)
  done

lemma pspace_relation_tcb_relation:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); kheap s ptr = Some (TCB tcb);
    ksPSpace s' ptr = Some (KOTCB tcb')\<rbrakk>
   \<Longrightarrow> tcb_relation tcb tcb'"
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=ptr in bspec)
   apply (fastforce simp: obj_at_def)
  apply (clarsimp simp: tcb_relation_cut_def obj_at_def obj_at'_def)
  done

lemma pspace_relation_update_concrete_tcb:
  "\<lbrakk>pspace_relation s s'; s ptr = Some (TCB tcb); s' ptr = Some (KOTCB otcb');
    tcb_relation tcb tcb'\<rbrakk>
   \<Longrightarrow> pspace_relation s (s'(ptr \<mapsto> KOTCB tcb'))"
  by (fastforce dest: pspace_relation_update_tcbs simp: map_upd_triv)

lemma threadSet_pspace_relation:
  fixes s :: det_state
  assumes tcb_rel: "(\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> tcb_relation tcb (F tcb'))"
  shows "threadSet F tcbPtr \<lbrace>\<lambda>s'. pspace_relation (kheap s) (ksPSpace s')\<rbrace>"
  supply fun_upd_apply[simp del]
  unfolding threadSet_def setObject_def updateObject_default_def
  apply (wpsimp wp: getObject_tcb_wp simp: updateObject_default_def)
  apply normalise_obj_at'
  apply (frule tcb_at'_cross)
   apply (fastforce simp: obj_at'_def)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
  apply (rule pspace_relation_update_concrete_tcb)
     apply fastforce
    apply fastforce
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (frule (1) pspace_relation_tcb_relation)
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (fastforce dest!: tcb_rel)
  done

lemma ekheap_relation_update_tcbs:
  "\<lbrakk> ekheap_relation (ekheap s) (ksPSpace s'); ekheap s x = Some oetcb;
     ksPSpace s' x = Some (KOTCB otcb'); etcb_relation etcb tcb' \<rbrakk>
   \<Longrightarrow> ekheap_relation ((ekheap s)(x \<mapsto> etcb)) ((ksPSpace s')(x \<mapsto> KOTCB tcb'))"
  by (simp add: ekheap_relation_def)

lemma ekheap_relation_update_concrete_tcb:
  "\<lbrakk>ekheap_relation (ekheap s) (ksPSpace s'); ekheap s ptr = Some etcb;
    ksPSpace s' ptr = Some (KOTCB otcb');
    etcb_relation etcb tcb'\<rbrakk>
   \<Longrightarrow> ekheap_relation (ekheap s) ((ksPSpace s')(ptr \<mapsto> KOTCB tcb'))"
  by (fastforce dest: ekheap_relation_update_tcbs simp: map_upd_triv)

lemma ekheap_relation_etcb_relation:
  "\<lbrakk>ekheap_relation (ekheap s) (ksPSpace s'); ekheap s ptr = Some etcb;
    ksPSpace s' ptr = Some (KOTCB tcb')\<rbrakk>
   \<Longrightarrow> etcb_relation etcb tcb'"
  apply (clarsimp simp: ekheap_relation_def)
  apply (drule_tac x=ptr in bspec)
   apply (fastforce simp: obj_at_def)
  apply (clarsimp simp: obj_at_def obj_at'_def)
  done

lemma threadSet_ekheap_relation:
  fixes s :: det_state
  assumes etcb_rel: "(\<And>etcb tcb'. etcb_relation etcb tcb' \<Longrightarrow> etcb_relation etcb (F tcb'))"
  shows
    "\<lbrace>\<lambda>s'. ekheap_relation (ekheap s) (ksPSpace s') \<and> pspace_relation (kheap s) (ksPSpace s')
           \<and> valid_etcbs s\<rbrace>
     threadSet F tcbPtr
     \<lbrace>\<lambda>_ s'. ekheap_relation (ekheap s) (ksPSpace s')\<rbrace>"
  supply fun_upd_apply[simp del]
  unfolding threadSet_def setObject_def updateObject_default_def
  apply (wpsimp wp: getObject_tcb_wp simp: updateObject_default_def)
  apply (frule tcb_at'_cross)
   apply (fastforce simp: obj_at'_def)
  apply normalise_obj_at'
  apply (frule (1) tcb_at_is_etcb_at)
  apply (clarsimp simp: obj_at_def is_tcb_def is_etcb_at_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
  apply (rule ekheap_relation_update_concrete_tcb)
     apply fastforce
    apply fastforce
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (frule (1) ekheap_relation_etcb_relation)
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (fastforce dest!: etcb_rel)
  done

lemma tcbQueued_update_pspace_relation[wp]:
  fixes s :: det_state
  shows "threadSet (tcbQueued_update f) tcbPtr \<lbrace>\<lambda>s'. pspace_relation (kheap s) (ksPSpace s')\<rbrace>"
  by (wpsimp wp: threadSet_pspace_relation simp: tcb_relation_def)

lemma tcbQueued_update_ekheap_relation[wp]:
  fixes s :: det_state
  shows
    "\<lbrace>\<lambda>s'. ekheap_relation (ekheap s) (ksPSpace s') \<and> pspace_relation (kheap s) (ksPSpace s')
           \<and> valid_etcbs s\<rbrace>
     threadSet (tcbQueued_update f) tcbPtr
     \<lbrace>\<lambda>_ s'. ekheap_relation (ekheap s) (ksPSpace s')\<rbrace>"
  by (wpsimp wp: threadSet_ekheap_relation simp: etcb_relation_def)

lemma tcbQueueRemove_pspace_relation[wp]:
  fixes s :: det_state
  shows "tcbQueueRemove queue tcbPtr \<lbrace>\<lambda>s'. pspace_relation (kheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueueRemove_def
  by (wpsimp wp: threadSet_pspace_relation hoare_drop_imps simp: tcb_relation_def)

lemma tcbQueueRemove_ekheap_relation[wp]:
  fixes s :: det_state
  shows
    "\<lbrace>\<lambda>s'. ekheap_relation (ekheap s) (ksPSpace s') \<and> pspace_relation (kheap s) (ksPSpace s')
           \<and> valid_etcbs s\<rbrace>
     tcbQueueRemove queue tcbPtr
     \<lbrace>\<lambda>_ s'. ekheap_relation (ekheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueueRemove_def
  by (wpsimp wp: threadSet_ekheap_relation threadSet_pspace_relation hoare_drop_imps
           simp: tcb_relation_def etcb_relation_def)

lemma threadSet_ghost_relation[wp]:
  "threadSet f tcbPtr \<lbrace>\<lambda>s'. ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')\<rbrace>"
  unfolding threadSet_def setObject_def updateObject_default_def
  apply (wpsimp wp: getObject_tcb_wp simp: updateObject_default_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma removeFromBitmap_ghost_relation[wp]:
  "removeFromBitmap tdom prio \<lbrace>\<lambda>s'. ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')\<rbrace>"
  by (rule_tac f=gsUserPages in hoare_lift_Pf2; wpsimp simp: bitmap_fun_defs)

lemma tcbQueued_update_ctes_of[wp]:
  "threadSet (tcbQueued_update f) t \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_of)

lemma removeFromBitmap_ctes_of[wp]:
  "removeFromBitmap tdom prio \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp simp: bitmap_fun_defs)

crunches tcbQueueRemove, tcbQueuePrepend, tcbQueueAppend, tcbQueueInsert,
         setQueue, removeFromBitmap
  for ghost_relation_projs[wp]: "\<lambda>s. P (gsUserPages s) (gsCNodes s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"
  and ksWorkUnitsCompleted[wp]: "\<lambda>s. P (ksWorkUnitsCompleted s)"
  and ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
  (wp: crunch_wps getObject_tcb_wp simp: setObject_def updateObject_default_def obj_at'_def)

crunches tcbQueueRemove, tcbQueuePrepend, tcbQueueAppend, tcbQueueInsert,
         setQueue, removeFromBitmap
  for tcb_at'[wp]: "\<lambda>s. tcb_at' tcbPtr s"
  (wp: crunch_wps ignore: threadSet)

lemma set_tcb_queue_projs:
  "set_tcb_queue d p queue
   \<lbrace>\<lambda>s. P (kheap s) (cdt s) (is_original_cap s) (cur_thread s) (idle_thread s) (scheduler_action s)
          (domain_list s) (domain_index s) (cur_domain s) (domain_time s) (machine_state s)
          (interrupt_irq_node s) (interrupt_states s) (arch_state s) (caps_of_state s)
          (work_units_completed s) (cdt_list s) (ekheap s)\<rbrace>"
  by (wpsimp simp: set_tcb_queue_def)

lemma set_tcb_queue_cte_at:
  "set_tcb_queue d p queue \<lbrace>\<lambda>s. P (swp cte_at s)\<rbrace>"
  unfolding set_tcb_queue_def
  apply wpsimp
  apply (clarsimp simp: swp_def cte_wp_at_def)
  done

lemma set_tcb_queue_projs_inv:
  "fst (set_tcb_queue d p queue s) = {(r, s')} \<Longrightarrow>
   kheap s = kheap s'
   \<and> ekheap s = ekheap s'
   \<and> cdt s = cdt s'
   \<and> is_original_cap s = is_original_cap s'
   \<and> cur_thread s = cur_thread s'
   \<and> idle_thread s = idle_thread s'
   \<and> scheduler_action s = scheduler_action s'
   \<and> domain_list s = domain_list s'
   \<and> domain_index s = domain_index s'
   \<and> cur_domain s = cur_domain s'
   \<and> domain_time s = domain_time s'
   \<and> machine_state s = machine_state s'
   \<and> interrupt_irq_node s = interrupt_irq_node s'
   \<and> interrupt_states s = interrupt_states s'
   \<and> arch_state s = arch_state s'
   \<and> caps_of_state s = caps_of_state s'
   \<and> work_units_completed s = work_units_completed s'
   \<and> cdt_list s = cdt_list s'
   \<and> swp cte_at s = swp cte_at s'"
  apply (drule singleton_eqD)
  by (auto elim!: use_valid_inv[where E=\<top>, simplified]
           intro: set_tcb_queue_projs set_tcb_queue_cte_at)

lemma set_tcb_queue_new_state:
  "(rv, t) \<in> fst (set_tcb_queue d p queue s)  \<Longrightarrow>
   t = s\<lparr>ready_queues := \<lambda>dom prio. if dom = d \<and> prio = p then queue else ready_queues s dom prio\<rparr>"
  by (clarsimp simp: set_tcb_queue_def in_monad)

lemma tcbQueuePrepend_pspace_relation[wp]:
  fixes s :: det_state
  shows "tcbQueuePrepend queue tcbPtr \<lbrace>\<lambda>s'. pspace_relation (kheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: threadSet_pspace_relation simp: tcb_relation_def)

lemma tcbQueuePrepend_ekheap_relation[wp]:
  fixes s :: det_state
  shows
    "\<lbrace>\<lambda>s'. ekheap_relation (ekheap s) (ksPSpace s') \<and> pspace_relation (kheap s) (ksPSpace s')
           \<and> valid_etcbs s\<rbrace>
     tcbQueuePrepend queue tcbPtr
     \<lbrace>\<lambda>_ s'. ekheap_relation (ekheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: threadSet_pspace_relation threadSet_ekheap_relation
           simp: tcb_relation_def etcb_relation_def)

lemma tcbQueueAppend_pspace_relation[wp]:
  fixes s :: det_state
  shows "tcbQueueAppend queue tcbPtr \<lbrace>\<lambda>s'. pspace_relation (kheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueueAppend_def
  by (wpsimp wp: threadSet_pspace_relation simp: tcb_relation_def)

lemma tcbQueueAppend_ekheap_relation[wp]:
  fixes s :: det_state
  shows
    "\<lbrace>\<lambda>s'. ekheap_relation (ekheap s) (ksPSpace s') \<and> pspace_relation (kheap s) (ksPSpace s')
           \<and> valid_etcbs s\<rbrace>
     tcbQueueAppend queue tcbPtr
     \<lbrace>\<lambda>_ s'. ekheap_relation (ekheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueueAppend_def
  by (wpsimp wp: threadSet_pspace_relation threadSet_ekheap_relation
           simp: tcb_relation_def etcb_relation_def)

lemma tcbQueueInsert_pspace_relation[wp]:
  fixes s :: det_state
  shows "tcbQueueInsert tcbPtr afterPtr \<lbrace>\<lambda>s'. pspace_relation (kheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueueInsert_def
  by (wpsimp wp: threadSet_pspace_relation hoare_drop_imps simp: tcb_relation_def)

lemma tcbQueueInsert_ekheap_relation[wp]:
  fixes s :: det_state
  shows
    "\<lbrace>\<lambda>s'. ekheap_relation (ekheap s) (ksPSpace s') \<and> pspace_relation (kheap s) (ksPSpace s')
           \<and> valid_etcbs s\<rbrace>
     tcbQueueInsert tcbPtr afterPtr
     \<lbrace>\<lambda>_ s'. ekheap_relation (ekheap s) (ksPSpace s')\<rbrace>"
  unfolding tcbQueueInsert_def
  by (wpsimp wp: threadSet_pspace_relation threadSet_ekheap_relation hoare_drop_imps
           simp: tcb_relation_def etcb_relation_def)

lemma removeFromBitmap_pspace_relation[wp]:
  fixes s :: det_state
  shows "removeFromBitmap tdom prio \<lbrace>\<lambda>s'. pspace_relation (kheap s) (ksPSpace s')\<rbrace>"
  unfolding bitmap_fun_defs
  by wpsimp

crunches setQueue, removeFromBitmap
  for valid_pspace'[wp]: valid_pspace'
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
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
  and cur_tcb'[wp]: cur_tcb'
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"
  (wp: crunch_wps
   simp: crunch_simps tcb_cte_cases_def tcb_bound_refs'_def cur_tcb'_def threadSet_cur
         bitmap_fun_defs valid_machine_state'_def)

crunches tcbSchedEnqueue, tcbSchedAppend, tcbSchedDequeue, setQueue
  for pspace_aligned'[wp]: pspace_aligned'
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and pspace_distinct'[wp]: pspace_distinct'
  and pspace_canonical'[wp]: pspace_canonical'
  and no_0_obj'[wp]: no_0_obj'
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and valid_global_refs'[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  and irq_node[wp]: "\<lambda>s. P (irq_node' s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at' T p s)"
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
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps threadSet_state_refs_of'[where f'=id and g'=id]
   simp: crunch_simps tcb_cte_cases_def tcb_bound_refs'_def bitmap_fun_defs)

lemma threadSet_ready_queues_relation:
  "(\<And>tcb. tcbQueued (F tcb) = tcbQueued tcb) \<Longrightarrow>
   \<lbrace>\<lambda>s'. ready_queues_relation s s' \<and> \<not> (tcbQueued |< tcbs_of' s') tcbPtr\<rbrace>
   threadSet F tcbPtr
   \<lbrace>\<lambda>_ s'. ready_queues_relation s s'\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: list_queue_relation_def obj_at'_def projectKOs)
  apply (rename_tac tcb' d p)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply (clarsimp simp: list_queue_relation_def)
  apply (rule conjI)
   apply (drule_tac x=tcbPtr in spec)
   apply (fastforce intro: heap_path_heap_upd_not_in
                     simp: inQ_def opt_map_def opt_pred_def obj_at'_def)
  apply (rule conjI)
   apply (drule_tac x=tcbPtr in spec)
   apply (clarsimp simp: prev_queue_head_def)
   apply (prop_tac "ready_queues s d p \<noteq> []", fastforce)
   apply (fastforce dest: heap_path_head simp: inQ_def opt_pred_def opt_map_def fun_upd_apply)
  apply (auto simp: inQ_def opt_pred_def opt_map_def fun_upd_apply projectKOs split: option.splits)
  done

definition in_correct_ready_q_2 where
  "in_correct_ready_q_2 queues ekh \<equiv>
     \<forall>d p. \<forall>t \<in> set (queues d p). is_etcb_at' t ekh
                                  \<and> etcb_at' (\<lambda>t. tcb_priority t = p \<and> tcb_domain t = d) t ekh"

abbreviation in_correct_ready_q :: "det_ext state \<Rightarrow> bool" where
  "in_correct_ready_q s \<equiv> in_correct_ready_q_2 (ready_queues s) (ekheap s)"

lemmas in_correct_ready_q_def = in_correct_ready_q_2_def

lemma in_correct_ready_q_lift:
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  assumes r: "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  shows "f \<lbrace>in_correct_ready_q\<rbrace>"
  apply (rule hoare_pre)
   apply (wps assms | wpsimp)+
  done

definition ready_qs_distinct :: "det_ext state \<Rightarrow> bool" where
  "ready_qs_distinct s \<equiv> \<forall>d p. distinct (ready_queues s d p)"

lemma ready_qs_distinct_lift:
  assumes r: "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  shows "f \<lbrace>ready_qs_distinct\<rbrace>"
  unfolding ready_qs_distinct_def
  apply (rule hoare_pre)
   apply (wps assms | wpsimp)+
  done

lemma ready_queues_disjoint:
  "\<lbrakk>in_correct_ready_q s; ready_qs_distinct s; d \<noteq> d' \<or> p \<noteq> p'\<rbrakk>
   \<Longrightarrow> set (ready_queues s d p) \<inter> set (ready_queues s d' p') = {}"
  apply (clarsimp simp: ready_qs_distinct_def in_correct_ready_q_def)
  apply (rule disjointI)
  apply (frule_tac x=d in spec)
  apply (drule_tac x=d' in spec)
  apply (fastforce simp: etcb_at_def is_etcb_at_def split: option.splits)
  done

lemma isRunnable_sp:
  "\<lbrace>P\<rbrace>
   isRunnable tcb_ptr
   \<lbrace>\<lambda>rv s. \<exists>tcb'. ko_at' tcb' tcb_ptr s
                  \<and> (rv = (tcbState tcb' = Running \<or> tcbState tcb' = Restart))
           \<and> P s\<rbrace>"
  unfolding isRunnable_def getThreadState_def
  apply (wpsimp wp: hoare_case_option_wp getObject_tcb_wp simp: threadGet_def)
  apply (fastforce simp: obj_at'_def split: Structures_H.thread_state.splits)
  done

crunch (no_fail) no_fail[wp]: isRunnable

defs ksReadyQueues_asrt_def:
  "ksReadyQueues_asrt
     \<equiv> \<lambda>s'. \<forall>d p. \<exists>ts. ready_queue_relation d p ts (ksReadyQueues s' (d, p))
                                            (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
                                            (inQ d p |< tcbs_of' s')"

lemma ksReadyQueues_asrt_cross:
  "ready_queues_relation s s' \<Longrightarrow> ksReadyQueues_asrt s'"
  by (fastforce simp: ready_queues_relation_def Let_def ksReadyQueues_asrt_def)

crunches addToBitmap
  for ko_at'[wp]: "\<lambda>s. P (ko_at' ko ptr s)"
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReadyQueues_asrt[wp]: ksReadyQueues_asrt
  and st_tcb_at'[wp]: "\<lambda>s. P (st_tcb_at' Q tcbPtr s)"
  and valid_tcbs'[wp]: valid_tcbs'
  (simp: bitmap_fun_defs ksReadyQueues_asrt_def)

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

lemma tcbQueueHead_iff_tcbQueueEnd:
  "list_queue_relation ts q nexts prevs \<Longrightarrow> tcbQueueHead q \<noteq> None \<longleftrightarrow> tcbQueueEnd q \<noteq> None"
  apply (clarsimp simp: list_queue_relation_def queue_end_valid_def)
  using heap_path_None
  apply fastforce
  done

lemma tcbQueueEnd_ksReadyQueues:
  "\<lbrakk>list_queue_relation ts queue nexts prevs;
    \<forall>t. (inQ d p |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty queue \<longrightarrow> (inQ d p |< tcbs_of' s') (the (tcbQueueEnd queue))"
  apply (frule tcbQueueHead_iff_tcbQueueEnd)
  by (clarsimp simp: tcbQueueEmpty_def list_queue_relation_def queue_end_valid_def)

lemma obj_at'_tcbQueueEnd_ksReadyQueues:
  "\<lbrakk>list_queue_relation ts queue nexts prevs;
    \<forall>t. (inQ d p |< tcbs_of' s') t \<longleftrightarrow> t \<in> set ts;
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty queue \<longrightarrow> obj_at' (inQ d p) (the (tcbQueueEnd queue)) s'"
  by (fastforce dest!: tcbQueueEnd_ksReadyQueues intro: aligned'_distinct'_ko_wp_at'I
                 simp: obj_at'_real_def opt_map_def opt_pred_def split: option.splits)

lemma thread_get_exs_valid[wp]:
  "tcb_at tcb_ptr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> thread_get f tcb_ptr \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (clarsimp simp: thread_get_def get_tcb_def gets_the_def gets_def return_def get_def
                     exs_valid_def tcb_at_def bind_def)

lemma ethread_get_sp:
  "\<lbrace>P\<rbrace> ethread_get f ptr
   \<lbrace>\<lambda>rv. etcb_at (\<lambda>tcb. f tcb = rv) ptr and P\<rbrace>"
  apply wpsimp
  apply (clarsimp simp: etcb_at_def split: option.splits)
  done

lemma ethread_get_exs_valid[wp]:
  "\<lbrakk>tcb_at tcb_ptr s; valid_etcbs s\<rbrakk> \<Longrightarrow> \<lbrace>(=) s\<rbrace> ethread_get f tcb_ptr \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  apply (frule (1) tcb_at_is_etcb_at)
  apply (clarsimp simp: ethread_get_def get_etcb_def gets_the_def gets_def return_def get_def
                        is_etcb_at_def exs_valid_def bind_def)
  done

lemma no_fail_ethread_get[wp]:
  "no_fail (tcb_at tcb_ptr and valid_etcbs) (ethread_get f tcb_ptr)"
  unfolding ethread_get_def
  apply wpsimp
  apply (frule (1) tcb_at_is_etcb_at)
  apply (clarsimp simp: is_etcb_at_def get_etcb_def)
  done

lemma threadGet_sp:
  "\<lbrace>P\<rbrace> threadGet f ptr \<lbrace>\<lambda>rv s. \<exists>tcb :: tcb. ko_at' tcb ptr s \<and> f tcb = rv \<and> P s\<rbrace>"
  unfolding threadGet_def setObject_def
  apply (wpsimp wp: getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma in_set_ready_queues_inQ_eq:
  "ready_queues_relation s s' \<Longrightarrow> t \<in> set (ready_queues s d p) \<longleftrightarrow> (inQ d p |< tcbs_of' s') t"
  by (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)

lemma in_ready_q_tcbQueued_eq:
  "ready_queues_relation s s'
   \<Longrightarrow> (\<exists>d p. t \<in> set (ready_queues s d p))  \<longleftrightarrow> (tcbQueued |< tcbs_of' s') t"
  apply (intro iffI)
   apply clarsimp
   apply (frule in_set_ready_queues_inQ_eq)
   apply (fastforce simp: inQ_def opt_map_def opt_pred_def split: option.splits)
  apply (fastforce simp: ready_queues_relation_def ready_queue_relation_def Let_def inQ_def
                         opt_pred_def
                  split: option.splits)
  done

lemma tcbSchedEnqueue_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (in_correct_ready_q and ready_qs_distinct and valid_etcbs and st_tcb_at runnable tcb_ptr
      and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_sched_pointers and valid_tcbs')
     (tcb_sched_action tcb_sched_enqueue tcb_ptr) (tcbSchedEnqueue tcbPtr)"
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
  apply (clarsimp simp: tcb_sched_action_def tcb_sched_enqueue_def get_tcb_queue_def
                        tcbSchedEnqueue_def getQueue_def unless_def when_def)
  apply (rule corres_symb_exec_l[OF _ _ ethread_get_sp]; (solves wpsimp)?)
  apply (rename_tac domain)
  apply (rule corres_symb_exec_l[OF _ _ ethread_get_sp]; (solves wpsimp)?)
  apply (rename_tac priority)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (subst if_distrib[where f="set_tcb_queue domain prio" for domain prio])
  apply (rule corres_if_strong')
    apply (frule state_relation_ready_queues_relation)
    apply (frule in_ready_q_tcbQueued_eq[where t=tcbPtr])
    subgoal
      by (fastforce dest: tcb_at_ekheap_dom pred_tcb_at_tcb_at
                    simp: obj_at'_def opt_pred_def opt_map_def obj_at_def is_tcb_def
                          in_correct_ready_q_def etcb_at_def is_etcb_at_def projectKOs)
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
   apply (wpsimp simp: tcbQueuePrepend_def wp: hoare_vcg_if_lift2 | drule Some_to_the)+
   apply (clarsimp simp: ex_abs_underlying_def split: if_splits)
   apply (frule state_relation_ready_queues_relation)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (drule_tac x="tcbDomain tcb" in spec)
   apply (drule_tac x="tcbPriority tcb" in spec)
   subgoal by (force dest!: obj_at'_tcbQueueHead_ksReadyQueues simp: obj_at'_def projectKOs)

  apply (rename_tac s rv t)
  apply (clarsimp simp: state_relation_def)
  apply (intro hoare_vcg_conj_lift_pre_fix;
         (solves \<open>frule singleton_eqD, frule set_tcb_queue_projs_inv, wpsimp simp: swp_def\<close>)?)

  \<comment> \<open>ready_queues_relation\<close>
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (intro hoare_allI)
  apply (drule singleton_eqD)
  apply (drule set_tcb_queue_new_state)
  apply (wpsimp wp: threadSet_wp getObject_tcb_wp simp: setQueue_def tcbQueuePrepend_def)
  apply normalise_obj_at'
  apply (frule (1) tcb_at_is_etcb_at)
  apply (clarsimp simp: obj_at_def is_etcb_at_def etcb_at_def)
  apply (rename_tac s d p s' tcb' tcb etcb)
  apply (frule_tac t=tcbPtr in ekheap_relation_tcb_domain_priority)
    apply (force simp: obj_at_def)
   apply (force simp: obj_at'_def projectKOs)
  apply (clarsimp split: if_splits)
  apply (cut_tac ts="ready_queues s d p" in list_queue_relation_nil)
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (cut_tac ts="ready_queues s (tcb_domain etcb) (tcb_priority etcb)"
              in list_queue_relation_nil)
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (cut_tac ts="ready_queues s (tcb_domain etcb) (tcb_priority etcb)" and s'=s'
              in obj_at'_tcbQueueEnd_ksReadyQueues)
      apply fast
     apply auto[1]
    apply fastforce
   apply fastforce
  apply (cut_tac xs="ready_queues s d p" and st="tcbQueueHead (ksReadyQueues s' (d, p))"
              in heap_path_head')
   apply (auto dest: spec simp: list_queue_relation_def tcbQueueEmpty_def)[1]
  apply (cut_tac xs="ready_queues s (tcb_domain etcb) (tcb_priority etcb)"
             and st="tcbQueueHead (ksReadyQueues s' (tcb_domain etcb, tcb_priority etcb))"
              in heap_path_head')
   apply (auto dest: spec simp: list_queue_relation_def tcbQueueEmpty_def)[1]
  apply (clarsimp simp: list_queue_relation_def)

  apply (case_tac "\<not> (d = tcb_domain etcb \<and> p = tcb_priority etcb)")
   apply (cut_tac d=d and d'="tcb_domain etcb" and p=p and p'="tcb_priority etcb"
               in ready_queues_disjoint)
      apply force
     apply fastforce
    apply fastforce
   apply (prop_tac "tcbPtr \<notin> set (ready_queues s d p)")
    apply (clarsimp simp: obj_at'_def opt_pred_def opt_map_def)
    apply (metis inQ_def option.simps(5) tcb_of'_TCB projectKO_eq)
   apply (intro conjI impI; simp)

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
   apply (clarsimp simp: etcb_at_def obj_at'_def)
   apply (prop_tac "the (tcbQueueHead (ksReadyQueues s' (tcb_domain etcb, tcb_priority etcb)))
                    \<notin> set (ready_queues s d p)")
    apply (erule orthD2)
    apply (clarsimp simp: tcbQueueEmpty_def)
   apply (intro conjI impI allI)
        apply (intro heap_path_heap_upd_not_in)
          apply (clarsimp simp: fun_upd_apply split: if_splits)
         apply simp
        apply fastforce
       apply (clarsimp simp: queue_end_valid_def fun_upd_apply split: if_splits)
      apply (intro prev_queue_head_heap_upd)
        apply (force simp: fun_upd_apply split: if_splits)
       apply (case_tac "ready_queues s d p";
              force simp: fun_upd_apply tcbQueueEmpty_def split: if_splits)
      apply (clarsimp simp: fun_upd_apply inQ_def split: if_splits)
      apply (case_tac "ready_queues s d p"; force simp: tcbQueueEmpty_def)
     apply (case_tac "t = tcbPtr")
      apply (clarsimp simp: inQ_def fun_upd_apply obj_at'_def projectKOs split: if_splits)
     apply (case_tac "t = the (tcbQueueHead (ksReadyQueues s' (tcb_domain etcb, tcb_priority etcb)))")
      apply (clarsimp simp: inQ_def opt_pred_def opt_map_def obj_at'_def fun_upd_apply projectKOs
                     split: option.splits)
      apply metis
     apply (clarsimp simp: inQ_def in_opt_pred opt_map_def fun_upd_apply)
    apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (clarsimp simp: fun_upd_apply split: if_splits)

  \<comment> \<open>d = tcb_domain etcb \<and> p = tcb_priority etcb\<close>
  apply clarsimp
  apply (drule_tac x="tcb_domain etcb" in spec)
  apply (drule_tac x="tcb_priority etcb" in spec)
  apply (cut_tac ts="ready_queues s (tcb_domain etcb) (tcb_priority etcb)"
              in tcbQueueHead_iff_tcbQueueEnd)
   apply (force simp: list_queue_relation_def)
  apply (frule valid_tcbs'_maxDomain[where t=tcbPtr], simp add: obj_at'_def projectKOs)
  apply (frule valid_tcbs'_maxPriority[where t=tcbPtr], simp add: obj_at'_def projectKOs)
  apply (drule valid_sched_pointersD[where t=tcbPtr])
    apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def projectKOs)
   apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def projectKOs)
  apply (intro conjI; clarsimp simp: tcbQueueEmpty_def)

   \<comment> \<open>the ready queue was originally empty\<close>
   apply (force simp: inQ_def in_opt_pred fun_upd_apply queue_end_valid_def prev_queue_head_def
                      opt_map_red obj_at'_def
               split: if_splits)

  \<comment> \<open>the ready queue was not originally empty\<close>
  apply (drule (2) heap_ls_prepend[where new=tcbPtr])
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply)
  apply (rule conjI)
   apply (subst opt_map_upd_triv)
    apply (clarsimp simp: opt_map_def obj_at'_def fun_upd_apply split: if_splits)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply queue_end_valid_def)
  apply (rule conjI)
   apply (clarsimp simp: prev_queue_head_def fun_upd_apply opt_map_def split: if_splits)
  by (auto dest!: hd_in_set simp: inQ_def in_opt_pred opt_map_def fun_upd_apply projectKOs
           split: if_splits option.splits)

definition
  weak_sch_act_wf :: "scheduler_action \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "weak_sch_act_wf sa = (\<lambda>s. \<forall>t. sa = SwitchToThread t \<longrightarrow> st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s)"

lemma weak_sch_act_wf_updateDomainTime[simp]:
  "weak_sch_act_wf m (ksDomainTime_update f s) = weak_sch_act_wf m s"
  by (simp add:weak_sch_act_wf_def tcb_in_cur_domain'_def )

lemma setSchedulerAction_corres:
  "sched_act_relation sa sa'
    \<Longrightarrow> corres dc \<top> \<top> (set_scheduler_action sa) (setSchedulerAction sa')"
  apply (simp add: setSchedulerAction_def set_scheduler_action_def)
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp: in_monad simpler_modify_def state_relation_def)
  done

lemma getSchedulerAction_corres:
  "corres sched_act_relation \<top> \<top> (gets scheduler_action) getSchedulerAction"
  apply (simp add: getSchedulerAction_def)
  apply (clarsimp simp: state_relation_def)
  done

lemma rescheduleRequired_corres:
  "corres dc
     (weak_valid_sched_action and in_correct_ready_q and ready_qs_distinct and valid_etcbs
      and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_sched_pointers and valid_tcbs'
      and pspace_aligned' and pspace_distinct')
     (reschedule_required) rescheduleRequired"
  apply (simp add: rescheduleRequired_def reschedule_required_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getSchedulerAction_corres])
      apply (rule_tac P="case action of switch_thread t \<Rightarrow> P t | _ \<Rightarrow> \<top>"
                  and P'="case actiona of SwitchToThread t \<Rightarrow> P' t | _ \<Rightarrow> \<top>" for P P'
              in corres_split[where r'=dc])
         apply (case_tac action)
           apply simp
          apply simp
          apply (rule tcbSchedEnqueue_corres, simp)
         apply simp
        apply (rule setSchedulerAction_corres)
        apply simp
       apply (wp | wpc | simp)+
   apply (force dest: st_tcb_weakenE simp: in_monad weak_valid_sched_action_def valid_etcbs_def
               split: Deterministic_A.scheduler_action.split)
  apply simp
  apply (clarsimp simp: weak_sch_act_wf_def pred_tcb_at' split: scheduler_action.splits)
  done

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
  = weak_sch_act_wf_lift[OF threadSet_nosch threadSet_pred_tcb_no_state threadSet_tcbDomain_triv, simplified]

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

crunch st_tcb_at'[wp]: removeFromBitmap "st_tcb_at' P t"
crunch pred_tcb_at'[wp]: removeFromBitmap "\<lambda>s. Q (pred_tcb_at' proj P t s)"

crunch pred_tcb_at'[wp]: addToBitmap "\<lambda>s. Q (pred_tcb_at' proj P t s)"

crunch obj_at'[wp]: removeFromBitmap "\<lambda>s. Q (obj_at' P t s)"

crunch obj_at'[wp]: addToBitmap "\<lambda>s. Q (obj_at' P t s)"

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
  "tcbSchedDequeue tcbPtr \<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: tcbSchedDequeue_def tcbQueueRemove_def)
  apply (wp threadSet_weak_sch_act_wf getObject_tcb_wp removeFromBitmap_weak_sch_act_wf
         | simp add: crunch_simps threadGet_def)+
  apply (clarsimp simp: obj_at'_def)
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

lemma tcbQueueRemove_no_fail:
  "no_fail (\<lambda>s. tcb_at' tcbPtr s
                \<and> (\<exists>ts. list_queue_relation ts queue (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                        \<and> tcbPtr \<in> set ts)
                \<and> sym_heap_sched_pointers s \<and> valid_objs' s)
           (tcbQueueRemove queue tcbPtr)"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getObject_tcb_wp)
  apply normalise_obj_at'
  apply (frule (1) ko_at_valid_objs')
   apply (fastforce simp: projectKOs)
  apply (clarsimp simp: list_queue_relation_def)
  apply (prop_tac "tcbQueueHead queue \<noteq> Some tcbPtr \<longrightarrow> tcbSchedPrevs_of s tcbPtr \<noteq> None")
   apply (rule impI)
   apply (frule not_head_prev_not_None[where p=tcbPtr])
      apply (fastforce simp: inQ_def opt_pred_def opt_map_def obj_at'_def)
     apply (fastforce dest: heap_path_head)
    apply fastforce
   apply (fastforce simp: opt_map_def obj_at'_def valid_tcb'_def valid_bound_tcb'_def)
  by (fastforce dest!: not_last_next_not_None[where p=tcbPtr]
                 simp: queue_end_valid_def opt_map_def obj_at'_def valid_obj'_def valid_tcb'_def
                       projectKOs)

crunch (no_fail) no_fail[wp]: removeFromBitmap

crunches removeFromBitmap
  for ready_queues_relation[wp]: "ready_queues_relation s"
  and list_queue_relation[wp]:
   "\<lambda>s'. list_queue_relation ts (P (ksReadyQueues s'))
                             (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
  (simp: bitmap_fun_defs ready_queues_relation_def)

\<comment> \<open>
  A direct analogue of tcbQueueRemove, used in tcb_sched_dequeue' below, so that within the proof of
  tcbQueueRemove_corres, we may reason in terms of the list operations used within this function
  rather than @{term filter}.\<close>
definition tcb_queue_remove :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "tcb_queue_remove a ls \<equiv>
     if ls = [a]
     then []
     else if a = hd ls
          then tl ls
          else if a = last ls
               then butlast ls
               else list_remove ls a"

definition tcb_sched_dequeue' :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "tcb_sched_dequeue' tcb_ptr \<equiv> do
     d \<leftarrow> ethread_get tcb_domain tcb_ptr;
     prio \<leftarrow> ethread_get tcb_priority tcb_ptr;
     queue \<leftarrow> get_tcb_queue d prio;
     when (tcb_ptr \<in> set queue) $ set_tcb_queue d prio (tcb_queue_remove tcb_ptr queue)
   od"

lemma filter_tcb_queue_remove:
  "\<lbrakk>a \<in> set ls; distinct ls \<rbrakk> \<Longrightarrow> filter ((\<noteq>) a) ls = tcb_queue_remove a ls"
  apply (clarsimp simp: tcb_queue_remove_def)
  apply (intro conjI impI)
     apply (fastforce elim: filter_hd_equals_tl)
    apply (fastforce elim: filter_last_equals_butlast)
   apply (fastforce elim: filter_hd_equals_tl)
  apply (frule split_list)
  apply (clarsimp simp: list_remove_middle_distinct)
  apply (subst filter_True | clarsimp simp: list_remove_none)+
  done

lemma tcb_sched_dequeue_monadic_rewrite:
  "monadic_rewrite False True (is_etcb_at t and (\<lambda>s. \<forall>d p. distinct (ready_queues s d p)))
     (tcb_sched_action tcb_sched_dequeue t) (tcb_sched_dequeue' t)"
  supply if_split[split del]
  apply (clarsimp simp: tcb_sched_dequeue'_def tcb_sched_dequeue_def tcb_sched_action_def
                        set_tcb_queue_def)
  apply (rule monadic_rewrite_bind_tail)+
     apply (clarsimp simp: when_def)
     apply (rule monadic_rewrite_if_r)
      apply (rule_tac P="\<lambda>_. distinct queue" in monadic_rewrite_guard_arg_cong)
      apply (frule (1) filter_tcb_queue_remove)
      apply (metis (mono_tags, lifting) filter_cong)
     apply (rule monadic_rewrite_modify_noop)
    apply (wpsimp wp: thread_get_wp)+
  apply (clarsimp simp: etcb_at_def split: option.splits)
  apply (prop_tac "(\<lambda>d' p. if d' = tcb_domain x2 \<and> p = tcb_priority x2
                           then filter (\<lambda>x. x \<noteq> t) (ready_queues s (tcb_domain x2) (tcb_priority x2))
                           else ready_queues s d' p)
                   = ready_queues s")
   apply (subst filter_True)
    apply fastforce
   apply (fastforce split: if_splits)
  apply fastforce
  done

crunches removeFromBitmap
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"

lemma list_queue_relation_neighbour_in_set:
  "\<lbrakk>list_queue_relation ls q hp hp'; sym_heap hp hp'; p \<in> set ls\<rbrakk>
   \<Longrightarrow> \<forall>nbr. (hp p = Some nbr \<longrightarrow> nbr \<in> set ls) \<and> (hp' p = Some nbr \<longrightarrow> nbr \<in> set ls)"
  apply (rule heap_ls_neighbour_in_set)
     apply (fastforce simp: list_queue_relation_def)
    apply fastforce
   apply (clarsimp simp: list_queue_relation_def prev_queue_head_def)
  apply fastforce
  done

lemma in_queue_not_head_or_not_tail_length_gt_1:
  "\<lbrakk>tcbPtr \<in> set ls; tcbQueueHead q \<noteq> Some tcbPtr \<or> tcbQueueEnd q \<noteq> Some tcbPtr;
    list_queue_relation ls q nexts prevs\<rbrakk>
   \<Longrightarrow> Suc 0 < length ls"
  apply (clarsimp simp: list_queue_relation_def)
  apply (cases ls; fastforce simp: queue_end_valid_def)
  done

lemma tcbSchedDequeue_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (in_correct_ready_q and ready_qs_distinct and valid_etcbs and tcb_at tcb_ptr
      and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_objs')
     (tcb_sched_action tcb_sched_dequeue tcb_ptr) (tcbSchedDequeue tcbPtr)"
  supply heap_path_append[simp del] fun_upd_apply[simp del] distinct_append[simp del]
         list_remove_append[simp del] projectKOs[simp]
  apply (rule_tac Q'="tcb_at' tcbPtr" in corres_cross_add_guard)
   apply (fastforce intro!: tcb_at_cross simp: obj_at_def is_tcb_def)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (rule monadic_rewrite_corres_l[where P=P and Q=P for P, simplified])
   apply (rule monadic_rewrite_guard_imp[OF tcb_sched_dequeue_monadic_rewrite])
   apply (fastforce dest: tcb_at_is_etcb_at simp: in_correct_ready_q_def ready_qs_distinct_def)
  apply (clarsimp simp: tcb_sched_dequeue'_def get_tcb_queue_def tcbSchedDequeue_def  getQueue_def
                        unless_def when_def)
  apply (rule corres_symb_exec_l[OF _ _ ethread_get_sp]; wpsimp?)
  apply (rename_tac dom)
  apply (rule corres_symb_exec_l[OF _ _ ethread_get_sp]; wpsimp?)
  apply (rename_tac prio)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule corres_if_strong'; fastforce?)
    apply (frule state_relation_ready_queues_relation)
    apply (frule in_ready_q_tcbQueued_eq[where t=tcbPtr])
    apply (fastforce simp: obj_at'_def opt_pred_def opt_map_def obj_at_def is_tcb_def
                           in_correct_ready_q_def etcb_at_def is_etcb_at_def)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; wpsimp?)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; wpsimp?)
  apply (rule corres_symb_exec_r[OF _ gets_sp]; wpsimp?)
  apply (rule corres_from_valid_det)
    apply (fastforce intro: det_wp_modify det_wp_pre simp: set_tcb_queue_def)
   apply (wpsimp wp: tcbQueueRemove_no_fail)
   apply (fastforce dest: state_relation_ready_queues_relation
                    simp: ex_abs_underlying_def ready_queues_relation_def ready_queue_relation_def
                          Let_def inQ_def opt_pred_def opt_map_def obj_at'_def)
  apply (clarsimp simp: state_relation_def)
  apply (intro hoare_vcg_conj_lift_pre_fix;
         (solves \<open>frule singleton_eqD, frule set_tcb_queue_projs_inv, wpsimp simp: swp_def\<close>)?)

  \<comment> \<open>ready_queues_relation\<close>
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (intro hoare_allI)
  apply (drule singleton_eqD)
  apply (drule set_tcb_queue_new_state)
  apply (wpsimp wp: threadSet_wp getObject_tcb_wp
              simp: setQueue_def tcbQueueRemove_def
         split_del: if_split)
  apply (frule (1) tcb_at_is_etcb_at)
  apply (clarsimp simp: obj_at_def is_etcb_at_def etcb_at_def)
  apply normalise_obj_at'
  apply (rename_tac s d p s' tcb' tcb etcb)
  apply (frule_tac t=tcbPtr in ekheap_relation_tcb_domain_priority)
    apply (force simp: obj_at_def)
   apply (force simp: obj_at'_def)

  apply (case_tac "d \<noteq> tcb_domain etcb \<or> p \<noteq> tcb_priority etcb")
   apply clarsimp
   apply (cut_tac p=tcbPtr and ls="ready_queues s (tcb_domain etcb) (tcb_priority etcb)"
               in list_queue_relation_neighbour_in_set)
      apply (fastforce dest!: spec)
     apply fastforce
    apply fastforce
   apply (cut_tac xs="ready_queues s d p" in heap_path_head')
    apply (force dest!: spec simp: ready_queues_relation_def Let_def list_queue_relation_def)
   apply (cut_tac d=d and d'="tcb_domain etcb" and p=p and p'="tcb_priority etcb"
               in ready_queues_disjoint)
      apply force
     apply fastforce
    apply fastforce
   apply (cut_tac ts="ready_queues s d p" in list_queue_relation_nil)
    apply fast
   apply (clarsimp simp: tcbQueueEmpty_def)
   apply (prop_tac "Some tcbPtr \<noteq> tcbQueueHead (ksReadyQueues s' (d, p))")
    apply (metis hd_in_set not_emptyI option.sel option.simps(2))
   apply (prop_tac "tcbPtr \<notin> set (ready_queues s d p)")
    apply blast
   apply (clarsimp simp: list_queue_relation_def)
   apply (intro conjI; clarsimp)

    \<comment> \<open>the ready queue is the singleton consisting of tcbPtr\<close>
    apply (intro conjI)
         apply (force intro!: heap_path_heap_upd_not_in simp: fun_upd_apply)
        apply (clarsimp simp: queue_end_valid_def fun_upd_apply)
       apply (force simp: prev_queue_head_heap_upd fun_upd_apply)
      apply (clarsimp simp: inQ_def in_opt_pred fun_upd_apply)
     apply (clarsimp simp: fun_upd_apply)
    apply (clarsimp simp: fun_upd_apply)

   apply (clarsimp simp: etcb_at_def obj_at'_def)
   apply (intro conjI; clarsimp)

    \<comment> \<open>tcbPtr is the head of the ready queue\<close>
    apply (intro conjI)
         apply (intro heap_path_heap_upd_not_in)
           apply (force simp: fun_upd_apply)
          apply (force simp: not_emptyI opt_map_red)
         apply assumption
        apply (clarsimp simp: queue_end_valid_def fun_upd_apply)
       apply (clarsimp simp: prev_queue_head_def fun_upd_apply)
      apply (clarsimp simp: inQ_def opt_pred_def opt_map_def fun_upd_apply split: option.splits)
     apply (clarsimp simp: fun_upd_apply)
    apply (clarsimp simp: fun_upd_apply)
   apply (intro conjI; clarsimp)

    \<comment> \<open>tcbPtr is the end of the ready queue\<close>
    apply (intro conjI)
         apply (intro heap_path_heap_upd_not_in)
           apply (simp add: fun_upd_apply split: if_splits)
          apply (force simp: not_emptyI opt_map_red)
         apply (clarsimp simp: inQ_def opt_pred_def opt_map_def fun_upd_apply split: option.splits)
        apply (clarsimp simp: queue_end_valid_def fun_upd_apply)
       apply (force simp: prev_queue_head_def fun_upd_apply opt_map_red opt_map_upd_triv)
      apply (clarsimp simp: inQ_def opt_pred_def opt_map_def fun_upd_apply split: option.splits)
     apply (clarsimp simp: fun_upd_apply)
    apply (clarsimp simp: fun_upd_apply)

   \<comment> \<open>tcbPtr is in the middle of the ready queue\<close>
   apply (intro conjI)
     apply (intro heap_path_heap_upd_not_in)
        apply (simp add: fun_upd_apply)
       apply (force simp: not_emptyI opt_map_red)
      apply (force simp: not_emptyI opt_map_red)
     apply fastforce
    apply (clarsimp simp: opt_map_red opt_map_upd_triv)
    apply (intro prev_queue_head_heap_upd)
      apply (force dest!: spec)
     apply (metis hd_in_set not_emptyI option.sel option.simps(2))
    apply fastforce
   subgoal
     by (clarsimp simp: inQ_def opt_map_def opt_pred_def fun_upd_apply
                 split: if_splits option.splits)

  \<comment> \<open>d = tcb_domain tcb \<and> p = tcb_priority tcb\<close>
  apply clarsimp
  apply (drule_tac x="tcb_domain etcb" in spec)
  apply (drule_tac x="tcb_priority etcb" in spec)
  apply (clarsimp simp: list_queue_relation_def)
  apply (frule heap_path_head')
  apply (frule heap_ls_distinct)
  apply (intro conjI; clarsimp simp: tcbQueueEmpty_def)

   \<comment> \<open>the ready queue is the singleton consisting of tcbPtr\<close>
   apply (intro conjI)
      apply (simp add: fun_upd_apply tcb_queue_remove_def queue_end_valid_def heap_ls_unique
                       heap_path_last_end)
     apply (simp add: fun_upd_apply tcb_queue_remove_def queue_end_valid_def heap_ls_unique
                      heap_path_last_end)
    apply (simp add: fun_upd_apply prev_queue_head_def)
   apply (case_tac "ready_queues s (tcb_domain etcb) (tcb_priority etcb)";
          clarsimp simp: tcb_queue_remove_def inQ_def opt_pred_def fun_upd_apply)
  apply (intro conjI; clarsimp)

   \<comment> \<open>tcbPtr is the head of the ready queue\<close>
   apply (frule set_list_mem_nonempty)
   apply (frule in_queue_not_head_or_not_tail_length_gt_1)
     apply fastforce
    apply (fastforce simp: list_queue_relation_def)
   apply (frule list_not_head)
   apply (clarsimp simp: tcb_queue_remove_def)
   apply (frule length_tail_nonempty)
   apply (frule (2) heap_ls_next_of_hd)
   apply (clarsimp simp: obj_at'_def)
   apply (intro conjI impI allI)
      apply (drule (1) heap_ls_remove_head_not_singleton)
      apply (clarsimp simp: opt_map_red opt_map_upd_triv fun_upd_apply)
     apply (clarsimp simp: queue_end_valid_def fun_upd_apply last_tl)
    apply (clarsimp simp: prev_queue_head_def fun_upd_apply)
   apply (case_tac "ready_queues s (tcb_domain etcb) (tcb_priority etcb)";
          clarsimp simp: inQ_def opt_pred_def opt_map_def fun_upd_apply split: option.splits)
  apply (intro conjI; clarsimp)

   \<comment> \<open>tcbPtr is the end of the ready queue\<close>
   apply (frule set_list_mem_nonempty)
   apply (frule in_queue_not_head_or_not_tail_length_gt_1)
     apply fast
    apply (force dest!: spec simp: list_queue_relation_def)
   apply (clarsimp simp: queue_end_valid_def)
   apply (frule list_not_last)
   apply (clarsimp simp: tcb_queue_remove_def)
   apply (frule length_gt_1_imp_butlast_nonempty)
   apply (frule (3) heap_ls_prev_of_last)
   apply (clarsimp simp: obj_at'_def)
   apply (intro conjI impI; clarsimp?)
      apply (drule (1) heap_ls_remove_last_not_singleton)
      apply (force elim!: rsubst3[where P=heap_ls] simp: opt_map_def fun_upd_apply)
     apply (clarsimp simp: opt_map_def fun_upd_apply)
    apply (clarsimp simp: prev_queue_head_def fun_upd_apply opt_map_def)
   apply (clarsimp simp: inQ_def opt_pred_def opt_map_def fun_upd_apply split: option.splits)
   apply (meson distinct_in_butlast_not_last in_set_butlastD last_in_set not_last_in_set_butlast)

  \<comment> \<open>tcbPtr is in the middle of the ready queue\<close>
  apply (clarsimp simp: obj_at'_def)
  apply (frule set_list_mem_nonempty)
  apply (frule split_list)
  apply clarsimp
  apply (rename_tac xs ys)
  apply (prop_tac "xs \<noteq> [] \<and> ys \<noteq> []", fastforce simp: queue_end_valid_def)
  apply clarsimp
  apply (frule (2) ptr_in_middle_prev_next)
   apply fastforce
  apply (clarsimp simp: tcb_queue_remove_def)
  apply (prop_tac "tcbPtr \<noteq> last xs")
   apply (clarsimp simp: distinct_append)
  apply (prop_tac "tcbPtr \<noteq> hd ys")
   apply (fastforce dest: hd_in_set simp: distinct_append)
  apply (prop_tac "last xs \<noteq> hd ys")
   apply (metis distinct_decompose2 hd_Cons_tl last_in_set)
  apply (prop_tac "list_remove (xs @ tcbPtr # ys) tcbPtr = xs @ ys")
   apply (simp add: list_remove_middle_distinct)
  apply (intro conjI impI allI; (solves \<open>clarsimp simp: distinct_append\<close>)?)
     apply (fastforce elim!: rsubst3[where P=heap_ls]
                      dest!: heap_ls_remove_middle hd_in_set last_in_set
                       simp: distinct_append not_emptyI opt_map_def fun_upd_apply)
    apply (clarsimp simp: queue_end_valid_def fun_upd_apply)
   apply (case_tac xs;
          fastforce simp: prev_queue_head_def opt_map_def fun_upd_apply distinct_append)
  apply (clarsimp simp: inQ_def opt_pred_def opt_map_def fun_upd_apply distinct_append
                 split: option.splits)
  done

lemma thread_get_test: "do cur_ts \<leftarrow> get_thread_state cur; g (test cur_ts) od =
       do t \<leftarrow> (thread_get (\<lambda>tcb. test (tcb_state tcb)) cur); g t od"
  apply (simp add: get_thread_state_def thread_get_def)
  done

lemma thread_get_isRunnable_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (thread_get (\<lambda>tcb. runnable (tcb_state tcb)) t) (isRunnable t)"
  apply (simp add:  isRunnable_def getThreadState_def threadGet_def
                   thread_get_def)
  apply (fold liftM_def)
  apply simp
  apply (rule corres_rel_imp)
   apply (rule getObject_TCB_corres)
  apply (clarsimp simp add: tcb_relation_def thread_state_relation_def)
  apply (case_tac "tcb_state x",simp_all)
  done

lemma setThreadState_corres:
  "thread_state_relation ts ts' \<Longrightarrow>
   corres dc
          (tcb_at t and pspace_aligned and pspace_distinct)
          \<top>
          (set_thread_state t ts) (setThreadState ts' t)"
  (is "?tsr \<Longrightarrow> corres dc ?Pre ?Pre' ?sts ?sts'")
  apply (simp add: set_thread_state_def setThreadState_def)
  apply (simp add: set_thread_state_ext_def[abs_def])
  apply (subst bind_assoc[symmetric], subst thread_set_def[simplified, symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'=dc])
       apply (rule threadset_corres, (simp add: tcb_relation_def exst_same_def)+)
      apply (subst thread_get_test[where test="runnable"])
      apply (rule corres_split[OF thread_get_isRunnable_corres])
        apply (rule corres_split[OF getCurThread_corres])
          apply (rule corres_split[OF getSchedulerAction_corres])
            apply (simp only: when_def)
            apply (rule corres_if[where Q=\<top> and Q'=\<top>])
              apply (rule iffI)
               apply clarsimp+
              apply (case_tac rva,simp_all)[1]
             apply (wp rescheduleRequired_corres_simple corres_return_trivial | simp)+
    apply (wp hoare_vcg_conj_lift[where Q'="\<top>\<top>"] | simp add: sch_act_simple_def)+
  done

lemma setBoundNotification_corres:
  "corres dc
          (tcb_at t and pspace_aligned and pspace_distinct)
          \<top>
          (set_bound_notification t ntfn) (setBoundNotification ntfn t)"
  apply (simp add: set_bound_notification_def setBoundNotification_def)
  apply (subst thread_set_def[simplified, symmetric])
  apply (rule threadset_corres, simp_all add:tcb_relation_def exst_same_def)
  done

crunches rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for tcb'[wp]: "tcb_at' addr"

lemma tcbSchedNext_update_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_bound_tcb' ptrOpt\<rbrace>
   threadSet (tcbSchedNext_update (\<lambda>_. ptrOpt)) tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbSchedPrev_update_valid_objs'[wp]:
  "\<lbrace>valid_objs' and valid_bound_tcb' ptrOpt\<rbrace>
   threadSet (tcbSchedPrev_update (\<lambda>_. ptrOpt)) tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp wp: threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma tcbQueuePrepend_valid_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> tcb_at' tcbPtr s
        \<and> (\<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueHead queue)) s)\<rbrace>
   tcbQueuePrepend queue tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift' simp: tcbQueueEmpty_def)

crunches addToBitmap
  for valid_objs'[wp]: valid_objs'
  (simp: unless_def crunch_simps wp: crunch_wps)

lemma tcbSchedEnqueue_valid_objs'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbSchedEnqueue_def setQueue_def
  apply (wpsimp wp: threadSet_valid_objs' getObject_tcb_wp simp: threadGet_def)
  apply (fastforce dest!: obj_at'_tcbQueueHead_ksReadyQueues
                    simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def)
  done

crunches rescheduleRequired, removeFromBitmap
  for valid_objs'[wp]: valid_objs'
  (simp: crunch_simps)

lemmas ko_at_valid_objs'_pre =
  ko_at_valid_objs'[simplified project_inject, atomized, simplified, rule_format]

lemmas ep_ko_at_valid_objs_valid_ep' =
  ko_at_valid_objs'_pre[where 'a=endpoint, simplified injectKO_defs valid_obj'_def, simplified]

lemmas ntfn_ko_at_valid_objs_valid_ntfn' =
  ko_at_valid_objs'_pre[where 'a=notification, simplified injectKO_defs valid_obj'_def,
                        simplified]

lemmas tcb_ko_at_valid_objs_valid_tcb' =
  ko_at_valid_objs'_pre[where 'a=tcb, simplified injectKO_defs valid_obj'_def, simplified]

lemma tcbQueueRemove_valid_objs'[wp]:
  "tcbQueueRemove queue tcbPtr \<lbrace>valid_objs'\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getObject_tcb_wp)
  apply normalise_obj_at'
  apply (fastforce dest!: tcb_ko_at_valid_objs_valid_tcb'
                    simp: valid_tcb'_def valid_bound_tcb'_def obj_at'_def)
  done

lemma tcbSchedDequeue_valid_objs'[wp]:
  "tcbSchedDequeue t \<lbrace>valid_objs'\<rbrace>"
  unfolding tcbSchedDequeue_def setQueue_def
  by (wpsimp wp: threadSet_valid_objs')

lemma sts_valid_objs':
  "\<lbrace>valid_objs' and valid_tcb_state' st and pspace_aligned' and pspace_distinct'\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: setThreadState_def wp: threadSet_valid_objs')
   apply (rule_tac Q="\<lambda>_. valid_objs' and pspace_aligned' and pspace_distinct'" in hoare_post_imp)
    apply fastforce
   apply (wpsimp wp: threadSet_valid_objs')
  apply (simp add: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemma sbn_valid_objs':
  "\<lbrace>valid_objs' and valid_bound_ntfn' ntfn\<rbrace>
  setBoundNotification ntfn t
  \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_objs')
     apply (simp add: valid_tcb'_def tcb_cte_cases_def)
  done

lemma ssa_wp[wp]:
  "\<lbrace>\<lambda>s. P (s \<lparr>ksSchedulerAction := sa\<rparr>)\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: setSchedulerAction_def)

crunches rescheduleRequired, tcbSchedDequeue
  for aligned'[wp]: "pspace_aligned'"
  and distinct'[wp]: "pspace_distinct'"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"

crunches rescheduleRequired, tcbSchedDequeue
  for no_0_obj'[wp]: "no_0_obj'"
  and pspace_canonical'[wp]: "pspace_canonical'"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'

lemma sts'_valid_pspace'_inv[wp]:
  "\<lbrace> valid_pspace' and tcb_at' t and valid_tcb_state' st \<rbrace>
  setThreadState st t
  \<lbrace> \<lambda>rv. valid_pspace' \<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sts_valid_objs')
   apply (simp add: setThreadState_def threadSet_def
                    setQueue_def bind_assoc valid_mdb'_def)
   apply (wp getObject_obj_at_tcb | simp)+
  apply (clarsimp simp: valid_mdb'_def)
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply (simp add: tcb_cte_cases_def)
  done

lemma setQueue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setQueue d p xs \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  apply (simp add: setQueue_def tcb_in_cur_domain'_def)
  apply wp
  apply (simp add: ps_clear_def projectKOs obj_at'_def)
  done

lemma sbn'_valid_pspace'_inv[wp]:
  "\<lbrace> valid_pspace' and tcb_at' t and valid_bound_ntfn' ntfn \<rbrace>
  setBoundNotification ntfn t
  \<lbrace> \<lambda>rv. valid_pspace' \<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sbn_valid_objs')
   apply (simp add: setBoundNotification_def threadSet_def bind_assoc valid_mdb'_def)
   apply (wp getObject_obj_at_tcb | simp)+
  apply (clarsimp simp: valid_mdb'_def)
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply (simp add: tcb_cte_cases_def)
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
                in use_valid [OF _ threadSet_nosch],
         rule refl)
  apply (frule_tac P1="(=) (ksCurThread s)"
                in use_valid [OF _ threadSet_ct],
         rule refl)
  apply (frule_tac P1="(=) (ksCurDomain s)"
                in use_valid [OF _ threadSet_cd],
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
    apply (clarsimp elim!: obj_at'_weakenE, clarsimp simp: obj_at'_def projectKOs)
  apply (simp add: tcb_in_cur_domain'_def)
  apply (frule_tac t'1=word
               and P1="\<lambda>tcb. ksCurDomain b = tcbDomain tcb"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
   apply (clarsimp simp: o_def tcb_in_cur_domain'_def)
  apply clarsimp
  done

lemma threadSet_pred_tcb_at_state:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (if p = t
        then obj_at' (\<lambda>tcb. P (proj (tcb_to_itcb' (f tcb)))) t s
        else pred_tcb_at' proj P p s)\<rbrace>
  threadSet f t \<lbrace>\<lambda>_. pred_tcb_at' proj P p\<rbrace>"
  apply (rule hoare_chain)
    apply (rule threadSet_obj_at'_really_strongest)
   prefer 2
   apply (simp add: pred_tcb_at'_def)
  apply (clarsimp split: if_splits simp: pred_tcb_at'_def o_def)
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

lemma rescheduleRequired_sch_act'[wp]:
  "\<lbrace>\<top>\<rbrace>
      rescheduleRequired
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp)+
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
  including classic_wp_pre
  apply (simp add: sch_act_wf_cases
              split: scheduler_action.split)
  apply (wp hoare_vcg_conj_lift)
   apply (simp add: threadSet_def)
   apply (wp hoare_weak_lift_imp)
    apply (wps setObject_sa_unchanged)
    apply (wp hoare_weak_lift_imp getObject_tcb_wp)+
   apply (clarsimp simp: obj_at'_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_conj_lift hoare_convert_imp)+
   apply (simp add: threadSet_def)
   apply (wp getObject_tcb_wp)
   apply (clarsimp simp: obj_at'_def)
  apply (wp tcb_in_cur_domain'_lift | simp add: obj_at'_def)+
  done

lemma tcbSchedNext_update_pred_tcb_at'[wp]:
  "threadSet (tcbSchedNext_update f) t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+

lemma tcbSchedPrev_update_pred_tcb_at'[wp]:
  "threadSet (tcbSchedPrev_update f) t \<lbrace>\<lambda>s. P (pred_tcb_at' proj P' t' s)\<rbrace>"
  by (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+

lemma tcbSchedEnqueue_pred_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. pred_tcb_at' proj P' t' s \<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. pred_tcb_at' proj P' t' s\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def tcbQueuePrepend_def when_def unless_def)
  apply (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+
  done

lemma tcbSchedDequeue_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding tcbSchedDequeue_def tcbQueueRemove_def
  by (wp setQueue_sch_act threadSet_tcbDomain_triv hoare_drop_imps
      | wp sch_act_wf_lift | simp add: if_apply_def2)+

crunch nosch: tcbSchedDequeue "\<lambda>s. P (ksSchedulerAction s)"

lemma sts_sch_act':
  "\<lbrace>\<lambda>s. (\<not> runnable' st \<longrightarrow> sch_act_not t s) \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
  setThreadState st t  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp | simp)+
   prefer 2
   apply assumption
  apply (case_tac "runnable' st")
   apply ((wp threadSet_runnable_sch_act hoare_drop_imps | simp)+)[1]
  apply (rule_tac Q="\<lambda>rv s. st_tcb_at' (Not \<circ> runnable') t s \<and>
                     (ksCurThread s \<noteq> t \<or> ksSchedulerAction s \<noteq> ResumeCurrentThread \<longrightarrow>
                            sch_act_wf (ksSchedulerAction s) s)"
               in hoare_post_imp)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  apply (simp only: imp_conv_disj)
  apply (wp threadSet_pred_tcb_at_state threadSet_sch_act_wf
            hoare_vcg_disj_lift|simp)+
  done

lemma sts_sch_act[wp]:
  "\<lbrace>\<lambda>s. (\<not> runnable' st \<longrightarrow> sch_act_simple s) \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setThreadState_def)
  apply wp
   apply simp
   prefer 2
   apply assumption
  apply (case_tac "runnable' st")
   apply (rule_tac Q="\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
                in hoare_pre_imp, simp)
   apply ((wp hoare_drop_imps threadSet_runnable_sch_act | simp)+)[1]
  apply (rule_tac Q="\<lambda>rv s. st_tcb_at' (Not \<circ> runnable') t s \<and>
                     (ksCurThread s \<noteq> t \<or> ksSchedulerAction s \<noteq> ResumeCurrentThread \<longrightarrow>
                            sch_act_wf (ksSchedulerAction s) s)"
               in hoare_post_imp)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre)
   apply (wp threadSet_pred_tcb_at_state threadSet_sch_act_wf
             hoare_vcg_disj_lift|simp)+
  apply (auto simp: sch_act_simple_def)
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

lemma rescheduleRequired_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp)+
  done

crunch no_sa[wp]: tcbSchedDequeue "\<lambda>s. P (ksSchedulerAction s)"

lemma sts_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp hoare_drop_imps | rule sch_act_simple_lift | simp)+
  done

lemma setQueue_after:
  "(setQueue d p q >>= (\<lambda>rv. threadSet f t)) =
   (threadSet f t >>= (\<lambda>rv. setQueue d p q))"
  apply (simp add: setQueue_def)
  apply (rule oblivious_modify_swap)
  apply (simp add: threadSet_def getObject_def setObject_def
                   loadObject_default_def
                   split_def projectKO_def2 alignCheck_assert
                   magnitudeCheck_assert updateObject_default_def)
  apply (intro oblivious_bind, simp_all)
  done

lemma tcbSchedEnqueue_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (simp add: tcbSchedEnqueue_def tcbQueuePrepend_def unless_def)
     (wp setQueue_sch_act threadSet_tcbDomain_triv | wp sch_act_wf_lift  | clarsimp)+

lemma tcbSchedEnqueue_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def tcbQueuePrepend_def unless_def)
  apply (wp setQueue_sch_act threadSet_weak_sch_act_wf | clarsimp)+
  done

lemma threadGet_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at' tcb t s \<longrightarrow> P (f tcb) s\<rbrace> threadGet f t \<lbrace>P\<rbrace>"
  apply (simp add: threadGet_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadGet_const:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> obj_at' (P \<circ> f) t s\<rbrace> threadGet f t \<lbrace>\<lambda>rv s. P (rv)\<rbrace>"
  apply (simp add: threadGet_def liftM_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

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
   \<Longrightarrow> bitmapQ d p s = (\<not> tcbQueueEmpty (ksReadyQueues s (d, p)))"
  by (fastforce simp: valid_bitmapQ_except_def)

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
  "\<lbrace>valid_bitmapQ_except d p and bitmapQ_no_L2_orphans
    and (\<lambda>s. \<not> tcbQueueEmpty (ksReadyQueues s (d,p)))\<rbrace>
   addToBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q="\<lambda>_ s. ?pre s \<and> bitmapQ d p s" in hoare_strengthen_post)
   apply (wpsimp wp: addToBitmap_valid_bitmapQ_except addToBitmap_bitmapQ)
  apply (fastforce elim: valid_bitmap_valid_bitmapQ_exceptE)
  done

lemma threadGet_const_tcb_at:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> obj_at' (P s \<circ> f) t s\<rbrace> threadGet f t \<lbrace>\<lambda>rv s. P s rv \<rbrace>"
  apply (simp add: threadGet_def liftM_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadGet_const_tcb_at_imp_lift:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> obj_at' (P s \<circ> f) t s \<longrightarrow>  obj_at' (Q s \<circ> f) t s \<rbrace>
   threadGet f t
   \<lbrace>\<lambda>rv s. P s rv \<longrightarrow> Q s rv \<rbrace>"
  apply (simp add: threadGet_def liftM_def)
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

lemma setQueue_sets_queue[wp]:
  "\<And>d p ts P. \<lbrace> \<lambda>s. P ts \<rbrace> setQueue d p ts \<lbrace>\<lambda>rv s. P (ksReadyQueues s (d, p)) \<rbrace>"
  unfolding setQueue_def
  by (wp, simp)

lemma rescheduleRequired_valid_bitmapQ_sch_act_simple:
  "\<lbrace> valid_bitmapQ and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  including classic_wp_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac Q'="\<lambda>rv s. valid_bitmapQ s \<and>
                             (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)"
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
  apply (rule_tac Q'="\<lambda>rv s. bitmapQ_no_L1_orphans s \<and>
                             (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)"
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
  apply (rule_tac Q'="\<lambda>rv s. bitmapQ_no_L2_orphans s \<and>
                             (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)"
               in bind_wp)
   apply wpsimp
   apply (case_tac rv; simp)
  apply (wp, fastforce)
  done

lemma sts_valid_bitmapQ_sch_act_simple:
  "\<lbrace>valid_bitmapQ and sch_act_simple\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_valid_bitmapQ_sch_act_simple
            threadSet_valid_bitmapQ [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def inQ_def)+
  done

lemma sts_valid_bitmapQ_no_L2_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L2_orphans and sch_act_simple\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_bitmapQ_no_L2_orphans_sch_act_simple
            threadSet_valid_bitmapQ_no_L2_orphans [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def inQ_def)+
  done

lemma sts_valid_bitmapQ_no_L1_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L1_orphans and sch_act_simple\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_bitmapQ_no_L1_orphans_sch_act_simple
            threadSet_valid_bitmapQ_no_L1_orphans [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def inQ_def)+
  done

lemma rescheduleRequired_ksQ:
  "\<lbrace>\<lambda>s. sch_act_simple s \<and> P (ksReadyQueues s p)\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  including no_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac Q'="\<lambda>rv s. (rv = ResumeCurrentThread \<or> rv = ChooseNewThread) \<and> P (ksReadyQueues s p)"
               in bind_wp)
   apply wpsimp
   apply (case_tac rv; simp)
  apply wp
  done

lemma setSchedulerAction_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setSchedulerAction act \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wp, simp)

lemma threadSet_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (simp add: threadSet_def | wp updateObject_default_inv)+

lemma sbn_ksQ:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s p)\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv s. P (ksReadyQueues s p)\<rbrace>"
  by (simp add: setBoundNotification_def, wp)

lemma setQueue_ksQ[wp]:
  "\<lbrace>\<lambda>s. P ((ksReadyQueues s)((d, p) := q))\<rbrace>
     setQueue d p q
   \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (simp add: setQueue_def fun_upd_def[symmetric]
           | wp)+

lemma threadSet_tcbState_st_tcb_at':
  "\<lbrace>\<lambda>s. P st \<rbrace> threadSet (tcbState_update (\<lambda>_. st)) t \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: threadSet_def pred_tcb_at'_def)
  apply (wpsimp wp: setObject_tcb_strongest)
  done

lemma isRunnable_const:
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> isRunnable t \<lbrace>\<lambda>runnable _. runnable \<rbrace>"
  by (rule isRunnable_wp)

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
  = X64_H.msgRegisters_def
    msg_registers_def
    X64.msgRegisters_def
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
                   put_def bind_def return_def gets_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: map_upd_triv select_f_def image_def return_def)
  done

lemma getMRs_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct)
              (case_option \<top> valid_ipc_buffer_ptr' buf)
              (get_mrs t buf mi) (getMRs t buf (message_info_map mi))"
  proof -
  have S: "get = gets id"
    by (simp add: gets_def)
  have T: "corres (\<lambda>con regs. regs = map con msg_registers)
                  (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                  (thread_get (arch_tcb_get_registers o tcb_arch) t)
                  (asUser t (mapM getRegister X64_H.msgRegisters))"
   apply (subst thread_get_registers)
    apply (rule asUser_corres')
    apply (subst mapM_gets)
     apply (simp add: getRegister_def)
    apply (simp add: S X64_H.msgRegisters_def msg_registers_def)
    done
  show ?thesis
  apply (case_tac mi, simp add: get_mrs_def getMRs_def split del: if_split)
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
  "UserContext (fpu_state s) (foldl (\<lambda>s (x, y). s(x := y)) (user_regs s) xs) =
   foldl (\<lambda>s (r, v). UserContext (fpu_state s) ((user_regs s)(r := v))) s xs"
  apply (induct xs arbitrary: s; simp)
  apply (clarsimp split: prod.splits)
  by (metis user_context.sel(1) user_context.sel(2))

lemma setMRs_corres:
  assumes m: "mrs' = mrs"
  shows
  "corres (=) (tcb_at t and case_option \<top> in_user_frame buf and pspace_aligned and pspace_distinct)
              (case_option \<top> valid_ipc_buffer_ptr' buf)
              (set_mrs t buf mrs) (setMRs t buf mrs')"
proof -
  have setRegister_def2:
    "setRegister = (\<lambda>r v.  modify (\<lambda>s. UserContext (fpu_state s) ((user_regs s)(r := v))))"
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
  "corres (=) (tcb_at s and tcb_at r
               and case_option \<top> in_user_frame sb
               and case_option \<top> in_user_frame rb
               and pspace_aligned and pspace_distinct
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
    "\<And>v :: machine_word. corres dc (tcb_at s and tcb_at r and pspace_aligned and pspace_distinct) \<top>
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
        apply (rule corres_split_eqr[OF asUser_setRegister_corres asUser_getRegister_corres])
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
               (valid_objs' and pspace_aligned' and pspace_distinct' and no_0_obj')
               (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  apply (simp add: lookup_ipc_buffer_def X64_H.lookupIPCBuffer_def)
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
        apply (rename_tac word rights mt vmpage_size option)
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
  "corres (=) (tcb_at t and invs) invs'
          (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  using lookupIPCBuffer_corres'
  by (rule corres_guard_imp, auto simp: invs'_def valid_state'_def)


crunch inv[wp]: lookupIPCBuffer P
  (wp: crunch_wps simp: crunch_simps)

crunch pred_tcb_at'[wp]: rescheduleRequired "pred_tcb_at' proj P t"

lemma setThreadState_st_tcb':
  "\<lbrace>\<top>\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>s. s = st) t\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_pred_tcb_at_state | simp add: if_apply_def2)+
  done

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
  (simp: unless_def)

lemma ct_in_state'_decomp:
  assumes x: "\<lbrace>\<lambda>s. t = (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv s. t = (ksCurThread s)\<rbrace>"
  assumes y: "\<lbrace>Pre\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' Prop t\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Pre s \<and> t = (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv. ct_in_state' Prop\<rbrace>"
  apply (rule hoare_post_imp [where Q="\<lambda>rv s. t = ksCurThread s \<and> st_tcb_at' Prop t s"])
   apply (clarsimp simp add: ct_in_state'_def)
  apply (rule hoare_weaken_pre)
   apply (wp x y)
  apply simp
  done

lemma ct_in_state'_set:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> P st \<and> t = ksCurThread s\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule ct_in_state'_decomp[where t=t])
    apply (wp setThreadState_ct')
   apply (wp setThreadState_st_tcb)
  apply clarsimp
  done

crunches setQueue, rescheduleRequired, tcbSchedDequeue
  for idle'[wp]: "valid_idle'"
  (simp: crunch_simps wp: crunch_wps)

lemma sts_valid_idle'[wp]:
  "\<lbrace>valid_idle' and valid_pspace' and
    (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' ts)\<rbrace>
   setThreadState ts t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wpsimp wp: threadSet_idle' simp: idle_tcb'_def)
  done

lemma sbn_valid_idle'[wp]:
  "\<lbrace>valid_idle' and valid_pspace' and
    (\<lambda>s. t = ksIdleThread s \<longrightarrow> \<not>bound ntfn)\<rbrace>
   setBoundNotification ntfn t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wpsimp wp: threadSet_idle' simp: idle_tcb'_def)
  done

lemma gts_sp':
  "\<lbrace>P\<rbrace> getThreadState t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>st. st = rv) t and P\<rbrace>"
  apply (simp add: getThreadState_def threadGet_def)
  apply wp
  apply (simp add: o_def pred_tcb_at'_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma gbn_sp':
  "\<lbrace>P\<rbrace> getBoundNotification t \<lbrace>\<lambda>rv. bound_tcb_at' (\<lambda>st. st = rv) t and P\<rbrace>"
  apply (simp add: getBoundNotification_def threadGet_def)
  apply wp
  apply (simp add: o_def pred_tcb_at'_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbSchedDequeue_tcbState_obj_at'[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>rv. obj_at' (P \<circ> tcbState) t'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def tcbQueueRemove_def)
  apply (wpsimp wp: getObject_tcb_wp simp: o_def threadGet_def)
  apply (clarsimp simp: obj_at'_def)
  done

crunch typ_at'[wp]: setQueue "\<lambda>s. P' (typ_at' P t s)"

lemma setQueue_pred_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P' (pred_tcb_at' proj P t s)\<rbrace> setQueue d p q \<lbrace>\<lambda>rv s. P' (pred_tcb_at' proj P t s)\<rbrace>"
  unfolding pred_tcb_at'_def
  apply (rule_tac P=P' in P_bool_lift)
   apply (rule setQueue_obj_at)
  apply (rule_tac Q="\<lambda>_ s. \<not>typ_at' TCBT t s \<or> obj_at' (Not \<circ> (P \<circ> proj \<circ> tcb_to_itcb')) t s"
           in hoare_post_imp, simp add: not_obj_at' o_def)
  apply (wp hoare_vcg_disj_lift)
  apply (clarsimp simp: not_obj_at' o_def)
  done

lemma tcbSchedDequeue_pred_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. P' (pred_tcb_at' proj P t' s)\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_ s. P' (pred_tcb_at' proj P t' s)\<rbrace>"
  apply (rule_tac P=P' in P_bool_lift)
   apply (simp add: tcbSchedDequeue_def tcbQueueRemove_def)
   apply (wpsimp wp: threadSet_pred_tcb_no_state getObject_tcb_wp
               simp: threadGet_def tcb_to_itcb'_def)
   apply (clarsimp simp: obj_at'_def)
  apply (simp add: tcbSchedDequeue_def tcbQueueRemove_def)
  apply (wpsimp wp: threadSet_pred_tcb_no_state getObject_tcb_wp
              simp: threadGet_def tcb_to_itcb'_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma sts_st_tcb':
  "\<lbrace>if t = t' then K (P st) else st_tcb_at' P t\<rbrace>
  setThreadState st t'
  \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (cases "t = t'",
         simp_all add: setThreadState_def
                  split del: if_split)
   apply ((wp threadSet_pred_tcb_at_state | simp)+)[1]
  apply (wp threadSet_obj_at'_really_strongest
              | simp add: pred_tcb_at'_def)+
  done

lemma sts_bound_tcb_at':
  "\<lbrace>bound_tcb_at' P t\<rbrace>
  setThreadState st t'
  \<lbrace>\<lambda>_. bound_tcb_at' P t\<rbrace>"
  apply (cases "t = t'",
         simp_all add: setThreadState_def
                  split del: if_split)
   apply ((wp threadSet_pred_tcb_at_state | simp)+)[1]
   apply (wp threadSet_obj_at'_really_strongest
               | simp add: pred_tcb_at'_def)+
  done

lemma sbn_st_tcb':
  "\<lbrace>st_tcb_at' P t\<rbrace>
  setBoundNotification ntfn t'
  \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (cases "t = t'",
         simp_all add: setBoundNotification_def
                  split del: if_split)
   apply ((wp threadSet_pred_tcb_at_state | simp)+)[1]
  apply (wp threadSet_obj_at'_really_strongest
              | simp add: pred_tcb_at'_def)+
  done

lemma sbn_bound_tcb_at':
  "\<lbrace>if t = t' then K (P ntfn) else bound_tcb_at' P t\<rbrace>
  setBoundNotification ntfn t'
  \<lbrace>\<lambda>_. bound_tcb_at' P t\<rbrace>"
  apply (cases "t = t'",
         simp_all add: setBoundNotification_def
                  split del: if_split)
   apply ((wp threadSet_pred_tcb_at_state | simp)+)[1]
   apply (wp threadSet_obj_at'_really_strongest
               | simp add: pred_tcb_at'_def)+
  done

crunches rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemmas setThreadState_typ_ats[wp] = typ_at_lifts [OF setThreadState_typ_at']
lemmas setBoundNotification_typ_ats[wp] = typ_at_lifts [OF setBoundNotification_typ_at']

crunches setThreadState, setBoundNotification
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  (wp: hoare_when_weak_wp)

crunch refs_of'[wp]: rescheduleRequired "\<lambda>s. P (state_refs_of' s)"
  (wp: threadSet_state_refs_of')

lemma setThreadState_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' st
                                 \<union> {r \<in> state_refs_of' s t. snd r = TCBBound}))\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (simp add: setThreadState_def fun_upd_def
        | wp threadSet_state_refs_of')+

lemma setBoundNotification_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_bound_refs' ntfn
                                 \<union> {r \<in> state_refs_of' s t. snd r \<noteq> TCBBound}))\<rbrace>
     setBoundNotification ntfn t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (simp add: setBoundNotification_def Un_commute fun_upd_def
        | wp threadSet_state_refs_of' )+

lemma sts_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

lemma sbn_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

crunch iflive'[wp]: setQueue if_live_then_nonz_cap'
crunch nonz_cap[wp]: setQueue "ex_nonz_cap_to' t"
crunch iflive'[wp]: addToBitmap if_live_then_nonz_cap'
crunch nonz_cap[wp]: addToBitmap "ex_nonz_cap_to' t"
crunch iflive'[wp]: removeFromBitmap if_live_then_nonz_cap'
crunch nonz_cap[wp]: removeFromBitmap "ex_nonz_cap_to' t"

crunches rescheduleRequired
  for cap_to'[wp]: "ex_nonz_cap_to' p"

lemma tcbQueued_update_tcb_cte_cases:
  "(getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbQueued_update f tcb) = getF tcb"
  unfolding tcb_cte_cases_def
  by (case_tac tcb; fastforce simp: objBits_simps')

lemma tcbSchedNext_update_tcb_cte_cases:
  "(getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbSchedNext_update f tcb) = getF tcb"
  unfolding tcb_cte_cases_def
  by (case_tac tcb; fastforce simp: objBits_simps')

lemma tcbSchedPrev_update_tcb_cte_cases:
  "(getF, setF) \<in> ran tcb_cte_cases \<Longrightarrow> getF (tcbSchedPrev_update f tcb) = getF tcb"
  unfolding tcb_cte_cases_def
  by (case_tac tcb; fastforce simp: objBits_simps')

lemma tcbSchedNext_update_ctes_of[wp]:
  "threadSet (tcbSchedNext_update f) tptr \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_ofT simp: tcbSchedNext_update_tcb_cte_cases)

lemma tcbSchedPrev_update_ctes_of[wp]:
  "threadSet (tcbSchedPrev_update f) tptr \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  by (wpsimp wp: threadSet_ctes_ofT simp: tcbSchedPrev_update_tcb_cte_cases)

lemma tcbSchedNext_ex_nonz_cap_to'[wp]:
  "threadSet (tcbSchedNext_update f) tptr \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wpsimp wp: threadSet_cap_to simp: tcbSchedNext_update_tcb_cte_cases)

lemma tcbSchedPrev_ex_nonz_cap_to'[wp]:
  "threadSet (tcbSchedPrev_update f) tptr \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wpsimp wp: threadSet_cap_to simp: tcbSchedPrev_update_tcb_cte_cases)

lemma tcbSchedNext_update_iflive':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' t s\<rbrace>
   threadSet (tcbSchedNext_update f) t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: threadSet_iflive'T simp: tcbSchedNext_update_tcb_cte_cases)

lemma tcbSchedPrev_update_iflive':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' t s\<rbrace>
   threadSet (tcbSchedPrev_update f) t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: threadSet_iflive'T simp: tcbSchedPrev_update_tcb_cte_cases)

lemma tcbQueued_update_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' t s\<rbrace>
   threadSet (tcbQueued_update f) t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: threadSet_iflive'T simp: tcbQueued_update_tcb_cte_cases)

lemma getTCB_wp:
  "\<lbrace>\<lambda>s. \<forall>ko :: tcb. ko_at' ko p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  apply (wpsimp wp: getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbQueueRemove_if_live_then_nonz_cap':
  "\<lbrace>if_live_then_nonz_cap' and valid_objs' and sym_heap_sched_pointers and ex_nonz_cap_to' tcbPtr\<rbrace>
   tcbQueueRemove q tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: tcbSchedPrev_update_iflive' tcbSchedNext_update_iflive'
                    hoare_vcg_imp_lift' getTCB_wp)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (force dest: sym_heapD2[where p'=tcbPtr] sym_heapD1[where p=tcbPtr]
               elim: if_live_then_nonz_capE'
               simp: valid_tcb'_def opt_map_def obj_at'_def ko_wp_at'_def projectKOs)
  done

lemma tcbQueueRemove_ex_nonz_cap_to'[wp]:
  "tcbQueueRemove q tcbPtr \<lbrace>ex_nonz_cap_to' tcbPtr'\<rbrace>"
  unfolding tcbQueueRemove_def
  by (wpsimp wp: threadSet_cap_to' hoare_drop_imps getTCB_wp)

(* We could write this one as "\<forall>t. tcbQueueHead t \<longrightarrow> ..." instead, but we can't do the same in
   tcbQueueAppend_if_live_then_nonz_cap', and it's nicer if the two lemmas are symmetric *)
lemma tcbQueuePrepend_if_live_then_nonz_cap':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' tcbPtr s
        \<and> (\<not> tcbQueueEmpty q \<longrightarrow> ex_nonz_cap_to' (the (tcbQueueHead q)) s)\<rbrace>
   tcbQueuePrepend q tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: tcbSchedPrev_update_iflive' tcbSchedNext_update_iflive'
                 hoare_vcg_if_lift2 hoare_vcg_imp_lift')

lemma tcbQueueAppend_if_live_then_nonz_cap':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' tcbPtr s
        \<and> (\<not> tcbQueueEmpty q \<longrightarrow> ex_nonz_cap_to' (the (tcbQueueEnd q)) s)\<rbrace>
   tcbQueueAppend q tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbQueueAppend_def
  by (wpsimp wp: tcbSchedPrev_update_iflive' tcbSchedNext_update_iflive')

lemma tcbQueueInsert_if_live_then_nonz_cap':
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' tcbPtr and valid_objs' and sym_heap_sched_pointers\<rbrace>
   tcbQueueInsert tcbPtr afterPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbQueueInsert_def
  supply projectKOs[simp]
  apply (wpsimp wp: tcbSchedPrev_update_iflive' tcbSchedNext_update_iflive' getTCB_wp)
  apply (intro conjI)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def obj_at'_def)
  apply (erule if_live_then_nonz_capE')
  apply (frule_tac p'=afterPtr in sym_heapD2)
   apply (fastforce simp: opt_map_def obj_at'_def)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (clarsimp simp: valid_tcb'_def ko_wp_at'_def obj_at'_def opt_map_def)
  done

lemma tcbSchedEnqueue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbSchedEnqueue_def
  supply projectKOs[simp]
  apply (wpsimp wp: tcbQueuePrepend_if_live_then_nonz_cap' threadGet_wp)
  apply normalise_obj_at'
  apply (rename_tac tcb)
  apply (frule_tac p=tcbPtr in if_live_then_nonz_capE')
   apply (fastforce simp: ko_wp_at'_def obj_at'_def)
  apply clarsimp
  apply (erule if_live_then_nonz_capE')
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce dest!: obj_at'_tcbQueueHead_ksReadyQueues
                    simp: ko_wp_at'_def inQ_def opt_pred_def opt_map_def obj_at'_def
                   split: option.splits)
  done

crunches rescheduleRequired
  for iflive'[wp]: if_live_then_nonz_cap'

lemma sts_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setThreadState_def setQueue_def)
  apply wpsimp
   apply (rule_tac Q="\<lambda>rv. if_live_then_nonz_cap' and pspace_aligned' and pspace_distinct'"
                in hoare_post_imp)
    apply clarsimp
   apply (wpsimp wp: threadSet_iflive')
  apply fastforce
  done

lemma sbn_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (bound ntfn \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
     setBoundNotification ntfn t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (rule hoare_pre)
   apply (wp threadSet_iflive' | simp)+
  apply auto
  done

crunches setThreadState, setBoundNotification
  for ifunsafe'[wp]: "if_unsafe_then_cap'"

lemma st_tcb_ex_cap'':
  "\<lbrakk> st_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>st. P st \<Longrightarrow> st \<noteq> Inactive \<and> \<not> idle' st \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def projectKOs
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

lemma bound_tcb_ex_cap'':
  "\<lbrakk> bound_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>ntfn. P ntfn \<Longrightarrow> bound ntfn \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def projectKOs
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

crunches setThreadState, setBoundNotification
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: unless_def crunch_simps)

crunch it' [wp]: removeFromBitmap "\<lambda>s. P (ksIdleThread s)"

lemma sts_ctes_of [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> setThreadState st t \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_ctes_ofT | simp add: tcb_cte_cases_def)+
  done

lemma sbn_ctes_of [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_ctes_ofT | simp add: tcb_cte_cases_def)+
  done

crunches setThreadState, setBoundNotification
  for ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  (simp: unless_def crunch_simps)

crunches setThreadState, setBoundNotification
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (simp: unless_def crunch_simps wp: setObject_ksPSpace_only updateObject_default_inv)

lemmas setThreadState_irq_handlers[wp]
    = valid_irq_handlers_lift'' [OF sts_ctes_of setThreadState_ksInterruptState]

lemmas setBoundNotification_irq_handlers[wp]
    = valid_irq_handlers_lift'' [OF sbn_ctes_of setBoundNotification_ksInterruptState]

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
  (simp: crunch_simps)

crunches setThreadState, setBoundNotification
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (simp: unless_def crunch_simps)

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

lemma threadSet_ct_not_inQ:
  "(\<And>tcb. tcbQueued tcb = tcbQueued (F tcb))
   \<Longrightarrow> threadSet F tcbPtr \<lbrace>\<lambda>s. P (ct_not_inQ s)\<rbrace>"
  unfolding threadSet_def
  supply projectKOs[simp]
  apply (wpsimp wp: getTCB_wp simp: setObject_def updateObject_default_def)
  apply (erule rsubst[where P=P])
  by (fastforce simp: ct_not_inQ_def obj_at'_def objBits_simps ps_clear_def split: if_splits)

crunches tcbQueuePrepend, tcbQueueAppend, tcbQueueInsert, tcbQueueRemove, addToBitmap
  for ct_not_inQ[wp]: ct_not_inQ
  (wp: threadSet_ct_not_inQ crunch_wps)

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
      apply (rule hoare_convert_imp [OF threadSet_nosch])
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
      apply (wpsimp wp: ts sq hoare_vcg_imp_lift' getTCB_wp simp: threadGet_def)+
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
      apply (rule hoare_convert_imp [OF threadSet_nosch])
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
      apply (wpsimp wp: ts sq hoare_vcg_imp_lift' getTCB_wp simp: threadGet_def)+
      done
  qed

lemma setSchedulerAction_direct:
  "\<lbrace>\<top>\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_ s. ksSchedulerAction s = sa\<rbrace>"
  by (wpsimp simp: setSchedulerAction_def)

lemma rescheduleRequired_ct_not_inQ:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: rescheduleRequired_def ct_not_inQ_def)
  apply (rule_tac Q="\<lambda>_ s. ksSchedulerAction s = ChooseNewThread"
           in hoare_post_imp, clarsimp)
  apply (wp setSchedulerAction_direct)
  done

lemma rescheduleRequired_sa_cnt[wp]:
  "\<lbrace>\<lambda>s. True \<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread \<rbrace>"
  unfolding rescheduleRequired_def setSchedulerAction_def
  by wpsimp

lemma possibleSwitchTo_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
    possibleSwitchTo t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wpsimp wp: hoare_weak_lift_imp rescheduleRequired_ct_not_inQ tcbSchedEnqueue_ct_not_inQ
                    threadGet_wp
         | (rule hoare_post_imp[OF _ rescheduleRequired_sa_cnt], fastforce))+
  done

lemma threadSet_tcbState_update_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> threadSet (tcbState_update f) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: ct_not_inQ_def)
  apply (rule hoare_convert_imp [OF threadSet_nosch])
  apply (simp add: threadSet_def)
  apply (wp)
    apply (wps setObject_ct_inv)
    apply (rule setObject_tcb_strongest)
   prefer 2
   apply assumption
  apply (clarsimp)
  apply (rule hoare_conjI)
   apply (rule hoare_weaken_pre)
   apply (wps, wp hoare_weak_lift_imp)
   apply (wp OMG_getObject_tcb)+
   apply (clarsimp simp: comp_def)
  apply (wp hoare_drop_imp)
  done

lemma threadSet_tcbBoundNotification_update_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> threadSet (tcbBoundNotification_update f) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: ct_not_inQ_def)
  apply (rule hoare_convert_imp [OF threadSet_nosch])
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
   apply (wp hoare_weak_lift_imp)
   apply (wp OMG_getObject_tcb)
   apply (clarsimp simp: comp_def)
  apply (wp hoare_drop_imp)
  done

lemma setThreadState_ct_not_inQ:
  "\<lbrace>ct_not_inQ\<rbrace> setThreadState st t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  including no_pre
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_ct_not_inQ)
  apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
  apply (wp)
  done

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
      apply (wp hoare_convert_imp [OF threadSet_nosch])
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

crunches tcbQueuePrepend
  for ct_idle_or_in_cur_domain'[wp]: ct_idle_or_in_cur_domain'

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

lemma rescheduleRequired_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp setSchedulerAction_spec)
  done

lemma rescheduleRequired_ksCurDomain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s) \<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. P (ksCurDomain s) \<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply wpsimp
  done

lemma rescheduleRequired_ksDomSchedule[wp]:
  "\<lbrace> \<lambda>s. P (ksDomSchedule s) \<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  by (simp add: rescheduleRequired_def) wpsimp

lemma setThreadState_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setThreadState st tptr \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_ct_idle_or_in_cur_domain' hoare_drop_imps | simp)+
  done

lemma setThreadState_ksCurDomain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s) \<rbrace> setThreadState st tptr \<lbrace>\<lambda>_ s. P (ksCurDomain s) \<rbrace>"
  apply (simp add: setThreadState_def)
  apply wpsimp
  done

lemma setThreadState_ksDomSchedule[wp]:
  "\<lbrace> \<lambda>s. P (ksDomSchedule s) \<rbrace> setThreadState st tptr \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  apply (simp add: setThreadState_def)
  apply wpsimp
  done

lemma setBoundNotification_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setBoundNotification t a \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_ct_idle_or_in_cur_domain' hoare_drop_imps | simp)+
  done

lemma setBoundNotification_ksCurDomain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s) \<rbrace> setBoundNotification st tptr \<lbrace>\<lambda>_ s. P (ksCurDomain s) \<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply wpsimp
  done

lemma setBoundNotification_ksDomSchedule[wp]:
  "\<lbrace> \<lambda>s. P (ksDomSchedule s) \<rbrace> setBoundNotification st tptr \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply wpsimp
  done

crunches rescheduleRequired, setBoundNotification, setThreadState
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ioports'[wp]: valid_ioports'
  (wp: valid_ioports_lift'')

lemma sts_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp untyped_ranges_zero_lift)
  done

lemma removeFromBitmap_bitmapQ:
  "\<lbrace>\<top>\<rbrace> removeFromBitmap d p \<lbrace>\<lambda>_ s. \<not> bitmapQ d p s \<rbrace>"
  unfolding bitmapQ_defs bitmap_fun_defs
  by (wpsimp simp: bitmap_fun_defs)

lemma removeFromBitmap_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmapQ_except d p and bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans
    and (\<lambda>s. tcbQueueEmpty (ksReadyQueues s (d,p)))\<rbrace>
   removeFromBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q="\<lambda>_ s. ?pre s \<and> \<not> bitmapQ d p s" in hoare_strengthen_post)
   apply (wpsimp wp: removeFromBitmap_valid_bitmapQ_except removeFromBitmap_bitmapQ)
  apply (fastforce elim: valid_bitmap_valid_bitmapQ_exceptE)
  done

crunches tcbSchedDequeue
  for bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans
  (wp: crunch_wps simp: crunch_simps)

lemma setQueue_nonempty_valid_bitmapQ':
  "\<lbrace>\<lambda>s. valid_bitmapQ s \<and> \<not> tcbQueueEmpty (ksReadyQueues s (d, p))\<rbrace>
   setQueue d p queue
   \<lbrace>\<lambda>_ s. \<not> tcbQueueEmpty queue \<longrightarrow> valid_bitmapQ s\<rbrace>"
  apply (wpsimp simp: setQueue_def)
  apply (fastforce simp: valid_bitmapQ_def bitmapQ_def)
  done

lemma threadSet_valid_bitmapQ_except[wp]:
  "threadSet f tcbPtr \<lbrace>valid_bitmapQ_except d p\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: getTCB_wp simp: setObject_def updateObject_default_def)
  apply (clarsimp simp: valid_bitmapQ_except_def bitmapQ_def)
  done

lemma threadSet_bitmapQ:
  "threadSet F t \<lbrace>bitmapQ domain priority\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: getTCB_wp simp: setObject_def updateObject_default_def)
  by (clarsimp simp: bitmapQ_def)

crunches tcbQueueRemove, tcbQueuePrepend, tcbQueueAppend
  for valid_bitmapQ_except[wp]: "valid_bitmapQ_except d p"
  and valid_bitmapQ[wp]: valid_bitmapQ
  and bitmapQ[wp]: "bitmapQ tdom prio"
  (wp: crunch_wps)

lemma tcbQueued_imp_queue_nonempty:
  "\<lbrakk>list_queue_relation ts (ksReadyQueues s (tcbDomain tcb, tcbPriority tcb)) nexts prevs;
    \<forall>t. t \<in> set ts \<longleftrightarrow> (inQ (tcbDomain tcb) (tcbPriority tcb) |< tcbs_of' s) t;
    ko_at' tcb tcbPtr s; tcbQueued tcb\<rbrakk>
   \<Longrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (tcbDomain tcb, tcbPriority tcb))"
  supply projectKOs[simp]
  apply (clarsimp simp: list_queue_relation_def tcbQueueEmpty_def)
  apply (drule_tac x=tcbPtr in spec)
  apply (fastforce dest: heap_path_head simp: inQ_def opt_map_def opt_pred_def obj_at'_def)
  done

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

lemma setQueue_valid_bitmapQ': (* enqueue only *)
  "\<lbrace>valid_bitmapQ_except d p and bitmapQ d p and K (\<not> tcbQueueEmpty q)\<rbrace>
   setQueue d p q
   \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  unfolding setQueue_def bitmapQ_defs
  by (wpsimp simp: bitmapQ_def)

lemma tcbSchedEnqueue_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmaps\<rbrace> tcbSchedEnqueue tcbPtr \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  supply if_split[split del]
  unfolding tcbSchedEnqueue_def
  apply (wpsimp simp: tcbQueuePrepend_def
                  wp: setQueue_valid_bitmapQ' addToBitmap_valid_bitmapQ_except addToBitmap_bitmapQ
                      threadGet_wp)
  apply (fastforce simp: valid_bitmaps_def valid_bitmapQ_def tcbQueueEmpty_def split: if_splits)
  done

crunches tcbSchedEnqueue, tcbSchedAppend
  for bitmapQ_no_L1_orphans[wp]: bitmapQ_no_L1_orphans
  and bitmapQ_no_L2_orphans[wp]: bitmapQ_no_L2_orphans

lemma tcbSchedEnqueue_valid_bitmaps[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  unfolding valid_bitmaps_def
  apply wpsimp
  apply (clarsimp simp: valid_bitmaps_def)
  done

crunches rescheduleRequired, threadSet, setThreadState
  for valid_bitmaps[wp]: valid_bitmaps
  (rule: valid_bitmaps_lift)

lemma tcbSchedEnqueue_valid_sched_pointers[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  supply projectKOs[simp]
  apply (clarsimp simp: tcbSchedEnqueue_def getQueue_def unless_def)
  \<comment> \<open>we step forwards until we can step over the addToBitmap in order to avoid state blow-up\<close>
  apply (intro bind_wp[OF _ stateAssert_sp] bind_wp[OF _ isRunnable_inv]
               bind_wp[OF _ assert_sp] bind_wp[OF _ threadGet_sp]
               bind_wp[OF _ gets_sp]
         | rule hoare_when_cases, fastforce)+
  apply (forward_inv_step wp: hoare_vcg_ex_lift)
  supply if_split[split del]
  apply (wpsimp wp: getTCB_wp
              simp: threadSet_def setObject_def updateObject_default_def tcbQueuePrepend_def
                    setQueue_def)
  apply (clarsimp simp: valid_sched_pointers_def)
  apply (intro conjI impI)
   apply (fastforce simp: opt_pred_def opt_map_def split: if_splits)
  apply normalise_obj_at'
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (clarsimp simp: valid_sched_pointers_def list_queue_relation_def)
  apply (case_tac "ts = []", fastforce simp: tcbQueueEmpty_def)
  by (intro conjI impI;
      force dest!: hd_in_set heap_path_head
             simp: inQ_def opt_pred_def opt_map_def obj_at'_def split: if_splits)

lemma tcbSchedAppend_valid_sched_pointers[wp]:
  "tcbSchedAppend tcbPtr \<lbrace>valid_sched_pointers\<rbrace>"
  supply projectKOs[simp]
  apply (clarsimp simp: tcbSchedAppend_def getQueue_def unless_def)
  \<comment> \<open>we step forwards until we can step over the addToBitmap in order to avoid state blow-up\<close>
  apply (intro bind_wp[OF _ stateAssert_sp] bind_wp[OF _ isRunnable_inv]
               bind_wp[OF _ assert_sp] bind_wp[OF _ threadGet_sp]
               bind_wp[OF _ gets_sp]
         | rule hoare_when_cases, fastforce)+
  apply (forward_inv_step wp: hoare_vcg_ex_lift)
  supply if_split[split del]
  apply (wpsimp wp: getTCB_wp
              simp: threadSet_def setObject_def updateObject_default_def tcbQueueAppend_def
                    setQueue_def)
  apply (clarsimp simp: valid_sched_pointers_def)
  apply (intro conjI impI)
   apply (fastforce simp: opt_pred_def opt_map_def split: if_splits)
  apply normalise_obj_at'
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  by (intro conjI impI;
      clarsimp dest: last_in_set
               simp: valid_sched_pointers_def opt_map_def list_queue_relation_def tcbQueueEmpty_def
                     queue_end_valid_def inQ_def opt_pred_def obj_at'_def
              split: if_splits option.splits;
      fastforce)

lemma tcbSchedDequeue_valid_sched_pointers[wp]:
  "\<lbrace>valid_sched_pointers and sym_heap_sched_pointers\<rbrace>
   tcbSchedDequeue tcbPtr
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  supply if_split[split del] fun_upd_apply[simp del]
  supply projectKOs[simp]
  apply (clarsimp simp: tcbSchedDequeue_def getQueue_def setQueue_def)
  apply (wpsimp wp: threadSet_wp getTCB_wp threadGet_wp simp: tcbQueueRemove_def)
  apply normalise_obj_at'
  apply (rename_tac tcb)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (clarsimp split: if_splits)
  apply (frule (1) list_queue_relation_neighbour_in_set[where p=tcbPtr])
   apply (fastforce simp: inQ_def opt_pred_def opt_map_def obj_at'_def)
  apply (clarsimp simp: list_queue_relation_def)
  apply (intro conjI impI)
     \<comment> \<open>the ready queue is the singleton consisting of tcbPtr\<close>
     apply (clarsimp simp: valid_sched_pointers_def)
     apply (case_tac "ptr = tcbPtr")
      apply (force dest!: heap_ls_last_None
                    simp: prev_queue_head_def queue_end_valid_def inQ_def opt_map_def obj_at'_def)
     apply (simp add: fun_upd_def opt_pred_def)
    \<comment> \<open>tcbPtr is the head of the ready queue\<close>
    subgoal
      by (auto dest!: heap_ls_last_None
                simp: valid_sched_pointers_def fun_upd_apply prev_queue_head_def
                      inQ_def opt_pred_def opt_map_def obj_at'_def
               split: if_splits option.splits)
   \<comment> \<open>tcbPtr is the end of the ready queue\<close>
   subgoal
     by (auto dest!: heap_ls_last_None
               simp: valid_sched_pointers_def queue_end_valid_def inQ_def opt_pred_def
                     opt_map_def fun_upd_apply obj_at'_def
              split: if_splits option.splits)
  \<comment> \<open>tcbPtr is in the middle of the ready queue\<close>
  apply (intro conjI impI allI)
  by (clarsimp simp: valid_sched_pointers_def inQ_def opt_pred_def opt_map_def fun_upd_apply obj_at'_def
              split: if_splits option.splits;
      auto)

lemma tcbQueueRemove_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. sym_heap_sched_pointers s
        \<and> (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                \<and> tcbPtr \<in> set ts)\<rbrace>
   tcbQueueRemove q tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  supply heap_path_append[simp del]
  supply projectKOs[simp]
  apply (clarsimp simp: tcbQueueRemove_def)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (rename_tac tcb ts)

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
  apply (fastforce simp: fun_upd_swap opt_map_red opt_map_upd_triv obj_at'_def split: if_splits)
  done

lemma tcbQueuePrepend_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. sym_heap_sched_pointers s
        \<and> (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                \<and> tcbPtr \<notin> set ts)
        \<and> tcbSchedNexts_of s tcbPtr = None \<and> tcbSchedPrevs_of s tcbPtr = None\<rbrace>
   tcbQueuePrepend q tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  supply if_split[split del]
  supply projectKOs[simp]
  apply (clarsimp simp: tcbQueuePrepend_def)
  apply (wpsimp wp: threadSet_wp)
  apply (prop_tac "tcbPtr \<noteq> the (tcbQueueHead q)")
   apply (case_tac "ts = []";
          fastforce dest: heap_path_head simp: list_queue_relation_def tcbQueueEmpty_def)
  apply (drule_tac a=tcbPtr and b="the (tcbQueueHead q)" in sym_heap_connect)
    apply assumption
   apply (clarsimp simp: list_queue_relation_def prev_queue_head_def tcbQueueEmpty_def)
  apply (fastforce simp: fun_upd_swap opt_map_red opt_map_upd_triv obj_at'_def tcbQueueEmpty_def)
  done

lemma tcbQueueInsert_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. sym_heap_sched_pointers s
        \<and> tcbSchedNexts_of s tcbPtr = None \<and> tcbSchedPrevs_of s tcbPtr = None\<rbrace>
   tcbQueueInsert tcbPtr afterPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  supply projectKOs[simp]
  apply (clarsimp simp: tcbQueueInsert_def)
  \<comment> \<open>forwards step in order to name beforePtr below\<close>
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

lemma tcbQueueAppend_sym_heap_sched_pointers:
  "\<lbrace>\<lambda>s. sym_heap_sched_pointers s
        \<and> (\<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                \<and> tcbPtr \<notin> set ts)
        \<and> tcbSchedNexts_of s tcbPtr = None \<and> tcbSchedPrevs_of s tcbPtr = None\<rbrace>
   tcbQueueAppend q tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  supply if_split[split del]
  supply projectKOs[simp]
  apply (clarsimp simp: tcbQueueAppend_def)
  apply (wpsimp wp: threadSet_wp)
  apply (clarsimp simp: tcbQueueEmpty_def list_queue_relation_def queue_end_valid_def obj_at'_def
                 split: if_splits)
   apply fastforce
  apply (drule_tac a="last ts" and b=tcbPtr in sym_heap_connect)
    apply (fastforce dest: heap_ls_last_None)
   apply assumption
  apply (simp add: opt_map_red tcbQueueEmpty_def)
  apply (subst fun_upd_swap, simp)
  apply (fastforce simp: opt_map_red opt_map_upd_triv)
  done

lemma tcbQueued_update_sym_heap_sched_pointers[wp]:
  "threadSet (tcbQueued_update f) tcbPtr \<lbrace>sym_heap_sched_pointers\<rbrace>"
  by (rule sym_heap_sched_pointers_lift;
      wpsimp wp: threadSet_tcbSchedPrevs_of threadSet_tcbSchedNexts_of)

lemma tcbSchedEnqueue_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbSchedEnqueue_def
  supply projectKOs[simp]
  apply (wpsimp wp: tcbQueuePrepend_sym_heap_sched_pointers threadGet_wp
              simp: addToBitmap_def bitmap_fun_defs)
  apply (normalise_obj_at', rename_tac tcb)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce dest!: spec[where x=tcbPtr] inQ_implies_tcbQueueds_of
                    simp: valid_sched_pointers_def opt_pred_def opt_map_def obj_at'_def)
  done

lemma tcbSchedAppend_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbSchedAppend_def
  supply projectKOs[simp]
  apply (wpsimp wp: tcbQueueAppend_sym_heap_sched_pointers threadGet_wp
              simp: addToBitmap_def bitmap_fun_defs)
  apply (normalise_obj_at', rename_tac tcb)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce dest!: spec[where x=tcbPtr] inQ_implies_tcbQueueds_of
                    simp: valid_sched_pointers_def opt_pred_def opt_map_def obj_at'_def)
  done

lemma tcbSchedDequeue_sym_heap_sched_pointers[wp]:
  "\<lbrace>sym_heap_sched_pointers and valid_sched_pointers\<rbrace>
   tcbSchedDequeue tcbPtr
   \<lbrace>\<lambda>_. sym_heap_sched_pointers\<rbrace>"
  unfolding tcbSchedDequeue_def
  supply projectKOs[simp]
  apply (wpsimp wp: tcbQueueRemove_sym_heap_sched_pointers hoare_vcg_if_lift2 threadGet_wp
              simp: bitmap_fun_defs)
  apply (fastforce simp: ready_queue_relation_def ksReadyQueues_asrt_def inQ_def opt_pred_def
                         opt_map_def obj_at'_def)
  done

crunches setThreadState
  for valid_sched_pointers[wp]: valid_sched_pointers
  and sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  (simp: crunch_simps wp: crunch_wps threadSet_valid_sched_pointers threadSet_sched_pointers)

lemma sts_invs_minor':
  "\<lbrace>st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st
                   \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                      st' \<noteq> Inactive \<and> \<not> idle' st')) t
      and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' st)
      and (\<lambda>s. runnable' st \<and> obj_at' tcbQueued t s \<longrightarrow> st_tcb_at' runnable' t s)
      and sch_act_simple
      and invs'\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  including no_pre
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift irqs_masked_lift
             setThreadState_ct_not_inQ
            | simp add: cteCaps_of_def o_def)+
  apply (clarsimp simp: sch_act_simple_def)
  apply (intro conjI)
       apply clarsimp
      defer
      apply (clarsimp dest!: st_tcb_at_state_refs_ofD'
                      elim!: rsubst[where P=sym_refs]
                     intro!: ext)
      apply (clarsimp elim!: st_tcb_ex_cap'')
    apply fastforce
   apply fastforce
  apply (frule tcb_in_valid_state', clarsimp+)
  by (cases st; simp add: valid_tcb_state'_def split: Structures_H.thread_state.split_asm)

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

lemma sts_st_tcb_at'_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> (P ts \<and> tcb_at' t' s)) \<and> ((t \<noteq> t') \<longrightarrow> st_tcb_at' P t' s)\<rbrace>
     setThreadState ts t
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  apply (wp sts_st_tcb')
  apply fastforce
  done

lemma threadSet_ct_running':
  "(\<And>tcb. tcbState (f tcb) = tcbState tcb) \<Longrightarrow>
  \<lbrace>ct_running'\<rbrace> threadSet f t \<lbrace>\<lambda>rv. ct_running'\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply (wp threadSet_pred_tcb_no_state; simp)
  apply wp
  done

lemma tcbQueuePrepend_tcbPriority_obj_at'[wp]:
  "tcbQueuePrepend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbQueuePrepend_def
  supply projectKOs[simp]
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def objBits_simps ps_clear_def split: if_splits)

lemma tcbQueuePrepend_tcbDomain_obj_at'[wp]:
  "tcbQueuePrepend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  unfolding tcbQueuePrepend_def
  supply projectKOs[simp]
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def objBits_simps ps_clear_def split: if_splits)

lemma tcbSchedDequeue_tcbPriority[wp]:
  "tcbSchedDequeue t \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbSchedDequeue_def tcbQueueRemove_def
  by (wpsimp wp: hoare_when_weak_wp hoare_drop_imps)

lemma tcbSchedDequeue_tcbDomain[wp]:
  "tcbSchedDequeue t \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  unfolding tcbSchedDequeue_def tcbQueueRemove_def
  by (wpsimp wp: hoare_when_weak_wp hoare_drop_imps)

lemma tcbSchedEnqueue_tcbPriority_obj_at'[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbSchedEnqueue_def setQueue_def
  by wpsimp

lemma tcbSchedEnqueue_tcbDomain_obj_at'[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  unfolding tcbSchedEnqueue_def setQueue_def
  by wpsimp

crunches rescheduleRequired
  for tcbPriority_obj_at'[wp]: "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'"
  and tcbDomain_obj_at'[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'"

lemma setThreadState_tcbPriority_obj_at'[wp]:
  "setThreadState ts tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding setThreadState_def
  supply projectKOs[simp]
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce simp: obj_at'_def objBits_simps ps_clear_def)
  done

lemma setThreadState_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_pre)
   apply wps
  apply (simp add: setThreadState_def)
  apply (wpsimp wp: threadSet_ct_idle_or_in_cur_domain' hoare_drop_imps)+
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
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore bit_simps upto0_7_def
            split: if_split_asm)
  done
qed

lemma storeWord_invs_no_cicd'[wp]:
  "\<lbrace>pointerInUserData p and invs_no_cicd'\<rbrace> doMachineOp (storeWord p w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l. l<8 \<Longrightarrow> p && mask 3 = 0 \<Longrightarrow> p + l && ~~ mask 12 = p && ~~ mask 12"
  proof -
    fix l
    assume al: "p && mask 3 = 0"
    assume "(l::machine_word) < 8" hence less: "l<2^3" by simp
    have le: "(3::nat) \<le> 12" by simp
    show "?thesis l"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs_no_cicd' no_irq_storeWord no_irq)
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore upto0_7_def
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

(* the brave can try to move this up to near setObject_update_TCB_corres' *)

definition non_exst_same :: "Structures_H.tcb \<Rightarrow> Structures_H.tcb \<Rightarrow> bool"
where
  "non_exst_same tcb tcb' \<equiv> \<exists>d p ts. tcb' = tcb\<lparr>tcbDomain := d, tcbPriority := p, tcbTimeSlice := ts\<rparr>"

fun non_exst_same' :: "Structures_H.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "non_exst_same' (KOTCB tcb) (KOTCB tcb') = non_exst_same tcb tcb'" |
  "non_exst_same' _ _ = True"

lemma non_exst_same_prio_upd[simp]:
  "non_exst_same tcb (tcbPriority_update f tcb)"
  by (cases tcb, simp add: non_exst_same_def)

lemma non_exst_same_timeSlice_upd[simp]:
  "non_exst_same tcb (tcbTimeSlice_update f tcb)"
  by (cases tcb, simp add: non_exst_same_def)

lemma non_exst_same_domain_upd[simp]:
  "non_exst_same tcb (tcbDomain_update f tcb)"
  by (cases tcb, simp add: non_exst_same_def)

lemma set_eobject_corres':
  assumes e: "etcb_relation etcb tcb'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> KOTCB tcb')) = map_to_ctes (ksPSpace s)"
  shows
    "corres dc
       (tcb_at ptr and is_etcb_at ptr)
       (obj_at' (\<lambda>ko. non_exst_same ko tcb') ptr and obj_at' P ptr
        and obj_at' (\<lambda>tcb. (tcbDomain tcb \<noteq> tcbDomain tcb' \<or> tcbPriority tcb \<noteq> tcbPriority tcb')
                            \<longrightarrow> \<not> tcbQueued tcb) ptr)
       (set_eobject ptr etcb) (setObject ptr tcb')"
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
   apply (clarsimp simp: obj_at'_def)
  apply (unfold set_eobject_def setObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def projectKOs
                        updateObject_default_def in_magnitude_check objBits_simps')
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: obj_at_def is_etcb_at_def)
  apply (simp only: pspace_relation_def dom_fun_upd2 simp_thms)
  apply (elim conjE)
  apply (frule bspec, erule domI)
  apply (rule conjI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: is_other_obj_relation_type)
   apply (drule(1) bspec)
   apply (clarsimp simp: non_exst_same_def)
   apply (case_tac bb; simp)
     apply (clarsimp simp: obj_at'_def other_obj_relation_def tcb_relation_cut_def cte_relation_def
                           tcb_relation_def projectKOs
                     split: if_split_asm)+
   apply (clarsimp simp: aobj_relation_cuts_def split: X64_A.arch_kernel_obj.splits)
   apply (rename_tac arch_kernel_obj obj d p ts)
   apply (case_tac arch_kernel_obj; simp)
     apply (clarsimp simp: pte_relation_def pde_relation_def pdpte_relation_def pml4e_relation_def
                           is_tcb_def
                    split: if_split_asm)+
  apply (extract_conjunct \<open>match conclusion in "ekheap_relation _ _" \<Rightarrow> -\<close>)
   apply (simp only: ekheap_relation_def dom_fun_upd2 simp_thms)
   apply (frule bspec, erule domI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: obj_at'_def)
   apply (insert e)
   apply (clarsimp simp: other_obj_relation_def etcb_relation_def is_other_obj_relation_type
                  split: Structures_A.kernel_object.splits kernel_object.splits arch_kernel_obj.splits)
   apply (frule in_ready_q_tcbQueued_eq[where t=ptr])
  apply (rename_tac s' conctcb' abstcb exttcb)
  apply (clarsimp simp: ready_queues_relation_def Let_def)
  apply (prop_tac "(tcbSchedNexts_of s')(ptr := tcbSchedNext tcb') = tcbSchedNexts_of s'")
   apply (fastforce simp: opt_map_def obj_at'_def non_exst_same_def projectKOs split: option.splits)
  apply (prop_tac "(tcbSchedPrevs_of s')(ptr := tcbSchedPrev tcb') = tcbSchedPrevs_of s'")
   apply (fastforce simp: opt_map_def obj_at'_def non_exst_same_def projectKOs split: option.splits)
  apply (clarsimp simp: ready_queue_relation_def opt_map_def opt_pred_def obj_at'_def inQ_def
                        non_exst_same_def projectKOs
                 split: option.splits)
  apply metis
  done

lemma set_eobject_corres:
  assumes tcbs: "non_exst_same tcb' tcbu'"
  assumes e: "etcb_relation etcb tcb' \<Longrightarrow> etcb_relation etcbu tcbu'"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF tcbu' = getF tcb'"
  assumes r: "r () ()"
  shows
    "corres r
       (tcb_at add and (\<lambda>s. ekheap s add = Some etcb))
       (ko_at' tcb' add
        and obj_at' (\<lambda>tcb. (tcbDomain tcb \<noteq> tcbDomain tcbu' \<or> tcbPriority tcb \<noteq> tcbPriority tcbu')
                           \<longrightarrow> \<not> tcbQueued tcb) add)
       (set_eobject add etcbu) (setObject add tcbu')"
  apply (rule_tac F="non_exst_same tcb' tcbu' \<and> etcb_relation etcbu tcbu'" in corres_req)
   apply (clarsimp simp: state_relation_def obj_at_def obj_at'_def)
   apply (frule(1) pspace_relation_absD)
   apply (clarsimp simp: projectKOs other_obj_relation_def ekheap_relation_def e tcbs)
   apply (drule bspec, erule domI)
   apply (clarsimp simp: e)
  apply (erule conjE)
  apply (rule corres_guard_imp)
    apply (rule corres_rel_imp)
     apply (rule set_eobject_corres'[where P="(=) tcb'"])
      apply simp
     defer
    apply (simp add: r)
   apply (fastforce simp: is_etcb_at_def elim!: obj_at_weakenE)
   apply (subst(asm) eq_commute)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: projectKOs obj_at'_def objBits_simps)
  apply (subst map_to_ctes_upd_tcb, assumption+)
   apply (simp add: ps_clear_def3 field_simps objBits_defs mask_def)
  apply (subst if_not_P)
   apply (fastforce dest: bspec [OF tables', OF ranI])
  apply simp
  done

lemma ethread_set_corresT:
  assumes x: "\<And>tcb'. non_exst_same tcb' (f' tcb')"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (f' tcb) = getF tcb"
  assumes e: "\<And>etcb tcb'. etcb_relation etcb tcb' \<Longrightarrow> etcb_relation (f etcb) (f' tcb')"
  shows
    "corres dc
       (tcb_at t and valid_etcbs)
       (tcb_at' t
        and obj_at' (\<lambda>tcb. (tcbDomain tcb \<noteq> tcbDomain (f' tcb)
                             \<or> tcbPriority tcb \<noteq> tcbPriority (f' tcb))
                           \<longrightarrow> \<not> tcbQueued tcb) t)
       (ethread_set f t) (threadSet f' t)"
  apply (simp add: ethread_set_def threadSet_def bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_get_etcb set_eobject_corres])
         apply (rule x)
        apply (erule e)
       apply (simp add: z)+
     apply (wp getObject_tcb_wp)+
   apply clarsimp
   apply (simp add: valid_etcbs_def tcb_at_st_tcb_at[symmetric])
   apply (force simp: tcb_at_def get_etcb_def obj_at_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas ethread_set_corres =
    ethread_set_corresT [OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

end
end
