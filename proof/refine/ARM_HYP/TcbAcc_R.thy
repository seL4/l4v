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
  "\<lbrakk> valid_bitmapQ s \<rbrakk> \<Longrightarrow>
   bitmapQ d p s = (ksReadyQueues s (d, p) \<noteq> [])"
   unfolding valid_bitmapQ_def
   by simp

lemma prioToL1Index_l1IndexToPrio_or_id:
  "\<lbrakk> unat (w'::priority) < 2 ^ wordRadix ; w < size w' \<rbrakk>
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
  valid_queues_no_bitmap_except :: "word32 \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "valid_queues_no_bitmap_except t' \<equiv> \<lambda>s.
   (\<forall>d p. (\<forall>t \<in> set (ksReadyQueues s (d, p)). t \<noteq> t' \<longrightarrow> obj_at' (inQ d p and runnable' \<circ> tcbState) t s)
    \<and>  distinct (ksReadyQueues s (d, p))
    \<and> (d > maxDomain \<or> p > maxPriority \<longrightarrow> ksReadyQueues s (d,p) = []))"

lemma valid_queues_no_bitmap_exceptI[intro]:
  "valid_queues_no_bitmap s \<Longrightarrow> valid_queues_no_bitmap_except t s"
  unfolding valid_queues_no_bitmap_except_def valid_queues_no_bitmap_def
  by simp

lemma st_tcb_at_coerce_abstract:
  assumes t: "st_tcb_at' P t c"
  assumes sr: "(a, c) \<in> state_relation"
  shows "st_tcb_at (\<lambda>st. \<exists>st'. thread_state_relation st st' \<and> P st') t a"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def
                        projectKOs objBits_simps)
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply (clarsimp simp: st_tcb_at_def obj_at_def other_obj_relation_def
                        tcb_relation_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        ARM_A.arch_kernel_obj.split_asm)+
  apply fastforce
  done

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

lemma valid_objs_valid_tcbE: "\<And>s t.\<lbrakk> valid_objs' s; tcb_at' t s; \<And>tcb. valid_tcb' tcb s \<Longrightarrow> R s tcb \<rbrakk> \<Longrightarrow> obj_at' (R s) t s"
  apply (clarsimp simp add: projectKOs valid_objs'_def ran_def typ_at'_def
                            ko_wp_at'_def valid_obj'_def valid_tcb'_def obj_at'_def)
  apply (fastforce simp: projectKO_def projectKO_opt_tcb return_def valid_tcb'_def)
  done

lemma valid_objs'_maxDomain:
  "\<And>s t. \<lbrakk> valid_objs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t s"
  apply (erule (1) valid_objs_valid_tcbE)
  apply (clarsimp simp: valid_tcb'_def)
  done

lemma valid_objs'_maxPriority:
  "\<And>s t. \<lbrakk> valid_objs' s; tcb_at' t s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t s"
  apply (erule (1) valid_objs_valid_tcbE)
  apply (clarsimp simp: valid_tcb'_def)
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

lemma setObject_update_TCB_corres':
  assumes tcbs: "tcb_relation tcb tcb' \<Longrightarrow> tcb_relation tcbu tcbu'"
  assumes tables: "\<forall>(getF, v) \<in> ran tcb_cap_cases. getF tcbu = getF tcb"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF tcbu' = getF tcb'"
  assumes r: "r () ()"
  assumes exst: "exst_same tcb' tcbu'"
  shows "corres r (ko_at (TCB tcb) add)
                  (ko_at' tcb' add)
                  (set_object add (TCB tcbu)) (setObject add tcbu')"
  apply (rule_tac F="tcb_relation tcb tcb' \<and> exst_same tcb' tcbu'" in corres_req)
   apply (clarsimp simp: state_relation_def obj_at_def obj_at'_def)
   apply (frule(1) pspace_relation_absD)
   apply (clarsimp simp: projectKOs other_obj_relation_def exst)
  apply (rule corres_guard_imp)
    apply (rule corres_rel_imp)
     apply (rule setObject_other_corres[where P="(=) tcb'"])
           apply (rule ext)+
           apply simp
          defer
          apply (simp add: is_other_obj_relation_type_def
                           projectKOs objBits_simps'
                           other_obj_relation_def tcbs r)+
    apply (fastforce elim!: obj_at_weakenE dest: bspec[OF tables])
   apply (subst(asm) eq_commute, assumption)
  apply (clarsimp simp: projectKOs obj_at'_def objBits_simps)
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
     r () (); exst_same tcb' tcbu'\<rbrakk>
   \<Longrightarrow> corres r (\<lambda>s. get_tcb add s = Some tcb)
               (\<lambda>s'. (tcb', s') \<in> fst (getObject add s'))
               (set_object add (TCB tcbu)) (setObject add tcbu')"
  apply (rule corres_guard_imp)
    apply (erule (3) setObject_update_TCB_corres', force)
   apply fastforce
  apply (clarsimp simp: getObject_def in_monad split_def obj_at'_def
                        loadObject_default_def projectKOs objBits_simps'
                        in_magnitude_check)
  done

lemma getObject_TCB_corres:
  "corres tcb_relation (tcb_at t) (tcb_at' t)
          (gets_the (get_tcb t)) (getObject t)"
  apply (rule corres_guard_imp)
    apply (rule corres_gets_the)
    apply (rule corres_get_tcb)
   apply (simp add: tcb_at_def)
  apply assumption
  done

lemma threadGet_corres:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> r (f tcb) (f' tcb')"
  shows      "corres r (tcb_at t) (tcb_at' t) (thread_get f t) (threadGet f' t)"
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
  "\<lbrakk> \<And>a b c d e f g h i j k l m n p q. P (Thread a b c d e f g h i j k l m n p q) \<rbrakk> \<Longrightarrow> \<forall>tcb. P tcb"
  by (rule allI, case_tac tcb, simp)

lemma threadset_corresT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation (f tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  assumes e: "\<And>tcb'. exst_same tcb' (f' tcb')"
  shows      "corres dc (tcb_at t)
                        (tcb_at' t)
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
      apply (rule e)
     apply wp+
   apply (clarsimp simp add: tcb_at_def obj_at_def)
   apply (drule get_tcb_SomeD)
   apply fastforce
  apply simp
  done

lemmas threadset_corres =
    threadset_corresT [OF _ _ all_tcbI, OF _ ball_tcb_cap_casesI ball_tcb_cte_casesI]

lemma pspace_relation_tcb_at:
  assumes p: "pspace_relation (kheap a) (ksPSpace c)"
  assumes t: "tcb_at' t c"
  shows "tcb_at t a" using assms
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE)
  apply (clarsimp simp: other_obj_relation_def is_tcb obj_at_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        ARM_A.arch_kernel_obj.split_asm)+
  done

lemma threadSet_corres_noopT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation tcb (fn tcb')"
  assumes y: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (fn tcb) = getF tcb"
  assumes e: "\<And>tcb'. exst_same tcb' (fn tcb')"
  shows      "corres dc \<top> (tcb_at' t)
                           (return v) (threadSet fn t)"
proof -
  have S: "\<And>t s. tcb_at t s \<Longrightarrow> return v s = (thread_set id t >>= (\<lambda>x. return v)) s"
    apply (clarsimp simp: tcb_at_def)
    apply (simp add: return_def thread_set_def gets_the_def assert_def
                     assert_opt_def simpler_gets_def set_object_def get_object_def
                     put_def get_def bind_def)
    apply (subgoal_tac "(kheap s)(t \<mapsto> TCB tcb) = kheap s")
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
          apply (rule e)
         apply (rule corres_noop [where P=\<top> and P'=\<top>])
          apply wpsimp+
      apply (erule pspace_relation_tcb_at[rotated])
      apply clarsimp
     apply simp
    apply simp
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
  shows      "corres r P (tcb_at' t and P')
                           m (threadSet fn t >>= (\<lambda>rv. m'))"
  apply (rule corres_guard_imp)
    apply (subst return_bind[symmetric])
    apply (rule corres_split_nor[OF threadSet_corres_noopT])
         apply (simp add: x)
        apply (rule y)
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
  apply (wpsimp wp: valid_arch_state_lift' setObject_typ_at' setObject_ko_wp_at
              simp: objBits_simps', rule refl; simp add: pred_conj_def)
  apply (clarsimp simp: is_vcpu'_def ko_wp_at'_def obj_at'_def projectKOs)
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

  assumes y: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
                      \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes u: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes w: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  assumes w': "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  assumes v': "\<forall>tcb s. valid_arch_tcb' (tcbArch tcb) s \<longrightarrow> valid_arch_tcb' (tcbArch (F tcb)) s"
  shows
  "\<lbrace>valid_pspace' and (\<lambda>s. P \<longrightarrow> st_tcb_at' Q t s \<and> bound_tcb_at' Q' t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def threadSet_def)
  apply (rule hoare_pre,
         wp setObject_tcb_valid_objs getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def
                            bspec_split [OF spec [OF x]] z
                            split_paired_Ball y u w v w' v')
  done

lemmas threadSet_valid_pspace'T =
    threadSet_valid_pspace'T_P[where P=False, simplified]

lemmas threadSet_valid_pspace' =
    threadSet_valid_pspace'T [OF all_tcbI all_tcbI all_tcbI all_tcbI _ _ _ all_tcbI, OF ball_tcb_cte_casesI]

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

lemma threadSet_state_hyp_refs_of':
  assumes y: "\<And>tcb. atcbVCPUPtr (tcbArch (F tcb)) = atcbVCPUPtr (tcbArch tcb)"
  shows      "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wpsimp wp: setObject_state_hyp_refs_of' getObject_tcb_wp
    simp: objBits_simps' obj_at'_def projectKOs state_hyp_refs_of'_def)
  apply (clarsimp simp:objBits_simps' y state_hyp_refs_of'_def
                 elim!: rsubst[where P=P] intro!: ext)+
  done

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
      \<and> ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and>((\<exists>tcb. \<not> bound (atcbVCPUPtr (tcbArch tcb)) \<and> bound (atcbVCPUPtr (tcbArch (F tcb)))
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_iflive' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs live'_def hyp_live'_def)
  apply (subst conj_assoc[symmetric], subst imp_disjL[symmetric])+
  apply (rule conjI)
   apply (rule impI, clarsimp)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def live'_def hyp_live'_def)
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
   apply (rule setObject_cte_wp_at2')
    apply (clarsimp simp: updateObject_default_def projectKOs in_monad
                          obj_at'_def objBits_simps' in_magnitude_check prod_eq_iff)
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

lemma threadSet_valid_queues_no_bitmap:
  "\<lbrace> valid_queues_no_bitmap and
    (\<lambda>s. \<forall>d p. (\<exists>tcb. (inQ d p tcb \<and> runnable' (tcbState tcb)) \<and>
                     \<not>(inQ d p (f tcb) \<and> runnable' (tcbState (f tcb))))
                \<longrightarrow> obj_at' (\<lambda>tcb. (inQ d p tcb \<and> runnable' (tcbState tcb)) \<and>
                                 \<not>(inQ d p (f tcb) \<and> runnable' (tcbState (f tcb)))) t s
                \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p))
    )\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. valid_queues_no_bitmap \<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: Invariants_H.valid_queues_no_bitmap_def' pred_tcb_at'_def)

   apply (wp setObject_queues_unchanged_tcb
             hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_queues_no_bitmap_def' pred_tcb_at'_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (fastforce)
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

lemma threadSet_valid_queues:
  "\<lbrace>Invariants_H.valid_queues and
    (\<lambda>s. \<forall>d p. (\<exists>tcb. (inQ d p tcb \<and> runnable' (tcbState tcb)) \<and>
                     \<not>(inQ d p (f tcb) \<and> runnable' (tcbState (f tcb))))
                \<longrightarrow> obj_at' (\<lambda>tcb. (inQ d p tcb \<and> runnable' (tcbState tcb)) \<and>
                                 \<not>(inQ d p (f tcb) \<and> runnable' (tcbState (f tcb)))) t s
                \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p))
    )\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  unfolding valid_queues_def
  by (wp threadSet_valid_queues_no_bitmap;simp)

definition
  addToQs :: "(Structures_H.tcb \<Rightarrow> Structures_H.tcb)
                       \<Rightarrow> word32 \<Rightarrow> (domain \<times> priority \<Rightarrow> word32 list)
                       \<Rightarrow> (domain \<times> priority \<Rightarrow> word32 list)"
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
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs
                        objBits_simps addToQs_set_def
             split del: if_split cong: if_cong)
  apply (fastforce simp: projectKOs split: if_split_asm)
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
  (simp: unless_def crunch_simps)

crunch ksInterrupt'[wp]: threadSet "\<lambda>s. P (ksInterruptState s)"
  (wp: setObject_ksInterrupt updateObject_default_inv)

lemma threadSet_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> threadSet t F \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: threadSet_def, wp setObject_typ_at')

lemmas threadSet_typ_at_lifts[wp] = typ_at_lifts [OF threadSet_typ_at']

lemma setObject_tcb_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setObject p (tcb :: tcb) \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp valid_pde_mappings_lift' setObject_typ_at')
  apply (rule obj_at_setObject2)
  apply (auto dest: updateObject_default_result)
  done

crunches threadSet
  for irq_states' [wp]: valid_irq_states'
  and pde_mappings' [wp]: valid_pde_mappings'
  and pspace_domain_valid [wp]: pspace_domain_valid

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

lemma threadSet_invs_trivialT:
  assumes x: "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  assumes z: "\<forall>tcb. tcbState (F tcb) = tcbState tcb \<and> tcbDomain (F tcb) = tcbDomain tcb"
  assumes w: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes a: "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
  assumes w: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes v: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes u: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  assumes b: "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
  assumes r: "\<forall>tcb. atcbVCPUPtr (tcbArch (F tcb)) = atcbVCPUPtr (tcbArch tcb)"
  shows
  "\<lbrace>\<lambda>s. invs' s \<and>
       tcb_at' t s \<and>
       (\<forall>d p. (\<exists>tcb. inQ d p tcb \<and> \<not> inQ d p (F tcb)) \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p))) \<and>
       (\<forall>ko d p. ko_at' ko t s \<and> inQ d p (F ko) \<and> \<not> inQ d p ko \<longrightarrow> t \<in> set (ksReadyQueues s (d, p))) \<and>
       ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)) \<longrightarrow> ex_nonz_cap_to' t s \<and> t \<noteq> ksCurThread s) \<and>
       (\<forall>tcb. tcbQueued (F tcb) \<and> ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> tcbQueued tcb \<or> t \<noteq> ksCurThread s)\<rbrace>
   threadSet F t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  from z have domains: "\<And>tcb. tcbDomain (F tcb) = tcbDomain tcb" by blast
  note threadSet_sch_actT_P[where P=False, simplified]
  have y: "\<forall>tcb. tcb_st_refs_of' (tcbState (F tcb)) = tcb_st_refs_of' (tcbState tcb) \<and>
                 valid_tcb_state' (tcbState (F tcb)) = valid_tcb_state' (tcbState tcb)"
    by (auto simp: z)
  show ?thesis
    apply (simp add: invs'_def valid_state'_def split del: if_split)
    apply (rule hoare_pre)
     apply (wp x w v u b
              threadSet_valid_pspace'T
              threadSet_sch_actT_P[where P=False, simplified]
              threadSet_valid_queues
              threadSet_state_refs_of'T[where f'=id]
              threadSet_state_hyp_refs_of'
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
           |clarsimp simp: y z a r domains cteCaps_of_def valid_arch_tcb'_def|rule refl)+
   apply (clarsimp simp: obj_at'_def projectKOs pred_tcb_at'_def)
   apply (clarsimp simp: cur_tcb'_def valid_irq_node'_def valid_queues'_def o_def)
  apply (fastforce simp: domains ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def z a)
  done
qed

lemmas threadSet_invs_trivial =
    threadSet_invs_trivialT [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma zobj_refs'_capRange:
  "s \<turnstile>' cap \<Longrightarrow> zobj_refs' cap \<subseteq> capRange cap"
  apply (cases cap; simp add: valid_cap'_def capAligned_def capRange_def is_aligned_no_overflow
                       split: arch_capability.splits)
  apply clarsimp
  apply (drule is_aligned_no_overflow)
  apply simp
  done

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

lemma asUser_corres':
  assumes y: "corres_underlying Id False True r \<top> \<top> f g"
  shows      "corres r (tcb_at t)
                       (tcb_at' t)
                       (as_user t f) (asUser t g)"
  proof -
  note arch_tcb_context_get_def[simp]
  note atcbContextGet_def[simp]
  note arch_tcb_context_set_def[simp]
  note atcbContextSet_def[simp]
  have L1: "corres (\<lambda>tcb con. (arch_tcb_context_get o tcb_arch) tcb = con)
             (tcb_at t) (tcb_at' t)
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
  shows      "corres r (tcb_at t and invs) (tcb_at' t and invs') (as_user t f) (asUser t g)"
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
 "corres (=) (tcb_at t) (tcb_at' t)
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
  apply (wp threadSet_invs_trivial hoare_drop_imps | simp add: atcbContextSet_def)+
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
             | simp add: valid_tcb'_def tcb_cte_cases_def
                         valid_arch_tcb'_def atcbContextSet_def)+
  done

lemma asUser_valid_pspace'[wp]:
  "\<lbrace>valid_pspace'\<rbrace> asUser t m \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_valid_pspace' hoare_drop_imps
             | simp add: atcbContextSet_def valid_arch_tcb'_def)+
  done

lemma asUser_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> asUser t m \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+

  apply (wp threadSet_valid_queues hoare_drop_imps | simp)+
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

lemma asUser_st_hyp_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
     asUser t m
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_state_hyp_refs_of' hoare_drop_imps | simp add: atcbContextSet_def atcbVCPUPtr_atcbContext_update)+
  done

lemma asUser_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> asUser t m \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wpsimp wp: threadSet_iflive' hoare_drop_imps
         simp: atcbContextGet_def threadGet_def getObject_def split_def loadObject_default_def projectKO_def2)+
  apply (auto simp: atcbContextSet_def atcbVCPUPtr_atcbContext_update)
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
  "corres dc (tcb_at t)
             (tcb_at' t)
             (as_user t (setRegister r v))
             (asUser t (setRegister r v))"
  apply (simp add: setRegister_def)
  apply (rule asUser_corres')
  apply (rule corres_modify'; simp)
  done

lemma getThreadState_corres:
  "corres thread_state_relation (tcb_at t) (tcb_at' t)
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
  "corres (=) (tcb_at t) (tcb_at' t)
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

lemma get_tcb_corres:
  "corres tcb_relation (tcb_at t) (tcb_at' t) (gets_the (get_tcb t)) (getObject t)"
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp add: gets_def
                            get_def return_def bind_def get_tcb_def
                            gets_the_def assert_opt_def)
  apply (frule in_inv_by_hoareD [OF getObject_inv_tcb])
  apply (clarsimp simp add: obj_at_def is_tcb obj_at'_def projectKO_def
                            projectKO_opt_tcb split_def
                            getObject_def loadObject_default_def in_monad
                     split: option.split_asm)
  apply (clarsimp simp add: return_def in_magnitude_check objBits_simps
                            state_relation_def
                     split: kernel_object.split_asm)
  apply (frule(1) pspace_relation_absD)
  apply (clarsimp simp add: other_obj_relation_def)
  done

lemma no_fail_getQueue [wp]:
  "no_fail \<top> (getQueue d p)"
  by (simp add: getQueue_def)

lemma no_fail_setQueue [wp]:
  "no_fail \<top> (setQueue d p xs)"
  by (simp add: setQueue_def)

lemma in_magnitude_check':
  "\<lbrakk> is_aligned x n; (1 :: word32) < 2 ^ n; ksPSpace s x = Some y; ps = ksPSpace s \<rbrakk>
     \<Longrightarrow> ((v, s') \<in> fst (magnitudeCheck x (snd (lookupAround2 x ps)) n s)) =
        (s' = s \<and> ps_clear x n s)"
  by (simp add: in_magnitude_check)

lemma setObject_tcb_tcb' [wp]:
  "\<lbrace>tcb_at' t\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  apply (rule obj_at_setObject1)
    apply (simp add: updateObject_default_def in_monad)
   apply (simp add: projectKOs)
  apply (simp add: objBits_simps)
  done


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

lemma setQueue_corres:
  "corres dc \<top> \<top> (set_tcb_queue d p q) (setQueue d p q)"
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp: setQueue_def in_monad set_tcb_queue_def return_def simpler_modify_def)
  apply (fastforce simp: state_relation_def ready_queues_relation_def)
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

crunch typ_at'[wp]: addToBitmap "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps setCTE_typ_at')

crunch typ_at'[wp]: removeFromBitmap "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps setCTE_typ_at')

lemmas addToBitmap_typ_ats [wp] = typ_at_lifts [OF addToBitmap_typ_at']
lemmas removeFromBitmap_typ_ats [wp] = typ_at_lifts [OF removeFromBitmap_typ_at']

lemma tcbSchedEnqueue_corres:
  "corres dc (is_etcb_at t) (tcb_at' t and Invariants_H.valid_queues and valid_queues')
             (tcb_sched_action (tcb_sched_enqueue) t) (tcbSchedEnqueue t)"
proof -
  have ready_queues_helper:
    "\<And>t tcb a b. \<lbrakk> ekheap a t = Some tcb;  obj_at' tcbQueued t b  ;  valid_queues' b  ;
                   ekheap_relation (ekheap a) (ksPSpace b) \<rbrakk>
                 \<Longrightarrow> t \<in> set (ksReadyQueues b (tcb_domain tcb, tcb_priority tcb))"
  unfolding valid_queues'_def
  by (fastforce dest: ekheap_relation_absD simp: obj_at'_def inQ_def etcb_relation_def projectKO_eq projectKO_tcb)

  show ?thesis unfolding tcbSchedEnqueue_def tcb_sched_action_def
    apply (rule corres_symb_exec_r [OF _ _ threadGet_inv,
             where Q'="\<lambda>rv. tcb_at' t and Invariants_H.valid_queues and valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
      defer
      apply (wp threadGet_obj_at'; simp_all)
     apply (rule no_fail_pre, wp, blast)
    apply (case_tac queued; simp_all)
     apply (rule corres_no_failI; simp add: no_fail_return)
     apply (clarsimp simp: in_monad ethread_get_def gets_the_def bind_assoc
                           assert_opt_def exec_gets is_etcb_at_def get_etcb_def get_tcb_queue_def
                           set_tcb_queue_def simpler_modify_def ready_queues_relation_def
                           state_relation_def tcb_sched_enqueue_def)
     apply (rule ready_queues_helper; auto)
    apply (clarsimp simp: when_def)
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
               apply (simp add: tcb_sched_enqueue_def split del: if_split)
               apply (rule_tac P=\<top> and Q="K (t \<notin> set queuea)" in corres_assume_pre)
               apply simp
               apply (rule setQueue_corres[unfolded dc_def])
              apply (rule corres_split_noop_rhs2)
                 apply (fastforce intro: addToBitmap_noop_corres)
                apply (fastforce intro: threadSet_corres_noop simp: tcb_relation_def exst_same_def)
               apply (wp getObject_tcb_wp  | simp add: threadGet_def)+
    apply (fastforce simp: valid_queues_def valid_queues_no_bitmap_def obj_at'_def inQ_def
                           projectKO_eq project_inject)
    done
qed

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
  "corres dc (weak_valid_sched_action and valid_etcbs) (Invariants_H.valid_queues and valid_queues' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
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
          apply (rule tcbSchedEnqueue_corres)
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
crunch pred_tcb_at'[wp]: removeFromBitmap "pred_tcb_at' proj P t"

crunch not_st_tcb_at'[wp]: removeFromBitmap "\<lambda>s. \<not> (st_tcb_at' P' t) s"
crunch not_pred_tcb_at'[wp]: removeFromBitmap "\<lambda>s. \<not> (pred_tcb_at' proj P' t) s"

crunch st_tcb_at'[wp]: addToBitmap "st_tcb_at' P' t"
crunch pred_tcb_at'[wp]: addToBitmap "pred_tcb_at' proj P' t"

crunch not_st_tcb_at'[wp]: addToBitmap "\<lambda>s. \<not> (st_tcb_at' P' t) s"
crunch not_pred_tcb_at'[wp]: addToBitmap "\<lambda>s. \<not> (pred_tcb_at' proj P' t) s"

crunch obj_at'[wp]: removeFromBitmap "obj_at' P t"

crunch obj_at'[wp]: addToBitmap "obj_at' P t"

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
  "corres dc (is_etcb_at t) (tcb_at' t and Invariants_H.valid_queues)
             (tcb_sched_action tcb_sched_dequeue t) (tcbSchedDequeue t)"
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
   apply (clarsimp simp: in_monad ethread_get_def set_tcb_queue_def is_etcb_at_def state_relation_def)
   apply (subgoal_tac "t \<notin> set (ready_queues a (tcb_domain y) (tcb_priority y))")
    prefer 2
    subgoal by (force simp: tcb_sched_dequeue_def Invariants_H.valid_queues_def valid_queues_no_bitmap_def
                            ready_queues_relation_def obj_at'_def inQ_def projectKO_eq project_inject)
   apply (subst gets_the_exec)
    apply (simp add: get_etcb_def)
   apply (subst gets_the_exec)
    apply (simp add: get_etcb_def)
   apply (simp add: exec_gets simpler_modify_def get_etcb_def ready_queues_relation_def cong: if_cong get_tcb_queue_def)
  apply (simp add: when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)"])
       apply (rule ethreadget_corres, simp add: etcb_relation_def)
      apply (rule corres_split[where r'="(=)"])
         apply (rule ethreadget_corres, simp add: etcb_relation_def)
        apply (rule corres_split[where r'="(=)"])
           apply (simp, rule getQueue_corres)
          apply (rule corres_split_noop_rhs2)
             apply (simp add: tcb_sched_dequeue_def)
             apply (rule setQueue_corres)
            apply (rule corres_split_noop_rhs)
              apply (clarsimp, rule removeFromBitmap_corres_noop)
             apply (rule threadSet_corres_noop; simp_all add: tcb_relation_def exst_same_def)
            apply (wp | simp)+
  done

lemma thread_get_test: "do cur_ts \<leftarrow> get_thread_state cur; g (test cur_ts) od =
       do t \<leftarrow> (thread_get (\<lambda>tcb. test (tcb_state tcb)) cur); g t od"
  apply (simp add: get_thread_state_def thread_get_def)
  done

lemma thread_get_isRunnable_corres: "corres (=) (tcb_at t) (tcb_at' t) (thread_get (\<lambda>tcb. runnable (tcb_state tcb)) t) (isRunnable t)"
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
          (tcb_at t)
          (tcb_at' t)
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
          (tcb_at t)
          (tcb_at' t)
          (set_bound_notification t ntfn) (setBoundNotification ntfn t)"
  apply (simp add: set_bound_notification_def setBoundNotification_def)
  apply (subst thread_set_def[simplified, symmetric])
  apply (rule threadset_corres, simp_all add:tcb_relation_def exst_same_def)
  done

crunches rescheduleRequired, tcbSchedDequeue, setThreadState, setBoundNotification
  for tcb'[wp]: "tcb_at' addr"

crunches rescheduleRequired, removeFromBitmap
  for valid_objs'[wp]: valid_objs'
  (simp: crunch_simps)

lemma tcbSchedDequeue_valid_objs' [wp]: "\<lbrace> valid_objs' \<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_objs' \<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wp threadSet_valid_objs')
        apply (clarsimp simp add: valid_tcb'_def tcb_cte_cases_def)
        apply wp
       apply (simp add: if_apply_def2)
       apply (wp hoare_drop_imps)
       apply (wp | simp cong: if_cong add: valid_tcb'_def tcb_cte_cases_def if_apply_def2)+
  done

lemma sts_valid_objs':
  "\<lbrace>valid_objs' and valid_tcb_state' st\<rbrace>
  setThreadState st t
  \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setThreadState_def setQueue_def isRunnable_def isStopped_def)
  apply (wp threadSet_valid_objs')
     apply (simp add: valid_tcb'_def tcb_cte_cases_def)
     apply (wp threadSet_valid_objs' | simp)+
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def)
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

crunch ct[wp]: setQueue "\<lambda>s. P (ksCurThread s)"

crunch cur_domain[wp]: setQueue "\<lambda>s. P (ksCurDomain s)"

crunch ct'[wp]: addToBitmap "\<lambda>s. P (ksCurThread s)"
crunch ct'[wp]: removeFromBitmap "\<lambda>s. P (ksCurThread s)"

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

lemma tcbSchedEnqueue_pred_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. pred_tcb_at' proj P' t' s \<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. pred_tcb_at' proj P' t' s\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def when_def unless_def)
  apply (wp threadSet_pred_tcb_no_state crunch_wps | clarsimp simp: tcb_to_itcb'_def)+
  done

lemma tcbSchedDequeue_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  unfolding tcbSchedDequeue_def
  by (wp setQueue_sch_act | wp sch_act_wf_lift | simp add: if_apply_def2)+

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
  by (simp add: tcbSchedEnqueue_def unless_def)
     (wp setQueue_sch_act | wp sch_act_wf_lift  | clarsimp)+

lemma tcbSchedEnqueue_weak_sch_act[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp setQueue_sch_act threadSet_weak_sch_act_wf | clarsimp)+
  done

lemma threadGet_wp: "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (\<exists>tcb. ko_at' tcb t s \<and> P (f tcb) s)\<rbrace> threadGet f t \<lbrace>P\<rbrace>"
  apply (simp add: threadGet_def)
  apply (wp getObject_tcb_wp)
  apply clarsimp
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
  "((2 :: 32 word) ^ prioToL1Index p) !! prioToL1Index p"
 using l2BitmapSize_def'
 by (fastforce simp: nth_w2p_same intro: order_less_le_trans[OF prioToL1Index_size])

lemma prioL2Index_bit_set:
  fixes p :: priority
  shows "((2::32 word) ^ unat (p && mask wordRadix)) !! unat (p && mask wordRadix)"
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

  show ?thesis
  unfolding removeFromBitmap_def
  supply bit_not_iff[simp del] bit_not_exp_iff[simp del]
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
        apply (simp add: wordRadix_def' word_size)+
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
  apply wpsimp
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

lemma valid_queues_no_bitmap_objD:
  "\<lbrakk> valid_queues_no_bitmap s; t \<in> set (ksReadyQueues s (d, p))\<rbrakk>
   \<Longrightarrow> obj_at' (inQ d p and runnable' \<circ> tcbState) t s"
   unfolding valid_queues_no_bitmap_def
   by blast

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

lemma tcbSchedEnqueueOrAppend_valid_queues:
  (* f is either (t#ts) or (ts @ [t]), so we define its properties generally *)
  assumes f_set[simp]: "\<And>ts. t \<in> set (f ts)"
  assumes f_set_insert[simp]: "\<And>ts. set (f ts) = insert t (set ts)"
  assumes f_not_empty[simp]: "\<And>ts. f ts \<noteq> []"
  assumes f_distinct: "\<And>ts. \<lbrakk> distinct ts ; t \<notin> set ts \<rbrakk> \<Longrightarrow> distinct (f ts)"
  shows "\<lbrace>Invariants_H.valid_queues and st_tcb_at' runnable' t and valid_objs' \<rbrace>
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
    \<lambda>d p t. obj_at' (\<lambda>tcb. inQ d p (tcbQueued_update (\<lambda>_. True) tcb) \<and> runnable' (tcbState tcb)) t"

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
    by (wp, auto intro: f_distinct)

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
     apply (wp setObject_queues_unchanged_tcb hoare_Ball_helper hoare_vcg_all_lift
               setObject_tcb_strongest)
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
  apply (frule pred_tcb_at')
  apply (frule (1) valid_objs'_maxDomain)
  apply (frule (1) valid_objs'_maxPriority)
  apply (clarsimp simp: valid_queues_def st_tcb_at'_def obj_at'_def valid_queues_no_bitmap_exceptI)
  apply (fastforce dest!: valid_queues_no_bitmap_objD simp: obj_at'_def inQ_def could_run_def)
  done
qed

lemma tcbSchedEnqueue_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues
    and st_tcb_at' runnable' t
    and valid_objs' \<rbrace>
     tcbSchedEnqueue t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
   unfolding tcbSchedEnqueue_def
   by (fastforce intro:  tcbSchedEnqueueOrAppend_valid_queues)

lemma tcbSchedAppend_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues
    and st_tcb_at' runnable' t
    and valid_objs' \<rbrace>
     tcbSchedAppend t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
   unfolding tcbSchedAppend_def
   by (fastforce intro:  tcbSchedEnqueueOrAppend_valid_queues)

lemma rescheduleRequired_valid_queues[wp]:
  "\<lbrace>\<lambda>s. Invariants_H.valid_queues s \<and> valid_objs' s \<and>
        weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp)+
  apply (fastforce simp: weak_sch_act_wf_def elim: valid_objs'_maxDomain valid_objs'_maxPriority)
  done

lemma rescheduleRequired_valid_queues_sch_act_simple:
  "\<lbrace>Invariants_H.valid_queues and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp | fastforce simp: Invariants_H.valid_queues_def sch_act_simple_def)+
  done

lemma rescheduleRequired_valid_bitmapQ_sch_act_simple:
  "\<lbrace> valid_bitmapQ and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  including classic_wp_pre
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
  including classic_wp_pre
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
  including classic_wp_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. bitmapQ_no_L2_orphans s \<and>
                            (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)" in hoare_seq_ext)
   apply wpsimp
   apply (case_tac x; simp)
  apply (wp, fastforce)
  done

lemma sts_valid_bitmapQ_sch_act_simple:
  "\<lbrace>valid_bitmapQ and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_. valid_bitmapQ \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_valid_bitmapQ_sch_act_simple
            threadSet_valid_bitmapQ [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

lemma sts_valid_bitmapQ_no_L2_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L2_orphans and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_bitmapQ_no_L2_orphans_sch_act_simple
            threadSet_valid_bitmapQ_no_L2_orphans [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

lemma sts_valid_bitmapQ_no_L1_orphans_sch_act_simple:
  "\<lbrace> bitmapQ_no_L1_orphans and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_bitmapQ_no_L1_orphans_sch_act_simple
            threadSet_valid_bitmapQ_no_L1_orphans [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

lemma sts_valid_queues:
  "\<lbrace>\<lambda>s. Invariants_H.valid_queues s \<and>
    ((\<exists>p. t \<in> set(ksReadyQueues s p)) \<longrightarrow> runnable' st)\<rbrace>
   setThreadState st t \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_valid_queues_sch_act_simple
            threadSet_valid_queues [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

lemma sbn_valid_queues:
  "\<lbrace>\<lambda>s. Invariants_H.valid_queues s\<rbrace>
   setBoundNotification ntfn t \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_queues [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done



lemma addToBitmap_valid_queues'[wp]:
  "\<lbrace> valid_queues' \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. valid_queues' \<rbrace>"
  unfolding valid_queues'_def addToBitmap_def
            modifyReadyQueuesL1Bitmap_def modifyReadyQueuesL2Bitmap_def
            getReadyQueuesL1Bitmap_def getReadyQueuesL2Bitmap_def
  by (wp, simp)

lemma tcbSchedEnqueue_valid_queues'[wp]:
  "\<lbrace>valid_queues' and st_tcb_at' runnable' t \<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
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
        apply (clarsimp simp: valid_queues'_def obj_at'_def projectKOs inQ_def)
       apply (wp setQueue_valid_queues' | simp | simp add: setQueue_def)+
     apply (wp getObject_tcb_wp | simp add: threadGet_def)+
     apply (clarsimp simp: obj_at'_def inQ_def projectKOs valid_queues'_def)
    apply (wp getObject_tcb_wp | simp add: threadGet_def)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma rescheduleRequired_valid_queues'_weak[wp]:
  "\<lbrace>\<lambda>s. valid_queues' s \<and> weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply wpsimp
  apply (clarsimp simp: weak_sch_act_wf_def)
  done

lemma rescheduleRequired_valid_queues'_sch_act_simple:
  "\<lbrace>valid_queues' and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp | fastforce simp: valid_queues'_def sch_act_simple_def)+
  done

lemma setThreadState_valid_queues'[wp]:
  "\<lbrace>\<lambda>s. valid_queues' s\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_valid_queues'_sch_act_simple)
  apply (rule_tac Q="\<lambda>_. valid_queues'" in hoare_post_imp)
   apply (clarsimp simp: sch_act_simple_def)
  apply (wp threadSet_valid_queues')
  apply (fastforce simp: inQ_def obj_at'_def pred_tcb_at'_def)
  done

lemma setBoundNotification_valid_queues'[wp]:
  "\<lbrace>\<lambda>s. valid_queues' s\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_valid_queues')
  apply (fastforce simp: inQ_def obj_at'_def pred_tcb_at'_def)
  done

lemma valid_tcb'_tcbState_update:
  "\<lbrakk> valid_tcb_state' st s; valid_tcb' tcb s \<rbrakk> \<Longrightarrow> valid_tcb' (tcbState_update (\<lambda>_. st) tcb) s"
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def valid_tcb_state'_def)
  done

lemma setThreadState_valid_objs'[wp]:
  "\<lbrace> valid_tcb_state' st and valid_objs' \<rbrace> setThreadState st t \<lbrace> \<lambda>_. valid_objs' \<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_valid_objs' | clarsimp simp: valid_tcb'_tcbState_update)+
  done

lemma rescheduleRequired_ksQ:
  "\<lbrace>\<lambda>s. sch_act_simple s \<and> P (ksReadyQueues s p)\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  including no_pre
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)
                            \<and> P (ksReadyQueues s p)" in hoare_seq_ext)
   apply wpsimp
   apply (case_tac x; simp)
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

lemma sts_ksQ:
  "\<lbrace>\<lambda>s. sch_act_simple s \<and> P (ksReadyQueues s p)\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_ksQ)
  apply (rule_tac Q="\<lambda>_ s. P (ksReadyQueues s p)" in hoare_post_imp)
   apply (clarsimp simp: sch_act_simple_def)+
  apply (wp, simp)
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
  apply (wpsimp wp: tcbSchedEnqueue_ksQ)
  done

lemma threadSet_tcbState_st_tcb_at':
  "\<lbrace>\<lambda>s. P st \<rbrace> threadSet (tcbState_update (\<lambda>_. st)) t \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: threadSet_def pred_tcb_at'_def)
  apply (wpsimp wp: setObject_tcb_strongest)
  done

lemma isRunnable_const:
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> isRunnable t \<lbrace>\<lambda>runnable _. runnable \<rbrace>"
  by (rule isRunnable_wp)

lemma sts_ksQ':
  "\<lbrace>\<lambda>s. (runnable' st \<or> ksCurThread s \<noteq> t) \<and> P (ksReadyQueues s p)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. P (ksReadyQueues s p)\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (rule hoare_pre_disj')
   apply (rule hoare_seq_ext [OF _
                 hoare_vcg_conj_lift
                   [OF threadSet_tcbState_st_tcb_at' [where P=runnable']
                       threadSet_ksQ]])
   apply (rule hoare_seq_ext [OF _
                 hoare_vcg_conj_lift [OF isRunnable_const isRunnable_inv]])
   apply (clarsimp simp: when_def)
   apply (case_tac x)
    apply (clarsimp, wp)[1]
   apply (clarsimp)
  apply (rule hoare_seq_ext [OF _
                hoare_vcg_conj_lift
                  [OF threadSet_ct threadSet_ksQ]])
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

lemma valid_ipc_buffer_ptr'D:
  assumes yv: "y < unat max_ipc_words"
  and    buf: "valid_ipc_buffer_ptr' a s"
  shows "pointerInUserData (a + of_nat y * 4) s"
  using buf unfolding valid_ipc_buffer_ptr'_def pointerInUserData_def
  apply clarsimp
  apply (subgoal_tac
         "(a + of_nat y * 4) && ~~ mask pageBits = a  && ~~ mask pageBits")
   apply simp
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (erule is_aligned_add_helper [THEN conjunct2])
   apply (rule word_less_power_trans_ofnat [where k = 2, simplified])
     apply (rule order_less_le_trans [OF yv])
     apply (simp add: msg_align_bits max_ipc_words)
    apply (simp add: msg_align_bits)
   apply (simp_all add: msg_align_bits pageBits_def)
  done

lemma in_user_frame_eq:
  assumes y: "y < unat max_ipc_words"
  and    al: "is_aligned a msg_align_bits"
  shows "in_user_frame (a + of_nat y * 4) s = in_user_frame a s"
proof -
  have "\<And>sz. (a + of_nat y * 4) && ~~ mask (pageBitsForSize sz) =
             a && ~~ mask (pageBitsForSize sz)"
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (rule is_aligned_add_helper [OF al, THEN conjunct2])
   apply (rule word_less_power_trans_ofnat [where k = 2, simplified])
     apply (rule order_less_le_trans [OF y])
     apply (simp add: msg_align_bits max_ipc_words)
    apply (simp add: msg_align_bits)
   apply (simp add: msg_align_bits pageBits_def)
  apply (case_tac sz, simp_all add: msg_align_bits)
  done

  thus ?thesis by (simp add: in_user_frame_def)
qed

lemma loadWordUser_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres (=) \<top> (valid_ipc_buffer_ptr' a) (load_word_offs a y) (loadWordUser (a + of_nat y * 4))"
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
      apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
      apply (simp add: word_bits_conv msg_align_bits)+
  apply (simp add: valid_ipc_buffer_ptr'_def msg_align_bits)
  done

lemma storeWordUser_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres dc (in_user_frame a) (valid_ipc_buffer_ptr' a)
                   (store_word_offs a y w) (storeWordUser (a + of_nat y * 4) w)"
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
       apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
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
     (typ_at' UserDataT (a && ~~ mask pageBits) and (\<lambda>s. is_aligned a 2))
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
     apply wp
    apply assumption
   apply simp
  apply simp
  done

lemmas msgRegisters_unfold
  = ARM_HYP_H.msgRegisters_def
    msg_registers_def
    ARM_HYP.msgRegisters_def
        [unfolded upto_enum_def, simplified,
         unfolded fromEnum_def enum_register, simplified,
         unfolded toEnum_def enum_register, simplified]

lemma getMRs_corres:
  "corres (=) (tcb_at t)
              (tcb_at' t and case_option \<top> valid_ipc_buffer_ptr' buf)
              (get_mrs t buf mi) (getMRs t buf (message_info_map mi))"
  proof -
  have S: "get = gets id"
    by (simp add: gets_def)
  have T: "corres (\<lambda>con regs. regs = map con msg_registers) (tcb_at t) (tcb_at' t)
     (thread_get (arch_tcb_get_registers o tcb_arch) t) (asUser t (mapM getRegister ARM_HYP_H.msgRegisters))"
    unfolding arch_tcb_get_registers_def
    apply (subst thread_get_as_user)
    apply (rule asUser_corres')
    apply (subst mapM_gets)
     apply (simp add: getRegister_def)
    apply (simp add: S ARM_HYP_H.msgRegisters_def msg_registers_def)
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

lemma setMRs_corres:
  assumes m: "mrs' = mrs"
  shows
  "corres (=) (tcb_at t and case_option \<top> in_user_frame buf)
              (tcb_at' t and case_option \<top> valid_ipc_buffer_ptr' buf)
              (set_mrs t buf mrs) (setMRs t buf mrs')"
proof -
  have setRegister_def2: "setRegister = (\<lambda>r v. modify (\<lambda>s. s ( r := v )))"
    by ((rule ext)+, simp add: setRegister_def)

  have S: "\<And>xs ys n m. m - n \<ge> length xs \<Longrightarrow> (zip xs (drop n (take m ys))) = zip xs (drop n ys)"
    by (simp add: zip_take_triv2 drop_take)

  have upto_enum_nth_assist4:
    "\<And>i. i < 116 \<Longrightarrow> [(5::machine_word).e.0x78] ! i * 4 = 0x14 + of_nat i * 4"
    by (subst upto_enum_word, subst upt_lhs_sub_map, simp)

  note upt.simps[simp del] upt_rec_numeral[simp del]

  show ?thesis using m
    unfolding setMRs_def set_mrs_def
    apply (clarsimp simp: arch_tcb_set_registers_def arch_tcb_get_registers_def cong: option.case_cong split del: if_split)
    apply (subst bind_assoc[symmetric])
    apply (fold thread_set_def[simplified])
    apply (subst thread_set_as_user[where f="\<lambda>context. \<lambda>reg.
                      if reg \<in> set (take (length mrs) msg_registers)
                      then mrs ! (the_index msg_registers reg) else context reg",simplified])
    apply (cases buf)
     apply (clarsimp simp: msgRegisters_unfold setRegister_def2 zipWithM_x_Nil zipWithM_x_modify
                           take_min_len zip_take_triv2 min.commute)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor[OF asUser_corres'])
          apply (rule corres_modify')
           apply (fastforce simp: fold_fun_upd[symmetric] msgRegisters_unfold
                            cong: if_cong simp del: the_index.simps)
          apply ((wp |simp)+)[6]
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
          apply (fastforce simp: fold_fun_upd[symmetric])
         apply clarsimp
         apply (rule corres_split_nor)
           apply (rule_tac S="{((x, y), (x', y')). y = y' \<and> x' = (a + (of_nat x * 4)) \<and> x < unat max_ipc_words}"
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
               and K (unat n \<le> msg_max_length))
              (tcb_at' s and tcb_at' r
               and case_option \<top> valid_ipc_buffer_ptr' sb
               and case_option \<top> valid_ipc_buffer_ptr' rb)
              (copy_mrs s sb r rb n) (copyMRs s sb r rb n)"
proof -
  have U: "unat n \<le> msg_max_length \<Longrightarrow>
           map (toEnum :: nat \<Rightarrow> word32) [7 ..< Suc (unat n)] = map of_nat [7 ..< Suc (unat n)]"
    unfolding msg_max_length_def by auto
  note R'=msgRegisters_unfold[THEN meta_eq_to_obj_eq, THEN arg_cong[where f=length]]
  note R=R'[simplified]

  have as_user_bit:
    "\<And>v :: word32. corres dc (tcb_at s and tcb_at r) (tcb_at' s and tcb_at' r)
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

  have wordSize[simp]: "of_nat wordSize = 4"
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

lemma cte_at_tcb_at_16':
  "tcb_at' t s \<Longrightarrow> cte_at' (t + 16) s"
  apply (simp add: cte_at'_obj_at')
  apply (rule disjI2, rule bexI[where x=16])
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
  apply (case_tac vmpage_size, simp_all add: pageBits_def)
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
  "corres (=) (tcb_at t and valid_objs and pspace_aligned)
               (tcb_at' t and valid_objs' and pspace_aligned'
                and pspace_distinct' and no_0_obj')
               (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  apply (simp add: lookup_ipc_buffer_def ARM_HYP_H.lookupIPCBuffer_def)
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
        apply (rename_tac word rights vmpage_size option)
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
         apply (clarsimp simp: word_bits_def
                       intro!: word_less_sub_1 and_mask_less')
         apply (case_tac vmpage_size, simp_all)[1]
        apply (drule state_relation_pspace_relation)
        apply (clarsimp simp: valid_cap_def obj_at_def no_0_obj_kheap
                             obj_relation_cuts_def3 no_0_obj'_def split:if_split_asm)
       apply (wp get_cap_valid_ipc get_cap_aligned)+
     apply (wp thread_get_obj_at_eq)+
   apply (clarsimp elim!: tcb_at_cte_at)
  apply clarsimp
  done

lemma lookupIPCBuffer_corres:
  "corres (=) (tcb_at t and invs)
               (tcb_at' t and invs')
               (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  using lookupIPCBuffer_corres'
  by (rule corres_guard_imp, auto simp: invs'_def valid_state'_def)


crunch inv[wp]: lookupIPCBuffer P

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

crunches setQueue, rescheduleRequired, tcbSchedDequeue
  for idle'[wp]: "valid_idle'"
  (simp: crunch_simps )

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
  apply (simp add: tcbSchedDequeue_def)
  apply (wp | simp add: o_def split del: if_split cong: if_cong)+
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
   apply (simp add: tcbSchedDequeue_def)
   apply (wp threadSet_pred_tcb_no_state | clarsimp simp: tcb_to_itcb'_def)+
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadSet_pred_tcb_no_state | clarsimp simp: tcb_to_itcb'_def)+
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

crunch refs_of'[wp]: rescheduleRequired "\<lambda>s. P (state_refs_of' s)"
  (wp: threadSet_state_refs_of')

lemma setThreadState_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' st
                                 \<union> {r \<in> state_refs_of' s t. snd r = TCBBound}))\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (simp add: setThreadState_def fun_upd_def
        | wp threadSet_state_refs_of')+

crunch hyp_refs_of'[wp]: rescheduleRequired "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: unless_def crunch_simps wp: threadSet_state_hyp_refs_of' ignore: threadSet)

lemma setThreadState_state_hyp_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_hyp_refs_of' s))\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (simp add: setThreadState_def fun_upd_def
        | wp threadSet_state_hyp_refs_of')+
  done

lemma setBoundNotification_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_bound_refs' ntfn
                                 \<union> {r \<in> state_refs_of' s t. snd r \<noteq> TCBBound}))\<rbrace>
     setBoundNotification ntfn t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (simp add: setBoundNotification_def Un_commute fun_upd_def
        | wp threadSet_state_refs_of' )+

lemma setBoundNotification_state_hyp_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
     setBoundNotification ntfn t
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  by (simp add: setBoundNotification_def fun_upd_def
        | wp threadSet_state_hyp_refs_of')+

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

lemma tcbSchedEnqueue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' tcb\<rbrace>
    tcbSchedEnqueue tcb \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp threadSet_iflive' hoare_drop_imps | simp add: crunch_simps)+
  done

lemma rescheduleRequired_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'
        and (\<lambda>s. \<forall>t. ksSchedulerAction s = SwitchToThread t
                \<longrightarrow> st_tcb_at' runnable' t s)\<rbrace>
      rescheduleRequired
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp)+
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def)
  apply (erule(1) if_live_then_nonz_capD')
  apply (fastforce simp: projectKOs live'_def)
  done

lemma sts_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
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
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def projectKOs live'_def
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

lemma bound_tcb_ex_cap'':
  "\<lbrakk> bound_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>ntfn. P ntfn \<Longrightarrow> bound ntfn \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_real_def projectKOs live'_def
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

crunches setThreadState, setBoundNotification
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"
  (simp: unless_def crunch_simps)

crunches setThreadState, setBoundNotification
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: getObject_inv_tcb
   simp: updateObject_default_def unless_def crunch_simps)

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
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
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
  for irq_states'[wp]: valid_irq_states'
  and pde_mappings'[wp]: valid_pde_mappings'
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
  (simp: crunch_simps)

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
      apply (wp ts sq hoare_convert_imp [OF addToBitmap_nosch addToBitmap_ct'])+
           apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
           apply (wp sq hoare_convert_imp [OF setQueue_nosch setQueue_ct])+
       apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
       apply wp
      apply assumption
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

crunch nosch[wp]: tcbSchedEnqueue "\<lambda>s. P (ksSchedulerAction s)"
  (simp: unless_def)
crunch nosch[wp]: tcbSchedAppend "\<lambda>s. P (ksSchedulerAction s)"
  (simp: unless_def)

lemma rescheduleRequired_sa_cnt[wp]:
  "\<lbrace>\<lambda>s. True \<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread \<rbrace>"
  unfolding rescheduleRequired_def setSchedulerAction_def
  by wpsimp

lemma possibleSwitchTo_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
    possibleSwitchTo t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wpsimp wp: hoare_weak_lift_imp rescheduleRequired_ct_not_inQ tcbSchedEnqueue_ct_not_inQ
                    threadGet_wp
       | (rule hoare_post_imp[OF _ rescheduleRequired_sa_cnt], fastforce))+
  apply (fastforce simp: obj_at'_def)
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
  apply (simp add: setThreadState_def rescheduleRequired_def)
  apply (wp hoare_vcg_conj_lift tcbSchedEnqueue_not_st
          | wpc
          | rule hoare_drop_imps
          | simp)+
  apply (clarsimp simp: obj_at'_def)
  apply (case_tac obj)
  apply fastforce
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

lemma sts_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp untyped_ranges_zero_lift)
  done

lemma sts_invs_minor':
  "\<lbrace>st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st
                   \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                      st' \<noteq> Inactive \<and> \<not> idle' st')) t
      and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' st)
      and (\<lambda>s. (\<exists>p. t \<in> set(ksReadyQueues s p)) \<longrightarrow> runnable' st)
      and (\<lambda>s. runnable' st \<and> obj_at' tcbQueued t s \<longrightarrow> st_tcb_at' runnable' t s)
      and sch_act_simple
      and invs'\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  including no_pre
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp sts_valid_queues valid_irq_node_lift irqs_masked_lift
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
  apply (frule tcb_in_valid_state', clarsimp+)
  apply (cases st, simp_all add: valid_tcb_state'_def
                  split: Structures_H.thread_state.split_asm)
  done

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
    "\<And>l. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow> p + l && ~~ mask 12 = p && ~~ mask 12"
  proof -
    fix l
    assume al: "p && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "(2::nat) \<le> 12" by simp
    show "?thesis l"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs' no_irq_storeWord no_irq)
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
            split: if_split_asm)
  done
qed

lemma storeWord_invs_no_cicd'[wp]:
  "\<lbrace>pointerInUserData p and invs_no_cicd'\<rbrace> doMachineOp (storeWord p w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow> p + l && ~~ mask 12 = p && ~~ mask 12"
  proof -
    fix l
    assume al: "p && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "(2::nat) \<le> 12" by simp
    show "?thesis l"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs_no_cicd' no_irq_storeWord no_irq)
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
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
  shows "corres dc (tcb_at ptr and is_etcb_at ptr)
            (obj_at' (\<lambda>ko. non_exst_same ko tcb') ptr
            and obj_at' P ptr)
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
     apply (clarsimp simp: obj_at'_def other_obj_relation_def cte_relation_def tcb_relation_def projectKOs split: if_split_asm)+
   apply (clarsimp simp: aobj_relation_cuts_def split: ARM_A.arch_kernel_obj.splits)
   apply (rename_tac arch_kernel_obj obj d p ts)
   apply (case_tac arch_kernel_obj; simp)
     apply (clarsimp simp: pte_relation_def pde_relation_def is_tcb_def
                    split: if_split_asm)+
  apply (simp only: ekheap_relation_def dom_fun_upd2 simp_thms)
  apply (frule bspec, erule domI)
  apply (rule ballI, drule(1) bspec)
  apply (drule domD)
  apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: projectKOs)
  apply (insert e)
  apply (clarsimp simp: other_obj_relation_def etcb_relation_def is_other_obj_relation_type split: Structures_A.kernel_object.splits Structures_H.kernel_object.splits ARM_A.arch_kernel_obj.splits)
  done

lemma set_eobject_corres:
  assumes tcbs: "non_exst_same tcb' tcbu'"
  assumes e: "etcb_relation etcb tcb' \<Longrightarrow> etcb_relation etcbu tcbu'"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF tcbu' = getF tcb'"
  assumes r: "r () ()"
  shows "corres r (tcb_at add and (\<lambda>s. ekheap s add = Some etcb))
                  (ko_at' tcb' add)
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
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  assumes e: "\<And>etcb tcb'. etcb_relation etcb tcb' \<Longrightarrow>
                         etcb_relation (f etcb) (f' tcb')"
  shows      "corres dc (tcb_at t and valid_etcbs)
                        (tcb_at' t)
                    (ethread_set f t) (threadSet f' t)"
  apply (simp add: ethread_set_def threadSet_def bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_get_etcb set_eobject_corres])
         apply (rule x)
        apply (erule e)
       apply (simp add: z)+
     apply wp+
   apply clarsimp
   apply (simp add: valid_etcbs_def tcb_at_st_tcb_at[symmetric])
   apply (force simp: tcb_at_def get_etcb_def obj_at_def)
  apply simp
  done

lemmas ethread_set_corres =
    ethread_set_corresT [OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

end
end
