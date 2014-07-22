(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory TcbAcc_R
imports CSpace_R
begin

declare if_weak_cong [cong]

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

lemma valid_pspace'_ksPSpace:
  "ksPSpace s = ksPSpace s' \<Longrightarrow> valid_pspace' s = valid_pspace' s'"
  apply safe
   apply (rule valid_pspace', assumption+)
  apply (drule sym)
  apply (rule valid_pspace', assumption+)
  done

lemma invs'_machine:
  assumes mask: "irq_masks (f (ksMachineState s)) =
                 irq_masks (ksMachineState s)"
  assumes vms: "valid_machine_state' (ksMachineState_update f s) =
                valid_machine_state' s"
  shows "invs' (ksMachineState_update f s) = invs' s"
proof -
  have valid_pspace'_machine: "\<And>f s.
       valid_pspace' (ksMachineState_update f s) = valid_pspace' s"
    by (rule valid_pspace'_ksPSpace, simp)
  have ifunsafe'_machine[simp]: "\<And>f s.
       if_unsafe_then_cap' (ksMachineState_update f s) = if_unsafe_then_cap' s"
    by fastforce
  have iflive_machine[simp]: "\<And>f s.
       if_live_then_nonz_cap' (ksMachineState_update f s) = if_live_then_nonz_cap' s"
    by simp
  have valid_idle'_machine: "\<And>f s.
       valid_idle' (ksMachineState_update f s) = valid_idle' s"
    by fastforce
  show ?thesis
    apply (cases "ksSchedulerAction s")
    apply (simp_all add: invs'_def valid_state'_def cur_tcb'_def ct_in_state'_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                    valid_queues_def valid_pspace'_machine
                    valid_idle'_machine vms ct_not_inQ_def
                    state_refs_of'_def ps_clear_def
                    valid_irq_node'_def mask
              cong: option.case_cong)
    done
qed

lemma invs_no_cicd'_machine:
  assumes mask: "irq_masks (f (ksMachineState s)) =
                 irq_masks (ksMachineState s)"
  assumes vms: "valid_machine_state' (ksMachineState_update f s) =
                valid_machine_state' s"
  shows "invs_no_cicd' (ksMachineState_update f s) = invs_no_cicd' s"
proof -
  have valid_pspace'_machine: "\<And>f s.
       valid_pspace' (ksMachineState_update f s) = valid_pspace' s"
    by (rule valid_pspace'_ksPSpace, simp)
  have ifunsafe'_machine[simp]: "\<And>f s.
       if_unsafe_then_cap' (ksMachineState_update f s) = if_unsafe_then_cap' s"
    by fastforce
  have iflive_machine[simp]: "\<And>f s.
       if_live_then_nonz_cap' (ksMachineState_update f s) = if_live_then_nonz_cap' s"
    by simp
  have valid_idle'_machine: "\<And>f s.
       valid_idle' (ksMachineState_update f s) = valid_idle' s"
    by fastforce
  show ?thesis
    apply (cases "ksSchedulerAction s")
    apply (simp_all add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def cur_tcb'_def ct_in_state'_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                    valid_queues_def valid_pspace'_machine
                    valid_idle'_machine vms ct_not_inQ_def
                    state_refs_of'_def ps_clear_def
                    valid_irq_node'_def mask
              cong: option.case_cong)
    done
qed

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
             pointerInUserData p s \<or>
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
             pointerInUserData p s \<or>
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
     doMachineOp getActiveIRQ
   \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive\<rbrace>"
  apply (rule hoare_lift_Pf3 [where f="ksInterruptState"])
   prefer 2
   apply wp[1]
   apply (simp add: irq_state_independent_H_def)
  apply (rule dmo_lift')
  apply (rule getActiveIRQ_masked)
  done

lemma doMachineOp_getActiveIRQ_IRQ_active':
  "\<lbrace>valid_irq_states'\<rbrace>
     doMachineOp getActiveIRQ
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
  apply (wp hoare_whenE_wp|wpc)+
     apply (rule hoare_post_imp)
      prefer 2
     apply (rule doMachineOp_getActiveIRQ_IRQ_active)
    apply clarsimp
   apply wp
  apply clarsimp
  done

lemmas doMachineOp_obj_at = doMachineOp_obj_at'

(*
  "\<lbrace>\<lambda>s. P (obj_at' P' addr s)\<rbrace> doMachineOp opr \<lbrace>\<lambda>rv s. P (obj_at' P' addr s)\<rbrace>"
  apply (rule doMachineOp_obj_at')

proof -
  have obj_at'_machine: "\<And>P addr f s.
       obj_at' P addr (ksMachineState_update f s) = obj_at' P addr s"
    by (fastforce intro: obj_at'_pspaceI)
  show ?thesis
    apply (simp add: doMachineOp_def split_def)
    apply (wp select_wp)
    apply (clarsimp simp: obj_at'_machine)
    done
qed *)

lemma updateObject_tcb_inv:
  "\<lbrace>P\<rbrace> updateObject (obj::tcb) ko p q n \<lbrace>\<lambda>rv. P\<rbrace>"
  by simp (rule updateObject_default_inv)

lemma tcb_update_corres':
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
     apply (rule set_other_obj_corres[where P="op = tcb'"])
           apply (rule ext)+
           apply simp
          defer
          apply (simp add: is_other_obj_relation_type_def a_type_def
                           projectKOs objBits_simps
                           other_obj_relation_def tcbs r)+
    apply (fastforce elim!: obj_at_weakenE dest: bspec[OF tables])
   apply (subst(asm) eq_commute, assumption)
  apply (clarsimp simp: projectKOs obj_at'_def objBits_simps)
  apply (subst map_to_ctes_upd_tcb, assumption+)
   apply (simp add: ps_clear_def3 field_simps)
  apply (subst if_not_P)
   apply (fastforce dest: bspec [OF tables', OF ranI])
  apply simp
  done

lemma tcb_update_corres:
  "\<lbrakk> tcb_relation tcb tcb' \<Longrightarrow> tcb_relation tcbu tcbu';
     \<forall>(getF, v) \<in> ran tcb_cap_cases. getF tcbu = getF tcb;
     \<forall>(getF, v) \<in> ran tcb_cte_cases. getF tcbu' = getF tcb';
     r () (); exst_same tcb' tcbu'\<rbrakk>
   \<Longrightarrow> corres r (\<lambda>s. get_tcb add s = Some tcb) 
               (\<lambda>s'. (tcb', s') \<in> fst (getObject add s'))
               (set_object add (TCB tcbu)) (setObject add tcbu')"
  apply (rule corres_guard_imp)
    apply (erule (3) tcb_update_corres', force)
   apply fastforce
  apply (clarsimp simp: getObject_def in_monad split_def obj_at'_def
                        loadObject_default_def projectKOs objBits_simps
                        in_magnitude_check)
  done

lemma assert_get_tcb_corres:
  "corres tcb_relation (tcb_at t) (tcb_at' t)
          (gets_the (get_tcb t)) (getObject t)"
  apply (rule corres_guard_imp)
    apply (rule corres_gets_the)
    apply (rule corres_get_tcb)
   apply (simp add: tcb_at_def)
  apply assumption
  done

lemma threadget_corres:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> r (f tcb) (f' tcb')"
  shows      "corres r (tcb_at t) (tcb_at' t) (thread_get f t) (threadGet f' t)"
  apply (simp add: thread_get_def threadGet_def)
  apply (fold liftM_def)
  apply simp
  apply (rule corres_rel_imp)
   apply (rule assert_get_tcb_corres)
  apply (simp add: x)
  done

lemma threadGet_inv [wp]: "\<lbrace>P\<rbrace> threadGet f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: threadGet_def getObject_inv_tcb | wp)+

declare result_in_set_wp[wp]

lemma ball_tcb_cte_casesI:
  "\<lbrakk> P (tcbCTable, tcbCTable_update);
     P (tcbVTable, tcbVTable_update);
     P (tcbReply, tcbReply_update);
     P (tcbCaller, tcbCaller_update);
     P (tcbIPCBufferFrame, tcbIPCBufferFrame_update) \<rbrakk>
    \<Longrightarrow> \<forall>x \<in> ran tcb_cte_cases. P x"
  by (simp add: tcb_cte_cases_def)

lemma all_tcbI:
  "\<lbrakk> \<And>a b c d e f g h i j k l m n. P (Thread a b c d e f g h i j k l m n) \<rbrakk> \<Longrightarrow> \<forall>tcb. P tcb"
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
    apply (rule corres_split [OF _ assert_get_tcb_corres])
      apply (rule tcb_update_corres')
          apply (erule x)
         apply (rule y)
        apply (clarsimp simp: bspec_split [OF spec [OF z]])
        apply fastforce
       apply simp
      apply (rule e)
     apply wp
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
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply (clarsimp simp: other_obj_relation_def
                 split: Structures_A.kernel_object.split_asm
                        ARM_Structs_A.arch_kernel_obj.split_asm)
  apply (simp add: is_tcb obj_at_def)
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
    apply (simp add: return_def thread_set_def gets_the_def
                     assert_opt_def simpler_gets_def set_object_def
                     put_def get_def bind_def)
    apply (subgoal_tac "kheap s(t \<mapsto> TCB tcb) = kheap s", simp)
    apply (simp add: map_upd_triv get_tcb_SomeD)
    done
  show ?thesis
    apply (rule stronger_corres_guard_imp)
      apply (subst corres_cong [OF refl refl S refl refl])
       defer
       apply (subst bind_return [symmetric],
              rule corres_split' [OF threadset_corresT])
             apply (simp add: x)
            apply simp
           apply (rule y)
          apply (rule e)
         apply (rule corres_noop [where P=\<top> and P'=\<top>])
          apply simp
         apply (rule no_fail_pre, wp)[1]
        apply wp
      apply simp
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
    apply (rule corres_split_nor [OF _ threadSet_corres_noopT])
         apply (rule z)
        apply (simp add: x)
       apply (rule y)
      apply (rule e)
     apply (wp w)
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
  apply (simp add: threadSet_def)
  apply (wp setObject_nosch)
   apply (simp add: updateObject_default_def)
   apply wp
   apply simp
  apply wp
  done

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

lemma setObject_queues_unchanged_tcb:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  apply (rule setObject_queues_unchanged)
  apply (wp|simp add: updateObject_default_def)+
  done

lemma setObject_tcb_ctes_of[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s) \<and>
     obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t s\<rbrace>
     setObject t v
   \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (rule setObject_ctes_of)
   apply (clarsimp simp: updateObject_default_def in_monad Pair_fst_snd_eq
                         obj_at'_def objBits_simps in_magnitude_check
                         projectKOs)
   apply fastforce
  apply (clarsimp simp: updateObject_default_def in_monad Pair_fst_snd_eq
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
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' (tcbState v)))\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp setObject_state_refs_of',
      simp_all add: objBits_simps fun_upd_def)

lemma setObject_tcb_iflive':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and>
      (live' (injectKO v) \<longrightarrow> ex_nonz_cap_to' t s)
       \<and> obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF v) t s\<rbrace>
     setObject t (v :: tcb)
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule setObject_iflive')
      apply (simp add: objBits_simps)+
   apply (clarsimp simp: updateObject_default_def in_monad projectKOs
                         in_magnitude_check objBits_simps Pair_fst_snd_eq
                         obj_at'_def)
   apply fastforce
  apply (clarsimp simp: updateObject_default_def bind_def projectKOs)
  done

lemma setObject_tcb_idle':
  "\<lbrace>\<lambda>s. valid_idle' s \<and>
     (t = ksIdleThread s \<longrightarrow> idle' (tcbState v))\<rbrace>
     setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_pre)
  apply (rule_tac P="\<top>" in setObject_idle')
      apply (simp add: objBits_simps)+
   apply (simp add: updateObject_default_inv)
  apply (simp add: projectKOs)
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
                          in_magnitude_check objBits_simps Pair_fst_snd_eq
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
  unfolding pred_conj_def valid_global_refs'_def valid_refs'_def
  apply simp
  apply (rule hoare_lift_Pf2 [where f="global_refs'"])
   apply (subst conj_assoc [symmetric], rule setObject_ctes_of)
    apply (clarsimp simp: updateObject_default_def in_monad projectKOs
                          in_magnitude_check objBits_simps Pair_fst_snd_eq
                          obj_at'_def)
    apply fastforce
   apply (clarsimp simp: updateObject_default_def in_monad Pair_fst_snd_eq
                         obj_at'_def objBits_simps in_magnitude_check
                         projectKOs bind_def)
  apply wp
  done

lemma setObject_tcb_irq_handlers':
  "\<lbrace>valid_irq_handlers' and
    obj_at' (\<lambda>tcb. (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb = getF v)) t\<rbrace>
  setObject t (v :: tcb) 
  \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def cteCaps_of_def irq_issued'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF setObject_ksInterrupt])
    apply (simp, rule updateObject_default_inv)
   apply wp
  apply (auto simp: ran_def)
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

lemma getObject_valid_obj2:
  "\<lbrace>invs' and tcb_at' t\<rbrace> getObject t \<lbrace>\<lambda>rv :: tcb. valid_obj' (injectKO rv)\<rbrace>"
  apply (rule hoare_pre_imp [OF _ getObject_valid_obj])
    apply clarsimp
   apply simp
  apply (simp add: objBits_simps)
  done

lemma getObject_tcb_wp:
  "\<lbrace>\<lambda>s. tcb_at' p s \<longrightarrow> (\<exists>t::tcb. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad 
                     split_def objBits_simps loadObject_default_def
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

(* FIXME random place to have these *)
lemma pspace_no_overlap_queues [simp]:
  "pspace_no_overlap' w sz (ksReadyQueues_update f s) = pspace_no_overlap' w sz s"
  by (simp add: pspace_no_overlap'_def)

lemma pspace_no_overlap'_ksSchedulerAction[simp]:
  "pspace_no_overlap' a b (ksSchedulerAction_update f s) =
   pspace_no_overlap' a b s"
  by (simp add: pspace_no_overlap'_def)

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
  assumes y: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
                      \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes u: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes w: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  shows
  "\<lbrace>valid_pspace' and (\<lambda>s. P \<longrightarrow> st_tcb_at' Q t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def threadSet_def)
  apply (rule hoare_pre,
         wp setObject_tcb_valid_objs getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs st_tcb_at'_def)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def
                            bspec_split [OF spec [OF x]] z
                            split_paired_Ball y u w)
  done

lemmas threadSet_valid_pspace'T =
    threadSet_valid_pspace'T_P[where P=False, simplified]

lemmas threadSet_valid_pspace' =
    threadSet_valid_pspace'T [OF all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_ifunsafe'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows      "\<lbrace>if_unsafe_then_cap'\<rbrace> threadSet F t \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_ifunsafe' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def bspec_split [OF spec [OF x]])
  done

lemmas threadSet_ifunsafe' =
    threadSet_ifunsafe'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_state_refs_of'T_P:
  assumes x: "\<forall>tcb. (P' \<longrightarrow> Q (tcbState tcb)) \<longrightarrow>
                     tcb_st_refs_of' (tcbState (F tcb))
                       = f' (tcb_st_refs_of' (tcbState tcb))"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := f' (state_refs_of' s t)))
              \<and> (P' \<longrightarrow> st_tcb_at' Q t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp getObject_tcb_wp)
  apply clarsimp
  apply (clarsimp simp: obj_at'_def projectKOs st_tcb_at'_def
                 elim!: rsubst[where P=P] intro!: ext)
  apply (cut_tac s=s and p=t and 'a=tcb in ko_at_state_refs_ofD')
   apply (simp add: obj_at'_def projectKOs)
  apply (clarsimp simp: x)
  done

lemmas threadSet_state_refs_of'T =
    threadSet_state_refs_of'T_P [where P'=False, simplified]

lemmas threadSet_state_refs_of' =
    threadSet_state_refs_of'T [OF all_tcbI]

lemma threadSet_iflive'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
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
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (subst conj_assoc[symmetric], subst imp_disjL[symmetric])
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
  shows "\<lbrace>cte_wp_at' P p\<rbrace> threadSet F t \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  apply (simp add: threadSet_def)
  apply (rule hoare_seq_ext [where B="\<lambda>rv. obj_at' (op = rv) t and cte_wp_at' P p"])
   apply (subst and_commute)
   apply (rule setObject_cte_wp_at')
    apply (clarsimp simp: updateObject_default_def projectKOs in_monad objBits_simps
                          obj_at'_def objBits_simps in_magnitude_check Pair_fst_snd_eq)
    apply (case_tac tcba, clarsimp simp: bspec_split [OF spec [OF x]])
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
          (\<forall>tcb. ko_at' tcb t s \<and> idle' (tcbState tcb) \<longrightarrow> idle' (tcbState (F tcb))))\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_idle' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: valid_idle'_def st_tcb_at'_def obj_at'_def projectKOs)
  done

lemmas threadSet_idle' =
    threadSet_idle'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma threadSet_valid_queues:
  "\<lbrace>Invariants_H.valid_queues and (\<lambda>s. \<forall>d p. (\<exists>tcb. (inQ d p tcb \<and> runnable' (tcbState tcb)) \<and>
                                    \<not>(inQ d p (f tcb) \<and> runnable' (tcbState (f tcb))))
                        \<longrightarrow> obj_at' (\<lambda>tcb. (inQ d p tcb \<and> runnable' (tcbState tcb)) \<and>
                                          \<not>(inQ d p (f tcb) \<and> runnable' (tcbState (f tcb)))) t s
                        \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: Invariants_H.valid_queues_def' st_tcb_at'_def)
   apply (wp setObject_queues_unchanged_tcb
             hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_queues_def' st_tcb_at'_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (fastforce)
  done

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
                split del: split_if)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
     apply (wp setObject_ko_wp_at | simp add: objBits_simps)+
    apply (wp getObject_tcb_wp updateObject_default_inv
               | simp split del: split_if)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs
                        objBits_simps addToQs_set_def
             split del: split_if cong: if_cong)
  apply (fastforce simp: projectKOs split: split_if_asm)
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

lemma ksReadyQueues_update_id:
  "ksReadyQueues_update id s = s"
  by simp

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
  apply wp
   apply (rule hoare_lift_Pf, rule setObject_tcb_at') 
   apply (wp setObject_ct_inv)
  done

crunch valid_arch' [wp]: setThreadState valid_arch_state'
  (ignore: getObject setObject simp: unless_def crunch_simps)

crunch ksInterrupt'[wp]: threadSet "\<lambda>s. P (ksInterruptState s)"
  (ignore: getObject setObject wp: setObject_ksInterrupt updateObject_default_inv)

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

crunch irq_states' [wp]: threadSet valid_irq_states'
  (ignore: setObject getObject)

crunch pde_mappings' [wp]: threadSet valid_pde_mappings'
  (ignore: getObject setObject)

crunch pspace_domain_valid [wp]: threadSet "pspace_domain_valid"
  (ignore: getObject setObject)

lemma valid_queues_subset:
  "\<lbrakk> Invariants_H.valid_queues (ksReadyQueues_update Qf s);
        \<forall>d p. set (ksReadyQueues s (d, p))
                 \<subseteq> set (Qf (ksReadyQueues s) (d, p));
        \<forall>d p. distinct (Qf (ksReadyQueues s) (d, p))
                 \<longrightarrow> distinct (ksReadyQueues s (d, p));
        \<forall>d p. Qf (ksReadyQueues s) (d,p) = [] \<longrightarrow> ksReadyQueues s (d,p) = []
   \<rbrakk>
      \<Longrightarrow> Invariants_H.valid_queues s"
  by (simp add: Invariants_H.valid_queues_def subset_iff)

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
    apply (rule getObject_inv_tcb)
   apply (rule hoare_strengthen_post [OF getObject_ko_at])
     apply simp
    apply (simp add: objBits_simps)
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
lemma obj_at_not_obj_at_conj:
  assumes  obj: "obj_at' (\<lambda>tcb::tcb. P tcb) t s"
      and nobj: "\<not>obj_at' (\<lambda>tcb::tcb. Q tcb) t s"
    shows "obj_at' (\<lambda>tcb. P tcb \<and> \<not>Q tcb) t s "
  using assms
  apply -
  apply (drule not_obj_at' [THEN iffD1])
  apply (subgoal_tac "tcb_at' t s")
   apply (drule tcb_at_typ_at' [THEN iffD1])
   apply (clarsimp)
   apply (drule(1) obj_at_conj')
   apply (erule obj_at'_weakenE, fastforce)
  apply (erule obj_at'_weakenE, simp)
  done

(* FIXME: move *)
lemmas tcb_at_not_obj_at_elim' = not_obj_at_elim' [OF tcb_at_typ_at' [THEN iffD1]]

(* FIXME: move *)
lemma lift_neg_st_tcb_at':
  assumes typat: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
      and sttcb: "\<And>S p. \<lbrace>st_tcb_at' S p\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at' S p\<rbrace>"
    shows "\<lbrace>\<lambda>s. P (st_tcb_at' S p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (st_tcb_at' S p s)\<rbrace>"
  apply (rule_tac P=P in P_bool_lift)
   apply (rule sttcb)
  apply (simp add: st_tcb_at'_def not_obj_at')
  apply (wp hoare_convert_imp)
   apply (rule typat)
  apply (rule hoare_chain [OF sttcb])
   apply (fastforce simp: st_tcb_at'_def comp_def)
  apply (clarsimp simp: st_tcb_at'_def elim!: obj_at'_weakenE)
  done

lemma threadSet_obj_at'_strongish[wp]:
  "\<lbrace>obj_at' (\<lambda>obj. if t = t' then P (f obj) else P obj) t'\<rbrace>
     threadSet f t \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  by (simp add: hoare_weaken_pre [OF threadSet_obj_at'_really_strongest])

lemma threadSet_st_tcb_no_state:
  assumes "\<And>tcb. tcbState (f tcb) = tcbState tcb"
  shows   "\<lbrace>\<lambda>s. P (st_tcb_at' P' t' s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (st_tcb_at' P' t' s)\<rbrace>"
proof -
  have pos: "\<And>P' t' t.
            \<lbrace>st_tcb_at' P' t'\<rbrace> threadSet f t \<lbrace>\<lambda>rv. st_tcb_at' P' t'\<rbrace>"
    apply (simp add: st_tcb_at'_def)
    apply (wp threadSet_obj_at'_strongish)
    apply clarsimp
    apply (erule obj_at'_weakenE)
    apply (insert assms)
    apply clarsimp
    done
  show ?thesis
    apply (rule_tac P=P in P_bool_lift)
     apply (rule pos)
    apply (rule_tac Q="\<lambda>_ s. \<not> tcb_at' t' s \<or> st_tcb_at' (\<lambda>tcb. \<not> P' tcb) t' s"
             in hoare_post_imp)
     apply (erule disjE)
      apply (clarsimp dest!: st_tcb_at')
     apply (clarsimp)
     apply (frule_tac P=P' and Q="\<lambda>tcb. \<not> P' tcb" in st_tcb_at_conj')
     apply (clarsimp)+
    apply (wp hoare_convert_imp)
      apply (simp add: typ_at_tcb' [symmetric])
      apply (wp pos)
    apply (clarsimp simp: st_tcb_at'_def not_obj_at' elim!: obj_at'_weakenE)
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
  apply (wp_trace setObject_ksDomSchedule_inv)
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
apply (wp sch_act_wf_lift threadSet_st_tcb_no_state | simp add: tcb_in_cur_domain'_def)+
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
  apply (frule_tac P1="op = (ksCurThread s)"
                in use_valid [OF _ threadSet_ct], rule refl)
  apply (frule_tac P1="op = (ksCurDomain s)"
                in use_valid [OF _ threadSet_cd], rule refl)
  apply (case_tac "ksSchedulerAction b",
         simp_all add: ct_in_state'_def st_tcb_at'_def)
   apply (subgoal_tac "t \<noteq> ksCurThread s")
    apply (drule_tac t'1="ksCurThread s"
                 and P1="activatable' \<circ> tcbState"
                  in use_valid [OF _ threadSet_obj_at'_really_strongest])
     apply (clarsimp simp: o_def)
    apply clarsimp
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (subgoal_tac "t \<noteq> word")
   apply (frule_tac t'1=word
                and P1="runnable' \<circ> tcbState"
                 in use_valid [OF _ threadSet_obj_at'_really_strongest])
    apply (clarsimp simp: o_def)
   apply (rule conjI)
   apply clarsimp
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
      simp add: updateObject_tcb)+

lemma threadSet_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> threadSet F t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def)
  by (intro hoare_vcg_all_lift hoare_vcg_disj_lift, wp)

lemma vms_ksReadyQueues_update[simp]:
  "valid_machine_state' (ksReadyQueues_update f s) = valid_machine_state' s"
  by (simp add: valid_machine_state'_def)

lemma ct_not_inQ_ksReadyQueues_update[simp]:
  "ct_not_inQ (ksReadyQueues_update f s) = ct_not_inQ s"
  by (simp add: ct_not_inQ_def)

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
   apply (wp setObject_tcb_strongest getObject_tcb_wp)
  apply (case_tac "t = ksCurThread s")
   apply (clarsimp simp: obj_at'_def)+
  done

lemma threadSet_ct_idle_or_in_cur_domain':
  "(\<And>tcb. tcbDomain (F tcb) = tcbDomain tcb) \<Longrightarrow> \<lbrace>ct_idle_or_in_cur_domain'\<rbrace> threadSet F t \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
apply (rule ct_idle_or_in_cur_domain'_lift)
apply (wp hoare_vcg_disj_lift| simp)+
done

lemma setObject_tcb_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s) \<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>_ s. P (ksDomScheduleIdx s)\<rbrace>"
  apply (simp add:setObject_def)
  apply (simp add: updateObject_default_def in_monad)
   apply (wp|wpc)+
  apply (simp add: projectKOs)
  done

lemma threadSet_valid_dom_schedule':
  "\<lbrace> valid_dom_schedule'\<rbrace> threadSet F t \<lbrace>\<lambda>_. valid_dom_schedule'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_ksDomSchedule_inv hoare_Ball_helper)
  done

lemma threadSet_invs_trivialT_P_Qf:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (F tcb) = getF tcb"
  assumes z: "\<not> P \<Longrightarrow> (\<forall>tcb. tcbState (F tcb) = tcbState tcb
                          \<and> tcbDomain (F tcb) = tcbDomain tcb)"
  assumes z': "P \<Longrightarrow> (\<forall>tcb. tcbState (F tcb) = Inactive \<and> tcbDomain (F tcb) = tcbDomain tcb)
                      \<and> (\<forall>st. Q st \<longrightarrow> st = Inactive)"
  assumes w: "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
                        \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
  assumes v: "\<forall>tcb. tcbDomain tcb \<le> maxDomain \<longrightarrow> tcbDomain (F tcb) \<le> maxDomain"
  assumes u: "\<forall>tcb. tcbPriority tcb \<le> maxPriority \<longrightarrow> tcbPriority (F tcb) \<le> maxPriority"
  shows      "\<lbrace>\<lambda>s. invs' (ksReadyQueues_update Qf s)
                \<and> (\<forall>d p. set (Qf (ksReadyQueues s) (d, p))
                         \<subseteq> set (addToQs F t (ksReadyQueues s) (d, p)))
                \<and> (\<forall>d p. set (ksReadyQueues s (d, p))
                         \<subseteq> set (Qf (ksReadyQueues s) (d, p))
                     \<and> (distinct (Qf (ksReadyQueues s) (d, p))
                         \<longrightarrow> distinct (ksReadyQueues s (d, p)))
                     \<and> (Qf (ksReadyQueues s) (d,p) = [] \<longrightarrow> ksReadyQueues s (d,p) = []))
                \<and> tcb_at' t s
                \<and> (\<forall>d p. (\<exists>tcb. inQ d p tcb \<and> \<not> inQ d p (F tcb))
                        \<longrightarrow> (P \<longrightarrow> obj_at' (\<lambda>tcb. inQ d p tcb \<and> \<not> inQ d p (F tcb)) t s)
                        \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))
                \<and> (\<forall>ko d p. ko_at' ko t s \<and> inQ d p (F ko) \<and> \<not> inQ d p ko
                              \<longrightarrow> t \<in> set (ksReadyQueues s (d, p)))
                \<and> ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb))
                        \<longrightarrow> (P \<longrightarrow> obj_at' (\<lambda>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)) t s)
                        \<longrightarrow> ex_nonz_cap_to' t s \<and> t \<noteq> ksCurThread s)
                \<and> (P \<longrightarrow> st_tcb_at' Q t s \<and> \<not> t = ksIdleThread s)
                \<and> (\<forall>tcb. (tcbQueued (F tcb) \<and>
                          ksSchedulerAction s = ResumeCurrentThread)
                           \<longrightarrow> (tcbQueued tcb \<or> t \<noteq> ksCurThread s))\<rbrace>
                threadSet F t
              \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have y: "\<forall>tcb. (P \<longrightarrow> Q (tcbState tcb))
                      \<longrightarrow> tcb_st_refs_of' (tcbState (F tcb))
                              = tcb_st_refs_of' (tcbState tcb)
                       \<and> valid_tcb_state' (tcbState (F tcb))
                              = valid_tcb_state' (tcbState tcb)"
    apply (cases P)
     apply (auto dest!: z z' intro!: ext simp: valid_tcb_state'_def)
    done
  from z z' have domains: "\<And>tcb. tcbDomain (F tcb) = tcbDomain tcb" by blast
  show ?thesis
    apply (simp add: invs'_def valid_state'_def split del: split_if)
    apply (rule hoare_pre)
     apply (wp x y w v u
               threadSet_valid_pspace'T_P[where P=P and Q=Q]
               threadSet_sch_actT_P [OF z z']
               threadSet_valid_queues
               threadSet_valid_queues_Qf[where Qf=Qf]
               threadSet_state_refs_of'T_P[where f'=id and P'=P and Q=Q]
               threadSet_iflive'T
               threadSet_ifunsafe'T
               threadSet_idle'T
               threadSet_global_refsT
               threadSet_cur
               irqs_masked_lift
               valid_irq_node_lift
               valid_irq_handlers_lift''
               threadSet_ctes_ofT
               threadSet_not_inQ
               threadSet_ct_idle_or_in_cur_domain'
               threadSet_valid_dom_schedule'
               | simp add: spec [OF y] domains)+
    apply (clarsimp simp: obj_at'_def projectKOs st_tcb_at'_def)
    apply (drule valid_queues_subset, simp+)
    apply (clarsimp simp: cur_tcb'_def valid_irq_node'_def valid_queues'_def)
    apply (cases P)
    apply (fastforce simp: domains ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def dest!: z z')+
    done
qed

lemmas threadSet_invs_trivialT_P =
    threadSet_invs_trivialT_P_Qf
      [where Qf=id, simplified,
       simplified ksReadyQueues_update_id addToQs_subset simp_thms]

lemmas threadSet_invs_trivialT =
    threadSet_invs_trivialT_P [where P=False, simplified]

lemmas threadSet_invs_trivial =
    threadSet_invs_trivialT [OF all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

lemma zobj_refs'_capRange:
  "s \<turnstile>' cap \<Longrightarrow> zobj_refs' cap \<subseteq> capRange cap"
apply (cases cap)
apply (simp_all add: valid_cap'_def capAligned_def capRange_def
                     is_aligned_no_overflow)
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
  by (wp getObject_obj_at', simp)

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
  apply (clarsimp simp: valid_obj'_def)
  apply (frule (1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (simp add: valid_obj'_def)
  apply (clarsimp elim!: obj_at'_weakenE)
  done

lemma corres_as_user':
  assumes y: "corres_underlying Id True r \<top> \<top> f g"
  shows      "corres r (tcb_at t) 
                       (tcb_at' t)
                       (as_user t f) (asUser t g)"
  proof -
  have L1: "corres (\<lambda>tcb con. tcb_context tcb = con)
             (tcb_at t) (tcb_at' t)
             (gets_the (get_tcb t)) (threadGet tcbContext t)"
    apply (rule corres_guard_imp)
      apply (rule corres_gets_the)
      apply (simp add: threadGet_def)
      apply (rule corres_rel_imp [OF corres_get_tcb])
      apply (simp add: tcb_relation_def)
     apply (simp add: tcb_at_def)+
    done
  have L2: "\<And>tcb tcb' con con'. \<lbrakk> tcb_relation tcb tcb'; con = con'\<rbrakk>
              \<Longrightarrow> tcb_relation (tcb \<lparr> tcb_context := con \<rparr>)
                               (tcb' \<lparr> tcbContext := con' \<rparr>)"
    by (case_tac tcb', simp add: tcb_relation_def)
  have L3: "\<And>r add tcb tcb' con con'. \<lbrakk> r () (); con = con'\<rbrakk> \<Longrightarrow>
            corres r (\<lambda>s. get_tcb add s = Some tcb)
                     (\<lambda>s'. (tcb', s') \<in> fst (getObject add s'))
                     (set_object add (TCB (tcb \<lparr>tcb_context := con\<rparr>)))
                     (setObject add (tcb' \<lparr> tcbContext := con' \<rparr>))"
    by (rule tcb_update_corres [OF L2],
        (simp add: tcb_cte_cases_def tcb_cap_cases_def exst_same_def)+)
  have L4: "\<And>con con'. con = con' \<Longrightarrow>
            corres (\<lambda>(irv, nc) (irv', nc'). r irv irv' \<and> nc = nc')
                   \<top> \<top> (select_f (f con)) (select_f (g con'))"
    using y
    by (fastforce simp: corres_underlying_def select_f_def split_def Id_def)
  show ?thesis
  apply (simp add: as_user_def asUser_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>tcb con. tcb_context tcb = con" in corres_split)
       apply (rule corres_split [OF _ L4])
          apply clarsimp
          apply (rule corres_split_nor)
             apply (rule corres_trivial, simp)
            apply (simp add: threadSet_def)
            apply (rule corres_symb_exec_r)
               prefer 4
               apply (rule no_fail_pre_and, wp)
              apply (rule L3)
                apply simp
               apply simp
              apply (wp select_f_inv | simp)+
      apply (rule L1)
     apply wp
   apply auto
  done
qed

lemma corres_as_user:
  assumes y: "corres_underlying Id True r \<top> \<top> f g"
  shows      "corres r (tcb_at t and invs) (tcb_at' t and invs') (as_user t f) (asUser t g)"
  apply (rule corres_guard_imp)
    apply (rule corres_as_user' [OF y])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  done

declare hoare_in_monad_post[wp]

lemma asUser_inv:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> asUser t f \<lbrace>\<lambda>x. P\<rbrace>"
proof -
  have P: "\<And>a b input. (a, b) \<in> fst (f input) \<Longrightarrow> b = input"
    by (rule use_valid [OF _ x], assumption, rule refl)
  have R: "\<And>x. tcbContext_update (\<lambda>_. tcbContext x) x = x"
    by (case_tac x, simp)
  show ?thesis
    apply (simp add: asUser_def split_def threadGet_def threadSet_def
                     liftM_def bind_assoc)
    apply (clarsimp simp: valid_def in_monad getObject_def setObject_def 
                          loadObject_default_def projectKOs objBits_simps
                          modify_def split_def updateObject_default_def
                          in_magnitude_check select_f_def
                   dest!: P)
    apply (simp add: R map_upd_triv)
    done
qed
  
lemma user_getreg_corres:
 "corres op = (tcb_at t) (tcb_at' t)
        (as_user t (get_register r)) (asUser t (getRegister r))"
  apply (rule corres_as_user')
  apply (clarsimp simp: get_register_def getRegister_def)
  done

lemma user_getreg_inv'[wp]:
  "\<lbrace>P\<rbrace> asUser t (getRegister r) \<lbrace>\<lambda>x. P\<rbrace>"
  apply (rule asUser_inv)
   apply (simp_all add: getRegister_def)
  done

lemma asUser_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> asUser t' f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: asUser_def bind_assoc split_def, wp select_f_inv)

lemmas asUser_typ_ats[wp] = typ_at_lifts [OF asUser_typ_at']

lemma inQ_context[simp]:
  "inQ d p (tcbContext_update f tcb) = inQ d p tcb"
  by (cases tcb, simp add: inQ_def)

lemma asUser_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> asUser t m \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_invs_trivial hoare_drop_imps | simp)+
  done


lemma asUser_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> asUser t m \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  done

crunch aligned'[wp]: asUser pspace_aligned'
  (simp: crunch_simps ignore: getObject wp: crunch_wps)
crunch distinct'[wp]: asUser pspace_distinct'
  (simp: crunch_simps ignore: getObject wp: crunch_wps)

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

lemma asUser_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> asUser t m \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: asUser_def split_def)
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

lemma asUser_st_tcb_at' [wp]:
  "\<lbrace>st_tcb_at' P t\<rbrace> asUser t' f \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_st_tcb_no_state)
    apply (case_tac tcb)
    apply simp
   apply (wp select_f_inv)
  done

crunch ct[wp]: asUser "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps wp: hoare_drop_imps getObject_inv_tcb setObject_ct_inv
     ignore: getObject setObject)

crunch cur_domain[wp]: asUser "\<lambda>s. P (ksCurDomain s)"
  (wp: hoare_drop_imps ignore: getObject setObject)

lemma asUser_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> asUser t m \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
apply (simp add: asUser_def tcb_in_cur_domain'_def threadGet_def)
apply (wp | wpc | simp)+
apply (rule_tac f="ksCurDomain" in hoare_lift_Pf)
apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | simp)+
apply (clarsimp simp: obj_at'_def)
done

crunch tcb_in_cur_domain'[wp]: asUser "\<lambda>s. P (tcb_in_cur_domain' t)"
  (simp: crunch_simps wp: hoare_drop_imps getObject_inv_tcb setObject_ct_inv
     ignore: getObject setObject)

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

lemma asUser_ct_in_state [wp]:
  "\<lbrace>ct_in_state' x\<rbrace> asUser t' f \<lbrace>\<lambda>_. ct_in_state' x\<rbrace>"
  by (wp ct_in_state_thread_state_lift')

lemma asUser_idle'[wp]:
  "\<lbrace>valid_idle'\<rbrace> asUser t m \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_idle')
       apply simp+
  apply (wp select_f_inv)
  done

lemma no_fail_asUser [wp]:
  "no_fail \<top> f \<Longrightarrow> no_fail (tcb_at' t) (asUser t f)"
  apply (simp add: asUser_def split_def)
  apply (rule no_fail_pre, wp)
   apply (simp add: no_fail_def)
   apply (wp hoare_drop_imps)
  apply simp
  done

lemma user_setreg_corres:
  "corres dc (tcb_at t) 
             (tcb_at' t)
             (as_user t (set_register r v)) 
             (asUser t (setRegister r v))"
  apply (simp add: set_register_def setRegister_def)
  apply (rule corres_as_user')
  apply (rule corres_modify')
   apply simp
  apply simp
  done

lemma gts_corres:
  "corres thread_state_relation (tcb_at t) (tcb_at' t)
          (get_thread_state t) (getThreadState t)"
  apply (simp add: get_thread_state_def getThreadState_def)
  apply (rule threadget_corres)
  apply (simp add: tcb_relation_def)
  done

lemma gts_inv'[wp]: "\<lbrace>P\<rbrace> getThreadState t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getThreadState_def) wp

lemma gts_wf'[wp]: "\<lbrace>tcb_at' t and invs'\<rbrace> getThreadState t \<lbrace>valid_tcb_state'\<rbrace>"
  apply (simp add: getThreadState_def threadGet_def liftM_def)
  apply wp
  apply (rule hoare_chain)
    apply (rule getObject_valid_obj)
     apply simp
    apply (simp add: objBits_simps)
   apply clarsimp
  apply (simp add: valid_obj'_def valid_tcb'_def)
  done

lemma gts_st_tcb_at'[wp]: "\<lbrace>st_tcb_at' P t\<rbrace> getThreadState t \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: getThreadState_def threadGet_def liftM_def)
  apply wp
  apply (rule hoare_chain)
    apply (rule obj_at_getObject)
    apply (clarsimp simp: loadObject_default_def projectKOs in_monad)
   apply (simp add: st_tcb_at'_def)
  apply simp
  done
  
lemma isBlocked_def2:
  "isBlocked t = liftM (Not \<circ> activatable') (getThreadState t)"
  apply (unfold isBlocked_def fun_app_def)
  apply (fold liftM_def)
  apply (rule arg_cong [where f="\<lambda>f. liftM f (getThreadState t)"])
  apply (rule ext)
  apply (simp split: Structures_H.thread_state.split)
  done

lemma isRunnable_def2:
  "isRunnable t = liftM runnable' (getThreadState t)"
  apply (simp add: isRunnable_def isBlocked_def2 liftM_def)
  apply (rule bind_eqI, rule ext, rule arg_cong)
  apply (case_tac state)
  apply (clarsimp)+
  done

lemma isBlocked_inv[wp]:
  "\<lbrace>P\<rbrace> isBlocked t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: isBlocked_def2 | wp gts_inv')+

lemma isRunnable_inv[wp]:
  "\<lbrace>P\<rbrace> isRunnable t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: isRunnable_def2 | wp gts_inv')+

lemma isRunnable_wp[wp]:
  "\<lbrace>\<lambda>s. Q (st_tcb_at' (runnable') t s) s\<rbrace> isRunnable t \<lbrace>Q\<rbrace>"
  apply (simp add: isRunnable_def2)
  apply wp
  apply (simp add: getThreadState_def threadGet_def)
  apply wp
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
  by (force intro: ext)


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
   apply (rule no_fail_pre, wp)
  apply (clarsimp simp: setQueue_def in_monad set_tcb_queue_def return_def
                        simpler_modify_def)
  apply (fastforce simp: state_relation_def ready_queues_relation_def
                        trans_state_update'[symmetric])
  done


lemma trans_state_triv[simp]:
  "trans_state (\<lambda>e. (exst s)) s = s"
  by simp

lemma getPriority_not_queued:
  "\<lbrace>Invariants_H.valid_queues and obj_at' (\<lambda>obj. \<not> tcbQueued obj) t\<rbrace> threadGet tcbPriority t \<lbrace>\<lambda>rv s. t \<notin> set (ksReadyQueues s (d, rv))\<rbrace>"
  apply (rule_tac Q="\<lambda>rv. Invariants_H.valid_queues and obj_at' (\<lambda>obj. \<not> tcbQueued obj) t" in hoare_strengthen_post)
   apply wp
  apply clarsimp
  apply (drule (1) valid_queues_obj_at'D)
  apply (clarsimp simp: inQ_def obj_at'_def)
  done

lemma ready_queues_update[simp]: "ready_queues_update (\<lambda>_. ready_queues a) a = a"
  apply simp
  done

lemma getQueue_corres: "corres op = \<top> \<top> (get_tcb_queue qdom prio) (getQueue qdom prio)"
  apply (clarsimp simp add: getQueue_def state_relation_def ready_queues_relation_def get_tcb_queue_def gets_def)
  apply (fold gets_def)
  apply simp
  done

lemma tcbSchedEnqueue_corres:
  "corres dc (is_etcb_at t) (tcb_at' t and Invariants_H.valid_queues and valid_queues') (tcb_sched_action (tcb_sched_enqueue) t) (tcbSchedEnqueue t)"
  apply (simp only: tcbSchedEnqueue_def tcb_sched_action_def)
  apply (rule corres_symb_exec_r [OF _ _ threadGet_inv, where Q'="\<lambda>rv. tcb_at' t and Invariants_H.valid_queues and valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
    defer
    apply (wp threadGet_obj_at', simp, simp)
   apply (rule no_fail_pre, wp, simp)
  apply (case_tac queued)
   apply (simp add: unless_def when_def)
   apply (rule corres_no_failI)
    apply (rule no_fail_pre, wp)
   apply (clarsimp simp: in_monad ethread_get_def gets_the_def bind_assoc
                         assert_opt_def exec_gets is_etcb_at_def get_etcb_def get_tcb_queue_def
                         set_tcb_queue_def simpler_modify_def)
    
   apply (subgoal_tac "tcb_sched_enqueue t (ready_queues a (tcb_domain y) (tcb_priority y))
                       = (ready_queues a (tcb_domain y) (tcb_priority y))")
    apply (simp add: in_monad ready_queues_relation_def state_relation_def cong: if_cong)
   apply (clarsimp simp: tcb_sched_enqueue_def state_relation_def 
                         valid_queues'_def ready_queues_relation_def
                         ekheap_relation_def etcb_relation_def
                         obj_at'_def inQ_def projectKO_eq project_inject)
   apply (drule_tac x=t in bspec,clarsimp)
   apply (drule_tac x="tcb_domain y" in spec)
   apply (drule_tac x="tcb_priority y" in spec) back
   apply clarsimp
  apply (clarsimp simp: unless_def when_def cong: if_cong)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[where r'="op =", OF _ ethreadget_corres])
       apply (rule corres_split[where r'="op =", OF _ ethreadget_corres])
          apply (rule corres_split[where r'="op ="])
             apply (rule corres_split_noop_rhs2)
                apply (rule threadSet_corres_noop, simp_all add: tcb_relation_def exst_same_def)[1]
               apply (simp add: tcb_sched_enqueue_def)
               apply (intro conjI impI)
                apply (rule corres_guard_imp)
                  apply (rule setQueue_corres)
                 prefer 3
                 apply (rule_tac P=\<top> and Q="K (t \<notin> set queuea)" in corres_assume_pre)
                 apply (wp getQueue_corres getObject_tcb_wp  | simp add: etcb_relation_def threadGet_def)+
  apply (fastforce simp: valid_queues_def obj_at'_def inQ_def 
                         projectKO_eq project_inject)
done


definition
  weak_sch_act_wf :: "scheduler_action \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "weak_sch_act_wf sa = (\<lambda>s. \<forall>t. sa = SwitchToThread t \<longrightarrow> st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s)"

declare trans_state_update'[symmetric,simp]

lemma set_sa_corres:
  "sched_act_relation sa sa'
    \<Longrightarrow> corres dc \<top> \<top> (set_scheduler_action sa) (setSchedulerAction sa')"
  apply (simp add: setSchedulerAction_def set_scheduler_action_def)
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp: in_monad simpler_modify_def state_relation_def)
  done

lemma get_sa_corres:
  "corres sched_act_relation \<top> \<top> (gets scheduler_action) getSchedulerAction"
  apply (simp add: getSchedulerAction_def)
  apply (clarsimp simp: state_relation_def)
  done

lemma rescheduleRequired_corres:
  "corres dc (weak_valid_sched_action and valid_etcbs) (Invariants_H.valid_queues and valid_queues' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
     (reschedule_required) rescheduleRequired"
  apply (simp add: rescheduleRequired_def reschedule_required_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ get_sa_corres])
      apply (rule_tac P="case action of switch_thread t \<Rightarrow> ?P t | _ \<Rightarrow> \<top>"
              and P'="case actiona of SwitchToThread t \<Rightarrow> ?P' t | _ \<Rightarrow> \<top>" in corres_split[where r'=dc])
         apply (rule set_sa_corres)
         apply simp
        apply (case_tac action)
          apply simp
         apply simp
         apply (rule tcbSchedEnqueue_corres)
        apply simp
       apply (wp | wpc | simp)+
   apply (force dest: st_tcb_weakenE simp: in_monad weak_valid_sched_action_def valid_etcbs_def split: Deterministic_A.scheduler_action.split)
  apply simp
  apply (clarsimp simp: weak_sch_act_wf_def st_tcb_at' split: scheduler_action.splits)
  done

lemma sch_act_simple_imp_weak_sch_act_wf:
  "sch_act_simple s \<Longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  by (clarsimp simp add: sch_act_simple_def weak_sch_act_wf_def)

lemma no_fail_false:
  "no_fail (\<lambda>_. False) f"
  by (simp add: no_fail_def)

lemma rescheduleRequired_corres_simple:
  "corres dc \<top> sch_act_simple
     (set_scheduler_action choose_new_thread) rescheduleRequired"
  apply (simp add: rescheduleRequired_def)
  apply (rule corres_symb_exec_r[where Q'="\<lambda>rv s. rv = ResumeCurrentThread \<or> rv = ChooseNewThread"])
     apply (rule corres_symb_exec_r)
        apply (rule set_sa_corres, simp)
       apply (wp | clarsimp split: scheduler_action.split)+
    apply (wp | clarsimp simp: sch_act_simple_def split: scheduler_action.split)+
  apply (simp add: getSchedulerAction_def, rule no_fail_pre, wp)
  done

lemma weak_sch_act_wf_lift:
  assumes pre: "\<And>P. \<lbrace>\<lambda>s. P (sa s)\<rbrace> f \<lbrace>\<lambda>rv s. P (sa s)\<rbrace>"
               "\<And>t. \<lbrace>st_tcb_at' runnable' t\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
               "\<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_in_cur_domain' t\<rbrace>"
  shows "\<lbrace>\<lambda>s. weak_sch_act_wf (sa s) s\<rbrace> f \<lbrace>\<lambda>rv s. weak_sch_act_wf (sa s) s\<rbrace>"
  apply (simp only: weak_sch_act_wf_def imp_conv_disj)
  apply (intro hoare_vcg_all_lift hoare_vcg_conj_lift hoare_vcg_disj_lift pre | simp)+
  done

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
  = weak_sch_act_wf_lift[OF threadSet_nosch threadSet_st_tcb_no_state threadSet_tcbDomain_triv]

lemma tcbSchedDequeue_weak_sch_act_wf[wp]:
  "\<lbrace> \<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace> tcbSchedDequeue a \<lbrace> \<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadSet_weak_sch_act_wf | simp add: crunch_simps)+
  done

lemma no_queues_in_tcb_relation[simp]:
  "tcb_relation tcb (tcbQueued_update F tcb') = tcb_relation tcb tcb'"
  by (clarsimp simp: tcb_relation_def)

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
  "corres dc (is_etcb_at t) (tcb_at' t and Invariants_H.valid_queues) (tcb_sched_action tcb_sched_dequeue t) (tcbSchedDequeue t)"
  apply (simp only: tcbSchedDequeue_def tcb_sched_action_def)
  apply (rule corres_symb_exec_r[OF _ _ threadGet_inv, where Q'="\<lambda>rv. tcb_at' t and Invariants_H.valid_queues and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
    defer
    apply (wp threadGet_obj_at', simp, simp)
   apply (rule no_fail_pre, wp, simp)
  apply (case_tac queued)
   defer
   apply (simp add: when_def)
   apply (rule corres_no_failI)
    apply (rule no_fail_pre, wp)
   apply (clarsimp simp: in_monad ethread_get_def set_tcb_queue_def is_etcb_at_def state_relation_def)
   apply (subgoal_tac "t \<notin> set (ready_queues a (tcb_domain y) (tcb_priority y))")
    prefer 2
    apply (force simp: tcb_sched_dequeue_def Invariants_H.valid_queues_def
           ready_queues_relation_def obj_at'_def inQ_def projectKO_eq project_inject)
   apply (subst gets_the_exec)
    apply (simp add: get_etcb_def)
   apply (subst gets_the_exec)
    apply (simp add: get_etcb_def)
   apply (simp add: exec_gets simpler_modify_def get_etcb_def ready_queues_relation_def cong: if_cong get_tcb_queue_def)
  apply (simp add: when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="op =", OF _ ethreadget_corres])
       apply (rule corres_split[where r'="op =", OF _ ethreadget_corres])
          apply (rule corres_split[where r'="op ="])
             apply (rule corres_split_noop_rhs2)
                apply (rule threadSet_corres_noop, simp_all add: tcb_relation_def exst_same_def)[1]
               apply (simp add: tcb_sched_dequeue_def)
               apply (rule setQueue_corres)
              apply wp
            apply simp
          apply (rule getQueue_corres)
         apply (wp | simp add: etcb_relation_def)+
  done

lemma thread_get_test: "do cur_ts \<leftarrow> get_thread_state cur; g (test cur_ts) od =
       do t \<leftarrow> (thread_get (\<lambda>tcb. test (tcb_state tcb)) cur); g t od"
  apply (simp add: get_thread_state_def thread_get_def)
  done


lemma thread_get_isRunnable_corres: "corres op = (tcb_at t) (tcb_at' t) (thread_get (\<lambda>tcb. runnable (tcb_state tcb)) t) (isRunnable t)" 
  apply (simp add:  isRunnable_def getThreadState_def threadGet_def
                   thread_get_def)
  apply (fold liftM_def)
  apply simp
  apply (rule corres_rel_imp)
   apply (rule assert_get_tcb_corres)
  apply (clarsimp simp add: tcb_relation_def thread_state_relation_def)
  apply (case_tac "tcb_state x",simp_all)
  done


lemma corres_return_trivial: "corres_underlying srel nf dc \<top> \<top> (return a) (return b)"
  apply (simp add: corres_underlying_def return_def)
  done

lemma sts_corres:
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
       apply simp
       apply (subst thread_get_test[where test="runnable"])
       apply (rule corres_split[OF _ thread_get_isRunnable_corres])
         apply (rule corres_split[OF _ gct_corres])
           apply (rule corres_split[OF _ get_sa_corres])
             apply (simp only: when_def)
             apply (rule corres_if[where Q=\<top> and Q'=\<top>])
               apply (rule iffI)
                apply clarsimp+
               apply (case_tac rva,simp_all)[1]
              apply (wp rescheduleRequired_corres_simple corres_return_trivial | simp)+
      apply (rule threadset_corres, (simp add: tcb_relation_def exst_same_def)+)
     apply (wp hoare_vcg_conj_lift[where Q'="\<top>\<top>"] | simp add: sch_act_simple_def)+
   done

crunch tcb'[wp]: rescheduleRequired "tcb_at' addr"
  (simp: unless_def)

crunch tcb'[wp]: tcbSchedDequeue "tcb_at' addr"
crunch tcb'[wp]: setThreadState "tcb_at' addr"
  (simp: crunch_simps)

lemma valid_tcb_tcbQueued:
  "valid_tcb' (tcbQueued_update f tcb) = valid_tcb' tcb"
  by (cases tcb, rule ext, simp add: valid_tcb'_def tcb_cte_cases_def)

crunch valid_objs'[wp]: rescheduleRequired valid_objs'
  (simp: unless_def valid_tcb_tcbQueued crunch_simps)

lemma tcbSchedDequeue_valid_objs' [wp]: "\<lbrace> valid_objs' \<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_objs' \<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadSet_valid_objs')
     apply (clarsimp simp add: valid_tcb'_def tcb_cte_cases_def)
    apply (wp)
  apply (simp split: split_if cong: if_cong)
  apply (wp)
  done

lemma sts_valid_objs':
  "\<lbrace>valid_objs' and valid_tcb_state' st\<rbrace> 
  setThreadState st t 
  \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: setThreadState_def setQueue_def isRunnable_def isBlocked_def)
  apply (wp threadSet_valid_objs')
     apply (simp add: valid_tcb'_def tcb_cte_cases_def)
     apply (wp threadSet_valid_objs' | simp)+
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def)
  done

lemma ssa_lift[wp]:
  "(\<And>s. P s \<longrightarrow> P (s \<lparr>ksSchedulerAction := sa\<rparr>)) \<Longrightarrow>
   \<lbrace>P\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: setSchedulerAction_def | wp)+

crunch aligned'[wp]: rescheduleRequired "pspace_aligned'"
  (simp: unless_def)
crunch distinct'[wp]: rescheduleRequired "pspace_distinct'"
  (simp: unless_def)
crunch no_0_obj'[wp]: rescheduleRequired "no_0_obj'"
  (simp: unless_def ignore: getObject)
crunch ctes_of[wp]: rescheduleRequired "\<lambda>s. P (ctes_of s)"
  (simp: unless_def)

crunch aligned'[wp]: tcbSchedDequeue "pspace_aligned'"
crunch distinct'[wp]: tcbSchedDequeue "pspace_distinct'"
crunch no_0_obj'[wp]: tcbSchedDequeue "no_0_obj'"
crunch ctes_of[wp]: tcbSchedDequeue "\<lambda>s. P (ctes_of s)"

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

crunch st_tcb_at'[wp]: setQueue "\<lambda>s. P (st_tcb_at' P' t s)"
crunch ct[wp]: setQueue "\<lambda>s. P (ksCurThread s)"
crunch cur_domain[wp]: setQueue "\<lambda>s. P (ksCurDomain s)"

lemma setQueue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setQueue d p xs \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
apply (simp add: setQueue_def tcb_in_cur_domain'_def)
apply wp
apply (simp add: ps_clear_def projectKOs obj_at'_def)
done

lemma setQueue_sch_act:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace> 
  setQueue d p xs 
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift)

lemma setQueue_valid_queues:
  "\<lbrace>Invariants_H.valid_queues
      and (\<lambda>s. \<forall>t \<in> set ts. obj_at' (inQ d p and runnable' \<circ> tcbState) t s)
      and K (distinct ts) and K (d \<le> maxDomain \<and> p \<le> maxPriority)\<rbrace>
  setQueue d p ts
  \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: setQueue_def Invariants_H.valid_queues_def)
  apply wp
  apply force
  done

lemma setQueue_valid_queues':
  "\<lbrace>valid_queues' and (\<lambda>s. \<forall>t. obj_at' (inQ d p) t s \<longrightarrow> t \<in> set ts)\<rbrace>
    setQueue d p ts \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp | simp add: valid_queues'_def setQueue_def)+

lemma setQueue_cur:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setQueue d p ts \<lbrace>\<lambda>rv s. cur_tcb' s\<rbrace>"
  apply (simp add: setQueue_def cur_tcb'_def)
  apply wp
  apply clarsimp
  done

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
  apply (frule_tac P1="op = (ksSchedulerAction s)"
                in use_valid [OF _ threadSet_nosch],
         rule refl)
  apply (frule_tac P1="op = (ksCurThread s)"
                in use_valid [OF _ threadSet_ct],
         rule refl)
  apply (frule_tac P1="op = (ksCurDomain s)"
                in use_valid [OF _ threadSet_cd],
         rule refl)
  apply (case_tac "ksSchedulerAction b",
         simp_all add: sch_act_simple_def ct_in_state'_def st_tcb_at'_def)
   apply (drule_tac t'1="ksCurThread s"
                and P1="activatable' \<circ> tcbState"
                 in use_valid [OF _ threadSet_obj_at'_really_strongest])
    apply (clarsimp elim!: obj_at'_weakenE)
   apply simp
  apply (rule conjI)
  apply (frule_tac t'1=word
               and P1="runnable' \<circ> tcbState"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
   apply (clarsimp elim!: obj_at'_weakenE, simp)
  apply (simp add: tcb_in_cur_domain'_def)
  apply (frule_tac t'1=word
               and P1="\<lambda>tcb. ksCurDomain b = tcbDomain tcb"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
   apply (clarsimp simp: o_def tcb_in_cur_domain'_def)
  apply clarsimp
  done

lemma threadSet_simple_sch_act:
  "\<lbrace>\<lambda>s. ksCurThread s \<noteq> t \<and> sch_act_simple s
      \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
    threadSet F t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule_tac P1="op = (ksSchedulerAction s)"
                in use_valid [OF _ threadSet_nosch],
         rule refl)
  apply (frule_tac P1="op = (ksCurThread s)"
                in use_valid [OF _ threadSet_ct],
         rule refl)
  apply (case_tac "ksSchedulerAction b", simp_all add: sch_act_simple_def)
  apply (drule_tac t'1="ksCurThread s"
               and P1="activatable' \<circ> tcbState"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
   apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def o_def)
  apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def)
  done


lemma threadSet_sch_act_switch:
  "\<lbrace>\<lambda>s. ksCurThread s \<noteq> t \<and> sch_act_not t s \<and> 
       sch_act_wf (ksSchedulerAction s) s\<rbrace> 
  threadSet F t 
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule_tac P1="op = (ksSchedulerAction s)"
                in use_valid [OF _ threadSet_nosch],
         rule refl)
  apply (frule_tac P1="op = (ksCurThread s)"
                in use_valid [OF _ threadSet_ct],
         rule refl)
  apply (frule_tac P1="op = (ksCurDomain s)"
                in use_valid [OF _ threadSet_cd],
         rule refl)
  apply (case_tac "ksSchedulerAction b", simp_all add: sch_act_sane_def)
   apply (drule_tac t'1="ksCurThread s"
                and P1="activatable' o tcbState"
                 in use_valid [OF _ threadSet_obj_at'_really_strongest])
    apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def o_def)
   apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def)
  apply (rule conjI)
  apply (clarsimp simp: st_tcb_at'_def)
  apply (frule_tac t'1="word"
               and P1="runnable' o tcbState"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
   apply (clarsimp simp: st_tcb_at'_def o_def, simp)
  apply (clarsimp simp: tcb_in_cur_domain'_def)
  apply (drule_tac t'1="word"
               and P1="op = (ksCurDomain b) o tcbDomain"
                in use_valid [OF _ threadSet_obj_at'_really_strongest])
   apply (clarsimp simp: st_tcb_at'_def tcb_in_cur_domain'_def o_def)
  apply (clarsimp simp: st_tcb_at'_def tcb_in_cur_domain'_def o_def)
  done

lemma threadSet_st_tcb_at_state:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (if p = t 
        then obj_at' (\<lambda>tcb. P (tcbState (f tcb))) t s 
        else st_tcb_at' P p s)\<rbrace> 
  threadSet f t \<lbrace>\<lambda>_. st_tcb_at' P p\<rbrace>"
  apply (rule hoare_chain)
    apply (rule threadSet_obj_at'_really_strongest)
   prefer 2
   apply (simp add: st_tcb_at'_def)
  apply (clarsimp split: if_splits simp: st_tcb_at'_def o_def)
  done

lemma threadSet_tcbDomain_triv':
  "\<lbrace>tcb_in_cur_domain' t' and K (t \<noteq> t')\<rbrace> threadSet f t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
apply (simp add: tcb_in_cur_domain'_def)
apply (rule hoare_assume_pre)
apply simp
apply (rule_tac f="ksCurDomain" in hoare_lift_Pf)
apply (wp threadSet_obj_at'_strongish getObject_tcb_wp | simp add: assms)+
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
   apply (wp threadSet_st_tcb_at_state)
   apply clarsimp
  apply wp
  apply (clarsimp)
  apply (wp threadSet_st_tcb_at_state threadSet_tcbDomain_triv' | clarsimp)+
  done

lemma rescheduleRequired_sch_act'[wp]:
  "\<lbrace>\<top>\<rbrace>
      rescheduleRequired
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp)+
  done

lemma setObject_queued_st_tcb_at'[wp]:
  "\<lbrace>st_tcb_at' P t' and obj_at' (op = tcb) t\<rbrace>
    setObject t (tcbQueued_update f tcb)
   \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: st_tcb_at'_def)
  apply (rule hoare_pre)
  apply (wp setObject_tcb_strongest)
  apply (clarsimp simp: obj_at'_def)
  done

lemma setObject_queued_ct_activatable'[wp]:
  "\<lbrace>ct_in_state' activatable' and obj_at' (op = tcb) t\<rbrace>
    setObject t (tcbQueued_update f tcb)
   \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def)
  apply (rule hoare_pre)
   apply (wps setObject_ct_inv)
   apply (wp setObject_tcb_strongest)
  apply (clarsimp simp: obj_at'_def)
  done

lemma threadSet_queued_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    threadSet (tcbQueued_update f) t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: sch_act_wf_cases
            split: scheduler_action.split)
  apply (wp hoare_vcg_conj_lift)
   apply (simp add: threadSet_def)
   apply (wp static_imp_wp)
   apply (wps setObject_sa_unchanged)
   apply (wp static_imp_wp getObject_tcb_wp)+
   apply (clarsimp simp: obj_at'_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_conj_lift hoare_imp_lift_something)+
    apply (simp add: threadSet_def)
    apply (wp getObject_tcb_wp)
    apply (clarsimp simp: obj_at'_def)
  apply (wp tcb_in_cur_domain'_lift | simp add: obj_at'_def)+
  done

lemma tcbSchedEnqueue_st_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. P(st_tcb_at' P' t' s)\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. P(st_tcb_at' P' t' s)\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp threadSet_st_tcb_no_state | clarsimp)+
  done

lemma tcbSchedDequeue_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp setQueue_sch_act | simp)+
  done

crunch nosch: tcbSchedDequeue "\<lambda>s. P (ksSchedulerAction s)"

lemma sts_sch_act':
  "\<lbrace>\<lambda>s. (\<not> runnable' st \<longrightarrow> sch_act_not t s) \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace> 
  setThreadState st t  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp | simp)+
  apply (case_tac "runnable' st")
   apply ((wp threadSet_runnable_sch_act hoare_drop_imps | simp)+)[1]
  apply (rule_tac Q="\<lambda>rv s. st_tcb_at' (Not \<circ> runnable') t s \<and>
                     (ksCurThread s \<noteq> t \<or> ksSchedulerAction s \<noteq> ResumeCurrentThread \<longrightarrow>
                            sch_act_wf (ksSchedulerAction s) s)"
               in hoare_post_imp)
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def projectKOs)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre)
   apply (wp threadSet_st_tcb_at_state threadSet_sch_act_wf
             hoare_vcg_disj_lift|simp)+
  done

lemma sts_sch_act[wp]:
  "\<lbrace>\<lambda>s. (\<not> runnable' st \<longrightarrow> sch_act_simple s) \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setThreadState_def)
  apply wp
  apply simp
  apply (case_tac "runnable' st")
   apply (rule_tac Q="\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
                in hoare_pre_imp, simp)
   apply ((wp hoare_drop_imps threadSet_runnable_sch_act | simp)+)[1]
  apply (rule_tac Q="\<lambda>rv s. st_tcb_at' (Not \<circ> runnable') t s \<and>
                     (ksCurThread s \<noteq> t \<or> ksSchedulerAction s \<noteq> ResumeCurrentThread \<longrightarrow>
                            sch_act_wf (ksSchedulerAction s) s)"
               in hoare_post_imp)
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def projectKOs)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre)
   apply (wp threadSet_st_tcb_at_state threadSet_sch_act_wf
             hoare_vcg_disj_lift|simp)+
  apply (auto simp: sch_act_simple_def)
  done

lemma ssa_sch_act_simple[wp]:
  "sa = ResumeCurrentThread \<or> sa = ChooseNewThread \<Longrightarrow>
   \<lbrace>\<top>\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (simp add: setSchedulerAction_def sch_act_simple_def)
  apply wp
  apply simp
  done

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

lemma more_queued[simp]:
  "\<not> (inQ d p tcb \<and> \<not> inQ d p (tcbQueued_update (\<lambda>_. True) tcb))"
  by (cases tcb, simp add: inQ_def)

lemma setQueue_after:
  "(setQueue d p q >>= (\<lambda>rv. threadSet f t)) =
   (threadSet f t >>= (\<lambda>rv. setQueue d p q))"
  apply (simp add: setQueue_def)
  apply (rule oblivious_modify_swap)
  apply (simp add: threadSet_def getObject_def setObject_def
                   loadObject_default_def
                   split_def projectKO_def2 alignCheck_assert
                   magnitudeCheck_assert updateObject_default_def
                   projectKO_def2)
  apply (intro oblivious_bind, simp_all)
  done

lemma threadSet_obj_at':
  "\<lbrace>\<lambda>s. tcb_at' t s
       \<longrightarrow> obj_at' (\<lambda>tcb. if t = t' then P (f tcb) else P tcb) t' s\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_strongest getObject_tcb_wp)
  apply (cases "t = t'")
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbSchedEnqueue_sch_act[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp setQueue_sch_act | clarsimp)+
  done

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

lemma tcbSchedEnqueue_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues
    and st_tcb_at' runnable' t
    and valid_objs' \<rbrace>
     tcbSchedEnqueue t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def setQueue_after)
  apply (rule hoare_pre)
   apply (rule_tac B="\<lambda>rv. Invariants_H.valid_queues
                             and st_tcb_at' runnable' t
                             and obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t
                             and obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t
                             and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
    apply (rename_tac queued)
    apply (case_tac queued, simp_all add: unless_def when_def)[1]
     apply (wp setQueue_valid_queues threadSet_valid_queues hoare_vcg_const_Ball_lift threadGet_obj_at' threadGet_wp| simp)+
     apply (fastforce simp: Invariants_H.valid_queues_def inQ_def obj_at'_def st_tcb_at'_def projectKOs valid_tcb'_def)
    apply (wp threadGet_wp)
    apply (subgoal_tac "\<exists>tcb. obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t s \<and> obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t s")
    apply (fastforce simp: obj_at'_def st_tcb_at'_def )
    apply (fastforce elim: valid_objs'_maxDomain valid_objs'_maxPriority)
  done

lemma valid_queues_ksSchedulerAction_update[simp]:
  "Invariants_H.valid_queues (s\<lparr>ksSchedulerAction := sa\<rparr>) = Invariants_H.valid_queues s"
  by (simp add: Invariants_H.valid_queues_def)

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

lemma sts_valid_queues:
  "\<lbrace>\<lambda>s. Invariants_H.valid_queues s \<and>
    ((\<exists>p. t \<in> set(ksReadyQueues s p)) \<longrightarrow> runnable' st)\<rbrace>
   setThreadState st t \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_valid_queues_sch_act_simple
            threadSet_valid_queues [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

lemma sts_valid_queues_not_runnable':
  "\<lbrace>Invariants_H.valid_queues and st_tcb_at' (Not \<circ> runnable') t\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (wp sts_valid_queues)
  apply (simp only: Invariants_H.valid_queues_def)
  apply (clarsimp)
  apply (drule_tac x=a in spec)
  apply (drule_tac x=b in spec)
  apply (clarify)
  apply (drule(1) bspec)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
  done

lemma tcbSchedEnqueue_valid_queues'[wp]:
  "\<lbrace>valid_queues' and st_tcb_at' runnable' t \<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def)
  apply (rule hoare_pre)
   apply (rule_tac B="\<lambda>rv. valid_queues' and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
    apply (rename_tac queued)
    apply (case_tac queued, simp_all add: unless_def when_def)[1]
     apply (wp threadSet_valid_queues' setQueue_valid_queues' | simp)+
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

lemma rescheduleRequired_valid_queues'[wp]:
  "\<lbrace>\<lambda>s. valid_queues' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp | fastforce simp: valid_queues'_def)+
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
  apply (fastforce simp: inQ_def obj_at'_def st_tcb_at'_def)
  done

lemma valid_tcb'_tcbState_update:"\<And>tcb s st . \<lbrakk> valid_tcb_state' st s; valid_tcb' tcb s \<rbrakk> \<Longrightarrow> valid_tcb' (tcbState_update (\<lambda>_. st) tcb) s"
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
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)
                            \<and> P (ksReadyQueues s p)" in hoare_seq_ext)
  apply (wp | clarsimp)+
  apply (case_tac "x")
  apply (clarsimp)+
  apply (wp)
  done

lemma setSchedulerAction_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setSchedulerAction act \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wp, simp)

lemma threadSet_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (simp add: threadSet_def | wp updateObject_default_inv)+

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
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp)
    apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
   apply (wp)
  apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
  apply (wp)
  done

lemma rescheduleRequired_ksQ':
  "\<lbrace>\<lambda>s. t \<notin> set (ksReadyQueues s p) \<and> sch_act_not t s \<rbrace>
   rescheduleRequired \<lbrace>\<lambda>_ s. t \<notin> set (ksReadyQueues s p)\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: rescheduleRequired_def)
  apply (wp, wpc, wp tcbSchedEnqueue_ksQ)
  apply (clarsimp)
  done

crunch ksQ[wp]: getCurThread "\<lambda>s. P (ksReadyQueues s p)"

lemma threadSet_tcbState_st_tcb_at':
  "\<lbrace>\<lambda>s. P st \<rbrace> threadSet (tcbState_update (\<lambda>_. st)) t \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: threadSet_def st_tcb_at'_def)
  apply (wp setObject_tcb_strongest)
  apply (clarsimp)
  apply (wp)
  done

lemma st_tcb'_weakenE:
  "\<lbrakk> st_tcb_at' P t s; \<And>st. P st \<Longrightarrow> P' st \<rbrakk> \<Longrightarrow> st_tcb_at' P' t s"
  apply (simp add: st_tcb_at'_def)
  apply (erule obj_at'_weakenE)
  apply clarsimp
  done

lemma isRunnable_const:
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> isRunnable t \<lbrace>\<lambda>runnable _. runnable \<rbrace>"
  apply (simp add: isRunnable_def)
  apply (wp)
  apply (erule st_tcb'_weakenE)
  apply (case_tac st, clarsimp+)
  done

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
                  [OF gct_wp getCurThread_ksQ]])
  apply (rename_tac ct)
  apply (case_tac "ct\<noteq>t")
   apply (clarsimp simp: when_def)
   apply (wp)[1]
  apply (clarsimp)
  done

crunch ct'[wp]: getThreadState "\<lambda>s. P (ksCurThread s)"
crunch nosch[wp]: getThreadState "\<lambda>s. P (ksSchedulerAction s)"

lemma tcbSchedDequeue_ksQ:
  "\<lbrace>\<lambda>s. P (set (ksReadyQueues s (d, p)) - {t})
        \<and> obj_at' (tcbQueued and op = d \<circ> tcbDomain and op = p \<circ> tcbPriority) t s\<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. P (set (ksReadyQueues s (d, p)))\<rbrace>"
  (is "\<lbrace>\<lambda>s. ?NT s \<and> ?OA s\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadGet_wp)
  apply (fastforce simp: set_minus_filter_out obj_at'_def projectKOs)
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

lemma load_word_offs_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres op = \<top> (valid_ipc_buffer_ptr' a) (load_word_offs a y) (loadWordUser (a + of_nat y * 4))"
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

lemma store_word_offs_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres dc (in_user_frame a) (valid_ipc_buffer_ptr' a)
                   (store_word_offs a y w) (storeWordUser (a + of_nat y * 4) w)"
  apply (simp add: storeWordUser_def bind_assoc[symmetric]
                   store_word_offs_def word_size_def)
  apply (rule corres_guard2_imp)
   apply (rule_tac F = "is_aligned a msg_align_bits" in corres_gen_asm2)
   apply (rule corres_guard1_imp)
    apply (rule_tac r'=dc in corres_split)
       apply (rule corres_machine_op)
       apply (rule corres_Id [OF refl])
        apply simp
       apply (rule no_fail_pre)
        apply (wp no_fail_storeWord)
       apply (erule_tac n=msg_align_bits in aligned_add_aligned)
         apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
         apply (simp add: word_bits_conv msg_align_bits)+
      apply (simp add: stateAssert_def)
      apply (rule_tac r'=dc in corres_split)
         apply (rule corres_assert)
        apply (rule corres_trivial)
        apply simp
       apply wp
   apply (simp add: in_user_frame_eq[OF y])
  apply simp
  apply (rule conjI)
  apply (frule (1) valid_ipc_buffer_ptr'D [OF y])
  apply (simp add: valid_ipc_buffer_ptr'_def)
  done

lemma load_word_corres:
  "corres op= \<top> 
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

lemma store_word_corres:
  "corres dc \<top>
     (typ_at' UserDataT (a && ~~ mask pageBits) and (\<lambda>s. is_aligned a 2))
     (do_machine_op (storeWord a w)) (storeWordUser a w)"
  unfolding storeWordUser_def
  apply (rule corres_gen_asm2)
  apply (rule corres_stateAssert_assume [rotated])
   apply (simp add: pointerInUserData_def)
  apply (rule corres_guard_imp)
    apply simp
    apply (rule corres_machine_op)
    apply (rule corres_Id [OF refl])
     apply simp
    apply (rule no_fail_pre)
     apply (wp no_fail_storeWord)
    apply assumption
   apply simp
  apply simp
  done

lemmas msgRegisters_unfold
  = State_H.msgRegisters_def
    msg_registers_def
    ARMMachineTypes.msgRegisters_def
        [unfolded upto_enum_def, simplified,
         unfolded fromEnum_def enum_register, simplified,
         unfolded toEnum_def enum_register, simplified]

lemma get_mrs_corres:
  "corres op= (tcb_at t)
              (tcb_at' t and option_case \<top> valid_ipc_buffer_ptr' buf)
              (get_mrs t buf mi) (getMRs t buf (message_info_map mi))"
  proof -
  have S: "get = gets id"
    by (simp add: gets_def)
  have T: "corres (\<lambda>con regs. regs = map con msg_registers) (tcb_at t) (tcb_at' t)
     (thread_get tcb_context t) (asUser t (mapM getRegister State_H.msgRegisters))"
    apply (subst thread_get_as_user)
    apply (rule corres_as_user')
    apply (subst mapM_gets)
     apply (simp add: getRegister_def)
    apply (simp add: S State_H.msgRegisters_def msg_registers_def)
    done
  show ?thesis
  apply (case_tac mi, simp add: get_mrs_def getMRs_def split del: split_if)
  apply (case_tac buf)
   apply (rule corres_guard_imp)
    apply (rule corres_split [where R = "\<lambda>_. \<top>" and R' =  "\<lambda>_. \<top>", OF _ T])
       apply simp
      apply wp
    apply simp
   apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ T])
      apply (simp only: option.simps return_bind fun_app_def
                        load_word_offs_def doMachineOp_mapM ef_loadWord)
      apply (rule corres_split_eqr)
         apply (rule corres_trivial, simp)
        apply (simp only: mapM_map_simp msgMaxLength_def msgLengthBits_def
                          msg_max_length_def o_def upto_enum_word)
        apply (rule corres_mapM [where r'="op =" and S="{a. fst a = snd a \<and> fst a < unat max_ipc_words}"])
              apply simp+
            apply (simp add: word_size)
	    apply (rule load_word_offs_corres)
 	    apply simp
           apply wp
         apply simp
         apply (unfold msg_registers_def msgRegisters_unfold)[1]
         apply simp
        apply (clarsimp simp: set_zip)
        apply (simp add: msg_registers_def msgRegisters_unfold max_ipc_words nth_append)
       apply (wp hoare_vcg_all_lift | simp add: valid_ipc_buffer_ptr'_def)+
  done
qed

lemmas doMachineOp_return = submonad_doMachineOp.return

lemma doMachineOp_bind:
 "\<lbrakk> empty_fail a; \<And>x. empty_fail (b x) \<rbrakk> \<Longrightarrow> doMachineOp (a >>= b) = (doMachineOp a >>= (\<lambda>rv. doMachineOp (b rv)))"
  by (blast intro: submonad_bind submonad_doMachineOp)

declare empty_fail_sequence_x[simp]

lemma zipWithM_x_doMachineOp:
  assumes m: "\<And>x y. empty_fail (m x y)"
  shows "doMachineOp (zipWithM_x m as bs) = zipWithM_x (\<lambda>a b. doMachineOp (m a b)) as bs"
proof -
  show ?thesis
    apply (simp add: zipWithM_x_def zipWith_def)
    apply (induct ("zip as bs"))
     apply (simp add: sequence_x_def doMachineOp_return)
    apply (clarsimp simp add: sequence_x_Cons)
    apply (subst doMachineOp_bind)
      apply (fastforce simp add: image_iff m intro: empty_fail_sequence_x)+
    done
qed

lemma zipWithM_x_corres:
  assumes x: "\<And>x x' y y'. ((x, y), (x', y')) \<in> S \<Longrightarrow> corres dc P P' (f x y) (f' x' y')"
  assumes y: "\<And>x x' y y'. ((x, y), (x', y')) \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x y \<lbrace>\<lambda>rv. P\<rbrace>"
      and z: "\<And>x x' y y'. ((x, y), (x', y')) \<in> S \<Longrightarrow> \<lbrace>P'\<rbrace> f' x' y' \<lbrace>\<lambda>rv. P'\<rbrace>"
      and a: "set (zip (zip xs ys) (zip xs' ys')) \<subseteq> S"
      and b: "length (zip xs ys) = length (zip xs' ys')"
  shows      "corres dc P P' (zipWithM_x f xs ys) (zipWithM_x f' xs' ys')"
  apply (simp add: zipWithM_x_mapM)
  apply (rule corres_split')
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

(* Levity: added (20090713 10:03:39) *)
declare storeWordUser_typ_at' [wp]

lemma valid_ipc_buffer_ptr'_def2:
  "valid_ipc_buffer_ptr' = (\<lambda>p s. (is_aligned p msg_align_bits \<and> typ_at' UserDataT (p && ~~ mask pageBits) s))"
  apply (rule ext, rule ext)
  apply (simp add: valid_ipc_buffer_ptr'_def)
  done

lemma storeWordUser_valid_ipc_buffer_ptr' [wp]:
  "\<lbrace>valid_ipc_buffer_ptr' p\<rbrace> storeWordUser p' w \<lbrace>\<lambda>_. valid_ipc_buffer_ptr' p\<rbrace>"
  unfolding valid_ipc_buffer_ptr'_def2
  by (wp hoare_vcg_all_lift storeWordUser_typ_at')

declare of_nat_power [simp del]
declare word_neq_0_conv [simp del]

lemma set_mrs_corres:
  assumes m: "mrs' = mrs"
  shows 
  "corres op= (tcb_at t and option_case \<top> in_user_frame buf)
              (tcb_at' t and option_case \<top> valid_ipc_buffer_ptr' buf)
              (set_mrs t buf mrs) (setMRs t buf mrs')"
proof -
  have setRegister_def2: "setRegister = (\<lambda>r v. modify (\<lambda>s. s ( r := v )))"
    by ((rule ext)+, simp add: setRegister_def)
  have P: "corres_underlying Id True dc \<top> \<top> 
              (modify (\<lambda>context reg.
                            if reg \<in> set (take (length mrs) msg_registers)
                            then mrs ! (the_index msg_registers reg) else context reg))
              (zipWithM_x setRegister State_H.msgRegisters
                  (take (length State_H.msgRegisters +
                         length (case buf of None \<Rightarrow> []
                                 | Some a \<Rightarrow>
                                     map (\<lambda>x. a + (x * 4))
                                      [1 + of_nat (length State_H.msgRegisters).e.msgMaxLength]))
                    mrs))"
    apply (simp add: setRegister_def2 zipWithM_x_modify)
    apply (subst zip_take_triv2)
     apply simp
    apply (rule corres_modify')
     apply clarsimp
     apply (rule ext)
     apply (subst fold_fun_upd)
      apply (simp add: msgRegisters_unfold)
     apply (simp add: msg_registers_def msgRegisters_def)
    apply simp
    done
  have S: "\<And>xs ys n m. m - n \<ge> length xs \<Longrightarrow> (zip xs (drop n (take m ys))) = zip xs (drop n ys)"
    apply (subst list_eq_iff_nth_eq)
    apply safe
     apply (simp add: min_def)
     apply clarsimp
     apply (drule not_leE)
     apply simp
    apply clarsimp
    apply (subst nth_drop)
     apply simp
     apply arith
    apply (subst nth_take)
     apply simp
    apply simp
    done
  have U: "map (toEnum :: nat \<Rightarrow> word32) [7 ..< 128] = map of_nat [7 ..< 128]"
    apply (rule map_cong[OF refl])
    apply (unfold set_upt)
    apply simp
    done
  show ?thesis using m
    apply (simp add: set_mrs_def setMRs_def word_size take_min_len
                     capTransferDataSize_def cong: option.case_cong
                del: upt.simps split del: split_if)
    apply (subst bind_assoc[symmetric], fold thread_set_def[simplified])
    apply (subst thread_set_as_user[where f="\<lambda>context. \<lambda>reg.
                      if reg \<in> set (take (length mrs) msg_registers)
                      then mrs ! (the_index msg_registers reg) else context reg"])
    apply (cases buf)
    apply (rule corres_guard_imp)
      apply (rule corres_split_nor [OF _ corres_as_user' [OF P]])
 	 apply (rule corres_trivial)
 	 apply (simp add: min_max.inf_commute msgRegisters_unfold zipWithM_x_Nil)
	 apply wp
     apply (simp del: upt.simps split del: split_if)+
   -- "buf = Some a"
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor [OF _ corres_as_user'])
         apply (clarsimp split del: split_if simp del: upt.simps)
         apply (rule corres_split_nor)
            apply (rule corres_trivial, clarsimp)
            apply (rule arg_cong [where f="\<lambda>x. of_nat (min (length mrs) x)"])
            apply (simp add: upto_enum_def msgMaxLength_def msgLengthBits_def
                             msg_max_length_def)
            apply (simp add: msgRegisters_unfold)
           apply (simp   add: zipWithM_x_doMachineOp number_of_mrs_def
                              upto_enum_def ef_storeWord
                         del: upt.simps
                   split del: split_if)
           apply (rule_tac S="{((x, y), (x', y')). y = y' \<and> x' = (a + (of_nat x * 4)) \<and> x < unat max_ipc_words}"
                        in zipWithM_x_corres)
               apply clarsimp
               apply (erule store_word_offs_corres)
              apply wp
            apply (simp add: S msgMaxLength_def msgLengthBits_def U
                             msg_max_length_def)
            apply (clarsimp simp: set_zip)
            apply (simp add: msgRegisters_unfold max_ipc_words)
           apply (simp add: S msgMaxLength_def msgLengthBits_def
                            msg_max_length_def)
           apply (simp add: msgRegisters_unfold)
          apply wp
        apply (insert P)
        apply simp
       apply (simp add: valid_ipc_buffer_ptr'_def2 | wp hoare_vcg_all_lift )+
    done
qed

lemma copy_mrs_corres:
  "corres op= (tcb_at s and tcb_at r
               and option_case \<top> in_user_frame sb
               and option_case \<top> in_user_frame rb
               and K (unat n \<le> msg_max_length))
              (tcb_at' s and tcb_at' r
               and option_case \<top> valid_ipc_buffer_ptr' sb
               and option_case \<top> valid_ipc_buffer_ptr' rb)
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
             (\<lambda>ra. do v \<leftarrow> as_user s (get_register ra);
                      as_user r (set_register ra v)
                   od)
             (take (unat n) msg_registers))
           (mapM
             (\<lambda>ra. do v \<leftarrow> asUser s (getRegister ra);
                      asUser r (setRegister ra v)
                   od)
             (take (unat n) State_H.msgRegisters))"
    apply (rule corres_guard_imp)
    apply (rule_tac S=Id in corres_mapM, simp+)
        apply (rule corres_split_eqr [OF user_setreg_corres user_getreg_corres])
        apply (wp | clarsimp simp: msg_registers_def msgRegisters_def)+
        done

  show ?thesis
    apply (rule corres_assume_pre)
    apply (simp add: copy_mrs_def copyMRs_def word_size
               cong: option.case_cong
          split del: split_if del: upt.simps)
    apply (cases sb)
     apply (simp add: R)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor [OF _ as_user_bit])
         apply (rule corres_trivial, simp)
        apply wp
      apply simp
     apply simp
    apply (cases rb)
     apply (simp add: R)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor [OF _ as_user_bit])
         apply (rule corres_trivial, simp)
        apply wp
      apply simp
     apply simp
    apply (simp add: R del: upt.simps)
    apply (rule corres_guard_imp)
      apply (rename_tac sb_ptr rb_ptr)
      apply (rule corres_split_nor [OF _ as_user_bit])
        apply (rule corres_split_eqr)
           apply (rule corres_trivial, simp)
          apply (rule_tac S="{(x, y). y = of_nat x \<and> x < unat max_ipc_words}" in corres_mapM, simp+)
              apply (rule corres_split_eqr)
	       apply (rule store_word_offs_corres)
	       apply simp
	       apply (rule load_word_offs_corres)
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
  apply (drule use_valid [OF _ getCTE_sp[where P="op = s'"], OF _ refl, standard])
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
     apply (clarsimp simp: of_bl_def word_of_int_hom_syms)
    apply (rule range_eqI [where x = 0], simp)+
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

lemma lipcb_corres':
  "corres op = (tcb_at t and valid_objs and pspace_aligned) 
               (tcb_at' t and valid_objs' and pspace_aligned'
                and pspace_distinct' and no_0_obj')
               (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  apply (simp add: lookup_ipc_buffer_def lookupIPCBuffer_def
                   ArchVSpace_H.lookupIPCBuffer_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr [OF _ threadget_corres])
       apply (simp add: getThreadBufferSlot_def locateSlot_conv)
       apply (rule corres_split [OF _ getSlotCap_corres])
          apply (rule_tac F="valid_ipc_buffer_cap rv buffer_ptr"
                       in corres_gen_asm)
          apply (rule_tac P="valid_cap rv" and Q="no_0_obj'"
                    in corres_assume_pre)
          apply (simp add: Let_def split: cap.split arch_cap.split
                         split del: split_if cong: if_cong)
          apply (safe, simp_all add: isCap_simps)[1]
          apply (subgoal_tac "word + (buffer_ptr &&
                                      mask (pageBitsForSize vmpage_size)) \<noteq> 0")
           apply (simp add: cap_aligned_def
                            valid_ipc_buffer_cap_def
                            vmrights_map_def vm_read_only_def vm_read_write_def)
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
                                obj_relation_cuts_def3 no_0_obj'_def)
         apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def tcbIPCBufferSlot_def)
        apply (wp get_cap_valid_ipc get_cap_aligned)
      apply (simp add: tcb_relation_def)
     apply (wp thread_get_obj_at_eq)
   apply (clarsimp elim!: tcb_at_cte_at)
  apply clarsimp
  done

lemma lipcb_corres:
  "corres op = (tcb_at t and invs) 
               (tcb_at' t and invs')
               (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  using lipcb_corres'
  by (rule corres_guard_imp, auto simp: invs'_def valid_state'_def)

lemma lookupIPC_inv[wp]: "\<lbrace>I\<rbrace> lookupIPCBuffer w t \<lbrace>\<lambda>rv. I\<rbrace>"
  by (simp add:      lookupIPCBuffer_def nothingOnFailure_def
                     ArchVSpace_H.lookupIPCBuffer_def Let_def
                     getThreadBufferSlot_def
          split del: split_if | wp crunch_wps)+

crunch st_tcb_at'[wp]: rescheduleRequired "st_tcb_at' P t"
  (wp: threadSet_st_tcb_no_state simp: unless_def ignore: threadSet)

lemma setThreadState_st_tcb':
  "\<lbrace>\<top>\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>s. s = st) t\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_st_tcb_at_state | simp add: if_apply_def2)+
  done

lemma st_tcb'_neq_contra:
  "\<lbrakk> st_tcb_at' P p s; st_tcb_at' Q p s; \<And>st. P st \<noteq> Q st \<rbrakk> \<Longrightarrow> False"
  by (clarsimp simp: st_tcb_at'_def obj_at'_def)

lemma setThreadState_st_tcb:
  "\<lbrace>\<lambda>s. P st\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (cases "P st")
   apply simp
   apply (rule hoare_post_imp [OF _ setThreadState_st_tcb'])
   apply (erule st_tcb'_weakenE, simp)
  apply (simp add: hoare_pre_cont)
  done

crunch ct'[wp]: rescheduleRequired "\<lambda>s. P (ksCurThread s)"
  (simp: unless_def)

crunch ct'[wp]: tcbSchedDequeue "\<lambda>s. P (ksCurThread s)"
crunch ct'[wp]: setThreadState "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps)

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

crunch idle'[wp]: setQueue "valid_idle'"
  (simp: valid_idle'_pspace_itI)

crunch idle'[wp]: rescheduleRequired "valid_idle'"
  (simp: unless_def crunch_simps)

crunch idle'[wp]: tcbSchedDequeue "valid_idle'"
  (simp: unless_def crunch_simps)

lemma sts_valid_idle'[wp]:
  "\<lbrace>valid_idle' and valid_pspace' and
    (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' ts)\<rbrace>
   setThreadState ts t
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_idle', simp+)+
  done

lemma gts_sp':
  "\<lbrace>P\<rbrace> getThreadState t \<lbrace>\<lambda>rv. st_tcb_at' (\<lambda>st. st = rv) t and P\<rbrace>"
  apply (simp add: getThreadState_def threadGet_def)
  apply wp
  apply (simp add: o_def st_tcb_at'_def)
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcbSchedDequeue_tcbState_obj_at'[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>rv. obj_at' (P \<circ> tcbState) t'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp | simp add: o_def split del: split_if cong: if_cong)+
  done

crunch typ_at'[wp]: setQueue "\<lambda>s. P' (typ_at' P t s)"

lemma setQueue_st_tcb_at[wp]:
  "\<lbrace>\<lambda>s. P' (st_tcb_at' P t s)\<rbrace> setQueue d p q \<lbrace>\<lambda>rv s. P' (st_tcb_at' P t s)\<rbrace>"
  unfolding st_tcb_at'_def
  apply (rule_tac P=P' in P_bool_lift)
   apply (rule setQueue_obj_at)
  apply (rule_tac Q="\<lambda>_ s. \<not>typ_at' TCBT t s \<or> obj_at' (Not \<circ> (P \<circ> tcbState)) t s"
           in hoare_post_imp, simp add: not_obj_at')
  apply (wp hoare_vcg_disj_lift)
  apply (clarsimp simp: not_obj_at')
  done

lemma tcbSchedDequeue_st_tcb_at'[wp]:
  "\<lbrace>\<lambda>s. P' (st_tcb_at' P t' s)\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_ s. P' (st_tcb_at' P t' s)\<rbrace>"
  apply (rule_tac P=P' in P_bool_lift)
   apply (simp add: tcbSchedDequeue_def)
   apply (wp threadSet_st_tcb_no_state | clarsimp)+
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadSet_st_tcb_no_state | clarsimp)+
  done

lemma sts_st_tcb':
  "\<lbrace>if t = t' then K (P st) else st_tcb_at' P t\<rbrace> 
  setThreadState st t' 
  \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (cases "t = t'",
         simp_all add: setThreadState_def
                  split del: split_if)
   apply ((wp threadSet_st_tcb_at_state | simp)+)[1]
  apply (wp threadSet_obj_at'_really_strongest
              | simp add: st_tcb_at'_def)+
  apply (simp add: o_def | wp)+
  done

crunch typ_at'[wp]: rescheduleRequired "\<lambda>s. P (typ_at' T p s)"
  (simp: unless_def)
crunch typ_at'[wp]: tcbSchedDequeue "\<lambda>s. P (typ_at' T p s)"

crunch typ_at'[wp]: setThreadState "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_when_weak_wp)

lemmas setThreadState_typ_ats[wp] = typ_at_lifts [OF setThreadState_typ_at']

crunch aligned'[wp]: setThreadState pspace_aligned'
  (wp: hoare_when_weak_wp)

crunch distinct'[wp]: setThreadState pspace_distinct'
  (wp: hoare_when_weak_wp)

crunch cte_wp_at'[wp]: setThreadState "cte_wp_at' P p"
  (wp: hoare_when_weak_wp simp: unless_def)

lemma state_refs_of'_queues[simp]:
  "state_refs_of' (ksReadyQueues_update f s) = state_refs_of' s"
  by (fastforce elim!: state_refs_of'_pspaceI intro!: ext)

schematic_lemma test:
  "\<And>queued prio queue f. tcb_st_refs_of' f = ?f'7 False prio queue () (tcb_st_refs_of' f)"
  apply (simp, (rule exI)?, (wp+)?) 
  done

crunch refs_of'[wp]: rescheduleRequired "\<lambda>s. P (state_refs_of' s)"
  (simp: unless_def crunch_simps wp: threadSet_state_refs_of' ignore: threadSet)

lemma setThreadState_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_st_refs_of' st))\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (simp add: setThreadState_def setQueue_def
        | wp threadSet_state_refs_of')+

lemma threadSet_ksCurThread[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> threadSet t f \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  by (clarsimp simp: threadSet_def valid_def in_monad
                     setObject_def split_def getObject_def
              dest!: in_inv_by_hoareD [OF updateObject_default_inv]
                     in_inv_by_hoareD [OF loadObject_default_inv])

lemma sts_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  apply (wp cur_tcb_lift)
  done

lemma iflive'_queues[simp]:
  "if_live_then_nonz_cap' (ksReadyQueues_update f s)
     = if_live_then_nonz_cap' s"
  by (fastforce intro: if_live_then_nonz_cap'_pspaceI)

crunch iflive'[wp]: setQueue if_live_then_nonz_cap'
crunch nonz_cap[wp]: setQueue "ex_nonz_cap_to' t"

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
  apply (clarsimp simp: st_tcb_at'_def obj_at'_real_def)
  apply (erule(1) if_live_then_nonz_capD')
  apply (fastforce simp: projectKOs)
  done

lemma tcbSchedDequeue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' t\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def unless_def)
  apply (wp threadSet_iflive' hoare_drop_imps | simp add: crunch_simps)+
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

crunch ifunsafe'[wp]: setThreadState "if_unsafe_then_cap'"
  (simp: unless_def crunch_simps)

lemma st_tcb_ex_cap'':
  "\<lbrakk> st_tcb_at' P t s; if_live_then_nonz_cap' s;
     \<And>st. P st \<Longrightarrow> st \<noteq> Inactive \<and> \<not> idle' st \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: st_tcb_at'_def obj_at'_real_def projectKOs
              elim!: ko_wp_at'_weakenE
                     if_live_then_nonz_capE')

crunch arch' [wp]: setThreadState "\<lambda>s. P (ksArchState s)"
  (ignore: getObject setObject simp: unless_def crunch_simps)

crunch it' [wp]: setThreadState "\<lambda>s. P (ksIdleThread s)"
  (ignore: getObject setObject wp: getObject_inv_tcb
     simp: updateObject_default_def unless_def crunch_simps)

crunch ctes_of [wp]: setQueue "\<lambda>s. P (ctes_of s)"

lemma sts_ctes_of [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> setThreadState st t \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_ctes_ofT | simp add: tcb_cte_cases_def)+
  done

crunch ksInterruptState[wp]: setThreadState "\<lambda>s. P (ksInterruptState s)"
  (simp: unless_def crunch_simps)

lemmas setThreadState_irq_handlers[wp]
    = valid_irq_handlers_lift'' [OF sts_ctes_of setThreadState_ksInterruptState]

lemma sts_global_reds' [wp]:
  "\<lbrace>valid_global_refs'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift') wp 

crunch irq_states' [wp]: setThreadState valid_irq_states'
  (simp: unless_def crunch_simps)
crunch pde_mappings' [wp]: setThreadState valid_pde_mappings'
  (simp: unless_def crunch_simps)

lemma tcbSchedEnqueue_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> tcbSchedEnqueue x \<lbrace>\<lambda>_ s. P (ksMachineState s)\<rbrace>"
  by (simp add: tcbSchedEnqueue_def unless_def setQueue_def | wp)+

crunch ksMachine[wp]: setThreadState "\<lambda>s. P (ksMachineState s)"
 (simp: crunch_simps)

crunch pspace_domain_valid[wp]: setThreadState "pspace_domain_valid"
  (simp: unless_def crunch_simps)

lemma setThreadState_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setThreadState F t \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift, wp)
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
      apply (rule hoare_convert_imp [OF threadSet_no_sa])
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
      apply (simp add: tcbSchedEnqueue_def unless_def)
      apply (wp ts sq
                hoare_convert_imp [OF setQueue_no_sa setQueue_ct'])
      apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
      apply (wp)
      done
  qed

lemma ct_not_inQ_update_cnt:
  "ct_not_inQ s \<Longrightarrow> ct_not_inQ (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>)"
   by (simp add: ct_not_inQ_def)

lemma ct_not_inQ_update_stt:
  "ct_not_inQ s \<Longrightarrow> ct_not_inQ (s\<lparr>ksSchedulerAction := SwitchToThread t\<rparr>)"
   by (simp add: ct_not_inQ_def)

lemma invs'_update_cnt:
  "invs' s \<Longrightarrow> invs' (s\<lparr>ksSchedulerAction := ChooseNewThread\<rparr>)"
   by (clarsimp simp: invs'_def valid_state'_def ct_not_inQ_update_cnt
                      valid_queues_def valid_queues'_def valid_irq_node'_def
                      cur_tcb'_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma invs'_update_stt:
  "\<lbrakk> invs' s; st_tcb_at' runnable' t s; tcb_in_cur_domain' t s; obj_at' (\<lambda>tcb. tcbDomain tcb \<le> maxDomain) t s;obj_at' (\<lambda>tcb. tcbPriority tcb \<le> maxPriority) t s \<rbrakk> \<Longrightarrow> invs' (s\<lparr>ksSchedulerAction := SwitchToThread t\<rparr>)"
   by (clarsimp simp: invs'_def valid_state'_def ct_not_inQ_update_stt
                      valid_queues_def valid_queues'_def valid_irq_node'_def
                      cur_tcb'_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma setSchedulerAction_direct:
  "\<lbrace>\<top>\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>_ s. ksSchedulerAction s = sa\<rbrace>"
  by (clarsimp simp: setSchedulerAction_def)

lemma rescheduleRequired_ct_not_inQ:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: rescheduleRequired_def ct_not_inQ_def)
  apply (rule_tac Q="\<lambda>_ s. ksSchedulerAction s = ChooseNewThread"
           in hoare_post_imp, clarsimp)
  apply (wp setSchedulerAction_direct)
  done

lemma possibleSwitchTo_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
    possibleSwitchTo t same \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: possibleSwitchTo_def curDomain_def)
  apply (wp static_imp_wp rescheduleRequired_ct_not_inQ tcbSchedEnqueue_ct_not_inQ threadGet_wp
       | wpc
       | clarsimp simp: ct_not_inQ_update_stt)+
  apply (fastforce simp: obj_at'_def)
  done

lemma attemptSwitchTo_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
   attemptSwitchTo t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  by (simp add: attemptSwitchTo_def, wp possibleSwitchTo_ct_not_inQ)

lemma switchIfRequiredTo_ct_not_inQ:
  "\<lbrace>ct_not_inQ and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
    switchIfRequiredTo t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  by (simp add: switchIfRequiredTo_def, wp possibleSwitchTo_ct_not_inQ)

lemma threadSet_tcbState_update_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> threadSet (tcbState_update f) t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (simp add: ct_not_inQ_def)
  apply (rule hoare_convert_imp [OF threadSet_no_sa])
  apply (simp add: threadSet_def)
  apply (wp)
   apply (wps setObject_ct_inv)
   apply (rule setObject_tcb_strongest)
  apply (clarsimp)
  apply (rule hoare_conjI)
   apply (rule hoare_weaken_pre)
   apply (wps, wp static_imp_wp)
   apply (wp OMG_getObject_tcb)
   apply (clarsimp simp: comp_def)
  apply (wp hoare_drop_imp)
  done

lemma setThreadState_ct_not_inQ:
  "\<lbrace>ct_not_inQ\<rbrace> setThreadState st t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_ct_not_inQ)
  apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
  apply (wp)
  done

crunch ct_not_inQ[wp]: setQueue "ct_not_inQ"

lemma tcbSchedDequeue_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  proof -
    have TSNIQ: "\<And>F t.
      \<lbrace>ct_not_inQ and (\<lambda>_. \<forall>tcb. \<not>tcbQueued (F tcb))\<rbrace>
      threadSet F t \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
      apply (simp add: ct_not_inQ_def)
      apply (wp hoare_convert_imp [OF threadSet_no_sa])
       apply (simp add: threadSet_def)
       apply (wp)
       apply (wps setObject_ct_inv)
       apply (wp setObject_tcb_strongest getObject_tcb_wp)
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

lemma tcbSchedEnqueue_ksCurDomain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s)\<rbrace> tcbSchedEnqueue tptr \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
apply (simp add: tcbSchedEnqueue_def unless_def)
apply (wp  | simp)+
done

lemma tcbSchedEnqueue_ksDomSchedule[wp]:
  "\<lbrace> \<lambda>s. P (ksDomSchedule s)\<rbrace> tcbSchedEnqueue tptr \<lbrace>\<lambda>_ s. P (ksDomSchedule s)\<rbrace>"
apply (simp add: tcbSchedEnqueue_def unless_def)
apply (wp | simp)+
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
apply (wp | wpc | simp )+
done

lemma rescheduleRequired_ksDomSchedule[wp]:
  "\<lbrace> \<lambda>s. P (ksDomSchedule s) \<rbrace> rescheduleRequired \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
apply (simp add: rescheduleRequired_def)
apply (wp | wpc | simp )+
done

lemma setThreadState_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setThreadState st tptr \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
apply (simp add: setThreadState_def)
apply (wp threadSet_ct_idle_or_in_cur_domain' hoare_drop_imps | simp)+
done

lemma setThreadState_ksCurDomain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s) \<rbrace> setThreadState st tptr \<lbrace>\<lambda>_ s. P (ksCurDomain s) \<rbrace>"
apply (simp add: setThreadState_def)
apply (wp  | simp)+
done

lemma setThreadState_ksDomSchedule[wp]:
  "\<lbrace> \<lambda>s. P (ksDomSchedule s) \<rbrace> setThreadState st tptr \<lbrace>\<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
apply (simp add: setThreadState_def)
apply (wp  | simp)+
done

crunch ksDomScheduleIdx[wp]: rescheduleRequired "\<lambda>s. P (ksDomScheduleIdx s)"
(ignore: setObject getObject getObject wp:crunch_wps hoare_unless_wp)

lemma setThreadState_ksDomScheduleIdx[wp]:
  "\<lbrace> \<lambda>s. P (ksDomScheduleIdx s) \<rbrace> setThreadState st tptr \<lbrace>\<lambda>_ s. P (ksDomScheduleIdx s) \<rbrace>"
apply (simp add: setThreadState_def)
apply (wp  | simp)+
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
  apply (simp add: invs'_def valid_state'_def)
  apply (wp irqs_masked_lift valid_irq_node_lift sts_valid_queues
            setThreadState_ct_not_inQ, simp_all)
     apply (clarsimp simp: sch_act_simple_def)
    apply (clarsimp elim!: st_tcb_ex_cap'')
   apply (clarsimp dest!: st_tcb_at_state_refs_ofD'
                   elim!: rsubst[where P=sym_refs]
                  intro!: ext)
  apply (rule conjI, clarsimp)
  apply (clarsimp simp: st_tcb_at'_def)
  apply (drule obj_at_valid_objs')
   apply (clarsimp simp: valid_pspace'_def)
  apply (clarsimp simp: valid_obj'_def valid_tcb'_def projectKOs)
  apply (fastforce simp: valid_tcb_state'_def
                  split: Structures_H.thread_state.splits)
  done

lemma sts_invs_minor'_notrunnable':
  assumes "\<not>runnable' st"
  shows "\<lbrace>st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st
                            \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                               st' \<noteq> Inactive \<and> \<not> idle' st')) t
            and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' st)
            and (\<lambda>s. \<forall>p. t \<notin> set(ksReadyQueues s p))
            and sch_act_simple
            and invs'\<rbrace>
            setThreadState st t
         \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (rule hoare_weaken_pre [OF sts_invs_minor'], fastforce simp: assms)

lemma sts_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma sts_st_tcb_neq':
  "\<lbrace>st_tcb_at' P t and K (t \<noteq> t')\<rbrace> 
  setThreadState st t' 
  \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  by (wp sts_st_tcb') simp

lemma sts_ct_in_state_neq':
  "\<lbrace>(\<lambda>s. ksCurThread s \<noteq> t') and ct_in_state' P\<rbrace> 
  setThreadState st t' 
  \<lbrace>\<lambda>_. ct_in_state' P\<rbrace>"
  apply (clarsimp simp add: valid_def ct_in_state'_def) 
  apply (frule_tac P1="\<lambda>k. k \<noteq> t'" in use_valid [OF _ setThreadState_ct'])
   apply assumption
  apply (rule use_valid [OF _ sts_st_tcb_neq'], assumption)
  apply simp
  apply (erule (1) use_valid [OF _ setThreadState_ct'])
  done

lemmas isTS_defs =
  isRunning_def isBlockedOnSend_def isBlockedOnReceive_def
  isBlockedOnAsyncEvent_def isBlockedOnReply_def
  isRestart_def isInactive_def
  isIdleThreadState_def

lemma st_tcb_at_tcb_at'[elim!]:
  "st_tcb_at' P t s \<Longrightarrow> tcb_at' t s"
  by (clarsimp simp: st_tcb_at'_def elim!: obj_at'_weakenE)

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
   apply (wp threadSet_st_tcb_no_state)
   apply simp
  apply wp
  done

lemma asUser_global_refs':   "\<lbrace>valid_global_refs'\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_global_refs)
       apply simp+
  apply (wp select_f_inv)
  done

lemma sch_act_sane_lift:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  shows "\<lbrace>sch_act_sane\<rbrace> f \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: sch_act_sane_def)
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply (wp assms)
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
    apply (wp dmo_invs' no_irq_storeWord)
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
            split: split_if_asm)
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
    apply (wp dmo_invs_no_cicd' no_irq_storeWord)
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
            split: split_if_asm)
  done
qed

lemma storeWordUser_invs[wp]:
  "\<lbrace>invs'\<rbrace> storeWordUser p w \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (simp add: storeWordUser_def | wp)+

lemma storeWordUser_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> storeWordUser p w \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (simp add: storeWordUser_def | wp)+

lemma hoare_valid_ipc_buffer_ptr_typ_at':
  "(\<And>q. \<lbrace>typ_at' UserDataT q\<rbrace> a \<lbrace>\<lambda>_. typ_at' UserDataT q\<rbrace>)
   \<Longrightarrow> \<lbrace>valid_ipc_buffer_ptr' p\<rbrace> a \<lbrace>\<lambda>_. valid_ipc_buffer_ptr' p\<rbrace>"
  unfolding valid_ipc_buffer_ptr'_def2
  apply wp
  apply assumption
  done

lemma gts_wp':
  "\<lbrace>\<lambda>s. \<forall>st. st_tcb_at' (op = st) t s \<longrightarrow> P st s\<rbrace> getThreadState t \<lbrace>P\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule gts_sp')
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
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
    apply (rule corres_split [OF _ get_cap_corres_P [where P=P]])
      defer
      apply (wp getCTE_wp')
    apply simp
   apply fastforce
  apply (insert cap_relation_masks, simp)
  done

lemma asUser_irq_handlers':
  "\<lbrace>valid_irq_handlers'\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_irq_handlers' [OF all_tcbI, OF ball_tcb_cte_casesI])
        apply simp+
   apply (wp select_f_inv)
  done

(* the brave can try to move this up to near tcb_update_corres' *)

definition non_exst_same :: "Structures_H.tcb \<Rightarrow> Structures_H.tcb \<Rightarrow> bool"
where
  "non_exst_same tcb tcb' \<equiv> \<exists>d p ts. tcb' = tcb\<lparr>tcbDomain := d, tcbPriority := p, tcbTimeSlice := ts\<rparr>"

fun non_exst_same' :: "Structures_H.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "non_exst_same' (KOTCB tcb) (KOTCB tcb') = non_exst_same tcb tcb'" |
  "non_exst_same' _ _ = True"

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
                        updateObject_default_def in_magnitude_check objBits_def objBitsKO_def)
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
   apply (case_tac bb, simp_all)[1]
     apply (clarsimp simp: obj_at'_def other_obj_relation_def cte_relation_def tcb_relation_def projectKOs split: split_if_asm)+
   apply (clarsimp simp: aobj_relation_cuts_def split: ARM_Structs_A.arch_kernel_obj.splits)
   apply (case_tac arch_kernel_obj, simp_all)
     apply (clarsimp simp: pte_relation_def pde_relation_def is_tcb_def)+
  apply (simp only: ekheap_relation_def dom_fun_upd2 simp_thms)
  apply (frule bspec, erule domI)
  apply (rule ballI, drule(1) bspec)
  apply (drule domD)
  apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: projectKOs)
  apply (insert e)
  apply (clarsimp simp: a_type_def other_obj_relation_def etcb_relation_def is_other_obj_relation_type split: Structures_A.kernel_object.splits Structures_H.kernel_object.splits ARM_Structs_A.arch_kernel_obj.splits)
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
     apply (rule set_eobject_corres'[where P="op = tcb'"])
      apply simp
     defer
    apply (simp add: r)
   apply (fastforce simp: is_etcb_at_def elim!: obj_at_weakenE)
   apply (subst(asm) eq_commute)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: projectKOs obj_at'_def objBits_simps)
  apply (subst map_to_ctes_upd_tcb, assumption+)
   apply (simp add: ps_clear_def3 field_simps)
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
    apply (rule corres_split [OF set_eobject_corres corres_get_etcb])
         apply (rule x)
        apply (erule e)
       apply (simp add: z)+
     apply wp
   apply clarsimp
   apply (simp add: valid_etcbs_def tcb_at_st_tcb_at[symmetric])
   apply (force simp: tcb_at_def get_etcb_def obj_at_def)
  apply simp
  done

lemmas ethread_set_corres =
    ethread_set_corresT [OF _ all_tcbI, OF _ ball_tcb_cte_casesI]

lemma non_exst_same_prio_upd[simp]:
  "non_exst_same tcb (tcbPriority_update f tcb)"
  by (cases tcb, simp add: non_exst_same_def)

lemma non_exst_same_timeSlice_upd[simp]:
  "non_exst_same tcb (tcbTimeSlice_update f tcb)"
  by (cases tcb, simp add: non_exst_same_def)

end
