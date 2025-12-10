(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* VSpace refinement - generic interface *)

(* FIXME arch-split: arguably most of this can be moved elsewhere and this file deleted, making
   VSpace_R an arch-only theory *)

theory VSpace_R
imports ArchTcbAcc_R
begin

(* TODO: maybe move? *)
lemma mapM_mapM_x: "do y \<leftarrow> mapM f l;
                g
             od =
             do mapM_x f l;
                g
             od"
  by (simp add: mapM_x_mapM)

lemma cteCaps_of_ctes_of_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>) \<Longrightarrow> f \<lbrace>\<lambda>s. P (cteCaps_of s)\<rbrace>"
  unfolding cteCaps_of_def .

(* FIXME AARCH64: Added to crunch_param_rules in Crunch_Instances_NonDet as
   trans[OF liftE_bindE return_bind]; move to monad equations instead and give it the name below *)
lemma liftE_return_bindE:
  "liftE (return x) >>=E f = f x"
  by (rule Crunch.crunch_param_rules(8))

crunch getIRQState
  for inv[wp]: P

lemma dmo_invs_no_cicd_lift': (* FIXME AARCH64: move up *)
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  assumes "\<And>P p. f \<lbrace>\<lambda>s. P (underlying_memory s p)\<rbrace>"
  shows "doMachineOp f \<lbrace>all_invs_but_ct_idle_or_in_cur_domain'\<rbrace>"
  apply (wp dmo_invs_no_cicd' assms)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid,
         rule assms, rule refl)
  apply simp
  done

lemma dmo_invs_lift': (* FIXME AARCH64: move up *)
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  assumes "\<And>P p. f \<lbrace>\<lambda>s. P (underlying_memory s p)\<rbrace>"
  shows "doMachineOp f \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs' assms)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid,
         rule assms, rule refl)
  apply simp
  done

lemma valid_irq_node_lift_asm:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
  assumes y: "\<And>p. \<lbrace>real_cte_at' p and Q\<rbrace> f \<lbrace>\<lambda>rv. real_cte_at' p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s \<and> Q s\<rbrace> f \<lbrace>\<lambda>rv s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (simp add: valid_irq_node'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF x])
   apply (wp hoare_vcg_all_lift y)
  apply simp
  done

lemma getIRQState_wp:
  "\<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s) irq) s \<rbrace> getIRQState irq \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getIRQState_def getInterruptState_def
  by (wpsimp simp: comp_def)

lemma maskInterrupt_irq_states':
  "\<lbrace>valid_irq_states'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  by (wpsimp wp: dmo_maskInterrupt)
     (auto simp add: valid_irq_states_def valid_irq_masks'_def)

crunch storeWordUser
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch asUser
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps)
crunch asUser
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps simp: crunch_simps)

lemma maskInterrupt_invs':
  "\<lbrace>invs'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
   by (wpsimp wp: maskInterrupt_irq_states' dmo_maskInterrupt simp: invs'_def valid_state'_def)
      (auto simp: valid_irq_states_def valid_irq_masks'_def valid_machine_state'_def
                  ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma dmo'_gets_wp:
  "\<lbrace>\<lambda>s. Q (f (ksMachineState s)) s\<rbrace> doMachineOp (gets f) \<lbrace>Q\<rbrace>"
  unfolding doMachineOp_def by (wpsimp simp: in_monad)

lemma maskInterrupt_invs_no_cicd':
  "\<lbrace>invs_no_cicd'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: maskInterrupt_irq_states' dmo_maskInterrupt simp: invs_no_cicd'_def)
     (auto simp: valid_irq_states_def valid_irq_masks'_def valid_machine_state'_def
                 ct_not_inQ_def)

lemma dmo_maskInterrupt_True_invs_no_cicd'[wp]:
  "doMachineOp (maskInterrupt True irq) \<lbrace>invs_no_cicd'\<rbrace>"
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs_no_cicd'_def valid_state'_def)
  apply (simp add: valid_irq_masks'_def valid_machine_state'_def
                   ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

(* FIXME AARCH64: replacing getSlotCap_wp is probably going to be too much breakage, but
                   rename would be good *)
lemma getSlotCap_actual_wp:
  "\<lbrace>\<lambda>s.  \<forall>cap. cteCaps_of s p = Some cap \<longrightarrow> Q cap s\<rbrace>
   getSlotCap p \<lbrace>Q\<rbrace>"
  unfolding getSlotCap_def
  by (wpsimp wp: getCTE_cteCap_wp split: option.splits)

lemma dMo_no_0_obj'[wp]:
  "doMachineOp f \<lbrace>no_0_obj'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (simp add: no_0_obj'_def)

lemma dMo_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. P (valid_arch_state' s)\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (valid_arch_state' s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

(* FIXME AARCH64: move (all arches) *)
lemma corres_split_strengthen_ftE:
  "\<lbrakk> corres (ftr \<oplus> r') P P' f j;
     \<And>rv rv'. r' rv rv' \<Longrightarrow> corres (ftr' \<oplus> r) (R rv) (R' rv') (g rv) (k rv');
     \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-; \<lbrace>Q'\<rbrace> j \<lbrace>R'\<rbrace>,- \<rbrakk>
   \<Longrightarrow> corres (dc \<oplus> r) (P and Q) (P' and Q') (f >>=E (\<lambda>rv. g rv)) (j >>=E (\<lambda>rv'. k rv'))"
  apply (rule_tac r'=r' in corres_splitEE)
     apply (erule corres_rel_imp)
     apply (case_tac x, auto)[1]
    apply (rule corres_rel_imp, assumption)
    apply (case_tac x, auto)[1]
   apply (simp add: validE_R_def)+
  done

lemma message_info_to_data_eqv:
  "wordFromMessageInfo (message_info_map mi) = message_info_to_data mi"
  by (cases mi)
     (simp add: wordFromMessageInfo_def msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def
                shiftL_nat)

lemma message_info_from_data_eqv:
  "message_info_map (data_to_message_info v) = messageInfoFromWord v"
  unfolding data_to_message_info_def messageInfoFromWord_def Let_def
  by (clarsimp simp: msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def shiftL_nat
                     msgLabelBits_msg_label_bits msgMaxLength_def mask_def)

lemma set_mi_invs'[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> setMessageInfo t a \<lbrace>\<lambda>x. invs'\<rbrace>"
  by (simp add: setMessageInfo_def) wp

lemma setMessageInfo_corres:
  "mi' = message_info_map mi \<Longrightarrow>
   corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
             (set_message_info t mi) (setMessageInfo t mi')"
  apply (simp add: setMessageInfo_def set_message_info_def)
  apply (subgoal_tac "wordFromMessageInfo (message_info_map mi) =
                      message_info_to_data mi")
   apply (simp add: asUser_setRegister_corres msgInfoRegister_msg_info_register)
  apply (simp add: message_info_to_data_eqv)
  done

lemma set_mi_tcb' [wp]:
  "\<lbrace> tcb_at' t \<rbrace> setMessageInfo receiver msg \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  by (simp add: setMessageInfo_def) wp

lemma setMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def, wp crunch_wps)

lemmas setMRs_typ_at_lifts[wp] = gen_typ_at_lifts[OF setMRs_typ_at']

crunch doMachineOp
  for arch[wp]: "\<lambda>s. P (ksArchState s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and cur'[wp]: "\<lambda>s. P (ksCurThread s)"
  and cteCaps_of[wp]: "\<lambda>s. P (cteCaps_of s)"
  and dmo_global_refs'[wp]: "\<lambda>s. P (global_refs' s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ctes[wp]: "\<lambda>s. P (ctes_of s)"
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"

crunch haskell_fail
  for inv[wp]: "P"

end
