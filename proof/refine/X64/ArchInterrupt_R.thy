(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific refinement for interrupt controller operations *)

theory ArchInterrupt_R
imports Interrupt_R
begin

context Arch begin arch_global_naming

named_theorems Interrupt_R_assms

lemma maxIRQ_H_ucast_toEnum_eq_irq[Interrupt_R_assms]:
  "x \<le> ucast maxIRQ \<Longrightarrow> toEnum (unat x) = (ucast x :: irq)" for x::machine_word
  by (simp add: word_le_nat_alt maxIRQ_def)

lemma arch_valid_irq_le_maxIRQ[Interrupt_R_assms]:
  "arch_valid_irq irq \<Longrightarrow> irq \<le> maxIRQ"
  by simp

lemma arch_valid_irq_valid_IRQHandlerCap[Interrupt_R_assms]:
  "arch_valid_irq irq \<Longrightarrow> valid_cap' (capability.IRQHandlerCap irq) s"
  by (simp add: valid_cap'_def capAligned_def)

primrec arch_irq_control_inv_relation ::
  "arch_irq_control_invocation \<Rightarrow> Arch.irqcontrol_invocation \<Rightarrow> bool"
  where
  "arch_irq_control_inv_relation (X64_A.IssueIRQHandlerIOAPIC i ptr1 ptr2 a b c d e) x =
     (x = X64_H.IssueIRQHandlerIOAPIC i (cte_map ptr1) (cte_map ptr2) a b c d e)"
| "arch_irq_control_inv_relation (X64_A.IssueIRQHandlerMSI i p p' a b c d) x =
     ( x = X64_H.IssueIRQHandlerMSI i (cte_map p) (cte_map p') a b c d)"

primrec arch_irq_control_inv_valid' :: "Arch.irqcontrol_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "arch_irq_control_inv_valid' (X64_H.IssueIRQHandlerIOAPIC irq p p' a b c d e) =
                (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) p and
                 cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) p' and
                 ex_cte_cap_to' p and real_cte_at' p and
                (Not o irq_issued' irq) and K (irq \<le> maxIRQ))"
| "arch_irq_control_inv_valid' (X64_H.IssueIRQHandlerMSI irq p p' a b c d) =
                (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) p and
                 cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) p' and
                 ex_cte_cap_to' p and real_cte_at' p and
                (Not o irq_issued' irq) and K (irq \<le> maxIRQ))"

lemma checkIRQ_corres[Interrupt_R_assms]:
  "corres (ser \<oplus> dc) \<top> \<top> (arch_check_irq irq) (Arch.checkIRQ irq)"
  unfolding arch_check_irq_def checkIRQ_def
  by (clarsimp simp: minIRQ_def maxIRQ_def whenE_rangeCheck_eq whenE_def returnOk_def split: if_split)

lemmas irq_const_defs =
  maxIRQ_def minIRQ_def
  X64.maxUserIRQ_def X64.minUserIRQ_def X64_H.maxUserIRQ_def X64_H.minUserIRQ_def

crunch arch_check_irq, checkIRQ
  for inv[Interrupt_R_assms]: "P"
  (simp: crunch_simps)

lemma arch_check_irq_valid:
  "\<lbrace>\<top>\<rbrace> arch_check_irq irq \<lbrace>\<lambda>_. (\<lambda>s. irq \<le> ucast maxIRQ)\<rbrace>, -"
  unfolding arch_check_irq_def
  by (wpsimp simp: validE_R_def not_less word_le_nat_alt maxIRQ_def wp: whenE_throwError_wp)

lemma arch_check_irq_valid'[Interrupt_R_assms]:
  "\<lbrace>\<top>\<rbrace> arch_check_irq irq \<lbrace>\<lambda>_ _. irq \<le> ucast maxIRQ\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (wp arch_check_irq_valid)

lemma checkIRQ_irq_valid[Interrupt_R_assms]:
  "\<lbrace>\<top>\<rbrace> checkIRQ irq \<lbrace>\<lambda>_ _. arch_valid_irq (toEnum (unat irq))\<rbrace>, -"
  unfolding checkIRQ_def rangeCheck_def validE_R_def
  supply hoare_vcg_prop[wp del]
  apply (clarsimp simp: unlessE_def split del: if_split)
  apply (wpsimp simp: maxIRQ_H_ucast_toEnum_eq_irq)
  done

lemma toEnum_unat_ucast_helper_64_8:
  "unat yf \<le> 107 \<Longrightarrow> toEnum (unat (UCAST(64 \<rightarrow> 8) yf) + 16) = UCAST(64 \<rightarrow> 8) yf + 16"
  apply (subgoal_tac "unat (UCAST (64 \<rightarrow> 8) yf) = unat yf")
  apply (subst unat_ucast)
  apply (simp add: ucast_nat_def)
  apply (subst unat_ucast)
  apply simp
  done

lemma toEnum_unat_ucast'_helper_64_8:
  "unat yf \<le> 107 \<Longrightarrow> toEnum (16 + unat (UCAST(64 \<rightarrow> 8) yf)) = 16 + UCAST(64 \<rightarrow> 8) yf"
  apply (subst add.commute)
  apply (subst add.commute[where a="0x10"])
  using toEnum_unat_ucast_helper_64_8
  apply simp
  done

lemma corres_gets_ioapic_nirqs[corres]:
  "corres (=) \<top> \<top> (gets (x64_ioapic_nirqs \<circ> arch_state)) (gets (x64KSIOAPICnIRQs \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma arch_decodeIRQControlInvocation_corres[Interrupt_R_assms]:
  "list_all2 cap_relation caps caps' \<Longrightarrow>
   corres (ser \<oplus> arch_irq_control_inv_relation)
     (invs and (\<lambda>s. \<forall>cp \<in> set caps. s \<turnstile> cp))
     (invs' and (\<lambda>s. \<forall>cp \<in> set caps'. s \<turnstile>' cp))
     (arch_decode_irq_control_invocation label args slot caps)
     (Arch.decodeIRQControlInvocation label args (cte_map slot) caps')"
  apply (clarsimp simp: arch_decode_irq_control_invocation_def X64_H.decodeIRQControlInvocation_def Let_def)
  apply (rule conjI, clarsimp)
   prefer 2
   apply clarsimp
   apply (cases caps, simp)
    apply (auto split: arch_invocation_label.splits list.splits invocation_label.splits
                 simp: length_Suc_conv list_all2_Cons1 whenE_rangeCheck_eq liftE_bindE split_def)[2]
  apply (cases caps, simp split: list.split)
  apply (case_tac "\<exists>n. length args = Suc (Suc (Suc (Suc (Suc (Suc (Suc n))))))",
              clarsimp simp: length_Suc_conv list_all2_Cons1 whenE_rangeCheck_eq
                             liftE_bindE split_def)
   prefer 2 apply (auto split: list.split)[1]
  apply (rule conjI, clarsimp)
   \<comment> \<open>MSI\<close>
   apply (rule corres_guard_imp)
     apply (rule whenE_throwError_corres)
       apply (simp add: irq_const_defs)
      apply (simp add: irq_const_defs)
     apply (simp add: linorder_not_less )
     apply (simp add: irq_const_defs word_le_nat_alt)
     apply (simp add: ucast_nat_def Groups.ab_semigroup_add_class.add.commute toEnum_unat_ucast_helper_64_8)
     apply (rule corres_split_eqr[OF is_irq_active_corres])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE)
          apply (rule lookupSlotForCNodeOp_corres; simp)
         apply (rule corres_splitEE[OF ensureEmptySlot_corres])
            apply simp
           apply (rule whenE_throwError_corres, ((simp add: maxPCIBus_def maxPCIDev_def maxPCIFunc_def)+)[2])+
           apply (rule corres_returnOkTT)
           apply (clarsimp simp: arch_irq_control_inv_relation_def )
           apply (wpsimp wp: isIRQActive_inv
                       simp: invs_valid_objs invs_psp_aligned invs_valid_objs'
                             invs_pspace_aligned' invs_pspace_distinct'
                  | wp (once) hoare_drop_imps)+
    \<comment> \<open>IOAPIC\<close>
  apply (rule conjI, clarsimp)
   apply (rule corres_guard_imp)
     apply (rule whenE_throwError_corres)
       apply (simp add: irq_const_defs)
      apply (simp add: irq_const_defs)
     apply (simp add: linorder_not_less )
     apply (simp add: irq_const_defs word_le_nat_alt)
     apply (simp add: ucast_nat_def add.commute toEnum_unat_ucast_helper_64_8)
     apply (rule corres_split_eqr[OF is_irq_active_corres])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE)
          apply (rule lookupSlotForCNodeOp_corres; simp)
         apply (rule corres_splitEE[OF ensureEmptySlot_corres])
            apply simp
           apply (rule corres_split[OF corres_gets_num_ioapics])
             apply (rule corres_split[OF corres_gets_ioapic_nirqs])
               apply (rule whenE_throwError_corres, ((simp add: ioapicIRQLines_def)+)[2])+
               apply (rule corres_returnOkTT)
               apply (clarsimp simp: arch_irq_control_inv_relation_def )
              apply (wpsimp wp: isIRQActive_inv
                          simp: invs_valid_objs invs_psp_aligned invs_valid_objs'
                                invs_pspace_aligned' invs_pspace_distinct'
                     | wp (once) hoare_drop_imps)+
  by (auto split: arch_invocation_label.splits invocation_label.splits)

(* FIXME: decrypt magic numbers *)
lemma unat_add_ucast_helper:
  "unat xm \<le> 107 \<Longrightarrow> unat (0x10 + UCAST(64 \<rightarrow> 8) xm) \<le> 125"
  apply (subgoal_tac "unat (UCAST(64 \<rightarrow> 8) xm) = unat xm")
   apply (rule le_trans, rule unat_plus_gt, simp)
  apply (simp add: unat_ucast)
  done

lemma arch_decode_irq_control_valid'[Interrupt_R_assms, wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' cap)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
        \<and> cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot s\<rbrace>
   Arch.decodeIRQControlInvocation label args slot caps
   \<lbrace>arch_irq_control_inv_valid'\<rbrace>,-"
   apply (clarsimp simp add: X64_H.decodeIRQControlInvocation_def Let_def split_def checkIRQ_def
                   rangeCheck_def unlessE_whenE
                split del: if_split cong: if_cong list.case_cong prod.case_cong
                                          arch_invocation_label.case_cong)
  apply (rule hoare_pre)
   apply (simp add: rangeCheck_def unlessE_whenE cong: list.case_cong prod.case_cong
          | wp whenE_throwError_wp isIRQActive_wp ensureEmptySlot_stronger
          | wpc
          | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: invs_valid_objs' irq_const_defs unat_word_ariths word_le_nat_alt)
  apply (fastforce simp add: toEnum_unat_ucast'_helper_64_8 unat_add_ucast_helper)+
  done

crunch Arch.decodeIRQControlInvocation
  for inv[Interrupt_R_assms, wp]: "P"
  (simp: crunch_simps wp: crunch_wps)

lemmas [Interrupt_R_assms] = arch_check_irq_inv

lemma irq_node_in_global_refs'[Interrupt_R_assms]:
  "Invariants_H.irq_node' s + (ucast irq << cteSizeBits) \<in> global_refs' s" for irq :: irq
  by (simp add: global_refs'_def cteSizeBits_cte_level_bits cte_level_bits_def shiftl_t2n)

lemma arch_invokeIRQHandler_corres[Interrupt_R_assms]:
  "irq_handler_inv_relation i i' \<Longrightarrow>
   corres dc \<top> \<top> (arch_invoke_irq_handler i) (Arch.invokeIRQHandler i')"
  by (cases i; clarsimp simp: X64_H.invokeIRQHandler_def)
     (rule corres_machine_op, rule corres_Id; simp?)

lemma is_derived'_NotificationCap[Interrupt_R_assms]:
  "\<lbrakk>isNotificationCap cap; isNotificationCap cap'\<rbrakk>
   \<Longrightarrow> is_derived' ctes src cap' cap = badge_derived' cap' cap"
  by (clarsimp simp add: is_derived'_def isCap_simps vsCapRef_def)

lemma IRQHandler_valid':
  "(s' \<turnstile>' IRQHandlerCap irq) = (irq \<le> maxIRQ)"
  by (simp add: valid_cap'_def capAligned_def word_bits_conv)

lemma updateIRQState_corres[wp]:
  "state = x64irqstate_to_abstract state' \<Longrightarrow>
     corres dc \<top> \<top>
       (update_irq_state irq state)
       (updateIRQState irq state')"
  apply (clarsimp simp: update_irq_state_def updateIRQState_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_x64_irq_state])
      apply (rule corres_modify[where P=\<top> and P'=\<top>])
      apply (auto simp: state_relation_def arch_state_relation_def x64_irq_relation_def)
  done

crunch updateIRQState
  for pspace_distinct'[wp]: "pspace_distinct'"
  and pspace_aligned'[wp]: "pspace_aligned'"
  and cte_wp_at'[wp]: "cte_wp_at' a b"
  and valid_mdb'[wp]: "valid_mdb'"
  and real_cte_at'[wp]: "real_cte_at' x"
  and valid_cap'[wp]: "valid_cap' a"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s a)"
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"
  and ex_cte_cap_wp_to'[wp]: "ex_cte_cap_wp_to' a b"
  (simp: ex_cte_cap_wp_to'_def valid_mdb'_def)

lemma maxUserIRQ_le_maxIRQ:
  "X64.maxUserIRQ \<le> maxIRQ"
  by (simp add: X64.maxUserIRQ_def maxIRQ_def)

lemma arch_performIRQControl_corres[Interrupt_R_assms]:
  "arch_irq_control_inv_relation ivk ivk' \<Longrightarrow> corres (dc \<oplus> dc)
          (einvs and arch_irq_control_inv_valid ivk)
          (invs' and arch_irq_control_inv_valid' ivk')
          (arch_invoke_irq_control ivk)
          (Arch.performIRQControl ivk')"
  apply (cases ivk; simp add: X64_H.performIRQControl_def arch_invoke_irq_control_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor)
        apply do_machine_op_corres
       apply (rule corres_split_nor)
          apply (wpsimp simp: IRQ_def)
         apply (rule corres_split_nor)
            apply (rule setIRQState_corres)
            apply (simp add: irq_state_relation_def)
           apply (rule cteInsert_simple_corres)
             apply (wpsimp simp: IRQHandler_valid IRQHandler_valid'
                    | strengthen invs_arch_state
                    | wps)+
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cte_wp_at_caps_of_state
                          is_simple_cap_def is_cap_simps arch_irq_control_inv_valid_def
                          maxIRQ_def[symmetric]
                          safe_parent_for_def order_trans[OF _ maxUserIRQ_le_maxIRQ])
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def IRQHandler_valid
                      IRQHandler_valid' is_simple_cap'_def isCap_simps IRQ_def)
   apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
   apply (case_tac ctea)
   apply (clarsimp simp: isCap_simps sameRegionAs_def3)
   apply (auto dest: valid_irq_handlers_ctes_ofD)[1]
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (wpsimp simp: IRQ_def)
      apply (rule corres_split_nor)
         apply (rule setIRQState_corres)
         apply (simp add: irq_state_relation_def)
        apply (rule cteInsert_simple_corres)
           apply (wpsimp simp: IRQHandler_valid IRQHandler_valid'
                  | strengthen invs_arch_state
                 | wps)+
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cte_wp_at_caps_of_state
                            is_simple_cap_def is_cap_simps arch_irq_control_inv_valid_def
                            maxIRQ_def[symmetric]
                            safe_parent_for_def order_trans[OF _ maxUserIRQ_le_maxIRQ])
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def IRQHandler_valid
                      IRQHandler_valid' is_simple_cap'_def isCap_simps IRQ_def)
  apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
  apply (case_tac ctea)
  apply (clarsimp simp: isCap_simps sameRegionAs_def3)
  apply (auto dest: valid_irq_handlers_ctes_ofD)[1]
  done

lemma is_simple_cap'_IRQHandlerCap[Interrupt_R_assms]:
  "isIRQHandlerCap cap \<Longrightarrow> is_simple_cap' cap"
  by (clarsimp simp: isCap_simps is_simple_cap'_def)

lemma sameRegionAs_IRQControl_handler[Interrupt_R_assms, simp]:
  "global.sameRegionAs capability.IRQControlCap (capability.IRQHandlerCap irq)"
  by (simp add: sameRegionAs_def3 isCap_simps)

lemma updateIRQState_invs'[wp]:
  "\<lbrace>invs' and K (irq \<le> maxIRQ)\<rbrace>
   updateIRQState irq state
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: updateIRQState_def)
  apply wp
  apply (fastforce simp: invs'_def valid_state'_def cur_tcb'_def
                         valid_idle'_def valid_irq_node'_def
                         valid_arch_state'_def valid_global_refs'_def
                         global_refs'_def valid_machine_state'_def
                         if_unsafe_then_cap'_def ex_cte_cap_to'_def
                         valid_irq_handlers'_def irq_issued'_def
                         cteCaps_of_def valid_irq_masks'_def
                         bitmapQ_defs  valid_x64_irq_state'_def
                         all_ioports_issued'_def issued_ioports'_def)
  done

lemma dmo_ioapicMapPinToVector_invs'[wp]:
  "doMachineOp (ioapicMapPinToVector a b c d e) \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_ioapicMapPinToVector no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
                in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (wpsimp wp: ioapicMapPinToVector_def machine_op_lift_def
                      machine_rest_lift_def split_def)+
  done

lemma arch_invoke_irq_control_invs'[Interrupt_R_assms, wp]:
  "\<lbrace>invs' and arch_irq_control_inv_valid' i\<rbrace> Arch.performIRQControl i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: X64_H.performIRQControl_def)
  apply (rule hoare_pre)
   apply (wp cteInsert_simple_invs
          | simp add: cte_wp_at_ctes_of isCap_simps
          | wpc)+
  apply (clarsimp simp: cte_wp_at_ctes_of IRQHandler_valid'
                        is_simple_cap'_def isCap_simps
                        safe_parent_for'_def sameRegionAs_def3)
  apply (rule conjI, clarsimp simp: cte_wp_at_ctes_of)
   apply (case_tac ctea)
   apply (auto dest: valid_irq_handlers_ctes_ofD
               simp: invs'_def valid_state'_def IRQ_def)[1]
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac ctea)
  apply (auto dest: valid_irq_handlers_ctes_ofD
              simp: invs'_def valid_state'_def IRQ_def)[1]
  done

lemma handle_reserved_irq_corres[Interrupt_R_assms, corres]:
  "corres dc einvs
     (\<lambda>s. invs' s \<and> (irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s))
     (handle_reserved_irq irq) (handleReservedIRQ irq)"
  unfolding handle_reserved_irq_def handleReservedIRQ_def by corres

lemma maskIrqSignal_corres[Interrupt_R_assms, corres]:
  "corres dc \<top> \<top> (arch_mask_irq_signal irq) (Arch.maskIrqSignal irq)"
  unfolding arch_mask_irq_signal_def maskIrqSignal_def when_def
  by (corres corres: corres_machine_op)

lemma dmo_ackInterrupt_corres[Interrupt_R_assms, corres]:
  "corres dc \<top> \<top> (do_machine_op (ackInterrupt irq)) (doMachineOp (ackInterrupt irq))"
  by (corres corres: corres_machine_op)

crunch maskIrqSignal
  for invs'[Interrupt_R_assms]: invs'
  (wp: dmo_maskInterrupt_True ignore: doMachineOp)

lemma handleReservedIRQ_invs'[Interrupt_R_assms]:
  "\<lbrace>invs' and (\<lambda>s. irq \<in> non_kernel_IRQs \<longrightarrow> sch_act_not (ksCurThread s) s)\<rbrace>
   handleReservedIRQ irq
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: handleReservedIRQ_def)


end (* Arch *)

interpretation Interrupt_R?: Interrupt_R X64.arch_irq_control_inv_valid'
                                         X64.arch_irq_control_inv_relation
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Interrupt_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Interrupt_R_2_assms

lemma invoke_arch_irq_handler_invs'[Interrupt_R_2_assms, wp]:
  "\<lbrace>invs' and irq_handler_inv_valid' i\<rbrace> Arch.invokeIRQHandler i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (cases i; wpsimp simp: X64_H.invokeIRQHandler_def)

end (* Arch *)

interpretation Interrupt_R_2?: Interrupt_R_2 X64.arch_irq_control_inv_valid'
                                             X64.arch_irq_control_inv_relation
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Interrupt_R_2_assms)?)?)
qed

end
