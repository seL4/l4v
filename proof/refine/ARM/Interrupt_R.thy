(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Refinement for interrupt controller operations
*)

theory Interrupt_R
imports Ipc_R Invocations_R
begin

context Arch begin

(*FIXME: arch-split: move up *)
requalify_types
  irqcontrol_invocation

lemmas [crunch_def] = decodeIRQControlInvocation_def performIRQControl_def

context begin global_naming global

(*FIXME: arch-split: move up *)
requalify_types
  Invocations_H.irqcontrol_invocation

(*FIXME: arch-split*)
requalify_facts
  Interrupt_H.decodeIRQControlInvocation_def
  Interrupt_H.performIRQControl_def

end
end

primrec
  irq_handler_inv_relation :: "irq_handler_invocation \<Rightarrow> irqhandler_invocation \<Rightarrow> bool"
where
  "irq_handler_inv_relation (Invocations_A.ACKIrq irq) x = (x = AckIRQ irq)"
| "irq_handler_inv_relation (Invocations_A.ClearIRQHandler irq) x = (x = ClearIRQHandler irq)"
| "irq_handler_inv_relation (Invocations_A.SetIRQHandler irq cap ptr) x =
       (\<exists>cap'. x = SetIRQHandler irq cap' (cte_map ptr) \<and> cap_relation cap cap')"

consts
  interrupt_control_relation :: "arch_irq_control_invocation \<Rightarrow> Arch.irqcontrol_invocation \<Rightarrow> bool"

primrec
  arch_irq_control_inv_relation :: "arch_irq_control_invocation \<Rightarrow> Arch.irqcontrol_invocation \<Rightarrow> bool"
where
  "arch_irq_control_inv_relation (ARM_A.ArchIRQControlIssue i ptr1 ptr2 t) x =
     (x = ARM_H.IssueIRQHandler i (cte_map ptr1) (cte_map ptr2) t)"
| "arch_irq_control_inv_relation (ARM_A.IssueSGISignal irq target ptr ptr') x =
     (x = ARM_H.IssueSGISignal (ucast irq) (ucast target) (cte_map ptr) (cte_map ptr'))"

primrec
  irq_control_inv_relation :: "irq_control_invocation \<Rightarrow> irqcontrol_invocation \<Rightarrow> bool"
where
  "irq_control_inv_relation (Invocations_A.IRQControl irq slot slot') x
       = (x = IssueIRQHandler irq (cte_map slot) (cte_map slot'))"
| "irq_control_inv_relation (Invocations_A.ArchIRQControl ivk) x
       = (\<exists>ivk'. x = ArchIRQControl ivk' \<and> arch_irq_control_inv_relation ivk ivk')"

primrec
  irq_handler_inv_valid' :: "irqhandler_invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "irq_handler_inv_valid' (AckIRQ irq) = (\<lambda>s. intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive)"
| "irq_handler_inv_valid' (ClearIRQHandler irq) = \<top>"
| "irq_handler_inv_valid' (SetIRQHandler irq cap cte_ptr)
     = (valid_cap' cap and valid_cap' (IRQHandlerCap irq)
           and K (isNotificationCap cap)
           and cte_wp_at' (badge_derived' cap \<circ> cteCap) cte_ptr
           and (\<lambda>s. \<exists>ptr'. cte_wp_at' (\<lambda>cte. cteCap cte = IRQHandlerCap irq) ptr' s)
           and ex_cte_cap_wp_to' isCNodeCap cte_ptr)"

primrec
  arch_irq_control_inv_valid' :: "Arch.irqcontrol_invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "arch_irq_control_inv_valid' (ARM_H.IssueIRQHandler irq p p' t) =
                (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) p and
                 cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) p' and
                 ex_cte_cap_to' p and real_cte_at' p and
                (Not o irq_issued' irq) and K (irq \<le> maxIRQ))"
| "arch_irq_control_inv_valid' (ARM_H.IssueSGISignal irq target src_slot sgi_slot) =
     (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) sgi_slot and
      cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) src_slot and
      ex_cte_cap_to' sgi_slot and real_cte_at' sgi_slot)"

primrec
  irq_control_inv_valid' :: "irqcontrol_invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "irq_control_inv_valid' (ArchIRQControl ivk) = arch_irq_control_inv_valid' ivk"
| "irq_control_inv_valid' (IssueIRQHandler irq ptr ptr') =
       (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) ptr and
        cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) ptr' and
        ex_cte_cap_to' ptr and real_cte_at' ptr and
        (Not o irq_issued' irq) and K (irq \<le> maxIRQ))"

context begin interpretation Arch . (*FIXME: arch-split*)

lemma decodeIRQHandlerInvocation_corres:
  "\<lbrakk> list_all2 cap_relation (map fst caps) (map fst caps');
    list_all2 (\<lambda>p pa. snd pa = cte_map (snd p)) caps caps' \<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> irq_handler_inv_relation) invs invs'
     (decode_irq_handler_invocation label irq caps)
     (decodeIRQHandlerInvocation label irq caps')"
  apply (simp add: decode_irq_handler_invocation_def decodeIRQHandlerInvocation_def
                 split del: if_split)
  apply (cases caps)
   apply (simp add: returnOk_def split: invocation_label.split gen_invocation_labels.split list.splits split del: if_split)
   defer
  apply (clarsimp simp: list_all2_Cons1 split del: if_split)
  apply (simp add: returnOk_def split: invocation_label.split gen_invocation_labels.split list.splits)
  apply (clarsimp split: cap_relation_split_asm arch_cap.split_asm simp: returnOk_def)
  done

crunch decodeIRQHandlerInvocation
  for inv[wp]: "P"
  (simp: crunch_simps)

lemma decode_irq_handler_valid'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' fst cap)
        \<and> (\<exists>ptr'. cte_wp_at' (\<lambda>cte. cteCap cte = IRQHandlerCap irq) ptr' s)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' (fst cap) (irq_node' s). ex_cte_cap_to' r s)
        \<and> (\<forall>cap \<in> set caps. ex_cte_cap_wp_to' isCNodeCap (snd cap) s)
        \<and> (\<forall>cap \<in> set caps. cte_wp_at' (badge_derived' (fst cap) \<circ> cteCap) (snd cap) s)
        \<and> s \<turnstile>' IRQHandlerCap irq\<rbrace>
     decodeIRQHandlerInvocation label irq caps
   \<lbrace>irq_handler_inv_valid'\<rbrace>,-"
  apply (simp add: decodeIRQHandlerInvocation_def Let_def split_def
               split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  apply (clarsimp simp: neq_Nil_conv isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule (1) valid_irq_handlers_ctes_ofD)
    apply (simp add: invs'_def valid_state'_def)
   apply (simp add: irq_issued'_def)
  apply clarsimp
  done

lemma is_irq_active_corres:
  "corres (=) \<top> \<top> (is_irq_active irq) (isIRQActive irq)"
  apply (simp add: is_irq_active_def isIRQActive_def get_irq_state_def
                   getIRQState_def getInterruptState_def)
  apply (clarsimp simp: state_relation_def interrupt_state_relation_def)
  apply (drule_tac x=irq in spec)+
  apply (simp add: irq_state_relation_def
            split: irqstate.split_asm irq_state.split_asm)
  done

crunch isIRQActive
  for inv: "P"

lemma isIRQActive_wp:
  "\<lbrace>\<lambda>s. \<forall>rv. (irq_issued' irq s \<longrightarrow> rv) \<longrightarrow> Q rv s\<rbrace> isIRQActive irq \<lbrace>Q\<rbrace>"
  apply (simp add: isIRQActive_def getIRQState_def
                   getInterruptState_def)
  apply wp
  apply (clarsimp simp: irq_issued'_def)
  done

lemma checkIRQ_corres:
  "corres (ser \<oplus> dc) \<top> \<top> (arch_check_irq irq) (checkIRQ irq)"
  unfolding arch_check_irq_def checkIRQ_def rangeCheck_def
  apply (rule corres_guard_imp)
    apply (clarsimp simp: minIRQ_def unlessE_whenE not_le)
    apply (rule corres_whenE)
      apply fastforce+
  done

lemma whenE_rangeCheck_eq:
  "(rangeCheck (x :: 'a :: {linorder, integral}) y z) =
    (whenE (x < fromIntegral y \<or> fromIntegral z < x)
      (throwError (RangeError (fromIntegral y) (fromIntegral z))))"
  by (simp add: rangeCheck_def unlessE_whenE linorder_not_le[symmetric])

(* 125 = maxIRQ *)
lemma unat_ucast_ucast_shenanigans[simp]:
  "unat (yf :: machine_word) \<le> (125::nat) \<Longrightarrow> ucast ((ucast yf) :: word8) = yf"
  apply (subgoal_tac "unat yf \<le> unat 125")
   apply (thin_tac "unat yf \<le> 125")
   apply (subst (asm) word_le_nat_alt[symmetric])
   apply (simp add: ucast_ucast_mask mask_def)
  by (word_bitwise, auto)

lemmas irq_const_defs = minIRQ_def

crunch arch_check_irq, checkIRQ
  for inv: "P"
  (simp: crunch_simps)

lemma arch_check_irq_maxIRQ_valid:
  "\<lbrace>\<top>\<rbrace> arch_check_irq irq \<lbrace>\<lambda>_ s. irq \<le> Kernel_Config.maxIRQ\<rbrace>, -"
  unfolding arch_check_irq_def
  apply (wpsimp simp: validE_R_def wp: whenE_throwError_wp)
  apply (simp add: word_not_le)
  done

lemma arch_check_irq_maxIRQ_valid':
  "\<lbrace>\<top>\<rbrace> arch_check_irq irq \<lbrace>\<lambda>_ _. irq \<le> Kernel_Config.maxIRQ\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (wp arch_check_irq_maxIRQ_valid)

lemma isSGITargetValid_eq:
  "isSGITargetValid w = sgi_target_valid w"
  unfolding isSGITargetValid_def sgi_target_valid_def
  by simp

lemma sgi_target_cast[simp]:
  "sgi_target_valid w \<Longrightarrow> ucast (ucast w :: sgi_target) = w"
  unfolding sgi_target_valid_def gicNumTargets_def
  by (simp flip: sgi_target_len_def add: ucast_ucast_len sgi_target_len_val)

lemma sgi_irq_cast:
  "w \<le> word_of_nat numSGIs - 1 \<Longrightarrow> ucast (ucast w :: sgi_irq) = (w :: machine_word)"
  unfolding numSGIs_def
  by (simp flip: sgi_irq_len_def
           add: ucast_ucast_len sgi_irq_len_val word_le_nat_alt word_less_nat_alt)

lemma arch_decodeIRQControlInvocation_corres:
  "list_all2 cap_relation caps caps' \<Longrightarrow>
   corres (ser \<oplus> arch_irq_control_inv_relation)
     (invs and (\<lambda>s. \<forall>cp \<in> set caps. s \<turnstile> cp))
     (invs' and (\<lambda>s. \<forall>cp \<in> set caps'. s \<turnstile>' cp))
     (arch_decode_irq_control_invocation label args slot caps)
     (ARM_H.decodeIRQControlInvocation label args (cte_map slot) caps')"
  apply (clarsimp simp: arch_decode_irq_control_invocation_def ARM_H.decodeIRQControlInvocation_def Let_def)
  apply (rule conjI, clarsimp)
   prefer 2
   apply clarsimp
   apply (cases caps, simp)
    apply (auto split: arch_invocation_label.splits list.splits invocation_label.splits
                 simp: length_Suc_conv list_all2_Cons1 whenE_rangeCheck_eq liftE_bindE split_def)[2]
  apply (cases caps, simp split: list.split)
  apply (case_tac "\<exists>n. length args = Suc (Suc (Suc (Suc n)))",
              clarsimp simp: length_Suc_conv list_all2_Cons1 liftE_bindE split_def)
   prefer 2 apply (auto split: list.split)[1]
  \<comment>\<open>ARMIRQIssueSGISignal\<close>
  apply (rule conjI, clarsimp)
   apply (simp add: range_check_def rangeCheck_def)
   apply (corres corres: lookupSlotForCNodeOp_corres ensureEmptySlot_corres corres_returnOkTT
                 term_simp: numSGIs_def isSGITargetValid_eq sgi_irq_cast)
    apply fastforce
   apply fastforce
  \<comment>\<open>ARMIRQIssueIRQHandler\<close>
  apply (rule impI, rule conjI, clarsimp)
  \<comment>\<open>ARMIRQIssueIRQHandler\<close>
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE[OF checkIRQ_corres])
       apply (rule_tac F="y \<le> Kernel_Config.maxIRQ" in corres_gen_asm)
       apply (clarsimp simp: toEnum_unat_ucast le_maxIRQ_machine_less_irqBits_val)
       apply (rule corres_split_eqr[OF is_irq_active_corres])
         apply (rule whenE_throwError_corres, clarsimp, clarsimp)
         apply (rule corres_splitEE)
            apply (rule lookupSlotForCNodeOp_corres; simp)
           apply (rule corres_splitEE)
              apply (rule ensureEmptySlot_corres; simp)
             apply (rule corres_returnOkTT)
             apply (clarsimp simp: arch_irq_control_inv_relation_def )
            apply ((wpsimp wp: isIRQActive_inv arch_check_irq_maxIRQ_valid' checkIRQ_inv
                           simp: invs_valid_objs invs_psp_aligned invs_valid_objs'
                                 invs_pspace_aligned' invs_pspace_distinct'
                   | strengthen invs_valid_objs invs_psp_aligned
                   | wp (once) hoare_drop_imps arch_check_irq_inv)+)
  apply (auto split: arch_invocation_label.splits invocation_label.splits)
  done

lemma irqhandler_simp[simp]:
  "gen_invocation_type label \<noteq> IRQIssueIRQHandler \<Longrightarrow>
   (case gen_invocation_type label of IRQIssueIRQHandler \<Rightarrow> b | _ \<Rightarrow> c) = c"
  by (clarsimp split: gen_invocation_labels.splits)

lemmas unat_le_mono = word_le_nat_alt [THEN iffD1]

lemma decodeIRQControlInvocation_corres:
  "list_all2 cap_relation caps caps' \<Longrightarrow>
   corres (ser \<oplus> irq_control_inv_relation)
     (invs and (\<lambda>s. \<forall>cp \<in> set caps. s \<turnstile> cp)) (invs' and (\<lambda>s. \<forall>cp \<in> set caps'. s \<turnstile>' cp))
     (decode_irq_control_invocation label args slot caps)
     (decodeIRQControlInvocation label args (cte_map slot) caps')"
  apply (clarsimp simp: decode_irq_control_invocation_def decodeIRQControlInvocation_def
                        arch_check_irq_def ARM_H.checkIRQ_def
                  split del: if_split cong: if_cong
                  split: )
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp)
    apply (cases caps, simp split: list.split)
    apply (case_tac "\<exists>n. length args = Suc (Suc (Suc n))")
     apply (clarsimp simp: list_all2_Cons1 Let_def split_def liftE_bindE
                           length_Suc_conv checkIRQ_def )
     defer
     apply (subgoal_tac "length args \<le> 2", clarsimp split: list.split)
     apply arith
    apply (simp add: minIRQ_def o_def)
    apply (auto intro!: corres_guard_imp[OF arch_decodeIRQControlInvocation_corres])[1]
   apply (auto intro!: corres_guard_imp[OF arch_decodeIRQControlInvocation_corres]
               dest!: not_le_imp_less
               simp: minIRQ_def o_def length_Suc_conv whenE_rangeCheck_eq ucast_nat_def
               split: list.splits)[1]
  apply (simp add: minIRQ_def o_def length_Suc_conv whenE_rangeCheck_eq)
  apply (rule corres_guard_imp)
    apply (rule whenE_throwError_corres, clarsimp, clarsimp)
    apply (rule_tac F="y \<le> Kernel_Config.maxIRQ" in corres_gen_asm)
    apply (clarsimp simp: toEnum_unat_ucast le_maxIRQ_machine_less_irqBits_val)
    apply (rule corres_split_eqr[OF is_irq_active_corres])
      apply (rule whenE_throwError_corres, clarsimp, clarsimp)
      apply (rule corres_splitEE)
         apply (rule lookupSlotForCNodeOp_corres; simp)
        apply (rule corres_splitEE)
           apply (rule ensureEmptySlot_corres; simp)
          apply (rule corres_returnOkTT)
          apply (clarsimp simp: arch_irq_control_inv_relation_def )
         apply (wpsimp wp: isIRQActive_inv arch_check_irq_maxIRQ_valid' checkIRQ_inv
                       simp: invs_valid_objs invs_psp_aligned invs_valid_objs'
                             invs_pspace_aligned' invs_pspace_distinct'
                | strengthen invs_valid_objs invs_psp_aligned
                | wp (once) hoare_drop_imps arch_check_irq_inv)+
   apply (auto split: arch_invocation_label.splits invocation_label.splits
               simp: not_less unat_le_helper)
  done

crunch "InterruptDecls_H.decodeIRQControlInvocation"
  for inv[wp]: "P"
  (simp: crunch_simps)


(* Levity: added (20090201 10:50:27) *)
declare ensureEmptySlot_stronger [wp]

lemma lsfco_real_cte_at'[wp]:
  "\<lbrace>valid_objs' and valid_cap' croot\<rbrace>
     lookupSlotForCNodeOp is_src croot ptr depth
   \<lbrace>\<lambda>rv s. real_cte_at' rv s\<rbrace>,-"
  apply (simp add: lookupSlotForCNodeOp_def split_def unlessE_def
                   whenE_def
               split del: if_split
             cong: if_cong list.case_cong capability.case_cong)
  apply (rule hoare_pre)
   apply (wp resolveAddressBits_real_cte_at'
            | simp
            | wpc | wp (once) hoare_drop_imps)+
  done

lemma arch_decode_irq_control_valid'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' cap)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
        \<and> cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot s\<rbrace>
     ARM_H.decodeIRQControlInvocation label args slot caps
   \<lbrace>arch_irq_control_inv_valid'\<rbrace>,-"
  apply (clarsimp simp add: ARM_H.decodeIRQControlInvocation_def Let_def split_def
                            rangeCheck_def unlessE_whenE
                  split del: if_split
                  cong: if_cong list.case_cong prod.case_cong arch_invocation_label.case_cong)
  apply (rule hoare_pre)
   apply (simp add: rangeCheck_def unlessE_whenE checkIRQ_def
               cong: list.case_cong prod.case_cong
          | wp whenE_throwError_wp isIRQActive_wp ensureEmptySlot_stronger
          | wpc
          | wp (once) hoare_drop_imps)+
  apply (clarsimp, rule conjI; clarsimp)
  apply (clarsimp simp: invs_valid_objs' toEnum_unat_ucast
                        le_maxIRQ_machine_less_irqBits_val irq_machine_le_maxIRQ_irq)
  done

lemma decode_irq_control_valid'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' cap)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
        \<and> cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot s\<rbrace>
     decodeIRQControlInvocation label args slot caps
   \<lbrace>irq_control_inv_valid'\<rbrace>,-"
  apply (simp add: decodeIRQControlInvocation_def Let_def split_def checkIRQ_def
                   rangeCheck_def unlessE_whenE
                split del: if_split cong: if_cong list.case_cong
                                          gen_invocation_labels.case_cong)
  apply (wpsimp wp: ensureEmptySlot_stronger isIRQActive_wp whenE_throwError_wp
                simp: o_def
         | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: invs_valid_objs' toEnum_unat_ucast
                        le_maxIRQ_machine_less_irqBits_val irq_machine_le_maxIRQ_irq)
  done

lemma valid_globals_ex_cte_cap_irq:
  "\<lbrakk> ex_cte_cap_wp_to' isCNodeCap ptr s; valid_global_refs' s;
         valid_objs' s \<rbrakk>
       \<Longrightarrow> ptr \<noteq> intStateIRQNode (ksInterruptState s) + 2 ^ cte_level_bits * ucast (irq :: irq)"
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_wp_to'_def)
  apply (drule(1) ctes_of_valid'[rotated])
  apply (drule(1) valid_global_refsD')
  apply (drule subsetD[rotated], erule cte_refs_capRange)
   apply (clarsimp simp: isCap_simps)
  apply (subgoal_tac "irq_node' s + 2 ^ cte_level_bits * ucast irq \<in> global_refs' s")
   apply blast
  apply (simp add: global_refs'_def cte_level_bits_def
                   mult.commute mult.left_commute cteSizeBits_def shiftl_t2n)
  done

lemma no_fail_deactivateInterrupt[wp, simp]:
  "config_ARM_GIC_V3 \<Longrightarrow> no_fail \<top> (deactivateInterrupt irq)"
  unfolding deactivateInterrupt_def
  by wpsimp

lemma arch_invokeIRQHandler_corres:
  "irq_handler_inv_relation i i' \<Longrightarrow>
   corres dc \<top> \<top> (arch_invoke_irq_handler i) (ARM_H.invokeIRQHandler i')"
  apply (cases i; clarsimp simp: ARM_H.invokeIRQHandler_def theIRQ_def)
  apply (intro conjI impI; rule corres_machine_op, rule corres_Id; simp add: no_fail_maskInterrupt)
  done


lemma invokeIRQHandler_corres:
  "irq_handler_inv_relation i i' \<Longrightarrow>
   corres dc (einvs and irq_handler_inv_valid i)
             (invs' and irq_handler_inv_valid' i')
     (invoke_irq_handler i)
     (InterruptDecls_H.invokeIRQHandler i')"
  supply arch_invoke_irq_handler.simps[simp del]
  apply (cases i; simp add: Interrupt_H.invokeIRQHandler_def)
    apply (rule corres_guard_imp, rule arch_invokeIRQHandler_corres; simp)
   apply (rename_tac word cap prod)
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getIRQSlot_corres])
       apply simp
       apply (rule corres_split_nor[OF cap_delete_one_corres])
         apply (rule cteInsert_corres, simp+)
        apply (rule_tac Q'="\<lambda>rv s. einvs s \<and> cte_wp_at (\<lambda>c. c = cap.NullCap) irq_slot s
                                  \<and> (a, b) \<noteq> irq_slot
                                  \<and> cte_wp_at (is_derived (cdt s) (a, b) cap) (a, b) s"
                      in hoare_post_imp)
         apply fastforce
        apply (wp cap_delete_one_still_derived)+
       apply (strengthen invs_mdb_strengthen')
       apply wp+
      apply (simp add: conj_comms eq_commute)
      apply (wp get_irq_slot_different hoare_drop_imps)+
    apply (clarsimp simp: valid_state_def invs_def)
    apply (erule cte_wp_at_weakenE, simp add: is_derived_use_interrupt)
   apply fastforce
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getIRQSlot_corres])
      apply simp
      apply (rule cap_delete_one_corres)
     apply wp+
   apply simp+
  done

lemma ntfn_badge_derived_enough_strg:
  "cte_wp_at' (\<lambda>cte. isNotificationCap cap \<and> badge_derived' cap (cteCap cte)) ptr s
        \<longrightarrow> cte_wp_at' (is_derived' ctes ptr cap \<circ> cteCap) ptr s"
  by (clarsimp simp: cte_wp_at_ctes_of isCap_simps
                     badge_derived'_def is_derived'_def vsCapRef_def)

lemma cteDeleteOne_ex_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_wp_to' P p\<rbrace> cteDeleteOne ptr \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF cteDeleteOne_irq_node'])
   apply (wp hoare_vcg_ex_lift cteDeleteOne_cte_wp_at_preserved)
   apply (case_tac cap, simp_all add: finaliseCap_def isCap_simps)
  done

lemma cteDeleteOne_other_cap:
  "\<lbrace>(\<lambda>s. cte_wp_at' (P o cteCap) p s) and K (p \<noteq> p')\<rbrace>
     cteDeleteOne p'
   \<lbrace>\<lambda>rv s. cte_wp_at' (P o cteCap) p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: tree_cte_cteCap_eq)
  apply (wp cteDeleteOne_cteCaps_of)
  apply simp
  done

lemma isnt_irq_handler_strg:
  "(\<not> isIRQHandlerCap cap) \<longrightarrow> (\<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> P irq)"
  by (clarsimp simp: isCap_simps)

lemma dmo_maskInterrupt:
  "\<lbrace>\<lambda>s. invs' s \<and> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive\<rbrace>
   doMachineOp (maskInterrupt m irq)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (simp add: valid_irq_masks'_def valid_machine_state'_def
                   ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma doMachineOp_deactivateInterrupt[wp]:
  "\<lbrace> \<lambda>s. invs' s \<and> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive \<and> config_ARM_GIC_V3 \<rbrace>
   doMachineOp (deactivateInterrupt irq)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding deactivateInterrupt_def
  by (cases config_ARM_GIC_V3; wpsimp wp: dmo_maskInterrupt)

lemma invoke_arch_irq_handler_invs'[wp]:
  "\<lbrace>invs' and irq_handler_inv_valid' i\<rbrace> ARM_H.invokeIRQHandler i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (cases i; wpsimp simp: ARM_H.invokeIRQHandler_def theIRQ_def)
  apply (rule conjI; wpsimp wp: dmo_maskInterrupt)
  done

lemma invoke_irq_handler_invs'[wp]:
  "\<lbrace>invs' and irq_handler_inv_valid' i\<rbrace>
    InterruptDecls_H.invokeIRQHandler i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (cases i; simp add: Interrupt_H.invokeIRQHandler_def)
    apply wpsimp
   apply (wp cteInsert_invs)+
   apply (strengthen ntfn_badge_derived_enough_strg isnt_irq_handler_strg)
   apply (wp cteDeleteOne_other_cap cteDeleteOne_other_cap[unfolded o_def])
  apply (rename_tac word1 cap word2)
  apply (simp add: getInterruptState_def getIRQSlot_def locateSlot_conv)
  apply wp
  apply (rename_tac word1 cap word2 s)
  apply (clarsimp simp: ucast_nat_def)
  apply (drule_tac irq=word1 in valid_globals_ex_cte_cap_irq)
    apply clarsimp+
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_to'_def
                        isCap_simps untyped_derived_eq_def)
  apply (fastforce simp: cte_level_bits_def badge_derived'_def cteSizeBits_def shiftl_t2n)
  done

lemma IRQHandler_valid':
  "(s' \<turnstile>' IRQHandlerCap irq) = (irq \<le> maxIRQ)"
  by (simp add: valid_cap'_def capAligned_def word_bits_conv)

crunch setIRQState
  for valid_mdb'[wp]: "valid_mdb'"

lemma no_fail_setIRQTrigger[wp]:
  "no_fail \<top> (setIRQTrigger irq t)"
  unfolding setIRQTrigger_def
  by wpsimp

lemma setIRQTrigger_corres:
  "corres dc \<top> \<top> (do_machine_op (setIRQTrigger irq t)) (doMachineOp (setIRQTrigger irq t))"
  apply (rule corres_machine_op)
  apply (rule corres_guard_imp)
    apply (rule corres_rel_imp)
     apply (wp
            | rule corres_underlying_trivial
            | simp add: dc_def)+
  done

crunch set_irq_state
  for valid_arch_state[wp]: valid_arch_state

lemma SGISignalCap_valid[simp, intro!]:
  "valid_cap' (ArchObjectCap (SGISignalCap irq target)) s"
  by (simp add: valid_cap'_def capAligned_def word_bits_def)

lemma arch_performIRQControl_corres:
  "arch_irq_control_inv_relation x2 ivk' \<Longrightarrow> corres (dc \<oplus> dc)
          (einvs and arch_irq_control_inv_valid x2)
          (invs' and arch_irq_control_inv_valid' ivk')
          (arch_invoke_irq_control x2)
          (Arch.performIRQControl ivk')"
  apply (cases x2; simp add: ARM_H.performIRQControl_def invoke_irq_control.cases IRQ_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor)
        apply (rule setIRQTrigger_corres)
       apply (rule corres_split_nor)
          apply (rule setIRQState_corres)
          apply (simp add: irq_state_relation_def)
         apply (rule cteInsert_simple_corres; simp)
        apply (wp | simp add: irq_state_relation_def IRQHandler_valid IRQHandler_valid')+
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cte_wp_at_caps_of_state
                          is_simple_cap_def is_cap_simps arch_irq_control_inv_valid_def
                          safe_parent_for_def)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def IRQHandler_valid
                         IRQHandler_valid' is_simple_cap'_def isCap_simps IRQ_def)
   apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
   apply (rename_tac cte', case_tac cte')
   apply (clarsimp simp: isCap_simps sameRegionAs_def3)
   apply (auto dest: valid_irq_handlers_ctes_ofD)[1]
  apply (corres corres: cteInsert_simple_corres)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def cte_wp_at_caps_of_state
                         is_simple_cap_def is_cap_simps arch_irq_control_inv_valid_def
                         safe_parent_for_def is_irq_control_descendant_def)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                        is_simple_cap'_def isCap_simps)
  apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
  apply (rename_tac cte', case_tac cte', simp add: isCap_simps)
  done

lemma performIRQControl_corres:
  "irq_control_inv_relation i i' \<Longrightarrow>
   corres (dc \<oplus> dc) (einvs and irq_control_inv_valid i)
             (invs' and irq_control_inv_valid' i')
     (invoke_irq_control i)
     (performIRQControl i')"
  apply (cases i, simp_all add: performIRQControl_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor[OF setIRQState_corres])
        apply (simp add: irq_state_relation_def)
       apply (rule cteInsert_simple_corres)
         apply (wp | simp add: IRQHandler_valid IRQHandler_valid')+
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                          cte_wp_at_caps_of_state is_simple_cap_def
                          is_cap_simps safe_parent_for_def)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                         IRQHandler_valid  IRQHandler_valid' is_simple_cap'_def
                         isCap_simps)
   apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
   apply (case_tac ctea)
   apply (clarsimp simp: isCap_simps sameRegionAs_def3)
   apply (auto dest: valid_irq_handlers_ctes_ofD)[1]
  by (clarsimp simp: arch_performIRQControl_corres)

crunch setIRQState
  for valid_cap'[wp]: "valid_cap' cap"

lemma setIRQState_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setIRQState st irq \<lbrace>\<lambda>_. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: setIRQState_def doMachineOp_def
                   split_def setInterruptState_def getInterruptState_def)
  apply wp
  apply (clarsimp simp: ex_cte_cap_to'_def)
  done

lemma setIRQState_issued[wp]:
  "\<lbrace>K (st = IRQSignal)\<rbrace> setIRQState st irq \<lbrace>\<lambda>rv. irq_issued' irq\<rbrace>"
  apply (simp add: setIRQState_def irq_issued'_def setInterruptState_def
                   getInterruptState_def)
  apply wp
  apply clarsimp
  done

lemma dmo_setIRQTrigger_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (setIRQTrigger irq t) \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_setIRQTrigger no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: setIRQTrigger_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma arch_invoke_irq_control_invs'[wp]:
  "\<lbrace>invs' and arch_irq_control_inv_valid' i\<rbrace> ARM_H.performIRQControl i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: ARM_H.performIRQControl_def)
  apply (rule hoare_pre)
   apply (wp cteInsert_simple_invs
          | simp add: cte_wp_at_ctes_of isCap_simps IRQ_def
          | wpc)+
  apply (clarsimp simp: cte_wp_at_ctes_of IRQHandler_valid' is_simple_cap'_def isCap_simps
                        safe_parent_for'_def sameRegionAs_def3)
  apply (clarsimp simp: capRange_def)
  apply (rule conjI; clarsimp simp: cte_wp_at_ctes_of; case_tac ctea)
   apply (auto dest: valid_irq_handlers_ctes_ofD
               simp: invs'_def valid_state'_def IRQ_def)
  done

lemma invoke_irq_control_invs'[wp]:
  "\<lbrace>invs' and irq_control_inv_valid' i\<rbrace> performIRQControl i \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (cases i, simp_all add: performIRQControl_def)
  apply (rule hoare_pre)
   apply (wp cteInsert_simple_invs | simp add: cte_wp_at_ctes_of)+
  apply (clarsimp simp: cte_wp_at_ctes_of IRQHandler_valid'
                        is_simple_cap'_def isCap_simps
                        safe_parent_for'_def sameRegionAs_def3)
  apply (case_tac ctea)
  apply (auto dest: valid_irq_handlers_ctes_ofD
              simp: invs'_def valid_state'_def)
  done

lemma getIRQState_corres:
  "corres irq_state_relation \<top> \<top>
       (get_irq_state irq) (getIRQState irq)"
  apply (simp add: get_irq_state_def getIRQState_def getInterruptState_def)
  apply (clarsimp simp: state_relation_def interrupt_state_relation_def)
  done

lemma getIRQState_prop:
  "\<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s) irq)\<rbrace>
     getIRQState irq
   \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: getIRQState_def getInterruptState_def)
  apply wp
  apply simp
  done

lemma decDomainTime_corres:
  "corres dc \<top> \<top> dec_domain_time decDomainTime"
  apply (simp add:dec_domain_time_def corres_underlying_def decDomainTime_def simpler_modify_def)
  apply (clarsimp simp: state_relation_def cdt_relation_def)
  done

lemma thread_state_case_if:
 "(case state of Structures_A.thread_state.Running \<Rightarrow> f | _ \<Rightarrow> g) =
  (if state = Structures_A.thread_state.Running then f else g)"
  by (case_tac state,auto)

lemma threadState_case_if:
 "(case state of Structures_H.thread_state.Running \<Rightarrow> f | _ \<Rightarrow> g) =
  (if state = Structures_H.thread_state.Running then f else g)"
  by (case_tac state,auto)

lemma ready_qs_distinct_domain_time_update[simp]:
  "ready_qs_distinct (domain_time_update f s) = ready_qs_distinct s"
  by (clarsimp simp: ready_qs_distinct_def)

lemma timerTick_corres:
  "corres dc
     (cur_tcb and valid_sched and pspace_aligned and pspace_distinct) invs'
     timer_tick timerTick"
  apply (simp add: timerTick_def timer_tick_def)
  apply (simp add: thread_state_case_if threadState_case_if)
  apply (rule_tac Q="cur_tcb and valid_sched and pspace_aligned and pspace_distinct"
              and Q'=invs'
               in corres_guard_imp)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF getCurThread_corres])
        apply simp
        apply (rule corres_split[OF getThreadState_corres])
          apply (rename_tac state state')
          apply (rule corres_split[where r' = dc])
             apply (rule corres_if[where Q = \<top> and Q' = \<top>])
               apply (case_tac state,simp_all)[1]
              apply (rule_tac r'="(=)" in corres_split[OF threadGet_corres])
                 apply (simp add: tcb_relation_def)
                apply (rename_tac ts ts')
                apply (rule_tac R="1 < ts" in corres_cases)
                 apply (simp)
                 apply (unfold thread_set_time_slice_def)
                 apply (rule threadset_corres; simp add: tcb_relation_def inQ_def)
                apply simp
                apply (rule corres_split[OF threadset_corres])
                                apply (simp add: sch_act_wf_weak tcb_relation_def pred_conj_def inQ_def)+
                  apply (rule corres_split[OF tcbSchedAppend_corres], simp)
                    apply (rule rescheduleRequired_corres)
                   apply wp
                  apply ((wpsimp wp: tcbSchedAppend_sym_heap_sched_pointers
                                     tcbSchedAppend_valid_objs'
                          | strengthen valid_objs'_valid_tcbs')+)[1]
                 apply ((wpsimp wp: thread_set_valid_queues thread_set_no_change_tcb_state
                                    thread_set_weak_valid_sched_action
                         | strengthen valid_queues_in_correct_ready_q
                                      valid_queues_ready_qs_distinct)+)[1]
                apply ((wpsimp wp: threadSet_sched_pointers threadSet_valid_sched_pointers
                                   threadSet_valid_objs'
                        | strengthen valid_objs'_valid_tcbs')+)[1]
               apply wpsimp+
            apply (rule corres_when, simp)
            apply (rule corres_split[OF decDomainTime_corres])
              apply (rule corres_split[OF getDomainTime_corres])
                apply (rule corres_when,simp)
                apply (rule rescheduleRequired_corres)
               apply (wp hoare_drop_imp)+
             apply (wpsimp simp: dec_domain_time_def)
            apply (wpsimp simp: decDomainTime_def)
           apply (wpsimp wp: hoare_weak_lift_imp threadSet_timeslice_invs
                             tcbSchedAppend_valid_objs'
                             threadSet_pred_tcb_at_state threadSet_weak_sch_act_wf
                             rescheduleRequired_weak_sch_act_wf)+
              apply (strengthen valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct)
              apply (wpsimp wp: thread_set_valid_queues thread_set_weak_valid_sched_action)
             apply ((wpsimp wp: thread_set_valid_queues
                     | strengthen valid_queues_in_correct_ready_q valid_queues_ready_qs_distinct)+)[1]
            apply (wpsimp wp: thread_get_wp)
           apply wpsimp
          apply ((wpsimp wp: threadSet_sched_pointers threadSet_valid_sched_pointers
                             threadSet_valid_objs'
                  | strengthen valid_objs'_valid_tcbs'
                  | wp (once) hoare_drop_imp)+)[1]
         apply (wpsimp wp: gts_wp gts_wp')+
     apply (clarsimp simp: cur_tcb_def)
     apply (frule valid_sched_valid_queues)
     apply (fastforce simp: pred_tcb_at_def obj_at_def valid_sched_weak_strg)
    apply fastforce
   apply (fastforce simp: valid_state'_def ct_not_inQ_def)
  apply fastforce
  done

lemmas corres_eq_trivial = corres_Id[where f = h and g = h for h, simplified]

lemma handleInterrupt_corres:
  "corres dc
     (einvs) (invs' and (\<lambda>s. intStateIRQTable (ksInterruptState s) irq \<noteq> IRQInactive))
     (handle_interrupt irq) (handleInterrupt irq)"
  (is "corres dc (einvs) ?P' ?f ?g")
  apply (simp add: handle_interrupt_def handleInterrupt_def )
  apply (rule conjI[rotated]; rule impI)

   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getIRQState_corres,
                               where R="\<lambda>rv. einvs"
                                 and R'="\<lambda>rv. invs' and (\<lambda>s. rv \<noteq> IRQInactive)"])
       defer
       apply (wp getIRQState_prop getIRQState_inv do_machine_op_bind doMachineOp_bind | simp add: do_machine_op_bind doMachineOp_bind )+
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule corres_machine_op, rule corres_eq_trivial ; (simp add: dc_def no_fail_maskInterrupt no_fail_bind no_fail_ackInterrupt)+)+
      apply ((wp | simp)+)[4]
  apply (rule corres_gen_asm2)
  apply (case_tac st, simp_all add: irq_state_relation_def split: irqstate.split_asm)
   apply (simp add: getSlotCap_def bind_assoc)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getIRQSlot_corres])
       apply simp
       apply (rule corres_split[OF get_cap_corres,
                                 where R="\<lambda>rv. einvs and valid_cap rv"
                                  and R'="\<lambda>rv. invs' and valid_cap' (cteCap rv)"])
         apply (rule corres_underlying_split[where r'=dc])
            apply (case_tac xb, simp_all add: doMachineOp_return)[1]
             apply (clarsimp simp add: when_def doMachineOp_return)
             apply (rule corres_guard_imp, rule sendSignal_corres)
              apply (clarsimp simp: valid_cap_def valid_cap'_def)+
           apply (clarsimp simp: arch_mask_irq_signal_def maskIrqSignal_def)
           apply (corres corres: corres_machine_op corres_eq_trivial intro: no_fail_ackInterrupt)
          apply wpsimp+
   apply fastforce
  apply (corres corres: timerTick_corres corres_machine_op simp: bind_assoc)
   apply fastforce
  apply clarsimp
  done

lemma threadSet_ksDomainTime[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s)\<rbrace> threadSet f ptr \<lbrace>\<lambda>rv s. P (ksDomainTime s)\<rbrace>"
  apply (simp add: threadSet_def setObject_def split_def)
  apply (wp crunch_wps | simp add:updateObject_default_def)+
  done

crunch rescheduleRequired
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
(simp:tcbSchedEnqueue_def wp:unless_wp)

crunch tcbSchedAppend
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
(simp:tcbSchedEnqueue_def wp:unless_wp)

lemma updateTimeSlice_valid_pspace[wp]:
  "\<lbrace>valid_pspace'\<rbrace> threadSet (tcbTimeSlice_update (\<lambda>_. ts')) thread
  \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  apply (wp threadSet_valid_pspace'T)
  apply (auto simp: tcb_cte_cases_def tcb_cte_cases_neqs)
  done

lemma updateTimeSlice_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<rbrace>
   threadSet (tcbTimeSlice_update (\<lambda>_. ts')) thread
   \<lbrace>\<lambda>r s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp threadSet_sch_act,simp)

(* catch up tcbSchedAppend to tcbSchedEnqueue, which has these from crunches on possibleSwitchTo *)
crunch tcbSchedAppend
  for irq_handlers'[wp]: valid_irq_handlers'
  (simp: unless_def tcb_cte_cases_def tcb_cte_cases_neqs wp: crunch_wps)
crunch tcbSchedAppend
  for irqs_masked'[wp]: irqs_masked'
  (simp: unless_def wp: crunch_wps)
crunch tcbSchedAppend
  for ct[wp]: cur_tcb'
  (wp: cur_tcb_lift crunch_wps)

lemma timerTick_invs'[wp]:
  "timerTick \<lbrace>invs'\<rbrace>"
  apply (simp add: timerTick_def)
  apply (wpsimp wp: threadSet_invs_trivial threadSet_pred_tcb_no_state
                    rescheduleRequired_all_invs_but_ct_not_inQ
              simp: tcb_cte_cases_def)
      apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp)
       apply (clarsimp simp: invs'_def valid_state'_def)
      apply (simp add: decDomainTime_def)
      apply wp
     apply simp
     apply wpc
            apply (wp add: threadGet_wp threadSet_cur threadSet_timeslice_invs
                           rescheduleRequired_all_invs_but_ct_not_inQ
                           hoare_vcg_imp_lift threadSet_ct_idle_or_in_cur_domain')+
            apply (rule hoare_strengthen_post[OF tcbSchedAppend_all_invs_but_ct_not_inQ'])
            apply (wpsimp simp: invs'_def valid_state'_def valid_pspace'_def sch_act_wf_weak)+
           apply (rule_tac Q'="\<lambda>_. invs'" in hoare_strengthen_post)
            apply (wpsimp wp: threadSet_pred_tcb_no_state threadSet_tcbDomain_triv
                              threadSet_valid_objs' threadSet_timeslice_invs)+
           apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
          apply (wpsimp simp: invs'_def valid_state'_def valid_pspace'_def sch_act_wf_weak)+
      apply (wp gts_wp')+
  apply (auto simp: invs'_def st_tcb_at'_def obj_at'_def valid_state'_def cong: conj_cong)
  done

lemma resetTimer_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp resetTimer \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq no_irq_resetTimer)
  apply clarsimp
  apply (drule_tac Q="%_ b. underlying_memory b p = underlying_memory m p"
                in use_valid)
    apply (simp add: resetTimer_def
                     machine_op_lift_def machine_rest_lift_def split_def)
    apply wp
   apply clarsimp+
  done

lemma dmo_ackInterrupt[wp]:
"\<lbrace>invs'\<rbrace> doMachineOp (ackInterrupt irq) \<lbrace>\<lambda>y. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq no_irq_ackInterrupt)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: ackInterrupt_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  done

lemma hint_invs[wp]:
  "\<lbrace>invs'\<rbrace> InterruptDecls_H.handleInterrupt irq \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: Interrupt_H.handleInterrupt_def getSlotCap_def
             cong: irqstate.case_cong)
  apply (rule conjI; rule impI)
   apply (wp dmo_maskInterrupt_True getCTE_wp'
          | wpc | simp add: doMachineOp_bind maskIrqSignal_def )+
      apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp)
       apply (clarsimp simp: cte_wp_at_ctes_of ex_nonz_cap_to'_def)
       apply fastforce
      apply (wp threadSet_invs_trivial | simp add: inQ_def handleReservedIRQ_def)+
   apply (wp hoare_post_comb_imp_conj hoare_drop_imp getIRQState_inv)
  apply (assumption)+
  done


crunch timerTick
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (wp: threadSet_pred_tcb_no_state)

end

end
