(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Interrupt_C
imports CSpace_All Finalise_C
begin

context kernel_m begin

lemma invokeIRQHandler_AckIRQ_ccorres:
  "ccorres dc xfdc
       invs' (UNIV \<inter> {s. irq_' s = ucast irq}) []
     (InterruptDecls_H.invokeIRQHandler (AckIRQ irq)) (Call invokeIRQHandler_AckIRQ_'proc)"
  apply (cinit lift: irq_' simp: Interrupt_H.invokeIRQHandler_def invokeIRQHandler_def)
   apply (ctac add: maskInterrupt_ccorres)
  apply simp
  done

lemma getIRQSlot_ccorres:
  "ccorres ((=) \<circ> Ptr) irqSlot_'
          \<top> UNIV hs
      (getIRQSlot irq)
      (\<acute>irqSlot :== CTypesDefs.ptr_add intStateIRQNode_Ptr (uint irq))"
  apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: getIRQSlot_def liftM_def getInterruptState_def
                        locateSlot_conv)
  apply (simp add: simpler_gets_def bind_def return_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        cinterrupt_relation_def size_of_def
                        sint_ucast_eq_uint is_down of_int_uint_ucast
                        cte_level_bits_def mult.commute mult.left_commute ucast_nat_def
                        )
  done

lemma ptr_add_assertion_irq_guard:
"ccorres dc xfdc P Q hs a
     (Guard F
       \<lbrace>uint irq = 0 \<or> array_assertion intStateIRQNode_Ptr (nat (uint irq)) (hrs_htd \<acute>t_hrs)\<rbrace>
       c;;m)
  \<Longrightarrow> ccorres dc xfdc P Q hs a
            (Guard F
              \<lbrace>ptr_add_assertion intStateIRQNode_Ptr
                (sint (ucast (irq :: 8 word)::32 signed word)) False
                (hrs_htd \<acute>t_hrs)\<rbrace> c ;; m)"
  by (simp add: ptr_add_assertion_def sint_ucast_eq_uint is_down)

lemma cte_at_irq_node':
  "invs' s \<Longrightarrow>
    cte_at' (irq_node' s + 2 ^ cte_level_bits * ucast (irq :: 8 word)) s"
  by (clarsimp simp: invs'_def valid_state'_def valid_irq_node'_def
                     cte_level_bits_def real_cte_at' cteSizeBits_def shiftl_t2n)

lemma invokeIRQHandler_SetIRQHandler_ccorres:
  "ccorres dc xfdc
          (invs' and sch_act_simple
            and irq_handler_inv_valid' (SetIRQHandler irq cp slot))
          (UNIV \<inter> {s. irq_' s = ucast irq} \<inter> {s. slot_' s = Ptr slot}
                \<inter> {s. ccap_relation cp (cap_' s)}) []
      (InterruptDecls_H.invokeIRQHandler (SetIRQHandler irq cp slot))
      (Call invokeIRQHandler_SetIRQHandler_'proc)"
proof -
  have valid_objs_invs'_strg: "\<And>s. invs' s \<longrightarrow> valid_objs' s"
    by (clarsimp)
  show ?thesis
  apply (cinit lift: irq_' slot_' cap_' simp: Interrupt_H.invokeIRQHandler_def)
   apply (rule ccorres_Guard_intStateIRQNode_array_Ptr)
   apply (rule ccorres_move_array_assertion_irq)
   apply (simp)
   apply (ctac(no_vcg) add: getIRQSlot_ccorres[simplified])
     apply (rule ccorres_symb_exec_r)
       apply (ctac(no_vcg) add: cteDeleteOne_ccorres[where w="-1"])
        apply (rule ccorres_call)
           apply (rule cteInsert_ccorres)
          apply simp
         apply simp
        apply simp
       apply (simp add: pred_conj_def)
       apply (strengthen invs_mdb_strengthen' valid_objs_invs'_strg
                         invs_pspace_canonical' invs_pspace_aligned')
       apply (wp cteDeleteOne_other_cap[unfolded o_def])[1]
      apply vcg
     apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
        gs_set_assn_Delete_cstate_relation[unfolded o_def])
    apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
    apply wp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                    ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_at_irq_node' ucast_nat_def)
  apply (clarsimp simp: cte_wp_at_ctes_of badge_derived'_def
                        Collect_const_mem unat_gt_0 valid_cap_simps' X64.maxIRQ_def)
  apply (drule word_le_nat_alt[THEN iffD1])
  apply clarsimp
  apply (drule valid_globals_ex_cte_cap_irq[where irq=irq])
  apply auto
  done
qed

lemma invokeIRQHandler_ClearIRQHandler_ccorres:
  "ccorres dc xfdc
          (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and K(irq \<le> 0xFF))
          (UNIV \<inter> {s. irq_' s = ucast irq}) []
      (InterruptDecls_H.invokeIRQHandler (ClearIRQHandler irq))
      (Call invokeIRQHandler_ClearIRQHandler_'proc)"
  apply (cinit lift: irq_' simp: Interrupt_H.invokeIRQHandler_def)
   apply (rule ccorres_Guard_intStateIRQNode_array_Ptr)
   apply (rule ccorres_move_array_assertion_irq)
   apply (simp add: ucast_up_ucast is_up)
   apply (ctac(no_vcg) add: getIRQSlot_ccorres[simplified])
     apply (rule ccorres_symb_exec_r)
       apply (ctac add: cteDeleteOne_ccorres[where w="-1"])
      apply vcg
     apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
        gs_set_assn_Delete_cstate_relation[unfolded o_def])
    apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
    apply wp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                    ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_at_irq_node' ucast_nat_def)
  apply (drule word_le_nat_alt[THEN iffD1])
  apply (auto simp add:Word.uint_up_ucast)
  apply (case_tac "of_int (uint irq) \<noteq> 0 \<longrightarrow> 0 < unat irq")
   by (auto simp: Collect_const_mem unat_eq_0)


lemma ntfn_case_can_send:
  "(case cap of NotificationCap x1 x2 x3 x4 \<Rightarrow> f x3
        | _ \<Rightarrow> v) = (if isNotificationCap cap then f (capNtfnCanSend cap)
                     else v)"
  by (cases cap, simp_all add: isCap_simps)

lemma list_length_geq_helper[simp]:
  "\<lbrakk>\<not> length args < 2\<rbrakk>
       \<Longrightarrow> \<exists>y ys. args = y # ys"
  by (frule length_ineq_not_Nil(3), simp, metis list.exhaust)

lemma decodeIRQHandlerInvocation_ccorres:
  notes if_cong[cong] gen_invocation_type_eq[simp]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps o ctes_of)
              and (\<lambda>s. \<exists>slot. cte_wp_at' (\<lambda>cte. cteCap cte = IRQHandlerCap irq) slot s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s))
       (UNIV
            \<inter> {s. invLabel_' s = label}
            \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}) []
     (decodeIRQHandlerInvocation label irq extraCaps
            >>= invocationCatch thread isBlocking isCall InvokeIRQHandler)
     (Call decodeIRQHandlerInvocation_'proc)"
  apply (cinit' lift: invLabel_' irq_' current_extra_caps_'
           simp: decodeIRQHandlerInvocation_def invocation_eq_use_types)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: returnOk_bind ccorres_invocationCatch_Inr)
    apply (rule ccorres_rhs_assoc)+
    apply (simp add: performInvocation_def bindE_assoc, simp add: liftE_bindE)
    apply (ctac(no_vcg) add: setThreadState_ccorres)
     apply (ctac(no_vcg) add: invokeIRQHandler_AckIRQ_ccorres)
      apply (simp add: liftE_alternative returnOk_liftE[symmetric])
      apply (rule ccorres_alternative2)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (wp sts_invs_minor')+
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (simp add: list_case_If2 split_def del: Collect_const)
    apply (rule ccorres_if_bind)
    apply (rule ccorres_if_lhs[rotated])
     apply (rule ccorres_cond_false_seq)
     apply (simp add: Let_def split_def ntfn_case_can_send
                 del: Collect_const)
     apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
     apply (rule ccorres_move_c_guard_cte)
     apply (ctac(no_vcg))
       apply (rule ccorres_assert)
       apply (rule_tac P="\<lambda>s. ksCurThread s = thread"
                    in ccorres_cross_over_guard)
       apply (csymbr | rule ccorres_Guard_Seq)+
       apply (simp add: if_1_0_0 cap_get_tag_isCap del: Collect_const)
       apply (rule ccorres_Cond_rhs_Seq)
        apply (simp add: hd_conv_nth del: Collect_const)
        apply (rule ccorres_cond_true_seq)
        apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
         apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: throwError_bind invocationCatch_def)
        apply (simp add: throwError_def return_def)
        apply (simp add: syscall_error_rel_def syscall_error_to_H_cases)
        apply (simp add: exception_defs)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr+
       apply (subgoal_tac "(capNtfnCanSend_CL (cap_notification_cap_lift ntfnCap) = 0)
                              = (\<not> capNtfnCanSend rv)")
        apply (simp add: if_1_0_0 from_bool_0 hd_conv_nth del: Collect_const)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (rule ccorres_split_throws)
          apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: throwError_bind invocationCatch_def)
          apply (simp add: throwError_def return_def)
          apply (simp add: syscall_error_rel_def syscall_error_to_H_cases)
          apply (simp add: exception_defs)
         apply vcg
        apply (simp add: hd_conv_nth liftE_bindE returnOk_bind
                         invocationCatch_def performInvocation_def
                         bind_assoc bind_bindE_assoc excaps_map_def
                    del: Collect_const)
        apply (ctac(no_vcg) add: setThreadState_ccorres)
         apply (ctac(no_vcg) add: invokeIRQHandler_SetIRQHandler_ccorres)
          apply (simp add: liftE_alternative returnOk_liftE[symmetric])
          apply (rule ccorres_alternative2)
          apply (rule ccorres_return_CE, simp+)[1]
         apply (wp sts_invs_minor' hoare_vcg_ex_lift
                     | simp)+
       apply (clarsimp simp: cap_get_tag_isCap[symmetric]
                      dest!: cap_get_tag_to_H)
       apply (simp add: to_bool_def)
      apply simp
      apply (simp add: getSlotCap_def)
      apply (wp getCTE_wp)
     apply (clarsimp simp: Collect_const_mem neq_Nil_conv
                    dest!: interpret_excaps_eq)
     apply (simp add: rf_sr_ksCurThread if_1_0_0 mask_def[where n=4]
                      ThreadState_defs cap_get_tag_isCap excaps_map_def
                      word_sless_def word_sle_def)
    apply (simp add: invocationCatch_def throwError_bind
                     interpret_excaps_test_null Collect_True
                     excaps_map_def
                del: Collect_const
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocationCatch_def performInvocation_def
                     returnOk_bind liftE_bindE bind_assoc
                     bind_bindE_assoc bind_assoc)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac(no_vcg) add: setThreadState_ccorres)
     apply (ctac(no_vcg) add: invokeIRQHandler_ClearIRQHandler_ccorres)
      apply (simp add: liftE_alternative returnOk_liftE[symmetric])
      apply (rule ccorres_alternative2)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (wp sts_invs_minor')+
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: invocationCatch_def throwError_bind
                      split: gen_invocation_labels.split)
    apply (simp add: ccorres_cond_iffs cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply simp
  apply (clarsimp simp: Collect_const_mem tcb_at_invs')
  apply (clarsimp simp: invs_valid_objs'
                        ct_in_state'_def
                        ccap_rights_relation_def
                        mask_def[where n=4] ThreadState_defs)
  apply (subst pred_tcb'_weakenE, assumption, fastforce)+
  apply (clarsimp simp: rf_sr_ksCurThread word_sle_def word_sless_def
    sysargs_rel_n_def word_less_nat_alt)
  apply (clarsimp simp: cte_wp_at_ctes_of neq_Nil_conv sysargs_rel_def n_msgRegisters_def
                    excaps_map_def excaps_in_mem_def word_less_nat_alt hd_conv_nth
                    slotcap_in_mem_def valid_tcb_state'_def
             dest!: interpret_excaps_eq split: bool.splits)
  apply (intro conjI impI allI)
  apply (clarsimp simp: cte_wp_at_ctes_of neq_Nil_conv sysargs_rel_def n_msgRegisters_def
                    excaps_map_def excaps_in_mem_def word_less_nat_alt hd_conv_nth
                    slotcap_in_mem_def valid_tcb_state'_def
             dest!: interpret_excaps_eq split: bool.splits)+
     apply (auto dest: st_tcb_at_idle_thread' ctes_of_valid')[6]
    apply (drule ctes_of_valid')
     apply fastforce
    apply (clarsimp simp add:valid_cap_simps' X64.maxIRQ_def)
    apply (erule order.trans,simp)
  apply (auto dest: st_tcb_at_idle_thread' ctes_of_valid')
  done

declare mask_of_mask[simp]

lemma ucast_maxIRQ_le_eq:
  "UCAST(8 \<rightarrow> 64) irq \<le> SCAST(32 signed \<rightarrow> 64) Kernel_C.maxIRQ \<Longrightarrow>
          irq \<le> SCAST(32 signed \<rightarrow> 8) Kernel_C.maxIRQ"
  apply (subst ucast_le_ucast_8_64[symmetric])
  by (clarsimp simp: ucast_up_ucast is_up Kernel_C.maxIRQ_def)

lemma ucast_maxIRQ_le_eq':
  "UCAST(8 \<rightarrow> 64) irq \<le> SCAST(32 signed \<rightarrow> 64) Kernel_C.maxIRQ \<Longrightarrow> irq \<le> maxIRQ"
  apply (clarsimp simp: Kernel_C.maxIRQ_def maxIRQ_def)
  by word_bitwise

lemma invokeIRQControl_expanded_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. (ucast irq) \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = (ucast irq :: machine_word)}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent})
      hs
      (do y <- setIRQState irqstate.IRQSignal irq;
          liftE (cteInsert (capability.IRQHandlerCap irq) parent slot)
       od)
      (Call invokeIRQControl_'proc)"
  apply (cinit' lift: irq_' handlerSlot_' controlSlot_')
   apply (ctac add: setIRQState_ccorres)
     apply csymbr
     apply (rule ccorres_add_returnOk)
     apply (simp only: liftE_bindE)
     apply (ctac add: cteInsert_ccorres)
       apply (rule ccorres_return_CE)
         apply clarsimp+
      apply wp
     apply (vcg exspec=cteInsert_modifies)
    apply wp
   apply (vcg exspec=setIRQState_modifies)
  apply (rule conjI)
   apply (clarsimp simp: is_simple_cap'_def isCap_simps valid_cap_simps' capAligned_def)
   apply (clarsimp simp: Kernel_C.maxIRQ_def maxIRQ_def word_bits_def)
   apply (subgoal_tac "UCAST(8 \<rightarrow> 64) irq \<le> UCAST(8 \<rightarrow> 64) 0x7D \<and> LENGTH(8) \<le> LENGTH(64)")
    apply (erule conjE)
    apply (drule_tac x="irq" and y="0x7D" in ucast_le_ucast)
    apply (fastforce simp: word_bits_def)
   apply simp
  apply (clarsimp simp: Collect_const_mem ccap_relation_def cap_irq_handler_cap_lift
                        cap_to_H_def c_valid_cap_def cl_valid_cap_def
                        word_bw_assocs mask_twice Kernel_C.maxIRQ_def ucast_ucast_a
                        is_up ucast_ucast_b is_down)
  apply (subst less_mask_eq)
   apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD1])
    apply simp
   apply (erule order.trans, simp)
  apply simp
  apply (simp add: mask_def)
  apply word_bitwise
  done

lemma invokeIRQControl_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. (ucast irq) \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent}) []
      (performIRQControl (IssueIRQHandler irq slot parent))
      (Call invokeIRQControl_'proc)"
  by (clarsimp simp: performIRQControl_def liftE_def bind_assoc
               intro!: invokeIRQControl_expanded_ccorres[simplified liftE_def, simplified])

lemma isIRQActive_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
        (\<lambda>s. irq \<le> scast Kernel_C.maxIRQ) (UNIV \<inter> {s. irq_' s = ucast irq}) []
        (isIRQActive irq) (Call isIRQActive_'proc)"
  apply (cinit lift: irq_')
   apply (simp add: getIRQState_def getInterruptState_def)
   apply (rule_tac P="irq \<le> ucast Kernel_C.maxIRQ \<and> unat irq < (126::nat)" in ccorres_gen_asm)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: simpler_gets_def word_sless_msb_less maxIRQ_def
                         word_less_nat_alt)
   apply (clarsimp simp: order_le_less_trans unat_less_helper Kernel_C.IRQInactive_def
                         Kernel_C.maxIRQ_def word_0_sle_from_less[OF order_less_le_trans, OF ucast_less])
   apply (clarsimp simp: rf_sr_def cstate_relation_def Kernel_C.maxIRQ_def
                         Let_def cinterrupt_relation_def)
   apply (drule spec, drule(1) mp)
   apply (case_tac "intStateIRQTable (ksInterruptState \<sigma>) irq")
      apply (simp add: irq_state_defs Kernel_C.maxIRQ_def word_le_nat_alt)+
  done

lemma Platform_maxIRQ:
  "X64.maxIRQ = scast Kernel_C.maxIRQ"
   by (simp add: X64.maxIRQ_def Kernel_C.maxIRQ_def)

lemma le_maxirq_ucast_explicit:
  "irq \<le> 0x7D \<Longrightarrow> UCAST(8 \<rightarrow> 64) irq < 0x7E"
  apply (subgoal_tac "UCAST(8 \<rightarrow> 64) irq \<le> UCAST(8 \<rightarrow> 64) 0x7D \<and> LENGTH(8) \<le> LENGTH(64)")
   apply (erule conjE)
   apply (drule_tac x="irq" and y="0x7D" in ucast_le_ucast)
   apply word_bitwise
  apply (rule conjI)
   apply (rule ucast_up_mono_le)
   by auto

lemma updateIRQState_ccorres:
  "x64_irq_state_relation irq_state_h irq_state_c \<Longrightarrow>
   ccorres dc xfdc
      (\<top> and (\<lambda>s. irq \<le> SCAST(32 signed \<rightarrow> 8) Kernel_C.maxIRQ))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. state_' s = irq_state_c})
      hs
      (updateIRQState irq irq_state_h)
      (Call updateIRQState_'proc)"
  apply (rule ccorres_gen_asm)
  apply cinit
   apply (rule ccorres_symb_exec_l)
      apply (rule_tac P="\<lambda>s. irqStates = x64KSIRQState (ksArchState s)"
                  and P'= "(UNIV \<inter> {s. irq_' s = ucast irq}
                                 \<inter> {s. state_' s = irq_state_c})"
                   in ccorres_from_vcg)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: simpler_modify_def
                            rf_sr_def cstate_relation_def Let_def
                            carch_state_relation_def cmachine_state_relation_def carch_globals_def
                            Kernel_C.maxIRQ_def le_maxirq_ucast_explicit)
      apply (erule array_relation_update[simplified fun_upd_def]; fastforce simp: maxIRQ_def)
     apply wpsimp+
  done

lemma Arch_invokeIRQControl_ccorres:
  "x64_irq_state_relation (X64IRQIOAPIC ioapic pin level polarity True) irq_state_c \<Longrightarrow>
   ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. ucast irq \<le> (scast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent}
            \<inter> {s. irqState___struct_x86_irq_state_C_' s = irq_state_c})
      hs
      (do y <- updateIRQState irq (X64IRQIOAPIC ioapic pin level polarity True);
          y <- setIRQState irqstate.IRQSignal irq;
          liftE (cteInsert (capability.IRQHandlerCap irq) parent slot)
       od)
      (Call Arch_invokeIRQControl_'proc)"
  apply (cinit' lift: irq_' handlerSlot_' controlSlot_' irqState___struct_x86_irq_state_C_')
   apply (ctac (no_vcg) add: updateIRQState_ccorres)
    apply (rule ccorres_add_returnOk)
    apply (ctac add: invokeIRQControl_expanded_ccorres)
       apply (ctac add: ccorres_return_CE)
      apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
     apply wp
    apply (vcg exspec=invokeIRQControl_modifies)
   apply wp
  (* 0x7D = maxIRQ *)
  apply (fastforce simp: Kernel_C.maxIRQ_def maxIRQ_def ucast_le_ucast_8_64[where y="0x7D", simplified])
  done

lemma invokeIssueIRQHandlerMSI_ccorres:
  "x64_irq_state_relation
     (X64IRQMSI (pciBus && mask 8) (pciDev && mask 5) (pciFunc && mask 3) (handle && mask 32))
     irq_state_c \<Longrightarrow>
   ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. ucast irq \<le> (scast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent}
            \<inter> {s. irqState___struct_x86_irq_state_C_' s = irq_state_c})
      []
      (performIRQControl (ArchIRQControl (IssueIRQHandlerMSI irq slot parent pciBus pciDev pciFunc handle)))
      (Call Arch_invokeIRQControl_'proc)"
  apply (cinit' lift: irq_' handlerSlot_' controlSlot_' irqState___struct_x86_irq_state_C_')
   apply (clarsimp simp: performIRQControl_def X64_H.performIRQControl_def liftE_def bind_assoc)
   apply (ctac (no_vcg) add: updateIRQState_ccorres)
    apply (rule ccorres_add_returnOk)
    apply (ctac add: invokeIRQControl_expanded_ccorres[simplified liftE_def, simplified])
       apply (ctac add: ccorres_return_CE)
      apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
     apply wp
    apply (vcg exspec=invokeIRQControl_modifies)
   apply wp
  (* 0x7D = maxIRQ *)
  apply (fastforce simp: IRQ_def Kernel_C.maxIRQ_def maxIRQ_def ucast_le_ucast_8_64[where y="0x7D", simplified])
  done

lemma ucast_ucast_mask_le_64_32:
  "n \<le> 32 \<Longrightarrow> UCAST (32 \<rightarrow> 64) (UCAST (64 \<rightarrow> 32) x && mask n) = x && mask n"
  by (simp add: ucast_and_mask[symmetric], word_bitwise, clarsimp)

lemmas x64_irq_state_relation_helpers =
  ucast_ucast_mask_le_64_32
  ucast_ucast_mask_le_64_32[where n=1, simplified]

lemma invokeIssueIRQHandlerIOAPIC_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. (ucast irq) \<le> (scast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. ioapic___unsigned_long_' s = ioapic}
            \<inter> {s. pin___unsigned_long_' s = pin}
            \<inter> {s. level___unsigned_long_' s = level}
            \<inter> {s. polarity_' s = polarity}
            \<inter> {s. vector___unsigned_long_' s = vector}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent})
      []
      (performIRQControl (ArchIRQControl (IssueIRQHandlerIOAPIC irq slot parent ioapic pin level polarity vector)))
      (Call invokeIssueIRQHandlerIOAPIC_'proc)"
  apply (cinit lift: irq_' ioapic___unsigned_long_'
                     pin___unsigned_long_' level___unsigned_long_' polarity_'
                     vector___unsigned_long_' handlerSlot_' controlSlot_'
               simp: ArchInterrupt_H.X64_H.performIRQControl_def IRQ_def)
   apply clarsimp
   apply csymbr
   apply (simp add: bind_liftE_distrib liftE_bindE)
   apply (ctac (no_vcg) add: ioapicMapPinToVector_ccorres)
    apply clarsimp
    apply (rule ccorres_add_returnOk)
    apply (subgoal_tac "x64_irq_state_relation (X64IRQIOAPIC (ioapic && mask 5) (pin && mask 5) (level && 1) (polarity && 1) True)
                                               irqState___struct_x86_irq_state_C")
     prefer 2
     apply (fastforce simp: x64_irq_state_relation_def x86_irq_state_irq_ioapic_lift x64_irq_state_relation_helpers)
    apply (ctac add: Arch_invokeIRQControl_ccorres)
       apply (ctac add: ccorres_return_CE)
      apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
     apply wp
    apply (vcg exspec=Arch_invokeIRQControl_modifies)
   apply wp
  apply clarsimp
  done

lemma ccorres_pre_gets_x64KSNumIOAPICs_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. x64KSNumIOAPICs (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. s \<in> P' rv }
                          hs (gets (x64KSNumIOAPICs \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply clarsimp
  done

lemma ccorres_pre_gets_x64KSIOAPICnIRQs_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                   (\<lambda>s. (\<forall>rv. x64KSIOAPICnIRQs (ksArchState s) = rv  \<longrightarrow> P rv s))
                   {s. \<forall>rv. s \<in> P' rv } hs
                   (gets (x64KSIOAPICnIRQs \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply clarsimp
  done

lemma rf_sr_x64KSIOAPICnIRQs:
  "\<lbrakk> (s,s') \<in> rf_sr; i < of_nat maxNumIOAPIC \<rbrakk> \<Longrightarrow>
   ioapic_nirqs_' (globals s').[unat i] = x64KSIOAPICnIRQs (ksArchState s) i"
  by (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def Let_def
                     array_relation_def)

lemma ioapic_decode_map_pin_to_vector_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc)
     (liftxf errstate id (K ()) ret__unsigned_long_')
     valid_ioapic
     (\<lbrace>\<acute>ioapic___unsigned_long = ioapic\<rbrace> \<inter>
      \<lbrace>\<acute>pin___unsigned_long = pin\<rbrace> \<inter>
      \<lbrace>\<acute>level___unsigned_long = level\<rbrace> \<inter>
      \<lbrace>\<acute>polarity = polarity\<rbrace>)
     hs
     (doE numIOAPICs <- liftE (gets (x64KSNumIOAPICs \<circ> ksArchState));
          ioapic_nirqs <- liftE (gets (x64KSIOAPICnIRQs \<circ> ksArchState));
          whenE (numIOAPICs = 0) (throwError (Inl IllegalOperation));
          whenE (uint (numIOAPICs - 1) < uint ioapic)
                (throwError (Inl (RangeError 0 (numIOAPICs - 1))));
          whenE (uint (ucast (ioapic_nirqs ioapic - 1) :: machine_word) < uint pin)
                (throwError (Inl (RangeError 0 (ucast (ioapic_nirqs ioapic - 1)))));
          whenE (1 < uint level) (throwError (Inl (RangeError 0 1)));
          whenE (1 < uint polarity) (throwError (Inl (RangeError 0 1)))
       odE)
     (Call ioapic_decode_map_pin_to_vector_'proc)"
  supply Collect_const[simp del] word_less_1[simp del] (* for uniform array guard on ioapic_nirqs *)
  apply (cinit' lift: ioapic___unsigned_long_' pin___unsigned_long_' level___unsigned_long_'
                      polarity_')
   apply (simp add: ioapicIRQLines_def cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (clarsimp simp: liftE_bindE)
   apply (rule ccorres_pre_gets_x64KSNumIOAPICs_ksArchState)
   apply (rule ccorres_pre_gets_x64KSIOAPICnIRQs_ksArchState)
   apply (rule_tac Q="\<lambda>s. x64KSNumIOAPICs (ksArchState s) = numIOAPICs" and Q'=\<top>
                   in ccorres_split_when_throwError_cond)
      apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def Let_def)
      apply (fastforce simp: up_ucast_inj_eq[where y=0, simplified ucast_0])
     apply (fastforce simp: syscall_error_to_H_cases intro: syscall_error_throwError_ccorres_n)
    apply (rule_tac Q="\<lambda>s. x64KSNumIOAPICs (ksArchState s) = numIOAPICs" and Q'=\<top>
                    in ccorres_split_when_throwError_cond)
       apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def Let_def)
       apply (fastforce simp: word_less_alt[symmetric])
      (* Need to VCG it as the range error depends on num_ioapics_' from the global state *)
      apply (rule_tac P="\<lambda>s. numIOAPICs = x64KSNumIOAPICs (ksArchState s)"
                  and P'="UNIV" in ccorres_from_vcg_throws)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: fst_throwError_returnOk syscall_error_to_H_cases
                            EXCEPTION_SYSCALL_ERROR_def EXCEPTION_NONE_def syscall_error_rel_def)
      apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def Let_def)
      apply (subst ucast_sub_ucast; fastforce simp: lt1_neq0)
     apply (rule_tac P="numIOAPICs \<le> of_nat maxNumIOAPIC" in ccorres_gen_asm)
     apply (clarsimp simp: not_less word_le_def[symmetric])
     apply (prop_tac "ioapic < of_nat maxNumIOAPIC",
            solves \<open>simp add: le_m1_iff_lt[THEN iffD1] word_neq_0_conv\<close>)
     apply (rule ccorres_prove_guard)
      (* array guard where array dimension is maxNumIOAPIC *)
      apply (solves \<open>simp add: Kernel_Config.maxNumIOAPIC_def\<close>)
     apply ccorres_rewrite
     apply (rename_tac ioapic_nirqs)
     apply (rule_tac Q="\<lambda>s. ioapic_nirqs = x64KSIOAPICnIRQs (ksArchState s) \<and>
                            0 < x64KSIOAPICnIRQs (ksArchState s) ioapic" and
                     Q'=\<top>
                     in ccorres_split_when_throwError_cond)
        apply (fastforce simp: word_le_def scast_ucast_up_eq_ucast uint_up_ucast is_up
                               rf_sr_x64KSIOAPICnIRQs
                               uint_minus_1_less_le_eq)
      (* Need to VCG it as the range error depends on the global state *)
      apply (rule_tac P="\<lambda>s. ioapic_nirqs = x64KSIOAPICnIRQs (ksArchState s) \<and>
                             numIOAPICs \<le> of_nat maxNumIOAPIC \<and>
                             0 < x64KSIOAPICnIRQs (ksArchState s) ioapic \<and>
                             x64KSIOAPICnIRQs (ksArchState s) ioapic \<le> ucast ioapicIRQLines"
                  and P'="UNIV" in ccorres_from_vcg_throws)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: fst_throwError_returnOk syscall_error_to_H_cases
                            EXCEPTION_SYSCALL_ERROR_def EXCEPTION_NONE_def syscall_error_rel_def)
      apply (simp add: rf_sr_x64KSIOAPICnIRQs
                       scast_ucast_up_eq_ucast ioapicIRQLines_def sint_ucast_eq_uint is_down
                       scast_ucast_up_minus_1_ucast)
      apply (rule conjI, uint_arith)
      apply (rule conjI, uint_arith)
      (* array guard where array dimension is maxNumIOAPIC *)
      apply (solves \<open>simp add: Kernel_Config.maxNumIOAPIC_def\<close>)
     apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_split_when_throwError_cond)
        apply clarsimp
        apply (metis arith_special(21) diff_eq_diff_eq uint_1 word_less_def word_less_sub1
                     word_neq_0_conv word_sub_less_iff)
       apply (fastforce simp: syscall_error_to_H_cases intro: syscall_error_throwError_ccorres_n)
      apply (rule_tac Q=\<top> and Q'=\<top>
                      in ccorres_split_when_throwError_cond[where b="returnOk ()", simplified])
         apply clarsimp
         apply (metis arith_special(21) diff_eq_diff_eq uint_1 word_less_def word_less_sub1
                      word_neq_0_conv word_sub_less_iff)
        apply (fastforce simp: syscall_error_to_H_cases intro: syscall_error_throwError_ccorres_n)
       apply (ctac add: ccorres_return_CE)
      apply vcg+
  apply (clarsimp simp: not_less)
  apply (prop_tac "ioapic < x64KSNumIOAPICs (ksArchState s)")
   apply (meson word_leq_minus_one_le word_less_eq_iff_unsigned)
  apply (fastforce simp: valid_ioapic_def)
  done

(* Bundle of definitions for minIRQ, maxIRQ, minUserIRQ, etc *)
lemmas c_irq_const_defs = irq_const_defs irq_user_min_def irq_user_max_def

lemma Arch_decodeIRQControlInvocation_ccorres:
  assumes "interpret_excaps extraCaps' = excaps_map extraCaps"
  shows   "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. ksCurThread s = thread)
            and sch_act_simple and ct_active'
            and (excaps_in_mem extraCaps o ctes_of)
            and (\<lambda>s. \<forall>v \<in> set extraCaps.
                           s \<turnstile>' fst v \<and> cte_at' (snd v) s)
            and (\<lambda>s. \<forall>v \<in> set extraCaps.
                           ex_cte_cap_wp_to' isCNodeCap (snd v) s)
            and cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) srcSlot
            and sysargs_rel args buffer)
     (UNIV \<inter> {s. invLabel_' s = label}
           \<inter> {s. unat (length___unsigned_long_' s) = length args}
           \<inter> {s. srcSlot_' s = cte_Ptr srcSlot}
           \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
           \<inter> {s. buffer_' s = option_to_ptr buffer})
     []
     (Arch.decodeIRQControlInvocation label args srcSlot (map fst extraCaps)
        >>= invocationCatch thread isBlocking isCall (InvokeIRQControl o ArchIRQControl))
     (Call Arch_decodeIRQControlInvocation_'proc)"
     (is "ccorres _ _ ?pre _ _ _ _")
  proof -
  (* We begin with a collection of word proofs that should only be relevant to this lemma *)
  have irq64_toEnum_plus_unat:
    "\<And>irq. unat (irq :: 8 word) \<le> 107 \<Longrightarrow> toEnum (16 + unat irq) = irq + 0x10"
    apply (subst toEnum_of_nat)
     apply auto
    done
  have irq64_helper_one:
    "\<And>irq. (irq :: 64 word) \<le> 107 \<Longrightarrow> of_nat (unat irq) \<le> (0x6B :: 8 word)"
    apply (subst ucast_nat_def)
    apply (subgoal_tac "UCAST(64 \<rightarrow> 8) irq \<le> UCAST(64 \<rightarrow> 8) 0x6B")
     apply simp
    apply (rule ucast_mono_le')
     apply simp+
    done
  have irq64_helper_two:
    "\<And>irq. unat irq \<le> 107 \<Longrightarrow>
            UCAST(8 \<rightarrow> 64) (toEnum (16 + unat (UCAST(64 \<rightarrow> 8) irq))) \<le>
            SCAST(32 signed \<rightarrow> 64) Kernel_C.maxIRQ"
    apply (subst irq64_toEnum_plus_unat)
     apply (subst ucast_nat_def[symmetric])
     apply (subst unat_of_nat)
     apply simp
    supply Word.of_nat_unat[simp del]
    apply (simp flip: ucast_nat_def)
    apply (subgoal_tac "of_nat (unat irq + 0x10) = of_nat (unat irq) + 0x10")
     apply (erule subst)
     apply (subst unat_of_nat)
     apply (simp add: scast_def Kernel_C.maxIRQ_def)
     apply (subgoal_tac "irq \<le> 107")
      defer
      defer
      apply simp
     apply (subst add.commute)
     apply (rule Word.le_plus)
      apply (rule_tac y="0x6B" in xtrans(6))
       apply simp
      apply simp
     apply simp
    apply (subgoal_tac "unat irq \<le> unat (0x6B :: 64 word)")
     apply (subst word_le_nat_alt, simp)
    apply simp
    done
  have irq64_helper_three:
    "\<And>irq. \<not> 107 < unat irq \<Longrightarrow>
        toEnum (16 + unat (UCAST(64 \<rightarrow> 8) irq)) \<le> SCAST(32 signed \<rightarrow> 8) Kernel_C.maxIRQ"
    supply Word.of_nat_unat[simp del]
    apply (subst toEnum_of_nat)
     apply (simp add: unat_ucast)
    apply (simp add: unat_ucast Kernel_C.maxIRQ_def)
    apply (subgoal_tac "unat irq \<le> 107")
     apply simp
     apply (rule Word.le_plus)
      apply (rule_tac y="0x6B" in xtrans(6))
       apply simp
      defer
      apply simp
     apply simp
    apply (subgoal_tac "unat irq \<le> unat (0x6B :: 64 word)")
     apply (subst word_le_nat_alt, simp)
     apply (subst unat_of_nat)
     apply simp
    apply simp
    done
  have irq64_helper_four:
    "\<And>irq. \<not> 107 < unat irq \<Longrightarrow>
       irq + 0x10 =
       UCAST(8 \<rightarrow> 64) (toEnum (16 + unat (UCAST(64 \<rightarrow> 8) irq)))"
    supply Word.of_nat_unat[simp del]
    apply (subgoal_tac "unat irq \<le> 107")
     defer
     apply simp
    apply simp
    apply (subst irq64_toEnum_plus_unat)
     apply (simp add: unat_ucast)
    apply (simp add: ucast_nat_def[symmetric])
    apply (subgoal_tac "of_nat (unat irq + 0x10) = of_nat (unat irq) + 0x10")
     defer
     apply simp
    apply (erule subst)
    apply (subst unat_of_nat)
    apply simp
    done
  have irq64_helper_five:
    "\<And>irq. \<not> 107 < unat irq \<Longrightarrow>
           0x30 + irq =
           of_nat (unat ((toEnum :: nat \<Rightarrow> 8 word) (16 + unat (UCAST(64 \<rightarrow> 8) irq)))) + 0x20"
    apply (subst ucast_nat_def)
    apply simp
    apply (subst add.commute)
    apply (simp add: irq64_helper_four)
    done
from assms show ?thesis
  supply Collect_const[simp del]
  apply (cinit' lift: invLabel_' length___unsigned_long_' srcSlot_' current_extra_caps_' buffer_'
                simp: ArchInterrupt_H.X64_H.decodeIRQControlInvocation_def)
   apply (simp add: throwError_bind
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    apply ccorres_rewrite
    apply (auto split: invocation_label.split arch_invocation_label.split
                intro: syscall_error_throwError_ccorres_n[simplified throwError_def o_def]
                simp: throwError_def invocationCatch_def syscall_error_to_H_cases invocation_eq_use_types)[1]
   apply clarsimp
   apply (rule ccorres_rhs_assoc2)
   apply (rule_tac val="of_bool (length args < 7 \<or> extraCaps = [])" and
                   xf'=ret__int_' and
                   R=\<top> and
                   R'=UNIV in
                   ccorres_symb_exec_r_known_rv_UNIV)
      apply vcg
      apply ((clarsimp simp: interpret_excaps_test_null excaps_map_def | unat_arith)+)[1]
     apply ceqv
    apply (clarsimp simp: of_bool_def)
    apply (rule ccorres_Cond_rhs_Seq)
     apply ccorres_rewrite
     (* Insufficient args *)
     apply (erule ccorres_disj_division[where P="length args < 7"])
      apply (erule ccorres_disj_division;
             clarsimp split: invocation_label.split simp: invocation_eq_use_types)
       apply (auto split: list.split
                   intro: syscall_error_throwError_ccorres_n[simplified throwError_def o_def]
                   simp: throwError_def invocationCatch_def syscall_error_to_H_cases)[2]
     (* Insufficient extra caps *)
     apply (erule ccorres_disj_division;
            clarsimp split: invocation_label.split simp: invocation_eq_use_types)
      apply (auto split: list.split
                  intro: syscall_error_throwError_ccorres_n[simplified throwError_def o_def]
                  simp: throwError_def invocationCatch_def syscall_error_to_H_cases)[2]
    (* Arguments OK *)
    apply ccorres_rewrite
    apply (clarsimp simp: not_less val_le_length_Cons neq_Nil_conv
                    cong: invocation_label.case_cong arch_invocation_label.case_cong)
    apply (rule ccorres_add_return,
           ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
      apply (rule ccorres_add_return,
             ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=1])
        apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
        apply (ctac (no_vcg) add: ccorres_move_c_guard_cte)
          apply (rule ccorres_assert)
          apply (rule ccorres_add_return,
                 ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=6])
            apply (rule ccorres_move_const_guards)
            apply clarsimp
            apply (rule ccorres_Cond_rhs_Seq)
             (* Error case *)
             apply ccorres_rewrite
             apply (erule ccorres_disj_division;
                    clarsimp split: list.split simp: invocation_eq_use_types)
              apply (((auto simp: rangeCheck_def unlessE_whenE
                                  c_irq_const_defs word_less_alt
                                  word_sless_alt is_down sint_ucast_eq_uint word_le_not_less
                                  invocationCatch_use_injection_handler injection_handler_throwError
                                  syscall_error_to_H_cases
                            intro: syscall_error_throwError_ccorres_n) |
                       ccorres_rewrite)+)[2]
            apply (erule ccorres_disj_division; clarsimp simp: invocation_eq_use_types)
             (* X64IRQIssueIRQHandlerIOAPIC *)
             apply (clarsimp simp: rangeCheck_def unlessE_whenE c_irq_const_defs word_less_alt
                                   word_sless_alt is_down sint_ucast_eq_uint word_le_not_less)
             apply csymbr
             apply (clarsimp simp: scast_down_add is_down scast_ucast_simps)
             apply (clarsimp simp: Orderings.linorder_class.not_less)
             apply (simp add: invocationCatch_use_injection_handler
                              bindE_assoc
                              injection_bindE[OF refl refl]
                              injection_liftE[OF refl]
                         cong: call_ignore_cong)
             apply (clarsimp simp: liftE_bindE[where a="isIRQActive _"])
             apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
             apply (ctac add: isIRQActive_ccorres)
               apply (simp add: injection_handler_whenE injection_handler_throwError)
               apply (rule ccorres_split_when_throwError_cond[where Q=\<top> and Q'=\<top>])
                  apply clarsimp
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (fastforce simp: syscall_error_to_H_cases)
                apply csymbr
                apply (ctac add: ccorres_injection_handler_csum1
                                        [OF lookupTargetSlot_ccorres,
                                            unfolded lookupTargetSlot_def])
                   prefer 2
                   apply ccorres_rewrite
                   apply (ctac add: ccorres_return_C_errorE)
                  apply ccorres_rewrite
                  apply csymbr
                  apply clarsimp
                  apply (ctac add: ccorres_injection_handler_csum1[OF ensureEmptySlot_ccorres])
                     prefer 2
                     apply ccorres_rewrite
                     apply (ctac add: ccorres_return_C_errorE)
                    apply ccorres_rewrite
                    apply (rule ccorres_rhs_assoc)+
                    apply (rule ccorres_add_return,
                           ctac add: getSyscallArg_ccorres_foo
                                       [where args=args and buffer=buffer and n=2])
                      apply (rule ccorres_add_return,
                             ctac add: getSyscallArg_ccorres_foo
                                         [where args=args and buffer=buffer and n=3])
                        apply (rule ccorres_add_return,
                               ctac add: getSyscallArg_ccorres_foo
                                           [where args=args and buffer=buffer and n=4])
                          apply (rule ccorres_add_return,
                                 ctac add: getSyscallArg_ccorres_foo
                                             [where args=args and buffer=buffer and n=5])
                            (* Re-associate the Haskell so it corresponds to the C function *)
                            apply (clarsimp
                                     simp: bindE_assoc[symmetric,
                                             where g="\<lambda>_. injection_handler P Q >>=E R" for P Q R])
                            apply (clarsimp simp: injection_handler_returnOk)
                            apply (simp only: bindE_K_bind)
                            apply (ctac add: ioapic_decode_map_pin_to_vector_ccorres)
                               apply ccorres_rewrite
                               apply (simp add: ccorres_invocationCatch_Inr performInvocation_def
                                                returnOk_bind liftE_bindE bindE_assoc
                                                bind_bindE_assoc)
                               apply (ctac (no_vcg) add: setThreadState_ccorres)
                                apply (ctac add: invokeIssueIRQHandlerIOAPIC_ccorres)
                                   apply (clarsimp simp: liftE_alternative)
                                   apply (rule ccorres_alternative2)
                                   apply (ctac add: ccorres_return_CE)
                                  apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
                                 apply wp
                                apply (vcg exspec=invokeIssueIRQHandlerIOAPIC_modifies)
                               apply (wp sts_invs_minor')
                              apply ccorres_rewrite
                              apply (ctac add: ccorres_return_C_errorE)
                             apply wp
                            apply (vcg exspec=ioapic_decode_map_pin_to_vector_modifies)
                           apply clarsimp
                           apply wp
                          apply (vcg exspec=getSyscallArg_modifies)
                         apply (clarsimp, wp)
                        apply (vcg exspec=getSyscallArg_modifies)
                       apply (clarsimp, wp)
                      apply (vcg exspec=getSyscallArg_modifies)
                     apply (clarsimp, wp)
                    apply (vcg exspec=getSyscallArg_modifies)
                   apply (wpsimp wp: injection_wp_E[where f=Inl])
                  apply (vcg exspec=ensureEmptySlot_modifies)
                 apply (wpsimp wp: injection_wp_E[where f=Inl] hoare_drop_imps)
                apply (vcg exspec=lookupTargetSlot_modifies)
               apply vcg
              apply clarsimp
              apply (rule hoare_weaken_pre[where P="?pre"])
               apply (rule isIRQActive_wp)
              apply (clarsimp simp: sysargs_rel_to_n unat_less_2p_word_bits
                                    invs_valid_objs' tcb_at_invs' valid_tcb_state'_def
                                    invs_sch_act_wf' ct_in_state'_def cte_wp_at_weakenE'
                                    pred_tcb'_weakenE invs_pspace_aligned' invs_pspace_distinct')
              apply (subst pred_tcb'_weakenE, assumption, fastforce)+
              apply (rule conjI, fastforce)
              apply clarsimp
              apply (rule_tac irq1="yf" in irq64_helper_two)
              apply (simp only: unat_def)
             apply (vcg exspec=isIRQActive_modifies)
            (* X64IRQIssueIRQHandlerMSI *)
            (* Much of the proof below is copied from the IOAPIC case above \<up> *)
            apply (clarsimp simp: rangeCheck_def unlessE_whenE c_irq_const_defs word_less_alt
                                  word_sless_alt is_down sint_ucast_eq_uint word_le_not_less)
            apply csymbr
            apply (clarsimp simp: scast_down_add is_down scast_ucast_simps)
            apply (clarsimp simp: Orderings.linorder_class.not_less)
            apply (simp add: invocationCatch_use_injection_handler
                             bindE_assoc
                             injection_bindE[OF refl refl]
                             injection_liftE[OF refl]
                        cong: call_ignore_cong)
            apply (clarsimp simp: liftE_bindE[where a="isIRQActive _"])
            apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
            apply (ctac add: isIRQActive_ccorres)
              apply (simp add: injection_handler_whenE injection_handler_throwError)
              apply (rule ccorres_split_when_throwError_cond[where Q=\<top> and Q'=\<top>])
                 apply clarsimp
                apply (rule syscall_error_throwError_ccorres_n)
                apply (fastforce simp: syscall_error_to_H_cases)
               apply csymbr
               apply (ctac add: ccorres_injection_handler_csum1
                                      [OF lookupTargetSlot_ccorres,
                                          unfolded lookupTargetSlot_def])
                  prefer 2
                  apply ccorres_rewrite
                  apply (ctac add: ccorres_return_C_errorE)
                 apply ccorres_rewrite
                 apply csymbr
                 apply clarsimp
                 apply (ctac add: ccorres_injection_handler_csum1[OF ensureEmptySlot_ccorres])
                    prefer 2
                    apply ccorres_rewrite
                    apply (ctac add: ccorres_return_C_errorE)
                   apply ccorres_rewrite
                   apply (rule ccorres_rhs_assoc)+
                   apply (rule ccorres_add_return,
                          ctac add: getSyscallArg_ccorres_foo
                                      [where args=args and buffer=buffer and n=2])
                     apply (rule ccorres_add_return,
                            ctac add: getSyscallArg_ccorres_foo
                                        [where args=args and buffer=buffer and n=3])
                       apply (rule ccorres_add_return,
                              ctac add: getSyscallArg_ccorres_foo
                                          [where args=args and buffer=buffer and n=4])
                         apply (rule ccorres_add_return,
                                ctac add: getSyscallArg_ccorres_foo
                                            [where args=args and buffer=buffer and n=5])
                           (* Proof diverges from IOAPIC case here *)
                           apply csymbr
                           apply (clarsimp simp: maxPCIBus_def maxPCIDev_def maxPCIFunc_def)
                           (* Handle the conditional checks on PCI bus/dev/func *)
                           apply ((rule_tac Q=\<top> and Q'=\<top> in ccorres_split_when_throwError_cond,
                                   fastforce,
                                   rule syscall_error_throwError_ccorres_n,
                                   fastforce simp: syscall_error_to_H_cases)+)[3]
                              apply ccorres_rewrite
                              apply csymbr
                              apply (rename_tac irq_state_struct)
                              apply (simp add: injection_handler_returnOk returnOk_bind
                                               ccorres_invocationCatch_Inr performInvocation_def
                                               liftE_bindE bindE_assoc bind_bindE_assoc)
                              apply (ctac (no_vcg) add: setThreadState_ccorres)
                               apply clarsimp
                               (* Set up for invokeIssueIRQHandlerMSI_ccorres *)
                               apply (subgoal_tac "x64_irq_state_relation
                                                    (X64IRQMSI ((args ! 2) && mask 8)
                                                               ((args ! 3) && mask 5)
                                                               ((args ! 4) && mask 3)
                                                               ((args ! 5) && mask 32))
                                                    irq_state_struct")
                                prefer 2
                                apply (fastforce simp: x64_irq_state_relation_def
                                                       x86_irq_state_irq_msi_lift
                                                       x64_irq_state_relation_helpers)
                               apply (ctac add: invokeIssueIRQHandlerMSI_ccorres)
                                  apply (clarsimp simp: liftE_alternative)
                                  apply (rule ccorres_alternative2)
                                  apply (ctac add: ccorres_return_CE)
                                 apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
                                apply wp
                               apply (vcg exspec=Arch_invokeIRQControl_modifies)
                              apply (wp sts_invs_minor')
                             apply vcg+
                          apply (rule hoare_weaken_pre[where P="?pre"])
                           apply wp
                          apply (clarsimp simp: invs_valid_objs' tcb_at_invs'
                                                valid_tcb_state'_def invs_pspace_aligned'
                                                invs_sch_act_wf' ct_in_state'_def
                                                cte_wp_at_weakenE' invs_pspace_distinct')
                          apply (subst pred_tcb'_weakenE, assumption, fastforce)+
                          apply (intro conjI impI)
                            apply (rule TrueI)+
                          apply (rule_tac irq1="yf" in irq64_helper_two)
                          apply (simp only: unat_def)
                         apply (vcg exspec=getSyscallArg_modifies, wp)
                       apply (vcg exspec=getSyscallArg_modifies, wp)
                     apply (vcg exspec=getSyscallArg_modifies, wp)
                   apply (vcg exspec=getSyscallArg_modifies, wp)
                  apply (wpsimp wp: injection_wp_E[where f=Inl])
                 apply (vcg exspec=ensureEmptySlot_modifies)
                apply (wpsimp wp: injection_wp_E[where f=Inl] hoare_drop_imps)
               apply (vcg exspec=lookupTargetSlot_modifies)
              apply vcg
             apply (wp isIRQActive_wp)
            apply (vcg exspec=isIRQActive_modifies)
           apply wp
          apply (vcg exspec=getSyscallArg_modifies)
         apply (rule hoare_weaken_pre[where P="?pre"])
          apply (wpsimp wp: getSlotCap_wp)
         (* Defer the pure goals about the state so we can hit them with the auto hammer below *)
         defer
         defer
         apply wp
        apply (vcg exspec=getSyscallArg_modifies)
       apply wp
      apply (vcg exspec=getSyscallArg_modifies)
     apply clarsimp
     apply (fastforce simp: guard_is_UNIV_def interpret_excaps_eq excaps_map_def
                      split: Product_Type.prod.split)
    apply (auto simp: invs_valid_objs' ct_in_state'_def irqIntOffset_def
                      ccap_rights_relation_def mask_def[where n=4]
                      ThreadState_defs rf_sr_ksCurThread cte_wp_at_ctes_of
                      sysargs_rel_def sysargs_rel_n_def
                      excaps_map_def excaps_in_mem_def slotcap_in_mem_def
                      valid_tcb_state'_def word_less_nat_alt
                      c_irq_const_defs irq64_helper_one irq64_helper_two irq64_helper_three
                      irq64_helper_four irq64_helper_five
                      unat_less_2p_word_bits word_less_alt word_sless_alt is_down sint_ucast_eq_uint
                dest!: interpret_excaps_eq
                split: bool.splits Product_Type.prod.split)[3]
  done
  qed

lemma liftME_invocationCatch:
  "liftME f m >>= invocationCatch thread isBlocking isCall f'
     = m >>= invocationCatch thread isBlocking isCall (f' \<circ> f)"
  apply (simp add: liftME_def bindE_def bind_assoc)
  apply (rule bind_cong [OF refl])
  apply (simp add: lift_def throwError_bind invocationCatch_def
                   returnOk_bind
            split: sum.split)
  done

lemma maxIRQ_ucast_scast [simp]:
  "ucast (scast Kernel_C.maxIRQ :: 8 word) = scast Kernel_C.maxIRQ"
  by (clarsimp simp: Kernel_C.maxIRQ_def)

lemma decodeIRQ_arch_helper: "x \<noteq> IRQIssueIRQHandler \<Longrightarrow>
         (case x of IRQIssueIRQHandler \<Rightarrow> f | _ \<Rightarrow> g) = g"
  by (clarsimp split: gen_invocation_labels.splits)

lemma Arch_checkIRQ_ccorres:
  "ccorres (syscall_error_rel \<currency> dc) (liftxf errstate id undefined ret__unsigned_long_')
   \<top> UNIV []
   (checkIRQ irq) (Call Arch_checkIRQ_'proc)"
  apply (cinit lift:)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre)
    apply vcg
   apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                         syscall_error_to_H_cases exception_defs)
  apply clarsimp
  done

(* FIXME x64: no possibility of non-error case for checkIRQ *)
lemma checkIRQ_wp:
  "\<lbrace>\<lambda>s. Q s\<rbrace> checkIRQ irq \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. Q\<rbrace>"
  by (simp add: checkIRQ_def) wpsimp

(* FIXME x64: this could change when Arch_checkIRQ definition changes *)
lemma decodeIRQControlInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and sch_act_simple and ct_active'
              and (excaps_in_mem extraCaps o ctes_of)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v \<and> cte_at' (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. invLabel_' s = label} \<inter> {s. srcSlot_' s = cte_Ptr slot}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (decodeIRQControlInvocation label args slot (map fst extraCaps)
            >>= invocationCatch thread isBlocking isCall InvokeIRQControl)
     (Call decodeIRQControlInvocation_'proc)"
  supply gen_invocation_type_eq[simp]
  apply (cinit' lift: invLabel_' srcSlot_' length___unsigned_long_' current_extra_caps_' buffer_')
   apply (simp add: decodeIRQControlInvocation_def invocation_eq_use_types
               del: Collect_const
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: list_case_If2
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: word_less_nat_alt if_1_0_0
                      throwError_bind invocationCatch_def)
     apply (rule ccorres_cond_true_seq)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: interpret_excaps_test_null if_1_0_0 excaps_map_def
                      throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null if_1_0_0 excaps_map_def
                     word_less_nat_alt Let_def
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply csymbr
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply (rule ccorres_add_return)
        apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
          apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
          apply (rule ccorres_move_c_guard_cte)
          apply ctac
            apply (rule ccorres_assert2)
            apply (simp add: rangeCheck_def unlessE_def X64.minIRQ_def
                             ucast_nat_def word_le_nat_alt[symmetric]
                             linorder_not_le[symmetric] Platform_maxIRQ
                             length_ineq_not_Nil hd_conv_nth cast_simps
                             maxIRQ_ucast_scast
                        del: Collect_const cong: call_ignore_cong)
            apply (simp add: split_def invocationCatch_use_injection_handler injection_handler_bindE
                             bindE_assoc
                        del: Collect_const)
            apply (ctac add: ccorres_injection_handler_csum1[OF Arch_checkIRQ_ccorres])
               apply (simp add: injection_liftE)
               (* checkIRQ is guaranteed to throw on x86-64 so everything following it is never executed *)
               apply (rule ccorres_False[where P'=UNIV])
              apply (rule ccorres_split_throws)
               apply clarsimp
               apply ccorres_rewrite
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply vcg
             apply (wp injection_wp_E[OF refl] checkIRQ_wp)
            apply (simp add: Collect_const_mem all_ex_eq_helper)
            apply (vcg)
           apply (wp hoare_vcg_const_imp_lift |wp (once) hoare_drop_imps)+
          apply (simp add: Collect_const_mem all_ex_eq_helper)
          apply vcg
         apply wp
        apply (simp add: Collect_const_mem all_ex_eq_helper)
        apply (vcg exspec=getSyscallArg_modifies)
       apply simp
       apply wp
      apply (simp add: Collect_const_mem all_ex_eq_helper)
      apply (vcg exspec=getSyscallArg_modifies)
     apply simp
     apply wp
    apply (simp add: Collect_const_mem all_ex_eq_helper)
    apply (vcg exspec=getSyscallArg_modifies)
   apply (clarsimp simp: decodeIRQ_arch_helper)
   apply (simp add: liftME_invocationCatch)
   apply (rule ccorres_add_returnOk)
   apply (ctac add: Arch_decodeIRQControlInvocation_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (vcg exspec=Arch_decodeIRQControlInvocation_modifies)
  apply (simp add: syscall_error_to_H_cases)
  apply (clarsimp simp: interpret_excaps_test_null excaps_map_def
                        Collect_const_mem word_sless_def word_sle_def
                  cong: if_cong)
  apply (rule conjI)
   apply (cut_tac unat_lt2p[where x="args ! 2"])
   apply clarsimp
   apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt unat_ucast)
   apply (auto simp: ct_in_state'_def neq_Nil_conv word_bits_def
                     excaps_in_mem_def slotcap_in_mem_def
                     cte_wp_at_ctes_of numeral_eqs[symmetric]
                     valid_tcb_state'_def
              elim!: pred_tcb'_weakenE cte_wp_at_weakenE'
              dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[1]
  apply (clarsimp simp: neq_Nil_conv numeral_eqs[symmetric]
                        word_sle_def word_sless_def)
  apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (clarsimp simp: rf_sr_ksCurThread ccap_rights_relation_def rightsFromWord_wordFromRights)
  done
end
end
