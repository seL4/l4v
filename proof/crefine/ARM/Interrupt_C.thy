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
                        cte_level_bits_def mult.commute mult.left_commute ucast_nat_def)
  done

lemma ptr_add_assertion_irq_guard:
"ccorres dc xfdc P Q hs a
     (Guard F
       \<lbrace>uint irq = 0 \<or> array_assertion intStateIRQNode_Ptr (nat (uint irq)) (hrs_htd \<acute>t_hrs)\<rbrace>
       c;;m)
  \<Longrightarrow> ccorres dc xfdc P Q hs a
            (Guard F
              \<lbrace>ptr_add_assertion intStateIRQNode_Ptr
                (sint (ucast (irq :: 16 word)::32 signed word)) False
                (hrs_htd \<acute>t_hrs)\<rbrace> c ;; m)"
  by (simp add: ptr_add_assertion_def sint_ucast_eq_uint is_down)

lemma cte_at_irq_node':
  "invs' s \<Longrightarrow>
    cte_at' (irq_node' s + 2 ^ cte_level_bits * ucast (irq :: irq)) s"
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
          apply (simp add: pred_conj_def)+
       apply (strengthen ntfn_badge_derived_enough_strg
                         invs_mdb_strengthen' valid_objs_invs'_strg)
       apply (wp cteDeleteOne_other_cap[unfolded o_def])
      apply vcg
     apply (rule conseqPre, vcg,
            clarsimp simp: rf_sr_def gs_set_assn_Delete_cstate_relation[unfolded o_def])
    apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
    apply wp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                    ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_at_irq_node' ucast_nat_def)
  apply (clarsimp simp: invs_pspace_aligned' cte_wp_at_ctes_of badge_derived'_def
                        Collect_const_mem unat_gt_0 valid_cap_simps')
  apply (drule valid_globals_ex_cte_cap_irq[where irq=irq]; clarsimp)
  apply (unat_arith; simp) (* only word type bounds should be left *)
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
   apply simp
   apply (ctac(no_vcg) add: getIRQSlot_ccorres[simplified])
     apply (rule ccorres_symb_exec_r)
       apply (ctac add: cteDeleteOne_ccorres[where w="-1"])
      apply vcg
     apply (rule conseqPre, vcg,
            clarsimp simp: rf_sr_def gs_set_assn_Delete_cstate_relation[unfolded o_def])
    apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
    apply wp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                    ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_at_irq_node' ucast_nat_def)
  apply (drule word_le_nat_alt[THEN iffD1])
  apply clarsimp
  apply (case_tac "of_int (uint irq) \<noteq> 0 \<longrightarrow> 0 < unat irq")
  by (auto simp: Collect_const_mem unat_eq_0)


lemma ntfn_case_can_send:
  "(case cap of NotificationCap x1 x2 x3 x4 \<Rightarrow> f x3
        | _ \<Rightarrow> v) = (if isNotificationCap cap then f (capNtfnCanSend cap)
                     else v)"
  by (cases cap, simp_all add: isCap_simps)

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
    apply unat_arith (* only word type bounds should be left *)
    apply simp
  apply (auto dest: st_tcb_at_idle_thread' ctes_of_valid')
  done

declare mask_of_mask[simp]

lemma invokeIRQControl_expanded_ccorres:
  "ccorres (\<lambda>_ r. r = scast EXCEPTION_NONE) (ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. ucast irq \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. controlSlot_' s = cte_Ptr parent}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}) hs
      (do x <- setIRQState irqstate.IRQSignal irq;
          cteInsert (capability.IRQHandlerCap irq) parent slot
       od)
      (Call invokeIRQControl_'proc)"
  apply (cinit' lift: irq_' controlSlot_' handlerSlot_')
   apply (ctac add: setIRQState_ccorres)
     apply csymbr
     apply (rule ccorres_add_return2)
     apply (ctac (no_vcg) add: cteInsert_ccorres)
      apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def)
     apply wp+
   apply clarsimp
   apply (vcg exspec=setIRQState_modifies)
  apply (clarsimp simp: is_simple_cap'_def isCap_simps valid_cap_simps' capAligned_def
                        word_bits_def Kernel_C_maxIRQ)
  apply (rule conjI, fastforce)+
  apply (clarsimp simp: Collect_const_mem ccap_relation_def cap_irq_handler_cap_lift
                        cap_to_H_def c_valid_cap_def cl_valid_cap_def irq_len_val ucast_and_mask)
  (* if irq_len < 8, there may be an additional term in the goal *)
  apply (rule conjI, word_eqI_solve)?
  apply (word_eqI_solve dest: bit_imp_le_length)
  done

lemma invokeIRQControl_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. ucast irq \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
                  \<inter> {s. controlSlot_' s = cte_Ptr parent}
                  \<inter> {s. handlerSlot_' s = cte_Ptr slot}) hs
      (performIRQControl (Invocations_H.IssueIRQHandler irq slot parent))
      (Call invokeIRQControl_'proc)"
  unfolding performIRQControl_def
  apply simp
  apply (rule ccorres_liftE)
  apply (rule ccorres_rel_imp)
   apply (rule ccorres_guard_imp)
     apply (rule invokeIRQControl_expanded_ccorres)
    apply assumption
   apply simp+
  done

lemma Arch_invokeIRQControl_ccorres:
  "ccorres ((K (K \<bottom>)) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent and (\<lambda>_. (ucast irq) \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent}
            \<inter> {s. trigger_' s = from_bool trigger}) hs
      (performIRQControl (ArchIRQControl (IssueIRQHandler irq slot parent trigger)))
      (Call Arch_invokeIRQControl_'proc)"
  unfolding ARM_H.performIRQControl_def IRQ_def
  apply (cinit lift: irq_' handlerSlot_' controlSlot_' trigger_'
               simp: ARM_H.performIRQControl_def IRQ_def)
   apply (rule ccorres_liftE)
   apply (ctac (no_vcg) add: setIRQTrigger_ccorres)
     apply (rule ccorres_add_return2)
     apply (ctac (no_vcg) add: invokeIRQControl_expanded_ccorres)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply (wpsimp simp: guard_is_UNIV_def)+
  done

lemma irqstate_to_C_inactive:
  "(irqstate_to_C irq_st = scast Kernel_C.IRQInactive) = (irq_st = irqstate.IRQInactive)"
  by (cases irq_st; simp add: irq_state_defs)

lemma isIRQActive_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
        (\<lambda>s. irq \<le> scast Kernel_C.maxIRQ) \<lbrace>\<acute>irq = ucast irq\<rbrace> []
        (isIRQActive irq) (Call isIRQActive_'proc)"
  apply (cinit lift: irq_')
   apply (simp add: getIRQState_def getInterruptState_def)
   apply (rule_tac P="irq \<le> Kernel_Config.maxIRQ" in ccorres_gen_asm)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: simpler_gets_def)
   apply (rule conjI, solves \<open>clarsimp simp: ucast_irq_array_guard Kernel_C_maxIRQ\<close>)
   apply (clarsimp simp: from_bool_eq_if' cong: if_cong)
   apply (clarsimp simp: rf_sr_def cstate_relation_def  Let_def cinterrupt_relation_def)
   apply (fastforce simp: Kernel_C_maxIRQ irqstate_to_C_inactive)
  apply (simp add: Kernel_C_maxIRQ word_le_nat_alt)
  done

lemma liftME_invocationCatch:
  "liftME f m >>= invocationCatch thread isBlocking isCall f'
     = m >>= invocationCatch thread isBlocking isCall (f' \<circ> f)"
  apply (simp add: liftME_def bindE_def bind_assoc)
  apply (rule bind_cong [OF refl])
  apply (simp add: lift_def throwError_bind invocationCatch_def
                   returnOk_bind
            split: sum.split)
  done

lemma decodeIRQ_arch_helper: "x \<noteq> IRQIssueIRQHandler \<Longrightarrow>
         (case x of IRQIssueIRQHandler \<Rightarrow> f | _ \<Rightarrow> g) = g"
  by (clarsimp split: gen_invocation_labels.splits)

lemma decodeIRQ_arch_helper': "x \<noteq> ArchInvocationLabel ARMIRQIssueIRQHandler \<Longrightarrow>
         (case x of ArchInvocationLabel ARMIRQIssueIRQHandler \<Rightarrow> f | _ \<Rightarrow> g) = g"
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)

lemma Arch_checkIRQ_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>r r'. irq \<le> scast Kernel_C.maxIRQ))
           (liftxf errstate id undefined ret__unsigned_long_')
   \<top> (UNIV \<inter> \<lbrace>irq = \<acute>irq_w\<rbrace>) []
   (checkIRQ irq) (Call Arch_checkIRQ_'proc)"
  apply (cinit lift: irq_w_' )
   apply (simp add: rangeCheck_def unlessE_def ARM.minIRQ_def checkIRQ_def
                    ucast_nat_def word_le_nat_alt[symmetric] Kernel_C_maxIRQ
                    linorder_not_le[symmetric]
                    length_ineq_not_Nil hd_conv_nth cast_simps
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def
                          exception_defs syscall_error_rel_def
                          syscall_error_to_H_cases)
   apply clarsimp
   apply (rule ccorres_return_CE; simp)
  apply (simp add: Kernel_C_maxIRQ)
  done

lemma checkIRQ_ret_good:
  "\<lbrace>\<lambda>s. (irq \<le> Kernel_Config.maxIRQ \<longrightarrow> P s) \<and> Q s\<rbrace> checkIRQ irq \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (wpsimp simp: checkIRQ_def rangeCheck_def minIRQ_def)
  by (clarsimp split: if_split)

lemma Arch_decodeIRQControlInvocation_ccorres:
  notes if_cong[cong]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and sch_act_simple and ct_active'
              and (excaps_in_mem extraCaps o ctes_of)
              and cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v)
              and sysargs_rel args buffer)
       (UNIV
            \<inter> {s. invLabel_' s = label} \<inter> {s. srcSlot_' s = cte_Ptr slot}
            \<inter> {s. unat (length___unsigned_long_' s) = length args}
            \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
            \<inter> {s. buffer_' s = option_to_ptr buffer}) []
     (Arch.decodeIRQControlInvocation label args slot (map fst extraCaps)
        >>= invocationCatch thread isBlocking isCall (InvokeIRQControl o ArchIRQControl))
     (Call Arch_decodeIRQControlInvocation_'proc)"
  apply (cinit' lift: invLabel_' srcSlot_' length___unsigned_long_' current_extra_caps_' buffer_')
   apply (simp add: ARM_H.decodeIRQControlInvocation_def invocation_eq_use_types
               del: Collect_const
               cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: list_case_If2
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
     apply (rule ccorres_cond_true_seq)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: interpret_excaps_test_null excaps_map_def throwError_bind
                      invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null excaps_map_def
                     word_less_nat_alt Let_def
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply csymbr
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply (rule ccorres_add_return)
        apply csymbr
        apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
          apply (rule ccorres_add_return)
          apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=3 and buffer=buffer])
            apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
            apply (rule ccorres_move_c_guard_cte)
            apply ctac
              apply (rule ccorres_assert2)
              apply (simp add: rangeCheck_def unlessE_def ARM.minIRQ_def
                               ucast_nat_def word_le_nat_alt[symmetric]
                               linorder_not_le[symmetric]
                               length_ineq_not_Nil hd_conv_nth cast_simps
                          del: Collect_const cong: call_ignore_cong)
              apply (simp add: split_def invocationCatch_use_injection_handler
                               injection_handler_bindE bindE_assoc
                          del: Collect_const)
              apply (ctac add: ccorres_injection_handler_csum1[OF Arch_checkIRQ_ccorres])
                 apply (simp add: injection_liftE)
                 apply (simp add: liftE_bindE bind_assoc del: Collect_const)
                 apply (ctac add: isIRQActive_ccorres)
                   apply (simp add: from_bool_0 del: Collect_const)
                   apply (rule ccorres_Cond_rhs_Seq)
                    apply (simp add: throwError_bind invocationCatch_def whenE_def
                                     injection_handler_throwError)
                    apply (rule syscall_error_throwError_ccorres_n)
                    apply (simp add: syscall_error_to_H_cases)
                   apply (simp add: split_def invocationCatch_use_injection_handler
                                    injection_handler_bindE bindE_assoc whenE_def
                                    injection_handler_returnOk
                               del: Collect_const)
                   apply (ctac add: ccorres_injection_handler_csum1
                                    [OF lookupTargetSlot_ccorres, unfolded lookupTargetSlot_def])
                      apply (simp add: Collect_False split_def del: Collect_const)
                      apply csymbr
                      apply (ctac add: ccorres_injection_handler_csum1
                                       [OF ensureEmptySlot_ccorres])
                      apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                                       performInvocation_def bindE_assoc)
                      apply (ctac add: setThreadState_ccorres)
                      apply (ctac(no_vcg) add: Arch_invokeIRQControl_ccorres)
                      apply (rule ccorres_alternative2)
                      apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                      apply (wp sts_invs_minor')+
                      apply (simp add: Collect_const_mem)
                      apply (vcg exspec=setThreadState_modifies)
                      apply simp
                      apply (rule ccorres_split_throws)
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                      apply vcg
                      apply simp
                      apply (wp injection_wp_E [OF refl])
                      apply (simp add: Collect_const_mem all_ex_eq_helper)
                      apply (vcg exspec=ensureEmptySlot_modifies)
                     apply simp
                     apply (rule ccorres_split_throws)
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                     apply vcg
                    apply simp
                    apply (wp injection_wp_E[OF refl] hoare_drop_imps)
                   apply (simp add: Collect_const_mem all_ex_eq_helper)
                   apply (vcg exspec=lookupTargetSlot_modifies)
                  apply simp
                  apply (wp hoare_drop_imps isIRQActive_inv)
                 apply (simp add: Collect_const_mem all_ex_eq_helper)
                 apply (vcg exspec=isIRQActive_modifies)
                apply simp
                apply (rule ccorres_split_throws)
                 apply (rule ccorres_return_C_errorE, simp+)[1]
                apply vcg
               apply simp
               apply (wp injection_wp_E[OF refl] checkIRQ_ret_good)
              apply (simp add: Collect_const_mem all_ex_eq_helper)
              apply (vcg exspec=Arch_checkIRQ_modifies)
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
     apply simp
     apply wp
    apply (simp add: Collect_const_mem all_ex_eq_helper)
    apply (vcg exspec=getSyscallArg_modifies)
   apply (clarsimp simp: decodeIRQ_arch_helper')
   apply (simp add: throwError_bind invocationCatch_def)
   apply (rule syscall_error_throwError_ccorres_n)
   apply (simp add: syscall_error_to_H_cases)
  apply (clarsimp simp: interpret_excaps_test_null excaps_map_def
                        Collect_const_mem word_sless_def word_sle_def unat_of_nat mask_def)
  apply (rule conjI)
   apply (simp add: Kernel_C_maxIRQ maxIRQ_ucast_toEnum_eq_irq)
   apply (simp add: word_le_nat_alt ucast_nat_def unat_ucast)
   apply (cut_tac unat_lt2p[where x="args ! 3"])
   apply clarsimp
   apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt unat_ucast)
   apply (auto,
          auto simp: ct_in_state'_def neq_Nil_conv word_bits_def
                     excaps_in_mem_def slotcap_in_mem_def
                     cte_wp_at_ctes_of numeral_eqs[symmetric]
                     valid_tcb_state'_def
               elim!: pred_tcb'_weakenE
               dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[1]
  apply (clarsimp simp: neq_Nil_conv numeral_eqs[symmetric] word_sle_def word_sless_def)
  apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (clarsimp simp: mask_def[where n=4] ThreadState_defs
                        rf_sr_ksCurThread ccap_rights_relation_def
                        rightsFromWord_wordFromRights Kernel_C_maxIRQ maxIRQ_ucast_toEnum_eq_irq)
  apply (simp cong: conj_cong)
  apply (drule le_maxIRQ_machine_less_irqBits_val)
  apply (clarsimp simp: mask_eq_ucast_eq less_mask_eq[unfolded word_less_nat_alt])
  apply (cases "args ! Suc 0 = 0"; clarsimp)
  done

lemma decodeIRQControlInvocation_ccorres:
  notes if_cong[cong]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and sch_act_simple and ct_active'
              and (excaps_in_mem extraCaps o ctes_of)
              and cte_wp_at' (\<lambda>cte. cteCap cte = IRQControlCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v)
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
            apply (simp add: rangeCheck_def unlessE_def ARM.minIRQ_def
                             ucast_nat_def word_le_nat_alt[symmetric]
                             linorder_not_le[symmetric]
                             length_ineq_not_Nil hd_conv_nth cast_simps
                        del: Collect_const cong: call_ignore_cong)
            apply (simp add: split_def invocationCatch_use_injection_handler injection_handler_bindE
                             bindE_assoc
                        del: Collect_const)
            apply (ctac add: ccorres_injection_handler_csum1[OF Arch_checkIRQ_ccorres])
               apply (simp add: injection_liftE)
               apply (simp add: liftE_bindE bind_assoc del: Collect_const)
               apply (ctac add: isIRQActive_ccorres)
                 apply (simp add: from_bool_0 del: Collect_const)
                 apply (rule ccorres_Cond_rhs_Seq)
                  apply (simp add: throwError_bind invocationCatch_def whenE_def
                                   injection_handler_throwError)
                  apply (rule syscall_error_throwError_ccorres_n)
                  apply (simp add: syscall_error_to_H_cases)
                 apply (simp add: split_def invocationCatch_use_injection_handler
                                  injection_handler_bindE bindE_assoc whenE_def
                                  injection_handler_returnOk
                             del: Collect_const)
                 apply (ctac add: ccorres_injection_handler_csum1
                                  [OF lookupTargetSlot_ccorres, unfolded lookupTargetSlot_def])
                    apply (simp add: Collect_False split_def del: Collect_const)
                    apply csymbr
                    apply (ctac add: ccorres_injection_handler_csum1
                                     [OF ensureEmptySlot_ccorres])
                      apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                                       performInvocation_def bindE_assoc)
                      apply (ctac add: setThreadState_ccorres)
                      apply (ctac(no_vcg) add: invokeIRQControl_ccorres)
                      apply (rule ccorres_alternative2)
                      apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                      apply (wp sts_invs_minor')+
                      apply (simp add: Collect_const_mem)
                      apply (vcg exspec=setThreadState_modifies)
                      apply simp
                      apply (rule ccorres_split_throws)
                       apply (rule ccorres_return_C_errorE, simp+)[1]
                      apply vcg
                     apply simp
                     apply (wp injection_wp_E [OF refl])
                    apply (simp add: Collect_const_mem all_ex_eq_helper)
                    apply (vcg exspec=ensureEmptySlot_modifies)
                   apply simp
                   apply (rule ccorres_split_throws)
                    apply (rule ccorres_return_C_errorE, simp+)[1]
                   apply vcg
                  apply simp
                  apply (wp injection_wp_E[OF refl] hoare_drop_imps)
                 apply (simp add: Collect_const_mem all_ex_eq_helper)
                 apply (vcg exspec=lookupTargetSlot_modifies)
                apply simp
                apply (wp hoare_drop_imps isIRQActive_inv)
               apply (simp add: Collect_const_mem all_ex_eq_helper)
               apply (vcg exspec=isIRQActive_modifies)
              apply simp
              apply (rule ccorres_split_throws)
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply vcg
             apply simp
             apply (wp injection_wp_E[OF refl] checkIRQ_ret_good)
            apply (simp add: Collect_const_mem all_ex_eq_helper)
            apply (vcg exspec=Arch_checkIRQ_modifies)
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
                         unat_of_nat mask_def)
  apply (rule conjI)
   apply (simp add: Kernel_C_maxIRQ maxIRQ_ucast_toEnum_eq_irq)
   apply (simp add: Kernel_C_maxIRQ word_le_nat_alt ucast_nat_def
                    unat_ucast)
   apply (cut_tac unat_lt2p[where x="args ! 2"])
   apply clarsimp
   apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt unat_ucast)
   apply (auto,
          auto simp: ct_in_state'_def neq_Nil_conv word_bits_def
                     excaps_in_mem_def slotcap_in_mem_def
                     cte_wp_at_ctes_of numeral_eqs[symmetric]
                     valid_tcb_state'_def
              elim!: pred_tcb'_weakenE
              dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[1]
  apply (clarsimp simp: neq_Nil_conv numeral_eqs[symmetric]
                        word_sle_def word_sless_def)
  apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (clarsimp simp: mask_def[where n=4] ThreadState_defs
                        rf_sr_ksCurThread ccap_rights_relation_def
                        rightsFromWord_wordFromRights
                        Kernel_C_maxIRQ maxIRQ_ucast_toEnum_eq_irq)
  apply (simp cong: conj_cong)
  apply (drule le_maxIRQ_machine_less_irqBits_val)
  apply (clarsimp simp: mask_eq_ucast_eq less_mask_eq[unfolded word_less_nat_alt])
  done

end
end
