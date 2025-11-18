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
  apply (cinit lift: irq_' simp: Interrupt_H.invokeIRQHandler_def invokeIRQHandler_def dmo_if)
   apply csymbr (* make config_set(CONFIG_ARM_GIC_V3_SUPPORT) available *)
   apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
     apply (simp add: Kernel_Config.config_ARM_GIC_V3_def) (* match C condition *)
    apply (ctac add: deactivateInterrupt_ccorres)
   apply (ctac add: maskInterrupt_ccorres)
  apply (simp add: theIRQ_def)
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
    cte_at' (irq_node' s + 2 ^ cte_level_bits * ucast (irq :: irq_len word)) s"
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
                        Collect_const_mem unat_gt_0 valid_cap_simps')
  apply (drule word_le_nat_alt[THEN iffD1])
  apply clarsimp
  apply (drule valid_globals_ex_cte_cap_irq[where irq=irq])
    apply auto[2]
  apply clarsimp
  by (unat_arith; simp) (* only word type bounds should be left *)
qed

lemma invokeIRQHandler_ClearIRQHandler_ccorres:
  "ccorres dc xfdc
          (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
          \<lbrace>\<acute>irq = ucast irq\<rbrace> []
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
     apply (rule conseqPre, vcg,
            clarsimp simp: rf_sr_def gs_set_assn_Delete_cstate_relation[unfolded o_def])
    apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
    apply wp
   apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                    ghost_assertion_data_set_def)
  apply (clarsimp simp: cte_at_irq_node' ucast_nat_def)
  apply (unat_arith, auto) (* only word type bounds should be left *)
  done

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
       apply (simp add: cap_get_tag_isCap del: Collect_const)
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
        apply (simp add: from_bool_0 hd_conv_nth del: Collect_const)
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
     apply (simp add: rf_sr_ksCurThread mask_def[where n=4]
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
                     returnOk_bind liftE_bindE bind_assoc bind_bindE_assoc)
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
    apply (auto dest: st_tcb_at_idle_thread' ctes_of_valid')
  done

declare mask_of_mask[simp]

lemma invokeIRQControl_expanded_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent
       and (\<lambda>_. (ucast irq) \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
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
  apply (clarsimp simp: is_simple_cap'_def isCap_simps valid_cap_simps' capAligned_def)
  apply (rule conjI, fastforce simp: word_bits_def)+
  apply (rule conjI)
   apply (clarsimp simp: word_le_nat_alt Kernel_C_maxIRQ)
  apply (clarsimp simp: Collect_const_mem ccap_relation_def cap_irq_handler_cap_lift
                        cap_to_H_def c_valid_cap_def cl_valid_cap_def irq_len_val
                        word_bw_assocs Kernel_C_maxIRQ ucast_and_mask_drop)
  done

lemma invokeIRQControl_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent
       and (\<lambda>_. (ucast irq) \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent}) []
      (performIRQControl (Invocations_H.irqcontrol_invocation.IssueIRQHandler irq slot parent))
      (Call invokeIRQControl_'proc)"
  by (clarsimp simp: performIRQControl_def liftE_def bind_assoc
               intro!: invokeIRQControl_expanded_ccorres[simplified liftE_def, simplified])

lemma Arch_invokeIRQControl_IssueIRQHandler_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' parent
       and (\<lambda>_. ucast irq \<le> (scast Kernel_C.maxIRQ :: machine_word)))
      (UNIV \<inter> {s. irq_' s = ucast irq}
            \<inter> {s. handlerSlot_' s = cte_Ptr slot}
            \<inter> {s. controlSlot_' s = cte_Ptr parent}
            \<inter> {s. trigger_' s = from_bool trigger}
            )
      hs
      (Arch.performIRQControl (IssueIRQHandler irq slot parent trigger))
      (Call Arch_invokeIRQControl_'proc)"
  apply (cinit' lift: irq_' handlerSlot_' controlSlot_' trigger_')
   apply (clarsimp simp: AARCH64_H.performIRQControl_def simp flip: liftE_liftE)
   apply (rule ccorres_liftE_Seq)
   apply csymbr (* HAVE_SET_TRIGGER *)
   apply simp (* assume HAVE_SET_TRIGGER to be 1 for AArch64 platforms *)
   apply (ctac (no_vcg) add: setIRQTrigger_ccorres)
    apply (rule ccorres_liftE_Seq)
    apply (rule ccorres_add_returnOk)
    apply (ctac add: invokeIRQControl_expanded_ccorres)
       apply (ctac add: ccorres_return_CE)
      apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
     apply wp
    apply (vcg exspec=invokeIRQControl_modifies)
   apply wpsimp
  apply (clarsimp simp: Kernel_C_maxIRQ IRQ_def word_le_nat_alt)
  done

lemma sgi_target_valid_sgi_target_len:
  "isSGITargetValid w = (w \<le> mask sgi_target_len)"
  by (simp add: isSGITargetValid_def gicNumTargets_def sgi_target_len_def mask_def)

(* 32 is from width of field in bitfield generator for sgi target. *)
lemma sgi_target_len_le_32:
  "sgi_target_len \<le> 32"
  by (simp add: sgi_target_len_val)

lemma Arch_invokeIRQControl_IssueSGISignal_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and cte_at' controlSlot and K (isSGITargetValid target \<and> irq < of_nat numSGIs))
      (\<lbrace>\<acute>irq = irq\<rbrace> \<inter> \<lbrace>\<acute>target___unsigned_long = target\<rbrace> \<inter>
       \<lbrace>\<acute>controlSlot = cte_Ptr controlSlot\<rbrace> \<inter> \<lbrace>\<acute>sgiSlot = cte_Ptr sgiSlot\<rbrace>)
      hs
      (Arch.performIRQControl (IssueSGISignal irq target controlSlot sgiSlot))
      (Call Arch_invokeIssueSGISignal_'proc)"
  apply (cinit' lift: irq_' target___unsigned_long_' controlSlot_' sgiSlot_')
   apply (clarsimp simp: AARCH64_H.performIRQControl_def liftE_def)
   apply csymbr
   apply (ctac (no_vcg) add: cteInsert_ccorres)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (clarsimp, rule conseqPre, vcg)
    apply (clarsimp simp: return_def)
   apply wp
  apply (clarsimp split: if_split)
  apply (clarsimp simp: is_simple_cap'_def isCap_simps valid_cap_simps' capAligned_def)
  apply (rule conjI, fastforce)+
  apply clarsimp
  apply (erule notE)
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_lift_def
                        cap_sgi_signal_cap_lift_def Let_def cap_tag_defs cap_to_H_def
                        sgi_target_valid_sgi_target_len numSGIs_def)
  apply (rule conjI; rule le_mask_imp_and_mask[symmetric])
   apply (simp add: numSGIs_bits_def mask_def word_le_nat_alt word_less_nat_alt)
  apply (erule order_trans, rule mask_le_mono)
  apply (rule sgi_target_len_le_32)
  done

(* Bundle of definitions for minIRQ, maxIRQ, minUserIRQ, etc *)
lemmas c_irq_const_defs = irq_const_defs

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

lemma checkIRQ_wpE:
  "\<lbrace> \<lambda>s. irq \<le> ucast maxIRQ \<longrightarrow> P () s \<rbrace> checkIRQ irq \<lbrace>P\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  unfolding checkIRQ_def rangeCheck_def
  by (wpsimp simp: minIRQ_def irqInvalid_def not_le word_le_nat_alt split: if_split)

lemma toEnum_unat_irq_t_leq_scast:
  "x \<le> ucast maxIRQ \<Longrightarrow> (toEnum (unat x)::irq) \<le> scast Kernel_C.maxIRQ" for x::machine_word
  apply (simp add: Kernel_C_maxIRQ word_le_nat_alt)
  apply (subst toEnum_unat_ucast)
   apply (erule le_less_trans)
   apply (rule maxIRQ_less_2p_irq_len)
  apply (simp add: unat_ucast)
  done

lemma ucast_toEnum_unat_irq_t_leq_ucast:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow>
   UCAST(_ \<rightarrow> machine_word_len) (toEnum (unat x)::irq) \<le> ucast Kernel_C.maxIRQ"
  for x::machine_word
  by (simp add: Kernel_C_maxIRQ maxIRQ_ucast_toEnum_eq_irq ucast_ucast_mask word_and_le)

lemma ucast_toEnum_unat_irq_t_leq_scast:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow>
   UCAST(_ \<rightarrow> machine_word_len) (toEnum (unat x)::irq) \<le> scast Kernel_C.maxIRQ"
  for x::machine_word
  by (simp add: Kernel_C_maxIRQ maxIRQ_ucast_toEnum_eq_irq ucast_ucast_mask word_and_le)

lemmas maxIRQ_casts = toEnum_unat_irq_t_leq_scast ucast_toEnum_unat_irq_t_leq_ucast
                      maxIRQ_ucast_toEnum_eq_machine ucast_toEnum_unat_irq_t_leq_scast

lemma plat_SGITargetValid_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       Call plat_SGITargetValid_'proc
       { t. ret__unsigned_long_' t = from_bool (isSGITargetValid (target___unsigned_long_' s)) }"
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply (simp add: isSGITargetValid_def gicNumTargets_def sgi_target_len_val
              flip: sgi_target_len_def
              split: if_split)
  done

lemma Arch_decodeIRQControlInvocation_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
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
  supply maxIRQ_casts[simp]
  supply gen_invocation_type_eq[simp] if_cong[cong] Collect_const[simp del]
  apply (cinit' lift: invLabel_' length___unsigned_long_' srcSlot_' current_extra_caps_' buffer_'
                simp: ArchInterrupt_H.AARCH64_H.decodeIRQControlInvocation_def)
   apply (simp add: invocation_eq_use_types
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: list_case_If2 cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
     apply (rule ccorres_cond_true_seq)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: interpret_excaps_test_null excaps_map_def
                      throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply ccorres_rewrite
    apply csymbr (* !config_set(HAVE_SET_TRIGGER) *)
    apply ccorres_rewrite
    apply (simp add: interpret_excaps_test_null excaps_map_def
                     word_less_nat_alt Let_def
                cong: call_ignore_cong)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply csymbr
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply csymbr
        apply (rule ccorres_add_return)
        apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
          apply (rule ccorres_add_return)
          apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=3 and buffer=buffer])
            apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
            apply (rule ccorres_move_c_guard_cte)
            apply ctac
              apply (rule ccorres_assert2)
              apply (simp add: rangeCheck_def unlessE_def AARCH64.minIRQ_def
                               ucast_nat_def word_le_nat_alt[symmetric]
                               linorder_not_le[symmetric]
                               length_ineq_not_Nil hd_conv_nth
                          cong: call_ignore_cong ccorres_prog_only_cong)
              apply (simp add: split_def invocationCatch_use_injection_handler injection_handler_bindE
                               bindE_assoc
                          cong: call_ignore_cong ccorres_prog_only_cong)
              apply (ctac add: ccorres_injection_handler_csum1[OF Arch_checkIRQ_ccorres])
                 apply (simp add: injection_liftE liftE_bindE)
                 apply ccorres_rewrite
                 apply (ctac add: isIRQActive_ccorres)
                   apply (simp only: injection_handler_whenE injection_handler_throwError)
                   apply (rule ccorres_split_when_throwError_cond[where Q=\<top> and Q'=\<top>])
                      apply simp
                     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                     apply (rule allI, rule conseqPre, vcg)
                     apply (clarsimp simp: throwError_def return_def exception_defs
                                           syscall_error_rel_def syscall_error_to_H_def
                                           syscall_error_type_defs)
                    apply (ctac add: ccorres_injection_handler_csum1
                                            [OF lookupTargetSlot_ccorres,
                                                unfolded lookupTargetSlot_def])
                       prefer 2
                       apply ccorres_rewrite
                       apply (ctac add: ccorres_return_C_errorE)
                      apply ccorres_rewrite
                      apply csymbr
                      apply (ctac add: ccorres_injection_handler_csum1[OF ensureEmptySlot_ccorres])
                         prefer 2
                         apply ccorres_rewrite
                         apply (ctac add: ccorres_return_C_errorE)
                        apply ccorres_rewrite
                        apply (simp add: ccorres_invocationCatch_Inr performInvocation_def
                                         liftE_bindE bindE_assoc injection_handler_returnOk
                                    cong: ccorres_prog_only_cong)
                        apply (ctac (no_vcg) add: setThreadState_ccorres)
                         apply (simp add: performIRQControl_def)
                         apply (ctac add: Arch_invokeIRQControl_IssueIRQHandler_ccorres)
                            apply (clarsimp simp: liftE_alternative)
                            apply (rule ccorres_alternative2)
                            apply (ctac add: ccorres_return_CE)
                           apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
                          apply wp
                         apply (vcg exspec=invokeIRQControl_modifies)
                        apply (wp sts_invs_minor')
                       apply (rule injection_wp, rule refl, wp)
                      apply simp
                      apply vcg
                     apply (rule injection_wp, rule refl)
                     apply clarsimp
                     apply (wp hoare_drop_imps)
                    apply simp
                    apply (vcg exspec=lookupTargetSlot_modifies)
                   apply vcg
                  apply simp
                  apply (wp isIRQActive_wp)
                 apply simp
                 apply (vcg exspec=isIRQActive_modifies)
                apply ccorres_rewrite
                apply (ctac add: ccorres_return_C_errorE)
               apply (rule injection_wp, rule refl)
               apply simp
               apply (wp checkIRQ_wpE)
              apply (rule_tac P'="\<lbrace> \<acute>ksCurThread = tcb_ptr_to_ctcb_ptr thread\<rbrace>" in conseqPre)
               apply (prop_tac "\<forall>x::machine_word. \<not> scast Kernel_C.maxIRQ < x
                                                    \<longrightarrow> x = ucast (toEnum (unat x)::irq)")
                apply (clarsimp simp: Kernel_C_maxIRQ not_less word_le_nat_alt)
                apply (subst toEnum_unat_ucast)
                 apply (erule le_less_trans)
                 apply (rule maxIRQ_less_2p_irq_len)
                apply (subst ucast_ucast_len)
                 apply (rule le_less_trans[where y=Kernel_Config.maxIRQ])
                  apply (simp add: word_le_nat_alt)
                 apply (simp add: word_less_nat_alt maxIRQ_less_2p_irq_len[simplified])
                apply (rule refl)
               apply (clarsimp simp: numeral_2_eq_2 numeral_3_eq_3 exception_defs
                                     ThreadState_defs mask_def)
               apply (rule conseqPre, vcg)
               apply (fastforce simp: exception_defs split: if_split)
              apply (rule subset_refl)
             apply simp
             apply (wp getSlotCap_wp)
            apply vcg
           apply wp
          apply (vcg exspec=getSyscallArg_modifies)
         apply clarsimp
         apply wp
        apply (vcg exspec=getSyscallArg_modifies)
       apply (clarsimp, wp)
      apply (vcg exspec=getSyscallArg_modifies)
     apply (clarsimp, wp)
    apply (vcg exspec=getSyscallArg_modifies)
   apply ccorres_rewrite
   apply (rule ccorres_Cond_rhs)
    apply (simp add: list_case_If2 cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
     apply (rule ccorres_cond_true_seq)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: interpret_excaps_test_null excaps_map_def
                      throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (prop_tac "args \<noteq> []", solves \<open>clarsimp simp: word_less_nat_alt\<close>)
    apply (simp add: interpret_excaps_test_null excaps_map_def
                     word_less_nat_alt Let_def
                cong: call_ignore_cong)
    apply csymbr (* NUM_SGIS *)
    apply ccorres_rewrite (* assume NUM_SGIs always \<noteq> 0 on AArch64 *)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply (rule ccorres_add_return)
        apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
          apply (rule ccorres_add_return)
          apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=3 and buffer=buffer])
            apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
            apply (rule ccorres_move_c_guard_cte)
            apply ctac
              apply csymbr (* wrap NUM_SGIS; assume \<noteq> 0 on AArch64 *)
              apply (rule ccorres_assert2)
              apply (simp add: rangeCheck_def unlessE_def
                               length_ineq_not_Nil hd_conv_nth
                          cong: call_ignore_cong ccorres_prog_only_cong)
              apply (rule ccorres_Cond_rhs_Seq)
               apply (prop_tac "\<not> args!0 \<le> of_nat (numSGIs - Suc 0)")
                apply (solves \<open>clarsimp simp: numSGIs_def numSGIs_bits_def word_le_nat_alt\<close>)
               apply (simp add: throwError_bind invocationCatch_def
                           cong: call_ignore_cong ccorres_prog_only_cong)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases numSGIs_def numSGIs_bits_def)
              apply (prop_tac "args!0 \<le> of_nat (numSGIs - Suc 0)")
               apply (solves \<open>clarsimp simp: numSGIs_def numSGIs_bits_def word_le_nat_alt\<close>)
              apply (simp cong: call_ignore_cong ccorres_prog_only_cong)
              apply csymbr
              apply (simp cong: call_ignore_cong ccorres_prog_only_cong)
              apply (rule ccorres_Cond_rhs_Seq)
               apply (simp add: throwError_bind invocationCatch_def from_bool_0
                           cong: call_ignore_cong ccorres_prog_only_cong)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases
                                mask_def)
              apply (simp add: invocationCatch_use_injection_handler injection_handler_bindE
                               bindE_assoc
                          cong: call_ignore_cong ccorres_prog_only_cong)
              apply (ctac add: ccorres_injection_handler_csum1[OF lookupTargetSlot_ccorres,
                                                               unfolded lookupTargetSlot_def])
                 prefer 2
                 apply ccorres_rewrite
                 apply (ctac add: ccorres_return_C_errorE)
                apply ccorres_rewrite
                apply csymbr
                apply (ctac add: ccorres_injection_handler_csum1[OF ensureEmptySlot_ccorres])
                   prefer 2
                   apply ccorres_rewrite
                   apply (ctac add: ccorres_return_C_errorE)
                  apply ccorres_rewrite
                  apply (simp add: ccorres_invocationCatch_Inr performInvocation_def
                                   liftE_bindE bindE_assoc injection_handler_returnOk
                              cong: ccorres_prog_only_cong)
                  apply (ctac (no_vcg) add: setThreadState_ccorres)
                   apply (simp add: performIRQControl_def)
                   apply (ctac (no_vcg) add: Arch_invokeIRQControl_IssueSGISignal_ccorres)
                     apply (clarsimp simp: liftE_alternative)
                     apply (rule ccorres_alternative2)
                     apply (ctac add: ccorres_return_CE)
                    apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
                   apply wp
                  apply (wp sts_invs_minor')
                 apply clarsimp
                 apply (wp injection_handler_wp)
                apply (rule conseqPre, vcg exspec=ensureEmptySlot_modifies, rule order_refl)
               apply (wp injection_handler_wp hoare_drop_imps)
              apply clarsimp
              apply (rule conseqPre, vcg exspec=lookupTargetSlot_modifies, rule order_refl)
             apply (wpsimp wp: getSlotCap_wp)
            apply clarsimp
            apply (rule conseqPre, vcg, rule order_refl)
           apply wp
          apply (rule conseqPre, vcg exspec=getSyscallArg_modifies, rule order_refl)
         apply clarsimp
         apply wp
        apply (rule conseqPre, vcg exspec=getSyscallArg_modifies, rule order_refl)
       apply clarsimp
       apply wp
      apply (rule conseqPre, vcg exspec=getSyscallArg_modifies, rule order_refl)
     apply clarsimp
     apply wp
    apply clarsimp
    apply (rule conseqPre, vcg exspec=getSyscallArg_modifies, rule order_refl)
   apply ccorres_rewrite
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply (auto split: invocation_label.split arch_invocation_label.split
               intro: syscall_error_throwError_ccorres_n[simplified throwError_def o_def]
               simp: throwError_def invocationCatch_def syscall_error_to_H_cases invocation_eq_use_types)[1]
  apply clarsimp
  apply (clarsimp simp: interpret_excaps_test_null excaps_map_def
                        Collect_const_mem word_sless_def word_sle_def
                        sysargs_rel_to_n
                  cong: if_cong)
  apply (cut_tac unat_lt2p[where x="args ! 3"])
  apply (clarsimp simp: word_less_nat_alt unat_ucast neq_Nil_conv)
  (* this conjI construction gets the two Haskell conjuncts into adjacent goals for auto below *)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    prefer 3
    (* ARMIRQIssueIRQHandlerTrigger + ARMIRQIssueSGISignal Haskell *)
    apply (auto simp: ct_in_state'_def word_bits_def
                      excaps_in_mem_def slotcap_in_mem_def
                      cte_wp_at_ctes_of numeral_eqs[symmetric]
                      valid_tcb_state'_def
                      numSGIs_def numSGIs_bits_def word_le_nat_alt
               elim!: pred_tcb'_weakenE cte_wp_at_weakenE'
               dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[2]
  apply (rule conjI)
   (* ARMIRQIssueIRQHandlerTrigger C *)
   apply clarsimp
   apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
   apply (clarsimp simp: rf_sr_ksCurThread)
  (* ARMIRQIssueSGISignal C *)
  apply clarsimp
  apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
  by (auto simp: rf_sr_ksCurThread numeral_3_eq_3 numeral_2_eq_2)

lemma decodeIRQControlInvocation_ccorres:
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
  supply gen_invocation_type_eq[simp] if_cong[cong] Collect_const[simp del]
  supply maxIRQ_casts[simp]
  apply (cinit' lift: invLabel_' srcSlot_' length___unsigned_long_' current_extra_caps_' buffer_')
   apply (simp add: decodeIRQControlInvocation_def invocation_eq_use_types
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: list_case_If2 cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
     apply (rule ccorres_cond_true_seq)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: interpret_excaps_test_null excaps_map_def
                      throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null excaps_map_def
                     word_less_nat_alt Let_def
                cong: call_ignore_cong)
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
            apply (simp add: rangeCheck_def unlessE_def AARCH64.minIRQ_def
                             ucast_nat_def word_le_nat_alt[symmetric]
                             linorder_not_le[symmetric]
                             length_ineq_not_Nil hd_conv_nth
                        cong: call_ignore_cong ccorres_prog_only_cong)
            apply (simp add: split_def invocationCatch_use_injection_handler injection_handler_bindE
                             bindE_assoc
                        cong: call_ignore_cong ccorres_prog_only_cong)
            apply (ctac add: ccorres_injection_handler_csum1[OF Arch_checkIRQ_ccorres])
               apply (simp add: injection_liftE liftE_bindE)
               apply ccorres_rewrite
               apply (ctac add: isIRQActive_ccorres)
                 apply (simp only: injection_handler_whenE injection_handler_throwError)
                 apply (rule ccorres_split_when_throwError_cond[where Q=\<top> and Q'=\<top>])
                    apply simp
                   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                   apply (rule allI, rule conseqPre, vcg)
                   apply (clarsimp simp: throwError_def return_def exception_defs
                                         syscall_error_rel_def syscall_error_to_H_def
                                         syscall_error_type_defs)
                apply (ctac add: ccorres_injection_handler_csum1
                                        [OF lookupTargetSlot_ccorres,
                                            unfolded lookupTargetSlot_def])
                   prefer 2
                   apply ccorres_rewrite
                   apply (ctac add: ccorres_return_C_errorE)
                  apply ccorres_rewrite
                    apply csymbr
                    apply (ctac add: ccorres_injection_handler_csum1[OF ensureEmptySlot_ccorres])
                       prefer 2
                       apply ccorres_rewrite
                       apply (ctac add: ccorres_return_C_errorE)
                      apply ccorres_rewrite
                      apply (simp add: ccorres_invocationCatch_Inr performInvocation_def
                                       liftE_bindE bindE_assoc injection_handler_returnOk
                                  cong: ccorres_prog_only_cong)
                      apply (ctac (no_vcg) add: setThreadState_ccorres)
                       apply (ctac add: invokeIRQControl_ccorres)
                          apply (clarsimp simp: liftE_alternative)
                          apply (rule ccorres_alternative2)
                          apply (ctac add: ccorres_return_CE)
                         apply (ctac add: ccorres_inst[where P=\<top> and P'=UNIV])
                        apply wp
                       apply (vcg exspec=invokeIRQControl_modifies)
                      apply (wp sts_invs_minor')
                     apply (rule injection_wp, rule refl, wp)
                    apply simp
                    apply vcg
                   apply (rule injection_wp, rule refl)
                   apply clarsimp
                   apply (wp hoare_drop_imps)
                  apply simp
                  apply (vcg exspec=lookupTargetSlot_modifies)
                 apply vcg
                apply simp
                apply (wp isIRQActive_wp)
               apply simp
               apply (vcg exspec=isIRQActive_modifies)
              apply ccorres_rewrite
              apply (ctac add: ccorres_return_C_errorE)
             apply (rule injection_wp, rule refl)
             apply simp
             apply (wp checkIRQ_wpE)
            apply (rule_tac P'="\<lbrace> \<acute>ksCurThread = tcb_ptr_to_ctcb_ptr thread\<rbrace>" in conseqPre)
            apply (prop_tac "\<forall>x::machine_word. \<not> scast Kernel_C.maxIRQ < x
                                                 \<longrightarrow> x = ucast (toEnum (unat x)::irq)")
             apply (clarsimp simp: Kernel_C_maxIRQ not_less word_le_nat_alt)
             apply (subst toEnum_unat_ucast)
              apply (erule le_less_trans)
              apply (rule maxIRQ_less_2p_irq_len)
             apply (subst ucast_ucast_len)
              apply (rule le_less_trans[where y=Kernel_Config.maxIRQ])
               apply (simp add: word_le_nat_alt)
              apply (simp add: word_less_nat_alt maxIRQ_less_2p_irq_len[simplified])
             apply (rule refl)
            apply (clarsimp simp: numeral_2_eq_2 exception_defs ThreadState_defs mask_def)
            apply (rule conseqPre, vcg)
             apply (fastforce simp: exception_defs)
            apply (rule subset_refl)
           apply simp
           apply (wp getSlotCap_wp)
          apply vcg
         apply wp
        apply (vcg exspec=getSyscallArg_modifies)
       apply clarsimp
       apply wp
      apply (vcg exspec=getSyscallArg_modifies)
     apply (clarsimp, wp)
    apply (vcg exspec=getSyscallArg_modifies)
   apply simp
   apply (clarsimp simp: decodeIRQ_arch_helper)
   apply (simp add: liftME_invocationCatch)
   apply (rule ccorres_add_returnOk)
   apply (ctac add: Arch_decodeIRQControlInvocation_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wp
   apply (vcg exspec=Arch_decodeIRQControlInvocation_modifies)
  apply clarsimp
  apply (clarsimp simp: interpret_excaps_test_null excaps_map_def
                        Collect_const_mem word_sless_def word_sle_def
                        sysargs_rel_to_n
                  cong: if_cong)
  apply (rule conjI)
   apply (cut_tac unat_lt2p[where x="args ! 2"])
   apply clarsimp
   apply (clarsimp simp: word_less_nat_alt unat_ucast)
   apply (auto simp: ct_in_state'_def neq_Nil_conv word_bits_def
                     excaps_in_mem_def slotcap_in_mem_def
                     cte_wp_at_ctes_of numeral_eqs[symmetric]
                     valid_tcb_state'_def
              elim!: pred_tcb'_weakenE cte_wp_at_weakenE'
              dest!: st_tcb_at_idle_thread' interpret_excaps_eq)[1]
  apply (clarsimp simp: neq_Nil_conv)
  apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (clarsimp simp: rf_sr_ksCurThread)
  done

end
end
