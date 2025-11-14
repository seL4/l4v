(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Properties of machine operations.
*)

theory Machine_AI
imports Bits_AI
begin


definition
  "no_irq f \<equiv> \<forall>P. \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"

lemma wpc_helper_no_irq:
  "no_irq f \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') (no_irq f)"
  by (simp add: wpc_helper_def)

wpc_setup "\<lambda>m. no_irq m" wpc_helper_no_irq

ML \<open>
structure CrunchNoIrqInstance : CrunchInstance =
struct
  val name = "no_irq";
  val prefix_name_scheme = true;
  type extra = unit;
  val eq_extra = op =;
  fun parse_extra ctxt extra
        = case extra of
            "" => (Syntax.parse_term ctxt "%_. True", ())
          | _ => error "no_irq does not need a precondition";
  val has_preconds = false;
  fun mk_term _ body _ =
    (Syntax.parse_term @{context} "no_irq") $ body;
  fun dest_term (Const (@{const_name no_irq}, _) $ body)
    = SOME (Term.dummy, body, ())
    | dest_term _ = NONE;
  fun put_precond _ _ = error "crunch no_irq should not be calling put_precond";
  val pre_thms = [];
  val wpc_tactic = wp_cases_tactic_weak;
  fun wps_tactic _ _ _ = no_tac;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. no_irq mapp_lambda_ignore";
  val get_monad_state_type = get_nondet_monad_state_type;
end;

structure CrunchNoIrq : CRUNCH = Crunch(CrunchNoIrqInstance);
\<close>

setup \<open>
  add_crunch_instance "no_irq" (CrunchNoIrq.crunch_x, CrunchNoIrq.crunch_ignore_add_dels)
\<close>

crunch_ignore (no_irq) (add:
  Nondet_Monad.bind return "when" get gets fail
  assert put modify unless select
  alternative assert_opt gets_the
  returnOk throwError lift bindE
  liftE whenE unlessE throw_opt
  assertE liftM liftME sequence_x
  zipWithM_x mapM_x sequence mapM sequenceE_x
  mapME_x catch select_f
  handleE' handleE handle_elseE forM forM_x
  zipWithM ignore_failure)

context Arch begin arch_global_naming

lemma det_getRegister: "det (getRegister x)"
  by (simp add: getRegister_def)

lemma det_setRegister: "det (setRegister x w)"
  by (simp add: setRegister_def det_def modify_def get_def put_def bind_def)


lemma det_getRestartPC: "det getRestartPC"
  by (simp add: getRestartPC_def det_getRegister)


lemma det_setNextPC: "det (setNextPC p)"
  by (simp add: setNextPC_def det_setRegister)

(* FIXME empty_fail: make all empty_fail [intro!, wp], and non-conditional ones [simp] *)
lemma ef_loadWord: "empty_fail (loadWord x)"
  by (fastforce simp: loadWord_def)


lemma ef_storeWord: "empty_fail (storeWord x y)"
  by (fastforce simp: storeWord_def)


lemma no_fail_getRestartPC: "no_fail \<top> getRestartPC"
  by (simp add: getRestartPC_def getRegister_def)


lemma no_fail_loadWord [wp]: "no_fail (\<lambda>_. is_aligned p 2) (loadWord p)"
  apply (simp add: loadWord_def is_aligned_mask [symmetric])
  apply (rule no_fail_pre)
   apply wp
  apply simp
  done


lemma no_fail_storeWord: "no_fail (\<lambda>_. is_aligned p 2) (storeWord p w)"
  apply (simp add: storeWord_def is_aligned_mask [symmetric])
  apply (rule no_fail_pre)
   apply (wp)
  apply simp
  done


lemma no_fail_machine_op_lift [simp]:
  "no_fail \<top> (machine_op_lift f)"
  by (simp add: machine_op_lift_def)


lemma ef_machine_op_lift [simp]:
  "empty_fail (machine_op_lift f)"
  by (simp add: machine_op_lift_def)



lemma no_fail_setNextPC: "no_fail \<top> (setNextPC pc)"
  by (simp add: setNextPC_def setRegister_def)


lemma no_fail_getFAR: "no_fail \<top> getFAR"
  by (simp add: getFAR_def)


lemma no_fail_getDFSR: "no_fail \<top> getDFSR"
  by (simp add: getDFSR_def)


lemma no_fail_getIFSR: "no_fail \<top> getIFSR"
  by (simp add: getIFSR_def)

lemma no_fail_isb: "no_fail \<top> isb"
  by (simp add: isb_def)

lemma no_fail_dsb: "no_fail \<top> dsb"
  by (simp add: dsb_def)

lemma no_fail_dmb: "no_fail \<top> dmb"
  by (simp add: dmb_def)

lemma no_fail_writeTTBR0: "no_fail \<top> (writeTTBR0 w)"
  by (simp add: writeTTBR0_def)

lemma no_fail_set_current_pd: "no_fail \<top> (set_current_pd w)"
  by (simp add: set_current_pd_def setCurrentPDPL2_def)

lemma no_fail_cleanByVA: "no_fail \<top> (cleanByVA w p)"
  by (simp add: cleanByVA_def)

lemma no_fail_cleanByVA_PoU: "no_fail \<top> (cleanByVA_PoU w p)"
  by (simp add: cleanByVA_PoU_def)

lemma no_fail_invalidateLocalTLB: "no_fail \<top> invalidateLocalTLB"
  by (simp add: invalidateLocalTLB_def)

lemma no_fail_invalidateLocalTLB_ASID: "no_fail \<top> (invalidateLocalTLB_ASID x)"
  by (simp add: invalidateLocalTLB_ASID_def)

lemma no_fail_invalidateLocalTLB_VAASID: "no_fail \<top> (invalidateLocalTLB_VAASID x)"
  by (simp add: invalidateLocalTLB_VAASID_def)

lemma no_fail_invalidateByVA: "no_fail \<top> (invalidateByVA w p)"
  by (simp add: invalidateByVA_def)

lemma no_fail_invalidateByVA_I: "no_fail \<top> (invalidateByVA_I w p)"
  by (simp add: invalidateByVA_I_def)

lemma no_fail_invalidate_I_PoU: "no_fail \<top> invalidate_I_PoU"
  by (simp add: invalidate_I_PoU_def)

lemma no_fail_cleanInvalByVA: "no_fail \<top> (cleanInvalByVA w p)"
  by (simp add: cleanInvalByVA_def)

lemma no_fail_branchFlush: "no_fail \<top> (branchFlush w p)"
  by (simp add: branchFlush_def)

lemma no_fail_clean_D_PoU: "no_fail \<top> clean_D_PoU"
  by (simp add: clean_D_PoU_def)

lemma no_fail_cleanInvalidate_D_PoC: "no_fail \<top> cleanInvalidate_D_PoC"
  by (simp add: cleanInvalidate_D_PoC_def)

lemma no_fail_cleanInvalidateL2Range: "no_fail \<top> (cleanInvalidateL2Range w p)"
  by (simp add: cleanInvalidateL2Range_def)

lemma no_fail_invalidateL2Range: "no_fail \<top> (invalidateL2Range w p)"
  by (simp add: invalidateL2Range_def)

lemma no_fail_cleanL2Range: "no_fail \<top> (cleanL2Range w p)"
  by (simp add: cleanL2Range_def)

lemma no_fail_initL2Cache: "no_fail \<top> initL2Cache"
  by (simp add: initL2Cache_def)

lemma no_fail_clearExMonitor: "no_fail \<top> clearExMonitor"
  by (simp add: clearExMonitor_def)

lemma no_fail_flushBTAC: "no_fail \<top> flushBTAC"
  by (simp add: flushBTAC_def)

lemma no_fail_writeContextID: "no_fail \<top> writeContextID"
  by (simp add: writeContextID_def)

lemma no_fail_setHardwareASID: "no_fail \<top> (setHardwareASID hw_asid)"
  by (simp add: setHardwareASID_def)


lemma no_fail_resetTimer[wp]: "no_fail \<top> resetTimer"
  by (simp add: resetTimer_def)


lemma loadWord_inv: "\<lbrace>P\<rbrace> loadWord x \<lbrace>\<lambda>x. P\<rbrace>"
  apply (simp add: loadWord_def)
  apply wp
  apply simp
  done


lemma getRestartPC_inv: "\<lbrace>P\<rbrace> getRestartPC \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getRestartPC_def getRegister_def)


lemma getDFSR_inv: "\<lbrace>P\<rbrace> getDFSR \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getDFSR_def)


lemma getFAR_inv: "\<lbrace>P\<rbrace> getFAR \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getFAR_def)


lemma getIFSR_inv: "\<lbrace>P\<rbrace> getIFSR \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getIFSR_def)

lemma getHDFAR_inv: "\<lbrace>P\<rbrace> getHDFAR \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getHDFAR_def)

lemma getHSR_inv: "\<lbrace>P\<rbrace> getHSR \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getHSR_def)

lemma no_fail_cacheRangeOp[simp, wp]:
  assumes nf: "\<And>a b. no_fail \<top> (oper a b)"
  shows "no_fail \<top> (cacheRangeOp oper s e p)"
  apply (simp add: cacheRangeOp_def mapM_x_mapM)
  apply (rule no_fail_pre)
   apply (wp no_fail_mapM nf | wpc | clarsimp)+
  done

lemma no_fail_cleanCacheRange_PoU[simp, wp]:
  "no_fail \<top> (cleanCacheRange_PoU s e p)"
  by (simp add: cleanCacheRange_PoU_def, wp no_fail_cleanByVA_PoU)

lemma no_fail_cleanCacheRange_PoC[simp, wp]:
  "no_fail \<top> (cleanCacheRange_PoC s e p)"
  by (simp add: cleanCacheRange_PoC_def, wp no_fail_cleanByVA)

lemma no_fail_cleanInvalidateCacheRange_RAM[simp, wp]:
  "no_fail \<top> (cleanInvalidateCacheRange_RAM s e p)"
  by (simp add: cleanInvalidateCacheRange_RAM_def, rule no_fail_pre,
      wp no_fail_dsb no_fail_cleanInvalidateL2Range no_fail_cleanInvalByVA, simp)

lemma no_fail_cleanCacheRange_RAM[simp, wp]:
  "no_fail \<top> (cleanCacheRange_RAM s e p)"
  apply (simp add: cleanCacheRange_RAM_def)
  apply (rule no_fail_pre, wp no_fail_dsb no_fail_cleanL2Range, simp)
  done

lemma no_fail_invalidateCacheRange_I[simp, wp]:
  "no_fail \<top> (invalidateCacheRange_I s e p)"
  by (simp add: invalidateCacheRange_I_def, wp no_fail_invalidate_I_PoU)

lemma no_fail_invalidateCacheRange_RAM[simp, wp]:
  "no_fail \<top> (invalidateCacheRange_RAM s e p)"
  unfolding invalidateCacheRange_RAM_def
  by (wpsimp wp: no_fail_invalidateL2Range no_fail_invalidateByVA no_fail_dsb)

lemma no_fail_branchFlushRange[simp, wp]:
  "no_fail \<top> (branchFlushRange s e p)"
  by (simp add: branchFlushRange_def, wp no_fail_branchFlush)

lemma no_fail_cleanCaches_PoU[simp, wp]:
  "no_fail \<top> cleanCaches_PoU"
  by (simp add: cleanCaches_PoU_def, rule no_fail_pre,
      wp no_fail_dsb no_fail_clean_D_PoU no_fail_invalidate_I_PoU, simp)

lemma no_fail_cleanInvalidateL1Caches[simp, wp]:
  "no_fail \<top> cleanInvalidateL1Caches"
  by (simp add: cleanInvalidateL1Caches_def, rule no_fail_pre,
      wp no_fail_dsb no_fail_cleanInvalidate_D_PoC no_fail_invalidate_I_PoU, simp)

lemma no_fail_clearMemory[simp, wp]:
  "no_fail (\<lambda>_. is_aligned p 2) (clearMemory p b)"
  apply (simp add: clearMemory_def mapM_x_mapM)
  apply (rule no_fail_pre)
   apply (wp no_fail_mapM' no_fail_storeWord no_fail_cleanCacheRange_PoU)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule aligned_add_aligned)
   apply (simp add: word_size_def)
   apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
  apply simp
  done

lemma no_fail_freeMemory[simp, wp]:
  "no_fail (\<lambda>_. is_aligned p 2) (freeMemory p b)"
  apply (simp add: freeMemory_def mapM_x_mapM)
  apply (rule no_fail_pre)
  apply (wp no_fail_mapM' no_fail_storeWord)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule aligned_add_aligned)
   apply (simp add: word_size_def)
   apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
  apply simp
  done


lemma no_fail_getActiveIRQ[wp]:
  "no_fail \<top> (getActiveIRQ in_kernel)"
  apply (simp add: getActiveIRQ_def)
  apply (rule no_fail_pre)
   apply wp
  apply simp
  done

definition "irq_state_independent P \<equiv> \<forall>f s. P s \<longrightarrow> P (irq_state_update f s)"

lemma getActiveIRQ_inv [wp]:
  "\<lbrakk>irq_state_independent P\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> getActiveIRQ in_kernel \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply (simp add: irq_state_independent_def)
  done

lemma no_fail_ackInterrupt[wp]: "no_fail \<top> (ackInterrupt irq)"
  by (simp add: ackInterrupt_def)


lemma no_fail_maskInterrupt[wp]: "no_fail \<top> (maskInterrupt irq bool)"
  by (simp add: maskInterrupt_def)

lemma no_fail_sendSGI[wp]:
  "no_fail \<top> (sendSGI irq target)"
  by (simp add: sendSGI_def)

lemma no_irq_use:
  "\<lbrakk> no_irq f; (rv,s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> irq_masks s' = irq_masks s"
  apply (simp add: no_irq_def valid_def)
  apply (erule_tac x="\<lambda>x. x = irq_masks s" in allE)
  apply fastforce
  done

lemma no_irq_machine_rest_lift:
  "no_irq (machine_rest_lift f)"
  apply (clarsimp simp: no_irq_def machine_rest_lift_def split_def)
  apply wp
  apply simp
  done

crunch machine_op_lift
  for (no_irq) no_irq[wp, simp]

lemma no_irq:
  "no_irq f \<Longrightarrow> \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"
  by (simp add: no_irq_def)

lemma no_irq_sendSGI:
  "no_irq (sendSGI irq target)"
  by (simp add: sendSGI_def)

lemma no_irq_isb: "no_irq  isb"
  by (simp add: isb_def)

lemma no_irq_dsb: "no_irq  dsb"
  by (simp add: dsb_def)

lemma no_irq_dmb: "no_irq  dmb"
  by (simp add: dmb_def)

lemma no_irq_cleanByVA: "no_irq  (cleanByVA w p)"
  by (simp add: cleanByVA_def)

lemma no_irq_cleanByVA_PoU: "no_irq  (cleanByVA_PoU w p)"
  by (simp add: cleanByVA_PoU_def)

lemma no_irq_invalidateLocalTLB: "no_irq  invalidateLocalTLB"
  by (simp add: invalidateLocalTLB_def)

lemma no_irq_invalidateLocalTLB_ASID: "no_irq  (invalidateLocalTLB_ASID x)"
  by (simp add: invalidateLocalTLB_ASID_def)

lemma no_irq_invalidateLocalTLB_VAASID: "no_irq  (invalidateLocalTLB_VAASID x)"
  by (simp add: invalidateLocalTLB_VAASID_def)

lemma no_irq_invalidateByVA: "no_irq  (invalidateByVA w p)"
  by (simp add: invalidateByVA_def)

lemma no_irq_invalidateByVA_I: "no_irq  (invalidateByVA_I w p)"
  by (simp add: invalidateByVA_I_def)

lemma no_irq_invalidate_I_PoU: "no_irq  invalidate_I_PoU"
  by (simp add: invalidate_I_PoU_def)

lemma no_irq_cleanInvalByVA: "no_irq  (cleanInvalByVA w p)"
  by (simp add: cleanInvalByVA_def)

lemma no_irq_branchFlush: "no_irq  (branchFlush w p)"
  by (simp add: branchFlush_def)

lemma no_irq_clean_D_PoU: "no_irq  clean_D_PoU"
  by (simp add: clean_D_PoU_def)

lemma no_irq_cleanInvalidate_D_PoC: "no_irq  cleanInvalidate_D_PoC"
  by (simp add: cleanInvalidate_D_PoC_def)

lemma no_irq_cleanInvalidateL2Range: "no_irq  (cleanInvalidateL2Range w p)"
  by (simp add: cleanInvalidateL2Range_def)

lemma no_irq_invalidateL2Range: "no_irq  (invalidateL2Range w p)"
  by (simp add: invalidateL2Range_def)

lemma no_irq_cleanL2Range: "no_irq  (cleanL2Range w p)"
  by (simp add: cleanL2Range_def)

lemma no_irq_initL2Cache: "no_irq  initL2Cache"
  by (simp add: initL2Cache_def)

lemma no_irq_flushBTAC: "no_irq  flushBTAC"
  by (simp add: flushBTAC_def)

lemma no_irq_writeContextID: "no_irq  writeContextID"
  by (simp add: writeContextID_def)


lemma no_irq_setHardwareASID: "no_irq (setHardwareASID hw_asid)"
  by (simp add: setHardwareASID_def)

lemma no_irq_writeTTBR0: "no_irq (writeTTBR0 pd)"
  by (simp add: writeTTBR0_def)

lemma no_irq_gets [simp]:
  "no_irq (gets f)"
  by (simp add: no_irq_def)


lemma no_irq_getIFSR: "no_irq getIFSR"
  by (simp add: getIFSR_def)


lemma no_irq_getDFSR: "no_irq getDFSR"
  by (simp add: getDFSR_def)


lemma no_irq_getFAR: "no_irq getFAR"
  by (simp add: getFAR_def)


lemma no_irq_resetTimer: "no_irq resetTimer"
  by (simp add: resetTimer_def)


lemma no_irq_debugPrint: "no_irq (debugPrint $ xs)"
  by (simp add: no_irq_def)

lemma no_irq_writeContextIDAndPD: "no_irq (writeContextIDAndPD asid w)"
  by (simp add: writeContextIDAndPD_def)

lemma no_irq_addressTranslateS1: "no_irq (addressTranslateS1 w)"
  apply (clarsimp simp add: addressTranslateS1_def no_irq_def, wp)
  apply (simp only: atomize_all)
  apply (wp no_irq_machine_op_lift[simplified no_irq_def], simp)
  done

lemma no_irq_setHCR: "no_irq (setHCR w)"
  by (simp add: setHCR_def)

lemma no_irq_setSCTLR: "no_irq (setSCTLR w)"
  by (simp add: setSCTLR_def)

lemma no_irq_getSCTLR: "no_irq getSCTLR"
    by (simp add: getSCTLR_def)

lemma no_irq_readVCPUHardwareReg: "no_irq (readVCPUHardwareReg r)"
  by (simp add: readVCPUHardwareReg_def)

lemma no_irq_writeVCPUHardwareReg: "no_irq (writeVCPUHardwareReg r v)"
  by (simp add: writeVCPUHardwareReg_def)

lemma no_irq_get_gic_vcpu_ctrl_vmcr: "no_irq get_gic_vcpu_ctrl_vmcr"
  by (simp add: get_gic_vcpu_ctrl_vmcr_def)

lemma no_irq_set_gic_vcpu_ctrl_vmcr: "no_irq (set_gic_vcpu_ctrl_vmcr w)"
  by (simp add: set_gic_vcpu_ctrl_vmcr_def)

lemma no_irq_get_gic_vcpu_ctrl_apr: "no_irq get_gic_vcpu_ctrl_apr"
  by (simp add: get_gic_vcpu_ctrl_apr_def)

lemma no_irq_set_gic_vcpu_ctrl_apr: "no_irq (set_gic_vcpu_ctrl_apr w)"
  by (simp add: set_gic_vcpu_ctrl_apr_def)

lemma no_irq_get_gic_vcpu_ctrl_lr: "no_irq (get_gic_vcpu_ctrl_lr n)"
  apply (clarsimp simp add: get_gic_vcpu_ctrl_lr_def no_irq_def, wp)
  apply (simp only: atomize_all)
  apply (wp no_irq_machine_op_lift[simplified no_irq_def], simp)
  done

lemma no_irq_set_gic_vcpu_ctrl_lr: "no_irq (set_gic_vcpu_ctrl_lr n w)"
  by (simp add: set_gic_vcpu_ctrl_lr_def)

lemma no_irq_get_gic_vcpu_ctrl_hcr: "no_irq get_gic_vcpu_ctrl_hcr"
  by (simp add: get_gic_vcpu_ctrl_hcr_def)

lemma no_irq_set_gic_vcpu_ctrl_hcr: "no_irq (set_gic_vcpu_ctrl_hcr w)"
  by (simp add: set_gic_vcpu_ctrl_hcr_def)

context notes no_irq[wp] begin

lemma no_irq_ackInterrupt: "no_irq (ackInterrupt irq)"
  by (wp | clarsimp simp: no_irq_def ackInterrupt_def)+

lemma no_irq_setIRQTrigger: "no_irq (setIRQTrigger irq bool)"
  by (wp | clarsimp simp: no_irq_def setIRQTrigger_def)+

lemma no_irq_loadWord: "no_irq (loadWord x)"
  apply (clarsimp simp: no_irq_def)
  apply (rule loadWord_inv)
  done


lemma no_irq_getActiveIRQ: "no_irq (getActiveIRQ in_kernel)"
  apply (clarsimp simp: no_irq_def)
  apply (rule getActiveIRQ_inv)
  apply (simp add: irq_state_independent_def)
  done


lemma no_irq_mapM:
  "(\<And>x. x \<in> set xs \<Longrightarrow> no_irq (f x)) \<Longrightarrow> no_irq (mapM f xs)"
  apply (subst no_irq_def)
  apply clarify
  apply (rule mapM_wp)
   prefer 2
   apply (rule order_refl)
  apply wpsimp
  done

lemma no_irq_mapM_x:
  "(\<And>x. x \<in> set xs \<Longrightarrow> no_irq (f x)) \<Longrightarrow> no_irq (mapM_x f xs)"
  apply (subst no_irq_def)
  apply clarify
  apply (rule mapM_x_wp)
   prefer 2
   apply (rule order_refl)
  apply wpsimp
  done


lemma no_irq_swp:
  "no_irq (f y x) \<Longrightarrow> no_irq (swp f x y)"
  by (simp add: swp_def)


lemma no_irq_seq [wp]:
  "\<lbrakk> no_irq f; \<And>x. no_irq (g x) \<rbrakk> \<Longrightarrow> no_irq (f >>= g)"
  apply (subst no_irq_def)
  apply clarsimp
  apply (rule bind_wp)
  apply (wp|simp)+
  done

lemma no_irq_return [simp, wp]: "no_irq (return v)"
  unfolding no_irq_def return_def
  by (rule allI, simp add: valid_def)


lemma no_irq_fail [simp, wp]: "no_irq fail"
  unfolding no_irq_def fail_def
  by (rule allI, simp add: valid_def)



lemma no_irq_assert [simp, wp]: "no_irq (assert P)"
  unfolding assert_def by simp


lemma no_irq_modify:
  "(\<And>s. irq_masks (f s) = irq_masks s) \<Longrightarrow> no_irq (modify f)"
  unfolding modify_def no_irq_def
  apply (rule allI, simp add: valid_def put_def get_def)
  apply (clarsimp simp: in_monad)
  done

lemma no_irq_set_current_pd: "no_irq (set_current_pd pd)"
  by (clarsimp simp: set_current_pd_def setCurrentPDPL2_def)

lemma no_irq_clearExMonitor: "no_irq clearExMonitor"
  apply (simp add: clearExMonitor_def)
  apply (wp no_irq_modify)
  apply simp
  done


lemma no_irq_storeWord: "no_irq (storeWord w p)"
  apply (simp add: storeWord_def)
  apply (wp no_irq_modify)
  apply simp
  done

lemma no_irq_cacheRangeOp[simp, wp]:
  assumes nf: "\<And>a b. no_irq (oper a b)"
  shows "no_irq (cacheRangeOp oper s e p)"
  apply (simp add: cacheRangeOp_def)
   apply (wp no_irq_mapM_x nf | wpc | clarsimp)+
  done

lemma no_irq_cleanCacheRange_PoU[simp, wp]:
  "no_irq (cleanCacheRange_PoU s e p)"
  by (simp add: cleanCacheRange_PoU_def, wp no_irq_cleanByVA_PoU)

lemma no_irq_cleanCacheRange_PoC[simp, wp]:
  "no_irq (cleanCacheRange_PoC s e p)"
  by (simp add: cleanCacheRange_PoC_def, wp no_irq_cleanByVA)

lemma no_irq_cleanInvalidateCacheRange_RAM[simp, wp]:
  "no_irq (cleanInvalidateCacheRange_RAM s e p)"
  by (simp add: cleanInvalidateCacheRange_RAM_def,
      wp no_irq_dsb no_irq_cleanInvalidateL2Range no_irq_cleanInvalByVA)

lemma no_irq_cleanCacheRange_RAM[simp, wp]:
  "no_irq (cleanCacheRange_RAM s e p)"
  apply (simp add: cleanCacheRange_RAM_def)
  apply (wp no_irq_dsb no_irq_cleanL2Range)
  done

lemma no_irq_invalidateCacheRange_I[simp, wp]:
  "no_irq (invalidateCacheRange_I s e p)"
  by (simp add: invalidateCacheRange_I_def, wp no_irq_invalidate_I_PoU)

lemma no_irq_when:
  "\<lbrakk>P \<Longrightarrow> no_irq f\<rbrakk> \<Longrightarrow> no_irq (when P f)"
  by (simp add: when_def)

lemma no_irq_invalidateCacheRange_RAM[simp, wp]:
  "no_irq (invalidateCacheRange_RAM s e p)"
  apply (simp add: invalidateCacheRange_RAM_def)
  apply (wp no_irq_invalidateL2Range no_irq_invalidateByVA no_irq_dsb no_irq_when)
  done

lemma no_irq_branchFlushRange[simp, wp]:
  "no_irq (branchFlushRange s e p)"
  by (simp add: branchFlushRange_def, wp no_irq_branchFlush)

lemma no_irq_cleanCaches_PoU[simp, wp]:
  "no_irq cleanCaches_PoU"
  by (simp add: cleanCaches_PoU_def,
      wp no_irq_dsb no_irq_clean_D_PoU no_irq_invalidate_I_PoU)

lemma no_irq_cleanInvalidateL1Caches[simp, wp]:
  "no_irq cleanInvalidateL1Caches"
  by (simp add: cleanInvalidateL1Caches_def,
      wp no_irq_dsb no_irq_cleanInvalidate_D_PoC no_irq_invalidate_I_PoU)


lemma no_irq_clearMemory: "no_irq (clearMemory a b)"
  apply (simp add: clearMemory_def)
  apply (wp no_irq_mapM_x no_irq_storeWord no_irq_cleanCacheRange_PoU)
  done

lemma getActiveIRQ_le_maxIRQ':
  "\<lbrace>\<lambda>s. \<forall>irq > maxIRQ. irq_masks s irq\<rbrace> getActiveIRQ in_kernel \<lbrace>\<lambda>rv s. \<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply clarsimp
  apply (rule ccontr)
  apply (simp add: linorder_not_le)
  done

lemma getActiveIRQ_neq_non_kernel:
  "\<lbrace>\<top>\<rbrace> getActiveIRQ True \<lbrace>\<lambda>rv s. rv \<notin> Some ` non_kernel_IRQs \<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply auto
  done

lemma dmo_getActiveIRQ_non_kernel[wp]:
  "\<lbrace>\<top>\<rbrace> do_machine_op (getActiveIRQ True)
   \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> irq \<in> non_kernel_IRQs \<longrightarrow> P irq s\<rbrace>"
  unfolding do_machine_op_def
  apply wpsimp
  apply (drule use_valid, rule getActiveIRQ_neq_non_kernel, rule TrueI)
  apply clarsimp
  done

lemma empty_fail_isb: "empty_fail  isb"
  by (simp add: isb_def)

lemma empty_fail_dsb: "empty_fail  dsb"
  by (simp add: dsb_def)

lemma empty_fail_dmb: "empty_fail  dmb"
  by (simp add: dmb_def)

lemma empty_fail_sendSGI:
  "empty_fail (sendSGI irq target)"
  by (simp add: sendSGI_def)

lemma empty_fail_cleanByVA: "empty_fail  (cleanByVA w p)"
  by (simp add: cleanByVA_def)

lemma empty_fail_cleanByVA_PoU: "empty_fail  (cleanByVA_PoU w p)"
  by (simp add: cleanByVA_PoU_def)

lemma empty_fail_invalidateLocalTLB: "empty_fail  invalidateLocalTLB"
  by (simp add: invalidateLocalTLB_def)

lemma empty_fail_invalidateLocalTLB_ASID: "empty_fail  (invalidateLocalTLB_ASID x)"
  by (simp add: invalidateLocalTLB_ASID_def)

lemma empty_fail_invalidateLocalTLB_VAASID: "empty_fail  (invalidateLocalTLB_VAASID x)"
  by (simp add: invalidateLocalTLB_VAASID_def)

lemma empty_fail_invalidateByVA: "empty_fail  (invalidateByVA w p)"
  by (simp add: invalidateByVA_def)

lemma empty_fail_invalidateByVA_I: "empty_fail  (invalidateByVA_I w p)"
  by (simp add: invalidateByVA_I_def)

lemma empty_fail_invalidate_I_PoU: "empty_fail  invalidate_I_PoU"
  by (simp add: invalidate_I_PoU_def)

lemma empty_fail_cleanInvalByVA: "empty_fail  (cleanInvalByVA w p)"
  by (simp add: cleanInvalByVA_def)

lemma empty_fail_branchFlush: "empty_fail  (branchFlush w p)"
  by (simp add: branchFlush_def)

lemma empty_fail_clean_D_PoU: "empty_fail  clean_D_PoU"
  by (simp add: clean_D_PoU_def)

lemma empty_fail_cleanInvalidate_D_PoC: "empty_fail  cleanInvalidate_D_PoC"
  by (simp add: cleanInvalidate_D_PoC_def)

lemma empty_fail_cleanInvalidateL2Range: "empty_fail  (cleanInvalidateL2Range w p)"
  by (simp add: cleanInvalidateL2Range_def)

lemma empty_fail_invalidateL2Range: "empty_fail  (invalidateL2Range w p)"
  by (simp add: invalidateL2Range_def)

lemma empty_fail_cleanL2Range: "empty_fail  (cleanL2Range w p)"
  by (simp add: cleanL2Range_def)

lemma empty_fail_initL2Cache: "empty_fail  initL2Cache"
  by (simp add: initL2Cache_def)

lemma empty_fail_clearExMonitor: "empty_fail  clearExMonitor"
  by (simp add: clearExMonitor_def)

lemma empty_fail_flushBTAC: "empty_fail  flushBTAC"
  by (simp add: flushBTAC_def)

lemma empty_fail_writeContextID: "empty_fail  writeContextID"
  by (simp add: writeContextID_def)

lemma empty_fail_setHCR[simp, intro!]:
  "empty_fail (setHCR w)"
  by (simp add: setHCR_def)

lemma empty_fail_addressTranslateS1[simp, intro!]:
  "empty_fail (addressTranslateS1 w)"
  by (fastforce simp: addressTranslateS1_def)

lemma empty_fail_writeContextIDAndPD[simp, intro!]:
  "empty_fail (writeContextIDAndPD asid w)"
  by (simp add: writeContextIDAndPD_def)

lemma empty_fail_setSCTLR[simp, intro!]:
  "empty_fail (setSCTLR w)"
  by (simp add: setSCTLR_def)

lemma empty_fail_getSCTLR[simp, intro!]:
  "empty_fail getSCTLR"
  by (simp add: getSCTLR_def)

lemma empty_fail_get_gic_vcpu_ctrl_vmcr[simp, intro!]:
  "empty_fail get_gic_vcpu_ctrl_vmcr"
  by (simp add: get_gic_vcpu_ctrl_vmcr_def)

lemma empty_fail_set_gic_vcpu_ctrl_vmcr[simp, intro!]:
  "empty_fail (set_gic_vcpu_ctrl_vmcr w)"
  by (simp add: set_gic_vcpu_ctrl_vmcr_def)

lemma empty_fail_get_gic_vcpu_ctrl_apr[simp, intro!]:
  "empty_fail get_gic_vcpu_ctrl_apr"
  by (simp add: get_gic_vcpu_ctrl_apr_def)

lemma empty_fail_set_gic_vcpu_ctrl_apr[simp, intro!]:
  "empty_fail (set_gic_vcpu_ctrl_apr w)"
  by (simp add: set_gic_vcpu_ctrl_apr_def)

lemma empty_fail_get_gic_vcpu_ctrl_lr[simp, intro!]:
  "empty_fail (get_gic_vcpu_ctrl_lr n)"
  by (fastforce simp: get_gic_vcpu_ctrl_lr_def)

lemma empty_fail_set_gic_vcpu_ctrl_lr[simp, intro!]:
  "empty_fail (set_gic_vcpu_ctrl_lr n w)"
  by (simp add: set_gic_vcpu_ctrl_lr_def)

lemma empty_fail_get_gic_vcpu_ctrl_hcr[simp, intro!]:
  "empty_fail get_gic_vcpu_ctrl_hcr"
  by (simp add: get_gic_vcpu_ctrl_hcr_def)

lemma empty_fail_set_gic_vcpu_ctrl_hcr[simp, intro!]:
  "empty_fail (set_gic_vcpu_ctrl_hcr w)"
  by (simp add: set_gic_vcpu_ctrl_hcr_def)

crunch readVCPUHardwareReg, writeVCPUHardwareReg, get_cntv_cval_64, set_cntv_cval_64,
          get_cntv_off_64, set_cntv_off_64, read_cntpct
  for (no_fail) no_fail[intro!, wp, simp]
  and (empty_fail) empty_fail[intro!, wp, simp]
  and (no_irq) no_irq[intro!, wp, simp]
  (ignore: machine_op_lift writeVCPUHardwareReg_impl set_cntv_cval_64_impl set_cntv_off_64_impl gets
   wp: ef_machine_op_lift)

lemma empty_fail_cacheRangeOp [simp, intro!]:
  assumes ef: "\<And>a b. empty_fail (oper a b)"
  shows "empty_fail (cacheRangeOp oper s e p)"
  by (auto simp add: cacheRangeOp_def mapM_x_mapM intro: ef)

lemma empty_fail_cleanCacheRange_PoU[simp, intro!]:
  "empty_fail (cleanCacheRange_PoU s e p)"
  by (simp add: cleanCacheRange_PoU_def empty_fail_cleanByVA_PoU)

lemma empty_fail_cleanCacheRange_PoC[simp, intro!]:
  "empty_fail (cleanCacheRange_PoC s e p)"
  by (simp add: cleanCacheRange_PoC_def empty_fail_cleanByVA)

lemma empty_fail_cleanInvalidateCacheRange_RAM[simp, intro!]:
  "empty_fail (cleanInvalidateCacheRange_RAM s e p)"
  by (fastforce simp: cleanInvalidateCacheRange_RAM_def empty_fail_dsb
                      empty_fail_cleanInvalidateL2Range empty_fail_cleanInvalByVA)

lemma empty_fail_cleanCacheRange_RAM[simp, intro!]:
  "empty_fail (cleanCacheRange_RAM s e p)"
  by (fastforce simp: cleanCacheRange_RAM_def empty_fail_dsb empty_fail_cleanL2Range)

lemma empty_fail_invalidateCacheRange_I[simp, intro!]:
  "empty_fail (invalidateCacheRange_I s e p)"
  by (simp add: invalidateCacheRange_I_def empty_fail_invalidate_I_PoU)

lemma empty_fail_invalidateCacheRange_RAM[simp, intro!]:
  "empty_fail (invalidateCacheRange_RAM s e p)"
  by (fastforce simp: invalidateCacheRange_RAM_def
                      empty_fail_invalidateL2Range empty_fail_invalidateByVA empty_fail_dsb)

lemma empty_fail_branchFlushRange[simp, intro!]:
  "empty_fail (branchFlushRange s e p)"
  by (simp add: branchFlushRange_def empty_fail_branchFlush)

lemma empty_fail_cleanCaches_PoU[simp, intro!]:
  "empty_fail cleanCaches_PoU"
  by (fastforce simp: cleanCaches_PoU_def empty_fail_dsb empty_fail_clean_D_PoU empty_fail_invalidate_I_PoU)

lemma empty_fail_cleanInvalidateL1Caches[simp, intro!]:
  "empty_fail cleanInvalidateL1Caches"
  by (fastforce simp: cleanInvalidateL1Caches_def empty_fail_dsb empty_fail_cleanInvalidate_D_PoC
                     empty_fail_invalidate_I_PoU)

lemma empty_fail_clearMemory [simp, intro!]:
  "\<And>a b. empty_fail (clearMemory a b)"
  by (fastforce simp: clearMemory_def mapM_x_mapM ef_storeWord)


end
end

end
