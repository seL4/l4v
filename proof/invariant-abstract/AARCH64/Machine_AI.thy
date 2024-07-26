(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Properties of machine operations.
*)

theory Machine_AI
imports Bits_AI
begin

text \<open>Crunch setup\<close>

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

text \<open>Deterministic\<close>

lemma det_getRegister: "det (getRegister x)"
  by (simp add: getRegister_def)

lemma det_setRegister: "det (setRegister x w)"
  by (simp add: setRegister_def det_def modify_def get_def put_def bind_def)

lemma det_getRestartPC: "det getRestartPC"
  by (simp add: getRestartPC_def det_getRegister)

lemma det_setNextPC: "det (setNextPC p)"
  by (simp add: setNextPC_def det_setRegister)

text \<open>Failure on empty result\<close>

crunch loadWord, storeWord, machine_op_lift
  for (empty_fail) empty_fail[intro!, wp, simp]
  (ignore: Nondet_Monad.bind mapM_x simp: machine_op_lift_def empty_fail_cond)

lemmas ef_machine_op_lift = machine_op_lift_empty_fail \<comment> \<open>required for generic interface\<close>

text \<open>Does not affect state\<close>

definition "irq_state_independent P \<equiv> \<forall>f s. P s \<longrightarrow> P (irq_state_update f s)"

lemma getActiveIRQ_inv[wp]:
  "\<lbrakk>irq_state_independent P\<rbrakk> \<Longrightarrow> getActiveIRQ in_kernel \<lbrace>P\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply (simp add: irq_state_independent_def)
  done

lemma loadWord_inv[wp]: "loadWord x \<lbrace>P\<rbrace>"
  by (wpsimp simp: loadWord_def)

lemma getRestartPC_inv: "getRestartPC \<lbrace>P\<rbrace>"
  by (simp add: getRestartPC_def getRegister_def)

text \<open>Does not set failure flag\<close>

lemma no_fail_loadWord[wp]: "no_fail (\<lambda>_. is_aligned p 3) (loadWord p)"
  by (wpsimp simp: loadWord_def is_aligned_mask [symmetric])

lemma no_fail_storeWord: "no_fail (\<lambda>_. is_aligned p 3) (storeWord p w)"
  by (wpsimp simp: storeWord_def is_aligned_mask [symmetric])

lemma no_fail_machine_op_lift [simp]:
  "no_fail \<top> (machine_op_lift f)"
  by (simp add: machine_op_lift_def)

lemma no_fail_freeMemory[simp, wp]:
  "no_fail (\<lambda>_. is_aligned p 3) (freeMemory p b)"
  apply (simp add: freeMemory_def mapM_x_mapM)
  apply (rule no_fail_pre)
  apply (wp no_fail_mapM' no_fail_storeWord)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule aligned_add_aligned)
   apply (simp add: word_size_def)
   apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
  apply simp
  done

lemma no_fail_getActiveIRQ[wp]:
  "no_fail \<top> (getActiveIRQ in_kernel)"
  apply (simp add: getActiveIRQ_def)
  apply (rule no_fail_pre)
   apply wp
  apply simp
  done

text \<open>Does not affect IRQ masks - low-level properties of @{term no_irq}\<close>

lemma no_irq_bind[wp]:
  "\<lbrakk> no_irq f; \<And>rv. no_irq (g rv) \<rbrakk> \<Longrightarrow> no_irq (f >>= g)"
  unfolding no_irq_def
  by (wpsimp, blast+)

lemma no_irq_use:
  "\<lbrakk> no_irq f; (rv,s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> irq_masks s' = irq_masks s"
  apply (simp add: no_irq_def valid_def)
  apply (erule_tac x="\<lambda>x. x = irq_masks s" in allE)
  apply fastforce
  done

lemma no_irq_machine_rest_lift[simp, wp]:
  "no_irq (machine_rest_lift f)"
  by (wpsimp simp: no_irq_def machine_rest_lift_def split_def)

crunch machine_op_lift
  for (no_irq) no_irq[wp, simp]

lemma no_irq:
  "no_irq f \<Longrightarrow> \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>"
  by (simp add: no_irq_def)

lemma no_irq_return[simp, wp]:
  "no_irq (return v)"
  unfolding no_irq_def
  by simp

lemma no_irq_gets[simp, wp]:
  "no_irq (gets f)"
  by (simp add: no_irq_def)

lemma no_irq_mapM:
  "(\<And>x. x \<in> set xs \<Longrightarrow> no_irq (f x)) \<Longrightarrow> no_irq (mapM f xs)"
  apply (simp (no_asm) add: no_irq_def)
  apply (clarsimp intro!: mapM_wp[OF _ order_refl])
  apply (wpsimp wp: no_irq)
  done

lemma no_irq_mapM_x:
  "(\<And>x. x \<in> set xs \<Longrightarrow> no_irq (f x)) \<Longrightarrow> no_irq (mapM_x f xs)"
  apply (simp (no_asm) add: no_irq_def)
  apply (clarsimp intro!: mapM_x_wp[OF _ order_refl])
  apply (wpsimp wp: no_irq)
  done

lemma no_irq_swp:
  "no_irq (f y x) \<Longrightarrow> no_irq (swp f x y)"
  by (simp add: swp_def)

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

lemma no_irq_when[simp, wp]:
  "\<lbrakk>P \<Longrightarrow> no_irq f\<rbrakk> \<Longrightarrow> no_irq (when P f)"
  by (simp add: when_def)

text \<open>Architecture-specific @{term no_irq} preservations\<close>

lemma no_irq_loadWord: "no_irq (loadWord x)"
  by (wpsimp simp: no_irq_def wp: loadWord_inv)

lemma no_irq_getActiveIRQ: "no_irq (getActiveIRQ in_kernel)"
  by (wpsimp simp: no_irq_def irq_state_independent_def wp: getActiveIRQ_inv)

lemma no_irq_storeWord: "no_irq (storeWord w p)"
  by (wpsimp simp: storeWord_def wp: no_irq_modify)

crunch ackInterrupt
  for (no_irq) no_irq[intro!, wp, simp]

text \<open>Wide-angle crunch proofs over architecture-specific machine operations for
  @{term no_fail}, @{term empty_fail} and @{term no_irq}}}\<close>

(* Most of the basic machine ops in MachineOps.thy use abstract _impl constants which should never
   be expanded.
   Note: this was generated by running the following, and should likely be updated the same way:
   grep -o "\w\+_impl" MachineOps.thy|sort|uniq|sed "s/^/    /"
   *)
crunch_ignore (valid, empty_fail, no_fail)
  (add:
    addressTranslateS1_impl
    branchFlushRange_impl
    check_export_arch_timer_impl
    cleanByVA_PoU_impl
    cleanCacheRange_PoU_impl
    cleanCacheRange_RAM_impl
    cleanInvalidateCacheRange_RAM_impl
    configureTimer_impl
    dsb_impl
    enableFpuEL01_impl
    fpuThreadDeleteOp_impl
    get_gic_vcpu_ctrl_lr_impl
    initL2Cache_impl
    initTimer_impl
    invalidateCacheRange_I_impl
    invalidateCacheRange_RAM_impl
    invalidateTranslationASID_impl
    invalidateTranslationSingle_impl
    isb_impl
    nativeThreadUsingFPU_impl
    plic_complete_claim_impl
    resetTimer_impl
    set_gic_vcpu_ctrl_apr_impl
    set_gic_vcpu_ctrl_hcr_impl
    set_gic_vcpu_ctrl_lr_impl
    set_gic_vcpu_ctrl_vmcr_impl
    set_gic_vcpu_ctrl_vtr_impl
    setHCR_impl
    setIRQTrigger_impl
    setSCTLR_impl
    setVSpaceRoot_impl
    switchFpuOwner_impl
    writeVCPUHardwareReg_impl
    )

(* Crunches for machine ops without concrete implementations (using _impl or _val).
   List obtained using:
   grep -oE "(\w+_impl)|(get\w+)" MachineOps.thy|sort|uniq|sed "s/_impl//;s/$/,/;s/^/  /"
   with the following manual interventions:
   - remove false positives: get_def, gets_def, getFPUState, getRegister, getRestartPC
   - add read_cntpct
   - remove final comma
   - getActiveIRQ does not preserve no_irq *)
crunch
  addressTranslateS1,
  branchFlushRange,
  check_export_arch_timer,
  cleanByVA_PoU,
  cleanCacheRange_PoU,
  cleanCacheRange_RAM,
  cleanInvalidateCacheRange_RAM,
  configureTimer,
  dsb,
  enableFpuEL01,
  fpuThreadDeleteOp,
  getESR,
  getFAR,
  get_gic_vcpu_ctrl_apr,
  get_gic_vcpu_ctrl_eisr0,
  get_gic_vcpu_ctrl_eisr1,
  get_gic_vcpu_ctrl_hcr,
  get_gic_vcpu_ctrl_lr,
  get_gic_vcpu_ctrl_lr,
  get_gic_vcpu_ctrl_misr,
  get_gic_vcpu_ctrl_vmcr,
  get_gic_vcpu_ctrl_vtr,
  getHSR,
  getMemoryRegions,
  gets,
  getSCTLR,
  initL2Cache,
  initTimer,
  invalidateCacheRange_I,
  invalidateCacheRange_RAM,
  invalidateTranslationASID,
  invalidateTranslationSingle,
  isb,
  nativeThreadUsingFPU,
  plic_complete_claim,
  resetTimer,
  set_gic_vcpu_ctrl_apr,
  set_gic_vcpu_ctrl_hcr,
  set_gic_vcpu_ctrl_lr,
  set_gic_vcpu_ctrl_vmcr,
  set_gic_vcpu_ctrl_vtr,
  setHCR,
  setIRQTrigger,
  setSCTLR,
  setVSpaceRoot,
  switchFpuOwner,
  readVCPUHardwareReg,
  writeVCPUHardwareReg,
  read_cntpct
  for (no_fail) no_fail[intro!, wp, simp]
  and (empty_fail) empty_fail[intro!, wp, simp]
  and (no_irq) no_irq[intro!, wp, simp]
  and device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  and irq_masks[wp]: "\<lambda>s. P (irq_masks s)"
  and underlying_memory_inv[wp]: "\<lambda>s. P (underlying_memory s)"
  (wp: no_irq_bind ignore: empty_fail Nondet_Monad.bind)

crunch getFPUState, getRegister, getRestartPC, setNextPC, ackInterrupt, maskInterrupt
  for (no_fail) no_fail[intro!, wp, simp]
  and (empty_fail) empty_fail[intro!, wp, simp]

crunch ackInterrupt, maskInterrupt
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  and underlying_memory_inv[wp]: "\<lambda>s. P (underlying_memory s)"

crunch ackInterrupt
  for irq_masks[wp]: "\<lambda>s. P (irq_masks s)"

text \<open>Lifting rules\<close>

lemma dmo_machine_state_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P (machine_state s)\<rbrace> do_machine_op f \<lbrace>\<lambda>rv s. Q rv (machine_state s)\<rbrace>"
  unfolding do_machine_op_def by wpsimp (erule use_valid; assumption)

crunch do_machine_op
  for user_frame[wp]: "\<lambda>s. P (in_user_frame p s)"

lemma dmo_valid_machine_state[wp]:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (underlying_memory s)\<rbrace>"
  shows "do_machine_op f \<lbrace>valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift dmo_machine_state_lift assms)

lemma dmo_valid_irq_states[wp]:
  "(\<And>P. f \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>) \<Longrightarrow> do_machine_op f \<lbrace>valid_irq_states\<rbrace>"
  unfolding valid_irq_states_def do_machine_op_def
  by (wpsimp, erule use_valid; assumption)

text \<open>Ops that require machine-ops rules derived above\<close>

\<comment> \<open>These can't be placed into the sections above, as they require the derivation of the machine op
   properties, and those in turn rely on items in specific sections above. There are unlikely to be
   many definitions like this in MachineOps.thy\<close>

crunch clearMemory
  for (empty_fail) empty_fail[intro!, wp, simp]

lemma no_fail_clearMemory[unfolded word_size_bits_def, simp, wp]:
  "no_fail (\<lambda>_. is_aligned p word_size_bits) (clearMemory p b)"
  apply (simp add: clearMemory_def word_size_bits_def mapM_x_mapM)
  apply (rule no_fail_pre)
   apply (wp no_fail_mapM' no_fail_storeWord )
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule aligned_add_aligned)
   apply (simp add: word_size_def)
   apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
  apply simp
  done

lemma no_irq_clearMemory: "no_irq (clearMemory a b)"
  by (wpsimp simp: clearMemory_def no_irq_mapM_x no_irq_storeWord)

text \<open>Misc WP rules\<close>

lemma getActiveIRQ_le_maxIRQ':
  "\<lbrace>\<lambda>s. \<forall>irq > maxIRQ. irq_masks s irq\<rbrace>
    getActiveIRQ in_kernel
   \<lbrace>\<lambda>rv s. \<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wpsimp
  apply (rule ccontr)
  apply (simp add: linorder_not_le)
  done

lemma getActiveIRQ_neq_non_kernel:
  "\<lbrace>\<top>\<rbrace> getActiveIRQ True \<lbrace>\<lambda>rv s. rv \<notin> Some ` non_kernel_IRQs \<rbrace>"
  by (wpsimp simp: getActiveIRQ_def)

lemma dmo_getActiveIRQ_non_kernel[wp]:
  "\<lbrace>\<top>\<rbrace> do_machine_op (getActiveIRQ True)
   \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> irq \<in> non_kernel_IRQs \<longrightarrow> P irq s\<rbrace>"
  unfolding do_machine_op_def
  apply wpsimp
  apply (drule use_valid, rule getActiveIRQ_neq_non_kernel, rule TrueI)
  apply clarsimp
  done

lemma dmo_gets_inv[wp]:
  "do_machine_op (gets f) \<lbrace>P\<rbrace>"
  unfolding do_machine_op_def by (wpsimp simp: simpler_gets_def)

end

arch_requalify_facts
  det_getRegister
  det_setRegister
  det_getRestartPC
  det_setNextPC

end
