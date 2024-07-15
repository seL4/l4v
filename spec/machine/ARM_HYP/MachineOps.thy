(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Machine Operations"

theory MachineOps
imports
  MachineMonad
begin

section "Wrapping and Lifting Machine Operations"

text \<open>
  Most of the machine operations below work on the underspecified
  part of the machine state @{typ machine_state_rest} and cannot fail.
  We could express the latter by type (leaving out the failure flag),
  but if we later wanted to implement them,
  we'd have to set up a new hoare-logic
  framework for that type. So instead, we provide a wrapper for these
  operations that explicitly ignores the fail flag and sets it to
  False. Similarly, these operations never return an empty set of
  follow-on states, which would require the operation to fail.
  So we explicitly make this (non-existing) case a null operation.

  All this is done only to avoid a large number of axioms (2 for each operation).
\<close>

context Arch begin global_naming ARM_HYP

section "The Operations"

consts'
  memory_regions :: "(paddr \<times> paddr) list" (* avail_p_regs *)
  device_regions :: "(paddr \<times> paddr) list" (* dev_p_regs *)

definition
  getMemoryRegions :: "(paddr * paddr) list machine_monad"
  where "getMemoryRegions \<equiv> return memory_regions"

consts'
  getDeviceRegions_impl :: "unit machine_rest_monad"
  getDeviceRegions_val :: "machine_state \<Rightarrow> (paddr * paddr) list"

definition
  getDeviceRegions :: "(paddr * paddr) list machine_monad"
where
  "getDeviceRegions \<equiv> return device_regions"

consts'
  getKernelDevices_impl :: "unit machine_rest_monad"
  getKernelDevices_val :: "machine_state \<Rightarrow> (paddr * machine_word) list"

definition
  getKernelDevices :: "(paddr * machine_word) list machine_monad"
where
  "getKernelDevices \<equiv> do
    machine_op_lift getKernelDevices_impl;
    gets getKernelDevices_val
  od"

consts'
  setIRQTrigger_impl :: "irq \<Rightarrow> bool \<Rightarrow> unit machine_rest_monad"

definition
  setIRQTrigger :: "irq \<Rightarrow> bool \<Rightarrow> unit machine_monad"
where
  "setIRQTrigger irq trigger \<equiv> machine_op_lift (setIRQTrigger_impl irq trigger)"

definition
  loadWord :: "machine_word \<Rightarrow> machine_word machine_monad"
  where "loadWord p \<equiv> do m \<leftarrow> gets underlying_memory;
                         assert (p && mask 2 = 0);
                         return (word_rcat [m (p + 3), m (p + 2), m (p + 1), m p])
                      od"

definition
  storeWord :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where "storeWord p w \<equiv> do
                            assert (p && mask 2 = 0);
                            modify (underlying_memory_update (\<lambda>m.
                                      m(p := word_rsplit w ! 3,
                                        p + 1 := word_rsplit w ! 2,
                                        p + 2 := word_rsplit w ! 1,
                                        p + 3 := word_rsplit w ! 0)))
                         od"

lemma loadWord_storeWord_is_return:
  "p && mask 2 = 0 \<Longrightarrow> (do w \<leftarrow> loadWord p; storeWord p w od) = return ()"
  apply (rule ext)
  apply (simp add: loadWord_def storeWord_def bind_def assert_def return_def
    modify_def gets_def get_def eval_nat_numeral put_def)
  apply (simp add: word_rsplit_rcat_size word_size)
  done

text \<open>This instruction is required in the simulator, only.\<close>
definition
  storeWordVM :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where "storeWordVM w p \<equiv> return ()"

consts'
  configureTimer_impl :: "unit machine_rest_monad"
  configureTimer_val :: "machine_state \<Rightarrow> irq"

definition
  configureTimer :: "irq machine_monad"
where
  "configureTimer \<equiv> do
    machine_op_lift configureTimer_impl;
    gets configureTimer_val
  od"

consts' (* XXX: replaces configureTimer in new boot code
          TODO: remove configureTimer when haskell updated *)
  initTimer_impl :: "unit machine_rest_monad"
definition
  initTimer :: "unit machine_monad"
where "initTimer \<equiv> machine_op_lift initTimer_impl"

consts'
  resetTimer_impl :: "unit machine_rest_monad"

definition
  resetTimer :: "unit machine_monad"
where "resetTimer \<equiv> machine_op_lift resetTimer_impl"

consts'
  writeTTBR0_impl :: "paddr \<Rightarrow> unit machine_rest_monad"
definition
  writeTTBR0 :: "paddr \<Rightarrow> unit machine_monad"
where "writeTTBR0 pd \<equiv> machine_op_lift (writeTTBR0_impl pd)"


consts'
  setHardwareASID_impl :: "hardware_asid \<Rightarrow> unit machine_rest_monad"
definition
  setHardwareASID:: "hardware_asid \<Rightarrow> unit machine_monad"
where "setHardwareASID a \<equiv> machine_op_lift (setHardwareASID_impl a)"


(* Memory Barriers *)


consts'
  isb_impl :: "unit machine_rest_monad"
definition
  isb :: "unit machine_monad"
where "isb \<equiv> machine_op_lift isb_impl"

consts'
  dsb_impl :: "unit machine_rest_monad"
definition
  dsb :: "unit machine_monad"
where "dsb \<equiv> machine_op_lift dsb_impl"

consts'
  dmb_impl :: "unit machine_rest_monad"
definition
  dmb :: "unit machine_monad"
where "dmb \<equiv> machine_op_lift dmb_impl"

consts'
  setCurrentPDPL2_impl :: "paddr \<Rightarrow> unit machine_rest_monad"
definition
  setCurrentPDPL2 :: "paddr \<Rightarrow> unit machine_monad"
where "setCurrentPDPL2 pd \<equiv> machine_op_lift (setCurrentPDPL2_impl pd)"

consts'
  invalidateLocalTLB_impl :: "unit machine_rest_monad"
definition
  invalidateLocalTLB :: "unit machine_monad"
where "invalidateLocalTLB \<equiv> machine_op_lift invalidateLocalTLB_impl"


consts'
  invalidateLocalTLB_ASID_impl :: "hardware_asid \<Rightarrow> unit machine_rest_monad"
definition
  invalidateLocalTLB_ASID :: "hardware_asid \<Rightarrow> unit machine_monad"
where "invalidateLocalTLB_ASID a \<equiv> machine_op_lift (invalidateLocalTLB_ASID_impl a)"


(* C implementation takes one argument, which is w || a *)
consts'
  invalidateLocalTLB_VAASID_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  invalidateLocalTLB_VAASID :: "machine_word \<Rightarrow> unit machine_monad"
where "invalidateLocalTLB_VAASID w \<equiv> machine_op_lift (invalidateLocalTLB_VAASID_impl w)"

consts'
  cleanByVA_impl :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  cleanByVA :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "cleanByVA w p \<equiv> machine_op_lift (cleanByVA_impl w p)"

consts'
  cleanByVA_PoU_impl :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  cleanByVA_PoU :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "cleanByVA_PoU w p \<equiv> machine_op_lift (cleanByVA_PoU_impl w p)"

consts'
  invalidateByVA_impl :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  invalidateByVA :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "invalidateByVA w p \<equiv> machine_op_lift (invalidateByVA_impl w p)"

consts'
  invalidateByVA_I_impl :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  invalidateByVA_I :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "invalidateByVA_I w p \<equiv> machine_op_lift (invalidateByVA_I_impl w p)"

consts'
  invalidate_I_PoU_impl :: "unit machine_rest_monad"
definition
  invalidate_I_PoU :: "unit machine_monad"
where "invalidate_I_PoU \<equiv> machine_op_lift invalidate_I_PoU_impl"

consts'
  cleanInvalByVA_impl :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  cleanInvalByVA :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "cleanInvalByVA w p \<equiv> machine_op_lift (cleanInvalByVA_impl w p)"

consts'
  branchFlush_impl :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  branchFlush :: "machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "branchFlush w p \<equiv> machine_op_lift (branchFlush_impl w p)"

consts'
  clean_D_PoU_impl :: "unit machine_rest_monad"
definition
  clean_D_PoU :: "unit machine_monad"
where "clean_D_PoU \<equiv> machine_op_lift clean_D_PoU_impl"

consts'
  cleanInvalidate_D_PoC_impl :: "unit machine_rest_monad"
definition
  cleanInvalidate_D_PoC :: "unit machine_monad"
where "cleanInvalidate_D_PoC \<equiv> machine_op_lift cleanInvalidate_D_PoC_impl"

consts'
  cleanInvalidateL2Range_impl :: "paddr \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  cleanInvalidateL2Range :: "paddr \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "cleanInvalidateL2Range w p \<equiv> machine_op_lift (cleanInvalidateL2Range_impl w p)"

consts'
  invalidateL2Range_impl :: "paddr \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  invalidateL2Range :: "paddr \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "invalidateL2Range w p \<equiv> machine_op_lift (invalidateL2Range_impl w p)"

consts'
  cleanL2Range_impl :: "paddr \<Rightarrow> paddr \<Rightarrow> unit machine_rest_monad"
definition
  cleanL2Range :: "paddr \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where "cleanL2Range w p \<equiv> machine_op_lift (cleanL2Range_impl w p)"

consts'
  initL2Cache_impl :: "unit machine_rest_monad"
definition
  initL2Cache :: "unit machine_monad"
where "initL2Cache \<equiv> machine_op_lift initL2Cache_impl"

definition
  clearExMonitor :: "unit machine_monad"
where "clearExMonitor \<equiv> modify (\<lambda>s. s \<lparr> exclusive_state := default_exclusive_state \<rparr>)"

consts'
  flushBTAC_impl :: "unit machine_rest_monad"
definition
  flushBTAC :: "unit machine_monad"
where "flushBTAC \<equiv> machine_op_lift flushBTAC_impl"

consts'
  initIRQController_impl :: "unit machine_rest_monad"
definition
  initIRQController :: "unit machine_monad"
where "initIRQController \<equiv> machine_op_lift initIRQController_impl"

definition
  IRQ :: "irq \<Rightarrow> irq"
where "IRQ \<equiv> id"

consts'
  writeContextID_impl :: "unit machine_rest_monad"
definition
  writeContextID :: "unit machine_monad"
where "writeContextID \<equiv> machine_op_lift writeContextID_impl"

lemmas cache_machine_op_defs = isb_def dsb_def dmb_def writeContextID_def flushBTAC_def
                               clearExMonitor_def cleanL2Range_def invalidateL2Range_def
                               cleanInvalidateL2Range_def cleanInvalidate_D_PoC_def
                               clean_D_PoU_def branchFlush_def cleanInvalByVA_def
                               invalidate_I_PoU_def invalidateByVA_I_def invalidateByVA_def
                               cleanByVA_PoU_def cleanByVA_def invalidateLocalTLB_VAASID_def
                               invalidateLocalTLB_ASID_def invalidateLocalTLB_def
consts'
  IFSR_val :: "machine_state \<Rightarrow> machine_word"
  DFSR_val :: "machine_state \<Rightarrow> machine_word"
  FAR_val :: "machine_state \<Rightarrow> machine_word"

definition
  getIFSR :: "machine_word machine_monad"
  where "getIFSR \<equiv> gets IFSR_val"

definition
  getDFSR :: "machine_word machine_monad"
  where "getDFSR \<equiv> gets DFSR_val"

definition
  getFAR :: "machine_word machine_monad"
  where "getFAR \<equiv> gets FAR_val"

definition
  debugPrint :: "unit list \<Rightarrow> unit machine_monad"
where
  debugPrint_def[simp]:
 "debugPrint \<equiv> \<lambda>message. return ()"

consts'
  ackInterrupt_impl :: "irq \<Rightarrow> unit machine_rest_monad"
definition
  ackInterrupt :: "irq \<Rightarrow> unit machine_monad"
where
  "ackInterrupt irq \<equiv> machine_op_lift (ackInterrupt_impl irq)"

consts'
  TPIDRURO_val :: "machine_state \<Rightarrow> machine_word"
definition
  getTPIDRURO :: "machine_word machine_monad"
where "getTPIDRURO \<equiv> gets TPIDRURO_val"

consts'
  setTPIDRURO_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  setTPIDRURO :: "machine_word \<Rightarrow> unit machine_monad"
where
  "setTPIDRURO w \<equiv> machine_op_lift (setTPIDRURO_impl w)"

\<comment> \<open>Interrupt controller operations\<close>

text \<open>
  Interrupts that cannot occur while the kernel is running (e.g. at preemption points),
  but that can occur from user mode.
\<close>
definition
  "non_kernel_IRQs = {irqVGICMaintenance, irqVTimerEvent}"

text \<open>
  @{term getActiveIRQ} is now derministic.
  It 'updates' the irq state to the reflect the passage of
  time since last the irq was gotten, then it gets the active
  IRQ (if there is one).
\<close>
definition
  getActiveIRQ :: "bool \<Rightarrow> (irq option) machine_monad"
where
  "getActiveIRQ in_kernel \<equiv> do
    is_masked \<leftarrow> gets $ irq_masks;
    modify (\<lambda>s. s \<lparr> irq_state := irq_state s + 1 \<rparr>);
    active_irq \<leftarrow> gets $ irq_oracle \<circ> irq_state;
    if is_masked active_irq \<or> (in_kernel \<and> active_irq \<in> non_kernel_IRQs)
    then return None
    else return (Some active_irq)
  od"

definition
  maskInterrupt :: "bool \<Rightarrow> irq \<Rightarrow> unit machine_monad"
where
  "maskInterrupt m irq \<equiv>
  modify (\<lambda>s. s \<lparr> irq_masks := (irq_masks s) (irq := m) \<rparr>)"

definition
  lineStart :: "machine_word \<Rightarrow> machine_word"
where
  "lineStart addr = (addr >> cacheLineBits) << cacheLineBits"

text \<open>
  Performs the given operation on every cache line that intersects the
  supplied range.
\<close>
definition
  cacheRangeOp :: "(machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad)
                 \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "cacheRangeOp operation vstart vend pstart \<equiv>
    let pend = pstart + (vend - vstart);
        vptrs = [lineStart vstart, lineStart vstart + of_nat cacheLine .e. lineStart vend];
        pptrs = [lineStart pstart, lineStart pstart + of_nat cacheLine .e. lineStart pend]
    in mapM_x (\<lambda>(v, p). operation v p) (zip vptrs pptrs)"

definition
  cleanCacheRange_PoC :: "machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "cleanCacheRange_PoC vstart vend pstart \<equiv> cacheRangeOp cleanByVA vstart vend pstart"

definition
  cleanInvalidateCacheRange_RAM :: "machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "cleanInvalidateCacheRange_RAM vstart vend pstart \<equiv> do
    cleanCacheRange_PoC vstart vend pstart;
    dsb;
    cleanInvalidateL2Range pstart (pstart + (vend - vstart));
    cacheRangeOp cleanInvalByVA vstart vend pstart;
    dsb
  od"

definition
  cleanCacheRange_RAM :: "machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "cleanCacheRange_RAM vstart vend pstart \<equiv> do
    cleanCacheRange_PoC vstart vend pstart;
    dsb;
    cleanL2Range pstart (pstart + (vend - vstart))
  od"

definition
  cleanCacheRange_PoU :: "machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "cleanCacheRange_PoU vstart vend pstart \<equiv> cacheRangeOp cleanByVA_PoU vstart vend pstart"

definition
  invalidateCacheRange_RAM :: "machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "invalidateCacheRange_RAM vstart vend pstart \<equiv> do
    when (vstart \<noteq> lineStart vstart) $
        cleanCacheRange_RAM vstart vstart pstart;
    when (vend + 1 \<noteq> lineStart (vend + 1)) $
        cleanCacheRange_RAM (lineStart vend) (lineStart vend)
           (pstart + ((lineStart vend) - vstart));
    invalidateL2Range pstart (pstart + (vend - vstart));
    cacheRangeOp invalidateByVA vstart vend pstart;
    dsb
  od"

definition
  invalidateCacheRange_I :: "machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "invalidateCacheRange_I vstart vend pstart \<equiv> invalidate_I_PoU"
  (* for other than A53 and A35: "cacheRangeOp invalidateByVA_I vstart vend pstart" *)

definition
  branchFlushRange :: "machine_word \<Rightarrow> machine_word \<Rightarrow> paddr \<Rightarrow> unit machine_monad"
where
  "branchFlushRange vstart vend pstart \<equiv> cacheRangeOp branchFlush vstart vend pstart"

definition
  cleanCaches_PoU :: "unit machine_monad"
where
  "cleanCaches_PoU \<equiv> do
    dsb;
    clean_D_PoU;
    dsb;
    invalidate_I_PoU;
    dsb
  od"

definition
  cleanInvalidateL1Caches :: "unit machine_monad"
where
  "cleanInvalidateL1Caches \<equiv> do
    dsb;
    cleanInvalidate_D_PoC;
    dsb;
    invalidate_I_PoU;
    dsb
  od"

section "Memory Clearance"

text \<open>Clear memory contents to recycle it as user memory\<close>
definition
  clearMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
 "clearMemory ptr bytelength \<equiv>
  do mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size .e. ptr + (of_nat bytelength) - 1];
     cleanCacheRange_RAM ptr (ptr + of_nat bytelength - 1) (addrFromPPtr ptr)
  od"

definition
  clearMemoryVM :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
  "clearMemoryVM ptr bits \<equiv> return ()"

text \<open>
  Initialize memory to be used as user memory.
  Note that zeroing out the memory is redundant in the specifications.
  In any case, we cannot abstract from the call to cleanCacheRange,
  which appears in the implementation.
\<close>
abbreviation (input) "initMemory == clearMemory"

text \<open>
  Free memory that had been initialized as user memory.
  While freeing memory is a no-(in) the implementation,
  we zero out the underlying memory in the specifications to avoid garbage.
  If we know that there is no garbage,
  we can compute from the implementation state
  what the exact memory content in the specifications is.
\<close>
definition
  freeMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
 "freeMemory ptr bits \<equiv>
  mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size  .e.  ptr + 2 ^ bits - 1]"

section "Platform specific definitions for TK1 (ARM with Hypervisor extensions)"

consts'
  writeContextIDAndPD_impl :: "hardware_asid \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition
  writeContextIDAndPD :: "hardware_asid \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where "writeContextIDAndPD a b \<equiv> machine_op_lift (writeContextIDAndPD_impl a b)"

consts'
  HSR_val :: "machine_state \<Rightarrow> machine_word"
  HDFAR_val :: "machine_state \<Rightarrow> machine_word"
  SCTLR_val :: "machine_state \<Rightarrow> machine_word"
  ACTLR_val :: "machine_state \<Rightarrow> machine_word"

definition
  getHSR :: "machine_word machine_monad"
where "getHSR \<equiv> gets HSR_val"

definition
  getHDFAR :: "machine_word machine_monad"
where "getHDFAR \<equiv> gets HDFAR_val"

consts'
  setHCR_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  setHCR :: "machine_word \<Rightarrow> unit machine_monad"
where
  "setHCR w \<equiv> machine_op_lift (setHCR_impl w)"

consts'
  addressTranslateS1_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
  addressTranslateS1_val :: "machine_word \<Rightarrow> machine_state \<Rightarrow> machine_word"
definition
  addressTranslateS1 :: "machine_word \<Rightarrow> machine_word machine_monad"
where
  "addressTranslateS1 w \<equiv> do
    machine_op_lift (addressTranslateS1_impl w);
    gets (addressTranslateS1_val w)
  od"

definition
  getSCTLR :: "machine_word machine_monad"
where "getSCTLR \<equiv> gets SCTLR_val"

consts'
  setSCTLR_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  setSCTLR :: "machine_word \<Rightarrow> unit machine_monad"
where
  "setSCTLR w \<equiv> machine_op_lift (setSCTLR_impl w)"

definition
  vgic_irq_active :: "machine_word"
where
  "vgic_irq_active \<equiv> 2 << 28"

definition
  vgic_irq_mask :: "machine_word"
where
  "vgic_irq_mask \<equiv> 3 << 28"

consts'
  gic_vcpu_ctrl_hcr_val :: "machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_hcr :: "machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_hcr \<equiv> gets gic_vcpu_ctrl_hcr_val"

consts'
  set_gic_vcpu_ctrl_hcr_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  set_gic_vcpu_ctrl_hcr :: "machine_word \<Rightarrow> unit machine_monad"
where
  "set_gic_vcpu_ctrl_hcr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_hcr_impl w)"

consts'
  gic_vcpu_ctrl_vmcr_val :: "machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_vmcr :: "machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_vmcr \<equiv> gets gic_vcpu_ctrl_vmcr_val"

consts'
  set_gic_vcpu_ctrl_vmcr_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  set_gic_vcpu_ctrl_vmcr :: "machine_word \<Rightarrow> unit machine_monad"
where
  "set_gic_vcpu_ctrl_vmcr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_vmcr_impl w)"

consts'
  gic_vcpu_ctrl_apr_val :: "machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_apr :: "machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_apr \<equiv> gets gic_vcpu_ctrl_apr_val"

consts'
  set_gic_vcpu_ctrl_apr_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  set_gic_vcpu_ctrl_apr :: "machine_word \<Rightarrow> unit machine_monad"
where
  "set_gic_vcpu_ctrl_apr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_apr_impl w)"

consts'
  gic_vcpu_ctrl_vtr_val :: "machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_vtr :: "machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_vtr \<equiv> gets gic_vcpu_ctrl_vtr_val"

consts'
  set_gic_vcpu_ctrl_vtr_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  set_gic_vcpu_ctrl_vtr :: "machine_word \<Rightarrow> unit machine_monad"
where
  "set_gic_vcpu_ctrl_vtr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_vtr_impl w)"

consts'
  gic_vcpu_ctrl_misr_val :: "machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_misr :: "machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_misr \<equiv> gets gic_vcpu_ctrl_misr_val"

consts'
  gic_vcpu_ctrl_eisr0_val :: "machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_eisr0 :: "machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_eisr0 \<equiv> gets gic_vcpu_ctrl_eisr0_val"

consts'
  gic_vcpu_ctrl_eisr1_val :: "machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_eisr1 :: "machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_eisr1 \<equiv> gets gic_vcpu_ctrl_eisr1_val"

consts'
  get_gic_vcpu_ctrl_lr_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
  gic_vcpu_ctrl_lr_val :: "machine_word \<Rightarrow> machine_state \<Rightarrow> machine_word"
definition
  get_gic_vcpu_ctrl_lr :: "machine_word \<Rightarrow> machine_word machine_monad"
where
  "get_gic_vcpu_ctrl_lr n \<equiv> do
      machine_op_lift (get_gic_vcpu_ctrl_lr_impl n);
      gets (gic_vcpu_ctrl_lr_val n)
    od"

consts'
  set_gic_vcpu_ctrl_lr_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition
  set_gic_vcpu_ctrl_lr :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where
  "set_gic_vcpu_ctrl_lr n w  \<equiv> machine_op_lift (set_gic_vcpu_ctrl_lr_impl n w)"

subsection "Virtual Timer"

consts'
  cntv_cval_64_val :: "machine_state \<Rightarrow> 64 word"
definition
  get_cntv_cval_64 :: "64 word machine_monad"
where
  "get_cntv_cval_64 \<equiv> gets cntv_cval_64_val"

consts'
  set_cntv_cval_64_impl :: "64 word \<Rightarrow> unit machine_rest_monad"
definition
  set_cntv_cval_64 :: "64 word \<Rightarrow> unit machine_monad"
where
  "set_cntv_cval_64 w \<equiv> machine_op_lift (set_cntv_cval_64_impl w)"

consts'
  cntv_off_64_val :: "machine_state \<Rightarrow> 64 word"
definition
  get_cntv_off_64 :: "64 word machine_monad"
where
  "get_cntv_off_64 \<equiv> gets cntv_off_64_val"

consts'
  set_cntv_off_64_impl :: "64 word \<Rightarrow> unit machine_rest_monad"
definition
  set_cntv_off_64 :: "64 word \<Rightarrow> unit machine_monad"
where
  "set_cntv_off_64 w \<equiv> machine_op_lift (set_cntv_off_64_impl w)"

consts'
  read_cntpct_val :: "machine_state \<Rightarrow> 64 word"
definition
  read_cntpct :: "64 word machine_monad"
where
  "read_cntpct \<equiv> gets read_cntpct_val"

subsection "Hypervisor Banked Registers"

consts'
  vcpuHardwareReg_val :: "vcpureg \<Rightarrow> machine_state \<Rightarrow> machine_word"
definition
  readVCPUHardwareReg :: "vcpureg \<Rightarrow> machine_word machine_monad"
where
  "readVCPUHardwareReg reg \<equiv> gets (vcpuHardwareReg_val reg)"

consts'
  writeVCPUHardwareReg_impl :: "vcpureg \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition
  writeVCPUHardwareReg :: "vcpureg \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where
  "writeVCPUHardwareReg reg val \<equiv> machine_op_lift (writeVCPUHardwareReg_impl reg val)"

section "User Monad"

type_synonym user_regs = "register \<Rightarrow> machine_word"

datatype user_context = UserContext (user_regs : user_regs)

type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition getRegister :: "register \<Rightarrow> machine_word user_monad" where
  "getRegister r \<equiv> gets (\<lambda>s. user_regs s r)"

definition modify_registers :: "(user_regs \<Rightarrow> user_regs) \<Rightarrow> user_context \<Rightarrow> user_context" where
  "modify_registers f uc \<equiv> UserContext (f (user_regs uc))"

definition setRegister :: "register \<Rightarrow> machine_word \<Rightarrow> unit user_monad" where
  "setRegister r v \<equiv> modify (\<lambda>s. UserContext ((user_regs s) (r := v)))"

definition
  "getRestartPC \<equiv> getRegister FaultIP"

definition
  "setNextPC \<equiv> setRegister NextIP"

end

translations
  (type) "'a ARM_HYP.user_monad" <= (type) "(ARM_HYP.register \<Rightarrow> machine_word, 'a) nondet_monad"


end
