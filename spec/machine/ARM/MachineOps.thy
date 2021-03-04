(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Machine Operations"

theory MachineOps
imports
  "../MachineMonad"
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

context Arch begin global_naming ARM

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


consts' maxTimer_us :: "64 word"
consts' timerPrecision :: "64 word"
consts' max_ticks_to_us :: "64 word"
consts' max_us_to_ticks :: "64 word"

end

qualify ARM (in Arch)

type_synonym ticks = "64 word"
type_synonym time  = "64 word"

axiomatization
  kernelWCET_us :: ticks
where
  kernelWCET_us_pos: "0 < kernelWCET_us"
and
  kernelWCET_us_pos2: "0 < 2 * kernelWCET_us"

text \<open>
  This matches @{text "60 * 60 * MS_IN_S * US_IN_MS"} because it should be in micro-seconds.
\<close>
definition
  MAX_PERIOD_US :: "64 word"
where
  "MAX_PERIOD_US \<equiv> 60 * 60 * 1000 * 1000"

axiomatization
  us_to_ticks :: "ticks \<Rightarrow> ticks"
where
  us_to_ticks_mono[intro!]: "mono us_to_ticks"
and
  us_to_ticks_zero[iff]: "us_to_ticks 0 = 0"
and
  us_to_ticks_nonzero: "y \<noteq> 0 \<Longrightarrow> us_to_ticks y \<noteq> 0"
and
  kernelWCET_ticks_no_overflow: "4 * unat (us_to_ticks kernelWCET_us) \<le> unat (max_word :: ticks)"
and
  cur_time_bound_no_overflow: "3 * unat (us_to_ticks MAX_PERIOD_US) + unat (us_to_ticks kernelWCET_us)
                               < unat (max_word :: ticks)"
and
  us_to_ticks_mult: "unat n * unat (us_to_ticks a) \<le> unat (max_word :: ticks)
                     \<Longrightarrow> n * us_to_ticks a = us_to_ticks (n * a)"
and
  cur_time_bound_nonzero: "0 < us_to_ticks kernelWCET_us + 3 * (us_to_ticks MAX_PERIOD_US)"

definition "MAX_PERIOD = us_to_ticks MAX_PERIOD_US"

axiomatization
  ticks_to_us :: "ticks \<Rightarrow> ticks"

end_qualify

context Arch begin global_naming ARM

definition
  "kernelWCET_ticks = us_to_ticks (kernelWCET_us)"

lemma replicate_no_overflow:
  "n * unat (a :: ticks) \<le> unat (upper_bound :: ticks)
   \<Longrightarrow> unat (word_of_int n * a) = n * unat a"
  by (metis (mono_tags, hide_lams) le_unat_uoi of_nat_mult word_of_nat word_unat.Rep_inverse)

lemma kernelWCET_ticks_pos2: "0 < 2 * kernelWCET_ticks"
  apply (simp add: kernelWCET_ticks_def word_less_nat_alt)
  apply (subgoal_tac "unat (2 * us_to_ticks kernelWCET_us) = 2 * unat (us_to_ticks kernelWCET_us)")
   using ARM.kernelWCET_us_pos2 ARM.us_to_ticks_nonzero unat_gt_0 apply force
  apply (subgoal_tac "2 * unat (us_to_ticks kernelWCET_us) \<le> unat (max_word :: ticks)")
   using replicate_no_overflow apply fastforce
  using kernelWCET_ticks_no_overflow by force

lemma cur_time_bound_nonzero':
  "0 < kernelWCET_ticks + 3 * MAX_PERIOD"
  apply (insert cur_time_bound_nonzero)
  apply (clarsimp simp: kernelWCET_ticks_def MAX_PERIOD_def)
  done

lemma cur_time_bound_no_overflow':
  "unat kernelWCET_ticks + 3 * unat MAX_PERIOD = unat (kernelWCET_ticks + 3 * MAX_PERIOD)"
  apply (prop_tac "3 * unat (us_to_ticks MAX_PERIOD_US) = unat (3 * us_to_ticks MAX_PERIOD_US)")
   apply (prop_tac "3 * unat (us_to_ticks MAX_PERIOD_US) \<le> unat (max_word :: 64 word)")
    using cur_time_bound_no_overflow apply linarith
   apply (fastforce dest: replicate_no_overflow[where a="us_to_ticks MAX_PERIOD_US" and n=3])
  apply (insert cur_time_bound_no_overflow)
  apply (clarsimp simp: kernelWCET_ticks_def MAX_PERIOD_def)
  apply (subst unat_add_lem')
   apply (clarsimp simp: max_word_def)
  apply simp
  done

lemma cur_time_bound_minus:
  "- kernelWCET_ticks - 3 * MAX_PERIOD - 1 \<le> - kernelWCET_ticks - 1"
  apply (prop_tac "kernelWCET_ticks \<le> kernelWCET_ticks + 3 * MAX_PERIOD")
   apply (clarsimp simp: word_le_nat_alt)
   using cur_time_bound_no_overflow' apply force
  apply (prop_tac "MAX_PERIOD * 3 \<le> - 1 - kernelWCET_ticks")
   apply (metis le_minus mult.commute word_n1_ge)
  apply (metis (no_types, hide_lams) ab_group_add_class.ab_diff_conv_add_uminus add.assoc
               add.commute mult.commute word_sub_le)
  done

lemma cur_time_bound_minus':
  "- kernelWCET_ticks - 3 * MAX_PERIOD - 1 < - kernelWCET_ticks"
  apply (insert cur_time_bound_minus)
  apply (prop_tac "kernelWCET_ticks \<noteq> 0")
   using us_to_ticks_nonzero kernelWCET_ticks_def kernelWCET_us_pos apply fastforce
  by (simp add: word_leq_minus_one_le)

text \<open>
This encodes the following assumptions:
  a) time increases monotonically,
  b) global 64-bit time does not overflow during the lifetime of the system.
\<close>
definition
  getCurrentTime :: "64 word machine_monad"
where
  "getCurrentTime = do
    modify (\<lambda>s. s \<lparr> time_state := time_state s + 1 \<rparr>);
    passed \<leftarrow> gets $ time_oracle o time_state;
    last' \<leftarrow> gets last_machine_time;
    last \<leftarrow> return (unat last');
    current \<leftarrow> return  (min (2^64 -(unat kernelWCET_ticks + 3 * unat MAX_PERIOD + 1)) (last + passed));
    modify (\<lambda>s. s\<lparr>last_machine_time := of_nat current\<rparr>);
    return (of_nat current)
  od"

consts'
  setDeadline_impl :: "64 word \<Rightarrow> unit machine_rest_monad"

definition
  setDeadline :: "64 word \<Rightarrow> unit machine_monad"
where
  "setDeadline d \<equiv> machine_op_lift (setDeadline_impl d)"

consts'
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

consts' deadlineIRQ :: irq

definition
  "ackDeadlineIRQ \<equiv> ackInterrupt deadlineIRQ"


\<comment> \<open>Interrupt controller operations\<close>

text \<open>
  Interrupts that cannot occur while the kernel is running (e.g. at preemption points),
  but that can occur from user mode. Empty on plain ARMv7.
\<close>
definition
  "non_kernel_IRQs = {}"

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
    if is_masked active_irq \<or> active_irq = 0x3FF \<or> (in_kernel \<and> active_irq \<in> non_kernel_IRQs)
    then return None
    else return ((Some active_irq) :: irq option)
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
  "invalidateCacheRange_I vstart vend pstart \<equiv> cacheRangeOp invalidateByVA_I vstart vend pstart"

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
     cleanCacheRange_PoU ptr (ptr + of_nat bytelength - 1) (addrFromPPtr ptr)
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




section "User Monad"

type_synonym user_context = "register \<Rightarrow> machine_word"

type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition
  getRegister :: "register \<Rightarrow> machine_word user_monad"
where
  "getRegister r \<equiv> gets (\<lambda>uc. uc r)"

definition
  setRegister :: "register \<Rightarrow> machine_word \<Rightarrow> unit user_monad"
where
  "setRegister r v \<equiv> modify (\<lambda>uc. uc (r := v))"

definition
  "getRestartPC \<equiv> getRegister FaultIP"

definition
  "setNextPC \<equiv> setRegister NextIP"

end

translations
  (type) "'a ARM.user_monad" <= (type) "(ARM.register \<Rightarrow> machine_word, 'a) nondet_monad"


end
