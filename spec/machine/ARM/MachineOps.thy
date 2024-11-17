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

abbreviation max_time :: time where
  "max_time \<equiv> max_word"

definition \<mu>s_in_ms :: "64 word" where
  "\<mu>s_in_ms = 1000"

text \<open> This matches @{text "60 * 60 * MS_IN_S * US_IN_MS"} because it should be in micro-seconds. \<close>
definition MAX_PERIOD_US :: "64 word" where
  "MAX_PERIOD_US \<equiv> 60 * 60 * 1000 * 1000"

\<comment> \<open>The following notepad shows that the axioms introduced below, which provide various results
    about several constants and their conversion via us_to_ticks, are consistent.\<close>

notepad begin

define ticks_per_timer_unit :: "64 word" where "ticks_per_timer_unit = of_nat 50"
define timer_unit :: "64 word" where "timer_unit = of_nat 1"
define kernelWCET_us :: "64 word" where "kernelWCET_us = of_nat 100"
define us_to_ticks :: "64 word \<Rightarrow> 64 word" where
  "us_to_ticks = (\<lambda>us. (us * ticks_per_timer_unit) div timer_unit)"

have kernelWCET_us_pos2: "0 < 2 * kernelWCET_us"
  by (simp add: kernelWCET_us_def)

have MIN_BUDGET_le_MAX_PERIOD: "2 * kernelWCET_us \<le> MAX_PERIOD_US"
  by (simp add: kernelWCET_us_def MAX_PERIOD_US_def)

have ticks_per_timer_unit_non_zero: "ticks_per_timer_unit \<noteq> 0"
  by (simp add: ticks_per_timer_unit_def)

have MIN_BUDGET_bound: "2 * unat kernelWCET_us * unat ticks_per_timer_unit < unat max_time"
  apply (subst unat_max_word[symmetric])
  apply clarsimp
  apply (prop_tac "unat kernelWCET_us \<le> 100")
   apply (fastforce simp: kernelWCET_us_def)
  apply (prop_tac "unat ticks_per_timer_unit \<le> 50")
   apply (fastforce simp: ticks_per_timer_unit_def)
  apply (rule_tac y="10000" in le_less_trans)
   apply (rule_tac j1=200 and l1=50 in order.trans[OF mult_le_mono]; fastforce)
  apply simp
  done

have getCurrentTime_buffer_bound:
  "5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit < unat max_time"
  apply (fastforce simp: unat_max_word[symmetric] ticks_per_timer_unit_def MAX_PERIOD_US_def)
  done

have kernelWCET_pos': "0 < us_to_ticks kernelWCET_us"
  apply (clarsimp simp: us_to_ticks_def word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have MIN_BUDGET_pos': "0 < 2 * us_to_ticks kernelWCET_us"
  apply (clarsimp simp: us_to_ticks_def word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have init_domain_time_pos: "0 < us_to_ticks (15 * \<mu>s_in_ms)"
  apply (clarsimp simp: us_to_ticks_def word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: \<mu>s_in_ms_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have init_domain_time_bound: "15 * unat \<mu>s_in_ms * unat ticks_per_timer_unit < unat max_time"
  apply (subst unat_mult_lem'
         | fastforce simp: \<mu>s_in_ms_def ticks_per_timer_unit_def unat_minus_one_word)+
  done

have getCurrentTime_buffer_pos:
  "0 < 5 * us_to_ticks MAX_PERIOD_US"
  apply (fastforce simp: us_to_ticks_def word_less_nat_alt MAX_PERIOD_US_def
                         ticks_per_timer_unit_def timer_unit_def)
  done

end

consts' kernelWCET_us :: ticks

axiomatization where
  kernelWCET_us_pos2: "0 < 2 * kernelWCET_us"
and
  MIN_BUDGET_le_MAX_PERIOD: "2 * kernelWCET_us \<le> MAX_PERIOD_US"

consts' ticks_per_timer_unit :: ticks
consts' timer_unit :: ticks

definition
  "us_to_ticks us = (us * ticks_per_timer_unit) div timer_unit"

axiomatization where
  ticks_per_timer_unit_non_zero: "ticks_per_timer_unit \<noteq> 0"
and
  MIN_BUDGET_bound: "2 * unat kernelWCET_us * unat ticks_per_timer_unit < unat max_time"
and
  \<comment> \<open>the 5 is from time_buffer_const (defined below)\<close>
  getCurrentTime_buffer_bound:
    "5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit < unat max_time"
and
  kernelWCET_pos': "0 < us_to_ticks kernelWCET_us"
and
  MIN_BUDGET_pos': "0 < 2 * us_to_ticks kernelWCET_us"
and
  \<comment> \<open>the 15 is from the domain time of the initial state\<close>
  init_domain_time_pos: "0 < us_to_ticks (15 * \<mu>s_in_ms)"
and
  \<comment> \<open>the 15 is from the domain time of the initial state\<close>
  init_domain_time_bound: "15 * unat \<mu>s_in_ms * unat ticks_per_timer_unit < unat max_time"
and
  \<comment> \<open>the 5 is from time_buffer_const (defined below)\<close>
  getCurrentTime_buffer_pos: "0 < 5 * us_to_ticks MAX_PERIOD_US"

definition "MAX_PERIOD = us_to_ticks MAX_PERIOD_US"

axiomatization
  ticks_to_us :: "ticks \<Rightarrow> ticks"

end_qualify

context Arch begin global_naming ARM

lemma kernelWCET_us_pos:
  "0 < kernelWCET_us"
  using kernelWCET_us_pos2 double_eq_zero_iff word_greater_zero_iff by blast

definition
  "kernelWCET_ticks = us_to_ticks kernelWCET_us"

text \<open>
  It is crucial that time does not overflow, and that overflow does not occur when performing any
  operation which modifies the refill lists. We therefore impose a cap on the time that can be
  returned by getCurrentTime, namely getCurrentTime_buffer. This is chosen to be the greatest word
  t such that if a refill list has its head r_time at t, and satisfies valid_refills, then
  when performing any function which does modify the refill list, overflow does not occur. The
  choice depends heavily on the implementation of refill_budget_check.
 \<close>

abbreviation time_buffer_const where "time_buffer_const \<equiv> 5"

abbreviation (input) getCurrentTime_buffer where
  "getCurrentTime_buffer \<equiv> time_buffer_const * MAX_PERIOD"

lemma replicate_no_overflow:
  "n * unat (a :: ticks) \<le> unat (upper_bound :: ticks)
   \<Longrightarrow> unat (word_of_nat n * a) = n * unat a"
  using le_unat_uoi by fastforce

lemma kernelWCET_ticks_pos2: "0 < 2 * kernelWCET_ticks"
  apply (simp add: kernelWCET_ticks_def)
  using MIN_BUDGET_pos' by simp

lemma getCurrentTime_buffer_nonzero':
  "0 < getCurrentTime_buffer"
  apply (insert getCurrentTime_buffer_pos)
  apply (clarsimp simp: kernelWCET_ticks_def MAX_PERIOD_def)
  done

lemma us_to_ticks_helper:
  "unat a * unat ticks_per_timer_unit \<le> unat max_time
   \<Longrightarrow> unat (us_to_ticks a) \<le> unat a * unat ticks_per_timer_unit"
  apply (clarsimp simp: us_to_ticks_def)
  by (subst unat_div | subst unat_mult_lem' | simp)+

lemma getCurrentTime_buffer_no_overflow:
  "5 * unat MAX_PERIOD < unat max_time"
  apply (insert getCurrentTime_buffer_bound)
  apply (rule_tac y=" 5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit" in le_less_trans;
         fastforce intro: us_to_ticks_helper simp: MAX_PERIOD_def)
  done

lemma MAX_PERIOD_mult:
  "(n :: 64 word) \<le> 5 \<Longrightarrow> unat (n * MAX_PERIOD) = unat n * unat MAX_PERIOD"
  apply (insert getCurrentTime_buffer_bound)
  apply (insert replicate_no_overflow[where n="unat n" and a=MAX_PERIOD and upper_bound=max_time, atomized])
  apply (elim impE)
   apply (clarsimp simp: MAX_PERIOD_def)
   apply (prop_tac "unat n \<le> (5 :: nat)")
    apply (clarsimp simp: word_le_nat_alt)
   apply (prop_tac "unat (us_to_ticks MAX_PERIOD_US) \<le> unat MAX_PERIOD_US * unat ticks_per_timer_unit")
  apply (simp add: us_to_ticks_helper)
   apply (prop_tac "5 * (unat MAX_PERIOD_US * unat ticks_per_timer_unit) \<le> unat max_time")
    apply linarith
   apply (metis (no_types, opaque_lifting) le_trans mult.commute mult_le_mono1)
  by simp

lemma getCurrentTime_buffer_no_overflow':
  "5 * unat MAX_PERIOD = unat getCurrentTime_buffer"
  apply (subst unat_mult_lem')
   apply (metis MAX_PERIOD_mult add.left_neutral order_refl unat_plus_simple unat_sum_boundE
                word_zero_le)
  apply (fastforce simp: us_to_ticks_helper)
  done

lemma us_to_ticks_zero:
  "us_to_ticks 0 = 0"
  by (clarsimp simp: us_to_ticks_def)

lemma unat_div_helper:
  "a * ticks_per_timer_unit \<le> b * ticks_per_timer_unit
   \<Longrightarrow> unat (a * ticks_per_timer_unit div timer_unit) \<le> unat (b * ticks_per_timer_unit div timer_unit)"
  by (simp add: word_le_nat_alt div_le_mono uno_simps(2) word_arith_nat_div)

lemma us_to_ticks_mono:
  "\<lbrakk>a \<le> b; unat b * unat ticks_per_timer_unit \<le> unat max_time\<rbrakk>
    \<Longrightarrow> us_to_ticks a \<le> us_to_ticks b"
  apply (simp add: us_to_ticks_def)
  apply (clarsimp simp: word_le_nat_alt)
  apply (rule unat_div_helper)
  apply (clarsimp simp: word_le_nat_alt)
  by (metis (no_types, opaque_lifting) le_unat_uoi mult_le_mono1 word_arith_nat_defs(2))

lemma divide_le_helper:
  "\<lbrakk>unat a * unat b  \<le> unat (max_word :: 'a :: len word)\<rbrakk>
   \<Longrightarrow> (a :: 'a :: len word) * (b  div c) \<le> a * b div c"
  apply (clarsimp simp: word_le_nat_alt)
  apply (subst unat_div | subst unat_mult_lem')+
  apply (blast intro: div_le_dividend le_trans mult_le_mono2)
  apply (subst unat_div | subst unat_mult_lem' | simp)+
  by (metis (no_types, opaque_lifting) Groups.mult_ac(3) arith_extra_simps(19) div_by_0 div_le_mono
                                       mult_le_mono2 nonzero_mult_div_cancel_left thd)

lemma MIN_BUDGET_helper:
  "2 * us_to_ticks kernelWCET_us \<le> us_to_ticks (2 * kernelWCET_us)"
  apply (clarsimp simp: us_to_ticks_def)
  apply (insert MIN_BUDGET_bound)
  apply (rule_tac order_trans[OF divide_le_helper])
   apply (subst unat_mult_lem' | simp)+
  by (simp add: mult.assoc)


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
    current \<leftarrow> return (min (unat (-(getCurrentTime_buffer + 1))) (last + passed));
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

text \<open>Clear memory contents to recycle it as user memory. Do not yet flush the cache.\<close>
definition
  clearMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
 "clearMemory ptr bytelength \<equiv>
    mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size .e. ptr + (of_nat bytelength) - 1]"

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
  (type) "'a ARM.user_monad" <= (type) "(ARM.register \<Rightarrow> machine_word, 'a) nondet_monad"


end
