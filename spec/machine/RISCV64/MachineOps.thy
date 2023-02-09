(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Machine Operations"

theory MachineOps
imports
  "Word_Lib.WordSetup"
  "Monads.NonDetMonad"
  MachineMonad
begin

section "Wrapping and Lifting Machine Operations"

text \<open>
  Most of the machine operations below work on the underspecified part of the machine state @{typ
  machine_state_rest} and cannot fail. We could express the latter by type (leaving out the failure
  flag), but if we later wanted to implement them, we'd have to set up a new Hoare logic framework
  for that type. So instead, we provide a wrapper for these operations that explicitly ignores the
  fail flag and sets it to False. Similarly, these operations never return an empty set of follow-on
  states, which would require the operation to fail. So we explicitly make this (non-existing) case
  a null operation.

  All this is done only to avoid a large number of axioms (2 for each operation).
\<close>

context Arch begin global_naming RISCV64

section "The Operations"

subsection "Memory"

definition loadWord :: "machine_word \<Rightarrow> machine_word machine_monad"
  where
  "loadWord p \<equiv> do
     m \<leftarrow> gets underlying_memory;
     assert (p && mask 3 = 0);
     return (word_rcat (map (\<lambda>i. m (p + (7 - of_int i))) [0 .. 7]))
   od"

definition storeWord :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where
  "storeWord p w \<equiv> do
     assert (p && mask 3 = 0);
     modify (underlying_memory_update
              (fold (\<lambda>i m. m((p + (of_int i)) := word_rsplit w ! (7 - nat i))) [0 .. 7]))
   od"

lemma upto0_7_def:
  "[0..7] = [0,1,2,3,4,5,6,7]" by eval

lemma loadWord_storeWord_is_return:
  "p && mask 3 = 0 \<Longrightarrow> (do w \<leftarrow> loadWord p; storeWord p w od) = return ()"
  by (auto simp: loadWord_def storeWord_def bind_def assert_def return_def word_rsplit_rcat_size
                 modify_def gets_def get_def eval_nat_numeral put_def upto0_7_def word_size)

consts' memory_regions :: "(paddr \<times> paddr) list"
definition getMemoryRegions :: "(paddr * paddr) list machine_monad"
  where
  "getMemoryRegions \<equiv> return memory_regions"

text \<open>This instruction is required in the simulator, only.\<close>
definition storeWordVM :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where
  "storeWordVM w p \<equiv> return ()"


subsection "Timer"

consts' configureTimer_impl :: "unit machine_rest_monad"
consts' configureTimer_val :: "machine_state \<Rightarrow> irq"
definition configureTimer :: "irq machine_monad"
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

qualify RISCV64 (in Arch)

type_synonym ticks = "64 word"
type_synonym time  = "64 word"

abbreviation max_time :: time where
  "max_time \<equiv> max_word"

\<comment> \<open>The following notepad shows that the axioms introduced below, which provide various results
    about several constants and their conversion via us_to_ticks, are consistent.\<close>

notepad begin

define ticks_per_timer_unit :: "64 word" where "ticks_per_timer_unit = of_nat 50"
define timer_unit :: "64 word" where "timer_unit = of_nat 1"
define kernelWCET_us :: "64 word" where "kernelWCET_us = of_nat 100"
define MAX_PERIOD_US :: "64 word" where "MAX_PERIOD_US = 60 * 60 * 1000 * 1000"
define \<mu>s_in_ms :: "64 word" where "\<mu>s_in_ms = 1000"

have ticks_per_timer_unit_non_zero:
  "ticks_per_timer_unit \<noteq> 0"
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
  "unat kernelWCET_us * unat ticks_per_timer_unit
    + 5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit
   < unat max_time"
  apply (subst unat_max_word[symmetric])
  apply clarsimp
  apply (rule_tac j1=5000 and l1="5 * 60 * 60 * 1000 * 1000 * 50"
               in order.strict_trans1[OF add_le_mono])
    apply (fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def)
   apply (fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def MAX_PERIOD_US_def)
  apply linarith
  done

have kernelWCET_pos': "0 < (kernelWCET_us * ticks_per_timer_unit) div timer_unit"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have MIN_BUDGET_pos': "0 < 2 * ((kernelWCET_us * ticks_per_timer_unit) div timer_unit)"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have domain_time_pos: "0 < ((15 * \<mu>s_in_ms) * ticks_per_timer_unit) div timer_unit"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: \<mu>s_in_ms_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have getCurrentTime_buffer_pos:
  "0 < (kernelWCET_us * ticks_per_timer_unit) div timer_unit
       + 5 * (MAX_PERIOD_US * ticks_per_timer_unit div timer_unit)"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_add_lem'' | subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def MAX_PERIOD_US_def ticks_per_timer_unit_def
                           timer_unit_def unat_minus_one_word)+
  done

have MIN_BUDGET_le_MAX_PERIOD:
  "2 * kernelWCET_us \<le> MAX_PERIOD_US"
  by (simp add: kernelWCET_us_def MAX_PERIOD_US_def)

end

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

definition "\<mu>s_in_ms = 1000"

consts' ticks_per_timer_unit :: ticks
consts' timer_unit :: ticks

definition
  "us_to_ticks us = (us * ticks_per_timer_unit) div timer_unit"

axiomatization where
  ticks_per_timer_unit_non_zero: "ticks_per_timer_unit \<noteq> 0"
and
  MIN_BUDGET_bound: "2 * unat kernelWCET_us * unat ticks_per_timer_unit < unat max_time"
and
  getCurrentTime_buffer_bound:
    "unat kernelWCET_us * unat ticks_per_timer_unit
      + 5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit
     < unat max_time"
and
  kernelWCET_pos': "0 < us_to_ticks kernelWCET_us"
and
  MIN_BUDGET_pos': "0 < 2 * us_to_ticks kernelWCET_us"
and
  domain_time_pos: "0 < us_to_ticks (15 * \<mu>s_in_ms)"
and
  getCurrentTime_buffer_pos: "0 < us_to_ticks kernelWCET_us + 5 * us_to_ticks MAX_PERIOD_US"
and
  MIN_BUDGET_le_MAX_PERIOD: "2 * kernelWCET_us \<le> MAX_PERIOD_US"

definition "MAX_PERIOD = us_to_ticks MAX_PERIOD_US"

axiomatization
  ticks_to_us :: "ticks \<Rightarrow> ticks"

end_qualify

context Arch begin global_naming RISCV64

definition
  "kernelWCET_ticks = us_to_ticks (kernelWCET_us)"

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
  "getCurrentTime_buffer \<equiv> kernelWCET_ticks + time_buffer_const * MAX_PERIOD"

lemma replicate_no_overflow:
  "n * unat (a :: ticks) \<le> unat (upper_bound :: ticks)
   \<Longrightarrow> unat (of_nat n * a) = n * unat a"
  by (metis (mono_tags, opaque_lifting) le_unat_uoi of_nat_mult word_unat.Rep_inverse)

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
  "unat kernelWCET_ticks + 5 * unat MAX_PERIOD < unat max_time"
  apply (insert getCurrentTime_buffer_bound)
  by (rule_tac j1="unat kernelWCET_us * unat ticks_per_timer_unit"
           and l1="5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit"
            in order.strict_trans1[OF add_le_mono]
      ; fastforce simp: kernelWCET_ticks_def MAX_PERIOD_def
                 intro: us_to_ticks_helper)

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
  by (metis word_unat.Rep_inverse)

lemma getCurrentTime_buffer_no_overflow':
  "unat kernelWCET_ticks + 5 * unat MAX_PERIOD = unat getCurrentTime_buffer"
  apply (subst unat_add_lem'')
   apply (insert getCurrentTime_buffer_bound)
   apply (clarsimp simp: MAX_PERIOD_mult[where n=5] kernelWCET_ticks_def MAX_PERIOD_def)
   apply (drule less_imp_le)
   apply (rule_tac j1="unat kernelWCET_us * unat ticks_per_timer_unit"
               and l1="5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit"
                in order.trans[OF add_le_mono])
     apply (fastforce simp: us_to_ticks_helper)
    apply (subst unat_div | subst unat_mult_lem')+
     apply (metis MAX_PERIOD_def MAX_PERIOD_mult add.left_neutral order_refl unat_plus_simple
                  unat_sum_boundE word_zero_le)
    apply (fastforce simp: us_to_ticks_helper)
   apply simp
  apply (clarsimp simp: MAX_PERIOD_mult kernelWCET_ticks_def)
  done

lemma getCurrentTime_buffer_no_overflow'_stronger:
  "unat (kernelWCET_ticks + 5 * MAX_PERIOD + 1) = unat kernelWCET_ticks + unat (5 * MAX_PERIOD) + 1"
  apply (subst unat_add_lem'')
   apply (subst getCurrentTime_buffer_no_overflow'[symmetric])
   apply (insert getCurrentTime_buffer_bound)
   apply (prop_tac "unat kernelWCET_ticks \<le> unat kernelWCET_us * unat ticks_per_timer_unit")
    apply (fastforce intro: us_to_ticks_helper
                      simp: kernelWCET_ticks_def)
   apply (prop_tac "5 * unat MAX_PERIOD \<le> 5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit")
    apply (fastforce intro: us_to_ticks_helper
                      simp: MAX_PERIOD_def)
  apply fastforce
  apply (insert getCurrentTime_buffer_no_overflow')
  apply (clarsimp simp: MAX_PERIOD_mult kernelWCET_ticks_def)
  done

lemma getCurrentTime_buffer_minus:
  "- kernelWCET_ticks - 5 * MAX_PERIOD - 1 \<le> - kernelWCET_ticks - 1"
  apply (prop_tac "kernelWCET_ticks \<le> kernelWCET_ticks + 5 * MAX_PERIOD")
   apply (clarsimp simp: word_le_nat_alt)
   using getCurrentTime_buffer_no_overflow' apply force
  apply (prop_tac "MAX_PERIOD * 5 \<le> - 1 - kernelWCET_ticks")
   apply (metis le_minus mult.commute word_n1_ge)
  apply (metis (no_types, opaque_lifting) ab_group_add_class.ab_diff_conv_add_uminus add.assoc
               add.commute mult.commute word_sub_le)
  done

lemma getCurrentTime_buffer_minus':
  "- kernelWCET_ticks - 5 * MAX_PERIOD - 1 < - kernelWCET_ticks"
  apply (insert getCurrentTime_buffer_minus)
  apply (prop_tac "kernelWCET_ticks \<noteq> 0")
   using kernelWCET_pos' kernelWCET_ticks_def apply simp
  by (simp add: word_leq_minus_one_le)

lemma us_to_ticks_zero:
  "us_to_ticks 0 = 0"
  apply (clarsimp simp: us_to_ticks_def)
  done

lemma unat_div_helper:
  "a * ticks_per_timer_unit \<le> b * ticks_per_timer_unit
   \<Longrightarrow> unat (a * ticks_per_timer_unit div timer_unit) \<le> unat (b * ticks_per_timer_unit div timer_unit)"
  by (simp add: div_le_mono unat_div_distrib word_le_nat_alt)

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

consts' initTimer_impl :: "unit machine_rest_monad"
definition initTimer :: "unit machine_monad"
  where
  "initTimer \<equiv> machine_op_lift initTimer_impl"

consts' resetTimer_impl :: "unit machine_rest_monad"
definition resetTimer :: "unit machine_monad"
  where
  "resetTimer \<equiv> machine_op_lift resetTimer_impl"

subsection "Debug"

definition debugPrint :: "unit list \<Rightarrow> unit machine_monad"
  where
  debugPrint_def[simp]:
  "debugPrint \<equiv> \<lambda>message. return ()"


subsection \<open>Interrupt Controller\<close>

definition
  IRQ :: "irq \<Rightarrow> irq"
where "IRQ \<equiv> id"

consts'
  setIRQTrigger_impl :: "irq \<Rightarrow> bool \<Rightarrow> unit machine_rest_monad"

definition
  setIRQTrigger :: "irq \<Rightarrow> bool \<Rightarrow> unit machine_monad"
where
  "setIRQTrigger irq trigger \<equiv> machine_op_lift (setIRQTrigger_impl irq trigger)"

consts'
  plic_complete_claim_impl :: "irq \<Rightarrow> unit machine_rest_monad"

definition
  plic_complete_claim :: "irq \<Rightarrow> unit machine_monad"
where
  "plic_complete_claim irq \<equiv> machine_op_lift (plic_complete_claim_impl irq)"

text \<open>Interrupts that cannot occur while the kernel is running (e.g. at preemption points), but
that can occur from user mode. Empty on RISCV64.\<close>
definition non_kernel_IRQs :: "irq set"
  where
  "non_kernel_IRQs = {}"

text \<open>@{term getActiveIRQ} is oracle-based and deterministic to allow information flow proofs. It
updates the IRQ state to the reflect the passage of time since last the IRQ, then it gets the active
IRQ (if there is one).\<close>
definition getActiveIRQ :: "bool \<Rightarrow> (irq option) machine_monad"
  where
  "getActiveIRQ in_kernel \<equiv> do
     is_masked \<leftarrow> gets $ irq_masks;
     modify (\<lambda>s. s \<lparr> irq_state := irq_state s + 1 \<rparr>);
     active_irq \<leftarrow> gets $ irq_oracle \<circ> irq_state;
     if is_masked active_irq \<or> active_irq = 0xFF \<or> (in_kernel \<and> active_irq \<in> non_kernel_IRQs)
     then return None
     else return ((Some active_irq) :: irq option)
   od"

definition maskInterrupt :: "bool \<Rightarrow> irq \<Rightarrow> unit machine_monad"
  where
  "maskInterrupt m irq \<equiv> modify (\<lambda>s. s \<lparr> irq_masks := (irq_masks s) (irq := m) \<rparr>)"

definition ackInterrupt :: "irq \<Rightarrow> unit machine_monad"
  where
  "ackInterrupt \<equiv> \<lambda>irq. return ()"

consts' deadlineIRQ :: irq

definition
  "ackDeadlineIRQ \<equiv> ackInterrupt deadlineIRQ"

definition setInterruptMode :: "irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad"
  where
  "setInterruptMode \<equiv> \<lambda>irq levelTrigger polarityLow. return ()"


subsection "Clearing Memory"

text \<open>Clear memory contents to recycle it as user memory\<close>
definition clearMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
  "clearMemory ptr bytelength \<equiv>
     mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size .e. ptr + (of_nat bytelength) - 1]"

text \<open>Haskell simulator interface stub.\<close>
definition clearMemoryVM :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
  "clearMemoryVM ptr bits \<equiv> return ()"

text \<open>
  Initialize memory to be used as user memory. Note that zeroing out the memory is redundant
  in the specifications. In any case, we cannot abstract from the call to cleanCacheRange, which
  appears in the implementation.
\<close>
abbreviation (input) "initMemory == clearMemory"

text \<open>
  Free memory that had been initialized as user memory. While freeing memory is a no-op in the
  implementation, we zero out the underlying memory in the specifications to avoid garbage. If we
  know that there is no garbage, we can compute from the implementation state what the exact memory
  content in the specifications is.
\<close>
definition freeMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
  "freeMemory ptr bits \<equiv>
   mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size  .e.  ptr + 2 ^ bits - 1]"


subsection "User Monad and Registers"

type_synonym user_regs = "register \<Rightarrow> machine_word"

datatype user_context = UserContext (user_regs : user_regs)

type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"


definition getRegister :: "register \<Rightarrow> machine_word user_monad"
  where
  "getRegister r \<equiv> gets (\<lambda>s. user_regs s r)"

definition modify_registers :: "(user_regs \<Rightarrow> user_regs) \<Rightarrow> user_context \<Rightarrow> user_context"
  where
  "modify_registers f uc \<equiv> UserContext (f (user_regs uc))"

definition setRegister :: "register \<Rightarrow> machine_word \<Rightarrow> unit user_monad"
  where
  "setRegister r v \<equiv> modify (\<lambda>s. UserContext ((user_regs s) (r := v)))"

definition getRestartPC :: "machine_word user_monad"
  where
  "getRestartPC \<equiv> getRegister FaultIP"

definition setNextPC :: "machine_word \<Rightarrow> unit user_monad"
  where
  "setNextPC \<equiv> setRegister NextIP"


subsection "Caches, Barriers, and Flushing"

consts' initL2Cache_impl :: "unit machine_rest_monad"
definition initL2Cache :: "unit machine_monad"
  where
  "initL2Cache \<equiv> machine_op_lift initL2Cache_impl"

consts' hwASIDFlush_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition hwASIDFlush :: "machine_word \<Rightarrow> unit machine_monad"
  where
  "hwASIDFlush asid \<equiv> machine_op_lift (hwASIDFlush_impl asid)"

consts' sfence_impl :: "unit machine_rest_monad"
definition sfence :: "unit machine_monad"
  where
  "sfence \<equiv> machine_op_lift sfence_impl"

lemmas cache_machine_op_defs = sfence_def hwASIDFlush_def


subsection "Faults"

consts' stval_val :: "machine_state \<Rightarrow> machine_word"
definition read_stval :: "machine_word machine_monad"
  where
  "read_stval = gets stval_val"


subsection "Virtual Memory"

consts' setVSpaceRoot_impl :: "paddr \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition setVSpaceRoot :: "paddr \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where
  "setVSpaceRoot pt asid \<equiv> machine_op_lift $ setVSpaceRoot_impl pt asid"

end

end
