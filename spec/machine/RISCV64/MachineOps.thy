(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Machine Operations"

theory MachineOps
imports
  "Word_Lib.WordSetup"
  "Lib.NonDetMonad"
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
     ta \<leftarrow> gets touched_addresses;
     assert (p \<in> ta);
     return (word_rcat (map (\<lambda>i. m (p + (7 - of_int i))) [0 .. 7]))
   od"

definition storeWord :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where
  "storeWord p w \<equiv> do
     assert (p && mask 3 = 0);
     ta \<leftarrow> gets touched_addresses;
     assert (p \<in> ta);
     modify (underlying_memory_update
              (fold (\<lambda>i m. m((p + (of_int i)) := word_rsplit w ! (7 - nat i))) [0 .. 7]))
   od"

lemma upto0_7_def:
  "[0..7] = [0,1,2,3,4,5,6,7]" by eval

lemma loadWord_storeWord_is_return:
  "p && mask 3 = 0 \<Longrightarrow> p \<in> touched_addresses s \<Longrightarrow>
   (do w \<leftarrow> loadWord p; storeWord p w od) s = return () s"
  by (auto simp: loadWord_def storeWord_def bind_def assert_def return_def word_rsplit_rcat_size
                 modify_def gets_def get_def eval_nat_numeral put_def upto0_7_def word_size)

consts' memory_regions :: "(paddr \<times> paddr) list"
definition getMemoryRegions :: "(paddr * paddr) list machine_monad"
  where
  "getMemoryRegions \<equiv> return memory_regions"

text \<open>Accessors and modifiers for touched_addresses\<close>

definition
  getTouchedAddresses :: "(machine_word set) machine_monad"
  where "getTouchedAddresses \<equiv> gets touched_addresses"

definition
  clearTouchedAddresses :: "unit machine_monad"
  where "clearTouchedAddresses \<equiv> modify (touched_addresses_update (\<lambda>_. {}))"

definition
  addTouchedAddresses :: "machine_word set \<Rightarrow> unit machine_monad"
  where "addTouchedAddresses da \<equiv> modify (touched_addresses_update ((\<union>) da))"

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

consts' L2FlushAddr_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition L2FlushAddr :: "machine_word \<Rightarrow> unit machine_monad"
  where
  "L2FlushAddr paddr \<equiv> machine_op_lift (L2FlushAddr_impl paddr)"

consts' hwASIDFlush_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition hwASIDFlush :: "machine_word \<Rightarrow> unit machine_monad"
  where
  "hwASIDFlush asid \<equiv> machine_op_lift (hwASIDFlush_impl asid)"

consts' sfence_impl :: "unit machine_rest_monad"
definition sfence :: "unit machine_monad"
  where
  "sfence \<equiv> machine_op_lift sfence_impl"

consts' tfence_impl :: "unit machine_rest_monad"
definition tfence :: "unit machine_monad"
  where
  "tfence \<equiv> machine_op_lift tfence_impl"

lemmas cache_machine_op_defs = tfence_def sfence_def hwASIDFlush_def L2FlushAddr_def


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
