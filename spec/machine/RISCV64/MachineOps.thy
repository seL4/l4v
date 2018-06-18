(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Machine Operations"

theory MachineOps
imports
  "../../../lib/$L4V_ARCH/WordSetup"
  "../../../lib/Monad_WP/NonDetMonad"
  "../MachineMonad"
begin

section "Wrapping and Lifting Machine Operations"

text {*
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
*}

context Arch begin global_naming RISCV64

section "The Operations"

definition
  loadWord :: "machine_word \<Rightarrow> machine_word machine_monad"
  where "loadWord p \<equiv> do m \<leftarrow> gets underlying_memory;
                         assert (p && mask 3 = 0);
                         return (word_rcat (map (\<lambda>i. m (p + (7 - of_int i))) [0 .. 7]))
                      od"

definition
  storeWord :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where "storeWord p w \<equiv> do
                            assert (p && mask 3 = 0);
                            modify (underlying_memory_update (
                                      fold (\<lambda>i m. m((p + (of_int i)) := word_rsplit w ! (7 - nat i))) [0 .. 7]))
                         od"

lemma upto0_7_def:
  "[0..7] = [0,1,2,3,4,5,6,7]" by eval

lemma loadWord_storeWord_is_return:
  "p && mask 3 = 0 \<Longrightarrow> (do w \<leftarrow> loadWord p; storeWord p w od) = return ()"
  apply (rule ext)
  by (simp add: loadWord_def storeWord_def bind_def assert_def return_def
    modify_def gets_def get_def eval_nat_numeral put_def upto0_7_def
    word_rsplit_rcat_size word_size)


text {* This instruction is required in the simulator, only. *}
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
  invalidateTLB_impl :: "unit machine_rest_monad"
definition
  invalidateTLB :: "unit machine_monad"
where "invalidateTLB \<equiv> machine_op_lift invalidateTLB_impl"

lemmas cache_machine_op_defs = invalidateTLB_def

definition
  debugPrint :: "unit list \<Rightarrow> unit machine_monad"
where
  debugPrint_def[simp]:
 "debugPrint \<equiv> \<lambda>message. return ()"


-- "Interrupt controller operations"

text {*
  Interrupts that cannot occur while the kernel is running (e.g. at preemption points),
  but that can occur from user mode. Empty on plain x86-64.
*}
definition
  "non_kernel_IRQs = {}"

text {*
  @{term getActiveIRQ} is now derministic.
  It 'updates' the irq state to the reflect the passage of
  time since last the irq was gotten, then it gets the active
  IRQ (if there is one).
*}
definition
  getActiveIRQ :: "bool \<Rightarrow> (irq option) machine_monad"
where
  "getActiveIRQ in_kernel \<equiv> do
    is_masked \<leftarrow> gets $ irq_masks;
    modify (\<lambda>s. s \<lparr> irq_state := irq_state s + 1 \<rparr>);
    active_irq \<leftarrow> gets $ irq_oracle \<circ> irq_state;
    if is_masked active_irq \<or> active_irq = 0xFF \<or> (in_kernel \<and> active_irq \<in> non_kernel_IRQs)
    then return None
    else return ((Some active_irq) :: irq option)
  od"

definition
  maskInterrupt :: "bool \<Rightarrow> irq \<Rightarrow> unit machine_monad"
where
  "maskInterrupt m irq \<equiv>
  modify (\<lambda>s. s \<lparr> irq_masks := (irq_masks s) (irq := m) \<rparr>)"

definition
  ackInterrupt :: "irq \<Rightarrow> unit machine_monad"
where
  "ackInterrupt \<equiv> \<lambda>irq. return ()"

definition
  setInterruptMode :: "irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad"
where
  "setInterruptMode \<equiv> \<lambda>irq levelTrigger polarityLow. return ()"

section "Memory Clearance"

text {* Clear memory contents to recycle it as user memory *}
definition
  clearMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
 "clearMemory ptr bytelength \<equiv> mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size .e. ptr + (of_nat bytelength) - 1]"

definition
  clearMemoryVM :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
  "clearMemoryVM ptr bits \<equiv> return ()"

text {*
  Initialize memory to be used as user memory.
  Note that zeroing out the memory is redundant in the specifications.
  In any case, we cannot abstract from the call to cleanCacheRange,
  which appears in the implementation.
*}
abbreviation (input) "initMemory == clearMemory"

text {*
  Free memory that had been initialized as user memory.
  While freeing memory is a no-op in the implementation,
  we zero out the underlying memory in the specifications to avoid garbage.
  If we know that there is no garbage,
  we can compute from the implementation state
  what the exact memory content in the specifications is.
*}
definition
  freeMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
 "freeMemory ptr bits \<equiv>
  mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size  .e.  ptr + 2 ^ bits - 1]"


section "User Monad"

type_synonym user_regs = "register \<Rightarrow> machine_word"

datatype user_context = UserContext (user_regs : user_regs)

type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition
  getRegister :: "register \<Rightarrow> machine_word user_monad"
where
  "getRegister r \<equiv> gets (\<lambda>s. user_regs s r)"

definition
  "modify_registers f uc \<equiv> UserContext (f (user_regs uc))"

definition
  setRegister :: "register \<Rightarrow> machine_word \<Rightarrow> unit user_monad"
where
  "setRegister r v \<equiv> modify (\<lambda>s. UserContext ((user_regs s) (r := v)))"

definition
  "getRestartPC \<equiv> getRegister SEPC"

definition
  "setNextPC \<equiv> setRegister NEXTPC"


consts'
  hwASIDFlush_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition
  hwASIDFlush :: "machine_word \<Rightarrow> unit machine_monad"
where
  "hwASIDFlush asid \<equiv> machine_op_lift (hwASIDFlush_impl asid)"

consts'
  sFence_impl :: "unit machine_rest_monad"
definition
  sFence :: "unit machine_monad"
where
  "sFence \<equiv> machine_op_lift sFence_impl"

consts'
  sBadAddr_val :: "machine_state \<Rightarrow> machine_word"
definition
  readSBADAddr :: "machine_word machine_monad"
 where
  "readSBADAddr = gets sBadAddr_val"

end


end
