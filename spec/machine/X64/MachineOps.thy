(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Machine Operations"

theory MachineOps
imports
  "Word_Lib.WordSetup"
  "Monads.Nondet_Monad"
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

context Arch begin global_naming X64

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


\<comment> \<open>Interrupt controller operations\<close>

text \<open>
  Interrupts that cannot occur while the kernel is running (e.g. at preemption points),
  but that can occur from user mode. Empty on plain x86-64.
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
    if is_masked active_irq \<or> active_irq = 0xFF \<or> (in_kernel \<and> active_irq \<in> non_kernel_IRQs)
    then return None
    else return ((Some active_irq) :: irq option)
  od"

definition
  maskInterrupt :: "bool \<Rightarrow> irq \<Rightarrow> unit machine_monad"
where
  "maskInterrupt m irq \<equiv>
  modify (\<lambda>s. s \<lparr> irq_masks := (irq_masks s) (irq := m) \<rparr>)"

text \<open>Does nothing on imx31\<close>
definition
  ackInterrupt :: "irq \<Rightarrow> unit machine_monad"
where
  "ackInterrupt \<equiv> \<lambda>irq. return ()"

text \<open>Does nothing on imx31\<close>
definition
  setInterruptMode :: "irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad"
where
  "setInterruptMode \<equiv> \<lambda>irq levelTrigger polarityLow. return ()"

section "Memory Clearance"

text \<open>Clear memory contents to recycle it as user memory\<close>
definition
  clearMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad"
  where
 "clearMemory ptr bytelength \<equiv> mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size .e. ptr + (of_nat bytelength) - 1]"

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


text \<open> There are 576 bytes of FPU state. Since there are no operations on this state apart from bulk
save/restore, we abstract from names and just say how many bytes there are. \<close>
type_synonym fpu_bytes = 576
type_synonym fpu_state = "fpu_bytes \<Rightarrow> 8 word"

type_synonym user_regs = "register \<Rightarrow> machine_word"

datatype user_context = UserContext (user_fpu_state : fpu_state) (user_regs : user_regs)

type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition
  getRegister :: "register \<Rightarrow> machine_word user_monad"
where
  "getRegister r \<equiv> gets (\<lambda>s. user_regs s r)"

definition
  "modify_registers f uc \<equiv> UserContext (user_fpu_state uc) (f (user_regs uc))"

definition
  setRegister :: "register \<Rightarrow> machine_word \<Rightarrow> unit user_monad"
where
  "setRegister r v \<equiv> modify (\<lambda>s. UserContext (user_fpu_state s) ((user_regs s) (r := v)))"

definition
  "getRestartPC \<equiv> getRegister FaultIP"

definition
  "setNextPC \<equiv> setRegister NextIP"


definition
  getFPUState :: "fpu_state user_monad"
where
  "getFPUState \<equiv> gets user_fpu_state"

definition
  setFPUState :: "fpu_state \<Rightarrow> unit user_monad"
where
  "setFPUState fc \<equiv> modify (\<lambda>s. UserContext fc (user_regs s))"

(* The FPU state is opaque; the null state is a constant snapshot taken after initialisation *)
consts'
  FPUNullState :: fpu_state

consts' readFpuState_val :: "machine_state_rest \<Rightarrow> fpu_state"
definition readFpuState :: "fpu_state machine_monad" where
  "readFpuState \<equiv>  do
     state_assert fpu_enabled;
     machine_rest_lift $ gets readFpuState_val
   od"

consts' writeFpuState_impl :: "fpu_state \<Rightarrow> unit machine_rest_monad"
definition writeFpuState :: "fpu_state \<Rightarrow> unit machine_monad" where
  "writeFpuState val \<equiv>  do
     state_assert fpu_enabled;
     machine_op_lift $ writeFpuState_impl val
   od"

consts' enableFpu_impl :: "unit machine_rest_monad"
definition enableFpu :: "unit machine_monad" where
  "enableFpu \<equiv> do
     machine_op_lift enableFpu_impl;
     modify (\<lambda>s. s\<lparr>fpu_enabled := True \<rparr>)
   od"

consts' disableFpu_impl :: "unit machine_rest_monad"
definition disableFpu :: "unit machine_monad" where
  "disableFpu \<equiv> do
     machine_op_lift disableFpu_impl;
     modify (\<lambda>s. s\<lparr>fpu_enabled := False \<rparr>)
   od"

definition isFpuEnable :: "bool machine_monad" where
  "isFpuEnable \<equiv> gets fpu_enabled"

consts'
  initL2Cache_impl :: "unit machine_rest_monad"
definition
  initL2Cache :: "unit machine_monad"
where "initL2Cache \<equiv> machine_op_lift initL2Cache_impl"

consts'
  writeCR3_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"

definition writeCR3 :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
  where
  "writeCR3 vspace pcid \<equiv> machine_op_lift (writeCR3_impl vspace pcid)"

consts'
  mfence_impl :: "unit machine_rest_monad"
definition
mfence :: "unit machine_monad"
where
"mfence \<equiv> machine_op_lift mfence_impl"

consts'
  invalidateTLBEntry_impl :: "word64 \<Rightarrow> unit machine_rest_monad"

definition
invalidateTLBEntry :: "word64 \<Rightarrow> unit machine_monad"
where
"invalidateTLBEntry vptr \<equiv> machine_op_lift (invalidateTLBEntry_impl vptr)"

consts'
  invalidateTranslationSingleASID_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"

definition
  invalidateTranslationSingleASID :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where
  "invalidateTranslationSingleASID vptr asid \<equiv> machine_op_lift (invalidateTranslationSingleASID_impl vptr asid)"

consts'
  invalidateASID_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"

definition
  invalidateASID :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where
  "invalidateASID vspace asid \<equiv> machine_op_lift (invalidateASID_impl vspace asid)"

consts'
  invalidateLocalPageStructureCacheASID_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"

definition
  invalidateLocalPageStructureCacheASID :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where
  "invalidateLocalPageStructureCacheASID vspace asid \<equiv>
     machine_op_lift (invalidateLocalPageStructureCacheASID_impl vspace asid)"

(* FIXME x64: VT-d
definition
firstValidIODomain :: "word16"
where
"firstValidIODomain \<equiv> undefined"

definition
numIODomainIDBits :: "nat"
where
"numIODomainIDBits \<equiv> undefined"
*)

definition
  hwASIDInvalidate :: "word64 \<Rightarrow> machine_word \<Rightarrow> unit machine_monad"
where
  "hwASIDInvalidate \<equiv> invalidateASID"

consts'
  getFaultAddress_val :: "machine_state \<Rightarrow> machine_word"
definition
getFaultAddress :: "word64 machine_monad"
where
"getFaultAddress \<equiv> gets getFaultAddress_val"

consts'
  irqIntOffset_val :: "machine_state \<Rightarrow> machine_word"
definition
irqIntOffset :: "machine_word"
where
"irqIntOffset \<equiv> 0x20"

definition
maxPCIBus :: "machine_word"
where
"maxPCIBus \<equiv> 0xFF"

definition
maxPCIDev :: "machine_word"
where
"maxPCIDev \<equiv> 31"

definition
maxPCIFunc :: "machine_word"
where
"maxPCIFunc \<equiv> 7"

definition
ioapicIRQLines :: "machine_word"
where
"ioapicIRQLines \<equiv> 24"

consts'
  ioapicMapPinToVector_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow>
    machine_word \<Rightarrow> unit machine_rest_monad"
definition
  ioapicMapPinToVector :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow>
    machine_word \<Rightarrow> unit machine_monad"
where
  "ioapicMapPinToVector ioapic pin level polarity vector \<equiv>
    machine_op_lift (ioapicMapPinToVector_impl ioapic pin level polarity vector)"

definition IRQ :: "word8 \<Rightarrow> irq"
where
  "IRQ \<equiv> id"

consts'
  in8_impl :: "word16 \<Rightarrow> unit machine_rest_monad"
  in8_val :: "machine_state \<Rightarrow> machine_word"
definition
  in8 :: "word16 \<Rightarrow> machine_word machine_monad"
where
  "in8 port \<equiv> do machine_op_lift $ in8_impl port; gets in8_val od"

consts'
  in16_impl :: "word16 \<Rightarrow> unit machine_rest_monad"
  in16_val :: "machine_state \<Rightarrow> machine_word"
definition
  in16 :: "word16 \<Rightarrow> machine_word machine_monad"
where
  "in16 port \<equiv> do machine_op_lift $ in16_impl port; gets in16_val od"

consts'
  in32_impl :: "word16 \<Rightarrow> unit machine_rest_monad"
  in32_val :: "machine_state \<Rightarrow> machine_word"
definition
  in32 :: "word16 \<Rightarrow> machine_word machine_monad"
where
  "in32 port \<equiv> do machine_op_lift $ in32_impl port; gets in32_val od"

consts'
  out8_impl :: "word16 \<Rightarrow> word8 \<Rightarrow> unit machine_rest_monad"
definition
  out8 :: "word16 \<Rightarrow> word8 \<Rightarrow> unit machine_monad"
where
  "out8 port dat \<equiv> machine_op_lift $ out8_impl port dat"

consts'
  out16_impl :: "word16 \<Rightarrow> word16 \<Rightarrow> unit machine_rest_monad"
definition
  out16 :: "word16 \<Rightarrow> word16 \<Rightarrow> unit machine_monad"
where
  "out16 port dat \<equiv> machine_op_lift $ out16_impl port dat"

consts'
  out32_impl :: "word16 \<Rightarrow> word32 \<Rightarrow> unit machine_rest_monad"
definition
  out32 :: "word16 \<Rightarrow> word32 \<Rightarrow> unit machine_monad"
where
  "out32 port dat \<equiv> machine_op_lift $ out32_impl port dat"

end


end
