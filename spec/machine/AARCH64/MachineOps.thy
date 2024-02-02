(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Machine Operations"

theory MachineOps
imports
  Word_Lib.WordSetup
  Monads.Nondet_Monad
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

  All this is done only to avoid a large number of axioms (2 for each operation).\<close>

context Arch begin global_naming AARCH64

section "The Operations"

subsection "Memory"

definition loadWord :: "machine_word \<Rightarrow> machine_word machine_monad" where
  "loadWord p \<equiv> do
     m \<leftarrow> gets underlying_memory;
     assert (p && mask 3 = 0);
     return (word_rcat (map (\<lambda>i. m (p + (7 - of_int i))) [0 .. 7]))
   od"

definition storeWord :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
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
definition getMemoryRegions :: "(paddr * paddr) list machine_monad" where
  "getMemoryRegions \<equiv> return memory_regions"

text \<open>This instruction is required in the simulator, only.\<close>
definition storeWordVM :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "storeWordVM w p \<equiv> return ()"


subsection "Timer"

consts' configureTimer_impl :: "unit machine_rest_monad"
consts' configureTimer_val :: "machine_state \<Rightarrow> irq"
definition configureTimer :: "irq machine_monad" where
  "configureTimer \<equiv> do
     machine_op_lift configureTimer_impl;
     gets configureTimer_val
   od"

consts' initTimer_impl :: "unit machine_rest_monad"
definition initTimer :: "unit machine_monad" where
  "initTimer \<equiv> machine_op_lift initTimer_impl"

consts' resetTimer_impl :: "unit machine_rest_monad"
definition resetTimer :: "unit machine_monad" where
  "resetTimer \<equiv> machine_op_lift resetTimer_impl"


subsection "Debug"

definition debugPrint :: "unit list \<Rightarrow> unit machine_monad" where
  debugPrint_def[simp]:
  "debugPrint \<equiv> \<lambda>message. return ()"


subsection \<open>Interrupt Controller\<close>

definition IRQ :: "irq \<Rightarrow> irq" where
  "IRQ \<equiv> id"

consts' setIRQTrigger_impl :: "irq \<Rightarrow> bool \<Rightarrow> unit machine_rest_monad"
definition setIRQTrigger :: "irq \<Rightarrow> bool \<Rightarrow> unit machine_monad" where
  "setIRQTrigger irq trigger \<equiv> machine_op_lift (setIRQTrigger_impl irq trigger)"

consts' plic_complete_claim_impl :: "irq \<Rightarrow> unit machine_rest_monad"
definition plic_complete_claim :: "irq \<Rightarrow> unit machine_monad" where
  "plic_complete_claim irq \<equiv> machine_op_lift (plic_complete_claim_impl irq)"

text \<open>
  Interrupts that cannot occur while the kernel is running (e.g. at preemption points),
  but that can occur from user mode.\<close>
definition non_kernel_IRQs :: "irq set" where
  "non_kernel_IRQs = {irqVGICMaintenance, irqVTimerEvent}"

text \<open>@{term getActiveIRQ} is oracle-based and deterministic to allow information flow proofs. It
updates the IRQ state to the reflect the passage of time since last the IRQ, then it gets the active
IRQ (if there is one).\<close>
definition getActiveIRQ :: "bool \<Rightarrow> (irq option) machine_monad" where
  "getActiveIRQ in_kernel \<equiv> do
     is_masked \<leftarrow> gets $ irq_masks;
     modify (\<lambda>s. s \<lparr> irq_state := irq_state s + 1 \<rparr>);
     active_irq \<leftarrow> gets $ irq_oracle \<circ> irq_state;
     if is_masked active_irq \<or> active_irq = 0xFF \<or> (in_kernel \<and> active_irq \<in> non_kernel_IRQs)
     then return None
     else return ((Some active_irq) :: irq option)
   od"

definition maskInterrupt :: "bool \<Rightarrow> irq \<Rightarrow> unit machine_monad" where
  "maskInterrupt m irq \<equiv> modify (\<lambda>s. s \<lparr> irq_masks := (irq_masks s) (irq := m) \<rparr>)"

definition ackInterrupt :: "irq \<Rightarrow> unit machine_monad" where
  "ackInterrupt \<equiv> \<lambda>irq. return ()"

definition setInterruptMode :: "irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad" where
  "setInterruptMode \<equiv> \<lambda>irq levelTrigger polarityLow. return ()"


subsection "User Monad and Registers"

type_synonym user_regs = "register \<Rightarrow> machine_word"

text \<open> There are 64 general FPU registers saved. \<close>
type_synonym fpu_regs = 64

text \<open>
  We use Haskell naming convention here, as we translate the Haskell FPUState directly
  to this one for use in the abstract and executable specs.\<close>
datatype fpu_state = FPUState (fpuRegs : "fpu_regs \<Rightarrow> 64 word")
                              (fpuSr : "32 word")
                              (fpuCr : "32 word")

datatype user_context = UserContext (fpu_state : fpu_state) (user_regs : user_regs)

type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition getRegister :: "register \<Rightarrow> machine_word user_monad" where
  "getRegister r \<equiv> gets (\<lambda>s. user_regs s r)"

definition modify_registers :: "(user_regs \<Rightarrow> user_regs) \<Rightarrow> user_context \<Rightarrow> user_context" where
  "modify_registers f uc \<equiv> UserContext (fpu_state uc) (f (user_regs uc))"

definition setRegister :: "register \<Rightarrow> machine_word \<Rightarrow> unit user_monad" where
  "setRegister r v \<equiv> modify (\<lambda>s. UserContext (fpu_state s) ((user_regs s) (r := v)))"

definition getRestartPC :: "machine_word user_monad" where
  "getRestartPC \<equiv> getRegister FaultIP"

definition setNextPC :: "machine_word \<Rightarrow> unit user_monad" where
  "setNextPC \<equiv> setRegister NextIP"


subsection "FPU-related"

consts' enableFpuEL01_impl :: "unit machine_rest_monad"
definition enableFpuEL01 :: "unit machine_monad" where
  "enableFpuEL01 \<equiv> machine_op_lift enableFpuEL01_impl"

definition getFPUState :: "fpu_state user_monad" where
  "getFPUState \<equiv> gets fpu_state"

definition setFPUState :: "fpu_state \<Rightarrow> unit user_monad" where
  "setFPUState fc \<equiv> modify (\<lambda>s. UserContext fc (user_regs s))"

consts' nativeThreadUsingFPU_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
consts' nativeThreadUsingFPU_val :: "machine_state \<Rightarrow> bool"
definition nativeThreadUsingFPU :: "machine_word \<Rightarrow> bool machine_monad" where
  "nativeThreadUsingFPU thread_ptr \<equiv> do
       machine_op_lift (nativeThreadUsingFPU_impl thread_ptr);
       gets nativeThreadUsingFPU_val
  od"

consts' switchFpuOwner_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition switchFpuOwner :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "switchFpuOwner new_owner cpu \<equiv> machine_op_lift (switchFpuOwner_impl new_owner cpu)"

(* FIXME this is a very high-level FPU abstraction *)
consts' fpuThreadDeleteOp_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition fpuThreadDeleteOp :: "machine_word \<Rightarrow> unit machine_monad" where
  "fpuThreadDeleteOp thread_ptr \<equiv> machine_op_lift (fpuThreadDeleteOp_impl thread_ptr)"

(* FIXME this machine op is used to abstract the entire lazy FPU switch interrupt mechanism,
   which can only trigger when the current thread's FPU is disabled and it performs an FPU
   operation. We have no model for this mechanism or the state that it caches, so for
   verification purposes we act as if the FPU is always enabled.
   Future lazy FPU switch overhaul will involve the state that this operation reads, at which
   point it should become a normal function. *)
definition isFpuEnable :: "bool machine_monad" where
  "isFpuEnable \<equiv> return True"


subsection "Fault Registers"


consts' FAR_val :: "machine_state \<Rightarrow> machine_word"
definition getFAR :: "machine_word machine_monad" where
  "getFAR \<equiv> gets FAR_val"

consts' DFSR_val :: "machine_state \<Rightarrow> machine_word"
definition getDFSR :: "machine_word machine_monad" where
  "getDFSR \<equiv> gets DFSR_val"

consts' IFSR_val :: "machine_state \<Rightarrow> machine_word"
definition getIFSR :: "machine_word machine_monad" where
  "getIFSR \<equiv> gets IFSR_val"


subsection "Control Registers"

consts' HSR_val :: "machine_state \<Rightarrow> machine_word"
definition getHSR :: "machine_word machine_monad" where
  "getHSR \<equiv> gets HSR_val"

consts' ESR_val :: "machine_state \<Rightarrow> machine_word"
definition getESR :: "machine_word machine_monad" where
  "getESR \<equiv> gets ESR_val"

consts' SCTLR_val :: "machine_state \<Rightarrow> machine_word"
definition getSCTLR :: "machine_word machine_monad" where
  "getSCTLR \<equiv> gets SCTLR_val"

consts' setHCR_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition setHCR :: "machine_word \<Rightarrow> unit machine_monad" where
  "setHCR w \<equiv> machine_op_lift (setHCR_impl w)"

consts' setSCTLR_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition setSCTLR :: "machine_word \<Rightarrow> unit machine_monad" where
  "setSCTLR w \<equiv> machine_op_lift (setSCTLR_impl w)"

consts' addressTranslateS1_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
consts' addressTranslateS1_val :: "machine_word \<Rightarrow> machine_state \<Rightarrow> machine_word"
definition addressTranslateS1 :: "machine_word \<Rightarrow> machine_word machine_monad" where
  "addressTranslateS1 w \<equiv> do
    machine_op_lift (addressTranslateS1_impl w);
    gets (addressTranslateS1_val w)
  od"


subsection "GIC VCPU Interface"

consts' gic_vcpu_ctrl_hcr_val :: "machine_state \<Rightarrow> 32 word"
definition get_gic_vcpu_ctrl_hcr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_hcr \<equiv> gets gic_vcpu_ctrl_hcr_val"

consts' set_gic_vcpu_ctrl_hcr_impl :: "32 word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_hcr :: "32 word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_hcr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_hcr_impl w)"

consts' gic_vcpu_ctrl_vmcr_val :: "machine_state \<Rightarrow> 32 word"
definition get_gic_vcpu_ctrl_vmcr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_vmcr \<equiv> gets gic_vcpu_ctrl_vmcr_val"

consts' set_gic_vcpu_ctrl_vmcr_impl :: "32 word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_vmcr :: "32 word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_vmcr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_vmcr_impl w)"

consts' gic_vcpu_ctrl_apr_val :: "machine_state \<Rightarrow> 32 word"
definition get_gic_vcpu_ctrl_apr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_apr \<equiv> gets gic_vcpu_ctrl_apr_val"

consts' set_gic_vcpu_ctrl_apr_impl :: "32 word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_apr :: "32 word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_apr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_apr_impl w)"

consts' gic_vcpu_ctrl_vtr_val :: "machine_state \<Rightarrow> 32 word"
definition get_gic_vcpu_ctrl_vtr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_vtr \<equiv> gets gic_vcpu_ctrl_vtr_val"

consts' set_gic_vcpu_ctrl_vtr_impl :: "32 word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_vtr :: "32 word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_vtr w \<equiv> machine_op_lift (set_gic_vcpu_ctrl_vtr_impl w)"

consts' gic_vcpu_ctrl_misr_val :: "machine_state \<Rightarrow> 32 word"
definition get_gic_vcpu_ctrl_misr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_misr \<equiv> gets gic_vcpu_ctrl_misr_val"

consts' gic_vcpu_ctrl_eisr0_val :: "machine_state \<Rightarrow> 32 word"
definition get_gic_vcpu_ctrl_eisr0 :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_eisr0 \<equiv> gets gic_vcpu_ctrl_eisr0_val"

consts' gic_vcpu_ctrl_eisr1_val :: "machine_state \<Rightarrow> 32 word"
definition get_gic_vcpu_ctrl_eisr1 :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_eisr1 \<equiv> gets gic_vcpu_ctrl_eisr1_val"

consts' get_gic_vcpu_ctrl_lr_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
consts' gic_vcpu_ctrl_lr_val :: "machine_word \<Rightarrow> machine_state \<Rightarrow> machine_word"
definition get_gic_vcpu_ctrl_lr :: "machine_word \<Rightarrow> machine_word machine_monad" where
  "get_gic_vcpu_ctrl_lr n \<equiv> do
     machine_op_lift (get_gic_vcpu_ctrl_lr_impl n);
     gets (gic_vcpu_ctrl_lr_val n)
   od"

consts' set_gic_vcpu_ctrl_lr_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_lr :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_lr n w  \<equiv> machine_op_lift (set_gic_vcpu_ctrl_lr_impl n w)"


subsection "Virtual Timer Interface"

consts' check_export_arch_timer_impl :: "unit machine_rest_monad"
definition check_export_arch_timer :: "unit machine_monad" where
  "check_export_arch_timer \<equiv> machine_op_lift check_export_arch_timer_impl"

consts' read_cntpct_val :: "machine_state \<Rightarrow> 64 word"
definition read_cntpct :: "64 word machine_monad" where
  "read_cntpct \<equiv> gets read_cntpct_val"


subsection "Hypervisor Banked Registers"

consts' vcpuHardwareReg_val :: "vcpureg \<Rightarrow> machine_state \<Rightarrow> machine_word"
definition readVCPUHardwareReg :: "vcpureg \<Rightarrow> machine_word machine_monad" where
  "readVCPUHardwareReg reg \<equiv> gets (vcpuHardwareReg_val reg)"

consts' writeVCPUHardwareReg_impl :: "vcpureg \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition writeVCPUHardwareReg :: "vcpureg \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "writeVCPUHardwareReg reg val \<equiv> machine_op_lift (writeVCPUHardwareReg_impl reg val)"


subsection "Caches, Barriers, and Flushing"

consts' initL2Cache_impl :: "unit machine_rest_monad"
definition initL2Cache :: "unit machine_monad" where
  "initL2Cache \<equiv> machine_op_lift initL2Cache_impl"

consts' isb_impl :: "unit machine_rest_monad"
definition isb :: "unit machine_monad" where
  "isb \<equiv> machine_op_lift isb_impl"

consts' dsb_impl :: "unit machine_rest_monad"
definition dsb :: "unit machine_monad" where
  "dsb \<equiv> machine_op_lift dsb_impl"

consts' invalidateTranslationASID_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition invalidateTranslationASID :: "machine_word \<Rightarrow> unit machine_monad" where
  "invalidateTranslationASID asid \<equiv> machine_op_lift (invalidateTranslationASID_impl asid)"

consts' invalidateTranslationSingle_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
definition invalidateTranslationSingle :: "machine_word \<Rightarrow> unit machine_monad" where
  "invalidateTranslationSingle r \<equiv> machine_op_lift (invalidateTranslationSingle_impl r)"

consts' cleanByVA_PoU_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition cleanByVA_PoU :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "cleanByVA_PoU vaddr paddr = machine_op_lift (cleanByVA_PoU_impl vaddr paddr)"

consts' cleanInvalidateCacheRange_RAM_impl ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition cleanInvalidateCacheRange_RAM ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "cleanInvalidateCacheRange_RAM vstart vend pstart =
     machine_op_lift (cleanInvalidateCacheRange_RAM_impl vstart vend pstart)"

consts' cleanCacheRange_RAM_impl ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition cleanCacheRange_RAM ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "cleanCacheRange_RAM vstart vend pstart =
     machine_op_lift (cleanCacheRange_RAM_impl vstart vend pstart)"

consts' cleanCacheRange_PoU_impl ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition cleanCacheRange_PoU ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "cleanCacheRange_PoU vstart vend pstart =
     machine_op_lift (cleanCacheRange_PoU_impl vstart vend pstart)"

consts' invalidateCacheRange_RAM_impl ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition invalidateCacheRange_RAM ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "invalidateCacheRange_RAM vstart vend pstart =
     machine_op_lift (invalidateCacheRange_RAM_impl vstart vend pstart)"

consts' invalidateCacheRange_I_impl ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition invalidateCacheRange_I ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "invalidateCacheRange_I vstart vend pstart =
     machine_op_lift (invalidateCacheRange_I_impl vstart vend pstart)"

consts' branchFlushRange_impl ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition branchFlushRange ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "branchFlushRange vstart vend pstart = machine_op_lift (branchFlushRange_impl vstart vend pstart)"

lemmas cache_machine_op_defs =
  invalidateTranslationASID_def
  invalidateTranslationSingle_def
  cleanByVA_PoU_def
  cleanInvalidateCacheRange_RAM_def
  cleanCacheRange_RAM_def
  cleanCacheRange_PoU_def
  invalidateCacheRange_RAM_def
  invalidateCacheRange_I_def
  branchFlushRange_def


subsection "Clearing Memory"

text \<open>Clear memory contents to recycle it as user memory\<close>
definition clearMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad" where
  "clearMemory ptr bytelength \<equiv> do
     mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size .e. ptr + (of_nat bytelength) - 1];
     cleanCacheRange_RAM ptr (ptr + of_nat bytelength - 1) (addrFromPPtr ptr)
   od"

text \<open>Haskell simulator interface stub.\<close>
definition clearMemoryVM :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad" where
  "clearMemoryVM ptr bits \<equiv> return ()"

text \<open>
  Initialize memory to be used as user memory. Note that zeroing out the memory is redundant
  in the specifications. In any case, we cannot abstract from the call to cleanCacheRange, which
  appears in the implementation.\<close>
abbreviation (input) "initMemory == clearMemory"

text \<open>
  Free memory that had been initialized as user memory. While freeing memory is a no-op in the
  implementation, we zero out the underlying memory in the specifications to avoid garbage. If we
  know that there is no garbage, we can compute from the implementation state what the exact memory
  content in the specifications is.\<close>
definition freeMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad" where
  "freeMemory ptr bits \<equiv>
     mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size  .e.  ptr + 2 ^ bits - 1]"


subsection "Virtual Memory"

consts' setVSpaceRoot_impl :: "paddr \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition setVSpaceRoot :: "paddr \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "setVSpaceRoot pt asid \<equiv> machine_op_lift $ setVSpaceRoot_impl pt asid"

end
end
