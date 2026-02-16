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

(* Interface function for the Haskell IRQ wrapper type *)
definition IRQ :: "irq \<Rightarrow> irq" where
  "IRQ \<equiv> id"

(* Interface function for the Haskell IRQ wrapper type *)
definition theIRQ :: "irq \<Rightarrow> irq" where
  "theIRQ \<equiv> id"

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
     if is_masked active_irq \<or> (in_kernel \<and> active_irq \<in> non_kernel_IRQs)
     then return None
     else return (Some active_irq)
   od"

definition maskInterrupt :: "bool \<Rightarrow> irq \<Rightarrow> unit machine_monad" where
  "maskInterrupt m irq \<equiv> modify (\<lambda>s. s \<lparr> irq_masks := (irq_masks s) (irq := m) \<rparr>)"

definition ackInterrupt :: "irq \<Rightarrow> unit machine_monad" where
  "ackInterrupt \<equiv> \<lambda>irq. return ()"

definition setInterruptMode :: "irq \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit machine_monad" where
  "setInterruptMode \<equiv> \<lambda>irq levelTrigger polarityLow. return ()"

consts' sendSGI_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition sendSGI :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "sendSGI sgi_irq target \<equiv> machine_op_lift $ sendSGI_impl sgi_irq target"

text \<open>Only exists on GICv3 platforms. We model interrupt deactivation as unmasking
  for the purposes of the interrupt oracle.\<close>
definition deactivateInterrupt :: "irq \<Rightarrow> unit machine_monad" where
  "deactivateInterrupt irq \<equiv> do
     assert config_ARM_GIC_V3;
     maskInterrupt False irq
   od"


subsection "User Monad and Registers"

type_synonym user_regs = "register \<Rightarrow> machine_word"

datatype user_context = UserContext (user_fpu_state : fpu_state) (user_regs : user_regs)

type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition getRegister :: "register \<Rightarrow> machine_word user_monad" where
  "getRegister r \<equiv> gets (\<lambda>s. user_regs s r)"

definition modify_registers :: "(user_regs \<Rightarrow> user_regs) \<Rightarrow> user_context \<Rightarrow> user_context" where
  "modify_registers f uc \<equiv> UserContext (user_fpu_state uc) (f (user_regs uc))"

definition setRegister :: "register \<Rightarrow> machine_word \<Rightarrow> unit user_monad" where
  "setRegister r v \<equiv> modify (\<lambda>s. UserContext (user_fpu_state s) ((user_regs s) (r := v)))"

definition getRestartPC :: "machine_word user_monad" where
  "getRestartPC \<equiv> getRegister FaultIP"

definition setNextPC :: "machine_word \<Rightarrow> unit user_monad" where
  "setNextPC \<equiv> setRegister NextIP"


subsection "FPU-related"

definition getFPUState :: "fpu_state user_monad" where
  "getFPUState \<equiv> gets user_fpu_state"

definition setFPUState :: "fpu_state \<Rightarrow> unit user_monad" where
  "setFPUState fc \<equiv> modify (\<lambda>s. UserContext fc (user_regs s))"

\<comment> \<open>This function touches the CPACR_EL1 register, which is used to enable/disable the FPU for EL0
   and EL1 and is generally controlled by the VM. seL4 only modifies it when unconditionally enabling
   it while disabling a VCPU, and seL4 instead toggles CPTR_EL2 to enable or disable the FPU for
   native tasks.\<close>
consts' enableFpuEL01_impl :: "unit machine_rest_monad"
consts' enableFpuEL01_val :: "machine_word \<Rightarrow> machine_word"
definition enableFpuEL01 :: "unit machine_monad" where
  "enableFpuEL01 \<equiv> do
     modify (vcpu_state_update (vcpu_regs_update (\<lambda>r. r(VCPURegCPACR := enableFpuEL01_val (r VCPURegCPACR)))));
     machine_op_lift enableFpuEL01_impl
   od"

definition readFpuState :: "fpu_state machine_monad" where
  "readFpuState \<equiv>  do
     state_assert fpu_enabled;
     gets fpu_state
   od"

consts' writeFpuState_impl :: "fpu_state \<Rightarrow> unit machine_rest_monad"
definition writeFpuState :: "fpu_state \<Rightarrow> unit machine_monad" where
  "writeFpuState fpu \<equiv>  do
     state_assert fpu_enabled;
     modify (fpu_state_update (\<lambda>_. fpu));
     machine_op_lift $ writeFpuState_impl fpu
   od"

\<comment> \<open>FIXME FPU: on AArch64 with hypervisor support this actually calls disableTrapFpu to enable the
     FPU. Do we want to model that as well or are we happy to abstract it away?\<close>
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
consts' setSCTLR_val :: "machine_word \<Rightarrow> machine_word"
definition setSCTLR :: "machine_word \<Rightarrow> unit machine_monad" where
  "setSCTLR w \<equiv> do
     modify (vcpu_state_update (vcpu_regs_update (\<lambda>r. r(VCPURegSCTLR := setSCTLR_val w))));
     machine_op_lift (setSCTLR_impl w)
   od"

consts' addressTranslateS1_impl :: "machine_word \<Rightarrow> unit machine_rest_monad"
consts' addressTranslateS1_val :: "machine_word \<Rightarrow> machine_state \<Rightarrow> machine_word"
definition addressTranslateS1 :: "machine_word \<Rightarrow> machine_word machine_monad" where
  "addressTranslateS1 w \<equiv> do
    machine_op_lift (addressTranslateS1_impl w);
    gets (addressTranslateS1_val w)
  od"


subsection "GIC VCPU Interface"

definition get_gic_vcpu_ctrl_hcr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_hcr \<equiv> gets (\<lambda>ms. vgic_hcr (vcpu_vgic (vcpu_state ms)))"

consts' set_gic_vcpu_ctrl_hcr_impl :: "32 word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_hcr :: "32 word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_hcr w \<equiv> do
     modify (vcpu_state_update (vcpu_vgic_update (vgic_hcr_update (\<lambda>_. w))));
     machine_op_lift (set_gic_vcpu_ctrl_hcr_impl w)
   od"

definition get_gic_vcpu_ctrl_vmcr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_vmcr \<equiv> gets (\<lambda>ms. vgic_vmcr (vcpu_vgic (vcpu_state ms)))"

consts' set_gic_vcpu_ctrl_vmcr_impl :: "32 word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_vmcr :: "32 word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_vmcr w \<equiv> do
     modify (vcpu_state_update (vcpu_vgic_update (vgic_vmcr_update (\<lambda>_. w))));
     machine_op_lift (set_gic_vcpu_ctrl_vmcr_impl w)
   od"

definition get_gic_vcpu_ctrl_apr :: "32 word machine_monad" where
  "get_gic_vcpu_ctrl_apr \<equiv> gets (\<lambda>ms. vgic_apr (vcpu_vgic (vcpu_state ms)))"

consts' set_gic_vcpu_ctrl_apr_impl :: "32 word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_apr :: "32 word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_apr w \<equiv> do
     modify (vcpu_state_update (vcpu_vgic_update (vgic_apr_update (\<lambda>_. w))));
     machine_op_lift (set_gic_vcpu_ctrl_apr_impl w)
   od"

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
definition get_gic_vcpu_ctrl_lr :: "machine_word \<Rightarrow> machine_word machine_monad" where
  "get_gic_vcpu_ctrl_lr n \<equiv> do
     machine_op_lift (get_gic_vcpu_ctrl_lr_impl n);
     gets (\<lambda>ms. vgic_lr (vcpu_vgic (vcpu_state ms)) (unat n))
   od"

consts' set_gic_vcpu_ctrl_lr_impl :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition set_gic_vcpu_ctrl_lr :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "set_gic_vcpu_ctrl_lr n w  \<equiv> do
     modify (vcpu_state_update (vcpu_vgic_update (vgic_lr_update (\<lambda>f. f(unat n := w)))));
     machine_op_lift (set_gic_vcpu_ctrl_lr_impl n w)
   od"


subsection "Virtual Timer Interface"

consts' check_export_arch_timer_impl :: "unit machine_rest_monad"
consts' check_export_arch_timer_val :: "machine_word"
definition check_export_arch_timer :: "unit machine_monad" where
  "check_export_arch_timer \<equiv> do
     modify (vcpu_state_update (vcpu_regs_update (\<lambda>r. r(VCPURegCNTKCTL_EL1 := check_export_arch_timer_val))));
     machine_op_lift check_export_arch_timer_impl
   od"

consts' read_cntpct_val :: "machine_state \<Rightarrow> 64 word"
definition read_cntpct :: "64 word machine_monad" where
  "read_cntpct \<equiv> gets read_cntpct_val"


subsection "Hypervisor Banked Registers"

definition readVCPUHardwareReg :: "vcpureg \<Rightarrow> machine_word machine_monad" where
  "readVCPUHardwareReg reg \<equiv> gets (\<lambda>ms. vcpu_regs (vcpu_state ms) reg)"

consts' writeVCPUHardwareReg_impl :: "vcpureg \<Rightarrow> machine_word \<Rightarrow> unit machine_rest_monad"
definition writeVCPUHardwareReg :: "vcpureg \<Rightarrow> machine_word \<Rightarrow> unit machine_monad" where
  "writeVCPUHardwareReg reg val \<equiv> do
     modify (vcpu_state_update (vcpu_regs_update (\<lambda>f. f(reg := val))));
     machine_op_lift (writeVCPUHardwareReg_impl reg val)
   od"


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

text \<open>Clear memory contents to recycle it as user memory. Do not yet flush the cache.\<close>
definition clearMemory :: "machine_word \<Rightarrow> nat \<Rightarrow> unit machine_monad" where
  "clearMemory ptr bytelength \<equiv>
     mapM_x (\<lambda>p. storeWord p 0) [ptr, ptr + word_size .e. ptr + (of_nat bytelength) - 1]"

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


subsection "Secure Monitor Calls (SMC)"

definition numSMCRegs :: nat where
  "numSMCRegs \<equiv> 8"

(* Tempting to use a list, but encoding the length requirement would make it ugly, and numSCMRegs
   is only going to change when the SMC spec changes. *)
type_synonym 'a eight_tuple = "'a \<times> 'a \<times>'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"

(* SMC calls can theoretically change any state in the machine. We assume here that they are well
   behaved (that the secure monitor is implemented correctly), that they do not affect main memory
   visible to the kernel, and that they do only affect machine_state_rest, i.e. no machine state
   that is explicitly modelled such as the IRQ controller.

   This will need to be extended in the future when things like core onlining/offlining are
   modelled. *)
consts' doSMC_mop_impl :: "machine_word eight_tuple \<Rightarrow> unit machine_rest_monad"
consts' doSMC_mop_val :: "machine_word eight_tuple \<Rightarrow> machine_state \<Rightarrow> machine_word eight_tuple"
definition doSMC_mop :: "machine_word eight_tuple \<Rightarrow> (machine_word eight_tuple) machine_monad"
  where
  "doSMC_mop args \<equiv> do
     machine_op_lift (doSMC_mop_impl args);
     gets (doSMC_mop_val args)
  od"


end
end
