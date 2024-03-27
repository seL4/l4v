(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Platform Definitions"

theory Platform
imports
  "Lib.Defs"
  "Lib.Lib"
  "Word_Lib.WordSetup"
  Setup_Locale
  Kernel_Config
begin

context Arch begin global_naming ARM_HYP

text \<open>
  This theory lists platform-specific types and basic constants, in particular
  the types of interrupts and physical addresses, constants for the
  kernel location, the offsets between physical and virtual kernel
  addresses, as well as the range of IRQs on the platform.
\<close>

(* General interrupts *)
type_synonym irq_len = 10
type_synonym irq = "irq_len word"

(* Software-generated interrupts *)
definition numSGIs :: nat where
  "numSGIs = 16"

definition gicSGITargetMaskBits :: nat where
  "gicSGITargetMaskBits \<equiv> if Kernel_Config.config_ARM_GIC_V3 then 16 else 8"

end

(* Need to declare code equation outside Arch locale. These are used in value_type below. *)
lemmas [code] = ARM_HYP.numSGIs_def ARM_HYP.gicSGITargetMaskBits_def

context Arch begin global_naming ARM_HYP

value_type sgi_irq_len = numSGIs
type_synonym sgi_irq = "sgi_irq_len word"

value_type sgi_mask_len = gicSGITargetMaskBits
type_synonym sgi_target_mask = "sgi_mask_len word"

(* guaranteed to succeed, because of value_type *)
lemma gicSGITargetMaskBits_sgi_target_len:
  "gicSGITargetMaskBits = LENGTH(sgi_mask_len)"
  by (simp add: gicSGITargetMaskBits_def Kernel_Config.config_ARM_GIC_V3_def)

(* Physical addresses *)
type_synonym paddr = machine_word
abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

definition pageColourBits :: nat where
  "pageColourBits \<equiv> 2"

definition cacheLineBits :: nat where
  "cacheLineBits = 6"

definition cacheLine :: nat where
  "cacheLine = 2^cacheLineBits"

(* The first virtual address of the kernel's physical memory window *)
definition pptrBase :: word32 where
  "pptrBase \<equiv> 0xe0000000"

abbreviation (input) "paddrBase \<equiv> physBase"

definition pptrBaseOffset :: machine_word where
  "pptrBaseOffset = pptrBase - paddrBase"

definition pptrTop :: "32 word" where
  "pptrTop \<equiv> 0xfff00000"

definition paddrTop :: "32 word" where
  "paddrTop \<equiv> pptrTop - pptrBaseOffset"

definition kernelELFPAddrBase :: word32 where
  "kernelELFPAddrBase \<equiv> physBase"

definition kernelELFBase :: word32 where
  "kernelELFBase \<equiv> pptrBase + (kernelELFPAddrBase && mask 22)"

definition kernelELFBaseOffset :: word32 where
  "kernelELFBaseOffset \<equiv> kernelELFBase - kernelELFPAddrBase"

definition ptrFromPAddr :: "paddr \<Rightarrow> word32" where
  "ptrFromPAddr paddr \<equiv> paddr + pptrBaseOffset"

definition addrFromPPtr :: "word32 \<Rightarrow> paddr" where
  "addrFromPPtr pptr \<equiv> pptr - pptrBaseOffset"

definition addrFromKPPtr :: "word32 \<Rightarrow> paddr" where
  "addrFromKPPtr kpptr \<equiv> kpptr - kernelELFBaseOffset"

definition minIRQ :: "irq" where
  "minIRQ \<equiv> 0"

definition maxIRQ :: "irq" where
  "maxIRQ \<equiv> 191"

definition irqVGICMaintenance :: "irq" where
  "irqVGICMaintenance \<equiv> 25"

definition irqVTimerEvent :: "irq" where
  "irqVTimerEvent  \<equiv> 27"

end

end
