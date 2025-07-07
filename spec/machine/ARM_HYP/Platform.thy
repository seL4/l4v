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

text \<open>
  This theory lists platform-specific types and basic constants, in particular
  the types of interrupts and physical addresses, constants for the
  kernel location, the offsets between physical and virtual kernel
  addresses, as well as the range of IRQs on the platform.
\<close>

section \<open>ABI Setup\<close>

(* representation of C int literals, the default for any unadorned numeral *)
type_synonym int_literal_len = "32 signed"
type_synonym int_word = "int_literal_len word"

section \<open>Platform Constants\<close>

context Arch begin global_naming ARM_HYP

(* General interrupts *)
value_type irq_len = Kernel_Config.irqBits (* IRQ_CNODE_SLOT_BITS *)
type_synonym irq = "irq_len word"

(* Software-generated interrupts *)
definition numSGIs_bits :: nat where
  "numSGIs_bits = 4"

definition numSGIs :: nat where
  "numSGIs = 2^numSGIs_bits"

definition gicNumTargets_bits :: nat where
  "gicNumTargets_bits \<equiv> if Kernel_Config.config_ARM_GIC_V3 then 4 else 3"

definition gicNumTargets :: nat where
  "gicNumTargets \<equiv> 2^gicNumTargets_bits"

end

(* Need to declare code equation outside Arch locale. Used in value_type below. *)
lemmas [code] = ARM_HYP.numSGIs_bits_def ARM_HYP.gicNumTargets_bits_def

context Arch begin global_naming ARM_HYP

value_type sgi_irq_len = numSGIs_bits
type_synonym sgi_irq = "sgi_irq_len word"

value_type sgi_target_len = gicNumTargets_bits
type_synonym sgi_target = "sgi_target_len word"

(* Physical addresses *)
type_synonym paddr = machine_word
abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

definition pageColourBits :: nat where
  "pageColourBits \<equiv> 2"

definition cacheLineBits :: nat where
  "cacheLineBits = CONFIG_L1_CACHE_LINE_SIZE_BITS"

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

definition irqVGICMaintenance :: "irq" where
  "irqVGICMaintenance \<equiv> 25"

definition irqVTimerEvent :: "irq" where
  "irqVTimerEvent  \<equiv> 27"

end

end
