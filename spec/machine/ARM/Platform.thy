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

context Arch begin global_naming ARM

(* General interrupts *)
value_type irq_len = Kernel_Config.irqBits (* IRQ_CNODE_SLOT_BITS *)
type_synonym irq = "irq_len word"

(* List of supported Arm platforms that support GICv3 or GICv2 *)
definition isGICPlatform :: bool where
  "isGICPlatform \<equiv> \<not>(config_PLAT_OMAP3 \<or> config_PLAT_AM335X \<or> config_PLAT_BCM2837)"

lemmas Kernel_Config_isGICPlatform_def =
  isGICPlatform_def
  Kernel_Config.config_PLAT_OMAP3_def
  Kernel_Config.config_PLAT_AM335X_def
  Kernel_Config.config_PLAT_BCM2837_def

(* Software-generated interrupts *)
definition numSGIs_bits :: nat where
  "numSGIs_bits = 4"

definition numSGIs :: nat where
  "numSGIs \<equiv> if isGICPlatform then 2^numSGIs_bits else 0"

definition gicNumTargets_bits :: nat where
  "gicNumTargets_bits \<equiv> if Kernel_Config.config_ARM_GIC_V3 then 32 else 3"

definition gicNumTargets :: nat where
  "gicNumTargets \<equiv> if isGICPlatform then 2^gicNumTargets_bits else 0"

(* Platforms that have a setTrigger IRQ function. These are currently all
   platforms that support the Arm GIC. *)
definition haveSetTrigger :: bool where
  "haveSetTrigger \<equiv> isGICPlatform"

lemmas Kernel_Config_haveSetTrigger_def =
  haveSetTrigger_def
  Kernel_Config_isGICPlatform_def

end

(* Need to declare code equation outside Arch locale. Used in value_type below. *)
lemmas [code] = ARM.numSGIs_bits_def ARM.gicNumTargets_bits_def

context Arch begin global_naming ARM

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

(* The first virtual address of the kernel's physical memory window.
   Coincides with seL4_UserTop and USER_TOP in C for AArch32.

   The definition below singles out the omap3 platform, because it is the only AArch32
   platform that does not put seL4_UserTop at 0xe0000000. The macro definition in C is
   hard to get at for the kernel config generation script and the definition here is
   comparatively straightforward. *)
definition pptrBase :: word32 where
  "pptrBase \<equiv> if config_PLAT_OMAP3 then 0xf0000000 else 0xe0000000"

schematic_goal pptrBase_val:
  "pptrBase = numeral ?n"
  by (simp add: pptrBase_def Kernel_Config.config_PLAT_OMAP3_def del: word_eq_numeral_iff_iszero)

lemma pptrBase_top_neq_0: (* 20 = size of ARMSectionBits *)
  "pptrBase >> 20 \<noteq> 0"
  by (simp add: pptrBase_def)

abbreviation (input) "paddrBase \<equiv> physBase"

definition pptrBaseOffset :: word32 where
  "pptrBaseOffset \<equiv> pptrBase - paddrBase"

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

end

end
