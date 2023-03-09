(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Platform Definitions"

theory Platform
imports
  "Lib.Lib"
  "Word_Lib.WordSetup"
  "Lib.Defs"
  Setup_Locale
  Kernel_Config_Lemmas
begin

context Arch begin global_naming AARCH64

type_synonym irq_len = 9 (* match IRQ_CNODE_SLOT_BITS in seL4 config *)
type_synonym irq = "irq_len word"
type_synonym paddr = machine_word

abbreviation (input) "toPAddr \<equiv> id"
abbreviation (input) "fromPAddr \<equiv> id"

(* For address space layout with hypervisor enabled see:
   seL4/include/arch/arm/arch/64/mode/hardware.h
   FIXME AARCH64 include diagram here after C revisions are done
*)

(* NOTE: a number of these constants appear in the Haskell, but are shadowed
   here due to more convenient formulation.
   Examples: kernelELFBase, kernelELFBaseOffset, kernelELFAddressBase, pptrBase
   Ideally and in future, we should converge on a single authoritative source
   of these constants.
*)

(* The canonical bit is the highest bit that can be set in a virtual address and still accepted
   by the hardware. Any bit higher than that will be overwritten by sign extension, zero extension,
   or result in a fault.
   For AArch64 with hyp, addresses >= 2^48 are invalid, and sign-extension is not used by the
   hardware. *)
definition canonical_bit :: nat where
  "canonical_bit = 47"

definition kdevBase :: machine_word where
  "kdevBase = 0x000000FFFFE00000"

definition kernelELFBase :: machine_word where
  "kernelELFBase = 2^39 + physBase"

definition kernelELFPAddrBase :: machine_word where
  "kernelELFPAddrBase = physBase"

definition kernelELFBaseOffset :: machine_word where
  "kernelELFBaseOffset = kernelELFBase - kernelELFPAddrBase"

definition pptrBase :: machine_word where
  "pptrBase = 0x8000000000" (* 2^39 *)

definition pptrUserTop :: machine_word where
  "pptrUserTop \<equiv> mask (if config_ARM_PA_SIZE_BITS_40 then 40 else 44)"

lemma "pptrUserTop = (if config_ARM_PA_SIZE_BITS_40 then 0xFFFFFFFFFF else 0xFFFFFFFFFFF)" (* Sanity check with C *)
  by (simp add: pptrUserTop_def mask_def)

definition pptrTop :: machine_word where
  "pptrTop = 2^40 - 2^30" (* FIXME AARCH64: see also seL4/seL4#957 *)

definition paddrBase :: machine_word where
  "paddrBase \<equiv> 0"

definition pptrBaseOffset :: machine_word where
  "pptrBaseOffset = pptrBase - paddrBase"

definition paddrTop :: machine_word where
  "paddrTop = pptrTop - pptrBaseOffset"

definition ptrFromPAddr :: "paddr \<Rightarrow> machine_word" where
  "ptrFromPAddr paddr \<equiv> paddr + pptrBaseOffset"

definition addrFromPPtr :: "machine_word \<Rightarrow> paddr" where
  "addrFromPPtr pptr \<equiv> pptr - pptrBaseOffset"

definition addrFromKPPtr :: "machine_word \<Rightarrow> paddr" where
  "addrFromKPPtr pptr \<equiv> pptr - kernelELFBaseOffset"

definition minIRQ :: "irq" where
  "minIRQ \<equiv> 0"

definition maxIRQ :: "irq" where
  "maxIRQ \<equiv> 383"

definition irqVGICMaintenance :: irq where
  "irqVGICMaintenance \<equiv> 25"

definition irqVTimerEvent :: irq where
  "irqVTimerEvent \<equiv> 27"

definition pageColourBits :: nat where
  "pageColourBits \<equiv> undefined" \<comment> \<open>not implemented on this platform\<close>

end
end
