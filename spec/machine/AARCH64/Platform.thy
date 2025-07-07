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
  Kernel_Config
begin

section \<open>ABI Setup\<close>

(* representation of C int literals, the default for any unadorned numeral *)
type_synonym int_literal_len = "32 signed"
type_synonym int_word = "int_literal_len word"

section \<open>Platform Constants\<close>

context Arch begin global_naming AARCH64

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
lemmas [code] = AARCH64.numSGIs_bits_def AARCH64.gicNumTargets_bits_def

context Arch begin global_naming AARCH64

value_type sgi_irq_len = numSGIs_bits
type_synonym sgi_irq = "sgi_irq_len word"

value_type sgi_target_len = gicNumTargets_bits
type_synonym sgi_target = "sgi_target_len word"

(* Physical addresses *)
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

definition cacheLineBits :: nat where
  "cacheLineBits = CONFIG_L1_CACHE_LINE_SIZE_BITS"

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

definition irqVGICMaintenance :: irq where
  "irqVGICMaintenance \<equiv> 25"

definition irqVTimerEvent :: irq where
  "irqVTimerEvent \<equiv> 27"

definition pageColourBits :: nat where
  "pageColourBits \<equiv> undefined" \<comment> \<open>not implemented on this platform\<close>


section \<open>Page table sizes\<close>

definition vs_index_bits :: nat where
  "vs_index_bits \<equiv> if config_ARM_PA_SIZE_BITS_40 then 10 else (9::nat)"

end

(* Need to declare code equation outside Arch locale. They are used in value_type below. *)
lemmas [code] = AARCH64.vs_index_bits_def

context Arch begin global_naming AARCH64

lemma vs_index_bits_ge0[simp, intro!]: "0 < vs_index_bits"
  by (simp add: vs_index_bits_def)

(* A dependent-ish type in Isabelle. We use typedef here instead of value_type so that we can
   retain a symbolic value (vs_index_bits) for the size of the type instead of getting a plain
   number such as 9 or 10. *)
typedef vs_index_len = "{n :: nat. n < vs_index_bits}" by auto

end

instantiation AARCH64.vs_index_len :: len0
begin
  interpretation Arch .
  definition len_of_vs_index_len: "len_of (x::vs_index_len itself) \<equiv> CARD(vs_index_len)"
  instance ..
end

instantiation AARCH64.vs_index_len :: len
begin
  interpretation Arch .
  instance
  proof
   show "0 < LENGTH(vs_index_len)"
     by (simp add: len_of_vs_index_len type_definition.card[OF type_definition_vs_index_len])
  qed
end

context Arch begin global_naming AARCH64

type_synonym vs_index = "vs_index_len word"

type_synonym pt_index_len = 9
type_synonym pt_index = "pt_index_len word"

text \<open>Sanity check:\<close>
lemma length_vs_index_len[simp]:
  "LENGTH(vs_index_len) = vs_index_bits"
  by (simp add: len_of_vs_index_len type_definition.card[OF type_definition_vs_index_len])


section \<open>C array sizes corresponding to page table sizes\<close>

value_type pt_array_len = "(2::nat) ^ LENGTH(pt_index_len)"
value_type vs_array_len = "(2::nat) ^ vs_index_bits"

end

end
