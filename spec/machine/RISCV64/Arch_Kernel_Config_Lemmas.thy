(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific lemmas constraining Kernel_Config definitions *)

theory Arch_Kernel_Config_Lemmas
imports
  Kernel_Config_Lemmas
  Platform
begin

context Arch begin global_naming RISCV64

lemma pptrBase_kernelELFBase:
  "pptrBase < kernelELFBase"
  by (simp add: pptrBase_def canonical_bit_def kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
                Kernel_Config.physBase_def mask_def)

(* 12 in this lemma and below is pageBits, which is not yet defined in this theory.
   Definition will be folded and the lemmas shadowed in AInvs. *)
lemma is_page_aligned_physBase:
  "is_aligned physBase 12"
  by (simp add: Kernel_Config.physBase_def is_aligned_def)

(* 22 is kernel_window_bits, defined in Init_A. To be folded in AInvs. *)
lemma kernel_window_sufficient:
  "pptrBase + (1 << 22) \<le> kernelELFBase"
  unfolding pptrBase_def canonical_bit_def kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

lemma kernel_elf_window_at_least_page:
  "kernelELFBase + 2 ^ 12 \<le> kdevBase"
  unfolding kernelELFBase_def kernelELFPAddrBase_def kdevBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

(* This doesn't follow from alignment, because we need <, not \<le> *)
lemma kernelELFBase_no_overflow:
  "kernelELFBase < kernelELFBase + 2 ^ 12"
  unfolding kernelELFBase_def kernelELFPAddrBase_def pptrTop_def
  by (simp add: mask_def Kernel_Config.physBase_def)

(* maxIRQ lemmas *)
lemma maxIRQ_less_2p_irqBits:
  "(Kernel_Config.maxIRQ::nat) < 2^irqBits"
  by (simp add: Kernel_Config.maxIRQ_def Kernel_Config.irqBits_def)

lemma irqBits_le_12: (* global C bitfield struct limit on maxIRQ *)
  "irqBits \<le> 12"
  by (simp add: Kernel_Config.irqBits_def)

lemma irq_machine_le_maxIRQ_irq:
  "irq \<le> Kernel_Config.maxIRQ \<Longrightarrow> (ucast irq::irq) \<le> Kernel_Config.maxIRQ" for irq::machine_word
  by (simp add: Kernel_Config.maxIRQ_def word_le_nat_alt unat_ucast)

lemma maxIRQ_leq_mask_irq_len:
  "(Kernel_Config.maxIRQ::machine_word) \<le> mask LENGTH(irq_len)"
  by (simp add: Kernel_Config.maxIRQ_def mask_def)

lemma unat_2p_irq_len_machine:
  "unat (2 ^ irq_len :: machine_word) = 2 ^ irq_len"
  by (simp add: irq_len_val)

lemma unat_irq_bounded:
  "unat irq < 2 ^ irq_len" for irq::irq
  using unat_lt2p[where 'a=irq_len]
  by (simp add: irq_len_val)

lemma unat_le_2p_irqBits:
  "unat irq \<le> 2 ^ irqBits" for irq :: irq
  by (metis irq_len_def nless_le unat_irq_bounded)

lemma unat_2p_irqBits_machine_word:
  "unat (2 ^ irqBits :: machine_word) = 2 ^ irqBits"
  using irq_len_def unat_2p_irq_len_machine
  by simp

(* follows from value_type definition of irq_len *)
lemma LENGTH_irq_len_irqBits[simp]: (* [simp] will fire only for simp del: len_of_numeral_defs *)
  "LENGTH(irq_len) = irqBits"
  using irq_len_def irq_len_val
  by simp

lemma maxIRQ_less_2p_irq_len:
  "(Kernel_Config.maxIRQ::nat) < 2^LENGTH(irq_len)"
  using maxIRQ_less_2p_irqBits
  by (simp del: len_of_numeral_defs)

(* maxIRQ as a generic numeral allows us to write rules about casts/unat/uint etc without
   mentioning numbers: *)

lemma of_nat_maxIRQ[simp]:
  "of_nat Kernel_Config.maxIRQ = (Kernel_Config.maxIRQ::'a::len word)"
  by (simp add: Kernel_Config.maxIRQ_def)

lemma of_int_maxIRQ[simp]:
  "of_int Kernel_Config.maxIRQ = (Kernel_Config.maxIRQ::'a::len word)"
  by (simp add: Kernel_Config.maxIRQ_def)

lemma scast_maxIRQ_32_signed_irq[simp]:
  "scast (Kernel_Config.maxIRQ :: 32 signed word) = (Kernel_Config.maxIRQ :: irq)"
  by (simp add: Kernel_Config.maxIRQ_def)

lemma scast_maxIRQ_32_signed_machine_word[simp]:
  "scast (Kernel_Config.maxIRQ :: 32 signed word) = (Kernel_Config.maxIRQ :: machine_word)"
  by (simp add: Kernel_Config.maxIRQ_def)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma unat_maxIRQ[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow> unat (Kernel_Config.maxIRQ::'a word) = Kernel_Config.maxIRQ"
  by (metis maxIRQ_less_2p_irq_len Word.of_nat_unat of_nat_inverse of_nat_maxIRQ unat_ucast_up_simp)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma uint_maxIRQ[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow> uint (Kernel_Config.maxIRQ::'a word) = Kernel_Config.maxIRQ"
  apply ((solves \<open>clarsimp simp: Kernel_Config.maxIRQ_def\<close>)?) (* proof for maxIRQ = 1 *)
  apply (metis Kernel_Config.maxIRQ_def of_nat_numeral uint_nat unat_maxIRQ)?
  done

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma ucast_maxIRQ[simp]:
  "\<lbrakk> LENGTH(irq_len) \<le> LENGTH('a::len); LENGTH(irq_len) \<le> LENGTH('b::len) \<rbrakk> \<Longrightarrow>
   UCAST ('a \<rightarrow> 'b) Kernel_Config.maxIRQ = Kernel_Config.maxIRQ"
  by (metis of_nat_maxIRQ ucast_nat_def unat_maxIRQ)

(* Safe for [simp] because we don't cast down from irq type *)
lemma maxIRQ_less_upcast[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow>
   (Kernel_Config.maxIRQ < (ucast irq :: 'a word)) = (Kernel_Config.maxIRQ < irq)" for irq::irq
  by (simp add: word_less_nat_alt unat_ucast_up_simp)

(* Safe for [simp] because we don't cast down from irq type *)
lemma maxIRQ_le_upcast[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow>
   ((ucast irq :: 'a word) \<le> Kernel_Config.maxIRQ) = (irq \<le> Kernel_Config.maxIRQ)" for irq::irq
  by (simp add: word_le_nat_alt unat_ucast_up_simp)

lemma maxIRQ_ucast_toEnum_eq_irq:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow> toEnum (unat x) = (ucast x :: irq)" for x::machine_word
  by (simp add: word_le_nat_alt Kernel_Config.maxIRQ_def)

lemma Kernel_Config_maxIRQ_ucast_toEnum_eq:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow> toEnum (unat x) = x" for x::machine_word
  by (simp add: word_le_nat_alt Kernel_Config.maxIRQ_def)

(* The following are derived and no longer need to unfold, but are small enough to include here *)
lemma leq_maxIRQ_leq_mask_irq_len:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow> x \<le> mask LENGTH(irq_len)" for x :: machine_word
  by (erule order_trans, rule maxIRQ_leq_mask_irq_len)

lemma ucast_eq_irqInvalid_conv:
  "x \<le> Kernel_Config.maxIRQ \<Longrightarrow> (ucast x = irqInvalid) = (x = ucast irqInvalid)" for x :: machine_word
  unfolding irqInvalid_def
  using leq_maxIRQ_leq_mask_irq_len
  by (simp add: ucast_0_eq_left)

lemma ucast_irq_bounded_machine_word:
  "(ucast irq :: machine_word) < 2 ^ irq_len" for irq::irq
  by (simp add: word_less_nat_alt unat_ucast_upcast is_up unat_2p_irq_len_machine unat_irq_bounded)

end
end
