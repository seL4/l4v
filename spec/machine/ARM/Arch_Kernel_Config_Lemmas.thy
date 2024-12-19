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

context Arch begin global_naming ARM

(* note: 24 = pageBitsForSize ARMSuperSection, we do not have access to ASpec at this point *)
lemma physBase_aligned:
  "is_aligned physBase 24"
  by (simp add: is_aligned_def Kernel_Config.physBase_def)


(* maxIRQ conditions *)

lemma maxIRQ_less_2p_irqBits:
  "(maxIRQ::nat) < 2^irqBits"
  by (simp add: Kernel_Config.maxIRQ_def Kernel_Config.irqBits_def)

(* follows from value_type definition of irq_len *)
lemma LENGTH_irq_len_irqBits[simp]: (* [simp] will fire only for simp del: len_of_numeral_defs *)
  "LENGTH(irq_len) = irqBits"
  using irq_len_def irq_len_val
  by simp

lemma maxIRQ_less_2p_irq_len:
  "(maxIRQ::nat) < 2^LENGTH(irq_len)"
  using maxIRQ_less_2p_irqBits
  by (simp del: len_of_numeral_defs)

(* maxIRQ as a generic numeral allows us to write rules about casts/unat/uint etc without
   mentioning numbers: *)

lemma of_nat_maxIRQ[simp]:
  "of_nat maxIRQ = (maxIRQ::'a::len word)"
  by (simp add: Kernel_Config.maxIRQ_def)

lemma of_int_maxIRQ[simp]:
  "of_int maxIRQ = (maxIRQ::'a::len word)"
  by (simp add: Kernel_Config.maxIRQ_def)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma unat_maxIRQ[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow> unat (maxIRQ::'a word) = maxIRQ"
  by (metis maxIRQ_less_2p_irq_len Word.of_nat_unat of_nat_inverse of_nat_maxIRQ unat_ucast_up_simp)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma uint_maxIRQ[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow> uint (maxIRQ::'a word) = maxIRQ"
  by (metis Kernel_Config.maxIRQ_def of_nat_numeral uint_nat unat_maxIRQ)

(* Safe for [simp] because we don't use maxIRQ at lower than irq_len *)
lemma ucast_maxIRQ[simp]:
  "\<lbrakk> LENGTH(irq_len) \<le> LENGTH('a::len); LENGTH(irq_len) \<le> LENGTH('b::len) \<rbrakk> \<Longrightarrow>
   UCAST ('a \<rightarrow> 'b) maxIRQ = maxIRQ"
  by (metis of_nat_maxIRQ ucast_nat_def unat_maxIRQ)

(* Safe for [simp] because we don't cast down from irq type *)
lemma maxIRQ_less_upcast[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow>
   (maxIRQ < (ucast irq :: 'a word)) = (maxIRQ < irq)" for irq::irq
  by (simp add: word_less_nat_alt unat_ucast_up_simp)

(* Safe for [simp] because we don't cast down from irq type *)
lemma maxIRQ_le_upcast[simp]:
  "LENGTH(irq_len) \<le> LENGTH('a::len) \<Longrightarrow>
   ((ucast irq :: 'a word) \<le> Kernel_Config.maxIRQ) = (irq \<le> Kernel_Config.maxIRQ)" for irq::irq
  by (simp add: word_le_nat_alt unat_ucast_up_simp)

(* The following are instances -- for some we could derive general rules, but the number of
   instances is limited and the concrete proofs are much simpler: *)

lemma le_maxIRQ_machine_less_irqBits_val[simplified]:
  "w \<le> maxIRQ \<Longrightarrow> unat w < 2^LENGTH(irq_len)" for w::machine_word
  using maxIRQ_less_2p_irq_len
  by (simp add: word_le_nat_alt)

lemma irq_machine_le_maxIRQ_irq:
  "irq \<le> Kernel_Config.maxIRQ \<Longrightarrow> (ucast irq::irq) \<le> maxIRQ" for irq::machine_word
  by (simp add: Kernel_Config.maxIRQ_def word_le_nat_alt unat_ucast)

lemma maxIRQ_eq_ucast_irq_32_signed_uint:
  "(maxIRQ = (ucast b :: int_word)) = (uint b = maxIRQ)" for b::irq
  unfolding Kernel_Config.maxIRQ_def
  apply uint_arith
  apply (simp add: uint_up_ucast is_up)
  done

lemma sint_maxIRQ_32[simp]:
  "sint (maxIRQ :: int_word) = maxIRQ"
  by (simp add: Kernel_Config.maxIRQ_def)

lemma scast_maxIRQ_32_machine[simp]:
  "scast (maxIRQ :: int_word) = (maxIRQ::machine_word)"
  by (simp add: Kernel_Config.maxIRQ_def)

lemma scast_maxIRQ_32_irq[simp]:
  "scast (maxIRQ :: int_word) = (maxIRQ::irq)"
  by (simp add: Kernel_Config.maxIRQ_def)

lemma maxIRQ_ucast_toEnum_eq_machine:
  "x \<le> maxIRQ \<Longrightarrow> toEnum (unat x) = x" for x::machine_word
  by (simp add: word_le_nat_alt Kernel_Config.maxIRQ_def)

lemma maxIRQ_ucast_toEnum_eq_irq:
  "x \<le> maxIRQ \<Longrightarrow> toEnum (unat x) = (ucast x :: irq)" for x::machine_word
  by (simp add: word_le_nat_alt Kernel_Config.maxIRQ_def)

lemma maxIRQ_1_plus_eq_Suc_machine[simp]:
  "unat (1 + maxIRQ :: machine_word) = Suc Kernel_Config.maxIRQ"
  by (simp add: Kernel_Config.maxIRQ_def)


(* cacheLineBits conditions *)

(* Folding cacheLineBits_val in C functions only works reliably if cacheLineBits is not 1 and
   not too large to conflict with other values used inside cache ops.
   10 is ptBits, which is only available after ExecSpec. Anything > 1 and smaller than ptBits
   works. *)
lemma cacheLineBits_sanity:
  "cacheLineBits \<in> {2..10}"
  by (simp add: cacheLineBits_def Kernel_Config.CONFIG_L1_CACHE_LINE_SIZE_BITS_def)

end
end
