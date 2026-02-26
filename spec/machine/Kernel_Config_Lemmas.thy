(*
 * Copyright 2021, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-independent lemmas constraining Kernel_Config definitions *)

theory Kernel_Config_Lemmas
imports "$L4V_ARCH/Kernel_Config"
begin

text \<open>
  seL4's build system allows configuration of some architecture-independent constants, such as the
  number of domains.

  The long-term goal is to make the proofs resilient in the face of changes of these configuration
  options. To this end this theory contains properties of these constants, to avoid unfolding
  their values later in the proofs.\<close>

lemma numDomains_not_zero:
  "numDomains > 0"
  unfolding Kernel_Config.numDomains_def
  by simp

lemma numDomains_machine_word_safe:
  "unat (of_nat numDomains :: machine_word) = numDomains"
  unfolding Kernel_Config.numDomains_def by simp

(* C stores the domain field in the top 8 bits of domain schedule entries. *)
definition domainBits :: nat where
  "domainBits \<equiv> 8"

lemma numDomains_fits_domainBits:
  "numDomains < 2^domainBits"
  by (simp add: Kernel_Config.numDomains_def domainBits_def)

end
