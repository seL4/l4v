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

end
