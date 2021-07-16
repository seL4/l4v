(*
 * Copyright 2021, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Kernel Configuration"

theory Kernel_Config
imports Platform
begin

text \<open>
  seL4's build system allows configuration of some architecture-independent variables, such as the
  number of domains.

  This theory contains shared definitions used by both the abstract and design specifications,
  to prevent multiple points of update.

  The long-term goal is to make the proofs resilient in the face of changes of these configuration
  options, possibly loading their values directly from the build system configuration. For this
  reason, definitions of variables used here should remain hidden, and their unfolding should be
  avoided whenever possible.\<close>

definition numDomains :: nat where
  "numDomains \<equiv> 16"

lemma numDomains_not_zero:
  "numDomains > 0"
  unfolding Kernel_Config.numDomains_def
  by simp

lemma numDomains_machine_word_safe:
  "unat (of_nat numDomains :: machine_word) = numDomains"
  unfolding Kernel_Config.numDomains_def by simp

hide_fact (open) numDomains_def

end
