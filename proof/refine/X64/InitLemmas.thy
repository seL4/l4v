(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* General lemmas removed from KernelInit *)

theory InitLemmas
imports IncKernelInit
begin

declare headM_tailM_Cons[simp]

declare cart_singletons[simp]

declare  less_1_simp[simp]

declare  is_aligned_no_overflow[simp]

declare unless_True[simp]

declare maybe_fail_bind_fail[simp]

crunch setPriority
  for cte_wp_at'[wp]: "cte_wp_at' P p" (simp: crunch_simps)
crunch setPriority
  for irq_node'[wp]: "\<lambda>s. P (irq_node' s)" (simp: crunch_simps)

end
