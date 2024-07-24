(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Handle Hyperviser Fault Event"

theory Hypervisor_A
imports Exceptions_A
begin

context Arch begin arch_global_naming (A)

fun handle_hypervisor_fault :: "word32 \<Rightarrow> hyp_fault_type \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
"handle_hypervisor_fault thread ARMNoHypFaults = return ()"


end
end
