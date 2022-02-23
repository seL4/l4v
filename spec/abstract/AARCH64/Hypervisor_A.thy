(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* FIXME AARCH64: verbatim setup copy of RISCV64; needs adjustment and validation;
                  only minimal type-check changes performed so far if any *)

(* FIXME AARCH64: base this on ARM_HYP *)

chapter "Handle Hypervisor Fault Events"

theory Hypervisor_A
imports Exceptions_A
begin

context Arch begin global_naming RISCV64_A

fun handle_hypervisor_fault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> (unit, 'z::state_ext) s_monad"
  where
  "handle_hypervisor_fault thread RISCVNoHypFaults = return ()"

end
end