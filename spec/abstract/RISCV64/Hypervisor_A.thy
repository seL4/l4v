(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Handle Hypervisor Fault Events"

theory Hypervisor_A
imports "../Exceptions_A"
begin

context Arch begin global_naming RISCV64_A

fun handle_hypervisor_fault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> (unit, 'z::state_ext) s_monad"
  where
  "handle_hypervisor_fault thread RISCVNoHypFaults = return ()"

end
end