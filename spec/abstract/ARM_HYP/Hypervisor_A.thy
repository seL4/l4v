(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Handle Hyperviser Fault Event"

theory Hypervisor_A
imports "../Exceptions_A"
begin

context Arch begin global_naming ARM_A

fun handle_hypervisor_fault :: "word32 \<Rightarrow> hyp_fault_type \<Rightarrow> (unit, 'z::state_ext) f_monad"
where
"handle_hypervisor_fault thread ARMNoHypFaults = fail"


end
end