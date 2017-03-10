(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchHypervisor_H.thy *)
(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
  Hypervisor stub for ARM
*)

theory ArchHypervisor_H
imports
  "../CNode_H"
  "../KI_Decls_H"
begin
context Arch begin global_naming ARM_H


consts'
handleHypervisorFault :: "machine_word \<Rightarrow> hyp_fault_type \<Rightarrow> unit kernel"

defs handleHypervisorFault_def:
"handleHypervisorFault x0 x1\<equiv> (case x1 of
    (ARMNoHypFaults) \<Rightarrow>    return ()
  )"


end
end
