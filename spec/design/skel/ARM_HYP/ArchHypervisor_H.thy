(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
  VSpace lookup code.
*)

theory ArchHypervisor_H
imports
  "../CNode_H"
(*  "../KI_Decls_H"
  ArchVSpaceDecls_H *)
begin
context Arch begin global_naming ARM_HYP_H


#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/ARM_HYP.lhs Arch= CONTEXT ARM_HYP_H decls_only

defs handleHypervisorFault_def:
"handleHypervisorFault arg1 hyp \<equiv> case hyp of ARMNoHypFaults \<Rightarrow> haskell_fail []"


end
end
