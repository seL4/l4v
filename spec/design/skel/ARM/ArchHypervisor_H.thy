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


#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/ARM.lhs Arch= CONTEXT ARM_H decls_only ArchInv= ArchLabels=
#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/ARM.lhs Arch= CONTEXT ARM_H bodies_only ArchInv= ArchLabels=

end
end
