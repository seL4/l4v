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

theory ArchVSpace_H
imports
  "../CNode_H"
  "../KI_Decls_H"
  ArchVSpaceDecls_H
begin
context Arch begin global_naming ARM_H


#INCLUDE_HASKELL SEL4/Kernel/VSpace/ARM.lhs CONTEXT ARM_H bodies_only ArchInv=ArchRetypeDecls_H.ARM ArchLabels=ArchInvocationLabels_H.ARM NOT checkPDAt checkPTAt checkPDASIDMapMembership checkValidMappingSize vptrFromPPtr

defs checkValidMappingSize_def:
  "checkValidMappingSize sz \<equiv> stateAssert
    (\<lambda>s. 2 ^ pageBitsForSize sz <= gsMaxObjectSize s) []"

end
end
