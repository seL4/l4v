(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  VSpace lookup code.
*)

theory ArchVSpace_H
imports
  CNode_H
  Untyped_H
  KI_Decls_H
  ArchVSpaceDecls_H
  ArchHypervisor_H
begin
context Arch begin arch_global_naming (H)


#INCLUDE_HASKELL SEL4/Kernel/VSpace/ARM.lhs CONTEXT ARM_H bodies_only ArchInv=ArchRetypeDecls_H.ARM ArchLabels=ArchInvocationLabels_H.ARM NOT checkPDAt checkPTAt checkPDASIDMapMembership checkValidMappingSize vptrFromPPtr

defs checkValidMappingSize_def:
  "checkValidMappingSize sz \<equiv> stateAssert
    (\<lambda>s. 2 ^ pageBitsForSize sz <= gsMaxObjectSize s) []"

end
end
