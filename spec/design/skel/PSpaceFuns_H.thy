(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Physical Memory Functions"

theory PSpaceFuns_H
imports
  ObjectInstances_H
  FaultMonad_H
  "../../lib/DataMap"
begin

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs decls_only Data.Map=DataMap NOT PSpace ptrBits ptrBitsForSize lookupAround maybeToMonad lookupAround2 typeError alignError alignCheck sizeCheck objBits

consts
lookupAround2 :: "('k :: {linorder,finite}) \<Rightarrow> ( 'k , 'a ) DataMap.map \<Rightarrow> (('k * 'a) option * 'k option)"

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs bodies_only Data.Map=DataMap NOT PSpace ptrBits ptrBitsForSize lookupAround maybeToMonad typeError alignError alignCheck sizeCheck objBits deletionIsSafe cNodePartialOverlap pointerInUserData ksASIDMapSafe

end
