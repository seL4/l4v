(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Physical Memory Functions"

theory PSpaceFuns_H
imports
  ObjectInstances_H
  FaultMonad_H
  ArchPSpace_H
  "Lib.DataMap"
begin

(* Haskell expects this with Arch prefix *)
requalify_consts (in Arch)
  deleteGhost

definition deleteRange :: "( machine_word , 'a ) DataMap.map \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> ( machine_word , 'a ) DataMap.map"
where "deleteRange m ptr bits \<equiv>
        let inRange = (\<lambda> x. x && ((- mask bits) - 1) = fromPPtr ptr) in
        data_map_filterWithKey (\<lambda> x _. Not (inRange x)) m"

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs decls_only Data.Map=DataMap NOT PSpace ptrBits ptrBitsForSize lookupAround maybeToMonad lookupAround2 typeError alignError alignCheck sizeCheck objBits deleteRange

consts
lookupAround2 :: "('k :: {linorder,finite}) \<Rightarrow> ( 'k , 'a ) DataMap.map \<Rightarrow> (('k * 'a) option * 'k option)"

#INCLUDE_HASKELL SEL4/Model/PSpace.lhs bodies_only Data.Map=DataMap NOT PSpace ptrBits ptrBitsForSize lookupAround maybeToMonad typeError alignError alignCheck sizeCheck objBits deletionIsSafe deletionIsSafe_delete_locale cNodePartialOverlap pointerInUserData ksASIDMapSafe deleteRange

end
