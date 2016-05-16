(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Config_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Config_H
imports Types_H
begin

definition
minFreeSlots :: "nat"
where
"minFreeSlots \<equiv> 128"

definition
minSmallBlocks :: "nat"
where
"minSmallBlocks \<equiv> 16"

definition
rootCNodeSize :: "nat"
where
"rootCNodeSize \<equiv> 12"

definition
timeSlice :: "nat"
where
"timeSlice \<equiv> 5"

definition
numDomains :: "nat"
where
"numDomains \<equiv> 16"

definition
numPriorities :: "nat"
where
"numPriorities \<equiv> 256"

definition
retypeFanOutLimit :: "machine_word"
where
"retypeFanOutLimit \<equiv> 256"

definition
resetChunkBits :: "nat"
where
"resetChunkBits \<equiv> 8"


end
