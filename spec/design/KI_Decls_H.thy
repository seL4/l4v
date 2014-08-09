(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Initialisation"

theory KI_Decls_H
imports
  ThreadDecls_H
  KernelInitMonad_H
begin

consts
allocRegion :: "nat \<Rightarrow> paddr kernel_init"

consts
allocFrame :: "paddr kernel_init"

consts
allocPage :: "(vptr * machine_word * machine_word) kernel_init"

consts
mapForInitTask :: "paddr \<Rightarrow> vptr \<Rightarrow> unit kernel_init"

consts
makeRootCNode :: "capability kernel_init"

consts
allocRootSlot :: "(cptr * machine_word) kernel_init"

consts
allocRootSlotWithColour :: "machine_word \<Rightarrow> (cptr * machine_word) kernel_init"

consts
requestRootSlot :: "cptr \<Rightarrow> (machine_word) kernel_init"

consts
makeSlots :: "unit kernel_init"

consts
provideCap :: "capability \<Rightarrow> (cptr * machine_word) kernel_init"

consts
provideRegion :: "boot_region \<Rightarrow> unit kernel_init"

consts
mergeBRs :: "boot_region \<Rightarrow> boot_region \<Rightarrow> nat \<Rightarrow> boot_region option"

consts
addRegionWithMerge :: "boot_region \<Rightarrow> nat \<Rightarrow> unit kernel_init"

consts
initKernel :: "vptr \<Rightarrow> paddr list \<Rightarrow> vptr \<Rightarrow> paddr list \<Rightarrow> paddr list \<Rightarrow> unit kernel"

consts
mapTaskRegions :: "(paddr * vptr) list \<Rightarrow> ((vptr * machine_word) * (vptr * machine_word)) kernel_init"

consts
createInitCaps :: "capability \<Rightarrow> (vptr * machine_word) \<Rightarrow> capability kernel_init"

consts
createUntypedCaps :: "unit kernel_init"

consts
storeLargeBlock :: "(paddr * nat) \<Rightarrow> unit kernel_init"

consts
makeBlockList :: "paddr \<Rightarrow> paddr \<Rightarrow> (paddr * nat) list"

consts
countUntypedCaps :: "nat kernel_init"

consts
getUntypedRegions :: "(paddr * paddr) list kernel_init"

consts
createDeviceCaps :: "unit kernel_init"

consts
createSmallBlockCaps :: "unit kernel_init"

consts
storeSmallBlockCaps :: "capability list \<Rightarrow> unit kernel_init"

consts
storeSmallBlockCap :: "capability \<Rightarrow> unit kernel_init"

consts
createFreeSlotRegions :: "unit kernel_init"

consts
createEmptyRegions :: "unit kernel_init"


end
