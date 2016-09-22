(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file KI_Decls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Initialisation"

theory KI_Decls_H
imports
  ThreadDecls_H
  KernelInitMonad_H
begin

consts'
noInitFailure :: "'a kernel_init_state \<Rightarrow> 'a kernel_init"

consts'
minNum4kUntypedObj :: "nat"

consts'
maxNumFreememRegions :: "nat"

consts'
getAPRegion :: "paddr \<Rightarrow> region list kernel_init"

consts'
initFreemem :: "paddr \<Rightarrow> region \<Rightarrow> unit kernel_init"

consts'
allocRegion :: "nat \<Rightarrow> paddr kernel_init"

consts'
initKernel :: "vptr \<Rightarrow> vptr \<Rightarrow> paddr list \<Rightarrow> paddr list \<Rightarrow> paddr list \<Rightarrow> unit kernel"

consts'
finaliseBIFrame :: "unit kernel_init"

consts'
createInitialThread :: "capability \<Rightarrow> capability \<Rightarrow> capability \<Rightarrow> vptr \<Rightarrow> vptr \<Rightarrow> vptr \<Rightarrow> unit kernel_init"

consts'
createIdleThread :: "unit kernel_init"

consts'
createUntypedObject :: "capability \<Rightarrow> region \<Rightarrow> unit kernel_init"

consts'
mapTaskRegions :: "(paddr * vptr) list \<Rightarrow> ((vptr * machine_word) * (vptr * machine_word)) kernel_init"

consts'
allocFrame :: "paddr kernel_init"

consts'
makeRootCNode :: "capability kernel_init"

consts'
provideCap :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel_init"

consts'
provideUntypedCap :: "capability \<Rightarrow> bool \<Rightarrow> paddr \<Rightarrow> word8 \<Rightarrow> machine_word \<Rightarrow> unit kernel_init"

consts'
coverOf :: "region list \<Rightarrow> region"


end
