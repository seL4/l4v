(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file FaultHandlerDecls_H.thy *)
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
	Declarations from SEL4.Kernel.FaultHandler
*)

chapter "Function Declarations for Fault Handlers"

theory FaultHandlerDecls_H
imports Structures_H FaultMonad_H
begin

consts'
handleFault :: "machine_word \<Rightarrow> fault \<Rightarrow> unit kernel"

consts'
sendFaultIPC :: "machine_word \<Rightarrow> fault \<Rightarrow> ( fault , unit ) kernel_f"

consts'
handleDoubleFault :: "machine_word \<Rightarrow> fault \<Rightarrow> fault \<Rightarrow> unit kernel"


end
