(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file EndpointDecls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for Endpoints"

theory EndpointDecls_H
imports FaultMonad_H
begin

consts'
sendIPC :: "bool \<Rightarrow> bool \<Rightarrow> machine_word \<Rightarrow> bool \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
isActive :: "notification \<Rightarrow> bool"

consts'
receiveIPC :: "machine_word \<Rightarrow> capability \<Rightarrow> bool \<Rightarrow> unit kernel"

consts'
replyFromKernel :: "machine_word \<Rightarrow> (machine_word * machine_word list) \<Rightarrow> unit kernel"

consts'
cancelIPC :: "machine_word \<Rightarrow> unit kernel"

consts'
cancelAllIPC :: "machine_word \<Rightarrow> unit kernel"

consts'
cancelBadgedSends :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
getEndpoint :: "machine_word \<Rightarrow> endpoint kernel"

consts'
setEndpoint :: "machine_word \<Rightarrow> endpoint \<Rightarrow> unit kernel"


end
