(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchFaultHandler_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Fault Handlers"

theory ArchFaultHandler_H
imports "../TCB_H" "../Structures_H"
begin

context Arch begin global_naming ARM_H



consts'
makeArchFaultMessage :: "arch_fault \<Rightarrow> machine_word \<Rightarrow> (machine_word * machine_word list) kernel"

consts'
handleArchFaultReply :: "arch_fault \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word list \<Rightarrow> bool kernel"

defs makeArchFaultMessage_def:
"makeArchFaultMessage x0 thread\<equiv> (case x0 of
    (VMFault vptr archData) \<Rightarrow>    (do
    pc \<leftarrow> asUser thread getRestartPC;
    return (5, pc#fromVPtr vptr#archData)
    od)
  )"

defs handleArchFaultReply_def:
"handleArchFaultReply x0 x1 x2 x3\<equiv> (case x0 of
    (VMFault _ _) \<Rightarrow>    return True
  )"


end


end
