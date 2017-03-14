(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchThread_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Threads"

theory ArchThread_H
imports
  ArchThreadDecls_H
  "../TCBDecls_H"
  ArchVSpaceDecls_H
begin


context Arch begin global_naming X64_H

defs switchToThread_def:
"switchToThread tcb \<equiv> setVMRoot tcb"

defs configureIdleThread_def:
"configureIdleThread arg1 \<equiv> error []"

defs switchToIdleThread_def:
"switchToIdleThread\<equiv> return ()"

defs activateIdleThread_def:
"activateIdleThread arg1 \<equiv> return ()"


end (* context X64 *)

end
