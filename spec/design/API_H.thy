(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file API_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "The API"

theory API_H
imports Syscall_H Delete_H
begin

text {* collects all API modules *}

definition
callKernel :: "event \<Rightarrow> unit kernel"
where
"callKernel ev\<equiv> (do
    runErrorT $ handleEvent ev
        `~catchError~` (\<lambda> _. withoutPreemption $ (do
                      irq \<leftarrow> doMachineOp getActiveIRQ;
                      when (isJust irq) $ handleInterrupt (fromJust irq)
        od)
                                                                        );
    schedule;
    activateThread
od)"


end
