(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file NotificationDecls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for Notifications"

theory NotificationDecls_H imports    "FaultMonad_H"
 begin

consts'
receiveBlocked :: "thread_state \<Rightarrow> bool"

consts'
sendSignal :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
doNBRecvFailedTransfer :: "machine_word \<Rightarrow> unit kernel"

consts'
receiveSignal :: "machine_word \<Rightarrow> capability \<Rightarrow> bool \<Rightarrow> unit kernel"

consts'
cancelAllSignals :: "machine_word \<Rightarrow> unit kernel"

consts'
cancelSignal :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
completeSignal :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
getNotification :: "machine_word \<Rightarrow> notification kernel"

consts'
setNotification :: "machine_word \<Rightarrow> notification \<Rightarrow> unit kernel"

consts'
bindNotification :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
doUnbindNotification :: "machine_word \<Rightarrow> notification \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
unbindNotification :: "machine_word \<Rightarrow> unit kernel"

consts'
unbindMaybeNotification :: "machine_word \<Rightarrow> unit kernel"


end
