(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Function Declarations for Asynchronous Endpoints"

theory AsyncEndpointDecls_H imports    "FaultMonad_H"
 begin

consts
receiveBlocked :: "thread_state \<Rightarrow> bool"

consts
sendAsyncIPC :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
receiveAsyncIPC :: "machine_word \<Rightarrow> capability \<Rightarrow> unit kernel"

consts
aepCancelAll :: "machine_word \<Rightarrow> unit kernel"

consts
asyncIPCCancel :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
completeAsyncIPC :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
getAsyncEP :: "machine_word \<Rightarrow> async_endpoint kernel"

consts
setAsyncEP :: "machine_word \<Rightarrow> async_endpoint \<Rightarrow> unit kernel"

consts
bindAsyncEndpoint :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
doUnbindAEP :: "machine_word \<Rightarrow> async_endpoint \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
unbindAsyncEndpoint :: "machine_word \<Rightarrow> unit kernel"

consts
unbindMaybeAEP :: "machine_word \<Rightarrow> unit kernel"


end
