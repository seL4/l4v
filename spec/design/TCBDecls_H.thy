(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file TCBDecls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for TCBs"

theory TCBDecls_H
imports FaultMonad_H Invocations_H
begin

context begin interpretation Arch .
requalify_types
  user_monad
end

consts'
decodeTCBInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> capability \<Rightarrow> machine_word \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeCopyRegisters :: "machine_word list \<Rightarrow> capability \<Rightarrow> capability list \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeReadRegisters :: "machine_word list \<Rightarrow> capability \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeWriteRegisters :: "machine_word list \<Rightarrow> capability \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeTCBConfigure :: "machine_word list \<Rightarrow> capability \<Rightarrow> machine_word \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
checkPrio :: "machine_word \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
decodeSetPriority :: "machine_word list \<Rightarrow> capability \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeSetMCPriority :: "machine_word list \<Rightarrow> capability \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeSetIPCBuffer :: "machine_word list \<Rightarrow> capability \<Rightarrow> machine_word \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeSetSpace :: "machine_word list \<Rightarrow> capability \<Rightarrow> machine_word \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeBindNotification :: "capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
decodeUnbindNotification :: "capability \<Rightarrow> ( syscall_error , tcbinvocation ) kernel_f"

consts'
invokeTCB :: "tcbinvocation \<Rightarrow> machine_word list kernel_p"

consts'
decodeDomainInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , (machine_word * domain) ) kernel_f"

consts'
checkCapAt :: "capability \<Rightarrow> machine_word \<Rightarrow> unit kernel \<Rightarrow> unit kernel"

consts'
assertDerived :: "machine_word \<Rightarrow> capability \<Rightarrow> 'a kernel \<Rightarrow> 'a kernel"

consts'
setMessageInfo :: "machine_word \<Rightarrow> message_info \<Rightarrow> unit kernel"

consts'
getMessageInfo :: "machine_word \<Rightarrow> message_info kernel"

consts'
setMRs :: "machine_word \<Rightarrow> (machine_word) option \<Rightarrow> machine_word list \<Rightarrow> machine_word kernel"

consts'
getMRs :: "machine_word \<Rightarrow> (machine_word) option \<Rightarrow> message_info \<Rightarrow> machine_word list kernel"

consts'
copyMRs :: "machine_word \<Rightarrow> (machine_word) option \<Rightarrow> machine_word \<Rightarrow> (machine_word) option \<Rightarrow> machine_word \<Rightarrow> machine_word kernel"

consts'
getExtraCPtrs :: "(machine_word) option \<Rightarrow> message_info \<Rightarrow> cptr list kernel"

consts'
lookupExtraCaps :: "machine_word \<Rightarrow> (machine_word) option \<Rightarrow> message_info \<Rightarrow> ( fault , ((capability * machine_word) list) ) kernel_f"

consts'
getExtraCPtr :: "machine_word \<Rightarrow> nat \<Rightarrow> cptr kernel"

consts'
setExtraBadge :: "machine_word \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> unit kernel"

consts'
bufferCPtrOffset :: "machine_word"

consts'
setupCallerCap :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
deleteCallerCap :: "machine_word \<Rightarrow> unit kernel"

consts'
getThreadCSpaceRoot :: "machine_word \<Rightarrow> (machine_word) kernel"

consts'
getThreadVSpaceRoot :: "machine_word \<Rightarrow> (machine_word) kernel"

consts'
getThreadReplySlot :: "machine_word \<Rightarrow> (machine_word) kernel"

consts'
getThreadCallerSlot :: "machine_word \<Rightarrow> (machine_word) kernel"

consts'
getThreadBufferSlot :: "machine_word \<Rightarrow> (machine_word) kernel"

consts'
threadGet :: "(tcb \<Rightarrow> 'a) \<Rightarrow> machine_word \<Rightarrow> 'a kernel"

consts'
threadSet :: "(tcb \<Rightarrow> tcb) \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
asUser :: "machine_word \<Rightarrow> 'a user_monad \<Rightarrow> 'a kernel"

consts'
sanitiseRegister :: "tcb \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word"


end
