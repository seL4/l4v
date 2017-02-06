(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file FaultHandler_H.thy *)
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

theory FaultHandler_H
imports FaultHandlerDecls_H TCB_H
  "./$L4V_ARCH/ArchFaultHandler_H"
begin

context begin interpretation Arch .
requalify_consts
  syscallMessage
  fromVPtr
  exceptionMessage
  debugPrint
  makeArchFaultMessage
  handleArchFaultReply
end


defs handleFault_def:
"handleFault tptr ex\<equiv> (
    sendFaultIPC tptr ex `~catchFailure~` handleDoubleFault tptr ex
)"

defs sendFaultIPC_def:
"sendFaultIPC tptr fault\<equiv> (doE
    handlerCPtr \<leftarrow> withoutFailure $ threadGet tcbFaultHandler tptr;
    handlerCap \<leftarrow> capFaultOnFailure handlerCPtr False $
        lookupCap tptr handlerCPtr;
    (case handlerCap of
          EndpointCap _ _ True _ True \<Rightarrow>  
          withoutFailure $ (do
            threadSet (\<lambda> tcb. tcb \<lparr>tcbFault := Just fault\<rparr>) tptr;
            sendIPC True False (capEPBadge handlerCap)
                True tptr (capEPPtr handlerCap)
          od)
        | _ \<Rightarrow>   throw $ CapFault handlerCPtr False $
            MissingCapability_ \<lparr> missingCapBitsLeft= 0 \<rparr>
        )
odE)"

defs handleDoubleFault_def:
"handleDoubleFault tptr ex1 ex2\<equiv> (do
        setThreadState Inactive tptr;
        faultPC \<leftarrow> asUser tptr getRestartPC;
        errmsg \<leftarrow> return ( [] @ (show ex2)
                @ [] @ (show ex1)
                @ [] @ (show tptr)
                @ [] @ (show faultPC));
        doMachineOp $ debugPrint errmsg
od)"

consts'
makeFaultMessage :: "fault \<Rightarrow> machine_word \<Rightarrow> (machine_word * machine_word list) kernel"

consts'
handleFaultReply :: "fault \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word list \<Rightarrow> bool kernel"

defs makeFaultMessage_def:
"makeFaultMessage x0 thread\<equiv> (case x0 of
    (CapFault cptr rp lf) \<Rightarrow>    (do
    pc \<leftarrow> asUser thread getRestartPC;
    return (1,
        pc#fromCPtr cptr#fromIntegral (fromEnum rp)#msgFromLookupFailure lf)
    od)
  | (UnknownSyscallException n) \<Rightarrow>    (do
    msg \<leftarrow> asUser thread $ mapM getRegister syscallMessage;
    return (2, msg @ [n])
  od)
  | (UserException exception code) \<Rightarrow>    (do
    msg \<leftarrow> asUser thread $ mapM getRegister exceptionMessage;
    return (3, msg @ [exception, code])
  od)
  | (ArchFault af) \<Rightarrow>    makeArchFaultMessage af thread
  )"

defs handleFaultReply_def:
"handleFaultReply x0 thread label msg\<equiv> (case x0 of
    (CapFault _ _ _) \<Rightarrow>    return True
  | (UnknownSyscallException _) \<Rightarrow>    (do
    t \<leftarrow> threadGet id thread;
    asUser thread $ zipWithM_x
        (\<lambda> r v. setRegister r $ sanitiseRegister t r v)
        syscallMessage msg;
    return (label = 0)
  od)
  | (UserException _ _) \<Rightarrow>    (do
    t \<leftarrow> threadGet id thread;
    asUser thread $ zipWithM_x
        (\<lambda> r v. setRegister r $ sanitiseRegister t r v)
        exceptionMessage msg;
    return (label = 0)
  od)
  | (ArchFault af) \<Rightarrow>   
    handleArchFaultReply af thread label msg
  )"


end
