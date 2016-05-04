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
context Arch begin global_naming ARM_H

defs switchToThread_def:
"switchToThread tcb\<equiv> (do
    setVMRoot tcb;
    globals \<leftarrow> gets $ armKSGlobalsFrame \<circ> ksArchState;
    bufferPtr \<leftarrow> threadGet tcbIPCBuffer tcb;
    storeWordUser globals $ fromVPtr bufferPtr;
    doMachineOp $ ARM.clearExMonitor
od)"

defs configureIdleThread_def:
"configureIdleThread tcb\<equiv> (
    doKernelOp $ asUser tcb $ (do
        setRegister (Register CPSR) 0x1f;
        setRegister (Register LR_svc) $ fromVPtr idleThreadStart
    od)
)"

defs switchToIdleThread_def:
"switchToIdleThread\<equiv> (do
 globals \<leftarrow> gets $ armKSGlobalsFrame \<circ> ksArchState;
 storeWordUser globals 0
od)"

defs activateIdleThread_def:
"activateIdleThread arg1 \<equiv> return ()"


end
end
