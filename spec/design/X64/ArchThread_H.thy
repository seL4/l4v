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


context X64 begin

defs baseToGDTDataWord_def:
"baseToGDTDataWord p \<equiv> error []"

defs switchToThread_def:
"switchToThread tcb\<equiv> (do
    setVMRoot tcb;
    gdt \<leftarrow> gets $ x64KSGDT \<circ> ksArchState;
    base \<leftarrow> asUser tcb $ getRegister (Register MachineTypes.TLS_BASE);
    gdt_tls_slot \<leftarrow> return ( fromIntegral (fromEnum MachineTypes.GDT_TLS) `~shiftL~` gdteBits);
    doMachineOp $ storeWord (gdt + gdt_tls_slot) $ baseToGDTDataWord $ base;
    bufferPtr \<leftarrow> threadGet tcbIPCBuffer tcb;
    gdt_ipcbuf_slot \<leftarrow> return ( fromIntegral (fromEnum MachineTypes.GDT_IPCBUF) `~shiftL~` gdteBits);
    doMachineOp $ storeWord (gdt + gdt_ipcbuf_slot) $ baseToGDTDataWord $ fromVPtr bufferPtr
od)"

defs configureIdleThread_def:
"configureIdleThread arg1 \<equiv> error []"

defs switchToIdleThread_def:
"switchToIdleThread\<equiv> return ()"

defs activateIdleThread_def:
"activateIdleThread arg1 \<equiv> return ()"


end (* context X64 *)

end
