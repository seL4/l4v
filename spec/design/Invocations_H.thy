(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Invocations_H
imports
  Structures_H
  "./$L4V_ARCH/ArchRetypeDecls_H"
  "./$L4V_ARCH/ArchLabelFuns_H"
begin

datatype tcbinvocation =
    Suspend machine_word
  | Resume machine_word
  | ThreadControl machine_word machine_word "cptr option" "priority option" "(capability * machine_word) option" "(capability * machine_word) option" "(vptr * (capability * machine_word) option) option"
  | NotificationControl machine_word "(machine_word) option"
  | WriteRegisters machine_word bool "machine_word list" ArchRetypeDecls_H.copy_register_sets
  | ReadRegisters machine_word bool machine_word ArchRetypeDecls_H.copy_register_sets
  | CopyRegisters machine_word machine_word bool bool bool bool ArchRetypeDecls_H.copy_register_sets

primrec
  notificationPtr :: "tcbinvocation \<Rightarrow> (machine_word) option"
where
  "notificationPtr (NotificationControl v0 v1) = v1"

primrec
  readRegsSuspend :: "tcbinvocation \<Rightarrow> bool"
where
  "readRegsSuspend (ReadRegisters v0 v1 v2 v3) = v1"

primrec
  writeRegsValues :: "tcbinvocation \<Rightarrow> machine_word list"
where
  "writeRegsValues (WriteRegisters v0 v1 v2 v3) = v2"

primrec
  tcThreadCapSlot :: "tcbinvocation \<Rightarrow> machine_word"
where
  "tcThreadCapSlot (ThreadControl v0 v1 v2 v3 v4 v5 v6) = v1"

primrec
  copyRegsSource :: "tcbinvocation \<Rightarrow> machine_word"
where
  "copyRegsSource (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = v1"

primrec
  tcNewCRoot :: "tcbinvocation \<Rightarrow> (capability * machine_word) option"
where
  "tcNewCRoot (ThreadControl v0 v1 v2 v3 v4 v5 v6) = v4"

primrec
  copyRegsTarget :: "tcbinvocation \<Rightarrow> machine_word"
where
  "copyRegsTarget (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = v0"

primrec
  notificationTCB :: "tcbinvocation \<Rightarrow> machine_word"
where
  "notificationTCB (NotificationControl v0 v1) = v0"

primrec
  writeRegsResume :: "tcbinvocation \<Rightarrow> bool"
where
  "writeRegsResume (WriteRegisters v0 v1 v2 v3) = v1"

primrec
  resumeThread :: "tcbinvocation \<Rightarrow> machine_word"
where
  "resumeThread (Resume v0) = v0"

primrec
  suspendThread :: "tcbinvocation \<Rightarrow> machine_word"
where
  "suspendThread (Suspend v0) = v0"

primrec
  tcNewIPCBuffer :: "tcbinvocation \<Rightarrow> (vptr * (capability * machine_word) option) option"
where
  "tcNewIPCBuffer (ThreadControl v0 v1 v2 v3 v4 v5 v6) = v6"

primrec
  tcThread :: "tcbinvocation \<Rightarrow> machine_word"
where
  "tcThread (ThreadControl v0 v1 v2 v3 v4 v5 v6) = v0"

primrec
  copyRegsResumeTarget :: "tcbinvocation \<Rightarrow> bool"
where
  "copyRegsResumeTarget (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = v3"

primrec
  copyRegsTransferArch :: "tcbinvocation \<Rightarrow> ArchRetypeDecls_H.copy_register_sets"
where
  "copyRegsTransferArch (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = v6"

primrec
  readRegsArch :: "tcbinvocation \<Rightarrow> ArchRetypeDecls_H.copy_register_sets"
where
  "readRegsArch (ReadRegisters v0 v1 v2 v3) = v3"

primrec
  readRegsThread :: "tcbinvocation \<Rightarrow> machine_word"
where
  "readRegsThread (ReadRegisters v0 v1 v2 v3) = v0"

primrec
  copyRegsSuspendSource :: "tcbinvocation \<Rightarrow> bool"
where
  "copyRegsSuspendSource (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = v2"

primrec
  tcNewPriority :: "tcbinvocation \<Rightarrow> priority option"
where
  "tcNewPriority (ThreadControl v0 v1 v2 v3 v4 v5 v6) = v3"

primrec
  copyRegsTransferFrame :: "tcbinvocation \<Rightarrow> bool"
where
  "copyRegsTransferFrame (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = v4"

primrec
  writeRegsThread :: "tcbinvocation \<Rightarrow> machine_word"
where
  "writeRegsThread (WriteRegisters v0 v1 v2 v3) = v0"

primrec
  writeRegsArch :: "tcbinvocation \<Rightarrow> ArchRetypeDecls_H.copy_register_sets"
where
  "writeRegsArch (WriteRegisters v0 v1 v2 v3) = v3"

primrec
  tcNewFaultEP :: "tcbinvocation \<Rightarrow> cptr option"
where
  "tcNewFaultEP (ThreadControl v0 v1 v2 v3 v4 v5 v6) = v2"

primrec
  copyRegsTransferInteger :: "tcbinvocation \<Rightarrow> bool"
where
  "copyRegsTransferInteger (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = v5"

primrec
  tcNewVRoot :: "tcbinvocation \<Rightarrow> (capability * machine_word) option"
where
  "tcNewVRoot (ThreadControl v0 v1 v2 v3 v4 v5 v6) = v5"

primrec
  readRegsLength :: "tcbinvocation \<Rightarrow> machine_word"
where
  "readRegsLength (ReadRegisters v0 v1 v2 v3) = v2"

primrec
  notificationPtr_update :: "(((machine_word) option) \<Rightarrow> ((machine_word) option)) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "notificationPtr_update f (NotificationControl v0 v1) = NotificationControl v0 (f v1)"

primrec
  readRegsSuspend_update :: "(bool \<Rightarrow> bool) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "readRegsSuspend_update f (ReadRegisters v0 v1 v2 v3) = ReadRegisters v0 (f v1) v2 v3"

primrec
  writeRegsValues_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "writeRegsValues_update f (WriteRegisters v0 v1 v2 v3) = WriteRegisters v0 v1 (f v2) v3"

primrec
  tcThreadCapSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "tcThreadCapSlot_update f (ThreadControl v0 v1 v2 v3 v4 v5 v6) = ThreadControl v0 (f v1) v2 v3 v4 v5 v6"

primrec
  copyRegsSource_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "copyRegsSource_update f (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = CopyRegisters v0 (f v1) v2 v3 v4 v5 v6"

primrec
  tcNewCRoot_update :: "(((capability * machine_word) option) \<Rightarrow> ((capability * machine_word) option)) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "tcNewCRoot_update f (ThreadControl v0 v1 v2 v3 v4 v5 v6) = ThreadControl v0 v1 v2 v3 (f v4) v5 v6"

primrec
  copyRegsTarget_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "copyRegsTarget_update f (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = CopyRegisters (f v0) v1 v2 v3 v4 v5 v6"

primrec
  notificationTCB_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "notificationTCB_update f (NotificationControl v0 v1) = NotificationControl (f v0) v1"

primrec
  writeRegsResume_update :: "(bool \<Rightarrow> bool) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "writeRegsResume_update f (WriteRegisters v0 v1 v2 v3) = WriteRegisters v0 (f v1) v2 v3"

primrec
  resumeThread_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "resumeThread_update f (Resume v0) = Resume (f v0)"

primrec
  suspendThread_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "suspendThread_update f (Suspend v0) = Suspend (f v0)"

primrec
  tcNewIPCBuffer_update :: "(((vptr * (capability * machine_word) option) option) \<Rightarrow> ((vptr * (capability * machine_word) option) option)) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "tcNewIPCBuffer_update f (ThreadControl v0 v1 v2 v3 v4 v5 v6) = ThreadControl v0 v1 v2 v3 v4 v5 (f v6)"

primrec
  tcThread_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "tcThread_update f (ThreadControl v0 v1 v2 v3 v4 v5 v6) = ThreadControl (f v0) v1 v2 v3 v4 v5 v6"

primrec
  copyRegsResumeTarget_update :: "(bool \<Rightarrow> bool) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "copyRegsResumeTarget_update f (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = CopyRegisters v0 v1 v2 (f v3) v4 v5 v6"

primrec
  copyRegsTransferArch_update :: "(ArchRetypeDecls_H.copy_register_sets \<Rightarrow> ArchRetypeDecls_H.copy_register_sets) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "copyRegsTransferArch_update f (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = CopyRegisters v0 v1 v2 v3 v4 v5 (f v6)"

primrec
  readRegsArch_update :: "(ArchRetypeDecls_H.copy_register_sets \<Rightarrow> ArchRetypeDecls_H.copy_register_sets) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "readRegsArch_update f (ReadRegisters v0 v1 v2 v3) = ReadRegisters v0 v1 v2 (f v3)"

primrec
  readRegsThread_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "readRegsThread_update f (ReadRegisters v0 v1 v2 v3) = ReadRegisters (f v0) v1 v2 v3"

primrec
  copyRegsSuspendSource_update :: "(bool \<Rightarrow> bool) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "copyRegsSuspendSource_update f (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = CopyRegisters v0 v1 (f v2) v3 v4 v5 v6"

primrec
  tcNewPriority_update :: "((priority option) \<Rightarrow> (priority option)) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "tcNewPriority_update f (ThreadControl v0 v1 v2 v3 v4 v5 v6) = ThreadControl v0 v1 v2 (f v3) v4 v5 v6"

primrec
  copyRegsTransferFrame_update :: "(bool \<Rightarrow> bool) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "copyRegsTransferFrame_update f (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = CopyRegisters v0 v1 v2 v3 (f v4) v5 v6"

primrec
  writeRegsThread_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "writeRegsThread_update f (WriteRegisters v0 v1 v2 v3) = WriteRegisters (f v0) v1 v2 v3"

primrec
  writeRegsArch_update :: "(ArchRetypeDecls_H.copy_register_sets \<Rightarrow> ArchRetypeDecls_H.copy_register_sets) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "writeRegsArch_update f (WriteRegisters v0 v1 v2 v3) = WriteRegisters v0 v1 v2 (f v3)"

primrec
  tcNewFaultEP_update :: "((cptr option) \<Rightarrow> (cptr option)) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "tcNewFaultEP_update f (ThreadControl v0 v1 v2 v3 v4 v5 v6) = ThreadControl v0 v1 (f v2) v3 v4 v5 v6"

primrec
  copyRegsTransferInteger_update :: "(bool \<Rightarrow> bool) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "copyRegsTransferInteger_update f (CopyRegisters v0 v1 v2 v3 v4 v5 v6) = CopyRegisters v0 v1 v2 v3 v4 (f v5) v6"

primrec
  tcNewVRoot_update :: "(((capability * machine_word) option) \<Rightarrow> ((capability * machine_word) option)) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "tcNewVRoot_update f (ThreadControl v0 v1 v2 v3 v4 v5 v6) = ThreadControl v0 v1 v2 v3 v4 (f v5) v6"

primrec
  readRegsLength_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> tcbinvocation \<Rightarrow> tcbinvocation"
where
  "readRegsLength_update f (ReadRegisters v0 v1 v2 v3) = ReadRegisters v0 v1 (f v2) v3"

abbreviation (input)
  Suspend_trans :: "(machine_word) \<Rightarrow> tcbinvocation" ("Suspend'_ \<lparr> suspendThread= _ \<rparr>")
where
  "Suspend_ \<lparr> suspendThread= v0 \<rparr> == Suspend v0"

abbreviation (input)
  Resume_trans :: "(machine_word) \<Rightarrow> tcbinvocation" ("Resume'_ \<lparr> resumeThread= _ \<rparr>")
where
  "Resume_ \<lparr> resumeThread= v0 \<rparr> == Resume v0"

abbreviation (input)
  ThreadControl_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (cptr option) \<Rightarrow> (priority option) \<Rightarrow> ((capability * machine_word) option) \<Rightarrow> ((capability * machine_word) option) \<Rightarrow> ((vptr * (capability * machine_word) option) option) \<Rightarrow> tcbinvocation" ("ThreadControl'_ \<lparr> tcThread= _, tcThreadCapSlot= _, tcNewFaultEP= _, tcNewPriority= _, tcNewCRoot= _, tcNewVRoot= _, tcNewIPCBuffer= _ \<rparr>")
where
  "ThreadControl_ \<lparr> tcThread= v0, tcThreadCapSlot= v1, tcNewFaultEP= v2, tcNewPriority= v3, tcNewCRoot= v4, tcNewVRoot= v5, tcNewIPCBuffer= v6 \<rparr> == ThreadControl v0 v1 v2 v3 v4 v5 v6"

abbreviation (input)
  NotificationControl_trans :: "(machine_word) \<Rightarrow> ((machine_word) option) \<Rightarrow> tcbinvocation" ("NotificationControl'_ \<lparr> notificationTCB= _, notificationPtr= _ \<rparr>")
where
  "NotificationControl_ \<lparr> notificationTCB= v0, notificationPtr= v1 \<rparr> == NotificationControl v0 v1"

abbreviation (input)
  WriteRegisters_trans :: "(machine_word) \<Rightarrow> (bool) \<Rightarrow> (machine_word list) \<Rightarrow> (ArchRetypeDecls_H.copy_register_sets) \<Rightarrow> tcbinvocation" ("WriteRegisters'_ \<lparr> writeRegsThread= _, writeRegsResume= _, writeRegsValues= _, writeRegsArch= _ \<rparr>")
where
  "WriteRegisters_ \<lparr> writeRegsThread= v0, writeRegsResume= v1, writeRegsValues= v2, writeRegsArch= v3 \<rparr> == WriteRegisters v0 v1 v2 v3"

abbreviation (input)
  ReadRegisters_trans :: "(machine_word) \<Rightarrow> (bool) \<Rightarrow> (machine_word) \<Rightarrow> (ArchRetypeDecls_H.copy_register_sets) \<Rightarrow> tcbinvocation" ("ReadRegisters'_ \<lparr> readRegsThread= _, readRegsSuspend= _, readRegsLength= _, readRegsArch= _ \<rparr>")
where
  "ReadRegisters_ \<lparr> readRegsThread= v0, readRegsSuspend= v1, readRegsLength= v2, readRegsArch= v3 \<rparr> == ReadRegisters v0 v1 v2 v3"

abbreviation (input)
  CopyRegisters_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (ArchRetypeDecls_H.copy_register_sets) \<Rightarrow> tcbinvocation" ("CopyRegisters'_ \<lparr> copyRegsTarget= _, copyRegsSource= _, copyRegsSuspendSource= _, copyRegsResumeTarget= _, copyRegsTransferFrame= _, copyRegsTransferInteger= _, copyRegsTransferArch= _ \<rparr>")
where
  "CopyRegisters_ \<lparr> copyRegsTarget= v0, copyRegsSource= v1, copyRegsSuspendSource= v2, copyRegsResumeTarget= v3, copyRegsTransferFrame= v4, copyRegsTransferInteger= v5, copyRegsTransferArch= v6 \<rparr> == CopyRegisters v0 v1 v2 v3 v4 v5 v6"

definition
  isSuspend :: "tcbinvocation \<Rightarrow> bool"
where
 "isSuspend v \<equiv> case v of
    Suspend v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isResume :: "tcbinvocation \<Rightarrow> bool"
where
 "isResume v \<equiv> case v of
    Resume v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isThreadControl :: "tcbinvocation \<Rightarrow> bool"
where
 "isThreadControl v \<equiv> case v of
    ThreadControl v0 v1 v2 v3 v4 v5 v6 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isNotificationControl :: "tcbinvocation \<Rightarrow> bool"
where
 "isNotificationControl v \<equiv> case v of
    NotificationControl v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isWriteRegisters :: "tcbinvocation \<Rightarrow> bool"
where
 "isWriteRegisters v \<equiv> case v of
    WriteRegisters v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isReadRegisters :: "tcbinvocation \<Rightarrow> bool"
where
 "isReadRegisters v \<equiv> case v of
    ReadRegisters v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isCopyRegisters :: "tcbinvocation \<Rightarrow> bool"
where
 "isCopyRegisters v \<equiv> case v of
    CopyRegisters v0 v1 v2 v3 v4 v5 v6 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype cnode_invocation =
    Insert capability machine_word machine_word
  | Rotate capability capability machine_word machine_word machine_word
  | Revoke machine_word
  | Move capability machine_word machine_word
  | Recycle machine_word
  | SaveCaller machine_word
  | Delete machine_word

primrec
  targetSlot :: "cnode_invocation \<Rightarrow> machine_word"
where
  "targetSlot (Insert v0 v1 v2) = v2"
| "targetSlot (Rotate v0 v1 v2 v3 v4) = v4"
| "targetSlot (SaveCaller v0) = v0"
| "targetSlot (Move v0 v1 v2) = v2"
| "targetSlot (Recycle v0) = v0"
| "targetSlot (Revoke v0) = v0"
| "targetSlot (Delete v0) = v0"

primrec
  pivotSlot :: "cnode_invocation \<Rightarrow> machine_word"
where
  "pivotSlot (Rotate v0 v1 v2 v3 v4) = v3"

primrec
  moveCap2 :: "cnode_invocation \<Rightarrow> capability"
where
  "moveCap2 (Rotate v0 v1 v2 v3 v4) = v1"

primrec
  moveCap1 :: "cnode_invocation \<Rightarrow> capability"
where
  "moveCap1 (Rotate v0 v1 v2 v3 v4) = v0"

primrec
  insertCap :: "cnode_invocation \<Rightarrow> capability"
where
  "insertCap (Insert v0 v1 v2) = v0"

primrec
  sourceSlot :: "cnode_invocation \<Rightarrow> machine_word"
where
  "sourceSlot (Insert v0 v1 v2) = v1"
| "sourceSlot (Rotate v0 v1 v2 v3 v4) = v2"
| "sourceSlot (Move v0 v1 v2) = v1"

primrec
  moveCap :: "cnode_invocation \<Rightarrow> capability"
where
  "moveCap (Move v0 v1 v2) = v0"

primrec
  targetSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> cnode_invocation \<Rightarrow> cnode_invocation"
where
  "targetSlot_update f (Insert v0 v1 v2) = Insert v0 v1 (f v2)"
| "targetSlot_update f (Rotate v0 v1 v2 v3 v4) = Rotate v0 v1 v2 v3 (f v4)"
| "targetSlot_update f (SaveCaller v0) = SaveCaller (f v0)"
| "targetSlot_update f (Move v0 v1 v2) = Move v0 v1 (f v2)"
| "targetSlot_update f (Recycle v0) = Recycle (f v0)"
| "targetSlot_update f (Revoke v0) = Revoke (f v0)"
| "targetSlot_update f (Delete v0) = Delete (f v0)"

primrec
  pivotSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> cnode_invocation \<Rightarrow> cnode_invocation"
where
  "pivotSlot_update f (Rotate v0 v1 v2 v3 v4) = Rotate v0 v1 v2 (f v3) v4"

primrec
  moveCap2_update :: "(capability \<Rightarrow> capability) \<Rightarrow> cnode_invocation \<Rightarrow> cnode_invocation"
where
  "moveCap2_update f (Rotate v0 v1 v2 v3 v4) = Rotate v0 (f v1) v2 v3 v4"

primrec
  moveCap1_update :: "(capability \<Rightarrow> capability) \<Rightarrow> cnode_invocation \<Rightarrow> cnode_invocation"
where
  "moveCap1_update f (Rotate v0 v1 v2 v3 v4) = Rotate (f v0) v1 v2 v3 v4"

primrec
  insertCap_update :: "(capability \<Rightarrow> capability) \<Rightarrow> cnode_invocation \<Rightarrow> cnode_invocation"
where
  "insertCap_update f (Insert v0 v1 v2) = Insert (f v0) v1 v2"

primrec
  sourceSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> cnode_invocation \<Rightarrow> cnode_invocation"
where
  "sourceSlot_update f (Insert v0 v1 v2) = Insert v0 (f v1) v2"
| "sourceSlot_update f (Rotate v0 v1 v2 v3 v4) = Rotate v0 v1 (f v2) v3 v4"
| "sourceSlot_update f (Move v0 v1 v2) = Move v0 (f v1) v2"

primrec
  moveCap_update :: "(capability \<Rightarrow> capability) \<Rightarrow> cnode_invocation \<Rightarrow> cnode_invocation"
where
  "moveCap_update f (Move v0 v1 v2) = Move (f v0) v1 v2"

abbreviation (input)
  Insert_trans :: "(capability) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> cnode_invocation" ("Insert'_ \<lparr> insertCap= _, sourceSlot= _, targetSlot= _ \<rparr>")
where
  "Insert_ \<lparr> insertCap= v0, sourceSlot= v1, targetSlot= v2 \<rparr> == Insert v0 v1 v2"

abbreviation (input)
  Rotate_trans :: "(capability) \<Rightarrow> (capability) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> cnode_invocation" ("Rotate'_ \<lparr> moveCap1= _, moveCap2= _, sourceSlot= _, pivotSlot= _, targetSlot= _ \<rparr>")
where
  "Rotate_ \<lparr> moveCap1= v0, moveCap2= v1, sourceSlot= v2, pivotSlot= v3, targetSlot= v4 \<rparr> == Rotate v0 v1 v2 v3 v4"

abbreviation (input)
  Revoke_trans :: "(machine_word) \<Rightarrow> cnode_invocation" ("Revoke'_ \<lparr> targetSlot= _ \<rparr>")
where
  "Revoke_ \<lparr> targetSlot= v0 \<rparr> == Revoke v0"

abbreviation (input)
  Move_trans :: "(capability) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> cnode_invocation" ("Move'_ \<lparr> moveCap= _, sourceSlot= _, targetSlot= _ \<rparr>")
where
  "Move_ \<lparr> moveCap= v0, sourceSlot= v1, targetSlot= v2 \<rparr> == Move v0 v1 v2"

abbreviation (input)
  Recycle_trans :: "(machine_word) \<Rightarrow> cnode_invocation" ("Recycle'_ \<lparr> targetSlot= _ \<rparr>")
where
  "Recycle_ \<lparr> targetSlot= v0 \<rparr> == Recycle v0"

abbreviation (input)
  SaveCaller_trans :: "(machine_word) \<Rightarrow> cnode_invocation" ("SaveCaller'_ \<lparr> targetSlot= _ \<rparr>")
where
  "SaveCaller_ \<lparr> targetSlot= v0 \<rparr> == SaveCaller v0"

abbreviation (input)
  Delete_trans :: "(machine_word) \<Rightarrow> cnode_invocation" ("Delete'_ \<lparr> targetSlot= _ \<rparr>")
where
  "Delete_ \<lparr> targetSlot= v0 \<rparr> == Delete v0"

definition
  isInsert :: "cnode_invocation \<Rightarrow> bool"
where
 "isInsert v \<equiv> case v of
    Insert v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isRotate :: "cnode_invocation \<Rightarrow> bool"
where
 "isRotate v \<equiv> case v of
    Rotate v0 v1 v2 v3 v4 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isRevoke :: "cnode_invocation \<Rightarrow> bool"
where
 "isRevoke v \<equiv> case v of
    Revoke v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isMove :: "cnode_invocation \<Rightarrow> bool"
where
 "isMove v \<equiv> case v of
    Move v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isRecycle :: "cnode_invocation \<Rightarrow> bool"
where
 "isRecycle v \<equiv> case v of
    Recycle v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSaveCaller :: "cnode_invocation \<Rightarrow> bool"
where
 "isSaveCaller v \<equiv> case v of
    SaveCaller v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isDelete :: "cnode_invocation \<Rightarrow> bool"
where
 "isDelete v \<equiv> case v of
    Delete v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype untyped_invocation =
    Retype machine_word machine_word machine_word object_type nat "machine_word list"

primrec
  retypeSource :: "untyped_invocation \<Rightarrow> machine_word"
where
  "retypeSource (Retype v0 v1 v2 v3 v4 v5) = v0"

primrec
  retypeNewType :: "untyped_invocation \<Rightarrow> object_type"
where
  "retypeNewType (Retype v0 v1 v2 v3 v4 v5) = v3"

primrec
  retypeRegionBase :: "untyped_invocation \<Rightarrow> machine_word"
where
  "retypeRegionBase (Retype v0 v1 v2 v3 v4 v5) = v1"

primrec
  retypeSlots :: "untyped_invocation \<Rightarrow> machine_word list"
where
  "retypeSlots (Retype v0 v1 v2 v3 v4 v5) = v5"

primrec
  retypeFreeRegionBase :: "untyped_invocation \<Rightarrow> machine_word"
where
  "retypeFreeRegionBase (Retype v0 v1 v2 v3 v4 v5) = v2"

primrec
  retypeNewSizeBits :: "untyped_invocation \<Rightarrow> nat"
where
  "retypeNewSizeBits (Retype v0 v1 v2 v3 v4 v5) = v4"

primrec
  retypeSource_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> untyped_invocation \<Rightarrow> untyped_invocation"
where
  "retypeSource_update f (Retype v0 v1 v2 v3 v4 v5) = Retype (f v0) v1 v2 v3 v4 v5"

primrec
  retypeNewType_update :: "(object_type \<Rightarrow> object_type) \<Rightarrow> untyped_invocation \<Rightarrow> untyped_invocation"
where
  "retypeNewType_update f (Retype v0 v1 v2 v3 v4 v5) = Retype v0 v1 v2 (f v3) v4 v5"

primrec
  retypeRegionBase_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> untyped_invocation \<Rightarrow> untyped_invocation"
where
  "retypeRegionBase_update f (Retype v0 v1 v2 v3 v4 v5) = Retype v0 (f v1) v2 v3 v4 v5"

primrec
  retypeSlots_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> untyped_invocation \<Rightarrow> untyped_invocation"
where
  "retypeSlots_update f (Retype v0 v1 v2 v3 v4 v5) = Retype v0 v1 v2 v3 v4 (f v5)"

primrec
  retypeFreeRegionBase_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> untyped_invocation \<Rightarrow> untyped_invocation"
where
  "retypeFreeRegionBase_update f (Retype v0 v1 v2 v3 v4 v5) = Retype v0 v1 (f v2) v3 v4 v5"

primrec
  retypeNewSizeBits_update :: "(nat \<Rightarrow> nat) \<Rightarrow> untyped_invocation \<Rightarrow> untyped_invocation"
where
  "retypeNewSizeBits_update f (Retype v0 v1 v2 v3 v4 v5) = Retype v0 v1 v2 v3 (f v4) v5"

abbreviation (input)
  Retype_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (object_type) \<Rightarrow> (nat) \<Rightarrow> (machine_word list) \<Rightarrow> untyped_invocation" ("Retype'_ \<lparr> retypeSource= _, retypeRegionBase= _, retypeFreeRegionBase= _, retypeNewType= _, retypeNewSizeBits= _, retypeSlots= _ \<rparr>")
where
  "Retype_ \<lparr> retypeSource= v0, retypeRegionBase= v1, retypeFreeRegionBase= v2, retypeNewType= v3, retypeNewSizeBits= v4, retypeSlots= v5 \<rparr> == Retype v0 v1 v2 v3 v4 v5"

lemma retypeSource_retypeSource_update [simp]:
  "retypeSource (retypeSource_update f v) = f (retypeSource v)"
  by (cases v) simp

lemma retypeSource_retypeNewType_update [simp]:
  "retypeSource (retypeNewType_update f v) = retypeSource v"
  by (cases v) simp

lemma retypeSource_retypeRegionBase_update [simp]:
  "retypeSource (retypeRegionBase_update f v) = retypeSource v"
  by (cases v) simp

lemma retypeSource_retypeSlots_update [simp]:
  "retypeSource (retypeSlots_update f v) = retypeSource v"
  by (cases v) simp

lemma retypeSource_retypeFreeRegionBase_update [simp]:
  "retypeSource (retypeFreeRegionBase_update f v) = retypeSource v"
  by (cases v) simp

lemma retypeSource_retypeNewSizeBits_update [simp]:
  "retypeSource (retypeNewSizeBits_update f v) = retypeSource v"
  by (cases v) simp

lemma retypeNewType_retypeSource_update [simp]:
  "retypeNewType (retypeSource_update f v) = retypeNewType v"
  by (cases v) simp

lemma retypeNewType_retypeNewType_update [simp]:
  "retypeNewType (retypeNewType_update f v) = f (retypeNewType v)"
  by (cases v) simp

lemma retypeNewType_retypeRegionBase_update [simp]:
  "retypeNewType (retypeRegionBase_update f v) = retypeNewType v"
  by (cases v) simp

lemma retypeNewType_retypeSlots_update [simp]:
  "retypeNewType (retypeSlots_update f v) = retypeNewType v"
  by (cases v) simp

lemma retypeNewType_retypeFreeRegionBase_update [simp]:
  "retypeNewType (retypeFreeRegionBase_update f v) = retypeNewType v"
  by (cases v) simp

lemma retypeNewType_retypeNewSizeBits_update [simp]:
  "retypeNewType (retypeNewSizeBits_update f v) = retypeNewType v"
  by (cases v) simp

lemma retypeRegionBase_retypeSource_update [simp]:
  "retypeRegionBase (retypeSource_update f v) = retypeRegionBase v"
  by (cases v) simp

lemma retypeRegionBase_retypeNewType_update [simp]:
  "retypeRegionBase (retypeNewType_update f v) = retypeRegionBase v"
  by (cases v) simp

lemma retypeRegionBase_retypeRegionBase_update [simp]:
  "retypeRegionBase (retypeRegionBase_update f v) = f (retypeRegionBase v)"
  by (cases v) simp

lemma retypeRegionBase_retypeSlots_update [simp]:
  "retypeRegionBase (retypeSlots_update f v) = retypeRegionBase v"
  by (cases v) simp

lemma retypeRegionBase_retypeFreeRegionBase_update [simp]:
  "retypeRegionBase (retypeFreeRegionBase_update f v) = retypeRegionBase v"
  by (cases v) simp

lemma retypeRegionBase_retypeNewSizeBits_update [simp]:
  "retypeRegionBase (retypeNewSizeBits_update f v) = retypeRegionBase v"
  by (cases v) simp

lemma retypeSlots_retypeSource_update [simp]:
  "retypeSlots (retypeSource_update f v) = retypeSlots v"
  by (cases v) simp

lemma retypeSlots_retypeNewType_update [simp]:
  "retypeSlots (retypeNewType_update f v) = retypeSlots v"
  by (cases v) simp

lemma retypeSlots_retypeRegionBase_update [simp]:
  "retypeSlots (retypeRegionBase_update f v) = retypeSlots v"
  by (cases v) simp

lemma retypeSlots_retypeSlots_update [simp]:
  "retypeSlots (retypeSlots_update f v) = f (retypeSlots v)"
  by (cases v) simp

lemma retypeSlots_retypeFreeRegionBase_update [simp]:
  "retypeSlots (retypeFreeRegionBase_update f v) = retypeSlots v"
  by (cases v) simp

lemma retypeSlots_retypeNewSizeBits_update [simp]:
  "retypeSlots (retypeNewSizeBits_update f v) = retypeSlots v"
  by (cases v) simp

lemma retypeFreeRegionBase_retypeSource_update [simp]:
  "retypeFreeRegionBase (retypeSource_update f v) = retypeFreeRegionBase v"
  by (cases v) simp

lemma retypeFreeRegionBase_retypeNewType_update [simp]:
  "retypeFreeRegionBase (retypeNewType_update f v) = retypeFreeRegionBase v"
  by (cases v) simp

lemma retypeFreeRegionBase_retypeRegionBase_update [simp]:
  "retypeFreeRegionBase (retypeRegionBase_update f v) = retypeFreeRegionBase v"
  by (cases v) simp

lemma retypeFreeRegionBase_retypeSlots_update [simp]:
  "retypeFreeRegionBase (retypeSlots_update f v) = retypeFreeRegionBase v"
  by (cases v) simp

lemma retypeFreeRegionBase_retypeFreeRegionBase_update [simp]:
  "retypeFreeRegionBase (retypeFreeRegionBase_update f v) = f (retypeFreeRegionBase v)"
  by (cases v) simp

lemma retypeFreeRegionBase_retypeNewSizeBits_update [simp]:
  "retypeFreeRegionBase (retypeNewSizeBits_update f v) = retypeFreeRegionBase v"
  by (cases v) simp

lemma retypeNewSizeBits_retypeSource_update [simp]:
  "retypeNewSizeBits (retypeSource_update f v) = retypeNewSizeBits v"
  by (cases v) simp

lemma retypeNewSizeBits_retypeNewType_update [simp]:
  "retypeNewSizeBits (retypeNewType_update f v) = retypeNewSizeBits v"
  by (cases v) simp

lemma retypeNewSizeBits_retypeRegionBase_update [simp]:
  "retypeNewSizeBits (retypeRegionBase_update f v) = retypeNewSizeBits v"
  by (cases v) simp

lemma retypeNewSizeBits_retypeSlots_update [simp]:
  "retypeNewSizeBits (retypeSlots_update f v) = retypeNewSizeBits v"
  by (cases v) simp

lemma retypeNewSizeBits_retypeFreeRegionBase_update [simp]:
  "retypeNewSizeBits (retypeFreeRegionBase_update f v) = retypeNewSizeBits v"
  by (cases v) simp

lemma retypeNewSizeBits_retypeNewSizeBits_update [simp]:
  "retypeNewSizeBits (retypeNewSizeBits_update f v) = f (retypeNewSizeBits v)"
  by (cases v) simp

datatype irqcontrol_invocation =
    ArchIRQControl ArchRetypeDecls_H.irqcontrol_invocation
  | IssueIRQHandler irq machine_word machine_word

primrec
  issueHandlerSlot :: "irqcontrol_invocation \<Rightarrow> machine_word"
where
  "issueHandlerSlot (IssueIRQHandler v0 v1 v2) = v1"

primrec
  issueHandlerIRQ :: "irqcontrol_invocation \<Rightarrow> irq"
where
  "issueHandlerIRQ (IssueIRQHandler v0 v1 v2) = v0"

primrec
  issueHandlerControllerSlot :: "irqcontrol_invocation \<Rightarrow> machine_word"
where
  "issueHandlerControllerSlot (IssueIRQHandler v0 v1 v2) = v2"

primrec
  archIRQControl :: "irqcontrol_invocation \<Rightarrow> ArchRetypeDecls_H.irqcontrol_invocation"
where
  "archIRQControl (ArchIRQControl v0) = v0"

primrec
  issueHandlerSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> irqcontrol_invocation \<Rightarrow> irqcontrol_invocation"
where
  "issueHandlerSlot_update f (IssueIRQHandler v0 v1 v2) = IssueIRQHandler v0 (f v1) v2"

primrec
  issueHandlerIRQ_update :: "(irq \<Rightarrow> irq) \<Rightarrow> irqcontrol_invocation \<Rightarrow> irqcontrol_invocation"
where
  "issueHandlerIRQ_update f (IssueIRQHandler v0 v1 v2) = IssueIRQHandler (f v0) v1 v2"

primrec
  issueHandlerControllerSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> irqcontrol_invocation \<Rightarrow> irqcontrol_invocation"
where
  "issueHandlerControllerSlot_update f (IssueIRQHandler v0 v1 v2) = IssueIRQHandler v0 v1 (f v2)"

primrec
  archIRQControl_update :: "(ArchRetypeDecls_H.irqcontrol_invocation \<Rightarrow> ArchRetypeDecls_H.irqcontrol_invocation) \<Rightarrow> irqcontrol_invocation \<Rightarrow> irqcontrol_invocation"
where
  "archIRQControl_update f (ArchIRQControl v0) = ArchIRQControl (f v0)"

abbreviation (input)
  ArchIRQControl_trans :: "(ArchRetypeDecls_H.irqcontrol_invocation) \<Rightarrow> irqcontrol_invocation" ("ArchIRQControl'_ \<lparr> archIRQControl= _ \<rparr>")
where
  "ArchIRQControl_ \<lparr> archIRQControl= v0 \<rparr> == ArchIRQControl v0"

abbreviation (input)
  IssueIRQHandler_trans :: "(irq) \<Rightarrow> (machine_word) \<Rightarrow> (machine_word) \<Rightarrow> irqcontrol_invocation" ("IssueIRQHandler'_ \<lparr> issueHandlerIRQ= _, issueHandlerSlot= _, issueHandlerControllerSlot= _ \<rparr>")
where
  "IssueIRQHandler_ \<lparr> issueHandlerIRQ= v0, issueHandlerSlot= v1, issueHandlerControllerSlot= v2 \<rparr> == IssueIRQHandler v0 v1 v2"

definition
  isArchIRQControl :: "irqcontrol_invocation \<Rightarrow> bool"
where
 "isArchIRQControl v \<equiv> case v of
    ArchIRQControl v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIssueIRQHandler :: "irqcontrol_invocation \<Rightarrow> bool"
where
 "isIssueIRQHandler v \<equiv> case v of
    IssueIRQHandler v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype irqhandler_invocation =
    AckIRQ irq
  | ClearIRQHandler irq
  | SetMode irq bool bool
  | SetIRQHandler irq capability machine_word

primrec
  modeIRQ :: "irqhandler_invocation \<Rightarrow> irq"
where
  "modeIRQ (SetMode v0 v1 v2) = v0"

primrec
  modeTrigger :: "irqhandler_invocation \<Rightarrow> bool"
where
  "modeTrigger (SetMode v0 v1 v2) = v1"

primrec
  irqHandlerIRQ :: "irqhandler_invocation \<Rightarrow> irq"
where
  "irqHandlerIRQ (AckIRQ v0) = v0"
| "irqHandlerIRQ (ClearIRQHandler v0) = v0"
| "irqHandlerIRQ (SetIRQHandler v0 v1 v2) = v0"

primrec
  setIRQHandlerCap :: "irqhandler_invocation \<Rightarrow> capability"
where
  "setIRQHandlerCap (SetIRQHandler v0 v1 v2) = v1"

primrec
  modePolarity :: "irqhandler_invocation \<Rightarrow> bool"
where
  "modePolarity (SetMode v0 v1 v2) = v2"

primrec
  setIRQHandlerSlot :: "irqhandler_invocation \<Rightarrow> machine_word"
where
  "setIRQHandlerSlot (SetIRQHandler v0 v1 v2) = v2"

primrec
  modeIRQ_update :: "(irq \<Rightarrow> irq) \<Rightarrow> irqhandler_invocation \<Rightarrow> irqhandler_invocation"
where
  "modeIRQ_update f (SetMode v0 v1 v2) = SetMode (f v0) v1 v2"

primrec
  modeTrigger_update :: "(bool \<Rightarrow> bool) \<Rightarrow> irqhandler_invocation \<Rightarrow> irqhandler_invocation"
where
  "modeTrigger_update f (SetMode v0 v1 v2) = SetMode v0 (f v1) v2"

primrec
  irqHandlerIRQ_update :: "(irq \<Rightarrow> irq) \<Rightarrow> irqhandler_invocation \<Rightarrow> irqhandler_invocation"
where
  "irqHandlerIRQ_update f (AckIRQ v0) = AckIRQ (f v0)"
| "irqHandlerIRQ_update f (ClearIRQHandler v0) = ClearIRQHandler (f v0)"
| "irqHandlerIRQ_update f (SetIRQHandler v0 v1 v2) = SetIRQHandler (f v0) v1 v2"

primrec
  setIRQHandlerCap_update :: "(capability \<Rightarrow> capability) \<Rightarrow> irqhandler_invocation \<Rightarrow> irqhandler_invocation"
where
  "setIRQHandlerCap_update f (SetIRQHandler v0 v1 v2) = SetIRQHandler v0 (f v1) v2"

primrec
  modePolarity_update :: "(bool \<Rightarrow> bool) \<Rightarrow> irqhandler_invocation \<Rightarrow> irqhandler_invocation"
where
  "modePolarity_update f (SetMode v0 v1 v2) = SetMode v0 v1 (f v2)"

primrec
  setIRQHandlerSlot_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> irqhandler_invocation \<Rightarrow> irqhandler_invocation"
where
  "setIRQHandlerSlot_update f (SetIRQHandler v0 v1 v2) = SetIRQHandler v0 v1 (f v2)"

abbreviation (input)
  AckIRQ_trans :: "(irq) \<Rightarrow> irqhandler_invocation" ("AckIRQ'_ \<lparr> irqHandlerIRQ= _ \<rparr>")
where
  "AckIRQ_ \<lparr> irqHandlerIRQ= v0 \<rparr> == AckIRQ v0"

abbreviation (input)
  ClearIRQHandler_trans :: "(irq) \<Rightarrow> irqhandler_invocation" ("ClearIRQHandler'_ \<lparr> irqHandlerIRQ= _ \<rparr>")
where
  "ClearIRQHandler_ \<lparr> irqHandlerIRQ= v0 \<rparr> == ClearIRQHandler v0"

abbreviation (input)
  SetMode_trans :: "(irq) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> irqhandler_invocation" ("SetMode'_ \<lparr> modeIRQ= _, modeTrigger= _, modePolarity= _ \<rparr>")
where
  "SetMode_ \<lparr> modeIRQ= v0, modeTrigger= v1, modePolarity= v2 \<rparr> == SetMode v0 v1 v2"

abbreviation (input)
  SetIRQHandler_trans :: "(irq) \<Rightarrow> (capability) \<Rightarrow> (machine_word) \<Rightarrow> irqhandler_invocation" ("SetIRQHandler'_ \<lparr> irqHandlerIRQ= _, setIRQHandlerCap= _, setIRQHandlerSlot= _ \<rparr>")
where
  "SetIRQHandler_ \<lparr> irqHandlerIRQ= v0, setIRQHandlerCap= v1, setIRQHandlerSlot= v2 \<rparr> == SetIRQHandler v0 v1 v2"

definition
  isAckIRQ :: "irqhandler_invocation \<Rightarrow> bool"
where
 "isAckIRQ v \<equiv> case v of
    AckIRQ v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isClearIRQHandler :: "irqhandler_invocation \<Rightarrow> bool"
where
 "isClearIRQHandler v \<equiv> case v of
    ClearIRQHandler v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSetMode :: "irqhandler_invocation \<Rightarrow> bool"
where
 "isSetMode v \<equiv> case v of
    SetMode v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSetIRQHandler :: "irqhandler_invocation \<Rightarrow> bool"
where
 "isSetIRQHandler v \<equiv> case v of
    SetIRQHandler v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype invocation =
    InvokeUntyped untyped_invocation
  | InvokeEndpoint machine_word machine_word bool
  | InvokeNotification machine_word machine_word
  | InvokeReply machine_word machine_word
  | InvokeDomain machine_word domain
  | InvokeTCB tcbinvocation
  | InvokeCNode cnode_invocation
  | InvokeIRQControl irqcontrol_invocation
  | InvokeIRQHandler irqhandler_invocation
  | InvokeArchObject ArchRetypeDecls_H.invocation

definition
invocationType :: "machine_word \<Rightarrow> invocation_label"
where
"invocationType x \<equiv>
    let
     x' = fromIntegral x
    in
    if
    x' \<le> fromEnum (maxBound ::invocation_label) then toEnum x'
    else if
    True      then InvalidInvocation
    else undefined"


end
