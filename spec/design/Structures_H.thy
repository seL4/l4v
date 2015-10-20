(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
   datatypes/records for the various kernel data structures.
*)

chapter "Kernel Data Structures"

theory Structures_H
imports
  Config_H
  State_H
  Fault_H
  Types_H
  ARMStructures_H
begin

datatype zombie_type =
    ZombieTCB
  | ZombieCNode nat

primrec
  zombieCTEBits :: "zombie_type \<Rightarrow> nat"
where
  "zombieCTEBits (ZombieCNode v0) = v0"

primrec
  zombieCTEBits_update :: "(nat \<Rightarrow> nat) \<Rightarrow> zombie_type \<Rightarrow> zombie_type"
where
  "zombieCTEBits_update f (ZombieCNode v0) = ZombieCNode (f v0)"

abbreviation (input)
  ZombieCNode_trans :: "(nat) \<Rightarrow> zombie_type" ("ZombieCNode'_ \<lparr> zombieCTEBits= _ \<rparr>")
where
  "ZombieCNode_ \<lparr> zombieCTEBits= v0 \<rparr> == ZombieCNode v0"

definition
  isZombieTCB :: "zombie_type \<Rightarrow> bool"
where
 "isZombieTCB v \<equiv> case v of
    ZombieTCB \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isZombieCNode :: "zombie_type \<Rightarrow> bool"
where
 "isZombieCNode v \<equiv> case v of
    ZombieCNode v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype capability =
    ThreadCap machine_word
  | NullCap
  | AsyncEndpointCap machine_word machine_word bool bool
  | IRQHandlerCap irq
  | EndpointCap machine_word machine_word bool bool bool
  | DomainCap
  | Zombie machine_word zombie_type nat
  | ArchObjectCap arch_capability
  | ReplyCap machine_word bool
  | UntypedCap machine_word nat nat
  | CNodeCap machine_word nat machine_word nat
  | IRQControlCap

primrec
  capCap :: "capability \<Rightarrow> arch_capability"
where
  "capCap (ArchObjectCap v0) = v0"

primrec
  capCNodeBits :: "capability \<Rightarrow> nat"
where
  "capCNodeBits (CNodeCap v0 v1 v2 v3) = v1"

primrec
  capPtr :: "capability \<Rightarrow> machine_word"
where
  "capPtr (UntypedCap v0 v1 v2) = v0"

primrec
  capZombieNumber :: "capability \<Rightarrow> nat"
where
  "capZombieNumber (Zombie v0 v1 v2) = v2"

primrec
  capCNodePtr :: "capability \<Rightarrow> machine_word"
where
  "capCNodePtr (CNodeCap v0 v1 v2 v3) = v0"

primrec
  capReplyMaster :: "capability \<Rightarrow> bool"
where
  "capReplyMaster (ReplyCap v0 v1) = v1"

primrec
  capFreeIndex :: "capability \<Rightarrow> nat"
where
  "capFreeIndex (UntypedCap v0 v1 v2) = v2"

primrec
  capAEPCanReceive :: "capability \<Rightarrow> bool"
where
  "capAEPCanReceive (AsyncEndpointCap v0 v1 v2 v3) = v3"

primrec
  capBlockSize :: "capability \<Rightarrow> nat"
where
  "capBlockSize (UntypedCap v0 v1 v2) = v1"

primrec
  capEPCanReceive :: "capability \<Rightarrow> bool"
where
  "capEPCanReceive (EndpointCap v0 v1 v2 v3 v4) = v3"

primrec
  capEPPtr :: "capability \<Rightarrow> machine_word"
where
  "capEPPtr (EndpointCap v0 v1 v2 v3 v4) = v0"

primrec
  capEPBadge :: "capability \<Rightarrow> machine_word"
where
  "capEPBadge (EndpointCap v0 v1 v2 v3 v4) = v1"

primrec
  capAEPCanSend :: "capability \<Rightarrow> bool"
where
  "capAEPCanSend (AsyncEndpointCap v0 v1 v2 v3) = v2"

primrec
  capZombiePtr :: "capability \<Rightarrow> machine_word"
where
  "capZombiePtr (Zombie v0 v1 v2) = v0"

primrec
  capIRQ :: "capability \<Rightarrow> irq"
where
  "capIRQ (IRQHandlerCap v0) = v0"

primrec
  capCNodeGuardSize :: "capability \<Rightarrow> nat"
where
  "capCNodeGuardSize (CNodeCap v0 v1 v2 v3) = v3"

primrec
  capTCBPtr :: "capability \<Rightarrow> machine_word"
where
  "capTCBPtr (ThreadCap v0) = v0"
| "capTCBPtr (ReplyCap v0 v1) = v0"

primrec
  capAEPBadge :: "capability \<Rightarrow> machine_word"
where
  "capAEPBadge (AsyncEndpointCap v0 v1 v2 v3) = v1"

primrec
  capEPCanGrant :: "capability \<Rightarrow> bool"
where
  "capEPCanGrant (EndpointCap v0 v1 v2 v3 v4) = v4"

primrec
  capEPCanSend :: "capability \<Rightarrow> bool"
where
  "capEPCanSend (EndpointCap v0 v1 v2 v3 v4) = v2"

primrec
  capCNodeGuard :: "capability \<Rightarrow> machine_word"
where
  "capCNodeGuard (CNodeCap v0 v1 v2 v3) = v2"

primrec
  capAEPPtr :: "capability \<Rightarrow> machine_word"
where
  "capAEPPtr (AsyncEndpointCap v0 v1 v2 v3) = v0"

primrec
  capZombieType :: "capability \<Rightarrow> zombie_type"
where
  "capZombieType (Zombie v0 v1 v2) = v1"

primrec
  capCap_update :: "(arch_capability \<Rightarrow> arch_capability) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capCap_update f (ArchObjectCap v0) = ArchObjectCap (f v0)"

primrec
  capCNodeBits_update :: "(nat \<Rightarrow> nat) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capCNodeBits_update f (CNodeCap v0 v1 v2 v3) = CNodeCap v0 (f v1) v2 v3"

primrec
  capPtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capPtr_update f (UntypedCap v0 v1 v2) = UntypedCap (f v0) v1 v2"

primrec
  capZombieNumber_update :: "(nat \<Rightarrow> nat) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capZombieNumber_update f (Zombie v0 v1 v2) = Zombie v0 v1 (f v2)"

primrec
  capCNodePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capCNodePtr_update f (CNodeCap v0 v1 v2 v3) = CNodeCap (f v0) v1 v2 v3"

primrec
  capReplyMaster_update :: "(bool \<Rightarrow> bool) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capReplyMaster_update f (ReplyCap v0 v1) = ReplyCap v0 (f v1)"

primrec
  capFreeIndex_update :: "(nat \<Rightarrow> nat) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capFreeIndex_update f (UntypedCap v0 v1 v2) = UntypedCap v0 v1 (f v2)"

primrec
  capAEPCanReceive_update :: "(bool \<Rightarrow> bool) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capAEPCanReceive_update f (AsyncEndpointCap v0 v1 v2 v3) = AsyncEndpointCap v0 v1 v2 (f v3)"

primrec
  capBlockSize_update :: "(nat \<Rightarrow> nat) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capBlockSize_update f (UntypedCap v0 v1 v2) = UntypedCap v0 (f v1) v2"

primrec
  capEPCanReceive_update :: "(bool \<Rightarrow> bool) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capEPCanReceive_update f (EndpointCap v0 v1 v2 v3 v4) = EndpointCap v0 v1 v2 (f v3) v4"

primrec
  capEPPtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capEPPtr_update f (EndpointCap v0 v1 v2 v3 v4) = EndpointCap (f v0) v1 v2 v3 v4"

primrec
  capEPBadge_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capEPBadge_update f (EndpointCap v0 v1 v2 v3 v4) = EndpointCap v0 (f v1) v2 v3 v4"

primrec
  capAEPCanSend_update :: "(bool \<Rightarrow> bool) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capAEPCanSend_update f (AsyncEndpointCap v0 v1 v2 v3) = AsyncEndpointCap v0 v1 (f v2) v3"

primrec
  capZombiePtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capZombiePtr_update f (Zombie v0 v1 v2) = Zombie (f v0) v1 v2"

primrec
  capIRQ_update :: "(irq \<Rightarrow> irq) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capIRQ_update f (IRQHandlerCap v0) = IRQHandlerCap (f v0)"

primrec
  capCNodeGuardSize_update :: "(nat \<Rightarrow> nat) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capCNodeGuardSize_update f (CNodeCap v0 v1 v2 v3) = CNodeCap v0 v1 v2 (f v3)"

primrec
  capTCBPtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capTCBPtr_update f (ThreadCap v0) = ThreadCap (f v0)"
| "capTCBPtr_update f (ReplyCap v0 v1) = ReplyCap (f v0) v1"

primrec
  capAEPBadge_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capAEPBadge_update f (AsyncEndpointCap v0 v1 v2 v3) = AsyncEndpointCap v0 (f v1) v2 v3"

primrec
  capEPCanGrant_update :: "(bool \<Rightarrow> bool) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capEPCanGrant_update f (EndpointCap v0 v1 v2 v3 v4) = EndpointCap v0 v1 v2 v3 (f v4)"

primrec
  capEPCanSend_update :: "(bool \<Rightarrow> bool) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capEPCanSend_update f (EndpointCap v0 v1 v2 v3 v4) = EndpointCap v0 v1 (f v2) v3 v4"

primrec
  capCNodeGuard_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capCNodeGuard_update f (CNodeCap v0 v1 v2 v3) = CNodeCap v0 v1 (f v2) v3"

primrec
  capAEPPtr_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capAEPPtr_update f (AsyncEndpointCap v0 v1 v2 v3) = AsyncEndpointCap (f v0) v1 v2 v3"

primrec
  capZombieType_update :: "(zombie_type \<Rightarrow> zombie_type) \<Rightarrow> capability \<Rightarrow> capability"
where
  "capZombieType_update f (Zombie v0 v1 v2) = Zombie v0 (f v1) v2"

abbreviation (input)
  ThreadCap_trans :: "(machine_word) \<Rightarrow> capability" ("ThreadCap'_ \<lparr> capTCBPtr= _ \<rparr>")
where
  "ThreadCap_ \<lparr> capTCBPtr= v0 \<rparr> == ThreadCap v0"

abbreviation (input)
  AsyncEndpointCap_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> capability" ("AsyncEndpointCap'_ \<lparr> capAEPPtr= _, capAEPBadge= _, capAEPCanSend= _, capAEPCanReceive= _ \<rparr>")
where
  "AsyncEndpointCap_ \<lparr> capAEPPtr= v0, capAEPBadge= v1, capAEPCanSend= v2, capAEPCanReceive= v3 \<rparr> == AsyncEndpointCap v0 v1 v2 v3"

abbreviation (input)
  IRQHandlerCap_trans :: "(irq) \<Rightarrow> capability" ("IRQHandlerCap'_ \<lparr> capIRQ= _ \<rparr>")
where
  "IRQHandlerCap_ \<lparr> capIRQ= v0 \<rparr> == IRQHandlerCap v0"

abbreviation (input)
  EndpointCap_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> capability" ("EndpointCap'_ \<lparr> capEPPtr= _, capEPBadge= _, capEPCanSend= _, capEPCanReceive= _, capEPCanGrant= _ \<rparr>")
where
  "EndpointCap_ \<lparr> capEPPtr= v0, capEPBadge= v1, capEPCanSend= v2, capEPCanReceive= v3, capEPCanGrant= v4 \<rparr> == EndpointCap v0 v1 v2 v3 v4"

abbreviation (input)
  Zombie_trans :: "(machine_word) \<Rightarrow> (zombie_type) \<Rightarrow> (nat) \<Rightarrow> capability" ("Zombie'_ \<lparr> capZombiePtr= _, capZombieType= _, capZombieNumber= _ \<rparr>")
where
  "Zombie_ \<lparr> capZombiePtr= v0, capZombieType= v1, capZombieNumber= v2 \<rparr> == Zombie v0 v1 v2"

abbreviation (input)
  ArchObjectCap_trans :: "(arch_capability) \<Rightarrow> capability" ("ArchObjectCap'_ \<lparr> capCap= _ \<rparr>")
where
  "ArchObjectCap_ \<lparr> capCap= v0 \<rparr> == ArchObjectCap v0"

abbreviation (input)
  ReplyCap_trans :: "(machine_word) \<Rightarrow> (bool) \<Rightarrow> capability" ("ReplyCap'_ \<lparr> capTCBPtr= _, capReplyMaster= _ \<rparr>")
where
  "ReplyCap_ \<lparr> capTCBPtr= v0, capReplyMaster= v1 \<rparr> == ReplyCap v0 v1"

abbreviation (input)
  UntypedCap_trans :: "(machine_word) \<Rightarrow> (nat) \<Rightarrow> (nat) \<Rightarrow> capability" ("UntypedCap'_ \<lparr> capPtr= _, capBlockSize= _, capFreeIndex= _ \<rparr>")
where
  "UntypedCap_ \<lparr> capPtr= v0, capBlockSize= v1, capFreeIndex= v2 \<rparr> == UntypedCap v0 v1 v2"

abbreviation (input)
  CNodeCap_trans :: "(machine_word) \<Rightarrow> (nat) \<Rightarrow> (machine_word) \<Rightarrow> (nat) \<Rightarrow> capability" ("CNodeCap'_ \<lparr> capCNodePtr= _, capCNodeBits= _, capCNodeGuard= _, capCNodeGuardSize= _ \<rparr>")
where
  "CNodeCap_ \<lparr> capCNodePtr= v0, capCNodeBits= v1, capCNodeGuard= v2, capCNodeGuardSize= v3 \<rparr> == CNodeCap v0 v1 v2 v3"

definition
  isThreadCap :: "capability \<Rightarrow> bool"
where
 "isThreadCap v \<equiv> case v of
    ThreadCap v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isNullCap :: "capability \<Rightarrow> bool"
where
 "isNullCap v \<equiv> case v of
    NullCap \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isAsyncEndpointCap :: "capability \<Rightarrow> bool"
where
 "isAsyncEndpointCap v \<equiv> case v of
    AsyncEndpointCap v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIRQHandlerCap :: "capability \<Rightarrow> bool"
where
 "isIRQHandlerCap v \<equiv> case v of
    IRQHandlerCap v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isEndpointCap :: "capability \<Rightarrow> bool"
where
 "isEndpointCap v \<equiv> case v of
    EndpointCap v0 v1 v2 v3 v4 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isDomainCap :: "capability \<Rightarrow> bool"
where
 "isDomainCap v \<equiv> case v of
    DomainCap \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isZombie :: "capability \<Rightarrow> bool"
where
 "isZombie v \<equiv> case v of
    Zombie v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isArchObjectCap :: "capability \<Rightarrow> bool"
where
 "isArchObjectCap v \<equiv> case v of
    ArchObjectCap v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isReplyCap :: "capability \<Rightarrow> bool"
where
 "isReplyCap v \<equiv> case v of
    ReplyCap v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isUntypedCap :: "capability \<Rightarrow> bool"
where
 "isUntypedCap v \<equiv> case v of
    UntypedCap v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isCNodeCap :: "capability \<Rightarrow> bool"
where
 "isCNodeCap v \<equiv> case v of
    CNodeCap v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIRQControlCap :: "capability \<Rightarrow> bool"
where
 "isIRQControlCap v \<equiv> case v of
    IRQControlCap \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype endpoint =
    RecvEP "machine_word list"
  | IdleEP
  | SendEP "machine_word list"

primrec
  epQueue :: "endpoint \<Rightarrow> machine_word list"
where
  "epQueue (RecvEP v0) = v0"
| "epQueue (SendEP v0) = v0"

primrec
  epQueue_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> endpoint \<Rightarrow> endpoint"
where
  "epQueue_update f (RecvEP v0) = RecvEP (f v0)"
| "epQueue_update f (SendEP v0) = SendEP (f v0)"

abbreviation (input)
  RecvEP_trans :: "(machine_word list) \<Rightarrow> endpoint" ("RecvEP'_ \<lparr> epQueue= _ \<rparr>")
where
  "RecvEP_ \<lparr> epQueue= v0 \<rparr> == RecvEP v0"

abbreviation (input)
  SendEP_trans :: "(machine_word list) \<Rightarrow> endpoint" ("SendEP'_ \<lparr> epQueue= _ \<rparr>")
where
  "SendEP_ \<lparr> epQueue= v0 \<rparr> == SendEP v0"

definition
  isRecvEP :: "endpoint \<Rightarrow> bool"
where
 "isRecvEP v \<equiv> case v of
    RecvEP v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIdleEP :: "endpoint \<Rightarrow> bool"
where
 "isIdleEP v \<equiv> case v of
    IdleEP \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isSendEP :: "endpoint \<Rightarrow> bool"
where
 "isSendEP v \<equiv> case v of
    SendEP v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype aep =
    IdleAEP
  | ActiveAEP machine_word
  | WaitingAEP "machine_word list"

primrec
  aepMsgIdentifier :: "aep \<Rightarrow> machine_word"
where
  "aepMsgIdentifier (ActiveAEP v0) = v0"

primrec
  aepQueue :: "aep \<Rightarrow> machine_word list"
where
  "aepQueue (WaitingAEP v0) = v0"

primrec
  aepMsgIdentifier_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> aep \<Rightarrow> aep"
where
  "aepMsgIdentifier_update f (ActiveAEP v0) = ActiveAEP (f v0)"

primrec
  aepQueue_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> aep \<Rightarrow> aep"
where
  "aepQueue_update f (WaitingAEP v0) = WaitingAEP (f v0)"

abbreviation (input)
  ActiveAEP_trans :: "(machine_word) \<Rightarrow> aep" ("ActiveAEP'_ \<lparr> aepMsgIdentifier= _ \<rparr>")
where
  "ActiveAEP_ \<lparr> aepMsgIdentifier= v0 \<rparr> == ActiveAEP v0"

abbreviation (input)
  WaitingAEP_trans :: "(machine_word list) \<Rightarrow> aep" ("WaitingAEP'_ \<lparr> aepQueue= _ \<rparr>")
where
  "WaitingAEP_ \<lparr> aepQueue= v0 \<rparr> == WaitingAEP v0"

definition
  isIdleAEP :: "aep \<Rightarrow> bool"
where
 "isIdleAEP v \<equiv> case v of
    IdleAEP \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isActiveAEP :: "aep \<Rightarrow> bool"
where
 "isActiveAEP v \<equiv> case v of
    ActiveAEP v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isWaitingAEP :: "aep \<Rightarrow> bool"
where
 "isWaitingAEP v \<equiv> case v of
    WaitingAEP v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype async_endpoint =
    AEP aep "(machine_word) option"

primrec
  aepBoundTCB :: "async_endpoint \<Rightarrow> (machine_word) option"
where
  "aepBoundTCB (AEP v0 v1) = v1"

primrec
  aepObj :: "async_endpoint \<Rightarrow> aep"
where
  "aepObj (AEP v0 v1) = v0"

primrec
  aepBoundTCB_update :: "(((machine_word) option) \<Rightarrow> ((machine_word) option)) \<Rightarrow> async_endpoint \<Rightarrow> async_endpoint"
where
  "aepBoundTCB_update f (AEP v0 v1) = AEP v0 (f v1)"

primrec
  aepObj_update :: "(aep \<Rightarrow> aep) \<Rightarrow> async_endpoint \<Rightarrow> async_endpoint"
where
  "aepObj_update f (AEP v0 v1) = AEP (f v0) v1"

abbreviation (input)
  AEP_trans :: "(aep) \<Rightarrow> ((machine_word) option) \<Rightarrow> async_endpoint" ("AEP'_ \<lparr> aepObj= _, aepBoundTCB= _ \<rparr>")
where
  "AEP_ \<lparr> aepObj= v0, aepBoundTCB= v1 \<rparr> == AEP v0 v1"

lemma aepBoundTCB_aepBoundTCB_update [simp]:
  "aepBoundTCB (aepBoundTCB_update f v) = f (aepBoundTCB v)"
  by (cases v) simp

lemma aepBoundTCB_aepObj_update [simp]:
  "aepBoundTCB (aepObj_update f v) = aepBoundTCB v"
  by (cases v) simp

lemma aepObj_aepBoundTCB_update [simp]:
  "aepObj (aepBoundTCB_update f v) = aepObj v"
  by (cases v) simp

lemma aepObj_aepObj_update [simp]:
  "aepObj (aepObj_update f v) = f (aepObj v)"
  by (cases v) simp

datatype mdbnode =
    MDB machine_word machine_word bool bool

primrec
  mdbPrev :: "mdbnode \<Rightarrow> machine_word"
where
  "mdbPrev (MDB v0 v1 v2 v3) = v1"

primrec
  mdbFirstBadged :: "mdbnode \<Rightarrow> bool"
where
  "mdbFirstBadged (MDB v0 v1 v2 v3) = v3"

primrec
  mdbNext :: "mdbnode \<Rightarrow> machine_word"
where
  "mdbNext (MDB v0 v1 v2 v3) = v0"

primrec
  mdbRevocable :: "mdbnode \<Rightarrow> bool"
where
  "mdbRevocable (MDB v0 v1 v2 v3) = v2"

primrec
  mdbPrev_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> mdbnode \<Rightarrow> mdbnode"
where
  "mdbPrev_update f (MDB v0 v1 v2 v3) = MDB v0 (f v1) v2 v3"

primrec
  mdbFirstBadged_update :: "(bool \<Rightarrow> bool) \<Rightarrow> mdbnode \<Rightarrow> mdbnode"
where
  "mdbFirstBadged_update f (MDB v0 v1 v2 v3) = MDB v0 v1 v2 (f v3)"

primrec
  mdbNext_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> mdbnode \<Rightarrow> mdbnode"
where
  "mdbNext_update f (MDB v0 v1 v2 v3) = MDB (f v0) v1 v2 v3"

primrec
  mdbRevocable_update :: "(bool \<Rightarrow> bool) \<Rightarrow> mdbnode \<Rightarrow> mdbnode"
where
  "mdbRevocable_update f (MDB v0 v1 v2 v3) = MDB v0 v1 (f v2) v3"

abbreviation (input)
  MDB_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> mdbnode" ("MDB'_ \<lparr> mdbNext= _, mdbPrev= _, mdbRevocable= _, mdbFirstBadged= _ \<rparr>")
where
  "MDB_ \<lparr> mdbNext= v0, mdbPrev= v1, mdbRevocable= v2, mdbFirstBadged= v3 \<rparr> == MDB v0 v1 v2 v3"

lemma mdbPrev_mdbPrev_update [simp]:
  "mdbPrev (mdbPrev_update f v) = f (mdbPrev v)"
  by (cases v) simp

lemma mdbPrev_mdbFirstBadged_update [simp]:
  "mdbPrev (mdbFirstBadged_update f v) = mdbPrev v"
  by (cases v) simp

lemma mdbPrev_mdbNext_update [simp]:
  "mdbPrev (mdbNext_update f v) = mdbPrev v"
  by (cases v) simp

lemma mdbPrev_mdbRevocable_update [simp]:
  "mdbPrev (mdbRevocable_update f v) = mdbPrev v"
  by (cases v) simp

lemma mdbFirstBadged_mdbPrev_update [simp]:
  "mdbFirstBadged (mdbPrev_update f v) = mdbFirstBadged v"
  by (cases v) simp

lemma mdbFirstBadged_mdbFirstBadged_update [simp]:
  "mdbFirstBadged (mdbFirstBadged_update f v) = f (mdbFirstBadged v)"
  by (cases v) simp

lemma mdbFirstBadged_mdbNext_update [simp]:
  "mdbFirstBadged (mdbNext_update f v) = mdbFirstBadged v"
  by (cases v) simp

lemma mdbFirstBadged_mdbRevocable_update [simp]:
  "mdbFirstBadged (mdbRevocable_update f v) = mdbFirstBadged v"
  by (cases v) simp

lemma mdbNext_mdbPrev_update [simp]:
  "mdbNext (mdbPrev_update f v) = mdbNext v"
  by (cases v) simp

lemma mdbNext_mdbFirstBadged_update [simp]:
  "mdbNext (mdbFirstBadged_update f v) = mdbNext v"
  by (cases v) simp

lemma mdbNext_mdbNext_update [simp]:
  "mdbNext (mdbNext_update f v) = f (mdbNext v)"
  by (cases v) simp

lemma mdbNext_mdbRevocable_update [simp]:
  "mdbNext (mdbRevocable_update f v) = mdbNext v"
  by (cases v) simp

lemma mdbRevocable_mdbPrev_update [simp]:
  "mdbRevocable (mdbPrev_update f v) = mdbRevocable v"
  by (cases v) simp

lemma mdbRevocable_mdbFirstBadged_update [simp]:
  "mdbRevocable (mdbFirstBadged_update f v) = mdbRevocable v"
  by (cases v) simp

lemma mdbRevocable_mdbNext_update [simp]:
  "mdbRevocable (mdbNext_update f v) = mdbRevocable v"
  by (cases v) simp

lemma mdbRevocable_mdbRevocable_update [simp]:
  "mdbRevocable (mdbRevocable_update f v) = f (mdbRevocable v)"
  by (cases v) simp

datatype cte =
    CTE capability mdbnode

primrec
  cteCap :: "cte \<Rightarrow> capability"
where
  "cteCap (CTE v0 v1) = v0"

primrec
  cteMDBNode :: "cte \<Rightarrow> mdbnode"
where
  "cteMDBNode (CTE v0 v1) = v1"

primrec
  cteCap_update :: "(capability \<Rightarrow> capability) \<Rightarrow> cte \<Rightarrow> cte"
where
  "cteCap_update f (CTE v0 v1) = CTE (f v0) v1"

primrec
  cteMDBNode_update :: "(mdbnode \<Rightarrow> mdbnode) \<Rightarrow> cte \<Rightarrow> cte"
where
  "cteMDBNode_update f (CTE v0 v1) = CTE v0 (f v1)"

abbreviation (input)
  CTE_trans :: "(capability) \<Rightarrow> (mdbnode) \<Rightarrow> cte" ("CTE'_ \<lparr> cteCap= _, cteMDBNode= _ \<rparr>")
where
  "CTE_ \<lparr> cteCap= v0, cteMDBNode= v1 \<rparr> == CTE v0 v1"

lemma cteCap_cteCap_update [simp]:
  "cteCap (cteCap_update f v) = f (cteCap v)"
  by (cases v) simp

lemma cteCap_cteMDBNode_update [simp]:
  "cteCap (cteMDBNode_update f v) = cteCap v"
  by (cases v) simp

lemma cteMDBNode_cteCap_update [simp]:
  "cteMDBNode (cteCap_update f v) = cteMDBNode v"
  by (cases v) simp

lemma cteMDBNode_cteMDBNode_update [simp]:
  "cteMDBNode (cteMDBNode_update f v) = f (cteMDBNode v)"
  by (cases v) simp

datatype thread_state =
    BlockedOnReceive machine_word bool
  | BlockedOnReply
  | BlockedOnAsyncEvent machine_word
  | Running
  | Inactive
  | IdleThreadState
  | BlockedOnSend machine_word machine_word bool bool
  | Restart

primrec
  blockingIPCIsCall :: "thread_state \<Rightarrow> bool"
where
  "blockingIPCIsCall (BlockedOnSend v0 v1 v2 v3) = v3"

primrec
  waitingOnAsyncEP :: "thread_state \<Rightarrow> machine_word"
where
  "waitingOnAsyncEP (BlockedOnAsyncEvent v0) = v0"

primrec
  blockingIPCBadge :: "thread_state \<Rightarrow> machine_word"
where
  "blockingIPCBadge (BlockedOnSend v0 v1 v2 v3) = v1"

primrec
  blockingIPCEndpoint :: "thread_state \<Rightarrow> machine_word"
where
  "blockingIPCEndpoint (BlockedOnReceive v0 v1) = v0"
| "blockingIPCEndpoint (BlockedOnSend v0 v1 v2 v3) = v0"

primrec
  blockingIPCDiminishCaps :: "thread_state \<Rightarrow> bool"
where
  "blockingIPCDiminishCaps (BlockedOnReceive v0 v1) = v1"

primrec
  blockingIPCCanGrant :: "thread_state \<Rightarrow> bool"
where
  "blockingIPCCanGrant (BlockedOnSend v0 v1 v2 v3) = v2"

primrec
  blockingIPCIsCall_update :: "(bool \<Rightarrow> bool) \<Rightarrow> thread_state \<Rightarrow> thread_state"
where
  "blockingIPCIsCall_update f (BlockedOnSend v0 v1 v2 v3) = BlockedOnSend v0 v1 v2 (f v3)"

primrec
  waitingOnAsyncEP_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> thread_state \<Rightarrow> thread_state"
where
  "waitingOnAsyncEP_update f (BlockedOnAsyncEvent v0) = BlockedOnAsyncEvent (f v0)"

primrec
  blockingIPCBadge_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> thread_state \<Rightarrow> thread_state"
where
  "blockingIPCBadge_update f (BlockedOnSend v0 v1 v2 v3) = BlockedOnSend v0 (f v1) v2 v3"

primrec
  blockingIPCEndpoint_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> thread_state \<Rightarrow> thread_state"
where
  "blockingIPCEndpoint_update f (BlockedOnReceive v0 v1) = BlockedOnReceive (f v0) v1"
| "blockingIPCEndpoint_update f (BlockedOnSend v0 v1 v2 v3) = BlockedOnSend (f v0) v1 v2 v3"

primrec
  blockingIPCDiminishCaps_update :: "(bool \<Rightarrow> bool) \<Rightarrow> thread_state \<Rightarrow> thread_state"
where
  "blockingIPCDiminishCaps_update f (BlockedOnReceive v0 v1) = BlockedOnReceive v0 (f v1)"

primrec
  blockingIPCCanGrant_update :: "(bool \<Rightarrow> bool) \<Rightarrow> thread_state \<Rightarrow> thread_state"
where
  "blockingIPCCanGrant_update f (BlockedOnSend v0 v1 v2 v3) = BlockedOnSend v0 v1 (f v2) v3"

abbreviation (input)
  BlockedOnReceive_trans :: "(machine_word) \<Rightarrow> (bool) \<Rightarrow> thread_state" ("BlockedOnReceive'_ \<lparr> blockingIPCEndpoint= _, blockingIPCDiminishCaps= _ \<rparr>")
where
  "BlockedOnReceive_ \<lparr> blockingIPCEndpoint= v0, blockingIPCDiminishCaps= v1 \<rparr> == BlockedOnReceive v0 v1"

abbreviation (input)
  BlockedOnAsyncEvent_trans :: "(machine_word) \<Rightarrow> thread_state" ("BlockedOnAsyncEvent'_ \<lparr> waitingOnAsyncEP= _ \<rparr>")
where
  "BlockedOnAsyncEvent_ \<lparr> waitingOnAsyncEP= v0 \<rparr> == BlockedOnAsyncEvent v0"

abbreviation (input)
  BlockedOnSend_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> (bool) \<Rightarrow> (bool) \<Rightarrow> thread_state" ("BlockedOnSend'_ \<lparr> blockingIPCEndpoint= _, blockingIPCBadge= _, blockingIPCCanGrant= _, blockingIPCIsCall= _ \<rparr>")
where
  "BlockedOnSend_ \<lparr> blockingIPCEndpoint= v0, blockingIPCBadge= v1, blockingIPCCanGrant= v2, blockingIPCIsCall= v3 \<rparr> == BlockedOnSend v0 v1 v2 v3"

definition
  isBlockedOnReceive :: "thread_state \<Rightarrow> bool"
where
 "isBlockedOnReceive v \<equiv> case v of
    BlockedOnReceive v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isBlockedOnReply :: "thread_state \<Rightarrow> bool"
where
 "isBlockedOnReply v \<equiv> case v of
    BlockedOnReply \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isBlockedOnAsyncEvent :: "thread_state \<Rightarrow> bool"
where
 "isBlockedOnAsyncEvent v \<equiv> case v of
    BlockedOnAsyncEvent v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isRunning :: "thread_state \<Rightarrow> bool"
where
 "isRunning v \<equiv> case v of
    Running \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isInactive :: "thread_state \<Rightarrow> bool"
where
 "isInactive v \<equiv> case v of
    Inactive \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isIdleThreadState :: "thread_state \<Rightarrow> bool"
where
 "isIdleThreadState v \<equiv> case v of
    IdleThreadState \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isBlockedOnSend :: "thread_state \<Rightarrow> bool"
where
 "isBlockedOnSend v \<equiv> case v of
    BlockedOnSend v0 v1 v2 v3 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isRestart :: "thread_state \<Rightarrow> bool"
where
 "isRestart v \<equiv> case v of
    Restart \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype tcb =
    Thread cte cte cte cte cte domain thread_state priority bool "fault option" nat cptr vptr "(machine_word) option" user_context

primrec
  tcbVTable :: "tcb \<Rightarrow> cte"
where
  "tcbVTable (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v1"

primrec
  tcbIPCBufferFrame :: "tcb \<Rightarrow> cte"
where
  "tcbIPCBufferFrame (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v4"

primrec
  tcbState :: "tcb \<Rightarrow> thread_state"
where
  "tcbState (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v6"

primrec
  tcbCTable :: "tcb \<Rightarrow> cte"
where
  "tcbCTable (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v0"

primrec
  tcbFaultHandler :: "tcb \<Rightarrow> cptr"
where
  "tcbFaultHandler (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v11"

primrec
  tcbIPCBuffer :: "tcb \<Rightarrow> vptr"
where
  "tcbIPCBuffer (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v12"

primrec
  tcbContext :: "tcb \<Rightarrow> user_context"
where
  "tcbContext (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v14"

primrec
  tcbCaller :: "tcb \<Rightarrow> cte"
where
  "tcbCaller (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v3"

primrec
  tcbBoundAEP :: "tcb \<Rightarrow> (machine_word) option"
where
  "tcbBoundAEP (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v13"

primrec
  tcbDomain :: "tcb \<Rightarrow> domain"
where
  "tcbDomain (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v5"

primrec
  tcbReply :: "tcb \<Rightarrow> cte"
where
  "tcbReply (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v2"

primrec
  tcbQueued :: "tcb \<Rightarrow> bool"
where
  "tcbQueued (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v8"

primrec
  tcbPriority :: "tcb \<Rightarrow> priority"
where
  "tcbPriority (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v7"

primrec
  tcbFault :: "tcb \<Rightarrow> fault option"
where
  "tcbFault (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v9"

primrec
  tcbTimeSlice :: "tcb \<Rightarrow> nat"
where
  "tcbTimeSlice (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = v10"

primrec
  tcbVTable_update :: "(cte \<Rightarrow> cte) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbVTable_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 (f v1) v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbIPCBufferFrame_update :: "(cte \<Rightarrow> cte) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbIPCBufferFrame_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 (f v4) v5 v6 v7 v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbState_update :: "(thread_state \<Rightarrow> thread_state) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbState_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 (f v6) v7 v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbCTable_update :: "(cte \<Rightarrow> cte) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbCTable_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread (f v0) v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbFaultHandler_update :: "(cptr \<Rightarrow> cptr) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbFaultHandler_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 (f v11) v12 v13 v14"

primrec
  tcbIPCBuffer_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbIPCBuffer_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 (f v12) v13 v14"

primrec
  tcbContext_update :: "(user_context \<Rightarrow> user_context) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbContext_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 (f v14)"

primrec
  tcbCaller_update :: "(cte \<Rightarrow> cte) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbCaller_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 (f v3) v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbBoundAEP_update :: "(((machine_word) option) \<Rightarrow> ((machine_word) option)) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbBoundAEP_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 (f v13) v14"

primrec
  tcbDomain_update :: "(domain \<Rightarrow> domain) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbDomain_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 (f v5) v6 v7 v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbReply_update :: "(cte \<Rightarrow> cte) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbReply_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 (f v2) v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbQueued_update :: "(bool \<Rightarrow> bool) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbQueued_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 v7 (f v8) v9 v10 v11 v12 v13 v14"

primrec
  tcbPriority_update :: "(priority \<Rightarrow> priority) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbPriority_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 (f v7) v8 v9 v10 v11 v12 v13 v14"

primrec
  tcbFault_update :: "((fault option) \<Rightarrow> (fault option)) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbFault_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 (f v9) v10 v11 v12 v13 v14"

primrec
  tcbTimeSlice_update :: "(nat \<Rightarrow> nat) \<Rightarrow> tcb \<Rightarrow> tcb"
where
  "tcbTimeSlice_update f (Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14) = Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 (f v10) v11 v12 v13 v14"

abbreviation (input)
  Thread_trans :: "(cte) \<Rightarrow> (cte) \<Rightarrow> (cte) \<Rightarrow> (cte) \<Rightarrow> (cte) \<Rightarrow> (domain) \<Rightarrow> (thread_state) \<Rightarrow> (priority) \<Rightarrow> (bool) \<Rightarrow> (fault option) \<Rightarrow> (nat) \<Rightarrow> (cptr) \<Rightarrow> (vptr) \<Rightarrow> ((machine_word) option) \<Rightarrow> (user_context) \<Rightarrow> tcb" ("Thread'_ \<lparr> tcbCTable= _, tcbVTable= _, tcbReply= _, tcbCaller= _, tcbIPCBufferFrame= _, tcbDomain= _, tcbState= _, tcbPriority= _, tcbQueued= _, tcbFault= _, tcbTimeSlice= _, tcbFaultHandler= _, tcbIPCBuffer= _, tcbBoundAEP= _, tcbContext= _ \<rparr>")
where
  "Thread_ \<lparr> tcbCTable= v0, tcbVTable= v1, tcbReply= v2, tcbCaller= v3, tcbIPCBufferFrame= v4, tcbDomain= v5, tcbState= v6, tcbPriority= v7, tcbQueued= v8, tcbFault= v9, tcbTimeSlice= v10, tcbFaultHandler= v11, tcbIPCBuffer= v12, tcbBoundAEP= v13, tcbContext= v14 \<rparr> == Thread v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14"

lemma tcbVTable_tcbVTable_update [simp]:
  "tcbVTable (tcbVTable_update f v) = f (tcbVTable v)"
  by (cases v) simp

lemma tcbVTable_tcbIPCBufferFrame_update [simp]:
  "tcbVTable (tcbIPCBufferFrame_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbState_update [simp]:
  "tcbVTable (tcbState_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbCTable_update [simp]:
  "tcbVTable (tcbCTable_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbFaultHandler_update [simp]:
  "tcbVTable (tcbFaultHandler_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbIPCBuffer_update [simp]:
  "tcbVTable (tcbIPCBuffer_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbContext_update [simp]:
  "tcbVTable (tcbContext_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbCaller_update [simp]:
  "tcbVTable (tcbCaller_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbBoundAEP_update [simp]:
  "tcbVTable (tcbBoundAEP_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbDomain_update [simp]:
  "tcbVTable (tcbDomain_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbReply_update [simp]:
  "tcbVTable (tcbReply_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbQueued_update [simp]:
  "tcbVTable (tcbQueued_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbPriority_update [simp]:
  "tcbVTable (tcbPriority_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbFault_update [simp]:
  "tcbVTable (tcbFault_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbVTable_tcbTimeSlice_update [simp]:
  "tcbVTable (tcbTimeSlice_update f v) = tcbVTable v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbVTable_update [simp]:
  "tcbIPCBufferFrame (tcbVTable_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbIPCBufferFrame_update [simp]:
  "tcbIPCBufferFrame (tcbIPCBufferFrame_update f v) = f (tcbIPCBufferFrame v)"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbState_update [simp]:
  "tcbIPCBufferFrame (tcbState_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbCTable_update [simp]:
  "tcbIPCBufferFrame (tcbCTable_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbFaultHandler_update [simp]:
  "tcbIPCBufferFrame (tcbFaultHandler_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbIPCBuffer_update [simp]:
  "tcbIPCBufferFrame (tcbIPCBuffer_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbContext_update [simp]:
  "tcbIPCBufferFrame (tcbContext_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbCaller_update [simp]:
  "tcbIPCBufferFrame (tcbCaller_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbBoundAEP_update [simp]:
  "tcbIPCBufferFrame (tcbBoundAEP_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbDomain_update [simp]:
  "tcbIPCBufferFrame (tcbDomain_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbReply_update [simp]:
  "tcbIPCBufferFrame (tcbReply_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbQueued_update [simp]:
  "tcbIPCBufferFrame (tcbQueued_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbPriority_update [simp]:
  "tcbIPCBufferFrame (tcbPriority_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbFault_update [simp]:
  "tcbIPCBufferFrame (tcbFault_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbIPCBufferFrame_tcbTimeSlice_update [simp]:
  "tcbIPCBufferFrame (tcbTimeSlice_update f v) = tcbIPCBufferFrame v"
  by (cases v) simp

lemma tcbState_tcbVTable_update [simp]:
  "tcbState (tcbVTable_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbIPCBufferFrame_update [simp]:
  "tcbState (tcbIPCBufferFrame_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbState_update [simp]:
  "tcbState (tcbState_update f v) = f (tcbState v)"
  by (cases v) simp

lemma tcbState_tcbCTable_update [simp]:
  "tcbState (tcbCTable_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbFaultHandler_update [simp]:
  "tcbState (tcbFaultHandler_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbIPCBuffer_update [simp]:
  "tcbState (tcbIPCBuffer_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbContext_update [simp]:
  "tcbState (tcbContext_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbCaller_update [simp]:
  "tcbState (tcbCaller_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbBoundAEP_update [simp]:
  "tcbState (tcbBoundAEP_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbDomain_update [simp]:
  "tcbState (tcbDomain_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbReply_update [simp]:
  "tcbState (tcbReply_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbQueued_update [simp]:
  "tcbState (tcbQueued_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbPriority_update [simp]:
  "tcbState (tcbPriority_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbFault_update [simp]:
  "tcbState (tcbFault_update f v) = tcbState v"
  by (cases v) simp

lemma tcbState_tcbTimeSlice_update [simp]:
  "tcbState (tcbTimeSlice_update f v) = tcbState v"
  by (cases v) simp

lemma tcbCTable_tcbVTable_update [simp]:
  "tcbCTable (tcbVTable_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbIPCBufferFrame_update [simp]:
  "tcbCTable (tcbIPCBufferFrame_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbState_update [simp]:
  "tcbCTable (tcbState_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbCTable_update [simp]:
  "tcbCTable (tcbCTable_update f v) = f (tcbCTable v)"
  by (cases v) simp

lemma tcbCTable_tcbFaultHandler_update [simp]:
  "tcbCTable (tcbFaultHandler_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbIPCBuffer_update [simp]:
  "tcbCTable (tcbIPCBuffer_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbContext_update [simp]:
  "tcbCTable (tcbContext_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbCaller_update [simp]:
  "tcbCTable (tcbCaller_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbBoundAEP_update [simp]:
  "tcbCTable (tcbBoundAEP_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbDomain_update [simp]:
  "tcbCTable (tcbDomain_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbReply_update [simp]:
  "tcbCTable (tcbReply_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbQueued_update [simp]:
  "tcbCTable (tcbQueued_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbPriority_update [simp]:
  "tcbCTable (tcbPriority_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbFault_update [simp]:
  "tcbCTable (tcbFault_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbCTable_tcbTimeSlice_update [simp]:
  "tcbCTable (tcbTimeSlice_update f v) = tcbCTable v"
  by (cases v) simp

lemma tcbFaultHandler_tcbVTable_update [simp]:
  "tcbFaultHandler (tcbVTable_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbIPCBufferFrame_update [simp]:
  "tcbFaultHandler (tcbIPCBufferFrame_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbState_update [simp]:
  "tcbFaultHandler (tcbState_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbCTable_update [simp]:
  "tcbFaultHandler (tcbCTable_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbFaultHandler_update [simp]:
  "tcbFaultHandler (tcbFaultHandler_update f v) = f (tcbFaultHandler v)"
  by (cases v) simp

lemma tcbFaultHandler_tcbIPCBuffer_update [simp]:
  "tcbFaultHandler (tcbIPCBuffer_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbContext_update [simp]:
  "tcbFaultHandler (tcbContext_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbCaller_update [simp]:
  "tcbFaultHandler (tcbCaller_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbBoundAEP_update [simp]:
  "tcbFaultHandler (tcbBoundAEP_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbDomain_update [simp]:
  "tcbFaultHandler (tcbDomain_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbReply_update [simp]:
  "tcbFaultHandler (tcbReply_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbQueued_update [simp]:
  "tcbFaultHandler (tcbQueued_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbPriority_update [simp]:
  "tcbFaultHandler (tcbPriority_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbFault_update [simp]:
  "tcbFaultHandler (tcbFault_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbFaultHandler_tcbTimeSlice_update [simp]:
  "tcbFaultHandler (tcbTimeSlice_update f v) = tcbFaultHandler v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbVTable_update [simp]:
  "tcbIPCBuffer (tcbVTable_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbIPCBufferFrame_update [simp]:
  "tcbIPCBuffer (tcbIPCBufferFrame_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbState_update [simp]:
  "tcbIPCBuffer (tcbState_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbCTable_update [simp]:
  "tcbIPCBuffer (tcbCTable_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbFaultHandler_update [simp]:
  "tcbIPCBuffer (tcbFaultHandler_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbIPCBuffer_update [simp]:
  "tcbIPCBuffer (tcbIPCBuffer_update f v) = f (tcbIPCBuffer v)"
  by (cases v) simp

lemma tcbIPCBuffer_tcbContext_update [simp]:
  "tcbIPCBuffer (tcbContext_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbCaller_update [simp]:
  "tcbIPCBuffer (tcbCaller_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbBoundAEP_update [simp]:
  "tcbIPCBuffer (tcbBoundAEP_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbDomain_update [simp]:
  "tcbIPCBuffer (tcbDomain_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbReply_update [simp]:
  "tcbIPCBuffer (tcbReply_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbQueued_update [simp]:
  "tcbIPCBuffer (tcbQueued_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbPriority_update [simp]:
  "tcbIPCBuffer (tcbPriority_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbFault_update [simp]:
  "tcbIPCBuffer (tcbFault_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbIPCBuffer_tcbTimeSlice_update [simp]:
  "tcbIPCBuffer (tcbTimeSlice_update f v) = tcbIPCBuffer v"
  by (cases v) simp

lemma tcbContext_tcbVTable_update [simp]:
  "tcbContext (tcbVTable_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbIPCBufferFrame_update [simp]:
  "tcbContext (tcbIPCBufferFrame_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbState_update [simp]:
  "tcbContext (tcbState_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbCTable_update [simp]:
  "tcbContext (tcbCTable_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbFaultHandler_update [simp]:
  "tcbContext (tcbFaultHandler_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbIPCBuffer_update [simp]:
  "tcbContext (tcbIPCBuffer_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbContext_update [simp]:
  "tcbContext (tcbContext_update f v) = f (tcbContext v)"
  by (cases v) simp

lemma tcbContext_tcbCaller_update [simp]:
  "tcbContext (tcbCaller_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbBoundAEP_update [simp]:
  "tcbContext (tcbBoundAEP_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbDomain_update [simp]:
  "tcbContext (tcbDomain_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbReply_update [simp]:
  "tcbContext (tcbReply_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbQueued_update [simp]:
  "tcbContext (tcbQueued_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbPriority_update [simp]:
  "tcbContext (tcbPriority_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbFault_update [simp]:
  "tcbContext (tcbFault_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbContext_tcbTimeSlice_update [simp]:
  "tcbContext (tcbTimeSlice_update f v) = tcbContext v"
  by (cases v) simp

lemma tcbCaller_tcbVTable_update [simp]:
  "tcbCaller (tcbVTable_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbIPCBufferFrame_update [simp]:
  "tcbCaller (tcbIPCBufferFrame_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbState_update [simp]:
  "tcbCaller (tcbState_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbCTable_update [simp]:
  "tcbCaller (tcbCTable_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbFaultHandler_update [simp]:
  "tcbCaller (tcbFaultHandler_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbIPCBuffer_update [simp]:
  "tcbCaller (tcbIPCBuffer_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbContext_update [simp]:
  "tcbCaller (tcbContext_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbCaller_update [simp]:
  "tcbCaller (tcbCaller_update f v) = f (tcbCaller v)"
  by (cases v) simp

lemma tcbCaller_tcbBoundAEP_update [simp]:
  "tcbCaller (tcbBoundAEP_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbDomain_update [simp]:
  "tcbCaller (tcbDomain_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbReply_update [simp]:
  "tcbCaller (tcbReply_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbQueued_update [simp]:
  "tcbCaller (tcbQueued_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbPriority_update [simp]:
  "tcbCaller (tcbPriority_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbFault_update [simp]:
  "tcbCaller (tcbFault_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbCaller_tcbTimeSlice_update [simp]:
  "tcbCaller (tcbTimeSlice_update f v) = tcbCaller v"
  by (cases v) simp

lemma tcbBoundAEP_tcbVTable_update [simp]:
  "tcbBoundAEP (tcbVTable_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbIPCBufferFrame_update [simp]:
  "tcbBoundAEP (tcbIPCBufferFrame_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbState_update [simp]:
  "tcbBoundAEP (tcbState_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbCTable_update [simp]:
  "tcbBoundAEP (tcbCTable_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbFaultHandler_update [simp]:
  "tcbBoundAEP (tcbFaultHandler_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbIPCBuffer_update [simp]:
  "tcbBoundAEP (tcbIPCBuffer_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbContext_update [simp]:
  "tcbBoundAEP (tcbContext_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbCaller_update [simp]:
  "tcbBoundAEP (tcbCaller_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbBoundAEP_update [simp]:
  "tcbBoundAEP (tcbBoundAEP_update f v) = f (tcbBoundAEP v)"
  by (cases v) simp

lemma tcbBoundAEP_tcbDomain_update [simp]:
  "tcbBoundAEP (tcbDomain_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbReply_update [simp]:
  "tcbBoundAEP (tcbReply_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbQueued_update [simp]:
  "tcbBoundAEP (tcbQueued_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbPriority_update [simp]:
  "tcbBoundAEP (tcbPriority_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbFault_update [simp]:
  "tcbBoundAEP (tcbFault_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbBoundAEP_tcbTimeSlice_update [simp]:
  "tcbBoundAEP (tcbTimeSlice_update f v) = tcbBoundAEP v"
  by (cases v) simp

lemma tcbDomain_tcbVTable_update [simp]:
  "tcbDomain (tcbVTable_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbIPCBufferFrame_update [simp]:
  "tcbDomain (tcbIPCBufferFrame_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbState_update [simp]:
  "tcbDomain (tcbState_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbCTable_update [simp]:
  "tcbDomain (tcbCTable_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbFaultHandler_update [simp]:
  "tcbDomain (tcbFaultHandler_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbIPCBuffer_update [simp]:
  "tcbDomain (tcbIPCBuffer_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbContext_update [simp]:
  "tcbDomain (tcbContext_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbCaller_update [simp]:
  "tcbDomain (tcbCaller_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbBoundAEP_update [simp]:
  "tcbDomain (tcbBoundAEP_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbDomain_update [simp]:
  "tcbDomain (tcbDomain_update f v) = f (tcbDomain v)"
  by (cases v) simp

lemma tcbDomain_tcbReply_update [simp]:
  "tcbDomain (tcbReply_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbQueued_update [simp]:
  "tcbDomain (tcbQueued_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbPriority_update [simp]:
  "tcbDomain (tcbPriority_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbFault_update [simp]:
  "tcbDomain (tcbFault_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbDomain_tcbTimeSlice_update [simp]:
  "tcbDomain (tcbTimeSlice_update f v) = tcbDomain v"
  by (cases v) simp

lemma tcbReply_tcbVTable_update [simp]:
  "tcbReply (tcbVTable_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbIPCBufferFrame_update [simp]:
  "tcbReply (tcbIPCBufferFrame_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbState_update [simp]:
  "tcbReply (tcbState_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbCTable_update [simp]:
  "tcbReply (tcbCTable_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbFaultHandler_update [simp]:
  "tcbReply (tcbFaultHandler_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbIPCBuffer_update [simp]:
  "tcbReply (tcbIPCBuffer_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbContext_update [simp]:
  "tcbReply (tcbContext_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbCaller_update [simp]:
  "tcbReply (tcbCaller_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbBoundAEP_update [simp]:
  "tcbReply (tcbBoundAEP_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbDomain_update [simp]:
  "tcbReply (tcbDomain_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbReply_update [simp]:
  "tcbReply (tcbReply_update f v) = f (tcbReply v)"
  by (cases v) simp

lemma tcbReply_tcbQueued_update [simp]:
  "tcbReply (tcbQueued_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbPriority_update [simp]:
  "tcbReply (tcbPriority_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbFault_update [simp]:
  "tcbReply (tcbFault_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbReply_tcbTimeSlice_update [simp]:
  "tcbReply (tcbTimeSlice_update f v) = tcbReply v"
  by (cases v) simp

lemma tcbQueued_tcbVTable_update [simp]:
  "tcbQueued (tcbVTable_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbIPCBufferFrame_update [simp]:
  "tcbQueued (tcbIPCBufferFrame_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbState_update [simp]:
  "tcbQueued (tcbState_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbCTable_update [simp]:
  "tcbQueued (tcbCTable_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbFaultHandler_update [simp]:
  "tcbQueued (tcbFaultHandler_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbIPCBuffer_update [simp]:
  "tcbQueued (tcbIPCBuffer_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbContext_update [simp]:
  "tcbQueued (tcbContext_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbCaller_update [simp]:
  "tcbQueued (tcbCaller_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbBoundAEP_update [simp]:
  "tcbQueued (tcbBoundAEP_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbDomain_update [simp]:
  "tcbQueued (tcbDomain_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbReply_update [simp]:
  "tcbQueued (tcbReply_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbQueued_update [simp]:
  "tcbQueued (tcbQueued_update f v) = f (tcbQueued v)"
  by (cases v) simp

lemma tcbQueued_tcbPriority_update [simp]:
  "tcbQueued (tcbPriority_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbFault_update [simp]:
  "tcbQueued (tcbFault_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbQueued_tcbTimeSlice_update [simp]:
  "tcbQueued (tcbTimeSlice_update f v) = tcbQueued v"
  by (cases v) simp

lemma tcbPriority_tcbVTable_update [simp]:
  "tcbPriority (tcbVTable_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbIPCBufferFrame_update [simp]:
  "tcbPriority (tcbIPCBufferFrame_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbState_update [simp]:
  "tcbPriority (tcbState_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbCTable_update [simp]:
  "tcbPriority (tcbCTable_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbFaultHandler_update [simp]:
  "tcbPriority (tcbFaultHandler_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbIPCBuffer_update [simp]:
  "tcbPriority (tcbIPCBuffer_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbContext_update [simp]:
  "tcbPriority (tcbContext_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbCaller_update [simp]:
  "tcbPriority (tcbCaller_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbBoundAEP_update [simp]:
  "tcbPriority (tcbBoundAEP_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbDomain_update [simp]:
  "tcbPriority (tcbDomain_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbReply_update [simp]:
  "tcbPriority (tcbReply_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbQueued_update [simp]:
  "tcbPriority (tcbQueued_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbPriority_update [simp]:
  "tcbPriority (tcbPriority_update f v) = f (tcbPriority v)"
  by (cases v) simp

lemma tcbPriority_tcbFault_update [simp]:
  "tcbPriority (tcbFault_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbPriority_tcbTimeSlice_update [simp]:
  "tcbPriority (tcbTimeSlice_update f v) = tcbPriority v"
  by (cases v) simp

lemma tcbFault_tcbVTable_update [simp]:
  "tcbFault (tcbVTable_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbIPCBufferFrame_update [simp]:
  "tcbFault (tcbIPCBufferFrame_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbState_update [simp]:
  "tcbFault (tcbState_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbCTable_update [simp]:
  "tcbFault (tcbCTable_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbFaultHandler_update [simp]:
  "tcbFault (tcbFaultHandler_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbIPCBuffer_update [simp]:
  "tcbFault (tcbIPCBuffer_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbContext_update [simp]:
  "tcbFault (tcbContext_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbCaller_update [simp]:
  "tcbFault (tcbCaller_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbBoundAEP_update [simp]:
  "tcbFault (tcbBoundAEP_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbDomain_update [simp]:
  "tcbFault (tcbDomain_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbReply_update [simp]:
  "tcbFault (tcbReply_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbQueued_update [simp]:
  "tcbFault (tcbQueued_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbPriority_update [simp]:
  "tcbFault (tcbPriority_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbFault_tcbFault_update [simp]:
  "tcbFault (tcbFault_update f v) = f (tcbFault v)"
  by (cases v) simp

lemma tcbFault_tcbTimeSlice_update [simp]:
  "tcbFault (tcbTimeSlice_update f v) = tcbFault v"
  by (cases v) simp

lemma tcbTimeSlice_tcbVTable_update [simp]:
  "tcbTimeSlice (tcbVTable_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbIPCBufferFrame_update [simp]:
  "tcbTimeSlice (tcbIPCBufferFrame_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbState_update [simp]:
  "tcbTimeSlice (tcbState_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbCTable_update [simp]:
  "tcbTimeSlice (tcbCTable_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbFaultHandler_update [simp]:
  "tcbTimeSlice (tcbFaultHandler_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbIPCBuffer_update [simp]:
  "tcbTimeSlice (tcbIPCBuffer_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbContext_update [simp]:
  "tcbTimeSlice (tcbContext_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbCaller_update [simp]:
  "tcbTimeSlice (tcbCaller_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbBoundAEP_update [simp]:
  "tcbTimeSlice (tcbBoundAEP_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbDomain_update [simp]:
  "tcbTimeSlice (tcbDomain_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbReply_update [simp]:
  "tcbTimeSlice (tcbReply_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbQueued_update [simp]:
  "tcbTimeSlice (tcbQueued_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbPriority_update [simp]:
  "tcbTimeSlice (tcbPriority_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbFault_update [simp]:
  "tcbTimeSlice (tcbFault_update f v) = tcbTimeSlice v"
  by (cases v) simp

lemma tcbTimeSlice_tcbTimeSlice_update [simp]:
  "tcbTimeSlice (tcbTimeSlice_update f v) = f (tcbTimeSlice v)"
  by (cases v) simp

datatype kernel_object =
    KOEndpoint endpoint
  | KOAEndpoint async_endpoint
  | KOKernelData
  | KOUserData
  | KOTCB tcb
  | KOCTE cte
  | KOArch arch_kernel_object

datatype scheduler_action =
    ResumeCurrentThread
  | ChooseNewThread
  | SwitchToThread machine_word

datatype irqstate =
    IRQInactive
  | IRQNotifyAEP
  | IRQTimer

datatype interrupt_state =
    InterruptState machine_word "irq \<Rightarrow> irqstate"

primrec
  intStateIRQNode :: "interrupt_state \<Rightarrow> machine_word"
where
  "intStateIRQNode (InterruptState v0 v1) = v0"

primrec
  intStateIRQTable :: "interrupt_state \<Rightarrow> irq \<Rightarrow> irqstate"
where
  "intStateIRQTable (InterruptState v0 v1) = v1"

primrec
  intStateIRQNode_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> interrupt_state \<Rightarrow> interrupt_state"
where
  "intStateIRQNode_update f (InterruptState v0 v1) = InterruptState (f v0) v1"

primrec
  intStateIRQTable_update :: "((irq \<Rightarrow> irqstate) \<Rightarrow> (irq \<Rightarrow> irqstate)) \<Rightarrow> interrupt_state \<Rightarrow> interrupt_state"
where
  "intStateIRQTable_update f (InterruptState v0 v1) = InterruptState v0 (f v1)"

abbreviation (input)
  InterruptState_trans :: "(machine_word) \<Rightarrow> (irq \<Rightarrow> irqstate) \<Rightarrow> interrupt_state" ("InterruptState'_ \<lparr> intStateIRQNode= _, intStateIRQTable= _ \<rparr>")
where
  "InterruptState_ \<lparr> intStateIRQNode= v0, intStateIRQTable= v1 \<rparr> == InterruptState v0 v1"

lemma intStateIRQNode_intStateIRQNode_update [simp]:
  "intStateIRQNode (intStateIRQNode_update f v) = f (intStateIRQNode v)"
  by (cases v) simp

lemma intStateIRQNode_intStateIRQTable_update [simp]:
  "intStateIRQNode (intStateIRQTable_update f v) = intStateIRQNode v"
  by (cases v) simp

lemma intStateIRQTable_intStateIRQNode_update [simp]:
  "intStateIRQTable (intStateIRQNode_update f v) = intStateIRQTable v"
  by (cases v) simp

lemma intStateIRQTable_intStateIRQTable_update [simp]:
  "intStateIRQTable (intStateIRQTable_update f v) = f (intStateIRQTable v)"
  by (cases v) simp

datatype user_data =
    UserData

consts
kernelObjectTypeName :: "kernel_object \<Rightarrow> unit list"

consts
objBitsKO :: "kernel_object \<Rightarrow> nat"

consts
tcbCTableSlot :: "machine_word"

consts
tcbVTableSlot :: "machine_word"

consts
tcbReplySlot :: "machine_word"

consts
tcbCallerSlot :: "machine_word"

consts
tcbIPCBufferSlot :: "machine_word"

consts
maxPriority :: "priority"

consts
maxDomain :: "priority"

consts
nullMDBNode :: "mdbnode"

consts
dschDomain :: "(domain * machine_word) \<Rightarrow> domain"

consts
dschLength :: "(domain * machine_word) \<Rightarrow> machine_word"

consts
wordBits :: "nat"

consts
wordRadix :: "nat"

consts
wordSize :: "nat"

consts
wordSizeCase :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

consts
isReceive :: "thread_state \<Rightarrow> bool"

consts
isSend :: "thread_state \<Rightarrow> bool"

consts
isReply :: "thread_state \<Rightarrow> bool"

consts
maxFreeIndex :: "nat \<Rightarrow> nat"

defs objBitsKO_def:
"objBitsKO x0\<equiv> (case x0 of
    (KOEndpoint _) \<Rightarrow>    wordSizeCase 4 5
  | (KOAEndpoint _) \<Rightarrow>    wordSizeCase 4 5
  | (KOCTE _) \<Rightarrow>    wordSizeCase 4 5
  | (KOTCB _) \<Rightarrow>    9
  | (KOUserData) \<Rightarrow>    pageBits
  | (KOKernelData) \<Rightarrow>    pageBits
  | (KOArch a) \<Rightarrow>    archObjSize a
  )"

defs tcbCTableSlot_def:
"tcbCTableSlot \<equiv> 0"

defs tcbVTableSlot_def:
"tcbVTableSlot \<equiv> 1"

defs tcbReplySlot_def:
"tcbReplySlot \<equiv> 2"

defs tcbCallerSlot_def:
"tcbCallerSlot \<equiv> 3"

defs tcbIPCBufferSlot_def:
"tcbIPCBufferSlot \<equiv> 4"

defs maxPriority_def:
"maxPriority\<equiv> fromIntegral (numPriorities - 1)"

defs maxDomain_def:
"maxDomain\<equiv> fromIntegral (numDomains - 1)"

defs nullMDBNode_def:
"nullMDBNode \<equiv> MDB_ \<lparr>
    mdbNext= nullPointer,
    mdbPrev= nullPointer,
    mdbRevocable= False,
    mdbFirstBadged= False \<rparr>"

defs dschDomain_def:
"dschDomain \<equiv> fst"

defs dschLength_def:
"dschLength \<equiv> snd"

defs wordBits_def:
"wordBits\<equiv> finiteBitSize (undefined::machine_word)"

defs wordRadix_def:
"wordRadix \<equiv> wordSizeCase 5 6"

defs wordSize_def:
"wordSize \<equiv> wordBits div 8"

defs wordSizeCase_def:
"wordSizeCase a b\<equiv> (if wordBits = 32
        then  a
        else if wordBits = 64
        then  b
        else  error []
        )"

defs isReceive_def:
"isReceive x0\<equiv> (case x0 of
    (BlockedOnReceive _ _) \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs isSend_def:
"isSend x0\<equiv> (case x0 of
    (BlockedOnSend _ _ _ _) \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs isReply_def:
"isReply x0\<equiv> (case x0 of
    BlockedOnReply \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs maxFreeIndex_def:
"maxFreeIndex magnitudeBits \<equiv> bit magnitudeBits"



end
