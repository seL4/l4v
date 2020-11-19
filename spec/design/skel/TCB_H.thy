(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Thread Control Blocks"

theory TCB_H
imports
  NotificationDecls_H
  TCBDecls_H
  CNode_H
  VSpace_H
  FaultHandlerDecls_H
  SchedContext_H
  "./$L4V_ARCH/ArchTCB_H"
begin

context begin interpretation Arch .
requalify_consts
  decodeTransfer
  gpRegisters
  frameRegisters
  badgeRegister
  getRegister
  setNextPC
  getRestartPC
  sanitiseRegister
  getSanitiseRegisterInfo
  setRegister
  performTransfer
  msgInfoRegister
  msgRegisters
  fromVPtr
  postModifyRegisters
  tlsBaseRegister
  maxUsToTicks
  timerIRQ
end

abbreviation "mapMaybe \<equiv> option_map"

fun tcbEPFindIndex where
  "tcbEPFindIndex tptr queue curIndex =
#INCLUDE_HASKELL SEL4/Object/TCB.lhs BODY tcbEPFindIndex
  tptr queue curIndex"

declare tcbEPFindIndex.simps[simp del]

#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch= bodies_only NOT liftFnMaybe assertDerived archThreadGet archThreadSet asUser sanitiseRegister getSanitiseRegisterInfo takeWhileM sort_key tcbEPFindIndex awaken

defs asUser_def:
"asUser tptr f\<equiv> (do
        uc \<leftarrow> threadGet  (atcbContextGet o tcbArch) tptr;
        (a, uc') \<leftarrow> select_f (f uc);
        threadSet (\<lambda> tcb. tcb \<lparr> tcbArch := atcbContextSet uc' (tcbArch tcb)\<rparr>) tptr;
        return a
od)"

end
