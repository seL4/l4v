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
  ArchTCB_H
begin

context begin interpretation Arch .
requalify_consts
  decodeTransfer
  gpRegisters
  frameRegisters
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
end

abbreviation "mapMaybe \<equiv> option_map"

#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch= bodies_only NOT liftFnMaybe assertDerived archThreadGet archThreadSet asUser sanitiseRegister getSanitiseRegisterInfo

defs asUser_def:
"asUser tptr f\<equiv> (do
        uc \<leftarrow> threadGet  (atcbContextGet o tcbArch) tptr;
        (a, uc') \<leftarrow> select_f (f uc);
        threadSet (\<lambda> tcb. tcb \<lparr> tcbArch := atcbContextSet uc' (tcbArch tcb)\<rparr>) tptr;
        return a
od)"

end
