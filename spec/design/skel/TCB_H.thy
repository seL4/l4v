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

arch_requalify_consts (H)
  decodeTransfer
  performTransfer
  msgInfoRegister
  msgRegisters
  fromVPtr
  postModifyRegisters
  sanitiseRegister
  getSanitiseRegisterInfo

(* clobbers previously requalified abstract spec constants with design spec versions *)
arch_requalify_consts (aliasing, H)
  gpRegisters
  frameRegisters
  tlsBaseRegister

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
