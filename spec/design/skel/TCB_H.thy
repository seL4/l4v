(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Thread Control Blocks"

theory TCB_H
imports
  TCBDecls_H
  CNode_H
  VSpace_H
  ArchTCB_H
begin

#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch=ArchTCB_H bodies_only NOT liftFnMaybe assertDerived asUser


defs asUser_def:
"asUser tptr f\<equiv> (do
        uc \<leftarrow> threadGet tcbContext tptr;
        (a, uc') \<leftarrow> select_f (f uc);
        threadSet (\<lambda> tcb. tcb \<lparr> tcbContext := uc' \<rparr>) tptr;
        return a
od)"

end
