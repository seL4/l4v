(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Deleting Capabilities"

theory Delete_H
imports
  CNode_H
  Interrupt_H
  Endpoint_H
  Thread_H
begin

definition
  slotsPointed :: "capability \<Rightarrow> machine_word set"
where
 "slotsPointed cap \<equiv> case cap of
   CNodeCap ptr a b c   \<Rightarrow> {ptr}
 | ThreadCap ptr        \<Rightarrow> {ptr}
 | Zombie ptr bits num  \<Rightarrow> {ptr}
 | _                    \<Rightarrow> {}"

primrec
  sethelper :: "bool \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "sethelper True  s = {}"
| "sethelper False s = s"

function
  finaliseSlot' :: "machine_word \<Rightarrow> bool \<Rightarrow> (bool * capability) kernel_p"
where
 "finaliseSlot' x b s =
(\<lambda> finaliseSlot.
(\<lambda> cteDelete.
(\<lambda> reduceZombie.
#INCLUDE_HASKELL SEL4/Object/CNode.lhs BODY finaliseSlot
)
(
#INCLUDE_HASKELL SEL4/Object/CNode.lhs BODY reduceZombie
)
)
(
#INCLUDE_HASKELL SEL4/Object/CNode.lhs BODY cteDelete
)
)
finaliseSlot' x b s"

  by auto

defs
  finaliseSlot_def:
 "finaliseSlot \<equiv> finaliseSlot'"

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs

function
  cteDeleteOne' :: "machine_word \<Rightarrow> unit kernel"
where
 "cteDeleteOne' x s =
(\<lambda> cteDeleteOne.
(\<lambda> deletingIRQHandler.
(\<lambda> cancelIPC.
(\<lambda> suspend.
(\<lambda> finaliseCap.
#INCLUDE_HASKELL SEL4/Object/CNode.lhs BODY cteDeleteOne
)
(
#INCLUDE_HASKELL SEL4/Object/ObjectType.lhs Arch=Arch BODY finaliseCap
)
)
(
#INCLUDE_HASKELL SEL4/Kernel/Thread.lhs BODY suspend
)
)
(
#INCLUDE_HASKELL SEL4/Object/Endpoint.lhs BODY cancelIPC
)
)
(
#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs BODY deletingIRQHandler
)
)
cteDeleteOne' x s"

  by auto

defs
  cteDeleteOne_def1:
 "cteDeleteOne \<equiv> cteDeleteOne'"

termination cteDeleteOne'
  by (rule cteDeleteOne'.termination[OF wf_on_bot], simp+)

lemma cteDeleteOne_def:
 "cteDeleteOne =
(
#INCLUDE_HASKELL SEL4/Object/CNode.lhs BODY cteDeleteOne
)"
  apply (rule ext)+
  apply (subst cteDeleteOne_def1)
  apply (subst cteDeleteOne'.simps)
  apply (unfold finaliseCap_def suspend_def cancelIPC_def
                deletingIRQHandler_def cteDeleteOne_def1)
  apply (rule refl)
  done

lemma card_reduce:
  "(s :: ('a :: finite) set) \<inter> s' = {} \<Longrightarrow> card (UNIV - (s \<union> s')) < card (UNIV - s) = (s' \<noteq> {})"
  apply (case_tac "s' \<subseteq> s")
   apply (simp add: Un_absorb2)
   apply (simp add: Int_absorb1)
  apply (clarsimp simp: subset_iff)
  apply (subst psubset_card_mono)
    apply simp
   apply blast
  apply blast
  done

lemma isCapDs:
  "isUntypedCap cap \<Longrightarrow> \<exists>dev ptr size freeIndex. cap = UntypedCap dev ptr size freeIndex"
  "isEndpointCap cap \<Longrightarrow> \<exists>ptr bdg cans canr cang cangr. cap = EndpointCap ptr bdg cans canr cang cangr"
  "isNotificationCap cap \<Longrightarrow> \<exists>ptr bdg cans canr. cap = NotificationCap ptr bdg cans canr"
  "isCNodeCap cap \<Longrightarrow> \<exists>ptr bits grd gsize. cap = CNodeCap ptr bits grd gsize"
  "isThreadCap cap \<Longrightarrow> \<exists>ptr. cap = ThreadCap ptr"
  "isArchObjectCap cap \<Longrightarrow> \<exists>archcap. cap = ArchObjectCap archcap"
  "isZombie cap \<Longrightarrow> \<exists>ptr bits num. cap = Zombie ptr bits num"
  apply (case_tac cap, simp_all add: isUntypedCap_def)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (case_tac cap, simp_all add: isNotificationCap_def)
  apply (case_tac cap, simp_all add: isCNodeCap_def)
  apply (case_tac cap, simp_all add: isThreadCap_def)
  apply (case_tac cap, simp_all add: isArchObjectCap_def)
  apply (case_tac cap, simp_all add: isZombie_def)
  done

end
