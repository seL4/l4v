(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchEmptyFail
imports EmptyFail
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for EmptyFail_R locale *)

lemma empty_fail_lookupIPCBuffer[Arch_assms]:
  "empty_fail (lookupIPCBuffer r t)"
  by (clarsimp simp: lookupIPCBuffer_def Let_def getThreadBufferSlot_def locateSlot_conv
              split: capability.splits arch_capability.splits | wp | wpc | safe)+

declare setRegister_empty_fail[intro!, simp] (* FIXME: tag original instead *)

lemmas EmptyFail_R_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

interpretation EmptyFail_R?: EmptyFail_R
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; fact ARM.EmptyFail_R_assms)?)
qed

end
