(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchEmptyFail
imports EmptyFail
begin

context Arch begin arch_global_naming

named_theorems EmptyFail_R_assms

lemma empty_fail_lookupIPCBuffer[EmptyFail_R_assms]:
  "empty_fail (lookupIPCBuffer r t)"
  by (clarsimp simp: lookupIPCBuffer_def Let_def getThreadBufferSlot_def locateSlot_conv
              split: capability.splits arch_capability.splits | wp | wpc | safe)+

declare setRegister_empty_fail[intro!, simp] (* FIXME: tag original instead *)

end

interpretation EmptyFail_R?: EmptyFail_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact EmptyFail_R_assms)?)
qed

end
