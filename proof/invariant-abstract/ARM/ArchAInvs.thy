(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAInvs
imports AInvs
begin

global_interpretation AInvs_AI?: AInvs_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (solves wpsimp)?)
qed

global_interpretation AInvs_AI_det_ext?: AInvs_AI_det_ext
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; wpsimp)
qed

end
