(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpcCancel_AI
imports IpcCancel_AI
begin

context Arch begin global_naming RISCV64

named_theorems IpcCancel_AI_assms

crunch arch_post_cap_deletion
  for typ_at[wp, IpcCancel_AI_assms]: "\<lambda>s. P (typ_at T p s)"
  and idle_thread[wp, IpcCancel_AI_assms]: "\<lambda>s. P (idle_thread s)"

end

interpretation IpcCancel_AI?: IpcCancel_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact IpcCancel_AI_assms)?)
  qed


end
