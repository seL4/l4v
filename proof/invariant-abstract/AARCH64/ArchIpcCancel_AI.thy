(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpcCancel_AI
imports IpcCancel_AI
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for IpcCancel_AI locale *)

crunch arch_post_cap_deletion
  for typ_at[wp, Arch_assms]: "\<lambda>s. P (typ_at T p s)"
  and idle_thread[wp, Arch_assms]: "\<lambda>s. P (idle_thread s)"

lemmas IpcCancel_AI_assms = Arch_assms (* extract accumulated assumptions *)

end

interpretation IpcCancel_AI?: IpcCancel_AI
  proof goal_cases
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact AARCH64.IpcCancel_AI_assms)?)
  qed


end
