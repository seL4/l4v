(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpcCancel_AI
imports IpcCancel_AI
begin

context Arch begin global_naming X64

named_theorems IpcCancel_AI_asms

crunches set_endpoint
  for v_ker_map[wp,IpcCancel_AI_asms]: "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)

crunches set_endpoint
  for eq_ker_map[wp,IpcCancel_AI_asms]: "equal_kernel_mappings"
  (ignore: set_object wp: set_object_equal_mappings crunch_wps)

crunches arch_post_cap_deletion
  for typ_at[wp, IpcCancel_AI_asms]: "\<lambda>s. P (typ_at T p s)"
  and idle_thread[wp, IpcCancel_AI_asms]: "\<lambda>s. P (idle_thread s)"

end

interpretation IpcCancel_AI?: IpcCancel_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact IpcCancel_AI_asms)?)
  qed

end
