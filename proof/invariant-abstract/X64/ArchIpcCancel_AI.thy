(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchIpcCancel_AI
imports "../IpcCancel_AI"
begin

context Arch begin global_naming ARM

named_theorems IpcCancel_AI_asms

crunch v_ker_map[wp,IpcCancel_AI_asms]: set_endpoint "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)

crunch eq_ker_map[wp,IpcCancel_AI_asms]: set_endpoint "equal_kernel_mappings"
  (ignore: set_object wp: set_object_equal_mappings crunch_wps)

end

interpretation IpcCancel_AI?: IpcCancel_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact IpcCancel_AI_asms)?) 
  qed

end
