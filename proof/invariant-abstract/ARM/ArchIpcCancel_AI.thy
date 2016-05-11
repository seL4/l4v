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

context Arch begin

named_theorems IpcCancel_AI_asms

definition "IpcCancel_AI_dummy_const \<equiv> (1 :: nat)"

lemma IpcCancel_AI_trivial_result[IpcCancel_AI_asms]:
  "IpcCancel_AI_dummy_const > 0"
  by (simp add: IpcCancel_AI_dummy_const_def)

end

interpretation IpcCancel_AI: IpcCancel_AI
  where IpcCancel_AI_dummy_const = Arch.IpcCancel_AI_dummy_const  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact IpcCancel_AI_asms)?)
  qed

end