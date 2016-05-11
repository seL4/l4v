(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchSchedule_AI
imports "../Schedule_AI"
begin

context Arch begin

named_theorems Schedule_AI_asms

definition "Schedule_AI_dummy_const \<equiv> (1 :: nat)"

lemma Schedule_AI_trivial_result[Schedule_AI_asms]:
  "Schedule_AI_dummy_const > 0"
  by (simp add: Schedule_AI_dummy_const_def)

end

interpretation Schedule_AI: Schedule_AI
  where Schedule_AI_dummy_const = Arch.Schedule_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Schedule_AI_asms)?)
  qed

end