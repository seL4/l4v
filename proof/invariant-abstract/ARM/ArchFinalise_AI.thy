(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchFinalise_AI
imports "../Finalise_AI"
begin

context Arch begin

named_theorems Finalise_AI_asms

definition "Finalise_AI_dummy_const \<equiv> (1 :: nat)"

lemma Finalise_AI_trivial_result[Finalise_AI_asms]:
  "Finalise_AI_dummy_const > 0"
  by (simp add: Finalise_AI_dummy_const_def)

end

interpretation Finalise_AI?: Finalise_AI 
  where Finalise_AI_dummy_const = Arch.Finalise_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Finalise_AI_asms)?)
  qed

end