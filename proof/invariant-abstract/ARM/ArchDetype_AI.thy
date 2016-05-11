(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchDetype_AI
imports "../Detype_AI"
begin

context Arch begin

named_theorems Detype_AI_asms

definition "Detype_AI_dummy_const \<equiv> (1 :: nat)"

lemma Detype_AI_trivial_result[Detype_AI_asms]:
  "Detype_AI_dummy_const > 0"
  by (simp add: Detype_AI_dummy_const_def)

end

interpretation Detype_AI?: Detype_AI
  where Detype_AI_dummy_const = Arch.Detype_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Detype_AI_asms)?)
  qed

end