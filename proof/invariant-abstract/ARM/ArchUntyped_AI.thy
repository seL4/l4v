(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchUntyped_AI
imports "../Untyped_AI"
begin

context Arch begin

named_theorems Untyped_AI_asms

definition "Untyped_AI_dummy_const \<equiv> (1 :: nat)"

lemma Untyped_AI_trivial_result[Untyped_AI_asms]:
  "Untyped_AI_dummy_const > 0"
  by (simp add: Untyped_AI_dummy_const_def)

end

interpretation Untyped_AI?: Untyped_AI
  where Untyped_AI_dummy_const = Arch.Untyped_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Untyped_AI_asms)?)
  qed

end