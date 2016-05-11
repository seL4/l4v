(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchArch_AI
imports "../Arch_AI"
begin

context Arch begin

named_theorems Arch_AI_asms

definition "Arch_AI_dummy_const \<equiv> (1 :: nat)"

lemma Arch_AI_trivial_result[Arch_AI_asms]:
  "Arch_AI_dummy_const > 0"
  by (simp add: Arch_AI_dummy_const_def)

end

interpretation Arch_AI?: Arch_AI 
  where Arch_AI_dummy_const = Arch.Arch_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Arch_AI_asms)?)
  qed

end