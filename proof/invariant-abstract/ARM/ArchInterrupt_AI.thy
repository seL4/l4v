(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchInterrupt_AI
imports "../Interrupt_AI"
begin

context Arch begin

named_theorems Interrupt_AI_asms

definition "Interrupt_AI_dummy_const \<equiv> (1 :: nat)"

lemma Interrupt_AI_trivial_result[Interrupt_AI_asms]:
  "Interrupt_AI_dummy_const > 0"
  by (simp add: Interrupt_AI_dummy_const_def)

end

interpretation Interrupt_AI?: Interrupt_AI 
  where Interrupt_AI_dummy_const = Arch.Interrupt_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Interrupt_AI_asms)?)
  qed

end