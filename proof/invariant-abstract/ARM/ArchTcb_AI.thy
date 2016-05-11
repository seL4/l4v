(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTcb_AI
imports "../Tcb_AI"
begin

context Arch begin

named_theorems Tcb_AI_asms

definition "Tcb_AI_dummy_const \<equiv> (1 :: nat)"

lemma Tcb_AI_trivial_result[Tcb_AI_asms]:
  "Tcb_AI_dummy_const > 0"
  by (simp add: Tcb_AI_dummy_const_def)

end

interpretation Tcb_AI?: Tcb_AI 
  where Tcb_AI_dummy_const = Arch.Tcb_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Tcb_AI_asms)?)
  qed

end