(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchIpc_AI
imports "../Ipc_AI"
begin

context Arch begin

named_theorems Ipc_AI_asms

definition "Ipc_AI_dummy_const \<equiv> (1 :: nat)"

lemma Ipc_AI_trivial_result[Ipc_AI_asms]:
  "Ipc_AI_dummy_const > 0"
  by (simp add: Ipc_AI_dummy_const_def)

end

interpretation Ipc_AI?: Ipc_AI 
  where Ipc_AI_dummy_const = Arch.Ipc_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Ipc_AI_asms)?)
  qed

end