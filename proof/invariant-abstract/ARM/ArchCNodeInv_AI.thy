(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchCNodeInv_AI
imports "../CNodeInv_AI"
begin

context Arch begin

named_theorems CNodeInv_AI_asms

definition "CNodeInv_AI_dummy_const \<equiv> (1 :: nat)"

lemma CNodeInv_AI_trivial_result[CNodeInv_AI_asms]:
  "CNodeInv_AI_dummy_const > 0"
  by (simp add: CNodeInv_AI_dummy_const_def)

end

interpretation CNodeInv_AI?: CNodeInv_AI 
  where CNodeInv_AI_dummy_const = Arch.CNodeInv_AI_dummy_const
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact CNodeInv_AI_asms)?)
  qed

end