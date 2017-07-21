(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Invocations_R
imports Invariants_H
begin
context begin interpretation Arch . (*FIXME: arch_split*)
lemma invocation_type_eq[simp]:
  "invocationType = invocation_type"
  apply (rule ext)
  apply (simp add: invocationType_def invocation_type_def Let_def)
  apply safe
   apply (frule from_to_enum)
   apply blast
  apply (cut_tac x=v in maxBound_is_bound)
  apply simp
  done
end
declare resolveAddressBits.simps[simp del]

end
