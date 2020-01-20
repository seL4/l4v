(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory Invocations_R
imports Bits_R
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
