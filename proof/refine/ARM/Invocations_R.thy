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

lemma invocationType_eq[simp]:
  "invocationType = invocation_type"
  unfolding invocationType_def invocation_type_def Let_def
  by (rule ext, simp) (metis from_to_enum maxBound_is_bound')

lemma genInvocationType_eq[simp]:
  "genInvocationType = gen_invocation_type"
  by (rule ext) (simp add: genInvocationType_def gen_invocation_type_def)

end

declare resolveAddressBits.simps[simp del]

end
