(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Invocations_R
imports Bits_R
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
