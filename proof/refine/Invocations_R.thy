(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Invocations_R
imports ArchBits_R
begin

declare resolveAddressBits.simps[simp del]

(* proof is identical and uninteresting on all architectures *)
lemma (in Arch) invocationType_eq:
  "invocationType = invocation_type"
  unfolding invocationType_def invocation_type_def Let_def
  by (rule ext, simp) (metis from_to_enum maxBound_is_bound')

requalify_facts Arch.invocationType_eq
declare invocationType_eq[simp]

lemma genInvocationType_eq[simp]:
  "genInvocationType = gen_invocation_type"
  by (rule ext) (simp add: genInvocationType_def gen_invocation_type_def)

end
