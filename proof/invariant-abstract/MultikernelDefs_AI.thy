(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory MultikernelDefs_AI
imports Invariants_AI
begin

(* FIXME: it would be nice if the existing obj_range was defined in terms of mask_range to match up
          with ut_span below. We might want to make that change first. *)
definition obj_ranges_2 :: "(obj_ref \<Rightarrow> kernel_object option) \<Rightarrow> obj_ref set" where
  "obj_ranges_2 kh \<equiv> \<Union> {obj_range p ko|p ko. kh p = Some ko}"

abbreviation obj_ranges :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "obj_ranges s \<equiv> obj_ranges_2 (kheap s)"

lemmas obj_ranges_def = obj_ranges_2_def

definition ut_span :: "cap \<Rightarrow> obj_ref set" where
  "ut_span cap \<equiv> case cap of UntypedCap _ p sz _ \<Rightarrow> mask_range p sz | _ \<Rightarrow> {}"

abbreviation ut_spans_of :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> obj_ref set option" where
  "ut_spans_of s \<equiv> caps_of_state s ||> ut_span"

(* Like option_set, but for 'a set option instead of 'a option, maps None to {}, Some S to S *)
abbreviation opt_set :: "'a set option \<Rightarrow> 'a set" where
  "opt_set \<equiv> none_bot id"

definition ut_ranges_2 :: "(cslot_ptr \<Rightarrow> obj_ref set option) \<Rightarrow> obj_ref set" where
  "ut_ranges_2 ut_spans \<equiv> \<Union>cptr. opt_set (ut_spans cptr)"

abbreviation ut_ranges :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "ut_ranges s \<equiv> ut_ranges_2 (ut_spans_of s)"

lemmas ut_ranges_def = ut_ranges_2_def

definition kernel_cover :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "kernel_cover s \<equiv> obj_ranges s \<union> ut_ranges s \<union> global_refs s"

(* This is the main invariant lemma to prove, likely will need invs et al as precondition *)
lemma call_kernel_cover_bounded:
  "call_kernel ev \<lbrace>\<lambda>s. kernel_cover s \<subseteq> C\<rbrace>"
  sorry

end
