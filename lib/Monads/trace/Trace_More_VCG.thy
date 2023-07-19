(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Partial correctness Hoare logic lemmas over the trace monad. Hoare triples, lifting lemmas, etc.
   If it doesn't contain a Hoare triple it likely doesn't belong in here. *)

theory Trace_More_VCG
  imports
    Trace_VCG
begin

lemma hoare_pre_tautI:
  "\<lbrakk> \<lbrace>A and P\<rbrace> a \<lbrace>B\<rbrace>; \<lbrace>A and not P\<rbrace> a \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> a \<lbrace>B\<rbrace>"
  by (fastforce simp: valid_def split_def pred_conj_def pred_neg_def)

end