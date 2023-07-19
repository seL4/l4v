(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas about no_throw. Usually should have a conclusion "no_throw P m".
   Includes some monad equations that have no_throw as a main assumption.  *)

theory Trace_No_Throw
  imports
    Trace_VCG
begin

section "Basic exception reasoning"

text \<open>
  The predicates @{text no_throw} and @{text no_return} allow us to reason about functions in
  the exception monad that never throw an exception or never return normally.\<close>

definition no_throw :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e + 'a) tmonad \<Rightarrow> bool" where
  "no_throw P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_ _. False \<rbrace>"

definition no_return :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b + 'c) tmonad \<Rightarrow> bool" where
  "no_return P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace>\<lambda>_ _. False\<rbrace>,\<lbrace>\<lambda>_ _. True \<rbrace>"

end