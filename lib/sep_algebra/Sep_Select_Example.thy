(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Select_Example
imports Sep_Select
begin

lemma sep_select: "(A \<and>* B \<and>* C \<and>* D) s \<Longrightarrow> (A \<and>* B \<and>* C \<and>* D) s"
  apply (sep_select 2)       (* moves the 2nd conjunct in the conclusions to the front *)
  apply (sep_select 2 3 4 1) (* we can reorder multiple conjuncts at once *)
  apply (sep_select 2 3 4)   (* the list can be partial *)
  apply (sep_select_asm 3 4) (* sep_select_asm works for the assumptions *)
  oops

end
