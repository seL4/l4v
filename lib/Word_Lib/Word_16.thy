(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Words of Length 16"

theory Word_16
imports
  More_Word
  Signed_Words
begin

lemma len16: "len_of (x :: 16 itself) = 16" by simp

context
  includes bit_operations_syntax
begin

lemma word16_and_max_simp:
  \<open>x AND 0xFFFF = x\<close> for x :: \<open>16 word\<close>
  using word_and_full_mask_simp [of x]
  by (simp add: numeral_eq_Suc mask_Suc_exp)

end

end
