(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory SignedWordAbsHeap
imports
  AutoCorres.AutoCorres
begin

text \<open>
  Regression test for signed word abs on the lifted heap.
  Jira issue ID: VER-1112

  For the gory details, see the comment for the function
  WordAbstract.mk_sword_heap_get_rule.
\<close>

external_file "signed_word_abs_heap.c"
install_C_file "signed_word_abs_heap.c"

autocorres [
    ts_rules=nondet,
    unsigned_word_abs=foo bar
  ]
  "signed_word_abs_heap.c"

context signed_word_abs_heap begin
text \<open>
  Previously, lifted word heap accesses would always be translated to
  unsigned @{type nat}s, instead of signed @{typ int}s where appropriate.
\<close>
thm foo'_def bar'_def

lemma bar_123_456:
  "\<lbrace>\<lambda>s. heap_w32 s p = 123 \<and> is_valid_w32 s p\<rbrace>
   bar' (ptr_coerce p) 456
   \<lbrace>\<lambda>r s. r = 579 \<and> heap_w32 s p = 579\<rbrace>!"
  unfolding bar'_def
  apply wp
  apply (clarsimp simp: fun_upd_apply)
  done

text \<open>
  Previously, this was unprovable.
\<close>
lemma bar_n123_456:
  "\<lbrace>\<lambda>s. heap_w32 s p = -123 \<and> is_valid_w32 s p\<rbrace>
   bar' (ptr_coerce p) 456
   \<lbrace>\<lambda>r s. r = 333 \<and> heap_w32 s p = 333\<rbrace>!"
  unfolding bar'_def
  apply wp
  apply (clarsimp simp: fun_upd_apply)
  done

end

end
