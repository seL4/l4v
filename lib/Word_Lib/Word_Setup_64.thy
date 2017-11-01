(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "64-Bit Machine Word Setup"

theory Word_Setup_64
imports Word_Enum
begin

text \<open>This theory defines standard platform-specific word size and alignment.\<close>

definition
  word_bits :: nat where
  "word_bits \<equiv> len_of TYPE(64)"

definition
  word_size :: "'a :: numeral" where
  "word_size \<equiv> 8"

lemma word_bits_conv[code]:
  "word_bits = 64" unfolding word_bits_def by simp

lemma word_bits_word_size_conv:
  "word_bits = word_size * 8"
  unfolding word_bits_def word_size_def by simp

end
