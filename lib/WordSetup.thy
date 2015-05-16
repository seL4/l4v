(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter "Machine Word Setup"

theory WordSetup
imports WordEnum DistinctProp

begin

text {* This theory defines the standard platform-specific word size
and alignment. *}

definition
  word_bits :: nat where
  "word_bits \<equiv> len_of TYPE(32)"

definition
  word_size :: "'a :: numeral" where
  "word_size \<equiv> 4"

lemma word_bits_conv:
  "word_bits = 32" unfolding word_bits_def by simp

lemma word_bits_word_size_conv:
  "word_bits = word_size * 8"
  unfolding word_bits_def word_size_def by simp

definition
  is_aligned :: "'a :: len word \<Rightarrow> nat \<Rightarrow> bool" where
  "is_aligned ptr n \<equiv> 2^n dvd unat ptr"

definition
  ptr_add :: "word32 \<Rightarrow> nat \<Rightarrow> word32" where
  "ptr_add ptr n \<equiv> ptr + of_nat n"

definition
  complement :: "('a :: len) word \<Rightarrow> 'a word"  where
 "complement x \<equiv> x xor -1"

definition
  alignUp :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
 "alignUp x n \<equiv> x + 2 ^ n - 1 && complement (2 ^ n - 1)"

end
