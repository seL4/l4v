(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Solving Word Equalities"

theory Word_EqI
  imports
    More_Word
    Aligned
    "HOL-Eisbach.Eisbach_Tools"
begin

text \<open>
  Some word equalities can be solved by considering the problem bitwise for all
  @{prop "n < LENGTH('a::len)"}. This is similar to the existing method @{text word_bitwise}
  and expanding into an explicit list of bits. The @{text word_bitwise} only works on
  concrete word lengths, but can treat a wider number of operators (in particular a mix of
  arithmetic, order, and bit operations). The @{text word_eqI} method below works on words of
  abstract size (@{typ "'a word"}) and produces smaller, more abstract goals, but does not deal
  with arithmetic operations.
\<close>

lemmas le_mask_high_bits_len = le_mask_high_bits[unfolded word_size]
lemmas neg_mask_le_high_bits_len = neg_mask_le_high_bits[unfolded word_size]

named_theorems word_eqI_simps

lemmas [word_eqI_simps] =
  word_or_zero
  neg_mask_test_bit
  nth_ucast
  less_2p_is_upper_bits_unset
  le_mask_high_bits_len
  neg_mask_le_high_bits_len
  bang_eq
  is_up
  is_down
  is_aligned_nth
  word_size (* keep this, because the goal may contain "n < size x" terms *)

lemmas word_eqI_folds [symmetric] =
  push_bit_eq_mult
  drop_bit_eq_div
  take_bit_eq_mod

(* bit_eqI subsumes the first rule; kept for backwards compatibility *)
lemmas word_eqI_rules = word_eqI [rule_format, unfolded word_size] bit_eqI

lemma test_bit_lenD:
  "bit x n \<Longrightarrow> n < LENGTH('a) \<and> bit x n" for x :: "'a :: len word"
  by (fastforce dest: test_bit_size simp: word_size)

\<comment> \<open>Method to reduce goals of the form @{prop "P \<Longrightarrow> x = y"} for words of abstract length to
    reasoning on bits of the words. Leaves open goal if unsolved.\<close>
method word_eqI uses simp simp_del split split_del cong flip =
  ((* reduce conclusion to test_bit: *)
   rule word_eqI_rules,
   (* fold common patterns into bit form *)
   (simp only: word_eqI_folds)?,
   (* make sure we're in clarsimp normal form: *)
   (clarsimp simp: simp simp del: simp_del simp flip: flip split: split split del: split_del cong: cong)?,
   (* turn x < 2^n assumptions into mask equations: *)
   ((drule less_mask_eq)+)?,
   (* expand and distribute test_bit everywhere: *)
   (simp only: bit_simps word_eqI_simps)?,
   (* clarsimp normal form again, also resolve negated < and \<le> *)
   (clarsimp simp: simp not_less not_le simp del: simp_del simp flip: flip
             split: split split del: split_del cong: cong)?,
   (* add any additional word size constraints to new indices: *)
   ((drule test_bit_lenD)+)?,
   (* try to make progress (can't use +, would loop): *)
   (simp only: bit_simps word_eqI_simps)?,
   (clarsimp simp: simp simp del: simp_del simp flip: flip
             split: split split del: split_del cong: cong)?,
   (* helps sometimes, rarely: *)
   (simp add: simp test_bit_conj_lt del: simp_del flip: flip split: split split del: split_del cong: cong)?)

\<comment> \<open>Method to reduce goals of the form @{prop "P \<Longrightarrow> x = y"} for words of abstract length to
    reasoning on bits of the words. Fails if goal unsolved, but tries harder than @{method word_eqI}.\<close>
method word_eqI_solve uses simp simp_del split split_del cong flip dest =
  solves \<open>word_eqI simp: simp simp_del: simp_del split: split split_del: split_del
                   cong: cong simp flip: flip;
          (fastforce dest: dest simp: simp flip: flip
                     simp: simp simp del: simp_del split: split split del: split_del cong: cong)?\<close>

end
