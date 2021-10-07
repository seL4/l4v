(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Solving Word Equalities"

theory Word_EqI
  imports
    More_Word
    Traditional_Infix_Syntax
    "HOL-Eisbach.Eisbach_Tools"
begin

text \<open>
  Some word equalities can be solved by considering the problem bitwise for all
  @{prop "n < LENGTH('a::len)"}, which is different to running @{text word_bitwise}
  and expanding into an explicit list of bits.
\<close>

named_theorems word_eqI_simps

lemmas [word_eqI_simps] =
  word_ops_nth_size
  word_size
  word_or_zero
  neg_mask_test_bit
  nth_ucast
  nth_w2p nth_shiftl
  nth_shiftr
  less_2p_is_upper_bits_unset
  le_mask_high_bits
  bang_eq
  neg_test_bit
  is_up
  is_down

lemmas word_eqI_rule = word_eqI [rule_format]

lemma test_bit_lenD:
  "x !! n \<Longrightarrow> n < LENGTH('a) \<and> x !! n" for x :: "'a :: len word"
  by (fastforce dest: test_bit_size simp: word_size)

method word_eqI uses simp simp_del split split_del cong flip =
  ((* reduce conclusion to test_bit: *)
   rule word_eqI_rule,
   (* make sure we're in clarsimp normal form: *)
   (clarsimp simp: simp simp del: simp_del simp flip: flip split: split split del: split_del cong: cong)?,
   (* turn x < 2^n assumptions into mask equations: *)
   ((drule less_mask_eq)+)?,
   (* expand and distribute test_bit everywhere: *)
   (clarsimp simp: word_eqI_simps simp simp del: simp_del simp flip: flip
             split: split split del: split_del cong: cong)?,
   (* add any additional word size constraints to new indices: *)
   ((drule test_bit_lenD)+)?,
   (* try to make progress (can't use +, would loop): *)
   (clarsimp simp: word_eqI_simps simp simp del: simp_del simp flip: flip
             split: split split del: split_del cong: cong)?,
   (* helps sometimes, rarely: *)
   (simp add: simp test_bit_conj_lt del: simp_del flip: flip split: split split del: split_del cong: cong)?)

method word_eqI_solve uses simp simp_del split split_del cong flip =
  solves \<open>word_eqI simp: simp simp_del: simp_del split: split split_del: split_del
                   cong: cong simp flip: flip;
          (fastforce dest: test_bit_size simp: word_eqI_simps simp flip: flip
                     simp: simp simp del: simp_del split: split split del: split_del cong: cong)?\<close>

end
