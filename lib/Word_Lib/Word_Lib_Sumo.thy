(*
 * Copyright Florian Haftmann
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Ancient comprehensive Word Library\<close>

theory Word_Lib_Sumo
imports
  "HOL-Library.Word"
  Aligned
  Bit_Comprehension
  Bit_Shifts_Infix_Syntax
  Bits_Int
  Bitwise_Signed
  Bitwise
  Enumeration_Word
  Generic_set_bit
  Hex_Words
  Least_significant_bit
  More_Arithmetic
  More_Divides
  More_Sublist
  Even_More_List
  More_Misc
  Strict_part_mono
  Legacy_Aliases
  Most_significant_bit
  Next_and_Prev
  Norm_Words
  Reversed_Bit_Lists
  Rsplit
  Signed_Words
  Syntax_Bundles
  Typedef_Morphisms
  Type_Syntax
  Word_EqI
  Word_Lemmas
  Word_8
  Word_16
  Word_32
  Word_Syntax
  Signed_Division_Word
  Singleton_Bit_Shifts
  More_Word_Operations
  Many_More
begin

unbundle bit_operations_syntax
unbundle bit_projection_infix_syntax

declare word_induct2[induct type]
declare word_nat_cases[cases type]

declare signed_take_bit_Suc [simp]

(* these generate take_bit terms, which we often don't want for concrete lengths *)
lemmas of_int_and_nat = unsigned_of_nat unsigned_of_int signed_of_int signed_of_nat

bundle no_take_bit
begin
declare of_int_and_nat[simp del]
end

lemmas bshiftr1_def = bshiftr1_eq
lemmas is_down_def = is_down_eq
lemmas is_up_def = is_up_eq
lemmas mask_def = mask_eq
lemmas scast_def = scast_eq
lemmas shiftl1_def = shiftl1_eq
lemmas shiftr1_def = shiftr1_eq
lemmas sshiftr1_def = sshiftr1_eq
lemmas sshiftr_def = sshiftr_eq_funpow_sshiftr1
lemmas to_bl_def = to_bl_eq
lemmas ucast_def = ucast_eq
lemmas unat_def = unat_eq_nat_uint
lemmas word_cat_def = word_cat_eq
lemmas word_reverse_def = word_reverse_eq_of_bl_rev_to_bl
lemmas word_roti_def = word_roti_eq_word_rotr_word_rotl
lemmas word_rotl_def = word_rotl_eq
lemmas word_rotr_def = word_rotr_eq
lemmas word_sle_def = word_sle_eq
lemmas word_sless_def = word_sless_eq

lemmas uint_0 = uint_nonnegative
lemmas uint_lt = uint_bounded
lemmas uint_mod_same = uint_idem
lemmas of_nth_def = word_set_bits_def

lemmas of_nat_word_eq_iff = word_of_nat_eq_iff
lemmas of_nat_word_eq_0_iff = word_of_nat_eq_0_iff
lemmas of_int_word_eq_iff = word_of_int_eq_iff
lemmas of_int_word_eq_0_iff = word_of_int_eq_0_iff

lemmas word_next_def = word_next_unfold

lemmas word_prev_def = word_prev_unfold

lemmas is_aligned_def = is_aligned_iff_dvd_nat

lemmas word_and_max_simps =
  word8_and_max_simp
  word16_and_max_simp
  word32_and_max_simp

lemma distinct_lemma: "f x \<noteq> f y \<Longrightarrow> x \<noteq> y" by auto

lemmas and_bang = word_and_nth

lemmas sdiv_int_def = signed_divide_int_def
lemmas smod_int_def = signed_modulo_int_def

(* shortcut for some specific lengths *)
lemma word_fixed_sint_1[simp]:
  "sint (1::8 word) = 1"
  "sint (1::16 word) = 1"
  "sint (1::32 word) = 1"
  "sint (1::64 word) = 1"
  by (auto simp: sint_word_ariths)

declare of_nat_diff [simp]

(* Haskellish names/syntax *)
notation (input)
  bit ("testBit")

lemmas cast_simps = cast_simps ucast_down_bl

(* shadows the slightly weaker Word.nth_ucast *)
lemma nth_ucast:
  "(ucast (w::'a::len word)::'b::len word) !! n =
   (w !! n \<and> n < min LENGTH('a) LENGTH('b))"
  by (auto simp add: bit_simps not_le dest: bit_imp_le_length)

end
