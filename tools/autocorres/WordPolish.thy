(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory WordPolish
imports WordAbstract
begin

(* Depending on the platform, these names don't necessarily correspond to
   the C types of the same names. But by this point, we're sufficiently
   abstract that it doesn't really matter. *)

definition [simplified]: "LONG_MAX \<equiv> (2 :: int) ^ 63 - 1"
definition [simplified]: "LONG_MIN \<equiv> - ((2 :: int) ^ 63)"
definition [simplified]: "ULONG_MAX \<equiv> (2 :: nat) ^ 64 - 1"

definition [simplified]: "INT_MAX \<equiv> (2 :: int) ^ 31 - 1"
definition [simplified]: "INT_MIN \<equiv> - ((2 :: int) ^ 31)"
definition [simplified]: "UINT_MAX \<equiv> (2 :: nat) ^ 32 - 1"

definition [simplified]: "SHORT_MAX \<equiv> (2 :: int) ^ 15 - 1"
definition [simplified]: "SHORT_MIN \<equiv> - ((2 :: int) ^ 15)"
definition [simplified]: "USHORT_MAX \<equiv> (2 :: nat) ^ 16 - 1"

definition [simplified]: "CHAR_MAX \<equiv> (2 :: int) ^ 7 - 1"
definition [simplified]: "CHAR_MIN \<equiv> - ((2 :: int) ^ 7)"
definition [simplified]: "UCHAR_MAX \<equiv> (2 :: nat) ^ 8 - 1"

(* These are added to the Polish simps after translation *)
lemma WORD_MAX_simps:
   "WORD_MAX TYPE(64) = LONG_MAX"
   "WORD_MAX TYPE(32) = INT_MAX"
   "WORD_MAX TYPE(16) = SHORT_MAX"
   "WORD_MAX TYPE(8) = CHAR_MAX"
  by (auto simp: LONG_MAX_def INT_MAX_def SHORT_MAX_def CHAR_MAX_def WORD_MAX_def)

lemma WORD_MIN_simps:
   "WORD_MIN TYPE(64) = LONG_MIN"
   "WORD_MIN TYPE(32) = INT_MIN"
   "WORD_MIN TYPE(16) = SHORT_MIN"
   "WORD_MIN TYPE(8) = CHAR_MIN"
  by (auto simp: LONG_MIN_def INT_MIN_def SHORT_MIN_def CHAR_MIN_def WORD_MIN_def)

lemma UWORD_MAX_simps:
   "UWORD_MAX TYPE(64) = ULONG_MAX"
   "UWORD_MAX TYPE(32) = UINT_MAX"
   "UWORD_MAX TYPE(16) = USHORT_MAX"
   "UWORD_MAX TYPE(8) = UCHAR_MAX"
  by (auto simp: ULONG_MAX_def UINT_MAX_def USHORT_MAX_def UCHAR_MAX_def UWORD_MAX_def)

lemma MIN_MAX_lemmas_schema:
  "sint (s::'a::len signed word) \<le> WORD_MAX TYPE('a)"
  "WORD_MIN TYPE('a) \<le> sint (s::'a::len signed word)"
  "unat (u::'a::len word) \<le> UWORD_MAX TYPE('a)"
  "\<not> (sint (s::'a::len signed word) > WORD_MAX TYPE('a))"
  "\<not> (WORD_MIN TYPE('a) > sint (s::'a::len signed word))"
  "\<not> (unat (u::'a::len word) > UWORD_MAX TYPE('a))"
  "WORD_MIN TYPE('a) \<le> WORD_MAX TYPE('a)"
  "0 \<le> WORD_MAX TYPE('a)"
  "WORD_MIN TYPE('a) \<le> 0"
  unfolding WORD_MAX_def WORD_MIN_def UWORD_MAX_def
  using unat_lt2p[where x=u] less_eq_Suc_le
        sint_range_size [where w=s, simplified word_size, simplified]
  by auto

lemmas MIN_MAX_lemmas_pre =
  MIN_MAX_lemmas_schema[where 'a=64]
  MIN_MAX_lemmas_schema[where 'a=32]
  MIN_MAX_lemmas_schema[where 'a=16]
  MIN_MAX_lemmas_schema[where 'a=8]

lemmas INT_MIN_MAX_lemmas [simp] =
  MIN_MAX_lemmas_pre[unfolded WORD_MAX_simps WORD_MIN_simps UWORD_MAX_simps]

end
