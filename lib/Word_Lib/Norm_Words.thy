(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Normalising Word Numerals"

theory Norm_Words
  imports Signed_Words
begin

text \<open>
  Normalise word numerals, including negative ones apart from @{term "-1"}, to the
  interval \<open>[0..2^len_of 'a)\<close>. Only for concrete word lengths.
\<close>

lemma neg_numeral_eq:
  \<open>- numeral n = (word_of_int (take_bit LENGTH('a) (- numeral n)) :: 'a::len word)\<close>
  by transfer simp

ML \<open>
local
  fun signed_dest_wordT \<^Type>\<open>word \<^Type>\<open>signed T\<close>\<close> = Word_Lib.dest_binT T
    | signed_dest_wordT T = Word_Lib.dest_wordT T;

  fun typ_size_of t = signed_dest_wordT (type_of (Thm.term_of t));

  fun num_len \<^Const_>\<open>Num.Bit0 for n\<close> = num_len n + 1
    | num_len \<^Const_>\<open>Num.Bit1 for n\<close> = num_len n + 1
    | num_len \<^Const_>\<open>Num.One\<close> = 1
    | num_len \<^Const_>\<open>numeral _ for t\<close> = num_len t
    | num_len \<^Const_>\<open>uminus _ for t\<close> = num_len t
    | num_len t = raise TERM ("num_len", [t]);

  val expand_pos = mk_eq @{thm num_abs_bintr};
  val expand_neg = mk_eq @{thm neg_numeral_eq};

  fun expand is_neg ct =
    [Thm.reflexive ct, if is_neg then expand_neg else expand_pos] MRS transitive_thm;

  val ss = simpset_of (@{context} |> put_simpset HOL_ss
    |> fold Simplifier.add_simp @{thms take_bit_0 take_bit_numeral_bit0 take_bit_numeral_bit1 take_bit_numeral_minus_bit0 take_bit_numeral_minus_bit1
         pred_numeral_simps len_num0 len_num1 len_bit0 len_bit1 len_signed
         arith_simps
         mult_1 mult_1_right numeral_plus_one uminus_numeral_One take_bit_numeral_minus_1_eq
         power_numeral Num.pow.simps Num.sqr.simps diff_numeral_special
         word_of_int_numeral word_of_int_1});

  fun norm ctxt = Simplifier.rewrite (put_simpset ss ctxt);
in
  (* will work in context of theory Word as well *)
  fun unsigned_norm is_neg _ ctxt ct =
    (if num_len (Thm.term_of ct) > typ_size_of ct orelse is_neg then
      SOME ((expand is_neg then_conv norm ctxt) ct)
    else NONE)
    handle TERM ("num_len", _) => NONE
         | TYPE ("dest_binT", _, _) => NONE
end
\<close>

simproc_setup
  unsigned_norm (\<open>numeral n :: 'a::len word\<close>) = \<open>unsigned_norm false\<close>

simproc_setup
  unsigned_norm_neg0 (\<open>- numeral (num.Bit0 n) :: 'a::len word\<close>) = \<open>unsigned_norm true\<close>

simproc_setup
  unsigned_norm_neg1 (\<open>- numeral (num.Bit1 n) :: 'a::len word\<close>) = \<open>unsigned_norm true\<close>

lemma minus_one_norm:
  \<open>(- 1 :: 'a :: len word) = word_of_nat (2 ^ LENGTH('a) - 1)\<close>
  by simp

lemmas minus_one_norm_num =
  minus_one_norm [where 'a="'b::len bit0"] minus_one_norm [where 'a="'b::len0 bit1"]

context
begin

declaration \<open>fn _ => Context.mapping I (put_simpset HOL_ss)\<close>

context
  notes [[simproc add: unsigned_norm unsigned_norm_neg0 unsigned_norm_neg1]]
begin

private lemma "- 2 = (13 + 1 :: 'a::len word)"
  using numeral_plus_one [simp]
  apply simp (* does not touch generic word length *)
  oops

private lemma "7 = (3 :: 2 word)"
  by simp

private lemma "- 2 = (22 :: 3 word)" 
  by simp

private lemma "- 2 = (0xFFFFFFFE :: 32 word)"
  by simp

private lemma "- 2 = (0xFFFFFFFE :: 32 signed word)"
  by simp

end

end

text \<open>
  We leave @{term "-1"} untouched by default, because it is often useful
  and its normal form can be large.
  To include it in the normalisation, add @{thm [source] minus_one_norm_num}.
  The additional normalisation is restricted to concrete numeral word lengths,
  like the rest.
\<close>

context
  notes minus_one_norm_num [simp]
begin

private lemma "f (- 1) = f (15 :: 4 word)"
  by simp

private lemma "f (- 1) = f (7 :: 3 word)"
  by simp

private lemma "f (- 1) = f (0xFFFF :: 16 word)"
  by simp

private lemma "f (- 1) = f (0xFFFF + 1 :: 'a::len word)"
  apply simp (* does not touch generic -1 *)
  oops

end

end
