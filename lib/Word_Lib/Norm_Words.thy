(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "Normalising Word Numerals"

theory Norm_Words
imports "Signed_Words"
begin

text \<open>
  Normalise word numerals, including negative ones apart from @{term "-1"}, to the
  interval @{text "[0..2^len_of 'a)"}. Only for concrete word lengths.
\<close>

lemma neg_num_bintr:
  "(- numeral x :: 'a::len word) =
  word_of_int (bintrunc (len_of TYPE('a)) (-numeral x))"
  by (simp only: word_ubin.Abs_norm word_neg_numeral_alt)

ML \<open>
  fun is_refl (Const (@{const_name Pure.eq}, _) $ x $ y) = (x = y)
    | is_refl _ = false;

  fun signed_dest_wordT (Type (@{type_name word}, [Type (@{type_name signed}, [T])])) = Word_Lib.dest_binT T
    | signed_dest_wordT T = Word_Lib.dest_wordT T

  fun typ_size_of t = signed_dest_wordT (type_of (Thm.term_of t));

  fun num_len (Const (@{const_name Num.Bit0}, _) $ n) = num_len n + 1
    | num_len (Const (@{const_name Num.Bit1}, _) $ n) = num_len n + 1
    | num_len (Const (@{const_name Num.One}, _)) = 1
    | num_len (Const (@{const_name numeral}, _) $ t) = num_len t
    | num_len (Const (@{const_name uminus}, _) $ t) = num_len t
    | num_len t = raise TERM ("num_len", [t])

  fun unsigned_norm is_neg _ ctxt ct =
  (if is_neg orelse num_len (Thm.term_of ct) > typ_size_of ct then let
      val btr = if is_neg
                then @{thm neg_num_bintr} else @{thm num_abs_bintr}
      val th = [Thm.reflexive ct, mk_eq btr] MRS transitive_thm

      (* will work in context of theory Word as well *)
      val ss = simpset_of (@{context} addsimps @{thms bintrunc_numeral})
      val cnv = simplify (put_simpset ss ctxt) th
    in if is_refl (Thm.prop_of cnv) then NONE else SOME cnv end
    else NONE)
  handle TERM ("num_len", _) => NONE
       | TYPE ("dest_binT", _, _) => NONE
\<close>

simproc_setup
  unsigned_norm ("numeral n::'a::len word") = \<open>unsigned_norm false\<close>

simproc_setup
  unsigned_norm_neg0 ("-numeral (num.Bit0 num)::'a::len word") = \<open>unsigned_norm true\<close>

simproc_setup
  unsigned_norm_neg1 ("-numeral (num.Bit1 num)::'a::len word") = \<open>unsigned_norm true\<close>

declare word_pow_0 [simp]

lemma minus_one_norm:
  "(-1 :: 'a :: len word) = of_nat (2 ^ len_of TYPE('a) - 1)"
  by (simp add:of_nat_diff)

lemmas minus_one_norm_num =
  minus_one_norm [where 'a="'b::len bit0"] minus_one_norm [where 'a="'b::len0 bit1"]

lemma "f (7 :: 2 word) = f 3" by simp

lemma "f 7 = f (3 :: 2 word)" by simp

lemma "f (-2) = f (21 + 1 :: 3 word)" by simp

lemma "f (-2) = f (13 + 1 :: 'a::len word)"
  apply simp (* does not touch generic word length *)
  oops

lemma "f (-2) = f (0xFFFFFFFE :: 32 word)" by simp

lemma "(-1 :: 2 word) = 3" by simp

lemma "f (-2) = f (0xFFFFFFFE :: 32 signed word)" by simp


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

lemma "f (-1) = f (15 :: 4 word)" by simp

lemma "f (-1) = f (7 :: 3 word)" by simp

lemma "f (-1) = f (0xFFFF :: 16 word)" by simp

lemma "f (-1) = f (0xFFFF + 1 :: 'a::len word)"
  apply simp (* does not touch generic -1 *)
  oops

end

end