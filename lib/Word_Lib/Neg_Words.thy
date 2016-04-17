(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Neg_Words
imports "~~/src/HOL/Word/Word"
begin

text {*
  Normalise word numerals, including negative ones, to the 
  interval @{text "[0..2^len_of 'a)"}. Only for concrete word lengths.
*}

lemma neg_num_bintr:
  "(- numeral x :: 'a::len word) =
  word_of_int (bintrunc (len_of TYPE('a)) (-numeral x))"
  by (simp only: word_ubin.Abs_norm word_neg_numeral_alt)

ML {*
  fun is_refl (Const (@{const_name Pure.eq}, _) $ x $ y) = (x = y)
    | is_refl _ = false;

  fun typ_size_of t = Word_Lib.dest_wordT (type_of (Thm.term_of t));

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
*}

simproc_setup
  unsigned_norm ("numeral n::'a::len word") = {* unsigned_norm false *}

simproc_setup
  unsigned_norm_neg0 ("-numeral (num.Bit0 num)::'a::len word") = {* unsigned_norm true *}

simproc_setup
  unsigned_norm_neg1 ("-numeral (num.Bit1 num)::'a::len word") = {* unsigned_norm true *}

declare word_pow_0 [simp]

lemma minus_one_norm:
  "(-1 :: ('a :: len) word) = of_nat (2 ^ len_of TYPE('a) - 1)" 
  by (simp add:of_nat_diff)

lemma "f (7 :: 2 word) = f 3" by simp

lemma "f 7 = f (3 :: 2 word)" by simp

lemma "f (-2) = f (22 :: 3 word)" by simp

lemma "f (-1) = f (13 :: 'a::len word)"
  (* apply simp *)
  oops

lemma "f (-2) = f (8589934590 :: 32 word)" by simp

lemma "(-1 :: 2 word) = 3" by simp

(* FIXME: these shouldn't need minus_one_norm: *)
lemma "f (-1) = f (15 :: 4 word)" by (simp add: minus_one_norm)

lemma "f (-1) = f (7 :: 3 word)" by (simp add: minus_one_norm)

lemma "f (-1) = f (0xFFFF :: 16 word)" by (simp add: minus_one_norm)

end