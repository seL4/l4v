(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
  Compatibility theory to recreate syntax for NICTA developments.
*)

theory NICTACompat
imports
  "~~/src/HOL/Word/WordBitwise"
  SignedWords
  NICTATools
  Eisbach_Compat
begin

(* all theories should import from NICTACompat rather than any ancestors *)

type_synonym word8 = "8 word"
type_synonym word16 = "16 word"
type_synonym word32 = "32 word"
type_synonym word64 = "64 word"

lemma len8: "len_of (x :: 8 itself) = 8" by simp
lemma len16: "len_of (x :: 16 itself) = 16" by simp
lemma len32: "len_of (x :: 32 itself) = 32" by simp
lemma len64: "len_of (x :: 64 itself) = 64" by simp


abbreviation
  wordNOT  :: "'a::len0 word \<Rightarrow> 'a word"      ("~~ _" [70] 71)
where
  "~~ x == NOT x"

abbreviation
  wordAND  :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixr "&&" 64)
where
  "a && b == a AND b"

abbreviation
  wordOR   :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixr "||"  59)
where
  "a || b == a OR b"

abbreviation
  wordXOR  :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixr "xor" 59)
where
  "a xor b == a XOR b"

(* testing for presence of word_bitwise *)
lemma "((x :: word32) >> 3) AND 7 = (x AND 56) >> 3"
  by word_bitwise

(* print words in hex *)
(* mostly clagged from Num.thy *)
typed_print_translation  {*
let
  fun dest_num (Const (@{const_syntax Num.Bit0}, _) $ n) = 2 * dest_num n
    | dest_num (Const (@{const_syntax Num.Bit1}, _) $ n) = 2 * dest_num n + 1
    | dest_num (Const (@{const_syntax Num.One}, _)) = 1;

  fun dest_bin_hex_str tm =
  let
    val num = dest_num tm;
    val pre = if num < 10 then "" else "0x"
  in
    pre ^ (Int.fmt StringCvt.HEX num)
  end;

  fun num_tr' sign ctxt T [n] =
    let
      val k = dest_bin_hex_str n;
      val t' = Syntax.const @{syntax_const "_Numeral"} $
        Syntax.free (sign ^ k);
    in
      case T of
        Type (@{type_name fun}, [_, T' as Type("Word.word",_)]) =>
          if not (Config.get ctxt show_types) andalso can Term.dest_Type T'
          then t'
          else Syntax.const @{syntax_const "_constrain"} $ t' $
                            Syntax_Phases.term_of_typ ctxt T'
      | T' => if T' = dummyT then t' else raise Match
    end;
in [(@{const_syntax numeral}, num_tr' "")] end
*}

lemma neg_num_bintr:
  "(- numeral x :: 'a::len word) =
  word_of_int (bintrunc (len_of TYPE('a)) (-numeral x))"
  by (simp only: word_ubin.Abs_norm word_neg_numeral_alt)

(* normalise word numerals to the interval [0..2^len_of 'a) *)
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

lemma minus_one_norm:
 "(-1 :: ('a :: len) word)
    = of_nat (2 ^ len_of TYPE('a) - 1)"
  by (simp add:of_nat_diff)
lemma "f (7 :: 2 word) = f 3"
  apply simp
  done

lemma "f 7 = f (3 :: 2 word)"
  apply simp
  done

lemma "f (-2) = f (22 :: 3 word)"
  apply simp
  done

lemma "f (-1) = f (13 :: 'a::len word)"
  (* apply simp *)
  oops

lemma "f (-2) = f (8589934590 :: word32)"
  using [[simp_trace]]
  apply simp
  done

lemma "(-1 :: 2 word) = 3"
  apply simp
  done

lemma "f (-1) = f (15 :: 4 word)"
  apply (simp add: minus_one_norm)
  done

lemma "f (-1) = f (7 :: 3 word)"
  apply (simp add: minus_one_norm)
  done

lemma "f (-1) = f (0xFFFF :: 16 word)"
  by (simp add: minus_one_norm)

lemma bin_nth_minus_Bit0[simp]:
  "0 < n \<Longrightarrow> bin_nth (numeral (num.Bit0 w)) n = bin_nth (numeral w) (n - 1)"
  by (cases n, simp_all)

lemma bin_nth_minus_Bit1[simp]:
  "0 < n \<Longrightarrow> bin_nth (numeral (num.Bit1 w)) n = bin_nth (numeral w) (n - 1)"
  by (cases n, simp_all)

end
