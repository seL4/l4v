(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "Additional Syntax for Word Bit Operations"

theory Word_Syntax
imports
  "HOL-Word.More_Word"
  WordBitwise_Signed
  Hex_Words
  Norm_Words
  Word_Type_Syntax
begin

text \<open>Additional bit and type syntax that forces word types.\<close>

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

(* FIXME: move to Word distribution *)
lemma bin_nth_minus_Bit0[simp]:
  "0 < n \<Longrightarrow> bin_nth (numeral (num.Bit0 w)) n = bin_nth (numeral w) (n - 1)"
  by (cases n; simp)

lemma bin_nth_minus_Bit1[simp]:
  "0 < n \<Longrightarrow> bin_nth (numeral (num.Bit1 w)) n = bin_nth (numeral w) (n - 1)"
  by (cases n; simp)

end
