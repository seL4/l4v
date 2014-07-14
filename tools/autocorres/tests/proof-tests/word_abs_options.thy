(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory word_abs_options imports "../../AutoCorres" begin

install_C_file "word_abs_options.c"

autocorres [
  ts_rules = nondet,
  unsigned_word_abs = usum2, no_signed_word_abs = isum1
  ] "word_abs_options.c"

context word_abs_options begin

lemma "\<lbrace> \<top> \<rbrace> isum1' (a :: sword32) (b :: sword32) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding isum1'_def
  apply (wp refl)
  done

lemma "\<lbrace> \<top> \<rbrace> isum2' (a :: int) (b :: int) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding isum2'_def
  apply (wp refl)
  done

lemma "\<lbrace> \<top> \<rbrace> usum1' (a :: word32) (b :: word32) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding usum1'_def
  apply (wp refl)
  done

lemma "\<lbrace> \<top> \<rbrace> usum2' (a :: nat) (b :: nat) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding usum2'_def
  apply (wp refl)
  done

end

end