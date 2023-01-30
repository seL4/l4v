(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory word_abs_options imports "AutoCorres.AutoCorres" begin

external_file "word_abs_options.c"
install_C_file "word_abs_options.c"

autocorres [
  ts_rules = nondet,
  unsigned_word_abs = usum2, no_signed_word_abs = isum1
  ] "word_abs_options.c"

context word_abs_options begin

lemma "\<lbrace> \<top> \<rbrace> isum1' (a :: sword32) (b :: sword32) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding isum1'_def
  apply (wp refl impI)
  done

lemma "\<lbrace> \<top> \<rbrace> isum2' (a :: int) (b :: int) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding isum2'_def
  apply (wp refl impI)
  done

lemma "\<lbrace> \<top> \<rbrace> usum1' (a :: word32) (b :: word32) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding usum1'_def
  apply (wp refl impI)
  done

lemma "\<lbrace> \<top> \<rbrace> usum2' (a :: nat) (b :: nat) \<lbrace> \<lambda>r _. r = a + b \<rbrace>"
  unfolding usum2'_def
  apply (wp refl impI)
  done

end

end
