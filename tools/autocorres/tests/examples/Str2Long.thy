(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Str2Long
imports
  "CParser.CTranslation"
  "AutoCorres.AutoCorres"
begin

external_file "str2long.c"
install_C_file "str2long.c"
autocorres "str2long.c"

context str2long begin

(* When passed a finite string, str2long never fails *)
lemma "\<lbrace> \<lambda>s. True \<rbrace>
        str2long' str
      \<lbrace>\<lambda>_ _. True\<rbrace>!"
  unfolding str2long'_def
  apply (wp)
  (* Need whileLoopE_add_inv and friends *)
  oops

end
end
