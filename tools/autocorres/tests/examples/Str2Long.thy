(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Str2Long
imports
  "../../../c-parser/CTranslation"
  "../../AutoCorres"
begin

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
