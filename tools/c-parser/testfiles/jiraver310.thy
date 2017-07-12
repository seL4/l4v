(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver310
  imports "../CTranslation"
begin

  install_C_file "jiraver310.c"

  context jiraver310
  begin

    thm f_body_def
    thm g_body_def

    lemma "g_body = X"
    apply (simp add: g_body_def)
    oops

    thm h_body_def

  end (* context *)

end (* theory *)
