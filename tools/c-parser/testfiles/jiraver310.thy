(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver310
  imports "CParser.CTranslation"
begin

external_file "jiraver310.c"
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
