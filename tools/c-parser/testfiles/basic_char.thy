(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory basic_char
imports "CParser.CTranslation"
begin

external_file "basic_char.c"
install_C_file "basic_char.c"

context basic_char
begin

  thm f_body_def
  thm g_body_def

end

end
