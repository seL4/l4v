(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver426
  imports "CParser.CTranslation"
begin

external_file "jiraver426.c"
install_C_file "jiraver426.c"

context jiraver426
begin

thm f_body_def
thm myexit_body_def

end (* context *)

end

