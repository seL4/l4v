(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory charlit
imports "CParser.CTranslation"
begin

external_file "charlit.c"
install_C_file "charlit.c"

context charlit
begin

  thm f_body_def

end

end
