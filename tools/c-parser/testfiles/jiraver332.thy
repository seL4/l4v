(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver332
  imports "CParser.CTranslation"
begin

external_file "jiraver332.c"
install_C_file "jiraver332.c"

context jiraver332
begin

  thm f_body_def

end

end
