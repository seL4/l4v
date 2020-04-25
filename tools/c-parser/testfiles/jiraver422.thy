(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver422
  imports "CParser.CTranslation"
begin

external_file "jiraver422.c"
install_C_file "jiraver422.c"

context jiraver422
begin

  thm qux_body_def

end

end
