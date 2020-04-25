(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver429
  imports "CParser.CTranslation"
begin

external_file "jiraver429.c"
  install_C_file "jiraver429.c"

  context jiraver429
  begin

  thm foo_body_def

  end

end
