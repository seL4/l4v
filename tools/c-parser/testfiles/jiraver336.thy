(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver336
  imports "CParser.CTranslation"
begin

external_file "jiraver336.c"
install_C_file "jiraver336.c"

context jiraver336
begin

 thm f_body_def

end

end
