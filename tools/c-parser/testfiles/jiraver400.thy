(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver400
  imports "CParser.CTranslation"
begin

external_file "jiraver400.c"
install_C_file "jiraver400.c" [machinety=bool,roots=[h,indep1]]

context jiraver400
begin

  thm f_body_def
  thm indep1_body_def

end

end
