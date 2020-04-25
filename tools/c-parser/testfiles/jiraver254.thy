(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver254
imports "CParser.CTranslation"
begin

external_file "jiraver254.c"
install_C_file "jiraver254.c"

context jiraver254
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm ptrconversion_body_def

end

end


