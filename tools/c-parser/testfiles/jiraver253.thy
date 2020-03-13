(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver253
imports "CParser.CTranslation"
begin

external_file "jiraver253.c"
install_C_file "jiraver253.c"

context jiraver253
begin

thm f_body_def
thm g_body_def

end

end
