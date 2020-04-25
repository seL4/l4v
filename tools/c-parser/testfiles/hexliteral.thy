(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory hexliteral
imports "CParser.CTranslation"
begin

external_file "hexliteral.c"
install_C_file "hexliteral.c"

thm hexliteral_global_addresses.f_body_def
thm hexliteral_global_addresses.g_body_def

end
