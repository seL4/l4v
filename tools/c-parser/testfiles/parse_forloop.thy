(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_forloop
imports "CParser.CTranslation"
begin

external_file "parse_forloop.c"
install_C_file "parse_forloop.c"

print_locale parse_forloop_global_addresses
thm parse_forloop_global_addresses.f_body_def
thm parse_forloop_global_addresses.g_body_def
thm parse_forloop_global_addresses.h_body_def

end
