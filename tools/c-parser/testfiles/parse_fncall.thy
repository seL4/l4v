(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_fncall
imports "CParser.CTranslation"
begin

external_file "parse_fncall.c"
install_C_file "parse_fncall.c"

print_locale parse_fncall_global_addresses
thm parse_fncall_global_addresses.f_body_def
thm parse_fncall_global_addresses.g_body_def
thm parse_fncall_global_addresses.h_body_def
thm parse_fncall_global_addresses.i_body_def
thm parse_fncall_global_addresses.j_body_def
thm parse_fncall_global_addresses.k_body_def

end
