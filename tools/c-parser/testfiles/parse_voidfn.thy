(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_voidfn
imports "CParser.CTranslation"
begin

external_file "parse_voidfn.c"
install_C_file "parse_voidfn.c"

print_locale parse_voidfn_global_addresses
thm parse_voidfn_global_addresses.f_body_def
thm parse_voidfn_global_addresses.g_body_def

end
