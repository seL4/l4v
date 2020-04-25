(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_retfncall
imports "CParser.CTranslation"
begin

external_file "parse_retfncall.c"
install_C_file "parse_retfncall.c"

print_locale parse_retfncall_global_addresses
thm parse_retfncall_global_addresses.add1_body_def
thm parse_retfncall_global_addresses.add2_body_def

end
