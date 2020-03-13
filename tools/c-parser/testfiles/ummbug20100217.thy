(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ummbug20100217
imports "CParser.CTranslation"
begin

external_file "ummbug20100217.c"
install_C_file "ummbug20100217.c"

print_locale ummbug20100217_global_addresses

context ummbug20100217_global_addresses
begin

thm g_body_def
thm h_body_def
thm j_body_def

end

end
