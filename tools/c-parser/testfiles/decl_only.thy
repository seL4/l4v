(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory decl_only
imports "CParser.CTranslation"
begin

external_file "decl_only.c"
install_C_file "decl_only.c"

print_locale decl_only_global_addresses

end
