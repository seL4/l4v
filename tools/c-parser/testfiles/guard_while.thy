(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory guard_while
imports "CParser.CTranslation"
begin

external_file "guard_while.c"
install_C_file "guard_while.c"

print_locale guard_while_global_addresses
thm guard_while_global_addresses.f_body_def

end
