(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory really_simple
imports "CParser.CTranslation"
begin

external_file "really_simple.c"
install_C_file "really_simple.c"

print_locale really_simple_global_addresses
thm really_simple_global_addresses.f_body_def
thm really_simple_global_addresses.f_impl

end
