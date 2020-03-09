(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory inner_fncalls
imports "CParser.CTranslation"
begin

external_file "inner_fncalls.c"
install_C_file "inner_fncalls.c"

print_locale inner_fncalls_global_addresses

context inner_fncalls_global_addresses
begin
thm f_body_def
thm e_body_def
thm f2_body_def
thm g_body_def
thm function_body_def
thm function2_body_def
end

end
