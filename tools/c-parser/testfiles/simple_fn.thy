(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory simple_fn
imports "CParser.CTranslation"
begin

external_file "simple_fn.c"
install_C_file "simple_fn.c"

print_locale simple_fn_global_addresses

thm simple_fn_global_addresses.fact_body_def
thm simple_fn_global_addresses.fact_impl

end
