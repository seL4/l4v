(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_include
imports "CParser.CTranslation"
begin

external_file "includes/test_include2.h"
external_file "parse_include.c"

new_C_include_dir "includes"

install_C_file "parse_include.c"

thm parse_include_global_addresses.g_body_def
thm parse_include_global_addresses.h_body_def
thm parse_include_global_addresses.included_fn_body_def

end
