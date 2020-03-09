(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_c99block
imports "CParser.CTranslation"
begin

external_file "parse_c99block.c"
install_C_file "parse_c99block.c"

thm parse_c99block_global_addresses.f_body_def

end
