(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_protos
imports "CParser.CTranslation"
begin

external_file "parse_protos.c"
install_C_file "parse_protos.c"

context parse_protos_global_addresses
begin

thm f_body_def
thm g_body_def
thm k_body_def

end

end
