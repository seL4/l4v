(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_addr
imports "CParser.CTranslation"
begin

external_file "parse_addr.c"
install_C_file "parse_addr.c"

context parse_addr_global_addresses
begin
thm f_body_def
thm f2_body_def
thm g_body_def
thm h_body_def
term c_'
end

end
