(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_sizeof
imports "CParser.CTranslation"
begin

external_file "parse_sizeof.c"
install_C_file "parse_sizeof.c"

print_locale parse_sizeof_global_addresses
context parse_sizeof_global_addresses
begin
thm f_body_def
(* notice how repulsive the above is *)
thm g_body_def
end

end
