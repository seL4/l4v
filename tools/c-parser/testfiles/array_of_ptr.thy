(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory array_of_ptr
imports "CParser.CTranslation"
begin

external_file "array_of_ptr.c"
install_C_file "array_of_ptr.c"

print_locale array_of_ptr_global_addresses

end
