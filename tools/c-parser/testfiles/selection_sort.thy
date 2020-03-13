(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory selection_sort
imports "CParser.CTranslation"
begin

external_file "selection_sort.c"
install_C_file "selection_sort.c"

print_locale selection_sort_global_addresses
thm selection_sort_global_addresses.len_body_def
thm selection_sort_global_addresses.lmin_body_def
thm selection_sort_global_addresses.ssort_body_def

end
