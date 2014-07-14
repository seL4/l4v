(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory selection_sort
imports "../CTranslation"
begin

install_C_file "selection_sort.c"

print_locale selection_sort_global_addresses
thm selection_sort_global_addresses.len_body_def
thm selection_sort_global_addresses.lmin_body_def
thm selection_sort_global_addresses.ssort_body_def

end
