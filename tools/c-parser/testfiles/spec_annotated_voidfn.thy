(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory spec_annotated_voidfn
imports "CParser.CTranslation"
begin

external_file "spec_annotated_voidfn.c"
install_C_file "spec_annotated_voidfn.c"

thm spec_annotated_voidfn_global_addresses.f_impl
print_locale f_spec
thm f_spec_def

end
