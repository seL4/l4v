(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory sizeof_typedef
imports "CParser.CTranslation"
begin

external_file "sizeof_typedef.c"
install_C_file "sizeof_typedef.c"

thm sizeof_typedef_global_addresses.f_body_def

end
