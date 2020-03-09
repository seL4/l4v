(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory void_ptr_init
imports "CParser.CTranslation"
begin

external_file "void_ptr_init.c"
install_C_file "void_ptr_init.c"

end
