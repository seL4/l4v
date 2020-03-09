(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory volatile_asm
imports "CParser.CTranslation"
begin

external_file "volatile_asm.c"
install_C_file "volatile_asm.c"

end
