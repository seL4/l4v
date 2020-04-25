(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory switch_unsigned_signed
imports "CParser.CTranslation"
begin

external_file "switch_unsigned_signed.c"
install_C_file "switch_unsigned_signed.c"

end
