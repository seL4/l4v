(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bigstruct
imports "CParser.CTranslation"
begin

external_file "bigstruct.c"
install_C_file "bigstruct.c"

end
