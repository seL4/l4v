(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver105
imports "CParser.CTranslation"
begin

external_file "jiraver105.c"
install_C_file "jiraver105.c"

end
