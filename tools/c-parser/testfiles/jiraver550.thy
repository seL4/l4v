(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory jiraver550
imports
  "CParser.CTranslation"
begin

external_file "jiraver550.c"
install_C_file "jiraver550.c"


end
