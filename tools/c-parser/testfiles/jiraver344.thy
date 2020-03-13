(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver344
  imports "CParser.CTranslation"
begin

external_file "jiraver344.c"

declare [[allow_underscore_idents=true]]
install_C_file "jiraver344.c"

end
