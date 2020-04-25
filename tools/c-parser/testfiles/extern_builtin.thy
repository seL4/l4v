(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory extern_builtin
  imports "CParser.CTranslation"
begin

declare [[allow_underscore_idents=true]]

external_file "extern_builtin.c"
install_C_file "extern_builtin.c"

end
