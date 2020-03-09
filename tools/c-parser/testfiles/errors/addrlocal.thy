(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory addrlocal
imports "CParser.CTranslation"
begin

external_file "addrlocal.c";
install_C_file "addrlocal.c";

end
