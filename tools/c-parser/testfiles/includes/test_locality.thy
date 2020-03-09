(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory test_locality
imports "CParser.CTranslation"
begin

external_file "test_include2.h"
install_C_file "test_include2.h"

end;
