(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory globals_in_record
imports
  "CParser.CTranslation"
begin

external_file "globals_in_record.c"
install_C_file "globals_in_record.c"

context globals_in_record begin

thm globals.equality

find_theorems "zuzu_'"
thm globals.zuzu_'_def

find_theorems "zozo"

find_theorems "zyzy"
thm zyzy_def

end

end
