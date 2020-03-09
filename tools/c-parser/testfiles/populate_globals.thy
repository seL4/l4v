(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory populate_globals
imports "CParser.CTranslation"
begin

external_file "globsall_addressed.c"

declare [[globals_all_addressed=true,populate_globals=true]]
install_C_file "globsall_addressed.c"

context globsall_addressed
begin
  thm f_body_def

  term wannabe_constant
  thm wannabe_constant_def

  term glob1_'
end

end
