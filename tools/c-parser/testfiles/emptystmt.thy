(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory emptystmt
imports "CParser.CTranslation"
begin

external_file "emptystmt.c"
install_C_file "emptystmt.c"

context emptystmt
begin
  thm f_body_def
  thm f_modifies
end

end
