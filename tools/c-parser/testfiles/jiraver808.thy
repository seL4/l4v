(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver808
  imports "CParser.CTranslation"
begin

external_file "jiraver808.c"
install_C_file "jiraver808.c"

context jiraver808
begin
thm bar_body_def
end

end
