(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory varinit
imports "CParser.CTranslation"
begin

external_file "varinit.c"
install_C_file "varinit.c"

context varinit begin
thm f_body_def
end

end
