(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver54
imports "CParser.CTranslation"
begin

external_file "jiraver54.c"
install_C_file "jiraver54.c"

context jiraver54
begin

thm f_body_def
thm f_modifies

end (* context *)


end
