(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver039
imports "CParser.CTranslation"
begin

external_file "jiraver039.c"
install_C_file "jiraver039.c"

context jiraver039
begin

thm f_body_def

end

end (* theory *)
