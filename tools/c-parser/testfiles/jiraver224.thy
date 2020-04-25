(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver224
imports "CParser.CTranslation"
begin

external_file "jiraver224.c"
install_C_file "jiraver224.c"

context jiraver224
begin

thm g_body_def
thm h_body_def

end

context jiraver224
begin

thm g_body_def
thm h_body_def

end

end
