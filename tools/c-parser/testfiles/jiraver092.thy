(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver092
imports "CParser.CTranslation"
begin

external_file "jiraver092.c"
install_C_file "jiraver092.c"

context jiraver092
begin

thm test_body_def

end

end
