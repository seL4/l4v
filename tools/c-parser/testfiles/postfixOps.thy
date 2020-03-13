(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory postfixOps
imports "CParser.CTranslation"
begin

external_file "postfixOps.c"
install_C_file "postfixOps.c"

context "postfixOps"
begin

thm doit_body_def


end (* context *)


end
