(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver307
  imports "CParser.CTranslation"
begin

external_file "jira ver307.c"
install_C_file "jira ver307.c"

context "jira ver307"
begin

thm f_body_def

end

end
