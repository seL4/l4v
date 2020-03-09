(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver473
  imports "CParser.CTranslation"
begin

declare [[munge_info_fname="jiraver473.minfo"]]

external_file "jiraver473.c"
install_C_file "jiraver473.c"

end
