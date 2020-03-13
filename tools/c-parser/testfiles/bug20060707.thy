(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bug20060707
imports "CParser.CTranslation"
begin

external_file "bug20060707.c"
install_C_file "bug20060707.c"

  print_locale bug20060707_global_addresses
  thm bug20060707_global_addresses.f_body_def
  thm bug20060707_global_addresses.f_invs_body_def


end
