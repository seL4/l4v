(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory isa2014
  imports "CParser.CTranslation"
begin

external_file "isa2014.c"
install_C_file "isa2014.c"

print_locale isa2014_global_addresses

context isa2014
begin

  thm f_body_def
  thm ff_body_def

end (* context *)

end
