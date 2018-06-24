(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
