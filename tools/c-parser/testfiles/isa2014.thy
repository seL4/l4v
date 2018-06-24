(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
