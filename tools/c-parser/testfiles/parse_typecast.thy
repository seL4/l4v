(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_typecast
imports "CParser.CTranslation"
begin

external_file "parse_typecast.c"
install_C_file "parse_typecast.c"

print_locale parse_typecast_global_addresses
thm parse_typecast_global_addresses.main_body_def

end
