(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ummbug20100217
imports "CParser.CTranslation"
begin

external_file "ummbug20100217.c"
install_C_file "ummbug20100217.c"

print_locale ummbug20100217_global_addresses

context ummbug20100217_global_addresses
begin

thm g_body_def
thm h_body_def
thm j_body_def

end

end
