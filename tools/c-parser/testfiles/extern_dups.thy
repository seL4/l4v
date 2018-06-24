(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory extern_dups
imports "CParser.CTranslation"
begin

external_file "extern_dups.c"
install_C_file "extern_dups.c"

print_locale extern_dups_global_addresses

context extern_dups_global_addresses
begin

thm f_body_def
thm g_body_def
thm index_body_def
thm update_body_def
thm h_body_def

end

end
