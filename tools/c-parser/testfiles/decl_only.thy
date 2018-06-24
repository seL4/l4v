(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory decl_only
imports "CParser.CTranslation"
begin

external_file "decl_only.c"
install_C_file "decl_only.c"

print_locale decl_only_global_addresses

end
