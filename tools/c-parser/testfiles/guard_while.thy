(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory guard_while
imports "CParser.CTranslation"
begin

external_file "guard_while.c"
install_C_file "guard_while.c"

print_locale guard_while_global_addresses
thm guard_while_global_addresses.f_body_def

end
