(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory array_of_ptr
imports "CParser.CTranslation"
begin

external_file "array_of_ptr.c"
install_C_file "array_of_ptr.c"

print_locale array_of_ptr_global_addresses

end
