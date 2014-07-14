(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory really_simple
imports "../CTranslation"
begin

install_C_file "really_simple.c"

print_locale really_simple_global_addresses
thm really_simple_global_addresses.f_body_def
thm really_simple_global_addresses.f_impl

end
