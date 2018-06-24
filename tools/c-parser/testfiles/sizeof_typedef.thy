(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory sizeof_typedef
imports "CParser.CTranslation"
begin

external_file "sizeof_typedef.c"
install_C_file "sizeof_typedef.c"

thm sizeof_typedef_global_addresses.f_body_def

end
