(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory simple_fn
imports "CParser.CTranslation"
begin

external_file "simple_fn.c"
install_C_file "simple_fn.c"

print_locale simple_fn_global_addresses

thm simple_fn_global_addresses.fact_body_def
thm simple_fn_global_addresses.fact_impl

end
