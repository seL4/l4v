(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory simple_constexpr_sizeof
imports "../CTranslation"
begin

install_C_file "simple_constexpr_sizeof.c"

thm simple_constexpr_sizeof_global_addresses.f_body_def


end
