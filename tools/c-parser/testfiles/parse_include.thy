(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_include
imports "../CTranslation"
begin

new_C_include_dir "includes"

install_C_file "parse_include.c"

thm parse_include_global_addresses.g_body_def
thm parse_include_global_addresses.h_body_def
thm parse_include_global_addresses.included_fn_body_def

end
