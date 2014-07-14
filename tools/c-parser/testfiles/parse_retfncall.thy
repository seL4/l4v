(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_retfncall
imports "../CTranslation"
begin

install_C_file "parse_retfncall.c"

print_locale parse_retfncall_global_addresses
thm parse_retfncall_global_addresses.add1_body_def
thm parse_retfncall_global_addresses.add2_body_def

end
