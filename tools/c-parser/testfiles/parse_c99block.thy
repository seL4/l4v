(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_c99block
imports "../CTranslation"
begin

install_C_file "parse_c99block.c"

thm parse_c99block_global_addresses.f_body_def

end
