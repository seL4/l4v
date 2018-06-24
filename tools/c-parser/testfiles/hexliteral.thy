(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory hexliteral
imports "CParser.CTranslation"
begin

external_file "hexliteral.c"
install_C_file "hexliteral.c"

thm hexliteral_global_addresses.f_body_def
thm hexliteral_global_addresses.g_body_def

end
