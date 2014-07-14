(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver224
imports "../CTranslation"
begin

install_C_file "jiraver224.c"

context jiraver224
begin

thm g_body_def
thm h_body_def

end

context jiraver224
begin

thm g_body_def
thm h_body_def

end

end
