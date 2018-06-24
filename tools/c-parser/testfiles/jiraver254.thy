(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver254
imports "CParser.CTranslation"
begin

external_file "jiraver254.c"
install_C_file "jiraver254.c"

context jiraver254
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm ptrconversion_body_def

end

end


