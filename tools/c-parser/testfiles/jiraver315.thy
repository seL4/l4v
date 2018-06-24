(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver315
  imports "CParser.CTranslation"
begin

external_file "jiraver315.c"
install_C_file "jiraver315.c"

context jiraver315
begin

thm f_body_def

end

end
