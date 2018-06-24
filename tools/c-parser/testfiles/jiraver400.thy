(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver400
  imports "CParser.CTranslation"
begin

external_file "jiraver400.c"
install_C_file "jiraver400.c" [machinety=bool,roots=[h,indep1]]

context jiraver400
begin

  thm f_body_def
  thm indep1_body_def

end

end
