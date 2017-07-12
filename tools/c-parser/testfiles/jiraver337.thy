(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver337
  imports "../CTranslation"
begin


  declare [[cpp_path=""]]
  install_C_file "jiraver337.c"

  context jiraver337
  begin
    thm f_body_def
  end (* context *)

end
