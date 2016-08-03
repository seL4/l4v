(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver429
  imports "../CTranslation"
begin

  install_C_file "jiraver429.c"

  context jiraver429
  begin

  thm foo_body_def

  end

end
