(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver307
  imports "../CTranslation"
begin

install_C_file "jira ver307.c"

context "jira ver307"
begin

thm f_body_def

end

end
