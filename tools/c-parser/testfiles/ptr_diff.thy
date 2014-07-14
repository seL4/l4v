(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ptr_diff
imports "../CTranslation"
begin

install_C_file "ptr_diff.c"

  context ptr_diff
  begin

  thm pdiff1_body_def
  thm pdiff2_body_def
  thm pdiff3_body_def[simplified, unfolded ptr_add_def', simplified]


  end

end
