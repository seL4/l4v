(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ptr_diff
imports "CParser.CTranslation"
begin

external_file "ptr_diff.c"
install_C_file "ptr_diff.c"

  context ptr_diff
  begin

  thm pdiff1_body_def
  thm pdiff2_body_def
  thm pdiff3_body_def[simplified, unfolded ptr_add_def', simplified]


  end

end
