(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver384
  imports "CParser.CTranslation"
begin

  external_file "jiraver384.c"
  install_C_file "jiraver384.c"

  context jiraver384
  begin
  thm foo_body_def
  end

end
