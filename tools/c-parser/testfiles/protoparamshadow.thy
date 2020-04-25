(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory protoparamshadow
imports "CParser.CTranslation"
begin

external_file "protoparamshadow.c"
install_C_file "protoparamshadow.c"

context protoparamshadow
begin

  thm f_body_def
  thm realone_body_def


end

end
