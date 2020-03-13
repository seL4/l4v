(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver432
  imports "CParser.CTranslation"
begin

external_file "jiraver432.c"
install_C_file "jiraver432.c"

thm AnonStruct1'_size
thm AnonStruct2'_size

context jiraver432
begin
  thm f_body_def
end (* context *)

end

