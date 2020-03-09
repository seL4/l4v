(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory arrays
imports "CParser.CTranslation"
begin

external_file "arrays.c"
install_C_file "arrays.c"

context arrays_global_addresses
begin
  thm f_body_def
  thm f2_body_def
  thm g_body_def
  thm h_body_def
  thm update_body_def
  thm local_body_def
  thm ptr_parameter_body_def
  thm pass_array1_body_def
  thm pass_array2_body_def
end

end
