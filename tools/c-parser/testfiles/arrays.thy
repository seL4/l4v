(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
