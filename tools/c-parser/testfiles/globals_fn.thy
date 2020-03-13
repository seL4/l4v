(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory globals_fn
imports "CParser.CTranslation"
begin

external_file "globals_fn.c"
install_C_file "globals_fn.c"

print_locale globals_fn_global_addresses
thm globals_fn_global_addresses.f_impl
thm globals_fn_global_addresses.gupdate_impl
thm globals_fn_global_addresses.update_impl
thm globals_fn_global_addresses.test1_impl
thm globals_fn_global_addresses.test2_impl
thm globals_fn_global_addresses.test3_impl

context globals_fn_global_addresses
begin
  thm f_body_def
  thm gupdate_body_def
end

lemma (in globals_fn_global_addresses) returns40:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC test2() \<lbrace> \<acute>ret__int = 40 \<rbrace>"
apply vcg
apply unat_arith
done

end
