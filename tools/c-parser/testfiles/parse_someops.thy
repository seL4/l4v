(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_someops
imports "CParser.CTranslation"
begin

external_file "parse_someops.c"
install_C_file "parse_someops.c"

print_locale parse_someops_global_addresses

context parse_someops_global_addresses
begin
thm f_body_def
thm g_body_def
thm condexp_body_def
thm cbools_body_def
thm bitwise_body_def
thm shifts_body_def
thm callbool_body_def
thm ptr_compare_body_def
thm large_literal_rshift_body_def
end

lemma (in parse_someops_global_addresses) foo:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL callbool(1) \<lbrace> \<acute>ret__int = 1 \<rbrace>"
apply vcg
apply simp
done

end
