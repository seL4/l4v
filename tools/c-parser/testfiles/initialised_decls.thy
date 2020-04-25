(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory initialised_decls
imports "CParser.CTranslation"
begin

external_file "initialised_decls.c"
install_C_file "initialised_decls.c"

context initialised_decls_global_addresses
begin
thm f_body_def
thm g_body_def
end

text \<open>
  Following proof confirms that we can prove stuff about g without needing
  to prove that f is side-effect free; which ain't true.  The translation
  doesn't incorrectly reckon that the initialisation of local variable i
  is an "embedded" function call.

  This proof still works, but there aren't side-effect-free guards inserted
  at any point in the current translation so the point is a bit moot.
\<close>

lemma (in initialised_decls_global_addresses) foo:
shows  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC g() \<lbrace> \<acute>ret__int = 3 \<rbrace>"
apply vcg
done

end
