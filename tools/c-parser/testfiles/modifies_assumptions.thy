(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory modifies_assumptions
imports "CParser.CTranslation"
begin

external_file "modifies_assumptions.c"
install_C_file "modifies_assumptions.c" [gamma = \<Gamma>0]

context modifies_assumptions
begin

thm f_body_def


thm f_modifies (* proved by working with the Spec body *)

(* rest are generated *)
thm g_modifies
thm h_modifies
thm j_modifies
thm k_modifies

lemma "\<Gamma>0 f_'proc = Some f_body"
apply (simp add: f_impl)
done

end

end
