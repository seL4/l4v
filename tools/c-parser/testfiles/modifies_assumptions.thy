(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory modifies_assumptions
imports "../CTranslation"
begin

install_C_file "modifies_assumptions.c"

context modifies_assumptions
begin

thm f_body_def


thm f_modifies (* proved by working with the Spec body *)

(* rest are generated *)
thm g_modifies
thm h_modifies
thm j_modifies
thm k_modifies

lemma "\<Gamma> f_'proc = Some f_body"
apply (simp add: f_impl)
done

end

end
