(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory globinits
imports "CParser.CTranslation"
begin

external_file "globinits.c"
install_C_file "globinits.c"

context globinits
begin

thm sptr_def
thm sval_def
thm svalprime_def
thm array_def
thm a2_def
thm z_def
thm u_def

lemma a2_0: "index a2 0 = B"
apply (simp add: a2_def fcp_beta fupdate_def)
done

term sptr

  thm f_body_def
  thm g_body_def

end (* context *)

end (* theory *)
