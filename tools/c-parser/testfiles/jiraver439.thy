(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver439
  imports "CParser.CTranslation"
begin

external_file "jiraver439.c"
install_C_file "jiraver439.c"

context jiraver439
begin

thm f_body_def
thm g1_body_def
thm g2_body_def
thm h3_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>z :== CALL f();; \<acute>ret__unsigned :== CALL f() \<lbrace> \<acute>ret__unsigned = \<acute>z + 1 \<rbrace>"
apply vcg
apply simp
done

end (* context *)



end
