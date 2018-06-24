(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory int_promotion
imports "CParser.CTranslation"
begin

external_file "int_promotion.c"
install_C_file "int_promotion.c"

  context int_promotion
  begin

  thm f_body_def

  lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL f() \<lbrace> \<acute>ret__int = 1 \<rbrace>"
    apply vcg
    apply simp
    done
  end

end
