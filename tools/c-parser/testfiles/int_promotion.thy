(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
