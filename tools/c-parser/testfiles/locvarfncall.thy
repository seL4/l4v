(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory locvarfncall
imports "CParser.CTranslation"
begin

external_file "locvarfncall.c"
install_C_file "locvarfncall.c"

context "locvarfncall"
begin

thm something_body_def
thm something_else_body_def
thm another_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL something() \<lbrace> \<acute>ret__int = 112 \<rbrace>"
apply vcg
apply simp
done

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL something_else(4)
           \<lbrace> \<acute>ret__int = 50 \<rbrace>"
apply vcg
apply simp
done

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL another(4)
           \<lbrace> \<acute>ret__int = 51 \<rbrace>"
apply vcg
apply simp
done

end

end
