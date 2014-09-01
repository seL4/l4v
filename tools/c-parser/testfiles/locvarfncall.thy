(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory locvarfncall
imports "../CTranslation"
begin

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
