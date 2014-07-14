(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory builtins
imports "../CTranslation"
begin

install_C_file "builtins.c"

context builtins
begin

thm f_body_def
thm g_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> \<acute>i = 3 \<rbrace> Call f_'proc \<lbrace> \<acute>ret__int = 6 \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>ret__int = 6 \<rbrace>"])
  apply (hoare_rule HoarePartial.Seq [where R="{}"])
    apply (hoare_rule HoarePartial.Cond [where P\<^sub>1="{}" and P\<^sub>2="\<lbrace>\<acute>i=3\<rbrace>"])
        apply (simp add: subset_eq word_sless_def word_sle_def)
      apply (hoare_rule HoarePartial.conseq_exploit_pre)
      apply simp
    apply vcg
    apply simp
  apply vcg
apply vcg
done

(* NOTE:

  apply vcg

at the outset generates three sub-goals, last of which is not provable
*)

end
end
