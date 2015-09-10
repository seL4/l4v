theory jiraver439
  imports "../CTranslation"
begin

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
