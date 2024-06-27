(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de

Copyright (C) 2006-2008 Norbert Schirmer
*)

theory XVcg
imports Vcg

begin


text \<open>We introduce a syntactic variant of the let-expression so that we can
safely unfold it during verification condition generation. With the new
theorem attribute \<open>vcg_simp\<close> we can declare equalities to be used
by the verification condition generator, while simplifying assertions.
\<close>

syntax
"_Let'" :: "[letbinds, basicblock] => basicblock"  ("(LET (_)/ IN (_))" 23)

translations
  "_Let' (_binds b bs) e"  == "_Let' b (_Let' bs e)"
  "_Let' (_bind x a) e"    == "CONST Let' a (%x. e)"


lemma Let'_unfold [vcg_simp]: "Let' x f = f x"
  by (simp add: Let'_def Let_def)

lemma Let'_split_conv [vcg_simp]:
  "(Let' x  (\<lambda>p. (case_prod (f p) (g p)))) =
   (Let' x  (\<lambda>p. (f p) (fst (g p)) (snd (g p))))"
  by (simp add: split_def)

end
