(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      XVcg.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2006-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

theory XVcg 
imports Vcg

begin


text {* We introduce a syntactic variant of the let-expression so that we can
safely unfold it during verification condition generation. With the new
theorem attribute @{text "vcg_simp"} we can declare equalities to be used
by the verification condition generator, while simplifying assertions.
*}

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