(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter "Prettier Printing for Programs"

theory PrettyProgs
imports "Simpl/Vcg"
begin

syntax (output)
  "_Assign"      :: "'b => 'b => ('a,'p,'f) com"    ("(2_ :==/ _)" [30, 30] 23)

  "_seq"::"('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" ("_;;//_" [20, 21] 20)

  "_While_inv"   :: "'a bexp => 'a assn => bdy => ('a,'p,'f) com"
        ("(0WHILE (_)//INV (_)//_)"  [25, 0, 81] 71)

  "_Do" :: "('a,'p,'f) com \<Rightarrow> bdy" ("DO//  (_)//OD" [0] 1000)

  "_Cond"        :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF _ THEN//  (_)//ELSE//  (_)//FI)" [0, 0, 0] 71)
  "_Cond_no_else":: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF _ THEN//  (_)//FI)" [0, 0] 71)

  "_Try_Catch":: "('a,'p,'f) com \<Rightarrow>('a,'p,'f) com \<Rightarrow> ('a,'p,'f) com"
        ("(0TRY//  (_)//CATCH _//END)"  [0,0] 71)

end
