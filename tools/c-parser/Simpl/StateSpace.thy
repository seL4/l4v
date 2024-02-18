(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de

Copyright (C) 2004-2008 Norbert Schirmer
Copyright (c) 2022 Apple Inc. All rights reserved.

*)

section \<open>State Space Template\<close>
theory StateSpace imports Hoare
begin

record 'g state = "globals"::'g

definition
  upd_globals:: "('g \<Rightarrow> 'g) \<Rightarrow> ('g,'z) state_scheme \<Rightarrow> ('g,'z) state_scheme"
where
  "upd_globals upd s = s\<lparr>globals := upd (globals s)\<rparr>"

named_theorems state_simp

lemma upd_globals_conv [state_simp]: "upd_globals f = (\<lambda>s. s\<lparr>globals := f (globals s)\<rparr>)"
  by (rule ext) (simp add: upd_globals_def)

record ('g, 'l) state_locals = "'g state" +
  locals :: 'l

(*
record ('g, 'n, 'val) stateSP = "'g state" +
  locals :: "'n \<Rightarrow> 'val"
*)

type_synonym ('g, 'n, 'val) stateSP = "('g, 'n \<Rightarrow> 'val) state_locals"
type_synonym ('g, 'n, 'val, 'x) stateSP_scheme = "('g, 'n \<Rightarrow> 'val, 'x) state_locals_scheme"


end
