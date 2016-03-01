(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      StateSpace.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
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

section {* State Space Template *}
theory StateSpace imports Hoare
begin

record 'g state = "globals"::'g

definition
  upd_globals:: "('g \<Rightarrow> 'g) \<Rightarrow> ('g,'z) state_scheme \<Rightarrow> ('g,'z) state_scheme"
where
  "upd_globals upd s = s\<lparr>globals := upd (globals s)\<rparr>" 

record ('g, 'n, 'val) stateSP = "'g state" +
  locals :: "'n \<Rightarrow> 'val"

lemma upd_globals_conv: "upd_globals f = (\<lambda>s. s\<lparr>globals := f (globals s)\<rparr>)"
  by (rule ext) (simp add: upd_globals_def)

end