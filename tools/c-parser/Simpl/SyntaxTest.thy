(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      SyntaxTest.thy
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
(*<*)
theory SyntaxTest imports HeapList Vcg begin

record "globals" =
 alloc_' :: "ref list"
 free_':: nat
 GA_' :: "ref list list"
 next_' :: "ref \<Rightarrow> ref"
 cont_' :: "ref \<Rightarrow> nat"

record 'g vars = "'g state" +
  A_' :: "nat list"
  AA_' :: "nat list list"
  I_' :: nat
  M_' :: nat
  N_' :: nat
  R_' :: int
  S_' :: int
  B_' :: bool
  Abr_':: string
  p_' :: ref
  q_' :: ref

procedures Foo (p,I|p) = "\<acute>p :== \<acute>p"

term "\<acute>I :==\<^sub>g 3 - 1"
term "\<acute>R :==\<^sub>g 3 - 1"
term "\<acute>I :==\<^sub>g \<acute>A!i"
term " \<acute>A!i :== j"
term " \<acute>AA :== \<acute>AA!![i,j]"
term " \<acute>AA!![i,j] :== \<acute>AA"
term "\<acute>A!i :==\<^sub>g j"
term "\<acute>p :==\<^sub>g \<acute>GA!i!j"
term "\<acute>GA!i!j :==\<^sub>g \<acute>p"
term "\<acute>p :==\<^sub>g \<acute>p \<rightarrow> \<acute>next"
term "\<acute>p \<rightarrow> \<acute>next :==\<^sub>g \<acute>p"
term "\<acute>p \<rightarrow> \<acute>next \<rightarrow> \<acute>next :==\<^sub>g \<acute>p"
term "\<acute>p :== NEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>p\<rightarrow>\<acute>next :==\<^sub>g NEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>p :== NNEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>p\<rightarrow>\<acute>next :==\<^sub>g NNEW sz [\<acute>next :== Null,\<acute>cont :== 0]"
term "\<acute>B :==\<^sub>g \<acute>N + 1 < 0 \<and> \<acute>M + \<acute>N < n"
term "\<acute>B :==\<^sub>g \<acute>N + 1 < 0 \<or>  \<acute>M + \<acute>N < n"
term "\<acute>I :==\<^sub>g \<acute>N mod n"
term "\<acute>I :==\<^sub>g \<acute>N div n"
term "\<acute>R :==\<^sub>g \<acute>R div n"
term "\<acute>R :==\<^sub>g \<acute>R mod n"
term "\<acute>R :==\<^sub>g \<acute>R * n"
term "\<acute>I :==\<^sub>g \<acute>I - \<acute>N"
term "\<acute>R :==\<^sub>g \<acute>R - \<acute>S"
term "\<acute>R :==\<^sub>g int \<acute>I"
term "\<acute>I :==\<^sub>g nat \<acute>R"
term "\<acute>R :==\<^sub>g -\<acute>R"
term "IF\<^sub>g \<acute>A!i < \<acute>N THEN c1 ELSE c2 FI"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N DO c OD"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> DO c OD"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> VAR bar x DO c OD"
term "WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> VAR bar x DO c OD;;c"
term "c;;WHILE\<^sub>g \<acute>A!i < \<acute>N INV \<lbrace>foo\<rbrace> VAR MEASURE \<acute>N + \<acute>M DO c;;c OD;;c"
context Foo_impl
begin
term "\<acute>q :== CALL Foo(\<acute>p,\<acute>M)" 
term "\<acute>q :== CALL\<^sub>g Foo(\<acute>p,\<acute>M + 1)" 
term "\<acute>q :== CALL Foo(\<acute>p\<rightarrow>\<acute>next,\<acute>M)" 
term "\<acute>q \<rightarrow> \<acute>next :== CALL Foo(\<acute>p,\<acute>M)" 
end

end

(*>*) 