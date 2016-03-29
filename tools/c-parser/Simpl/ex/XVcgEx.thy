(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      XVcgEx.thy
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

section "Examples for Parallel Assignments"

theory XVcgEx 
imports "../XVcg"

begin

record "globals" =
  "G_'"::"nat"
  "H_'"::"nat"

record 'g vars = "'g state" +
  A_' :: nat
  B_' :: nat
  C_' :: nat
  I_' :: nat
  M_' :: nat
  N_' :: nat
  R_' :: nat
  S_' :: nat
  Arr_' :: "nat list"
  Abr_':: string

term "BASIC
         \<acute>A :== x,
         \<acute>B :== y        
      END"

term "BASIC
         \<acute>G :== \<acute>H,
         \<acute>H :== \<acute>G        
      END"

term "BASIC
        LET (x,y) = (\<acute>A,b);
            z = \<acute>B
        IN \<acute>A :== x,
           \<acute>G :== \<acute>A + y + z
      END"


lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>A = 0\<rbrace> 
      \<lbrace>\<acute>A < 0\<rbrace> \<longmapsto> BASIC
       LET (a,b,c) = foo \<acute>A
       IN 
            \<acute>A :== a,
            \<acute>B :== b,
            \<acute>C :== c
      END
      \<lbrace>\<acute>A = x \<and> \<acute>B = y \<and> \<acute>C = c\<rbrace>"
apply vcg
oops

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>A = 0\<rbrace> 
      \<lbrace>\<acute>A < 0\<rbrace> \<longmapsto> BASIC
       LET (a,b,c) = foo \<acute>A
       IN 
            \<acute>A :== a,
            \<acute>G :== b + \<acute>B,
            \<acute>H :== c
      END
      \<lbrace>\<acute>A = x \<and> \<acute>G = y \<and> \<acute>H = c\<rbrace>"
apply vcg
oops

definition foo:: "nat \<Rightarrow> (nat \<times> nat \<times> nat)"
  where "foo n = (n,n+1,n+2)"

lemma "\<Gamma>\<turnstile> \<lbrace>\<acute>A = 0\<rbrace> 
      \<lbrace>\<acute>A < 0\<rbrace> \<longmapsto> BASIC
       LET (a,b,c) = foo \<acute>A
       IN 
            \<acute>A :== a,
            \<acute>G :== b + \<acute>B,
            \<acute>H :== c
      END
      \<lbrace>\<acute>A = x \<and> \<acute>G = y \<and> \<acute>H = c\<rbrace>"
apply (vcg add: foo_def snd_conv fst_conv)
oops

end
