(*
 * @TAG(OTHER_LGPL)
 *)

(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Generalise.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2005-2008 Norbert Schirmer 
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

theory Generalise imports "~~/src/HOL/Statespace/DistinctTreeProver"
begin

lemma protectRefl: "PROP prop (PROP C) \<Longrightarrow> PROP prop (PROP C)"
  by (simp add: prop_def)

lemma protectImp: 
 assumes i: "PROP prop (PROP P \<Longrightarrow> PROP Q)" 
 shows "PROP prop (PROP prop P \<Longrightarrow> PROP prop Q)"
proof -
  {
    assume P: "PROP prop P"
    from i [unfolded prop_def, OF P [unfolded prop_def]] 
    have "PROP prop Q"
      by (simp add: prop_def)
  }
  note i' = this
  show "PROP ?thesis" 
    apply (rule protectI)
    apply (rule i')
    apply assumption
    done
qed


lemma generaliseConj: 
  assumes i1: "PROP prop (PROP prop (Trueprop P) \<Longrightarrow> PROP prop (Trueprop Q))"
  assumes i2: "PROP prop (PROP prop (Trueprop P') \<Longrightarrow> PROP prop (Trueprop Q'))"
  shows "PROP prop (PROP prop (Trueprop (P \<and> P')) \<Longrightarrow> (PROP prop (Trueprop (Q \<and> Q'))))"
  using i1 i2
  by (auto simp add: prop_def)

lemma generaliseAll: 
 assumes i: "PROP prop (\<And>s. PROP prop (Trueprop (P s)) \<Longrightarrow> PROP prop (Trueprop (Q s)))" 
 shows "PROP prop (PROP prop (Trueprop (\<forall>s. P s)) \<Longrightarrow> PROP prop (Trueprop (\<forall>s. Q s)))"
  using i
  by (auto simp add: prop_def)

lemma generalise_all: 
 assumes i: "PROP prop (\<And>s. PROP prop (PROP P s) \<Longrightarrow> PROP prop (PROP Q s))" 
 shows "PROP prop ((PROP prop (\<And>s. PROP P s)) \<Longrightarrow> (PROP prop (\<And>s. PROP Q s)))"
  using i
  proof (unfold prop_def)
    assume i1: "\<And>s. (PROP P s) \<Longrightarrow> (PROP Q s)"
    assume i2: "\<And>s. PROP P s"
    show "\<And>s. PROP Q s"
      by (rule i1) (rule i2)
  qed

lemma generaliseTrans: 
  assumes i1: "PROP prop (PROP P \<Longrightarrow> PROP Q)"
  assumes i2: "PROP prop (PROP Q \<Longrightarrow> PROP R)" 
  shows "PROP prop (PROP P \<Longrightarrow> PROP R)"
  using i1 i2
  proof (unfold prop_def)
    assume P_Q: "PROP P \<Longrightarrow> PROP Q" 
    assume Q_R: "PROP Q \<Longrightarrow> PROP R" 
    assume P: "PROP P"
    show "PROP R"
      by (rule Q_R [OF P_Q [OF P]])
  qed

lemma meta_spec:
  assumes "\<And>x. PROP P x"
  shows "PROP P x" by fact

lemma meta_spec_protect:
  assumes g: "\<And>x. PROP P x"
  shows "PROP prop (PROP P x)"
using g
by (auto simp add: prop_def)

lemma generaliseImp: 
  assumes i: "PROP prop (PROP prop (Trueprop P) \<Longrightarrow> PROP prop (Trueprop Q))"
  shows "PROP prop (PROP prop (Trueprop (X \<longrightarrow> P)) \<Longrightarrow> PROP prop (Trueprop (X \<longrightarrow> Q)))"
  using i
  by (auto simp add: prop_def)

lemma generaliseEx: 
 assumes i: "PROP prop (\<And>s. PROP prop (Trueprop (P s)) \<Longrightarrow> PROP prop (Trueprop (Q s)))" 
 shows "PROP prop (PROP prop (Trueprop (\<exists>s. P s)) \<Longrightarrow> PROP prop (Trueprop (\<exists>s. Q s)))"
  using i
  by (auto simp add: prop_def)


lemma generaliseRefl: "PROP prop (PROP prop (Trueprop P) \<Longrightarrow> PROP prop (Trueprop P))"
  by (auto simp add: prop_def)

lemma generaliseRefl': "PROP prop (PROP P \<Longrightarrow> PROP P)"
  by (auto simp add: prop_def)

lemma generaliseAllShift:
  assumes i: "PROP prop (\<And>s. P \<Longrightarrow> Q s)"
  shows "PROP prop (PROP prop (Trueprop P) \<Longrightarrow> PROP prop (Trueprop (\<forall>s. Q s)))"
  using i
  by (auto simp add: prop_def)

lemma generalise_allShift:
  assumes i: "PROP prop (\<And>s. PROP P \<Longrightarrow> PROP Q s)"
  shows "PROP prop (PROP prop (PROP P) \<Longrightarrow> PROP prop (\<And>s. PROP Q s))"
  using i
  proof (unfold prop_def)
    assume P_Q: "\<And>s. PROP P \<Longrightarrow> PROP Q s" 
    assume P: "PROP P"
    show "\<And>s. PROP Q s"
      by (rule P_Q [OF P])
  qed


lemma generaliseImpl:
  assumes i: "PROP prop (PROP prop P \<Longrightarrow> PROP prop Q)"
  shows "PROP prop ((PROP prop (PROP X \<Longrightarrow> PROP P)) \<Longrightarrow> (PROP prop (PROP X \<Longrightarrow> PROP Q)))"
  using i
  proof (unfold prop_def)
    assume i1: "PROP P \<Longrightarrow> PROP Q"
    assume i2: "PROP X \<Longrightarrow> PROP P"
    assume X: "PROP X"
    show "PROP Q"
      by (rule i1 [OF i2 [OF X]])
  qed


ML_file "generalise_state.ML"

end

