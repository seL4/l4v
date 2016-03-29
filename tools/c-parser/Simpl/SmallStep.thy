(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      SmallStep.thy
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

section {* Small-Step Semantics and Infinite Computations*}

theory SmallStep imports Termination
begin

text {* The redex of a statement is the substatement, which is actually altered
by the next step in the small-step semantics.
*}

primrec redex:: "('s,'p,'f)com \<Rightarrow> ('s,'p,'f)com"
where
"redex Skip = Skip" |
"redex (Basic f) = (Basic f)" |
"redex (Spec r) = (Spec r)" |
"redex (Seq c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (Cond b c\<^sub>1 c\<^sub>2) = (Cond b c\<^sub>1 c\<^sub>2)" |
"redex (While b c) = (While b c)" |
"redex (Call p) = (Call p)" |
"redex (DynCom d) = (DynCom d)" |
"redex (Guard f b c) = (Guard f b c)" |
"redex (Throw) = Throw" |
"redex (Catch c\<^sub>1 c\<^sub>2) = redex c\<^sub>1"


subsection {*Small-Step Computation: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow> (c', s')"}*}

type_synonym ('s,'p,'f) config = "('s,'p,'f)com  \<times> ('s,'f) xstate"
inductive "step"::"[('s,'p,'f) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>/ _)" [81,81,81] 100)
  for \<Gamma>::"('s,'p,'f) body"
where

  Basic: "\<Gamma>\<turnstile>(Basic f,Normal s) \<rightarrow> (Skip,Normal (f s))"

| Spec: "(s,t) \<in> r \<Longrightarrow> \<Gamma>\<turnstile>(Spec r,Normal s) \<rightarrow> (Skip,Normal t)"
| SpecStuck: "\<forall>t. (s,t) \<notin> r \<Longrightarrow> \<Gamma>\<turnstile>(Spec r,Normal s) \<rightarrow> (Skip,Stuck)"

| Guard: "s\<in>g \<Longrightarrow> \<Gamma>\<turnstile>(Guard f g c,Normal s) \<rightarrow> (c,Normal s)"
  
| GuardFault: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>(Guard f g c,Normal s) \<rightarrow> (Skip,Fault f)"


| Seq: "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')
        \<Longrightarrow> 
        \<Gamma>\<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1' c\<^sub>2, s')"
| SeqSkip: "\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,s) \<rightarrow> (c\<^sub>2, s)"
| SeqThrow: "\<Gamma>\<turnstile>(Seq Throw c\<^sub>2,Normal s) \<rightarrow> (Throw, Normal s)"

| CondTrue:  "s\<in>b \<Longrightarrow> \<Gamma>\<turnstile>(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>1,Normal s)"
| CondFalse: "s\<notin>b \<Longrightarrow> \<Gamma>\<turnstile>(Cond b c\<^sub>1 c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"

| WhileTrue: "\<lbrakk>s\<in>b\<rbrakk> 
              \<Longrightarrow> 
              \<Gamma>\<turnstile>(While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"

| WhileFalse: "\<lbrakk>s\<notin>b\<rbrakk> 
               \<Longrightarrow> 
               \<Gamma>\<turnstile>(While b c,Normal s) \<rightarrow> (Skip,Normal s)"

| Call: "\<Gamma> p=Some bdy \<Longrightarrow>
         \<Gamma>\<turnstile>(Call p,Normal s) \<rightarrow> (bdy,Normal s)"

| CallUndefined: "\<Gamma> p=None \<Longrightarrow>
         \<Gamma>\<turnstile>(Call p,Normal s) \<rightarrow> (Skip,Stuck)"

| DynCom: "\<Gamma>\<turnstile>(DynCom c,Normal s) \<rightarrow> (c s,Normal s)"

| Catch: "\<lbrakk>\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow>
          \<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1' c\<^sub>2,s')"

| CatchThrow: "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
| CatchSkip: "\<Gamma>\<turnstile>(Catch Skip c\<^sub>2,s) \<rightarrow> (Skip,s)"

| FaultProp:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>(c,Fault f) \<rightarrow> (Skip,Fault f)"
| StuckProp:  "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>(c,Stuck) \<rightarrow> (Skip,Stuck)"
| AbruptProp: "\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>(c,Abrupt f) \<rightarrow> (Skip,Abrupt f)"


lemmas step_induct = step.induct [of _ "(c,s)" "(c',s')", split_format (complete), case_names
Basic Spec SpecStuck Guard GuardFault Seq SeqSkip SeqThrow CondTrue CondFalse
WhileTrue WhileFalse Call CallUndefined DynCom Catch CatchThrow CatchSkip
FaultProp StuckProp AbruptProp, induct set]


inductive_cases step_elim_cases [cases set]:
 "\<Gamma>\<turnstile>(Skip,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Guard f g c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Basic f,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Spec r,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Seq c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Cond b c1 c2,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(While b c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Call p,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(DynCom c,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Throw,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Catch c1 c2,s) \<rightarrow> u"

inductive_cases step_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>(Skip,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Guard f g c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Basic f,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Spec r,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Seq c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Cond b c1 c2,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(While b c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Call p,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(DynCom c,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Throw,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Catch c1 c2,Normal s) \<rightarrow> u"


text {* The final configuration is either of the form @{text "(Skip,_)"} for normal
termination, or @{term "(Throw,Normal s)"} in case the program was started in 
a @{term "Normal"} state and terminated abruptly. The @{const "Abrupt"} state is not used to
model abrupt termination, in contrast to the big-step semantics. Only if the
program starts in an @{const "Abrupt"} states it ends in the same @{term "Abrupt"}
state.*}

definition final:: "('s,'p,'f) config \<Rightarrow> bool" where
"final cfg = (fst cfg=Skip \<or> (fst cfg=Throw \<and> (\<exists>s. snd cfg=Normal s)))"


abbreviation 
 "step_rtrancl" :: "[('s,'p,'f) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
 where
  "\<Gamma>\<turnstile>cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST step \<Gamma>)\<^sup>*\<^sup>* cf0 cf1"
abbreviation 
 "step_trancl" :: "[('s,'p,'f) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>\<^sup>+/ _)" [81,81,81] 100)
 where
  "\<Gamma>\<turnstile>cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> (CONST step \<Gamma>)\<^sup>+\<^sup>+ cf0 cf1"








(* ************************************************************************ *)
subsection {* Structural Properties of Small Step Computations *}
(* ************************************************************************ *)

lemma redex_not_Seq: "redex c = Seq c1 c2 \<Longrightarrow> P"
  apply (induct c)
  apply auto
  done

lemma no_step_final: 
  assumes step: "\<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s')"
  shows "final (c,s) \<Longrightarrow> P"
using step
by induct (auto simp add: final_def)

lemma no_step_final':
  assumes step: "\<Gamma>\<turnstile>cfg \<rightarrow> cfg'"
  shows "final cfg \<Longrightarrow> P"
using step
  by (cases cfg, cases cfg') (auto intro: no_step_final)

lemma step_Abrupt: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>x. s=Abrupt x \<Longrightarrow> s'=Abrupt x"
using step
by (induct) auto

lemma step_Fault: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step
by (induct) auto

lemma step_Stuck: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma SeqSteps: 
  assumes steps: "\<Gamma>\<turnstile>cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<Gamma>\<turnstile> cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<Gamma>\<turnstile> cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have "\<Gamma>\<turnstile> (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1'' c\<^sub>2,s'')"
    by (rule step.Seq)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma>\<turnstile> (Seq c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .
qed


lemma CatchSteps: 
  assumes steps: "\<Gamma>\<turnstile>cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s); cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<Gamma>\<turnstile> cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<Gamma>\<turnstile> cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg'' 
  have s: "\<Gamma>\<turnstile> (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Catch c\<^sub>1'' c\<^sub>2,s'')"
    by (rule step.Catch)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<Gamma>\<turnstile> (Catch c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Catch c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .      
qed

lemma steps_Fault: "\<Gamma>\<turnstile> (c, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile> (c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma>\<turnstile> (Seq Skip c\<^sub>2, Fault f) \<rightarrow> (c\<^sub>2, Fault f)" by (rule SeqSkip)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Fault f) \<rightarrow>\<^sup>* (Skip, Fault f)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Fault f) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Fault f)".
  also
  have "\<Gamma>\<turnstile> (Catch Skip c\<^sub>2, Fault f) \<rightarrow> (Skip, Fault f)" by (rule CatchSkip) 
  finally show ?case by simp
qed (fastforce intro: step.intros)+

lemma steps_Stuck: "\<Gamma>\<turnstile> (c, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile> (c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Stuck)".
  also
  have "\<Gamma>\<turnstile> (Seq Skip c\<^sub>2, Stuck) \<rightarrow> (c\<^sub>2, Stuck)" by (rule SeqSkip)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Stuck) \<rightarrow>\<^sup>* (Skip, Stuck)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Stuck)" .
  also
  have "\<Gamma>\<turnstile> (Catch Skip c\<^sub>2, Stuck) \<rightarrow> (Skip, Stuck)" by (rule CatchSkip) 
  finally show ?case by simp
qed (fastforce intro: step.intros)+

lemma steps_Abrupt: "\<Gamma>\<turnstile> (c, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  have steps_c\<^sub>2: "\<Gamma>\<turnstile> (c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Abrupt s)".
  also
  have "\<Gamma>\<turnstile> (Seq Skip c\<^sub>2, Abrupt s) \<rightarrow> (c\<^sub>2, Abrupt s)" by (rule SeqSkip)
  also note steps_c\<^sub>2
  finally show ?case by simp
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Abrupt s) \<rightarrow>\<^sup>* (Skip, Abrupt s)" by fact
  from CatchSteps [OF steps_c\<^sub>1 refl refl]
  have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, Abrupt s)".
  also
  have "\<Gamma>\<turnstile> (Catch Skip c\<^sub>2, Abrupt s) \<rightarrow> (Skip, Abrupt s)" by (rule CatchSkip) 
  finally show ?case by simp
qed (fastforce intro: step.intros)+

lemma step_Fault_prop: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>f. s=Fault f \<Longrightarrow> s'=Fault f"
using step
by (induct) auto

lemma step_Abrupt_prop: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "\<And>x. s=Abrupt x \<Longrightarrow> s'=Abrupt x"
using step
by (induct) auto

lemma step_Stuck_prop: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
by (induct) auto

lemma steps_Fault_prop: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Fault f \<Longrightarrow> s'=Fault f"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Fault_prop)
qed

lemma steps_Abrupt_prop: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Abrupt t \<Longrightarrow> s'=Abrupt t"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Abrupt_prop)
qed

lemma steps_Stuck_prop: 
  assumes step: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Stuck \<Longrightarrow> s'=Stuck"
using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Stuck_prop)
qed

(* ************************************************************************ *)
subsection {* Equivalence between Small-Step and Big-Step Semantics *}
(* ************************************************************************ *)

theorem exec_impl_steps:
  assumes exec: "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
  shows "\<exists>c' t'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',t') \<and>
               (case t of
                 Abrupt x \<Rightarrow> if s=t then c'=Skip \<and> t'=t else c'=Throw \<and> t'=Normal x
                | _ \<Rightarrow> c'=Skip \<and> t'=t)"
using exec
proof (induct)
  case Skip thus ?case
    by simp
next
  case Guard thus ?case by (blast intro: step.Guard rtranclp_trans)
next
  case GuardFault thus ?case by (fastforce intro: step.GuardFault rtranclp_trans)
next
  case FaultProp show ?case by (fastforce intro: steps_Fault)
next
  case Basic thus ?case by (fastforce intro: step.Basic rtranclp_trans)
next
  case Spec thus ?case by (fastforce intro: step.Spec rtranclp_trans)
next
  case SpecStuck thus ?case by (fastforce intro: step.SpecStuck rtranclp_trans)
next
  case (Seq c\<^sub>1 s s' c\<^sub>2 t) 
  have exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s'" by fact
  have exec_c\<^sub>2: "\<Gamma>\<turnstile> \<langle>c\<^sub>2,s'\<rangle> \<Rightarrow> t" by fact
  show ?case
  proof (cases "\<exists>x. s'=Abrupt x")
    case False
    from False Seq.hyps (2) 
    have "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, s')"
      by (cases s') auto
    hence seq_c\<^sub>1: "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, s')"
      by (rule SeqSteps) auto
    from Seq.hyps (4) obtain c' t' where
      steps_c\<^sub>2: "\<Gamma>\<turnstile> (c\<^sub>2, s') \<rightarrow>\<^sup>* (c', t')" and
      t: "(case t of
           Abrupt x \<Rightarrow> if s' = t then c' = Skip \<and> t' = t 
                       else c' = Throw \<and> t' = Normal x
           | _ \<Rightarrow> c' = Skip \<and> t' = t)"
      by auto
    note seq_c\<^sub>1 
    also have "\<Gamma>\<turnstile> (Seq Skip c\<^sub>2, s') \<rightarrow> (c\<^sub>2, s')" by (rule step.SeqSkip)
    also note steps_c\<^sub>2
    finally have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow>\<^sup>* (c', t')".
    with t False show ?thesis
      by (cases t) auto
  next
    case True
    then obtain x where s': "s'=Abrupt x"
      by blast
    from s' Seq.hyps (2) 
    have "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal x)"
      by auto
    hence seq_c\<^sub>1: "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow>\<^sup>* (Seq Throw c\<^sub>2, Normal x)"
      by (rule SeqSteps) auto
    also have "\<Gamma>\<turnstile> (Seq Throw c\<^sub>2, Normal x) \<rightarrow> (Throw, Normal x)"
      by (rule SeqThrow)
    finally have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow>\<^sup>* (Throw, Normal x)".
    moreover
    from exec_c\<^sub>2 s' have "t=Abrupt x"
      by (auto intro: Abrupt_end)
    ultimately show ?thesis
      by auto
  qed
next
  case CondTrue thus ?case by (blast intro: step.CondTrue rtranclp_trans)
next
  case CondFalse thus ?case by (blast intro: step.CondFalse rtranclp_trans)
next
  case (WhileTrue s b c s' t) 
  have exec_c: "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> s'" by fact
  have exec_w: "\<Gamma>\<turnstile> \<langle>While b c,s'\<rangle> \<Rightarrow> t" by fact
  have b: "s \<in> b" by fact
  hence step: "\<Gamma>\<turnstile> (While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"
    by (rule step.WhileTrue)
  show ?case
  proof (cases "\<exists>x. s'=Abrupt x")
    case False
    from False WhileTrue.hyps (3) 
    have "\<Gamma>\<turnstile> (c, Normal s) \<rightarrow>\<^sup>* (Skip, s')"
      by (cases s') auto
    hence seq_c: "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow>\<^sup>* (Seq Skip (While b c), s')"
      by (rule SeqSteps) auto
    from WhileTrue.hyps (5) obtain c' t' where
      steps_c\<^sub>2: "\<Gamma>\<turnstile> (While b c, s') \<rightarrow>\<^sup>* (c', t')" and
      t: "(case t of
           Abrupt x \<Rightarrow> if s' = t then c' = Skip \<and> t' = t 
                       else c' = Throw \<and> t' = Normal x
           | _ \<Rightarrow> c' = Skip \<and> t' = t)"
      by auto
    note step also note seq_c 
    also have "\<Gamma>\<turnstile> (Seq Skip (While b c), s') \<rightarrow> (While b c, s')" 
      by (rule step.SeqSkip)
    also note steps_c\<^sub>2
    finally have "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow>\<^sup>* (c', t')".
    with t False show ?thesis
      by (cases t) auto
  next
    case True
    then obtain x where s': "s'=Abrupt x"
      by blast
    note step
    also
    from s' WhileTrue.hyps (3) 
    have "\<Gamma>\<turnstile> (c, Normal s) \<rightarrow>\<^sup>* (Throw, Normal x)"
      by auto
    hence 
      seq_c: "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow>\<^sup>* (Seq Throw (While b c), Normal x)"
      by (rule SeqSteps) auto
    also have "\<Gamma>\<turnstile> (Seq Throw (While b c), Normal x) \<rightarrow> (Throw, Normal x)"
      by (rule SeqThrow)
    finally have "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow>\<^sup>* (Throw, Normal x)".
    moreover
    from exec_w s' have "t=Abrupt x"
      by (auto intro: Abrupt_end)
    ultimately show ?thesis
      by auto
  qed
next
  case WhileFalse thus ?case by (fastforce intro: step.WhileFalse rtrancl_trans)
next
  case Call thus ?case by (blast intro: step.Call rtranclp_trans)
next
  case CallUndefined thus ?case by (fastforce intro: step.CallUndefined rtranclp_trans)
next
  case StuckProp thus ?case by (fastforce intro: steps_Stuck)
next
  case DynCom thus ?case by (blast intro: step.DynCom rtranclp_trans)
next
   case Throw thus ?case by simp 
next
  case AbruptProp thus ?case by (fastforce intro: steps_Abrupt)
next
  case (CatchMatch c\<^sub>1 s s' c\<^sub>2 t)
  from CatchMatch.hyps (2)
  have "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')"
    by simp
  hence "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow>\<^sup>* (Catch Throw c\<^sub>2, Normal s')"
    by (rule CatchSteps) auto
  also have "\<Gamma>\<turnstile> (Catch Throw c\<^sub>2, Normal s') \<rightarrow> (c\<^sub>2, Normal s')"
    by (rule step.CatchThrow)
  also
  from CatchMatch.hyps (4) obtain c' t' where
      steps_c\<^sub>2: "\<Gamma>\<turnstile> (c\<^sub>2, Normal s') \<rightarrow>\<^sup>* (c', t')" and
      t: "(case t of
           Abrupt x \<Rightarrow> if Normal s' = t then c' = Skip \<and> t' = t 
                       else c' = Throw \<and> t' = Normal x
           | _ \<Rightarrow> c' = Skip \<and> t' = t)"
      by auto
  note steps_c\<^sub>2  
  finally show ?case
    using t
    by (auto split: xstate.splits)
next
  case (CatchMiss c\<^sub>1 s t c\<^sub>2) 
  have t: "\<not> isAbr t" by fact
  with CatchMiss.hyps (2)
  have "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Skip, t)"
    by (cases t) auto
  hence "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow>\<^sup>* (Catch Skip c\<^sub>2, t)"
    by (rule CatchSteps) auto
  also 
  have "\<Gamma>\<turnstile> (Catch Skip c\<^sub>2, t) \<rightarrow> (Skip, t)"
    by (rule step.CatchSkip)
  finally show ?case
    using t
    by (fastforce split: xstate.splits)
qed

corollary exec_impl_steps_Normal:
  assumes exec: "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Normal t"
  shows "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (Skip, Normal t)"
using exec_impl_steps [OF exec]  
by auto

corollary exec_impl_steps_Normal_Abrupt:
  assumes exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t"
  shows "\<Gamma>\<turnstile>(c,Normal s) \<rightarrow>\<^sup>* (Throw, Normal t)"
using exec_impl_steps [OF exec]  
by auto

corollary exec_impl_steps_Abrupt_Abrupt:
  assumes exec: "\<Gamma>\<turnstile>\<langle>c,Abrupt t\<rangle> \<Rightarrow> Abrupt t"
  shows "\<Gamma>\<turnstile>(c,Abrupt t) \<rightarrow>\<^sup>* (Skip, Abrupt t)"
using exec_impl_steps [OF exec]  
by auto

corollary exec_impl_steps_Fault:
  assumes exec: "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Fault f"
  shows "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (Skip, Fault f)"
using exec_impl_steps [OF exec]  
by auto

corollary exec_impl_steps_Stuck:
  assumes exec: "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Stuck"
  shows "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (Skip, Stuck)"
using exec_impl_steps [OF exec]  
by auto


lemma step_Abrupt_end: 
  assumes step: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Abrupt x \<Longrightarrow> s=Abrupt x"
using step
by induct auto

lemma step_Stuck_end: 
  assumes step: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Stuck \<Longrightarrow> 
          s=Stuck \<or> 
          (\<exists>r x. redex c\<^sub>1 = Spec r \<and> s=Normal x \<and> (\<forall>t. (x,t)\<notin>r)) \<or> 
          (\<exists>p x. redex c\<^sub>1=Call p \<and> s=Normal x \<and> \<Gamma> p = None)"
using step
by induct auto

lemma step_Fault_end: 
  assumes step: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Fault f \<Longrightarrow> 
          s=Fault f \<or> 
          (\<exists>g c x. redex c\<^sub>1 = Guard f g c \<and> s=Normal x \<and> x \<notin> g)"
using step
by induct auto

lemma exec_redex_Stuck:
"\<Gamma>\<turnstile>\<langle>redex c,s\<rangle> \<Rightarrow> Stuck \<Longrightarrow> \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Stuck"
proof (induct c)
  case Seq
  thus ?case
    by (cases s) (auto intro: exec.intros elim:exec_elim_cases)
next
  case Catch
  thus ?case
    by (cases s) (auto intro: exec.intros elim:exec_elim_cases)
qed simp_all

lemma exec_redex_Fault:
"\<Gamma>\<turnstile>\<langle>redex c,s\<rangle> \<Rightarrow> Fault f \<Longrightarrow> \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Fault f"
proof (induct c)
  case Seq
  thus ?case
    by (cases s) (auto intro: exec.intros elim:exec_elim_cases)
next
  case Catch
  thus ?case
    by (cases s) (auto intro: exec.intros elim:exec_elim_cases)
qed simp_all

lemma step_extend:
  assumes step: "\<Gamma>\<turnstile>(c,s) \<rightarrow> (c', s')"
  shows "\<And>t. \<Gamma>\<turnstile>\<langle>c',s'\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
using step 
proof (induct)
  case Basic thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case Spec thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case SpecStuck thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case Guard thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next  
  case GuardFault thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case (Seq c\<^sub>1 s c\<^sub>1' s' c\<^sub>2) 
  have step: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')" by fact
  have exec': "\<Gamma>\<turnstile> \<langle>Seq c\<^sub>1' c\<^sub>2,s'\<rangle> \<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Normal x)
    note s_Normal = this
    show ?thesis
    proof (cases s')
      case (Normal x')
      from exec' [simplified Normal] obtain s'' where
        exec_c\<^sub>1': "\<Gamma>\<turnstile> \<langle>c\<^sub>1',Normal x'\<rangle> \<Rightarrow> s''" and
        exec_c\<^sub>2: "\<Gamma>\<turnstile> \<langle>c\<^sub>2,s''\<rangle> \<Rightarrow> t"
        by cases
      from Seq.hyps (2) Normal exec_c\<^sub>1' s_Normal
      have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> s''"
        by simp
      from exec.Seq [OF this exec_c\<^sub>2] s_Normal
      show ?thesis by simp
    next
      case (Abrupt x')
      with exec' have "t=Abrupt x'"
        by (auto intro:Abrupt_end)
      moreover
      from step Abrupt
      have "s=Abrupt x'"
        by (auto intro: step_Abrupt_end)
      ultimately
      show ?thesis
        by (auto intro: exec.intros)
    next
      case (Fault f)
      from step_Fault_end [OF step this] s_Normal
      obtain g c where 
        redex_c\<^sub>1: "redex c\<^sub>1 = Guard f g c" and
        fail: "x \<notin> g"
        by auto
      hence "\<Gamma>\<turnstile> \<langle>redex c\<^sub>1,Normal x\<rangle> \<Rightarrow> Fault f"
        by (auto intro: exec.intros)
      from exec_redex_Fault [OF this]
      have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> Fault f".
      moreover from Fault exec' have "t=Fault f"
        by (auto intro: Fault_end)
      ultimately
      show ?thesis
        using s_Normal
        by (auto intro: exec.intros)
    next
      case Stuck
      from step_Stuck_end [OF step this] s_Normal
      have "(\<exists>r. redex c\<^sub>1 = Spec r \<and> (\<forall>t. (x, t) \<notin> r)) \<or>
            (\<exists>p. redex c\<^sub>1 = Call p \<and> \<Gamma> p = None)"
        by auto
      moreover
      {
        fix r
        assume "redex c\<^sub>1 = Spec r" and "(\<forall>t. (x, t) \<notin> r)"
        hence "\<Gamma>\<turnstile> \<langle>redex c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck"
          by (auto intro: exec.intros)
        from exec_redex_Stuck [OF this]
        have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck".
        moreover from Stuck exec' have "t=Stuck"
          by (auto intro: Stuck_end)
        ultimately
        have ?thesis
          using s_Normal
          by (auto intro: exec.intros)
      }
      moreover
      {
        fix p
        assume "redex c\<^sub>1 = Call p" and "\<Gamma> p = None"
        hence "\<Gamma>\<turnstile> \<langle>redex c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck"
          by (auto intro: exec.intros)
        from exec_redex_Stuck [OF this]
        have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck".
        moreover from Stuck exec' have "t=Stuck"
          by (auto intro: Stuck_end)
        ultimately
        have ?thesis
          using s_Normal
          by (auto intro: exec.intros)
      }
      ultimately show ?thesis
        by auto
    qed
  next
    case (Abrupt x)
    from step_Abrupt [OF step this]
    have "s'=Abrupt x".
    with exec'
    have "t=Abrupt x"
      by (auto intro: Abrupt_end)
    with Abrupt
    show ?thesis
      by (auto intro: exec.intros)
  next
    case (Fault f)
    from step_Fault [OF step this]
    have "s'=Fault f".
    with exec'
    have "t=Fault f"
      by (auto intro: Fault_end)
    with Fault
    show ?thesis
      by (auto intro: exec.intros)
  next
    case Stuck
    from step_Stuck [OF step this]
    have "s'=Stuck".
    with exec'
    have "t=Stuck"
      by (auto intro: Stuck_end)
    with Stuck
    show ?thesis
      by (auto intro: exec.intros)
  qed
next
  case (SeqSkip c\<^sub>2 s t) thus ?case
    by (cases s) (fastforce intro: exec.intros elim: exec_elim_cases)+      
next
  case (SeqThrow c\<^sub>2 s t) thus ?case
    by (fastforce intro: exec.intros elim: exec_elim_cases)+      
next      
  case CondTrue thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next      
  case CondFalse thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case WhileTrue thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case WhileFalse thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case Call thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case CallUndefined thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case DynCom thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case (Catch c\<^sub>1 s c\<^sub>1' s' c\<^sub>2 t)
  have step: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')" by fact
  have exec': "\<Gamma>\<turnstile> \<langle>Catch c\<^sub>1' c\<^sub>2,s'\<rangle> \<Rightarrow> t" by fact
  show ?case
  proof (cases s)
    case (Normal x)
    note s_Normal = this
    show ?thesis
    proof (cases s')
      case (Normal x')
      from exec' [simplified Normal] 
      show ?thesis
      proof (cases)
        fix s''
        assume exec_c\<^sub>1': "\<Gamma>\<turnstile> \<langle>c\<^sub>1',Normal x'\<rangle> \<Rightarrow> Abrupt s''" 
        assume exec_c\<^sub>2: "\<Gamma>\<turnstile> \<langle>c\<^sub>2,Normal s''\<rangle> \<Rightarrow> t"
        from Catch.hyps (2) Normal exec_c\<^sub>1' s_Normal
        have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> Abrupt s''"
          by simp
        from exec.CatchMatch [OF this exec_c\<^sub>2] s_Normal
        show ?thesis by simp
      next
        assume exec_c\<^sub>1': "\<Gamma>\<turnstile> \<langle>c\<^sub>1',Normal x'\<rangle> \<Rightarrow> t" 
        assume t: "\<not> isAbr t"
        from Catch.hyps (2) Normal exec_c\<^sub>1' s_Normal
        have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> t"
          by simp
        from exec.CatchMiss [OF this t] s_Normal
        show ?thesis by simp
      qed
    next
      case (Abrupt x')
      with exec' have "t=Abrupt x'"
        by (auto intro:Abrupt_end)
      moreover
      from step Abrupt
      have "s=Abrupt x'"
        by (auto intro: step_Abrupt_end)
      ultimately
      show ?thesis
        by (auto intro: exec.intros)
    next
      case (Fault f)
      from step_Fault_end [OF step this] s_Normal
      obtain g c where 
        redex_c\<^sub>1: "redex c\<^sub>1 = Guard f g c" and
        fail: "x \<notin> g"
        by auto
      hence "\<Gamma>\<turnstile> \<langle>redex c\<^sub>1,Normal x\<rangle> \<Rightarrow> Fault f"
        by (auto intro: exec.intros)
      from exec_redex_Fault [OF this]
      have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> Fault f".
      moreover from Fault exec' have "t=Fault f"
        by (auto intro: Fault_end)
      ultimately
      show ?thesis
        using s_Normal
        by (auto intro: exec.intros)
    next
      case Stuck
      from step_Stuck_end [OF step this] s_Normal
      have "(\<exists>r. redex c\<^sub>1 = Spec r \<and> (\<forall>t. (x, t) \<notin> r)) \<or>
            (\<exists>p. redex c\<^sub>1 = Call p \<and> \<Gamma> p = None)"
        by auto
      moreover
      {
        fix r
        assume "redex c\<^sub>1 = Spec r" and "(\<forall>t. (x, t) \<notin> r)"
        hence "\<Gamma>\<turnstile> \<langle>redex c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck"
          by (auto intro: exec.intros)
        from exec_redex_Stuck [OF this]
        have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck".
        moreover from Stuck exec' have "t=Stuck"
          by (auto intro: Stuck_end)
        ultimately
        have ?thesis
          using s_Normal
          by (auto intro: exec.intros)
      }
      moreover
      {
        fix p
        assume "redex c\<^sub>1 = Call p" and "\<Gamma> p = None"
        hence "\<Gamma>\<turnstile> \<langle>redex c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck"
          by (auto intro: exec.intros)
        from exec_redex_Stuck [OF this]
        have "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal x\<rangle> \<Rightarrow> Stuck".
        moreover from Stuck exec' have "t=Stuck"
          by (auto intro: Stuck_end)
        ultimately
        have ?thesis
          using s_Normal
          by (auto intro: exec.intros)
      }
      ultimately show ?thesis
        by auto
    qed
  next
    case (Abrupt x)
    from step_Abrupt [OF step this]
    have "s'=Abrupt x".
    with exec'
    have "t=Abrupt x"
      by (auto intro: Abrupt_end)
    with Abrupt
    show ?thesis
      by (auto intro: exec.intros)
  next
    case (Fault f)
    from step_Fault [OF step this]
    have "s'=Fault f".
    with exec'
    have "t=Fault f"
      by (auto intro: Fault_end)
    with Fault
    show ?thesis
      by (auto intro: exec.intros)
  next
    case Stuck
    from step_Stuck [OF step this]
    have "s'=Stuck".
    with exec'
    have "t=Stuck"
      by (auto intro: Stuck_end)
    with Stuck
    show ?thesis
      by (auto intro: exec.intros)
  qed
next
  case CatchThrow thus ?case
    by (fastforce intro: exec.intros elim: exec_Normal_elim_cases)
next
  case CatchSkip thus ?case
    by (fastforce intro: exec.intros elim: exec_elim_cases)
next
  case FaultProp thus ?case
    by (fastforce intro: exec.intros elim: exec_elim_cases)
next
  case StuckProp thus ?case
    by (fastforce intro: exec.intros elim: exec_elim_cases)
next
  case AbruptProp thus ?case
    by (fastforce intro: exec.intros elim: exec_elim_cases)
qed

theorem steps_Skip_impl_exec:
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (Skip,t)"
  shows "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case
    by (cases t) (auto intro: exec.intros)
next
  case (Trans c s c' s')
  have "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')" and "\<Gamma>\<turnstile> \<langle>c',s'\<rangle> \<Rightarrow> t" by fact+
  thus ?case
    by (rule step_extend)
qed

theorem steps_Throw_impl_exec:
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (Throw,Normal t)"
  shows "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Abrupt t"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case
    by (auto intro: exec.intros)
next
  case (Trans c s c' s')
  have "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s')" and "\<Gamma>\<turnstile> \<langle>c',s'\<rangle> \<Rightarrow> Abrupt t" by fact+
  thus ?case
    by (rule step_extend)
qed

(* ************************************************************************ *)
subsection {* Infinite Computations: @{text "\<Gamma>\<turnstile>(c, s) \<rightarrow> \<dots>(\<infinity>)"}*}
(* ************************************************************************ *)

definition inf:: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) config \<Rightarrow> bool"
 ("_\<turnstile> _ \<rightarrow> \<dots>'(\<infinity>')" [60,80] 100) where
"\<Gamma>\<turnstile> cfg \<rightarrow> \<dots>(\<infinity>) \<equiv> (\<exists>f. f (0::nat) = cfg \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)))" 

lemma not_infI: "\<lbrakk>\<And>f. \<lbrakk>f 0 = cfg; \<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)\<rbrakk> \<Longrightarrow> False\<rbrakk>  
                \<Longrightarrow> \<not>\<Gamma>\<turnstile> cfg \<rightarrow> \<dots>(\<infinity>)"
  by (auto simp add: inf_def)

(* ************************************************************************ *)
subsection {* Equivalence between Termination and the Absence of Infinite Computations*}
(* ************************************************************************ *)


lemma step_preserves_termination: 
  assumes step: "\<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"  
using step
proof (induct)
  case Basic thus ?case by (fastforce intro: terminates.intros)
next
  case Spec thus ?case by (fastforce intro: terminates.intros)
next
  case SpecStuck thus ?case by (fastforce intro: terminates.intros)
next
  case Guard thus ?case 
    by (fastforce intro: terminates.intros elim: terminates_Normal_elim_cases)
next
  case GuardFault thus ?case by (fastforce intro: terminates.intros)
next
  case (Seq c\<^sub>1 s c\<^sub>1' s' c\<^sub>2) thus ?case
    apply (cases s)
    apply     (cases s')
    apply         (fastforce intro: terminates.intros step_extend 
                    elim: terminates_Normal_elim_cases)
    apply (fastforce intro: terminates.intros dest: step_Abrupt_prop 
      step_Fault_prop step_Stuck_prop)+
    done
next
  case (SeqSkip c\<^sub>2 s) 
  thus ?case 
    apply (cases s)
    apply (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )+
    done
next
  case (SeqThrow c\<^sub>2 s) 
  thus ?case 
    by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case CondTrue 
  thus ?case 
    by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case CondFalse 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case WhileTrue
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case WhileFalse 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case Call 
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case CallUndefined
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case DynCom
  thus ?case 
    by (fastforce intro: terminates.intros 
            elim: terminates_Normal_elim_cases )
next
  case (Catch c\<^sub>1 s c\<^sub>1' s' c\<^sub>2) thus ?case
    apply (cases s)
    apply     (cases s')
    apply         (fastforce intro: terminates.intros step_extend 
                    elim: terminates_Normal_elim_cases)
    apply (fastforce intro: terminates.intros dest: step_Abrupt_prop 
      step_Fault_prop step_Stuck_prop)+
    done
next
  case CatchThrow
  thus ?case 
   by (fastforce intro: terminates.intros exec.intros
            elim: terminates_Normal_elim_cases )
next
  case (CatchSkip c\<^sub>2 s) 
  thus ?case 
    by (cases s) (fastforce intro: terminates.intros)+
next
  case FaultProp thus ?case by (fastforce intro: terminates.intros)
next
  case StuckProp thus ?case by (fastforce intro: terminates.intros)
next
  case AbruptProp thus ?case by (fastforce intro: terminates.intros)
qed

lemma steps_preserves_termination: 
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"
using steps
proof (induct rule: rtranclp_induct2 [consumes 1, case_names Refl Trans])
  case Refl thus ?case  .
next
  case Trans
  thus ?case
    by (blast dest: step_preserves_termination)
qed

ML {*
  ML_Thms.bind_thm ("tranclp_induct2", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(aa,ab)"), ((("b", 0), Position.none), "(ba,bb)")] []
      @{thm tranclp_induct}));
*}

lemma steps_preserves_termination': 
  assumes steps: "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s')"
  shows "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s'"
using steps
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case Step thus ?case by (blast intro: step_preserves_termination)
next
  case Trans
  thus ?case
    by (blast dest: step_preserves_termination)
qed



definition head_com:: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
where
"head_com c =
  (case c of
     Seq c\<^sub>1 c\<^sub>2 \<Rightarrow> c\<^sub>1
   | Catch c\<^sub>1 c\<^sub>2 \<Rightarrow> c\<^sub>1
   | _ \<Rightarrow> c)"

  
definition head:: "('s,'p,'f) config \<Rightarrow> ('s,'p,'f) config"
  where "head cfg = (head_com (fst cfg), snd cfg)"

lemma le_Suc_cases: "\<lbrakk>\<And>i. \<lbrakk>i < k\<rbrakk> \<Longrightarrow> P i; P k\<rbrakk> \<Longrightarrow> \<forall>i<(Suc k). P i"
  apply clarify
  apply (case_tac "i=k")
  apply auto
  done

lemma redex_Seq_False: "\<And>c' c''. (redex c = Seq c'' c') = False"
  by (induct c) auto

lemma redex_Catch_False: "\<And>c' c''. (redex c = Catch c'' c') = False"
  by (induct c) auto


lemma infinite_computation_extract_head_Seq:
  assumes inf_comp: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)"
  assumes f_0: "f 0 = (Seq c\<^sub>1 c\<^sub>2,s)"
  assumes not_fin: "\<forall>i<k. \<not> final (head (f i))"
  shows "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s')) \<and>  
               \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i+1))"
        (is "\<forall>i<k. ?P i")
using not_fin
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have not_fin_Suc: 
    "\<forall>i<Suc k. \<not> final (head (f i))" by fact
  from this[rule_format] have not_fin_k: 
    "\<forall>i<k. \<not> final (head (f i))" 
    apply clarify
    apply (subgoal_tac "i < Suc k")
    apply blast
    apply simp
    done

  from Suc.hyps [OF this]
  have hyp: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s')) \<and> 
                   \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))".
  show ?case
  proof (rule le_Suc_cases)
    fix i 
    assume "i < k"
    then show "?P i"
      by (rule hyp [rule_format])
  next
    show "?P k"
    proof -
      from hyp [rule_format, of "k - 1"] f_0
      obtain c' fs' L' s' where  f_k: "f k = (Seq c' c\<^sub>2, s')"
        by (cases k) auto
      from inf_comp [rule_format, of k] f_k
      have "\<Gamma>\<turnstile>(Seq c' c\<^sub>2, s') \<rightarrow> f (k + 1)"
        by simp
      moreover
      from not_fin_Suc [rule_format, of k] f_k
      have "\<not> final (c',s')"
        by (simp add: final_def head_def head_com_def)
      ultimately
      obtain c'' s'' where
         "\<Gamma>\<turnstile>(c', s') \<rightarrow> (c'', s'')" and
         "f (k + 1) = (Seq c'' c\<^sub>2, s'')"
        by cases (auto simp add: redex_Seq_False final_def)
      with f_k
      show ?thesis
        by (simp add: head_def head_com_def)
    qed
  qed
qed

lemma infinite_computation_extract_head_Catch:
  assumes inf_comp: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)"
  assumes f_0: "f 0 = (Catch c\<^sub>1 c\<^sub>2,s)"
  assumes not_fin: "\<forall>i<k. \<not> final (head (f i))"
  shows "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s')) \<and>  
               \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i+1))"
        (is "\<forall>i<k. ?P i")
using not_fin
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have not_fin_Suc: 
    "\<forall>i<Suc k. \<not> final (head (f i))" by fact
  from this[rule_format] have not_fin_k: 
    "\<forall>i<k. \<not> final (head (f i))" 
    apply clarify
    apply (subgoal_tac "i < Suc k")
    apply blast
    apply simp
    done

  from Suc.hyps [OF this]
  have hyp: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s')) \<and> 
                   \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))".
  show ?case
  proof (rule le_Suc_cases)
    fix i 
    assume "i < k"
    then show "?P i"
      by (rule hyp [rule_format])
  next
    show "?P k"
    proof -
      from hyp [rule_format, of "k - 1"] f_0
      obtain c' fs' L' s' where  f_k: "f k = (Catch c' c\<^sub>2, s')"
        by (cases k) auto
      from inf_comp [rule_format, of k] f_k
      have "\<Gamma>\<turnstile>(Catch c' c\<^sub>2, s') \<rightarrow> f (k + 1)"
        by simp
      moreover
      from not_fin_Suc [rule_format, of k] f_k
      have "\<not> final (c',s')"
        by (simp add: final_def head_def head_com_def)
      ultimately
      obtain c'' s'' where
         "\<Gamma>\<turnstile>(c', s') \<rightarrow> (c'', s'')" and
         "f (k + 1) = (Catch c'' c\<^sub>2, s'')"
        by cases (auto simp add: redex_Catch_False final_def)+
      with f_k
      show ?thesis
        by (simp add: head_def head_com_def)
    qed
  qed
qed

lemma no_inf_Throw: "\<not> \<Gamma>\<turnstile>(Throw,s) \<rightarrow> \<dots>(\<infinity>)"
proof 
  assume "\<Gamma>\<turnstile> (Throw, s) \<rightarrow> \<dots>(\<infinity>)"
  then obtain f where
    step [rule_format]: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Throw, s)"
    by (auto simp add: inf_def)
  from step [of 0, simplified f_0] step [of 1]
  show False
    by cases (auto elim: step_elim_cases)
qed

lemma split_inf_Seq: 
  assumes inf_comp: "\<Gamma>\<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>) \<or> 
         (\<exists>s'. \<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s') \<and> \<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>))"
proof -
  from inf_comp obtain f where
    step: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Seq c\<^sub>1 c\<^sub>2, s)"
    by (auto simp add: inf_def)
  from f_0 have head_f_0: "head (f 0) = (c\<^sub>1,s)" 
    by (simp add: head_def head_com_def)
  show ?thesis
  proof (cases "\<exists>i. final (head (f i))")
    case True
    def k\<equiv>"(LEAST i. final (head (f i)))"
    have less_k: "\<forall>i<k. \<not> final (head (f i))"
      apply (intro allI impI)
      apply (unfold k_def)
      apply (drule not_less_Least)
      apply auto
      done
    from infinite_computation_extract_head_Seq [OF step f_0 this]
    obtain step_head: "\<forall>i<k. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" and
           conf: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Seq c' c\<^sub>2, s'))"
      by blast 
    from True
    have final_f_k: "final (head (f k))"
      apply -
      apply (erule exE)
      apply (drule LeastI)
      apply (simp add: k_def)
      done
    moreover
    from f_0 conf [rule_format, of "k - 1"]
    obtain c' s' where f_k: "f k = (Seq c' c\<^sub>2,s')"
      by (cases k) auto
    moreover
    from step_head have steps_head: "\<Gamma>\<turnstile>head (f 0) \<rightarrow>\<^sup>* head (f k)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc m)
      have step: "\<forall>i<Suc m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" by fact
      hence "\<forall>i<m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))"
        by auto
      hence "\<Gamma>\<turnstile> head (f 0) \<rightarrow>\<^sup>*  head (f m)"
        by (rule Suc.hyps)
      also from step [rule_format, of m]
      have "\<Gamma>\<turnstile> head (f m) \<rightarrow> head (f (m + 1))" by simp
      finally show ?case by simp
    qed
    {
      assume f_k: "f k = (Seq Skip c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k
      obtain "\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,s') \<rightarrow> (c\<^sub>2,s')" and
        f_Suc_k: "f (k + 1) = (c\<^sub>2,s')"
        by (fastforce elim: step.cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (c\<^sub>2,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      ultimately
      have ?thesis
        by auto
    }
    moreover
    {
      fix x
      assume s': "s'=Normal x" and f_k: "f k = (Seq Throw c\<^sub>2, s')"
      from step [rule_format, of k] f_k s'
      obtain "\<Gamma>\<turnstile>(Seq Throw c\<^sub>2,s') \<rightarrow> (Throw,s')" and
        f_Suc_k: "f (k + 1) = (Throw,s')"
        by (fastforce elim: step_elim_cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (Throw,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(Throw,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      with no_inf_Throw
      have ?thesis
        by auto
    }
    ultimately 
    show ?thesis
      by (auto simp add: final_def head_def head_com_def)
  next
    case False
    then have not_fin: "\<forall>i. \<not> final (head (f i))"
      by blast
    have "\<forall>i. \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i + 1))"
    proof 
      fix k
      from not_fin 
      have "\<forall>i<(Suc k). \<not> final (head (f i))"
        by simp
      
      from infinite_computation_extract_head_Seq [OF step f_0 this ]
      show "\<Gamma>\<turnstile> head (f k) \<rightarrow> head (f (k + 1))" by simp
    qed
    with head_f_0 have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>)"
      by (auto simp add: inf_def)
    thus ?thesis
      by simp
  qed
qed

lemma split_inf_Catch: 
  assumes inf_comp: "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2,s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>) \<or> 
         (\<exists>s'. \<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Throw,Normal s') \<and> \<Gamma>\<turnstile>(c\<^sub>2,Normal s') \<rightarrow> \<dots>(\<infinity>))"
proof -
  from inf_comp obtain f where
    step: "\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow> f (i+1)" and
    f_0: "f 0 = (Catch c\<^sub>1 c\<^sub>2, s)"
    by (auto simp add: inf_def)
  from f_0 have head_f_0: "head (f 0) = (c\<^sub>1,s)" 
    by (simp add: head_def head_com_def)
  show ?thesis
  proof (cases "\<exists>i. final (head (f i))")
    case True
    def k\<equiv>"(LEAST i. final (head (f i)))"
    have less_k: "\<forall>i<k. \<not> final (head (f i))"
      apply (intro allI impI)
      apply (unfold k_def)
      apply (drule not_less_Least)
      apply auto
      done
    from infinite_computation_extract_head_Catch [OF step f_0 this]
    obtain step_head: "\<forall>i<k. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" and
           conf: "\<forall>i<k. (\<exists>c' s'. f (i + 1) = (Catch c' c\<^sub>2, s'))"
      by blast 
    from True
    have final_f_k: "final (head (f k))"
      apply -
      apply (erule exE)
      apply (drule LeastI)
      apply (simp add: k_def)
      done
    moreover
    from f_0 conf [rule_format, of "k - 1"]
    obtain c' s' where f_k: "f k = (Catch c' c\<^sub>2,s')"
      by (cases k) auto
    moreover
    from step_head have steps_head: "\<Gamma>\<turnstile>head (f 0) \<rightarrow>\<^sup>* head (f k)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc m)
      have step: "\<forall>i<Suc m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))" by fact
      hence "\<forall>i<m. \<Gamma>\<turnstile> head (f i) \<rightarrow> head (f (i + 1))"
        by auto
      hence "\<Gamma>\<turnstile> head (f 0) \<rightarrow>\<^sup>*  head (f m)"
        by (rule Suc.hyps)
      also from step [rule_format, of m]
      have "\<Gamma>\<turnstile> head (f m) \<rightarrow> head (f (m + 1))" by simp
      finally show ?case by simp
    qed
    {
      assume f_k: "f k = (Catch Skip c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Skip,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k
      obtain "\<Gamma>\<turnstile>(Catch Skip c\<^sub>2,s') \<rightarrow> (Skip,s')" and
        f_Suc_k: "f (k + 1) = (Skip,s')"
        by (fastforce elim: step.cases intro: step.intros)
      from step [rule_format, of "k+1", simplified f_Suc_k]
      have ?thesis
        by (rule no_step_final') (auto simp add: final_def)
    }
    moreover
    {
      fix x
      assume s': "s'=Normal x" and f_k: "f k = (Catch Throw c\<^sub>2, s')"
      with steps_head
      have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow>\<^sup>* (Throw,s')"
        using head_f_0
        by (simp add: head_def head_com_def)
      moreover
      from step [rule_format, of k] f_k s'
      obtain "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,s') \<rightarrow> (c\<^sub>2,s')" and
        f_Suc_k: "f (k + 1) = (c\<^sub>2,s')"
        by (fastforce elim: step_elim_cases intro: step.intros)
      def g\<equiv>"\<lambda>i. f (i + (k + 1))"
      from f_Suc_k
      have g_0: "g 0 = (c\<^sub>2,s')"
        by (simp add: g_def)
      from step
      have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (i + 1)"
        by (simp add: g_def)
      with g_0 have "\<Gamma>\<turnstile>(c\<^sub>2,s') \<rightarrow> \<dots>(\<infinity>)"
        by (auto simp add: inf_def)
      ultimately
      have ?thesis
        using s'
        by auto
    }
    ultimately 
    show ?thesis
      by (auto simp add: final_def head_def head_com_def)
  next
    case False
    then have not_fin: "\<forall>i. \<not> final (head (f i))"
      by blast
    have "\<forall>i. \<Gamma>\<turnstile>head (f i) \<rightarrow> head (f (i + 1))"
    proof 
      fix k
      from not_fin 
      have "\<forall>i<(Suc k). \<not> final (head (f i))"
        by simp
      
      from infinite_computation_extract_head_Catch [OF step f_0 this ]
      show "\<Gamma>\<turnstile> head (f k) \<rightarrow> head (f (k + 1))" by simp
    qed
    with head_f_0 have "\<Gamma>\<turnstile>(c\<^sub>1,s) \<rightarrow> \<dots>(\<infinity>)"
      by (auto simp add: inf_def)
    thus ?thesis
      by simp
  qed
qed

lemma Skip_no_step: "\<Gamma>\<turnstile>(Skip,s) \<rightarrow> cfg \<Longrightarrow> P"
  apply (erule no_step_final')
  apply (simp add: final_def)
  done

lemma not_inf_Stuck: "\<not> \<Gamma>\<turnstile>(c,Stuck) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Stuck)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Stuck_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Stuck)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Stuck) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Stuck_prop)
  qed  
qed

lemma not_inf_Fault: "\<not> \<Gamma>\<turnstile>(c,Fault x) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Fault x)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Fault x) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Fault_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Fault x)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Fault x) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Fault_prop)
  qed  
qed

lemma not_inf_Abrupt: "\<not> \<Gamma>\<turnstile>(c,Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
proof (induct c)
  case Skip
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Abrupt s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto dest: steps_Abrupt_prop)
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c\<^sub>1 c\<^sub>2, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (While b c) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (DynCom d) 
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom d, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard m g c)
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case Throw
  show ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Abrupt s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Catch c\<^sub>1 c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Abrupt s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto dest: steps_Abrupt_prop)
  qed  
qed


theorem terminates_impl_no_infinite_computation:
  assumes termi: "\<Gamma>\<turnstile>c \<down> s"
  shows "\<not> \<Gamma>\<turnstile>(c,s) \<rightarrow> \<dots>(\<infinity>)"
using termi
proof (induct)
  case (Skip s) thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Skip, Normal s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: Skip_no_step)
  qed
next
  case (Basic g s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Basic g, Normal s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Spec r s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Spec r, Normal s)" 
    from f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Guard s g c m)
  have g: "s \<in> g" by fact
  have hyp: "\<not> \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Normal s)" 
    from f_step [of 0] f_0  g
    have "f 1 = (c,Normal s)"
      by (fastforce elim: step_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp show False ..
  qed
next
  case (GuardFault s g m c)
  have g: "s \<notin> g" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Guard m g c, Normal s)" 
    from g f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Fault c m)
  thus ?case
    by (rule not_inf_Fault)
next
  case (Seq c\<^sub>1 s c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] Seq.hyps
    show False
      by (auto intro: steps_Skip_impl_exec)
  qed
next
  case (CondTrue s b c1 c2)
  have b: "s \<in> b" by fact
  have hyp_c1: "\<not> \<Gamma>\<turnstile> (c1, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c1 c2, Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = (c1,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c1, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c1 show False by simp
  qed    
next
  case (CondFalse s b c2 c1)
  have b: "s \<notin> b" by fact
  have hyp_c2: "\<not> \<Gamma>\<turnstile> (c2, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Cond b c1 c2, Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = (c2,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (c2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c2 show False by simp
  qed
next    
  case (WhileTrue s b c)
  have b: "s \<in> b" by fact
  have hyp_c: "\<not> \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  have hyp_w: "\<forall>s'. \<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> 
                     \<Gamma>\<turnstile>While b c \<down> s' \<and> \<not> \<Gamma>\<turnstile> (While b c, s') \<rightarrow> \<dots>(\<infinity>)" by fact
  have not_inf_Seq: "\<not> \<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
  proof 
    assume "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Seq [OF this] hyp_c hyp_w show False
      by (auto intro: steps_Skip_impl_exec)
  qed
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    then obtain f where
      f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)" and
      f_0: "f 0 = (While b c, Normal s)" 
      by (auto simp add: inf_def)
    from f_step [of 0] f_0 b
    have "f 1 = (Seq c (While b c),Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with not_inf_Seq show False by simp
  qed
next
  case (WhileFalse s b c)
  have b: "s \<notin> b" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (While b c, Normal s)" 
    from b f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Call p bdy s)
  have bdy: "\<Gamma> p = Some bdy" by fact
  have hyp: "\<not> \<Gamma>\<turnstile> (bdy, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Normal s)" 
    from bdy f_step [of 0] f_0
    have "f 1 = (bdy,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "\<Gamma>\<turnstile> (bdy, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp show False by simp
  qed    
next
  case (CallUndefined p s)
  have no_bdy: "\<Gamma> p = None" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Call p, Normal s)" 
    from no_bdy f_step [of 0] f_0 f_step [of 1]
    show False
      by (fastforce elim: Skip_no_step step_elim_cases)
  qed
next
  case (Stuck c)
  show ?case
    by (rule not_inf_Stuck)
next
  case (DynCom c s)
  have hyp: "\<not> \<Gamma>\<turnstile> (c s, Normal s) \<rightarrow> \<dots>(\<infinity>)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (DynCom c, Normal s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = (c s, Normal s)"
      by (auto elim: step_elim_cases)
    with f_step have "\<Gamma>\<turnstile> (c s, Normal s) \<rightarrow> \<dots>(\<infinity>)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp
    show False by simp
  qed
next
  case (Throw s) thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = (Throw, Normal s)" 
    from f_step [of 0] f_0
    show False
      by (auto elim: step_elim_cases)
  qed  
next
  case (Abrupt c)
  show ?case
    by (rule not_inf_Abrupt)
next
  case (Catch c\<^sub>1 s c\<^sub>2)
  show ?case
  proof 
    assume "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> \<dots>(\<infinity>)"
    from split_inf_Catch [OF this] Catch.hyps
    show False
      by (auto intro: steps_Throw_impl_exec)
  qed
qed


definition
 termi_call_steps :: "('s,'p,'f) body \<Rightarrow> (('s \<times> 'p) \<times> ('s \<times> 'p))set"
where
"termi_call_steps \<Gamma> =
 {((t,q),(s,p)). \<Gamma>\<turnstile>Call p\<down>Normal s \<and> 
       (\<exists>c. \<Gamma>\<turnstile>(Call p,Normal s) \<rightarrow>\<^sup>+ (c,Normal t) \<and> redex c = Call q)}"


primrec subst_redex:: "('s,'p,'f)com \<Rightarrow> ('s,'p,'f)com \<Rightarrow> ('s,'p,'f)com"
where
"subst_redex Skip c = c" |
"subst_redex (Basic f) c = c" |
"subst_redex (Spec r) c = c" |
"subst_redex (Seq c\<^sub>1 c\<^sub>2) c  = Seq (subst_redex c\<^sub>1 c) c\<^sub>2" |
"subst_redex (Cond b c\<^sub>1 c\<^sub>2) c = c" |
"subst_redex (While b c') c = c" |
"subst_redex (Call p) c = c" |
"subst_redex (DynCom d) c = c" |
"subst_redex (Guard f b c') c = c" |
"subst_redex (Throw) c = c" |
"subst_redex (Catch c\<^sub>1 c\<^sub>2) c = Catch (subst_redex c\<^sub>1 c) c\<^sub>2"

lemma subst_redex_redex:
  "subst_redex c (redex c) = c"
  by (induct c) auto

lemma redex_subst_redex: "redex (subst_redex c r) = redex r"
  by (induct c) auto
  
lemma step_redex':
  shows "\<Gamma>\<turnstile>(redex c,s) \<rightarrow> (r',s') \<Longrightarrow> \<Gamma>\<turnstile>(c,s) \<rightarrow> (subst_redex c r',s')"
by (induct c) (auto intro: step.Seq step.Catch)


lemma step_redex:
  shows "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s') \<Longrightarrow> \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow> (subst_redex c r',s')"
by (induct c) (auto intro: step.Seq step.Catch)

lemma steps_redex:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow>\<^sup>* (subst_redex c r',s')"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl 
  show "\<Gamma>\<turnstile> (subst_redex c r', s') \<rightarrow>\<^sup>* (subst_redex c r', s')"
    by simp
next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" by fact
  from step_redex [OF this]
  have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow> (subst_redex c r'', s'')".
  also  
  have "\<Gamma>\<turnstile> (subst_redex c r'', s'') \<rightarrow>\<^sup>* (subst_redex c r', s')" by fact
  finally show ?case .
qed

ML {*
  ML_Thms.bind_thm ("trancl_induct2", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(aa, ab)"), ((("b", 0), Position.none), "(ba, bb)")] []
      @{thm trancl_induct}));
*}

lemma steps_redex':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. \<Gamma>\<turnstile>(subst_redex c r,s) \<rightarrow>\<^sup>+ (subst_redex c r',s')"
using steps
proof (induct rule: tranclp_induct2 [consumes 1,case_names Step Trans])
  case (Step r' s')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  then have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow> (subst_redex c r', s')"
    by (rule step_redex)
  then show "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r', s')"..
next
  case (Trans r' s' r'' s'')
  have "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r', s')" by fact
  also
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  hence "\<Gamma>\<turnstile> (subst_redex c r', s') \<rightarrow> (subst_redex c r'', s'')"
    by (rule step_redex)
  finally show "\<Gamma>\<turnstile> (subst_redex c r, s) \<rightarrow>\<^sup>+ (subst_redex c r'', s'')" .
qed

primrec seq:: "(nat \<Rightarrow> ('s,'p,'f)com) \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('s,'p,'f)com"
where
"seq c p 0 = Call p" |
"seq c p (Suc i) = subst_redex (seq c p i) (c i)"


lemma renumber':
  assumes f: "\<forall>i. (a,f i) \<in> r\<^sup>* \<and> (f i,f(Suc i)) \<in> r" 
  assumes a_b: "(a,b) \<in> r\<^sup>*" 
  shows "b = f 0 \<Longrightarrow> (\<exists>f. f 0 = a \<and> (\<forall>i. (f i, f(Suc i)) \<in> r))"
using a_b
proof (induct rule: converse_rtrancl_induct [consumes 1])
  assume "b = f 0"
  with f show "\<exists>f. f 0 = b \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
    by blast
next
  fix a z
  assume a_z: "(a, z) \<in> r" and "(z, b) \<in> r\<^sup>*" 
  assume "b = f 0 \<Longrightarrow> \<exists>f. f 0 = z \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
         "b = f 0"
  then obtain f where f0: "f 0 = z" and seq: "\<forall>i. (f i, f (Suc i)) \<in> r"
    by iprover
  {
    fix i have "((\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> f i) i, f i) \<in> r"
      using seq a_z f0
      by (cases i) auto
  }
  then
  show "\<exists>f. f 0 = a \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)"
    by - (rule exI [where x="\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> f i"],simp)
qed

lemma renumber:
 "\<forall>i. (a,f i) \<in> r\<^sup>* \<and> (f i,f(Suc i)) \<in> r 
 \<Longrightarrow> \<exists>f. f 0 = a \<and> (\<forall>i. (f i, f(Suc i)) \<in> r)"
  by (blast dest:renumber')

lemma lem:
  "\<forall>y. r\<^sup>+\<^sup>+ a y \<longrightarrow> P a \<longrightarrow> P y 
   \<Longrightarrow> ((b,a) \<in> {(y,x). P x \<and> r x y}\<^sup>+) = ((b,a) \<in> {(y,x). P x \<and> r\<^sup>+\<^sup>+ x y})"
apply(rule iffI)
 apply clarify
 apply(erule trancl_induct)
  apply blast
 apply(blast intro:tranclp_trans)
apply clarify
apply(erule tranclp_induct)
 apply blast
apply(blast intro:trancl_trans)
done

corollary terminates_impl_no_infinite_trans_computation:
 assumes terminates: "\<Gamma>\<turnstile>c\<down>s"
 shows "\<not>(\<exists>f. f 0 = (c,s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f(Suc i)))"
proof -
  have "wf({(y,x). \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
  proof (rule wf_trancl)
    show "wf {(y, x). \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}"
    proof (simp only: wf_iff_no_infinite_down_chain,clarify,simp)
      fix f
      assume "\<forall>i. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
      hence "\<exists>f. f (0::nat) = (c,s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
        by (rule renumber [to_pred])
      moreover from terminates_impl_no_infinite_computation [OF terminates]
      have "\<not> (\<exists>f. f (0::nat) = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
        by (simp add: inf_def)
      ultimately show False
        by simp
    qed
  qed
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i)
                 \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
    by (simp add: wf_iff_no_infinite_down_chain)
  thus ?thesis
  proof (rule contrapos_nn)
    assume "\<exists>f. f (0::nat) = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i))"
    then obtain f where
      f0: "f 0 = (c, s)" and
      seq: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i)"
      by iprover
    show 
      "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
    proof (rule exI [where x=f],rule allI)
      fix i
      show "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
      proof -   
        {
          fix i have "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i"
          proof (induct i)
            case 0 show "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f 0"
              by (simp add: f0)
          next
            case (Suc n)
            have "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f n"  by fact
            with seq show "\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f (Suc n)"
              by (blast intro: tranclp_into_rtranclp rtranclp_trans)
          qed
        }
        hence "\<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* f i"
          by iprover
        with seq have
          "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow>\<^sup>+ y}"
          by clarsimp
        moreover 
        have "\<forall>y. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ y\<longrightarrow>\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f i\<longrightarrow>\<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* y"
          by (blast intro: tranclp_into_rtranclp rtranclp_trans)
        ultimately 
        show ?thesis 
          by (subst lem )
      qed
    qed
  qed
qed

theorem wf_termi_call_steps: "wf (termi_call_steps \<Gamma>)"
proof (simp only: termi_call_steps_def wf_iff_no_infinite_down_chain,
       clarify,simp)
  fix f
  assume inf: "\<forall>i. (\<lambda>(t, q) (s, p).
                \<Gamma>\<turnstile>Call p \<down> Normal s \<and>
                (\<exists>c. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow>\<^sup>+ (c, Normal t) \<and> redex c = Call q))
             (f (Suc i)) (f i)"
  def s\<equiv>"\<lambda>i::nat. fst (f i)" 
  def p\<equiv>"\<lambda>i::nat. snd (f i)::'b"
  from inf
  have inf': "\<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i) \<and>
               (\<exists>c. \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c, Normal (s (i+1))) \<and> 
                    redex c = Call (p (i+1)))"
    apply -
    apply (rule allI)
    apply (erule_tac x=i in allE)
    apply (auto simp add: s_def p_def)
    done
  show False
  proof -
    from inf'
    have "\<exists>c. \<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i) \<and>
               \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i+1))) \<and> 
                    redex (c i) = Call (p (i+1))"
      apply -
      apply (rule choice)
      by blast
    then obtain c where
      termi_c: "\<forall>i. \<Gamma>\<turnstile>Call (p i) \<down> Normal (s i)" and
      steps_c: "\<forall>i. \<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i+1)))" and
      red_c:   "\<forall>i. redex (c i) = Call (p (i+1))"
      by auto
    def g\<equiv>"\<lambda>i. (seq c (p 0) i,Normal (s i)::('a,'c) xstate)"
    from red_c [rule_format, of 0]
    have "g 0 = (Call (p 0), Normal (s 0))"
      by (simp add: g_def)
    moreover
    {
      fix i
      have "redex (seq c (p 0) i) = Call (p i)"
        by (induct i) (auto simp add: redex_subst_redex red_c)
      from this [symmetric]
      have "subst_redex (seq c (p 0) i) (Call (p i)) = (seq c (p 0) i)"
        by (simp add: subst_redex_redex)
    } note subst_redex_seq = this
    have "\<forall>i. \<Gamma>\<turnstile> (g i) \<rightarrow>\<^sup>+ (g (i+1))"
    proof 
      fix i
      from steps_c [rule_format, of i]
      have "\<Gamma>\<turnstile> (Call (p i), Normal (s i)) \<rightarrow>\<^sup>+ (c i, Normal (s (i + 1)))".
      from steps_redex' [OF this, of "(seq c (p 0) i)"]
      have "\<Gamma>\<turnstile> (subst_redex (seq c (p 0) i) (Call (p i)), Normal (s i)) \<rightarrow>\<^sup>+
                (subst_redex (seq c (p 0) i) (c i), Normal (s (i + 1)))" .
      hence "\<Gamma>\<turnstile> (seq c (p 0) i, Normal (s i)) \<rightarrow>\<^sup>+ 
                 (seq c (p 0) (i+1), Normal (s (i + 1)))"
        by (simp add: subst_redex_seq)
      thus "\<Gamma>\<turnstile> (g i) \<rightarrow>\<^sup>+ (g (i+1))"
        by (simp add: g_def)
    qed
    moreover
    from terminates_impl_no_infinite_trans_computation [OF termi_c [rule_format, of 0]]
    have "\<not> (\<exists>f. f 0 = (Call (p 0), Normal (s 0)) \<and> (\<forall>i. \<Gamma>\<turnstile> f i \<rightarrow>\<^sup>+ f (Suc i)))" .
    ultimately show False
      by auto
  qed
qed


lemma no_infinite_computation_implies_wf: 
  assumes not_inf: "\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>)"
  shows "wf {(c2,c1). \<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma> \<turnstile> c1 \<rightarrow> c2}"
proof (simp only: wf_iff_no_infinite_down_chain,clarify, simp)
  fix f
  assume "\<forall>i. \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
  hence "\<exists>f. f 0 = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
    by (rule renumber [to_pred])
  moreover from not_inf
  have "\<not> (\<exists>f. f 0 = (c, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
    by (simp add: inf_def)
  ultimately show False
    by simp
qed

lemma not_final_Stuck_step: "\<not> final (c,Stuck) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Stuck) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Abrupt_step: 
  "\<not> final (c,Abrupt s) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Abrupt s) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Fault_step: 
  "\<not> final (c,Fault f) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Fault f) \<rightarrow> (c',s')"
by (induct c) (fastforce intro: step.intros simp add: final_def)+

lemma not_final_Normal_step: 
  "\<not> final (c,Normal s) \<Longrightarrow> \<exists>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c',s')"
proof (induct c) 
  case Skip thus ?case by (fastforce intro: step.intros simp add: final_def)
next
  case Basic thus ?case by (fastforce intro: step.intros)
next
  case (Spec r)
  thus ?case
    by (cases "\<exists>t. (s,t) \<in> r") (fastforce intro: step.intros)+
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case
    by (cases "final (c\<^sub>1,Normal s)") (fastforce intro: step.intros simp add: final_def)+
next
  case (Cond b c1 c2)
  show ?case
    by (cases "s \<in> b") (fastforce intro: step.intros)+
next
  case (While b c)
  show ?case
    by (cases "s \<in> b") (fastforce intro: step.intros)+
next
  case (Call p)
  show ?case
  by (cases "\<Gamma> p") (fastforce intro: step.intros)+
next
  case DynCom thus ?case by (fastforce intro: step.intros)
next
  case (Guard f g c)
  show ?case
    by (cases "s \<in> g") (fastforce intro: step.intros)+
next
  case Throw
  thus ?case by (fastforce intro: step.intros simp add: final_def)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  thus ?case
    by (cases "final (c\<^sub>1,Normal s)") (fastforce intro: step.intros simp add: final_def)+
qed

lemma final_termi:
"final (c,s) \<Longrightarrow> \<Gamma>\<turnstile>c\<down>s"
  by (cases s) (auto simp add: final_def terminates.intros)


lemma split_computation: 
assumes steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c\<^sub>f, s\<^sub>f)"
assumes not_final: "\<not> final (c,s)"
assumes final: "final (c\<^sub>f,s\<^sub>f)"
shows "\<exists>c' s'. \<Gamma>\<turnstile> (c, s) \<rightarrow> (c',s') \<and> \<Gamma>\<turnstile> (c', s') \<rightarrow>\<^sup>* (c\<^sub>f, s\<^sub>f)"
using steps not_final final
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c' s')
  thus ?case by auto
qed

lemma wf_implies_termi_reach_step_case:
assumes hyp: "\<And>c' s'. \<Gamma>\<turnstile> (c, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'"
shows "\<Gamma>\<turnstile>c \<down> Normal s"
using hyp
proof (induct c)
  case Skip show ?case by (fastforce intro: terminates.intros)
next
  case Basic show ?case by (fastforce intro: terminates.intros)
next
  case (Spec r)
  show ?case
    by (cases "\<exists>t. (s,t)\<in>r") (fastforce intro: terminates.intros)+
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (rule terminates.Seq)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c' c\<^sub>2, s')"
          by (rule step.Seq)
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Seq c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    }
    from Seq.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s".
  next
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        hence "c\<^sub>1=Skip \<or> c\<^sub>1=Throw"
          by (simp add: final_def)
        thus ?thesis
        proof
          assume Skip: "c\<^sub>1=Skip"
          have "\<Gamma>\<turnstile>(Seq Skip c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
            by (rule step.SeqSkip)
          from hyp [simplified Skip, OF this]
          have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s" .
          moreover from exec_c\<^sub>1 Skip
          have "s'=Normal s"
            by (auto elim: exec_Normal_elim_cases)
          ultimately show ?thesis by simp
        next
          assume Throw: "c\<^sub>1=Throw"
          with exec_c\<^sub>1 have "s'=Abrupt s"
            by (auto elim: exec_Normal_elim_cases)
          thus ?thesis
            by auto
        qed
      next
        case False
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (c\<^sub>f, t)" and
          fin:"(case s' of
                 Abrupt x \<Rightarrow> c\<^sub>f = Throw \<and> t = Normal x
                | _ \<Rightarrow> c\<^sub>f = Skip \<and> t = s')"
          by (fastforce split: xstate.splits)
        with fin have final: "final (c\<^sub>f,t)"
          by (cases s') (auto simp add: final_def)
        from split_computation [OF steps_c\<^sub>1 False this]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (c\<^sub>f, t)" 
          by blast
        from step.Seq [OF first]
        have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Seq c'' c\<^sub>2, s'')".
        from hyp [OF this]
        have termi_s'': "\<Gamma>\<turnstile>Seq c'' c\<^sub>2 \<down> s''".
        show ?thesis
        proof (cases s'')
          case (Normal x)
          from termi_s'' [simplified Normal]
          have termi_c\<^sub>2: "\<forall>t. \<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> t"
            by cases
          show ?thesis
          proof (cases "\<exists>x'. s'=Abrupt x'")
            case False
            with fin obtain "c\<^sub>f=Skip" "t=s'"
              by (cases s') auto
            from steps_Skip_impl_exec [OF rest [simplified this]] Normal
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> s'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this]
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" .
          next
            case True
            with fin obtain x' where s': "s'=Abrupt x'" and "c\<^sub>f=Throw" "t=Normal x'"
              by auto
            from steps_Throw_impl_exec [OF rest [simplified this]] Normal 
            have "\<Gamma>\<turnstile> \<langle>c'',Normal x\<rangle> \<Rightarrow> Abrupt x'"
              by simp
            from termi_c\<^sub>2 [rule_format, OF this] s'
            show "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" by simp
          qed
        next
          case (Abrupt x)
          from steps_Abrupt_prop [OF rest this]
          have "t=Abrupt x" by simp
          with fin have "s'=Abrupt x"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case (Fault f)
          from steps_Fault_prop [OF rest this]
          have "t=Fault f" by simp
          with fin have "s'=Fault f"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        next
          case Stuck
          from steps_Stuck_prop [OF rest this]
          have "t=Stuck" by simp
          with fin have "s'=Stuck"
            by (cases s') auto
          thus "\<Gamma>\<turnstile>c\<^sub>2 \<down> s'" 
            by auto
        qed
      qed
    qed
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>1, Normal s)"
      by (rule step.CondTrue)
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    then have "\<Gamma>\<turnstile> (Cond b c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c\<^sub>2, Normal s)"
      by (rule step.CondFalse)
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s".
    with False show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (While b c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>b") 
    case True
    then have "\<Gamma>\<turnstile> (While b c, Normal s) \<rightarrow> (Seq c (While b c), Normal s)"
      by (rule step.WhileTrue)
    from hyp [OF this] have "\<Gamma>\<turnstile>(Seq c (While b c)) \<down> Normal s".
    with True show ?thesis
      by (auto elim: terminates_Normal_elim_cases intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (Call p)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "\<Gamma> p")
    case None
    thus ?thesis
      by (auto intro: terminates.intros)
  next
    case (Some bdy)
    then have "\<Gamma>\<turnstile> (Call p, Normal s) \<rightarrow> (bdy, Normal s)"
      by (rule step.Call)
    from hyp [OF this] have "\<Gamma>\<turnstile>bdy \<down> Normal s".
    with Some show ?thesis
      by (auto intro: terminates.intros)
  qed
next
  case (DynCom c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  have "\<Gamma>\<turnstile> (DynCom c, Normal s) \<rightarrow> (c s, Normal s)"
    by (rule step.DynCom)
  from hyp [OF this] have "\<Gamma>\<turnstile>c s \<down> Normal s".
  then show ?case
    by (auto intro: terminates.intros)
next
  case (Guard f g c)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (cases "s\<in>g")
    case True
    then have "\<Gamma>\<turnstile> (Guard f g c, Normal s) \<rightarrow> (c, Normal s)"
      by (rule step.Guard)
    from hyp [OF this] have "\<Gamma>\<turnstile>c\<down> Normal s".
    with True show ?thesis
      by (auto intro: terminates.intros)
  next
    case False
    thus ?thesis
      by (auto intro: terminates.intros)
  qed
next  
  case Throw show ?case by (auto intro: terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have hyp: "\<And>c' s'. \<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma>\<turnstile>c' \<down> s'" by fact
  show ?case
  proof (rule terminates.Catch)
    {
      fix c' s'
      assume step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c', s')"
      have "\<Gamma>\<turnstile>c' \<down> s'"
      proof -
        from step_c\<^sub>1
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c' c\<^sub>2, s')"
          by (rule step.Catch)
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Catch c' c\<^sub>2 \<down> s'".
        thus "\<Gamma>\<turnstile>c'\<down> s'"
          by cases auto
      qed
    }
    from Catch.hyps (1) [OF this]
    show "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s".
  next  
    show "\<forall>s'. \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s' \<longrightarrow> \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
    proof (intro allI impI)
      fix s'
      assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s'"
      show "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s'"
      proof (cases "final (c\<^sub>1,Normal s)")
        case True
        with exec_c\<^sub>1
        have Throw: "c\<^sub>1=Throw"
          by (auto simp add: final_def elim: exec_Normal_elim_cases)
        have "\<Gamma>\<turnstile>(Catch Throw c\<^sub>2,Normal s) \<rightarrow> (c\<^sub>2,Normal s)"
          by (rule step.CatchThrow)
        from hyp [simplified Throw, OF this]
        have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s".
        moreover from exec_c\<^sub>1 Throw
        have "s'=s"
          by (auto elim: exec_Normal_elim_cases)
        ultimately show ?thesis by simp
      next
        case False
        from exec_impl_steps [OF exec_c\<^sub>1]
        obtain c\<^sub>f t where 
          steps_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (fastforce split: xstate.splits)
        from split_computation [OF steps_c\<^sub>1 False]
        obtain c'' s'' where
          first: "\<Gamma>\<turnstile> (c\<^sub>1, Normal s) \<rightarrow> (c'', s'')" and
          rest: "\<Gamma>\<turnstile> (c'', s'') \<rightarrow>\<^sup>* (Throw, Normal s')" 
          by (auto simp add: final_def)
        from step.Catch [OF first]
        have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, Normal s) \<rightarrow> (Catch c'' c\<^sub>2, s'')".
        from hyp [OF this]
        have "\<Gamma>\<turnstile>Catch c'' c\<^sub>2 \<down> s''".
        moreover
        from steps_Throw_impl_exec [OF rest]
        have "\<Gamma>\<turnstile> \<langle>c'',s''\<rangle> \<Rightarrow> Abrupt s'".
        moreover
        from rest obtain x where "s''=Normal x"
          by (cases s'')
             (auto dest: steps_Fault_prop steps_Abrupt_prop steps_Stuck_prop)
        ultimately show ?thesis
          by (fastforce elim: terminates_elim_cases)
      qed
    qed
  qed
qed

lemma wf_implies_termi_reach:
assumes wf: "wf {(cfg2,cfg1). \<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* cfg1 \<and> \<Gamma> \<turnstile> cfg1 \<rightarrow> cfg2}"
shows "\<And>c1 s1. \<lbrakk>\<Gamma> \<turnstile> (c,s) \<rightarrow>\<^sup>* cfg1;  cfg1=(c1,s1)\<rbrakk>\<Longrightarrow> \<Gamma>\<turnstile>c1\<down>s1"
using wf 
proof (induct cfg1, simp)
  fix c1 s1
  assume reach: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c1, s1)"
  assume hyp_raw: "\<And>y c2 s2.
           \<lbrakk>\<Gamma>\<turnstile> (c1, s1) \<rightarrow> (c2, s2); \<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>* (c2, s2); y = (c2, s2)\<rbrakk>
           \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
  have hyp: "\<And>c2 s2. \<Gamma>\<turnstile> (c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> \<Gamma>\<turnstile>c2 \<down> s2"
    apply -
    apply (rule hyp_raw)
    apply   assumption
    using reach 
    apply  simp
    apply (rule refl)
    done

  show "\<Gamma>\<turnstile>c1 \<down> s1"
  proof (cases s1)
    case (Normal s1')
    with wf_implies_termi_reach_step_case [OF hyp [simplified Normal]] 
    show ?thesis
      by auto
  qed (auto intro: terminates.intros)
qed

theorem no_infinite_computation_impl_terminates:
  assumes not_inf: "\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>)"
  shows "\<Gamma>\<turnstile>c\<down>s"
proof -
  from no_infinite_computation_implies_wf [OF not_inf]
  have wf: "wf {(c2, c1). \<Gamma>\<turnstile>(c, s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma>\<turnstile>c1 \<rightarrow> c2}".
  show ?thesis
    by (rule wf_implies_termi_reach [OF wf]) auto
qed

corollary terminates_iff_no_infinite_computation: 
  "\<Gamma>\<turnstile>c\<down>s = (\<not> \<Gamma>\<turnstile> (c, s) \<rightarrow> \<dots>(\<infinity>))"
  apply (rule)
  apply  (erule terminates_impl_no_infinite_computation)
  apply (erule no_infinite_computation_impl_terminates)
  done

(* ************************************************************************* *)
subsection {* Generalised Redexes *} 
(* ************************************************************************* *)

text {*
For an important lemma for the completeness proof of the Hoare-logic for
total correctness we need a generalisation of @{const "redex"} that not only
yield the redex itself but all the enclosing statements as well.
*}

primrec redexes:: "('s,'p,'f)com \<Rightarrow> ('s,'p,'f)com set"
where
"redexes Skip = {Skip}" |
"redexes (Basic f) = {Basic f}" |
"redexes (Spec r) = {Spec r}" |
"redexes (Seq c\<^sub>1 c\<^sub>2) = {Seq c\<^sub>1 c\<^sub>2} \<union> redexes c\<^sub>1" |
"redexes (Cond b c\<^sub>1 c\<^sub>2) = {Cond b c\<^sub>1 c\<^sub>2}" |
"redexes (While b c) = {While b c}" |
"redexes (Call p) = {Call p}" |
"redexes (DynCom d) = {DynCom d}" |
"redexes (Guard f b c) = {Guard f b c}" |
"redexes (Throw) = {Throw}" |
"redexes (Catch c\<^sub>1 c\<^sub>2) = {Catch c\<^sub>1 c\<^sub>2} \<union> redexes c\<^sub>1"

lemma root_in_redexes: "c \<in> redexes c"
  apply (induct c)
  apply auto
  done

lemma redex_in_redexes: "redex c \<in> redexes c"
  apply (induct c)
  apply auto
  done

lemma redex_redexes: "\<And>c'. \<lbrakk>c' \<in> redexes c; redex c' = c'\<rbrakk> \<Longrightarrow> redex c = c'" 
  apply (induct c)
  apply auto
  done

lemma step_redexes:
  shows "\<And>r r'. \<lbrakk>\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s'); r \<in> redexes c\<rbrakk> 
  \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> r' \<in> redexes c'"
proof (induct c)
  case Skip thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case Basic thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case Spec thus ?case by (fastforce intro: step.intros elim: step_elim_cases)
next
  case (Seq c\<^sub>1 c\<^sub>2)
  have "r \<in> redexes (Seq c\<^sub>1 c\<^sub>2)" by fact
  hence r: "r = Seq c\<^sub>1 c\<^sub>2 \<or> r \<in> redexes c\<^sub>1"
    by simp
  have step_r: "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  from r show ?case
  proof 
    assume "r = Seq c\<^sub>1 c\<^sub>2"
    with step_r
    show ?case
      by (auto simp add: root_in_redexes)
  next
    assume r: "r \<in> redexes c\<^sub>1"
    from Seq.hyps (1) [OF step_r this] 
    obtain c' where 
      step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c', s')" and
      r': "r' \<in> redexes c'"
      by blast
    from step.Seq [OF step_c\<^sub>1]
    have "\<Gamma>\<turnstile> (Seq c\<^sub>1 c\<^sub>2, s) \<rightarrow> (Seq c' c\<^sub>2, s')".
    with r'
    show ?case
      by auto
  qed
next
  case Cond 
  thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case While 
  thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Call thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case DynCom thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Guard thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case Throw thus ?case 
    by (fastforce intro: step.intros elim: step_elim_cases simp add: root_in_redexes)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have "r \<in> redexes (Catch c\<^sub>1 c\<^sub>2)" by fact
  hence r: "r = Catch c\<^sub>1 c\<^sub>2 \<or> r \<in> redexes c\<^sub>1"
    by simp
  have step_r: "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" by fact
  from r show ?case
  proof 
    assume "r = Catch c\<^sub>1 c\<^sub>2"
    with step_r
    show ?case
      by (auto simp add: root_in_redexes)
  next
    assume r: "r \<in> redexes c\<^sub>1"
    from Catch.hyps (1) [OF step_r this] 
    obtain c' where 
      step_c\<^sub>1: "\<Gamma>\<turnstile> (c\<^sub>1, s) \<rightarrow> (c', s')" and
      r': "r' \<in> redexes c'"
      by blast
    from step.Catch [OF step_c\<^sub>1]
    have "\<Gamma>\<turnstile> (Catch c\<^sub>1 c\<^sub>2, s) \<rightarrow> (Catch c' c\<^sub>2, s')".
    with r'
    show ?case
      by auto
  qed
qed 

lemma steps_redexes:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. r \<in> redexes c \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> r' \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then
  show "\<exists>c'. \<Gamma>\<turnstile> (c, s') \<rightarrow>\<^sup>* (c', s') \<and> r' \<in> redexes c'"
    by auto
next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "r \<in> redexes c" by fact+
  from step_redexes [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "r'' \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "r' \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed



lemma steps_redexes':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. r \<in> redexes c \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> r' \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "r \<in> redexes c'" by fact+
  from step_redexes [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "r' \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "r'' \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma step_redexes_Seq:
  assumes step: "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s')"
  assumes Seq: "Seq r c\<^sub>2 \<in> redexes c"
  shows "\<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
proof -
  from step.Seq [OF step]
  have "\<Gamma>\<turnstile> (Seq r c\<^sub>2, s) \<rightarrow> (Seq r' c\<^sub>2, s')".
  from step_redexes [OF this Seq] 
  show ?thesis .
qed

lemma steps_redexes_Seq:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. Seq r c\<^sub>2 \<in> redexes c \<Longrightarrow> 
              \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then show ?case
    by (auto)

next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "Seq r c\<^sub>2 \<in> redexes c" by fact+
  from step_redexes_Seq [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "Seq r'' c\<^sub>2 \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "Seq r' c\<^sub>2 \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed

lemma steps_redexes_Seq':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. Seq r c\<^sub>2 \<in> redexes c 
             \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> Seq r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "Seq r c\<^sub>2 \<in> redexes c'" by fact+
  from step_redexes_Seq [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "Seq r' c\<^sub>2 \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes_Seq [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "Seq r'' c\<^sub>2 \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma step_redexes_Catch:
  assumes step: "\<Gamma>\<turnstile>(r,s) \<rightarrow> (r',s')"
  assumes Catch: "Catch r c\<^sub>2 \<in> redexes c"
  shows "\<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow> (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
proof -
  from step.Catch [OF step]
  have "\<Gamma>\<turnstile> (Catch r c\<^sub>2, s) \<rightarrow> (Catch r' c\<^sub>2, s')".
  from step_redexes [OF this Catch] 
  show ?thesis .
qed

lemma steps_redexes_Catch:
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>* (r', s')"
  shows "\<And>c. Catch r c\<^sub>2 \<in> redexes c \<Longrightarrow> 
              \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>* (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl
  then show ?case
    by (auto)

next
  case (Trans r s r'' s'')
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r'', s'')" "Catch r c\<^sub>2 \<in> redexes c" by fact+
  from step_redexes_Catch [OF this]
  obtain c' where
    step: "\<Gamma>\<turnstile> (c, s) \<rightarrow> (c', s'')" and
    r'': "Catch r'' c\<^sub>2 \<in> redexes c'"
    by blast
  note step
  also
  from Trans.hyps (3) [OF r'']
  obtain c'' where
    steps: "\<Gamma>\<turnstile> (c', s'') \<rightarrow>\<^sup>* (c'', s')" and
    r': "Catch r' c\<^sub>2 \<in> redexes c''"
    by blast
  note steps
  finally
  show ?case
    using r'
    by blast
qed

lemma steps_redexes_Catch':
  assumes steps: "\<Gamma>\<turnstile> (r, s) \<rightarrow>\<^sup>+ (r', s')"
  shows "\<And>c. Catch r c\<^sub>2 \<in> redexes c 
             \<Longrightarrow> \<exists>c'. \<Gamma>\<turnstile>(c,s) \<rightarrow>\<^sup>+ (c',s') \<and> Catch r' c\<^sub>2 \<in> redexes c'"
using steps 
proof (induct rule: tranclp_induct2 [consumes 1, case_names Step Trans])
  case (Step r' s' c') 
  have "\<Gamma>\<turnstile> (r, s) \<rightarrow> (r', s')" "Catch r c\<^sub>2 \<in> redexes c'" by fact+
  from step_redexes_Catch [OF this]
  show ?case
    by (blast intro: r_into_trancl)
next
  case (Trans r' s' r'' s'')
  from Trans obtain c' where
    steps: "\<Gamma>\<turnstile> (c, s) \<rightarrow>\<^sup>+ (c', s')" and
    r': "Catch r' c\<^sub>2 \<in> redexes c'"
    by blast
  note steps
  moreover
  have "\<Gamma>\<turnstile> (r', s') \<rightarrow> (r'', s'')" by fact
  from step_redexes_Catch [OF this r'] obtain c'' where
    step: "\<Gamma>\<turnstile> (c', s') \<rightarrow> (c'', s'')" and
    r'': "Catch r'' c\<^sub>2 \<in> redexes c''"
    by blast
  note step
  finally show ?case
    using r'' by blast
qed

lemma redexes_subset:"\<And>c'. c' \<in> redexes c \<Longrightarrow> redexes c' \<subseteq> redexes c"
  by (induct c) auto

lemma redexes_preserves_termination:
  assumes termi: "\<Gamma>\<turnstile>c\<down>s"
  shows "\<And>c'. c' \<in> redexes c \<Longrightarrow> \<Gamma>\<turnstile>c'\<down>s"  
using termi
by induct (auto intro: terminates.intros)


end