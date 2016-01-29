(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      HoarePartialDef.thy
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

section {* Hoare Logic for Partial Correctness *}
theory HoarePartialDef imports Semantic begin

type_synonym ('s,'p) quadruple = "('s assn \<times> 'p \<times> 's assn \<times> 's assn)"

subsection {* Validity of Hoare Tuples: @{text "\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"} *}

definition
  valid :: "[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com,'s assn,'s assn] => bool"
                ("_\<Turnstile>\<^bsub>'/_\<^esub>/ _ _ _,_"  [61,60,1000, 20, 1000,1000] 60)
where
 "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<equiv> \<forall>s t. \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t \<longrightarrow> s \<in> Normal ` P \<longrightarrow> t \<notin> Fault ` F  
                      \<longrightarrow>  t \<in>  Normal ` Q \<union> Abrupt ` A"

definition
  cvalid::
  "[('s,'p,'f) body,('s,'p) quadruple set,'f set,
      's assn,('s,'p,'f) com,'s assn,'s assn] =>bool"
                ("_,_\<Turnstile>\<^bsub>'/_\<^esub>/ _ _ _,_"  [61,60,60,1000, 20, 1000,1000] 60)
where
 "\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<equiv> (\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A) \<longrightarrow> \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P c Q,A"


definition
  nvalid :: "[('s,'p,'f) body,nat,'f set, 
                's assn,('s,'p,'f) com,'s assn,'s assn] => bool"
                ("_\<Turnstile>_:\<^bsub>'/_\<^esub>/ _ _ _,_"  [61,60,60,1000, 20, 1000,1000] 60)
where
 "\<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A \<equiv> \<forall>s t. \<Gamma>\<turnstile>\<langle>c,s \<rangle> =n\<Rightarrow> t \<longrightarrow> s \<in> Normal ` P \<longrightarrow> t \<notin> Fault ` F 
                        \<longrightarrow> t \<in>  Normal ` Q \<union> Abrupt ` A"


definition
  cnvalid::
  "[('s,'p,'f) body,('s,'p) quadruple set,nat,'f set, 
     's assn,('s,'p,'f) com,'s assn,'s assn] \<Rightarrow> bool"
                ("_,_\<Turnstile>_:\<^bsub>'/_\<^esub>/ _ _ _,_"  [61,60,60,60,1000, 20, 1000,1000] 60)
where
 "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A \<equiv> (\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A) \<longrightarrow> \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"


notation (ASCII)
  valid  ("_|='/_/ _ _ _,_"  [61,60,1000, 20, 1000,1000] 60) and
  cvalid  ("_,_|='/_/ _ _ _,_"  [61,60,60,1000, 20, 1000,1000] 60) and
  nvalid  ("_|=_:'/_/ _ _ _,_"  [61,60,60,1000, 20, 1000,1000] 60) and
  cnvalid  ("_,_|=_:'/_/ _ _ _,_"  [61,60,60,60,1000, 20, 1000,1000] 60)


subsection {*Properties of Validity *}

lemma valid_iff_nvalid: "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A = (\<forall>n. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A)"
  apply (simp only: valid_def nvalid_def exec_iff_execn )
  apply (blast dest: exec_final_notin_to_execn)
  done
 
lemma cnvalid_to_cvalid: "(\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A) \<Longrightarrow> \<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  apply (unfold cvalid_def cnvalid_def valid_iff_nvalid [THEN eq_reflection])
  apply fast
  done

lemma nvalidI: 
 "\<lbrakk>\<And>s t. \<lbrakk>\<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> =n\<Rightarrow> t;s \<in> P; t\<notin> Fault ` F\<rbrakk> \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A\<rbrakk>
  \<Longrightarrow> \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  by (auto simp add: nvalid_def)

lemma validI: 
 "\<lbrakk>\<And>s t. \<lbrakk>\<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> \<Rightarrow> t;s \<in> P; t\<notin>Fault ` F\<rbrakk> \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A\<rbrakk>
  \<Longrightarrow> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  by (auto simp add: valid_def)

lemma cvalidI: 
 "\<lbrakk>\<And>s t. \<lbrakk>\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A;\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t;s \<in> P;t\<notin>Fault ` F\<rbrakk> 
          \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A\<rbrakk>
  \<Longrightarrow> \<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  by (auto simp add: cvalid_def valid_def)

lemma cvalidD: 
 "\<lbrakk>\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A;\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A;\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t;s \<in> P;t\<notin>Fault ` F\<rbrakk> 
  \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A"
  by (auto simp add: cvalid_def valid_def)

lemma cnvalidI: 
 "\<lbrakk>\<And>s t. \<lbrakk>\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A;
   \<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> =n\<Rightarrow> t;s \<in> P;t\<notin>Fault ` F\<rbrakk> 
          \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A\<rbrakk>
  \<Longrightarrow> \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  by (auto simp add: cnvalid_def nvalid_def)


lemma cnvalidD: 
 "\<lbrakk>\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A;\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A;
   \<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> =n\<Rightarrow> t;s \<in> P;
   t\<notin>Fault ` F\<rbrakk> 
  \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A"
  by (auto simp add: cnvalid_def nvalid_def)

lemma nvalid_augment_Faults:
  assumes validn:"\<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  assumes F': "F \<subseteq> F'"
  shows "\<Gamma>\<Turnstile>n:\<^bsub>/F'\<^esub> P c Q,A"
proof (rule nvalidI)
  fix s t
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P"
  assume F: "t \<notin> Fault ` F'"
  with F' have "t \<notin> Fault ` F"
    by blast
  with exec P validn
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
    by (auto simp add: nvalid_def)
qed

lemma valid_augment_Faults:
  assumes validn:"\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  assumes F': "F \<subseteq> F'"
  shows "\<Gamma>\<Turnstile>\<^bsub>/F'\<^esub> P c Q,A"
proof (rule validI)
  fix s t
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P"
  assume F: "t \<notin> Fault ` F'"
  with F' have "t \<notin> Fault ` F"
    by blast
  with exec P validn
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
    by (auto simp add: valid_def)
qed

lemma nvalid_to_nvalid_strip:
  assumes validn:"\<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  assumes F': "F' \<subseteq> -F"
  shows "strip F' \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
proof (rule nvalidI)
  fix s t
  assume exec_strip: "strip F' \<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P"
  assume F: "t \<notin> Fault ` F"
  from exec_strip obtain t' where
    exec: "\<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> =n\<Rightarrow> t'" and
    t': "t' \<in> Fault ` (-F') \<longrightarrow> t'=t" "\<not> isFault t' \<longrightarrow> t'=t"
    by (blast dest: execn_strip_to_execn)
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases "t' \<in> Fault ` F")
    case True
    with t' F F' have False
      by blast
    thus ?thesis ..
  next
    case False
    with exec P validn
    have "t' \<in> Normal ` Q \<union> Abrupt ` A"
      by (auto simp add: nvalid_def)
    moreover
    from this t' have "t'=t"
      by auto
    ultimately show ?thesis
      by simp
  qed
qed


lemma valid_to_valid_strip:
  assumes valid:"\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  assumes F': "F' \<subseteq> -F"
  shows "strip F' \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
proof (rule validI)
  fix s t
  assume exec_strip: "strip F' \<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P"
  assume F: "t \<notin> Fault ` F"
  from exec_strip obtain t' where
    exec: "\<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> \<Rightarrow> t'" and
    t': "t' \<in> Fault ` (-F') \<longrightarrow> t'=t" "\<not> isFault t' \<longrightarrow> t'=t"
    by (blast dest: exec_strip_to_exec)
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases "t' \<in> Fault ` F")
    case True
    with t' F F' have False
      by blast
    thus ?thesis ..
  next
    case False
    with exec P valid
    have "t' \<in> Normal ` Q \<union> Abrupt ` A"
      by (auto simp add: valid_def)
    moreover
    from this t' have "t'=t"
      by auto
    ultimately show ?thesis
      by simp
  qed
qed


subsection {* The Hoare Rules: @{text "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"} *}

lemma mono_WeakenContext: "A \<subseteq> B \<Longrightarrow>
        (\<lambda>(P, c, Q, A'). (\<Gamma>, \<Theta>, F, P, c, Q, A') \<in> A) x \<longrightarrow>
        (\<lambda>(P, c, Q, A'). (\<Gamma>, \<Theta>, F, P, c, Q, A') \<in> B) x"
apply blast
done


inductive "hoarep"::"[('s,'p,'f) body,('s,'p) quadruple set,'f set,
    's assn,('s,'p,'f) com, 's assn,'s assn] => bool"
    ("(3_,_/\<turnstile>\<^bsub>'/_ \<^esub>(_/ (_)/ _,/_))" [60,60,60,1000,20,1000,1000]60)
  for \<Gamma>::"('s,'p,'f) body"
where
  Skip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> Q Skip Q,A"

| Basic: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. f s \<in> Q} (Basic f) Q,A"

| Spec: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. (\<forall>t. (s,t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s,t) \<in> r)} (Spec r) Q,A"

| Seq: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c\<^sub>1 R,A; \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> R c\<^sub>2 Q,A\<rbrakk>
        \<Longrightarrow>
        \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (Seq c\<^sub>1 c\<^sub>2) Q,A"
  
| Cond: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<inter> b) c\<^sub>1 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<inter> - b) c\<^sub>2 Q,A\<rbrakk>
         \<Longrightarrow> 
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (Cond b c\<^sub>1 c\<^sub>2) Q,A"

| While: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<inter> b) c P,A
          \<Longrightarrow>
          \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (While b c) (P \<inter> - b),A"

| Guard: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (g \<inter> P) c Q,A
          \<Longrightarrow>
          \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (g \<inter> P) (Guard f g c) Q,A"

| Guarantee: "\<lbrakk>f \<in> F; \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (g \<inter> P) c Q,A\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (Guard f g c) Q,A"

| CallRec:
  "\<lbrakk>(P,p,Q,A) \<in> Specs;  
    \<forall>(P,p,Q,A) \<in> Specs. p \<in> dom \<Gamma> \<and> \<Gamma>,\<Theta>\<union>Specs\<turnstile>\<^bsub>/F\<^esub> P (the (\<Gamma> p)) Q,A \<rbrakk>
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A"

| DynCom:
      "\<forall>s \<in> P. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (c s) Q,A 
      \<Longrightarrow> 
      \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (DynCom c) Q,A"

| Throw: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> A Throw Q,A"

| Catch: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c\<^sub>1 Q,R; \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> R c\<^sub>2 Q,A\<rbrakk> \<Longrightarrow>  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P Catch c\<^sub>1 c\<^sub>2 Q,A"

| Conseq: "\<forall>s \<in> P. \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c Q',A' \<and> s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A 
           \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"


| Asm: "\<lbrakk>(P,p,Q,A) \<in> \<Theta>\<rbrakk>
         \<Longrightarrow> 
         \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A"


| ExFalso: "\<lbrakk>\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A; \<not> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  -- {* This is a hack rule that enables us to derive completeness for
        an arbitrary context @{text "\<Theta>"}, from completeness for an empty context.*}  



text {* Does not work, because of rule ExFalso, the context @{text "\<Theta>"} is to blame.
 A weaker version with empty context can be derived from soundness 
 and completeness later on. *}
lemma hoare_strip_\<Gamma>: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P p Q,A"
  shows "strip (-F) \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P p Q,A"
using deriv 
proof induct
  case Skip thus ?case by (iprover intro: hoarep.Skip)
next
  case Basic thus ?case by (iprover intro: hoarep.Basic)
next
  case Spec thus ?case by (iprover intro: hoarep.Spec)
next
  case Seq thus ?case by (iprover intro: hoarep.Seq)
next
  case Cond thus ?case by (iprover intro: hoarep.Cond)
next
  case While thus ?case by (iprover intro: hoarep.While)
next
  case Guard thus ?case by (iprover intro: hoarep.Guard)
(*next
  case CallSpec thus ?case by (iprover intro: hoarep.CallSpec)
next
  case (CallRec A Abr Abr' Init P Post Pre Procs Q R Result Return Z \<Gamma> \<Theta> init p
         result return )
  from CallRec.hyps
  have "\<forall>p\<in>Procs. \<forall>Z. (strip \<Gamma>),\<Theta> \<union>
             (\<Union>\<^bsub>p\<in>Procs\<^esub>
                 \<Union>\<^bsub>Z\<^esub> {(Pre p Z, Call (Init p) p (Return p) (Result p),
                      Post p Z, Abr p Z)})\<turnstile>
            (Pre p Z) (the (\<Gamma> p)) (R p Z),(Abr' p Z)" by blast
  hence "\<forall>p\<in>Procs. \<forall>Z. (strip \<Gamma>),\<Theta> \<union>
             (\<Union>\<^bsub>p\<in>Procs\<^esub>
                 \<Union>\<^bsub>Z\<^esub> {(Pre p Z, Call (Init p) p (Return p) (Result p),
                      Post p Z, Abr p Z)})\<turnstile>
            (Pre p Z) (the ((strip \<Gamma>) p)) (R p Z),(Abr' p Z)"
    by (auto intro: hoarep.StripI)
  then show ?case
    apply - 
    apply (rule hoarep.CallRec)
    apply (assumption | simp only:dom_strip)+
    done*)
next
  case DynCom 
  thus ?case
    by - (rule hoarep.DynCom,best  elim!: ballE exE)
next
  case Throw thus ?case by (iprover intro: hoarep.Throw)
next
  case Catch thus ?case by (iprover intro: hoarep.Catch)
(*next 
  case CONSEQ thus ?case apply (auto intro: hoarep.CONSEQ)*)
next
  case Asm thus ?case by (iprover intro: hoarep.Asm)
next
  case ExFalso
  thus ?case
    oops

lemma hoare_augment_context: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P p Q,A"
  shows "\<And>\<Theta>'. \<Theta> \<subseteq> \<Theta>' \<Longrightarrow> \<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P p Q,A"
using deriv
proof (induct)
  case CallRec
  case (CallRec P p Q A Specs \<Theta> F \<Theta>')
  from CallRec.prems
  have "\<Theta>\<union>Specs
       \<subseteq> \<Theta>'\<union>Specs"
    by blast
  with CallRec.hyps (2) 
  have "\<forall>(P,p,Q,A)\<in>Specs.  p \<in> dom \<Gamma> \<and> \<Gamma>,\<Theta>'\<union>Specs \<turnstile>\<^bsub>/F\<^esub> P  (the (\<Gamma> p)) Q,A"
    by fastforce

  with CallRec show ?case by - (rule hoarep.CallRec)
next
  case DynCom thus ?case by (blast intro: hoarep.DynCom)
next
  case (Conseq P \<Theta> F c Q A \<Theta>')
  from Conseq
  have "\<forall>s \<in> P. 
         (\<exists>P' Q' A'. \<Gamma>,\<Theta>' \<turnstile>\<^bsub>/F\<^esub> P' c Q',A' \<and> s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A)"
    by blast
  with Conseq show ?case by - (rule hoarep.Conseq)
next
  case (ExFalso \<Theta> F P c Q A \<Theta>')
  have valid_ctxt: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A" "\<Theta> \<subseteq> \<Theta>'" by fact+
  hence "\<forall>n. \<Gamma>,\<Theta>'\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
    by (simp add: cnvalid_def) blast
  moreover have invalid: "\<not> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"  by fact
  ultimately show ?case
    by (rule hoarep.ExFalso)
qed (blast intro: hoarep.intros)+


subsection {* Some Derived Rules *}

lemma  Conseq': "\<forall>s. s \<in> P \<longrightarrow> 
            (\<exists>P' Q' A'. 
              (\<forall> Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)) \<and>
                    (\<exists>Z. s \<in> P' Z \<and> (Q' Z \<subseteq> Q) \<and> (A' Z \<subseteq> A)))
           \<Longrightarrow>
           \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
apply (rule Conseq)
apply (rule ballI)
apply (erule_tac x=s in allE)
apply (clarify)
apply (rule_tac x="P' Z" in exI)
apply (rule_tac x="Q' Z" in exI)
apply (rule_tac x="A' Z" in exI)
apply blast
done

lemma conseq:"\<lbrakk>\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z);
              \<forall>s. s \<in> P \<longrightarrow> (\<exists> Z. s\<in>P' Z \<and> (Q' Z \<subseteq> Q) \<and> (A' Z \<subseteq> A))\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  by (rule Conseq) blast

theorem conseqPrePost [trans]: 
  "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c Q',A' \<Longrightarrow> P \<subseteq> P' \<Longrightarrow>  Q' \<subseteq> Q \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>  \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  by (rule conseq [where ?P'="\<lambda>Z. P'" and ?Q'="\<lambda>Z. Q'"]) auto

lemma conseqPre [trans]: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c Q,A \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
by (rule conseq) auto

lemma conseqPost [trans]: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q',A' \<Longrightarrow> Q' \<subseteq> Q \<Longrightarrow> A' \<subseteq> A 
 \<Longrightarrow>   \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  by (rule conseq) auto


lemma CallRec': 
  "\<lbrakk>p\<in>Procs; Procs \<subseteq> dom \<Gamma>;
   \<forall>p\<in>Procs. 
    \<forall>Z. \<Gamma>,\<Theta> \<union> (\<Union>p\<in>Procs. \<Union>Z. {((P p Z),p,Q p Z,A p Z)})
        \<turnstile>\<^bsub>/F\<^esub> (P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)\<rbrakk>
   \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P p Z) (Call p) (Q p Z),(A p Z)"
apply (rule CallRec [where Specs="\<Union>p\<in>Procs. \<Union>Z. {((P p Z),p,Q p Z,A p Z)}"])
apply  blast
apply blast
done

end 