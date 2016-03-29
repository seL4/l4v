(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      HoareTotalDef.thy
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

section {* Hoare Logic for Total Correctness *}

theory HoareTotalDef imports HoarePartialDef Termination begin 

subsection {* Validity of Hoare Tuples: @{text  "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"} *}

definition
  validt :: "[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com,'s assn,'s assn] \<Rightarrow> bool"
                ("_\<Turnstile>\<^sub>t\<^bsub>'/_\<^esub>/ _ _ _,_"  [61,60,1000, 20, 1000,1000] 60)
where
 "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<equiv> \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<and> (\<forall>s \<in> Normal ` P. \<Gamma>\<turnstile>c\<down>s)"

definition
  cvalidt::
  "[('s,'p,'f) body,('s,'p) quadruple set,'f set,
    's assn,('s,'p,'f) com,'s assn,'s assn] \<Rightarrow> bool"
                ("_,_\<Turnstile>\<^sub>t\<^bsub>'/_\<^esub>/ _ _ _,_"  [61,60, 60,1000, 20, 1000,1000] 60)
where
 "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<equiv> (\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A) \<longrightarrow> \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"



notation (ASCII)
  validt  ("_|=t'/_/ _ _ _,_"  [61,60,1000, 20, 1000,1000] 60) and
  cvalidt  ("_,_|=t'/_ / _ _ _,_"  [61,60,60,1000, 20, 1000,1000] 60)

subsection {* Properties of Validity *}

lemma validtI: 
 "\<lbrakk>\<And>s t. \<lbrakk>\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t;s \<in> P;t \<notin> Fault ` F\<rbrakk> \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A;
   \<And>s. s \<in> P \<Longrightarrow> \<Gamma>\<turnstile> c\<down>(Normal s) \<rbrakk>
  \<Longrightarrow> \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (auto simp add: validt_def valid_def)

lemma cvalidtI: 
 "\<lbrakk>\<And>s t. \<lbrakk>\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A;\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t;s \<in> P; 
          t \<notin> Fault ` F\<rbrakk> 
          \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A;
   \<And>s. \<lbrakk>\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A; s\<in>P\<rbrakk> \<Longrightarrow>  \<Gamma>\<turnstile>c\<down>(Normal s)\<rbrakk>
  \<Longrightarrow> \<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (auto simp add: cvalidt_def validt_def valid_def)

lemma cvalidt_postD: 
 "\<lbrakk>\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A; \<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A;\<Gamma>\<turnstile>\<langle>c,Normal s \<rangle> \<Rightarrow> t;
   s \<in> P;t \<notin> Fault ` F\<rbrakk> 
  \<Longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A"
  by (simp add: cvalidt_def validt_def valid_def)

lemma cvalidt_termD: 
 "\<lbrakk>\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A; \<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A;s \<in> P\<rbrakk> 
  \<Longrightarrow> \<Gamma>\<turnstile>c\<down>(Normal s)"
  by (simp add: cvalidt_def validt_def valid_def)


lemma validt_augment_Faults:
  assumes valid:"\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes F': "F \<subseteq> F'"
  shows "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F'\<^esub> P c Q,A"
  using valid F'
  by (auto intro: valid_augment_Faults simp add: validt_def)

subsection {* The Hoare Rules: @{text "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" } *}

inductive "hoaret"::"[('s,'p,'f) body,('s,'p) quadruple set,'f set,
                        's assn,('s,'p,'f) com,'s assn,'s assn] 
                       => bool"
    ("(3_,_/\<turnstile>\<^sub>t\<^bsub>'/_\<^esub> (_/ (_)/ _,_))" [61,60,60,1000,20,1000,1000]60)  
   for \<Gamma>::"('s,'p,'f) body"
where
  Skip: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> Q Skip Q,A"

| Basic: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. f s \<in> Q} (Basic f) Q,A"

| Spec: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. (\<forall>t. (s,t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s,t) \<in> r)} (Spec r) Q,A"

| Seq: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 R,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A\<rbrakk>
        \<Longrightarrow>
        \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Seq c\<^sub>1 c\<^sub>2 Q,A"
  
| Cond: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P \<inter> b) c\<^sub>1 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P \<inter> - b) c\<^sub>2 Q,A\<rbrakk>
         \<Longrightarrow> 
         \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c\<^sub>1 c\<^sub>2) Q,A"

| While: "\<lbrakk>wf r; \<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P \<inter> b) c ({t. (t,\<sigma>)\<in>r} \<inter> P),A\<rbrakk>
          \<Longrightarrow>
          \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (While b c) (P \<inter> - b),A"

| Guard: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> P) c Q,A
          \<Longrightarrow>
          \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> P) Guard f g c Q,A"

| Guarantee: "\<lbrakk>f \<in> F; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> P) c Q,A\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Guard f g c) Q,A"

| CallRec: 
  "\<lbrakk>(P,p,Q,A) \<in> Specs;
    wf r; 
    Specs_wf = (\<lambda>p \<sigma>. (\<lambda>(P,q,Q,A). (P \<inter> {s. ((s,q),(\<sigma>,p)) \<in> r},q,Q,A)) ` Specs);
    \<forall>(P,p,Q,A)\<in> Specs. 
      p \<in> dom \<Gamma> \<and> (\<forall>\<sigma>. \<Gamma>,\<Theta> \<union> Specs_wf p \<sigma>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P) (the (\<Gamma> p)) Q,A)
    \<rbrakk>
    \<Longrightarrow>
    \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"


| DynCom:  "\<forall>s \<in> P. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (c s) Q,A 
            \<Longrightarrow> 
            \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (DynCom c) Q,A"


| Throw: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> A Throw Q,A"

| Catch: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 Q,R; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A\<rbrakk> \<Longrightarrow>  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Catch c\<^sub>1 c\<^sub>2 Q,A"

| Conseq: "\<forall>s \<in> P. \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q',A' \<and> s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A 
           \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"


| Asm: "(P,p,Q,A) \<in> \<Theta> 
        \<Longrightarrow> 
        \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"

| ExFalso: "\<lbrakk>\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A; \<not> \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  -- {* This is a hack rule that enables us to derive completeness for
        an arbitrary context @{text "\<Theta>"}, from completeness for an empty context.*}

  
text {* Does not work, because of rule ExFalso, the context @{text \<Theta>} is to blame.
 A weaker version with empty context can be derived from soundness 
 later on. *}
lemma hoaret_to_hoarep:
  assumes hoaret: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P p Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P p Q,A"
using hoaret
proof (induct)
  case Skip thus ?case by (rule hoarep.intros)
next
  case Basic thus ?case by (rule hoarep.intros)
next
  case Seq thus ?case by - (rule hoarep.intros)
next
  case Cond thus ?case by - (rule hoarep.intros)
next
  case (While r \<Theta> F P b c A)
  hence "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P \<inter> b) c ({t. (t, \<sigma>) \<in> r} \<inter> P),A"
    by iprover
  hence "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<inter> b) c P,A"
    by (rule HoarePartialDef.conseq) blast
  then show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P While b c (P \<inter> - b),A"
    by (rule hoarep.While)
next
  case Guard thus ?case by - (rule hoarep.intros)
(*next
  case (CallRec A F P Procs Q Z \<Theta>  p r)
  hence hyp: "\<forall>p\<in>Procs. \<forall>\<tau> Z. 
           \<Gamma>,\<Theta> \<union> (\<Union>q\<in>Procs. \<Union>Z. {(P q Z \<inter> {s. ((s, q), \<tau>, p) \<in> r},
                      Call q, Q q Z,A q Z)})\<turnstile>\<^bsub>/F\<^esub>
              ({\<tau>} \<inter> P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)"
    by blast
  have "\<forall>p\<in>Procs. \<forall>Z. 
           \<Gamma>,\<Theta> \<union> (\<Union>q\<in>Procs. \<Union>Z. {(P q Z,
                      Call q, Q q Z,A q Z)})\<turnstile>\<^bsub>/F\<^esub>
              (P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)" 
  proof (intro ballI allI)
    fix p Z
    assume "p \<in> Procs"
    with hyp
    have hyp': "\<And> \<tau>. 
           \<Gamma>,\<Theta> \<union> (\<Union>q\<in>Procs. \<Union>Z. {(P q Z \<inter> {s. ((s, q), \<tau>, p) \<in> r},
                      Call q, Q q Z, A q Z)})\<turnstile>\<^bsub>/F\<^esub>
              ({\<tau>} \<inter> P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)"
      by blast
    have "\<forall>\<tau>. 
           \<Gamma>,\<Theta> \<union> (\<Union>q\<in>Procs. \<Union>Z. {(P q Z,
                      Call q, Q q Z,A q Z)})\<turnstile>\<^bsub>/F\<^esub>
              ({\<tau>} \<inter> P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)"
      (is "\<forall>\<tau>. \<Gamma>,?\<Theta>'\<turnstile>\<^bsub>/F\<^esub> ({\<tau>} \<inter> P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)")
    proof (rule allI, rule WeakenContext [OF hyp'],clarify)
      fix \<tau> P' c Q' A'
      assume "(P', c, Q', A') \<in> \<Theta> \<union>
         (\<Union>q\<in>Procs.
             \<Union>Z. {(P q Z \<inter> {s. ((s, q), \<tau>, p) \<in> r},
                  Call q, Q q Z,
                  A q Z)})" (is "(P', c, Q', A') \<in> \<Theta> \<union> ?Spec")
      then show "\<Gamma>,?\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P' c Q',A'"
      proof (cases rule: UnE [consumes 1])
        assume "(P',c,Q',A') \<in> \<Theta>" 
        then show ?thesis
          by (blast intro: HoarePartialDef.Asm)
      next
        assume "(P',c,Q',A') \<in> ?Spec" 
        then show ?thesis
        proof (clarify)
          fix q Z
          assume q: "q \<in> Procs"
          show "\<Gamma>,?\<Theta>'\<turnstile>\<^bsub>/F\<^esub> (P q Z \<inter> {s. ((s, q), \<tau>, p) \<in> r}) 
                         Call  q 
                        (Q q Z),(A q Z)"
          proof -
            from q
            have "\<Gamma>,?\<Theta>'\<turnstile>\<^bsub>/F\<^esub> (P q Z) Call q (Q q Z),(A q Z)"
              by - (rule HoarePartialDef.Asm,blast)
            thus ?thesis
              by (rule HoarePartialDef.conseqPre) blast
          qed
        qed
      qed
    qed
    then show "\<Gamma>,\<Theta> \<union> (\<Union>q\<in>Procs. \<Union>Z. {(P q Z, Call q, Q q Z,A q Z)})
                \<turnstile>\<^bsub>/F\<^esub> (P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)"
      by (rule HoarePartialDef.conseq) blast
  qed
  thus ?case
    by - (rule hoarep.CallRec)*)
next
  case DynCom thus ?case by (blast intro: hoarep.DynCom)
next
  case Throw thus ?case by - (rule hoarep.Throw)
next
  case Catch thus ?case by - (rule hoarep.Catch)
next
  case Conseq thus ?case by - (rule hoarep.Conseq,blast)
next
  case Asm thus ?case by (rule HoarePartialDef.Asm)
next
  case (ExFalso \<Theta> F P c Q A)
  assume "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  hence "\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
    oops


lemma hoaret_augment_context: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P p Q,A"
  shows "\<And>\<Theta>'. \<Theta> \<subseteq> \<Theta>' \<Longrightarrow> \<Gamma>,\<Theta>'\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P p Q,A"
using deriv
proof (induct)
  case (CallRec P p Q A Specs r Specs_wf \<Theta> F \<Theta>')
  have aug: "\<Theta> \<subseteq> \<Theta>'" by fact
  then
  have h: "\<And>\<tau> p. \<Theta> \<union> Specs_wf p \<tau>
       \<subseteq> \<Theta>' \<union> Specs_wf p \<tau>"
    by blast
  have "\<forall>(P,p,Q,A)\<in>Specs. p \<in> dom \<Gamma> \<and>
     (\<forall>\<tau>. \<Gamma>,\<Theta> \<union> Specs_wf p \<tau>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> P) (the (\<Gamma> p)) Q,A \<and>
           (\<forall>x. \<Theta> \<union> Specs_wf p \<tau>
                 \<subseteq> x \<longrightarrow>
                 \<Gamma>,x\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> P) (the (\<Gamma> p)) Q,A))" by fact
  hence "\<forall>(P,p,Q,A)\<in>Specs. p \<in> dom \<Gamma> \<and> 
         (\<forall>\<tau>. \<Gamma>,\<Theta>'\<union> Specs_wf p \<tau> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> P) (the (\<Gamma> p)) Q,A)"
    apply (clarify)
    apply (rename_tac P p Q A)
    apply (drule (1) bspec)
    apply (clarsimp)
    apply (erule_tac x=\<tau> in allE)
    apply clarify
    apply (erule_tac x="\<Theta>' \<union> Specs_wf p \<tau>" in allE)
    apply (insert aug)
    apply auto
    done
  with CallRec show ?case by - (rule hoaret.CallRec)
next
  case DynCom thus ?case by (blast intro: hoaret.DynCom)
next
  case (Conseq P \<Theta> F c Q A \<Theta>')
  from Conseq
  have "\<forall>s \<in> P. (\<exists>P' Q' A'. (\<Gamma>,\<Theta>' \<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q',A') \<and> s \<in> P'\<and> Q' \<subseteq> Q \<and> A' \<subseteq> A)"
    by blast
  with Conseq show ?case by - (rule hoaret.Conseq)
next
  case (ExFalso \<Theta> F P  c Q A \<Theta>')
  have "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" "\<not> \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" "\<Theta> \<subseteq> \<Theta>'"  by fact+
  then show ?case
    by (fastforce intro: hoaret.ExFalso simp add: cvalidt_def)
qed (blast intro: hoaret.intros)+

subsection {* Some Derived Rules *}


lemma  Conseq': "\<forall>s. s \<in> P \<longrightarrow> 
            (\<exists>P' Q' A'. 
              (\<forall> Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)) \<and>
                    (\<exists>Z. s \<in> P' Z \<and> (Q' Z \<subseteq> Q) \<and> (A' Z \<subseteq> A)))
           \<Longrightarrow>
           \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
apply (rule Conseq)
apply (rule ballI)
apply (erule_tac x=s in allE)
apply (clarify)
apply (rule_tac x="P' Z" in exI)
apply (rule_tac x="Q' Z" in exI)
apply (rule_tac x="A' Z" in exI)
apply blast
done

lemma conseq:"\<lbrakk>\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z);
              \<forall>s. s \<in> P \<longrightarrow> (\<exists> Z. s\<in>P' Z \<and> (Q' Z \<subseteq> Q)\<and> (A' Z \<subseteq> A))\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (rule Conseq) blast

theorem conseqPrePost: 
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q',A' \<Longrightarrow> P \<subseteq> P' \<Longrightarrow>  Q' \<subseteq> Q \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (rule conseq [where ?P'="\<lambda>Z. P'" and ?Q'="\<lambda>Z. Q'"]) auto

lemma conseqPre: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q,A \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
by (rule conseq) auto

lemma conseqPost: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q',A'\<Longrightarrow> Q' \<subseteq> Q \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (rule conseq) auto


lemma Spec_wf_conv: 
  "(\<lambda>(P, q, Q, A). (P \<inter> {s. ((s, q), \<tau>, p) \<in> r}, q, Q, A)) `
                (\<Union>p\<in>Procs. \<Union>Z. {(P p Z, p, Q p Z, A p Z)}) = 
        (\<Union>q\<in>Procs. \<Union>Z. {(P q Z \<inter> {s. ((s, q), \<tau>, p) \<in> r}, q, Q q Z, A q Z)})"
  by (auto intro!: image_eqI)

lemma CallRec': 
  "\<lbrakk>p\<in>Procs; Procs \<subseteq> dom \<Gamma>;
    wf r; 
   \<forall>p\<in>Procs. \<forall>\<tau> Z. 
   \<Gamma>,\<Theta>\<union>(\<Union>q\<in>Procs. \<Union>Z. 
    {((P q Z) \<inter> {s. ((s,q),(\<tau>,p)) \<in> r},q,Q q Z,(A q Z))})
     \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> (P p Z)) (the (\<Gamma> p)) (Q p Z),(A p Z)\<rbrakk>
   \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P p Z) (Call p) (Q p Z),(A p Z)"
apply (rule CallRec [where Specs="\<Union>p\<in>Procs. \<Union>Z. {((P p Z),p,Q p Z,A p Z)}" and
         r=r])
apply    blast
apply   assumption
apply  (rule refl)
apply (clarsimp)
apply (rename_tac p')
apply (rule conjI)
apply  blast
apply (intro allI)
apply (rename_tac Z \<tau>)
apply (drule_tac x=p' in bspec, assumption)
apply (erule_tac x=\<tau> in allE)
apply (erule_tac x=Z in allE)
apply (fastforce simp add: Spec_wf_conv)
done

end

