(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      HoarePartialProps.thy
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

section {* Properties of Partial Correctness Hoare Logic *}

theory HoarePartialProps imports HoarePartialDef begin

subsection {* Soundness *}

lemma hoare_cnvalid: 
 assumes hoare: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
 shows "\<And>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
using hoare
proof (induct)
  case (Skip \<Theta> F P A)
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P Skip P,A"
  proof (rule cnvalidI)
    fix s t
    assume "\<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> =n\<Rightarrow> t" "s \<in> P"
    thus "t \<in> Normal ` P \<union> Abrupt ` A"
      by cases auto
  qed
next
  case (Basic \<Theta> F f P A)
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> {s. f s \<in> P} (Basic f) P,A"
  proof (rule cnvalidI)
    fix s t
    assume "\<Gamma>\<turnstile>\<langle>Basic f,Normal s\<rangle> =n\<Rightarrow> t" "s \<in> {s. f s \<in> P}"
    thus "t \<in> Normal ` P \<union> Abrupt ` A"
      by cases auto
  qed
next 
  case (Spec \<Theta> F r Q A)
  show "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)} Spec r Q,A"
  proof (rule cnvalidI)
    fix s t
    assume exec: "\<Gamma>\<turnstile>\<langle>Spec r,Normal s\<rangle> =n\<Rightarrow> t"
    assume P: "s \<in> {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)}"
    from exec P
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
      by cases auto
  qed
next
  case (Seq \<Theta> F P c1 R A c2 Q)
  have valid_c1: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P c1 R,A" by fact
  have valid_c2: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> R c2 Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P Seq c1 c2 Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> =n\<Rightarrow> t"
    assume t_notin_F: "t \<notin> Fault ` F" 
    assume P: "s \<in> P"
    from exec P obtain r where
      exec_c1: "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> =n\<Rightarrow> r" and exec_c2:  "\<Gamma>\<turnstile>\<langle>c2,r\<rangle> =n\<Rightarrow> t"
      by cases auto
    with t_notin_F have "r \<notin> Fault ` F"
      by (auto dest: execn_Fault_end)
    with valid_c1 ctxt exec_c1 P
    have r: "r\<in>Normal ` R \<union> Abrupt ` A"
      by (rule cnvalidD)
    show "t\<in>Normal ` Q \<union> Abrupt ` A"
    proof (cases r)
      case (Normal r')
      with exec_c2 r
      show "t\<in>Normal ` Q \<union> Abrupt ` A"
        apply -
        apply (rule cnvalidD [OF valid_c2 ctxt _ _ t_notin_F])
        apply auto
        done
    next
      case (Abrupt r')
      with exec_c2 have "t=Abrupt r'"
        by (auto elim: execn_elim_cases)
      with Abrupt r show ?thesis
        by auto
    next
      case Fault with r show ?thesis by blast
    next
      case Stuck with r show ?thesis by blast
    qed
  qed
next
  case (Cond \<Theta> F P b c1 Q A c2)
  have valid_c1: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> (P \<inter> b) c1 Q,A" by fact
  have valid_c2: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> (P \<inter> - b) c2 Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P Cond b c1 c2 Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> =n\<Rightarrow> t"
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F" 
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof (cases "s\<in>b")
      case True
      with exec have "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> =n\<Rightarrow> t"
        by cases auto
      with P True 
      show ?thesis
        by - (rule cnvalidD [OF valid_c1 ctxt _ _ t_notin_F],auto)
    next
      case False
      with exec P have "\<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> =n\<Rightarrow> t"
        by cases auto
      with P False 
      show ?thesis
        by - (rule cnvalidD [OF valid_c2 ctxt _ _ t_notin_F],auto)
    qed
  qed
next
  case (While \<Theta> F P b c A n)
  have valid_c: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> (P \<inter> b) c P,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P While b c (P \<inter> - b),A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> =n\<Rightarrow> t"
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F" 
    show "t \<in> Normal ` (P \<inter> - b) \<union> Abrupt ` A"
    proof (cases "s \<in> b")
      case True
      {
        fix d::"('b,'a,'c) com" fix s t 
        assume exec: "\<Gamma>\<turnstile>\<langle>d,s\<rangle> =n\<Rightarrow> t"
        assume d: "d=While b c"
        assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
        from exec d ctxt
        have "\<lbrakk>s \<in> Normal ` P; t \<notin> Fault ` F\<rbrakk>
               \<Longrightarrow> t \<in> Normal ` (P \<inter> - b) \<union> Abrupt`A"
        proof (induct)
          case (WhileTrue s b' c' n r t)
          have t_notin_F: "t \<notin> Fault ` F" by fact
          have eqs: "While b' c' = While b c" by fact
          note valid_c
          moreover have ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" by fact
          moreover from WhileTrue
          obtain "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> r" and
            "\<Gamma>\<turnstile>\<langle>While b c,r\<rangle> =n\<Rightarrow> t" and
            "Normal s \<in> Normal `(P \<inter> b)" by auto
          moreover with t_notin_F have "r \<notin> Fault ` F"
            by (auto dest: execn_Fault_end)
          ultimately
          have r: "r \<in> Normal ` P \<union> Abrupt ` A"
            by - (rule cnvalidD,auto)
          from this _ ctxt
          show "t \<in> Normal ` (P \<inter> - b) \<union> Abrupt ` A "
          proof (cases r)
            case (Normal r')
            with r ctxt eqs t_notin_F
            show ?thesis
              by - (rule WhileTrue.hyps,auto)
          next
            case (Abrupt r')
            have "\<Gamma>\<turnstile>\<langle>While b' c',r\<rangle> =n\<Rightarrow> t" by fact
            with Abrupt have "t=r"
              by (auto dest: execn_Abrupt_end) 
            with r Abrupt show ?thesis
              by blast
          next
            case Fault with r show ?thesis by blast
          next
            case Stuck with r show ?thesis by blast
          qed   
        qed auto
      }
      with exec ctxt P t_notin_F
      show ?thesis
        by auto
    next
      case False
      with exec P have "t=Normal s"
        by cases auto
      with P False
      show ?thesis
        by auto
    qed
  qed
next
  case (Guard \<Theta> F g P c Q A f)
  have valid_c: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> (g \<inter> P) c Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> (g \<inter> P) Guard f g c  Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> =n\<Rightarrow> t"
    assume t_notin_F: "t \<notin> Fault ` F"
    assume P:"s \<in> (g \<inter> P)"
    from exec P have "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t"
      by cases auto
    from valid_c ctxt this P t_notin_F
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
      by (rule cnvalidD)
  qed
next
  case (Guarantee f F \<Theta> g P c Q A)
  have valid_c: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> (g \<inter> P) c Q,A" by fact
  have f_F: "f \<in> F" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P Guard f g c  Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> =n\<Rightarrow> t"
    assume t_notin_F: "t \<notin> Fault ` F"
    assume P:"s \<in> P"
    from exec f_F t_notin_F have g: "s \<in> g"
      by cases auto
    with P have P': "s \<in> g \<inter> P"
      by blast
    from exec P g have "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t"
      by cases auto
    from valid_c ctxt this P' t_notin_F
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
      by (rule cnvalidD)
  qed
next
  case (CallRec P p Q A Specs \<Theta> F)
  have p: "(P,p,Q,A) \<in> Specs" by fact
  have valid_body:
    "\<forall>(P,p,Q,A) \<in> Specs. p \<in> dom \<Gamma> \<and> (\<forall>n. \<Gamma>,\<Theta> \<union> Specs \<Turnstile>n:\<^bsub>/F\<^esub> P (the (\<Gamma> p)) Q,A)"
    using CallRec.hyps by blast
  show "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P Call p Q,A"
  proof -
    {
      fix n
      have "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A
        \<Longrightarrow> \<forall>(P,p,Q,A) \<in>Specs. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
      proof (induct n)
        case 0
        show "\<forall>(P,p,Q,A) \<in>Specs. \<Gamma>\<Turnstile>0:\<^bsub>/F\<^esub> P (Call p) Q,A"
          by (fastforce elim!: execn_elim_cases simp add: nvalid_def)
      next
        case (Suc m)
        have hyp: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>m:\<^bsub>/F\<^esub> P (Call p) Q,A
              \<Longrightarrow> \<forall>(P,p,Q,A) \<in>Specs. \<Gamma>\<Turnstile>m:\<^bsub>/F\<^esub> P (Call p) Q,A" by fact
        have "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>Suc m:\<^bsub>/F\<^esub> P (Call p) Q,A" by fact
        hence ctxt_m: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>m:\<^bsub>/F\<^esub> P (Call p) Q,A"
          by (fastforce simp add: nvalid_def intro: execn_Suc)
        hence valid_Proc:
          "\<forall>(P,p,Q,A) \<in>Specs. \<Gamma>\<Turnstile>m:\<^bsub>/F\<^esub> P (Call p) Q,A"
          by (rule hyp)
        let ?\<Theta>'= "\<Theta> \<union> Specs"
        from valid_Proc ctxt_m
        have "\<forall>(P, p, Q, A)\<in>?\<Theta>'. \<Gamma> \<Turnstile>m:\<^bsub>/F\<^esub> P (Call p) Q,A"
          by fastforce
        with valid_body
        have valid_body_m: 
          "\<forall>(P,p,Q,A) \<in>Specs. \<forall>n. \<Gamma> \<Turnstile>m:\<^bsub>/F\<^esub> P (the (\<Gamma> p)) Q,A"
          by (fastforce simp add: cnvalid_def)
        show "\<forall>(P,p,Q,A) \<in>Specs. \<Gamma> \<Turnstile>Suc m:\<^bsub>/F\<^esub> P (Call p) Q,A"
        proof (clarify)
          fix P p Q A assume p: "(P,p,Q,A) \<in> Specs"
          show "\<Gamma> \<Turnstile>Suc m:\<^bsub>/F\<^esub> P (Call p) Q,A"
          proof (rule nvalidI)
            fix s t
            assume exec_call: 
              "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> =Suc m\<Rightarrow> t"
            assume Pre: "s \<in> P"
            assume t_notin_F: "t \<notin> Fault ` F"
            from exec_call
            show "t \<in> Normal ` Q \<union> Abrupt ` A"
            proof (cases)
              fix bdy m' 
              assume m: "Suc m = Suc m'"
              assume bdy: "\<Gamma> p = Some bdy"
              assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal s\<rangle> =m'\<Rightarrow> t"
              from Pre valid_body_m exec_body bdy m p t_notin_F
              show ?thesis
                by (fastforce simp add: nvalid_def)
            next
              assume "\<Gamma> p = None"
              with valid_body p have False by auto
              thus ?thesis ..
            qed
          qed
        qed
      qed
    }
    with p show ?thesis
      by (fastforce simp add: cnvalid_def)
  qed
next
  case (DynCom P \<Theta> F c Q A)
  hence valid_c: "\<forall>s\<in>P. (\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P (c s) Q,A)" by auto
  show "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P DynCom c Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> =n\<Rightarrow> t" 
    assume P: "s \<in> P"
    assume t_notin_Fault: "t \<notin> Fault ` F"
    from exec show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof (cases)
      assume "\<Gamma>\<turnstile>\<langle>c s,Normal s\<rangle> =n\<Rightarrow> t"      
      from cnvalidD [OF valid_c [rule_format, OF P] ctxt this P t_notin_Fault]
      show ?thesis .
    qed
  qed
next
  case (Throw \<Theta> F A Q)
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> A Throw Q,A"
  proof (rule cnvalidI)
    fix s t
    assume "\<Gamma>\<turnstile>\<langle>Throw,Normal s\<rangle> =n\<Rightarrow> t" "s \<in> A"
    then show "t \<in> Normal ` Q \<union> Abrupt ` A"
      by cases simp
  qed
next
  case (Catch \<Theta> F P c\<^sub>1 Q R c\<^sub>2 A)
  have valid_c1: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P c\<^sub>1 Q,R" by fact
  have valid_c2: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> R c\<^sub>2 Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P Catch c\<^sub>1 c\<^sub>2 Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> =n\<Rightarrow> t" 
    assume P: "s \<in> P"
    assume t_notin_Fault: "t \<notin> Fault ` F"
    from exec show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof (cases)
      fix s'
      assume exec_c1: "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow> Abrupt s'" 
      assume exec_c2: "\<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s'\<rangle> =n\<Rightarrow> t"
      from cnvalidD [OF valid_c1 ctxt exec_c1 P ] 
      have "Abrupt s' \<in> Abrupt ` R"
        by auto
      with cnvalidD [OF valid_c2 ctxt _ _ t_notin_Fault] exec_c2
      show ?thesis
        by fastforce
    next
      assume exec_c1: "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow> t" 
      assume notAbr: "\<not> isAbr t"
      from cnvalidD [OF valid_c1 ctxt exec_c1 P t_notin_Fault] 
      have "t \<in> Normal ` Q \<union> Abrupt ` R" .
      with notAbr
      show ?thesis
        by auto
    qed
  qed
next
  case (Conseq P \<Theta> F c Q A)
  hence adapt: "\<forall>s \<in> P. (\<exists>P' Q' A'. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P' c Q',A'  \<and>
                          s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A)"
    by blast
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt:"\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t"
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F"
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof -
      from P adapt obtain P' Q' A' Z  where
        spec: "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P' c Q',A'" and
        P': "s \<in> P'"  and  strengthen: "Q' \<subseteq> Q \<and> A' \<subseteq> A"
        by auto
      from spec [rule_format] ctxt exec P' t_notin_F  
      have "t \<in> Normal ` Q' \<union> Abrupt ` A'"
        by (rule cnvalidD)
      with strengthen show ?thesis
        by blast
    qed
  qed
next
  case (Asm P p Q A \<Theta> F)
  have asm: "(P, p, Q, A) \<in> \<Theta>" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  proof (rule cnvalidI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> =n\<Rightarrow> t"
    from asm ctxt have "\<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P Call p Q,A" by auto
    moreover
    assume "s \<in> P" "t \<notin> Fault ` F"
    ultimately
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
      using exec
      by (auto simp add: nvalid_def)
  qed
next
  case ExFalso thus ?case by iprover
qed

theorem hoare_sound: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> \<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  by (iprover intro: cnvalid_to_cvalid hoare_cnvalid)

subsection {* Completeness *}

lemma MGT_valid:
"\<Gamma>\<Turnstile>\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union>  Fault ` (-F))} c 
   {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t}, {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof (rule validI) 
  fix s t
  assume "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
         "s \<in> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union>  Fault ` (-F))}"
         "t \<notin> Fault ` F"
  thus "t \<in> Normal ` {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t} \<union> 
            Abrupt ` {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (cases t) (auto simp add: final_notin_def)
qed

text {* The consequence rule where the existential @{term Z} is instantiated
to @{term s}. Usefull in proof of @{text "MGT_lemma"}.*}
lemma ConseqMGT: 
  assumes modif: "\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)"
  assumes impl: "\<And>s. s \<in> P \<Longrightarrow> s \<in> P' s \<and> (\<forall>t. t \<in> Q' s \<longrightarrow> t \<in> Q) \<and> 
                                            (\<forall>t. t \<in> A' s \<longrightarrow> t \<in> A)"
  shows "\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> P c Q,A"
using impl 
by -  (rule conseq [OF modif],blast)


lemma Seq_NoFaultStuckD1: 
  assumes noabort: "\<Gamma>\<turnstile>\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
  shows "\<Gamma>\<turnstile>\<langle>c1,s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
proof (rule final_notinI)
  fix t
  assume exec_c1: "\<Gamma>\<turnstile>\<langle>c1,s\<rangle> \<Rightarrow> t"
  show "t \<notin> {Stuck} \<union> Fault `  F"
  proof 
    assume "t \<in> {Stuck} \<union> Fault `  F"
    moreover
    {
      assume "t = Stuck"
      with exec_c1
      have "\<Gamma>\<turnstile>\<langle>Seq c1 c2,s\<rangle> \<Rightarrow> Stuck"
        by (auto intro: exec_Seq')
      with noabort have False
        by (auto simp add: final_notin_def)
      hence False ..
    }
    moreover 
    {
      assume "t \<in> Fault ` F"
      then obtain f where 
      t: "t=Fault f" and f: "f \<in> F"
        by auto
      from t exec_c1
      have "\<Gamma>\<turnstile>\<langle>Seq c1 c2,s\<rangle> \<Rightarrow> Fault f"
        by (auto intro: exec_Seq')
      with noabort f have False
        by (auto simp add: final_notin_def)
      hence False ..
    }
    ultimately show False by auto
  qed
qed

lemma Seq_NoFaultStuckD2: 
  assumes noabort: "\<Gamma>\<turnstile>\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
  shows "\<forall>t. \<Gamma>\<turnstile>\<langle>c1,s\<rangle> \<Rightarrow> t \<longrightarrow> t\<notin> ({Stuck} \<union> Fault `  F) \<longrightarrow> 
             \<Gamma>\<turnstile>\<langle>c2,t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault `  F)"
using noabort
by (auto simp add: final_notin_def intro: exec_Seq')


lemma MGT_implies_complete:
  assumes MGT: "\<forall>Z. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union>  Fault ` (-F))} c 
                           {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
                           {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  assumes valid: "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P c Q,A" 
  shows "\<Gamma>,{} \<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  using MGT
  apply (rule ConseqMGT) 
  apply (insert valid)
  apply (auto simp add: valid_def intro!: final_notinI)
  done

text {* Equipped only with the classic consequence rule @{thm "conseqPrePost"}
        we can only derive this syntactically more involved version
        of completeness. But semantically it is equivalent to the "real" one
        (see below) *}
lemma MGT_implies_complete':
  assumes MGT: "\<forall>Z. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> 
                       {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union>  Fault ` (-F))} c 
                           {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
                           {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  assumes valid: "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P c Q,A" 
  shows "\<Gamma>,{} \<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> s \<in> P} c {t. Z \<in> P \<longrightarrow> t \<in> Q},{t. Z \<in> P \<longrightarrow> t \<in> A}"
  using MGT [rule_format, of Z]
  apply (rule conseqPrePost)
  apply (insert valid)
  apply   (fastforce simp add: valid_def final_notin_def)
  apply  (fastforce simp add: valid_def)
  apply (fastforce simp add: valid_def)
  done

text {* Semantic equivalence of both kind of formulations *}
lemma valid_involved_to_valid:
  assumes valid: 
    "\<forall>Z. \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> s \<in> P} c {t. Z \<in> P \<longrightarrow> t \<in> Q},{t. Z \<in> P \<longrightarrow> t \<in> A}"
  shows "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  using valid
  apply (simp add: valid_def)
  apply clarsimp
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="Normal x" in allE)
  apply (erule_tac x=t in allE)
  apply fastforce
  done

text {* The sophisticated consequence rule allow us to do this 
        semantical transformation on the hoare-level, too. 
        The magic is, that it allow us to
        choose the instance of @{term Z} under the assumption of an state @{term "s \<in> P"} *}
lemma
  assumes deriv: 
    "\<forall>Z. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> s \<in> P} c {t. Z \<in> P \<longrightarrow> t \<in> Q},{t. Z \<in> P \<longrightarrow> t \<in> A}"
  shows "\<Gamma>,{} \<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  apply (rule ConseqMGT [OF deriv])
  apply auto
  done

lemma valid_to_valid_involved:
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow>
   \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> s \<in> P} c {t. Z \<in> P \<longrightarrow> t \<in> Q},{t. Z \<in> P \<longrightarrow> t \<in> A}"
by (simp add: valid_def Collect_conv_if)

lemma
  assumes deriv: "\<Gamma>,{} \<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> s \<in> P} c {t. Z \<in> P \<longrightarrow> t \<in> Q},{t. Z \<in> P \<longrightarrow> t \<in> A}"
  apply (rule conseqPrePost [OF deriv])
  apply auto
  done

lemma conseq_extract_state_indep_prop: 
  assumes state_indep_prop:"\<forall>s \<in> P. R" 
  assumes to_show: "R \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  apply (rule Conseq)
  apply (clarify)
  apply (rule_tac x="P" in exI)
  apply (rule_tac x="Q" in exI)
  apply (rule_tac x="A" in exI)
  using state_indep_prop to_show
  by blast


lemma MGT_lemma:
  assumes MGT_Calls: 
    "\<forall>p\<in>dom \<Gamma>. \<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> 
       {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}
        (Call p)
       {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
       {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  shows "\<And>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c 
             {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof (induct c)
  case Skip
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} Skip
           {t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoarep.Skip [THEN conseqPre])
       (auto elim: exec_elim_cases simp add: final_notin_def intro: exec.intros)
next
  case (Basic f)
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Basic f,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} Basic f
           {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Normal t}, 
           {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoarep.Basic [THEN conseqPre])
       (auto elim: exec_elim_cases simp add: final_notin_def intro: exec.intros)
next
  case (Spec r)
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Spec r,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} Spec r
           {t. \<Gamma>\<turnstile>\<langle>Spec r,Normal Z\<rangle> \<Rightarrow> Normal t}, 
           {t. \<Gamma>\<turnstile>\<langle>Spec r,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    apply (rule hoarep.Spec [THEN conseqPre])
    apply (clarsimp simp add: final_notin_def)
    apply (case_tac "\<exists>t. (Z,t) \<in> r")
    apply (auto elim: exec_elim_cases simp add: final_notin_def intro: exec.intros)
    done
next
  case (Seq c1 c2) 
  have hyp_c1: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c1 
                           {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
                           {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    using Seq.hyps by iprover
  have hyp_c2: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c2 
                          {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                          {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    using Seq.hyps by iprover
  from hyp_c1 
  have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c1 
              {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t \<and> 
                  \<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))},
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule ConseqMGT)
       (auto dest: Seq_NoFaultStuckD1 [simplified] Seq_NoFaultStuckD2 [simplified]
             intro: exec.Seq)
  thus "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
                   Seq c1 c2
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule hoarep.Seq )
    show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t \<and> 
                      \<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
                   c2
                 {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                 {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    proof (rule ConseqMGT [OF hyp_c2],safe)
      fix r t
      assume "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal r" "\<Gamma>\<turnstile>\<langle>c2,Normal r\<rangle> \<Rightarrow> Normal t"
      then show "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t"
        by (iprover intro: exec.intros)
    next
      fix r t
      assume "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal r" "\<Gamma>\<turnstile>\<langle>c2,Normal r\<rangle> \<Rightarrow> Abrupt t"
      then show "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t"
        by (iprover intro: exec.intros)
    qed
  qed
next
  case (Cond b c1 c2) 
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c1 
                 {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
                 {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    using Cond.hyps by iprover  
  hence "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> ({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}\<inter>b)
                   c1 
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    by (rule ConseqMGT)
       (fastforce intro: exec.CondTrue simp add: final_notin_def)
  moreover
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c2 
                    {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                    {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    using Cond.hyps by iprover  
  hence "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}\<inter>-b)
                  c2 
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    by (rule ConseqMGT)
       (fastforce intro: exec.CondFalse simp add: final_notin_def)
  ultimately
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
                 Cond b c1 c2
              {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoarep.Cond)       
next
  case (While b c)
  let ?unroll = "({(s,t). s\<in>b \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t})\<^sup>*"
  let ?P' = "\<lambda>Z. {t. (Z,t)\<in>?unroll \<and> 
                    (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                         \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                             (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u))}"
  let ?A' = "\<lambda>Z. {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
                While b c
              {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [where ?P'="?P'" 
                         and ?Q'="\<lambda>Z. ?P' Z \<inter> - b" and ?A'="?A'"])
    show "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (?P' Z) (While b c) (?P' Z \<inter> - b),(?A' Z)"
    proof (rule allI, rule hoarep.While)
      fix Z
      from While 
      have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c
                        {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
                        {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}" by iprover
      then show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (?P' Z  \<inter> b) c (?P' Z),(?A' Z)"
      proof (rule ConseqMGT)
        fix s
        assume  "s\<in> {t. (Z, t) \<in> ?unroll \<and> 
                      (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                           \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                               (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                    \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u))}
                   \<inter> b"
        then obtain 
          Z_s_unroll: "(Z,s) \<in> ?unroll" and
          noabort:"\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)" and
          s_in_b: "s\<in>b" 
          by blast
        show "s \<in> {t. t = s \<and> \<Gamma>\<turnstile>\<langle>c,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} \<and>
        (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t} \<longrightarrow>
             t \<in> {t. (Z, t) \<in> ?unroll \<and> 
                  (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow>  e\<in>b 
                       \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                           (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u))}) \<and> 
         (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t} \<longrightarrow>
             t \<in> {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t})"
          (is "?C1 \<and> ?C2 \<and> ?C3")
        proof (intro conjI)
          from Z_s_unroll noabort s_in_b show ?C1 by blast
        next
          {
            fix t 
            assume s_t: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t"
            moreover
            from Z_s_unroll s_t s_in_b 
            have "(Z, t) \<in> ?unroll"
              by (blast intro: rtrancl_into_rtrancl)
            moreover note noabort
            ultimately 
            have "(Z, t) \<in> ?unroll \<and> 
                  (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u))"
              by iprover
          }
          then show ?C2 by blast
        next
          {
            fix t
            assume s_t:  "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t" 
            from Z_s_unroll noabort s_t s_in_b 
            have "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t"
              by blast
          } thus ?C3 by simp
        qed
      qed
    qed
  next
    fix s
    assume P: "s \<in> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}"
    hence WhileNoFault: "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by auto
    show "s \<in> ?P' s \<and> 
    (\<forall>t. t\<in>(?P' s \<inter> - b)\<longrightarrow>
         t\<in>{t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t})\<and>
    (\<forall>t. t\<in>?A' s \<longrightarrow> t\<in>?A' Z)"
    proof (intro conjI)
      {
        fix e
        assume "(Z,e) \<in> ?unroll" "e \<in> b"
        from this WhileNoFault
        have "\<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
               (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                    \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)" (is "?Prop Z e")
        proof (induct rule: converse_rtrancl_induct [consumes 1])
          assume e_in_b: "e \<in> b"
          assume WhileNoFault: "\<Gamma>\<turnstile>\<langle>While b c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
          with e_in_b WhileNoFault
          have cNoFault: "\<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
            by (auto simp add: final_notin_def intro: exec.intros)
          moreover
          {
            fix u assume "\<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow> Abrupt u"
            with e_in_b have "\<Gamma>\<turnstile>\<langle>While b c,Normal e\<rangle> \<Rightarrow> Abrupt u"
              by (blast intro: exec.intros)
          }
          ultimately
          show "?Prop e e"
            by iprover
        next
          fix Z r
          assume e_in_b: "e\<in>b" 
          assume WhileNoFault: "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
          assume hyp: "\<lbrakk>e\<in>b;\<Gamma>\<turnstile>\<langle>While b c,Normal r\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))\<rbrakk>
                       \<Longrightarrow> ?Prop r e"
          assume Z_r:
            "(Z, r) \<in> {(Z, r). Z \<in> b \<and> \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal r}"
          with WhileNoFault
          have "\<Gamma>\<turnstile>\<langle>While b c,Normal r\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
            by (auto simp add: final_notin_def intro: exec.intros)
          from hyp [OF e_in_b this] obtain
            cNoFault: "\<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" and
            Abrupt_r: "\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow> Abrupt u \<longrightarrow> 
                            \<Gamma>\<turnstile>\<langle>While b c,Normal r\<rangle> \<Rightarrow> Abrupt u"
            by simp
          
           {
            fix u assume "\<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow> Abrupt u"
            with Abrupt_r have "\<Gamma>\<turnstile>\<langle>While b c,Normal r\<rangle> \<Rightarrow> Abrupt u" by simp
            moreover from  Z_r obtain
              "Z \<in> b"  "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal r"
              by simp
            ultimately have "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u"
              by (blast intro: exec.intros)
          }
          with cNoFault show "?Prop Z e"
            by iprover
        qed
      }
      with P show "s \<in> ?P' s"
        by blast
    next
      {
        fix t
        assume "termination": "t \<notin> b"
        assume "(Z, t) \<in> ?unroll"
        hence "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t"
        proof (induct rule: converse_rtrancl_induct [consumes 1])
          from "termination" 
          show "\<Gamma>\<turnstile>\<langle>While b c,Normal t\<rangle> \<Rightarrow> Normal t"
            by (blast intro: exec.WhileFalse)
        next
          fix Z r
          assume first_body: 
                 "(Z, r) \<in> {(s, t). s \<in> b \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t}"
          assume "(r, t) \<in> ?unroll"
          assume rest_loop: "\<Gamma>\<turnstile>\<langle>While b c, Normal r\<rangle> \<Rightarrow> Normal t"
          show "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t"
          proof -
            from first_body obtain
              "Z \<in> b" "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal r"
              by fast
            moreover
            from rest_loop have
              "\<Gamma>\<turnstile>\<langle>While b c,Normal r\<rangle> \<Rightarrow> Normal t"
              by fast
            ultimately show "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t"
              by (rule exec.WhileTrue)
          qed
        qed
      }
      with P
      show "(\<forall>t. t\<in>(?P' s \<inter> - b)
            \<longrightarrow>t\<in>{t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t})"
        by blast
    next
      from P show "\<forall>t. t\<in>?A' s \<longrightarrow> t\<in>?A' Z" by simp
    qed
  qed
next
  case (Call p)
  let ?P = "{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}"
  from noStuck_Call have "\<forall>s \<in> ?P. p \<in> dom \<Gamma>"
    by (fastforce simp add: final_notin_def )
  then show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> ?P (Call p)
               {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule conseq_extract_state_indep_prop)
    assume p_definied: "p \<in> dom \<Gamma>"
    with MGT_Calls show
      "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. s=Z \<and> 
                 \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}
                  (Call p)
                 {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
                 {t. \<Gamma>\<turnstile>\<langle>Call  p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      by (auto)
  qed
next
  case (DynCom c)
  have hyp: 
    "\<And>s'. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c s',Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c s'
      {t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using DynCom by simp
  have hyp':
  "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. s = Z \<and> \<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c Z
        {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule ConseqMGT [OF hyp])
       (fastforce simp add: final_notin_def intro: exec.intros)
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. s = Z \<and> \<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
               DynCom c
             {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Normal t},
             {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    apply (rule hoarep.DynCom)
    apply (clarsimp)
    apply (rule hyp' [simplified])
    done
next  
  case (Guard f g c)
  have hyp_c: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c
                    {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
                    {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Guard by iprover
  show ?case
  proof (cases "f \<in> F")
    case True 
    from hyp_c
    have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>(g \<inter> {s. s = Z \<and> 
                    \<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (- F))}) 
             c
           {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Normal t},
           {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      apply (rule ConseqMGT)
      apply (insert True)
      apply (auto simp add: final_notin_def intro: exec.intros)
      done
    from True this
    show ?thesis      
      by (rule conseqPre [OF Guarantee]) auto
  next
    case False
    from hyp_c
    have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> 
           (g \<inter> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}) 
           c
           {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Normal t},
           {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      apply (rule ConseqMGT)
      apply clarify
      apply (frule Guard_noFaultStuckD [OF _ False])
      apply (auto simp add: final_notin_def intro: exec.intros)
      done
    then show ?thesis
      apply (rule conseqPre [OF hoarep.Guard])
      apply clarify
      apply (frule Guard_noFaultStuckD [OF _ False])
      apply auto
      done
  qed
next
  case Throw
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Throw,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} Throw
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule conseqPre [OF hoarep.Throw]) (blast intro: exec.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c\<^sub>1
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  hence "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c\<^sub>1
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t \<and> 
                   \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}"
    by (rule ConseqMGT)
       (fastforce intro: exec.intros simp add: final_notin_def)
  moreover
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} c\<^sub>2
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  hence "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow>Abrupt s \<and> 
                   \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
               c\<^sub>2
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule ConseqMGT)
       (fastforce intro: exec.intros  simp add: final_notin_def)
  ultimately
  show "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
                   Catch c\<^sub>1 c\<^sub>2
              {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoarep.Catch)
qed

lemma MGT_Calls: 
 "\<forall>p\<in>dom \<Gamma>. \<forall>Z. 
     \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}
            (Call p)
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof - 
  {
    fix p Z 
    assume defined: "p \<in> dom \<Gamma>"
    have 
      "\<Gamma>,(\<Union>p\<in>dom \<Gamma>. \<Union>Z. 
          {({s. s=Z \<and> 
             \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))},
             p,
             {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
             {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t})})
       \<turnstile>\<^bsub>/F\<^esub>{s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
          (the (\<Gamma> p))
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      (is "\<Gamma>,?\<Theta> \<turnstile>\<^bsub>/F\<^esub> (?Pre p Z) (the (\<Gamma> p)) (?Post p Z),(?Abr p Z)")
    proof -
      have MGT_Calls:
       "\<forall>p\<in>dom \<Gamma>. \<forall>Z. \<Gamma>,?\<Theta> \<turnstile>\<^bsub>/F\<^esub> 
        {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}
         (Call p)
        {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
        {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
        by (intro ballI allI, rule HoarePartialDef.Asm,auto)
      have "\<forall>Z. \<Gamma>,?\<Theta>\<turnstile>\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>the (\<Gamma> p) ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault`(-F))} 
                        (the (\<Gamma> p))
                        {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Normal t},
                        {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Abrupt t}"
        by (iprover intro: MGT_lemma [OF MGT_Calls])
      thus "\<Gamma>,?\<Theta>\<turnstile>\<^bsub>/F\<^esub> (?Pre p Z) (the (\<Gamma> p)) (?Post p Z),(?Abr p Z)"
        apply (rule ConseqMGT)
        apply (clarify,safe)
      proof -
        assume "\<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
        with defined show "\<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
          by (fastforce simp add: final_notin_def 
                intro: exec.intros)
      next
        fix t
        assume "\<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Normal t"
        with defined 
        show "\<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow>Normal t"
          by  (auto intro: exec.Call)
      next
        fix t
        assume "\<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Abrupt t"
        with defined 
        show "\<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow>Abrupt t"
          by  (auto intro: exec.Call)
      qed
    qed
  }
  then show ?thesis
    apply -
    apply (intro ballI allI)
    apply (rule CallRec' [where Procs="dom \<Gamma>"  and 
      P="\<lambda>p Z. {s. s=Z \<and> 
                  \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}"and
      Q="\<lambda>p Z. 
        {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t}" and
      A="\<lambda>p Z. 
        {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"] )
    apply simp+
    done
qed

theorem hoare_complete: "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  by (iprover intro: MGT_implies_complete MGT_lemma [OF MGT_Calls])

lemma hoare_complete': 
  assumes cvalid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  shows  "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
proof (cases "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A")
  case True
  hence "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
    by (rule hoare_complete)
  thus "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P c Q,A"
    by (rule hoare_augment_context) simp
next
  case False
  with cvalid
  show ?thesis
    by (rule ExFalso)
qed
  

lemma hoare_strip_\<Gamma>: 
  assumes deriv: "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P p Q,A"
  assumes F': "F' \<subseteq> -F"
  shows "strip F' \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P p Q,A"
proof (rule hoare_complete)
  from hoare_sound [OF deriv] have "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P p Q,A"
    by (simp add: cvalid_def)
  from this F'
  show "strip F' \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P p Q,A"
    by (rule valid_to_valid_strip)
qed


subsection {* And Now: Some Useful Rules *}
 
subsubsection {* Consequence *}


lemma LiberalConseq_sound:
fixes F::"'f set" 
assumes cons: "\<forall>s \<in> P. \<forall>(t::('s,'f) xstate). \<exists>P' Q' A'. (\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P' c Q',A') \<and>
                ((s \<in> P' \<longrightarrow> t \<in> Normal ` Q' \<union> Abrupt ` A')
                              \<longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A)"
shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A "
proof (rule cnvalidI)
  fix s t
  assume ctxt:"\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t"
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof -
    from P cons obtain P' Q' A' where
      spec: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P' c Q',A'" and
      adapt: "(s \<in> P' \<longrightarrow> t \<in> Normal ` Q' \<union> Abrupt ` A')
                              \<longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A"
      apply -
      apply (drule (1) bspec)
      apply (erule_tac x=t in allE)
      apply (elim exE conjE)
      apply iprover
      done
    from exec spec ctxt t_notin_F
    have "s \<in> P' \<longrightarrow> t \<in> Normal ` Q' \<union> Abrupt ` A'"
      by (simp add: cnvalid_def nvalid_def)
    with adapt show ?thesis
      by simp
  qed
qed

lemma LiberalConseq:
fixes F:: "'f set"
assumes cons: "\<forall>s \<in> P.  \<forall>(t::('s,'f) xstate). \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c Q',A' \<and>
                ((s \<in> P' \<longrightarrow> t \<in> Normal ` Q' \<union> Abrupt ` A')
                              \<longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A "
apply (rule hoare_complete')
apply (rule allI)
apply (rule LiberalConseq_sound)
using cons
apply (clarify)
apply (drule (1) bspec)
apply (erule_tac x=t in allE)
apply clarify
apply (rule_tac x=P' in exI)
apply (rule_tac x=Q' in exI)
apply (rule_tac x=A' in exI)
apply (rule conjI)
apply (blast intro: hoare_cnvalid)
apply assumption
done

lemma "\<forall>s \<in> P. \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c Q',A' \<and> s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A 
           \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  apply (rule LiberalConseq)
  apply (rule ballI)
  apply (drule (1) bspec)
  apply clarify
  apply (rule_tac x=P' in exI)
  apply (rule_tac x=Q' in exI)
  apply (rule_tac x=A' in exI)
  apply auto
  done

lemma
fixes F:: "'f set"
assumes cons: "\<forall>s \<in> P.  \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c Q',A' \<and>
                (\<forall>(t::('s,'f) xstate). (s \<in> P' \<longrightarrow> t \<in> Normal ` Q' \<union> Abrupt ` A')
                              \<longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A "
  apply (rule Conseq)
  apply (rule ballI)
  apply (insert cons)
  apply (drule (1) bspec)
  apply clarify
  apply (rule_tac x=P' in exI)
  apply (rule_tac x=Q' in exI)
  apply (rule_tac x=A' in exI)
  apply (rule conjI)
  apply  assumption
  (* no way to get s \<in> P' *)
  oops

lemma LiberalConseq':
fixes F:: "'f set"
assumes cons: "\<forall>s \<in> P.  \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' c Q',A' \<and>
                (\<forall>(t::('s,'f) xstate). (s \<in> P' \<longrightarrow> t \<in> Normal ` Q' \<union> Abrupt ` A')
                              \<longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A "
apply (rule LiberalConseq)
apply (rule ballI)
apply (rule allI)
apply (insert cons)
apply (drule (1) bspec)
apply clarify
apply (rule_tac x=P' in exI)
apply (rule_tac x=Q' in exI)
apply (rule_tac x=A' in exI)
apply iprover
done

lemma LiberalConseq'':
fixes F:: "'f set"
assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)"
assumes cons: "\<forall>s (t::('s,'f) xstate). 
                 (\<forall>Z. s \<in> P' Z \<longrightarrow> t \<in> Normal ` Q' Z \<union> Abrupt ` A' Z)
                  \<longrightarrow> (s \<in> P \<longrightarrow> t \<in> Normal ` Q \<union> Abrupt ` A)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A "
apply (rule LiberalConseq)
apply (rule ballI)
apply (rule allI)
apply (insert cons)
apply (erule_tac x=s in allE)
apply (erule_tac x=t in allE)
apply (case_tac "t \<in> Normal ` Q \<union> Abrupt ` A")
apply (insert spec)
apply  iprover
apply auto
done

primrec procs:: "('s,'p,'f) com \<Rightarrow> 'p set"
where
"procs Skip = {}" |
"procs (Basic f) = {}" |
"procs (Seq c\<^sub>1 c\<^sub>2)  = (procs c\<^sub>1 \<union> procs c\<^sub>2)" |
"procs (Cond b c\<^sub>1 c\<^sub>2) = (procs c\<^sub>1 \<union> procs c\<^sub>2)" |
"procs (While b c) = procs c" |
"procs (Call p) = {p}" |
"procs (DynCom c) = (\<Union>s. procs (c s))" |
"procs (Guard f g c) = procs c" |
"procs Throw = {}" |
"procs (Catch c\<^sub>1 c\<^sub>2) = (procs c\<^sub>1 \<union> procs c\<^sub>2)"

primrec noSpec:: "('s,'p,'f) com \<Rightarrow> bool"
where
"noSpec Skip = True" |
"noSpec (Basic f) = True" |
"noSpec (Spec r) = False" |
"noSpec (Seq c\<^sub>1 c\<^sub>2)  = (noSpec c\<^sub>1 \<and> noSpec c\<^sub>2)" |
"noSpec (Cond b c\<^sub>1 c\<^sub>2) = (noSpec c\<^sub>1 \<and> noSpec c\<^sub>2)" |
"noSpec (While b c) = noSpec c" |
"noSpec (Call p) = True" |
"noSpec (DynCom c) = (\<forall>s. noSpec (c s))" |
"noSpec (Guard f g c) = noSpec c" |
"noSpec Throw = True" |
"noSpec (Catch c\<^sub>1 c\<^sub>2) = (noSpec c\<^sub>1 \<and> noSpec c\<^sub>2)"

lemma exec_noSpec_no_Stuck:
 assumes exec: "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
 assumes noSpec_c: "noSpec c"
 assumes noSpec_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noSpec (the (\<Gamma> p))"
 assumes procs_subset: "procs c \<subseteq> dom \<Gamma>"
 assumes procs_subset_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. procs (the (\<Gamma> p)) \<subseteq> dom \<Gamma>"
 assumes s_no_Stuck: "s\<noteq>Stuck"
 shows "t\<noteq>Stuck"
using exec noSpec_c procs_subset s_no_Stuck proof induct
  case (Call p bdy s t) with noSpec_\<Gamma> procs_subset_\<Gamma> show ?case
    by (auto dest!: bspec [of _ _ p])
next
  case (DynCom c s t) then show ?case
   by auto blast
qed auto

lemma execn_noSpec_no_Stuck:
 assumes exec: "\<Gamma>\<turnstile>\<langle>c,s\<rangle> =n\<Rightarrow> t"
 assumes noSpec_c: "noSpec c"
 assumes noSpec_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noSpec (the (\<Gamma> p))"
 assumes procs_subset: "procs c \<subseteq> dom \<Gamma>"
 assumes procs_subset_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. procs (the (\<Gamma> p)) \<subseteq> dom \<Gamma>"
 assumes s_no_Stuck: "s\<noteq>Stuck"
 shows "t\<noteq>Stuck"
using exec noSpec_c procs_subset s_no_Stuck proof induct
  case (Call p bdy n s t) with noSpec_\<Gamma> procs_subset_\<Gamma> show ?case
    by (auto dest!: bspec [of _ _ p])
next
  case (DynCom c s t) then show ?case
    by auto blast
qed auto

lemma LiberalConseq_noguards_nothrows_sound:
assumes spec: "\<forall>Z. \<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)"
assumes cons: "\<forall>s t. (\<forall>Z. s \<in> P' Z \<longrightarrow> t \<in>  Q' Z )
                  \<longrightarrow> (s \<in> P \<longrightarrow> t \<in> Q )"
assumes noguards_c: "noguards c"
assumes noguards_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noguards (the (\<Gamma> p))"
assumes nothrows_c: "nothrows c"
assumes nothrows_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. nothrows (the (\<Gamma> p))"
assumes noSpec_c: "noSpec c"
assumes noSpec_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noSpec (the (\<Gamma> p))"
assumes procs_subset: "procs c \<subseteq> dom \<Gamma>"
assumes procs_subset_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. procs (the (\<Gamma> p)) \<subseteq> dom \<Gamma>"
shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A "
proof (rule cnvalidI)
  fix s t
  assume ctxt:"\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t"
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof -
    from execn_noguards_no_Fault [OF exec noguards_c noguards_\<Gamma>]
     execn_nothrows_no_Abrupt [OF exec nothrows_c nothrows_\<Gamma> ]
     execn_noSpec_no_Stuck [OF exec  
              noSpec_c  noSpec_\<Gamma> procs_subset 
      procs_subset_\<Gamma>]                            
    obtain t' where t: "t=Normal t'"
      by (cases t) auto
    with exec spec ctxt
    have "(\<forall>Z. s \<in> P' Z \<longrightarrow> t' \<in>  Q' Z)"
      by (unfold  cnvalid_def nvalid_def) blast
    with cons P t show ?thesis
      by simp
  qed
qed


lemma LiberalConseq_noguards_nothrows:
assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)"
assumes cons: "\<forall>s t. (\<forall>Z. s \<in> P' Z \<longrightarrow> t \<in>  Q' Z )
                  \<longrightarrow> (s \<in> P \<longrightarrow> t \<in> Q )"
assumes noguards_c: "noguards c"
assumes noguards_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noguards (the (\<Gamma> p))"
assumes nothrows_c: "nothrows c"
assumes nothrows_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. nothrows (the (\<Gamma> p))"
assumes noSpec_c: "noSpec c"
assumes noSpec_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noSpec (the (\<Gamma> p))"
assumes procs_subset: "procs c \<subseteq> dom \<Gamma>"
assumes procs_subset_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. procs (the (\<Gamma> p)) \<subseteq> dom \<Gamma>"
shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A "
apply (rule hoare_complete')
apply (rule allI)
apply (rule LiberalConseq_noguards_nothrows_sound 
             [OF _ cons noguards_c noguards_\<Gamma> nothrows_c nothrows_\<Gamma> 
                 noSpec_c noSpec_\<Gamma> 
                 procs_subset procs_subset_\<Gamma>])
apply (insert spec)
apply (intro allI)
apply (erule_tac x=Z in allE)
by (rule hoare_cnvalid)

lemma 
assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. s=fst Z \<and> P s (snd Z)} c {t. Q (fst Z) (snd Z) t},{}"
assumes noguards_c: "noguards c"
assumes noguards_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noguards (the (\<Gamma> p))"
assumes nothrows_c: "nothrows c"
assumes nothrows_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. nothrows (the (\<Gamma> p))"
assumes noSpec_c: "noSpec c"
assumes noSpec_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. noSpec (the (\<Gamma> p))"
assumes procs_subset: "procs c \<subseteq> dom \<Gamma>"
assumes procs_subset_\<Gamma>: "\<forall>p \<in> dom \<Gamma>. procs (the (\<Gamma> p)) \<subseteq> dom \<Gamma>"
shows "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub>{s. s=\<sigma>} c {t. \<forall>l. P \<sigma> l \<longrightarrow> Q \<sigma> l t},{}"
apply (rule allI)
apply (rule LiberalConseq_noguards_nothrows
              [OF spec _ noguards_c noguards_\<Gamma> nothrows_c nothrows_\<Gamma>
                  noSpec_c noSpec_\<Gamma> 
                  procs_subset procs_subset_\<Gamma>])
apply auto
done

subsubsection {* Modify Return *}

lemma ProcModifyReturn_sound:
  assumes valid_call: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P call init p return' c Q,A"
  assumes valid_modif: 
    "\<forall>\<sigma>. \<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/UNIV\<^esub> {\<sigma>} Call p (Modif \<sigma>),(ModifAbr \<sigma>)" 
  assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) 
           \<longrightarrow> return' s t = return s t"
  assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) 
                             \<longrightarrow> return' s t = return s t"
  shows "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P (call init p return c) Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  then have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/UNIV\<^esub> P (Call p) Q,A"
    by (auto intro: nvalid_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>call init p return c,Normal s\<rangle> =n\<Rightarrow> t"
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  from exec
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: execn_call_Normal_elim)
    fix bdy m t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> =Suc m\<Rightarrow> t" 
    assume n: "n = Suc m"
    from exec_body n bdy
    have "\<Gamma>\<turnstile>\<langle>Call p,Normal (init s)\<rangle> =n\<Rightarrow> Normal t'"
      by (auto simp add: intro: execn.Call)
    from cnvalidD [OF valid_modif [rule_format, of n "init s"] ctxt' this] P
    have "t' \<in> Modif (init s)"
      by auto
    with ret_modif have "Normal (return' s t') = 
      Normal (return s t')"
      by simp
    with exec_body exec_c bdy n
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_call)
    from cnvalidD [OF valid_call [rule_format] ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Abrupt t'" 
    assume n: "n = Suc m"
    assume t: "t = Abrupt (return s t')"
    also from exec_body n bdy
    have "\<Gamma>\<turnstile>\<langle>Call p,Normal (init s)\<rangle> =n\<Rightarrow> Abrupt t'"
      by (auto simp add: intro: execn.intros)
    from cnvalidD [OF valid_modif [rule_format, of n "init s"] ctxt' this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')"  .
    with exec_body bdy n
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_callAbrupt)
    from cnvalidD [OF valid_call [rule_format] ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m f
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Fault f" "n = Suc m" 
      "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callFault)
    from valid_call [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    fix bdy m
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Stuck" "n = Suc m" 
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callStuck)
    from valid_call [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    fix m
    assume "\<Gamma> p = None"
    and  "n = Suc m" "t = Stuck"
    then have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callUndefined)
    from valid_call [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  qed
qed


lemma ProcModifyReturn:
  assumes spec: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (call init p return' c) Q,A"
  assumes result_conform:
      "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes return_conform:
      "\<forall>s t. t \<in> ModifAbr (init s) 
             \<longrightarrow> (return' s t) = (return s t)"
  assumes modifies_spec:  
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call p (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (call init p return c) Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule ProcModifyReturn_sound 
          [where Modif=Modif and ModifAbr=ModifAbr, 
            OF _ _ result_conform return_conform] )
using spec
apply (blast intro: hoare_cnvalid)
using modifies_spec
apply (blast intro: hoare_cnvalid)
done

lemma ProcModifyReturnSameFaults_sound:
  assumes valid_call: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P call init p return' c Q,A"
  assumes valid_modif: 
    "\<forall>\<sigma>. \<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> {\<sigma>} Call p (Modif \<sigma>),(ModifAbr \<sigma>)" 
  assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) 
           \<longrightarrow> return' s t = return s t"
  assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) 
                             \<longrightarrow> return' s t = return s t"
  shows "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P (call init p return c) Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>call init p return c,Normal s\<rangle> =n\<Rightarrow> t"
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  from exec
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: execn_call_Normal_elim)
    fix bdy m t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> =Suc m\<Rightarrow> t" 
    assume n: "n = Suc m"
    from exec_body n bdy 
    have "\<Gamma>\<turnstile>\<langle>Call p,Normal (init s)\<rangle> =n\<Rightarrow> Normal t'"
      by (auto simp add: intro: execn.intros)
    from cnvalidD [OF valid_modif [rule_format, of n "init s"] ctxt this] P
    have "t' \<in> Modif (init s)"
      by auto
    with ret_modif have "Normal (return' s t') = 
      Normal (return s t')"
      by simp
    with exec_body exec_c bdy n
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_call)
    from cnvalidD [OF valid_call [rule_format] ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Abrupt t'" 
    assume n: "n = Suc m"
    assume t: "t = Abrupt (return s t')"
    also 
    from exec_body n bdy
    have "\<Gamma>\<turnstile>\<langle>Call p,Normal (init s)\<rangle> =n \<Rightarrow> Abrupt t'"
      by (auto simp add: intro: execn.intros)
    from cnvalidD [OF valid_modif [rule_format, of n "init s"] ctxt this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')" .
    with exec_body bdy n
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_callAbrupt)
    from cnvalidD [OF valid_call [rule_format] ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m f
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Fault f" "n = Suc m"  and
      t: "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callFault)
    from cnvalidD [OF valid_call [rule_format] ctxt this P] t t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Stuck" "n = Suc m" 
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callStuck)
    from valid_call [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    fix m
    assume "\<Gamma> p = None"
    and  "n = Suc m" "t = Stuck"
    then have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callUndefined)
    from valid_call [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  qed
qed


lemma ProcModifyReturnSameFaults:
  assumes spec: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (call init p return' c) Q,A"
  assumes result_conform:
      "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes return_conform:
  "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes modifies_spec:  
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Call p (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (call init p return c) Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule ProcModifyReturnSameFaults_sound 
          [where Modif=Modif and ModifAbr=ModifAbr, 
         OF _ _ result_conform return_conform])
using spec
apply (blast intro: hoare_cnvalid)
using modifies_spec
apply (blast intro: hoare_cnvalid)
done

subsubsection {* DynCall *}
  
lemma dynProcModifyReturn_sound:
assumes valid_call: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes valid_modif: 
    "\<forall>s \<in> P. \<forall>\<sigma>. \<forall>n. 
       \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/UNIV\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)" 
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) 
           \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) 
                             \<longrightarrow> return' s t = return s t"
shows "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  then have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/UNIV\<^esub> P (Call p) Q,A"
    by (auto intro: nvalid_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>dynCall init p return c,Normal s\<rangle> =n\<Rightarrow> t"
  assume t_notin_F: "t \<notin> Fault ` F"
  assume P: "s \<in> P"
  with valid_modif 
  have valid_modif': "\<forall>\<sigma>. \<forall>n. 
       \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/UNIV\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)"
    by blast
  from exec
  have "\<Gamma>\<turnstile>\<langle>call init (p s) return c,Normal s\<rangle> =n\<Rightarrow> t"
    by (cases rule: execn_dynCall_Normal_elim)
  then show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: execn_call_Normal_elim)
    fix bdy m t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> =Suc m\<Rightarrow> t" 
    assume n: "n = Suc m"
    from exec_body n bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s) ,Normal (init s)\<rangle> =n\<Rightarrow> Normal t'"
      by (auto simp add: intro: execn.intros)
    from cnvalidD [OF valid_modif' [rule_format, of n "init s"] ctxt' this] P
    have "t' \<in> Modif (init s)"
      by auto
    with ret_modif have "Normal (return' s t') = Normal (return s t')"
      by simp
    with exec_body exec_c bdy n
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_call)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from cnvalidD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Abrupt t'" 
    assume n: "n = Suc m"
    assume t: "t = Abrupt (return s t')"
    also from exec_body n bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s) ,Normal (init s)\<rangle> =n\<Rightarrow> Abrupt t'"
      by (auto simp add: intro: execn.intros)
    from cnvalidD [OF valid_modif' [rule_format, of n "init s"] ctxt' this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')" .
    with exec_body bdy n
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_callAbrupt)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from cnvalidD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m f
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Fault f" "n = Suc m" 
      "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callFault)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    fix bdy m
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Stuck" "n = Suc m" 
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callStuck)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    fix m
    assume "\<Gamma> (p s) = None"
    and  "n = Suc m" "t = Stuck"
    hence "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callUndefined)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  qed
qed

lemma dynProcModifyReturn:
assumes dyn_call: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) 
           \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) 
                             \<longrightarrow> return' s t = return s t"
assumes modif: 
    "\<forall>s \<in> P. \<forall>\<sigma>.  
       \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)" 
shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule dynProcModifyReturn_sound [where Modif=Modif and ModifAbr=ModifAbr,
          OF hoare_cnvalid [OF dyn_call] _ ret_modif ret_modifAbr])
apply (intro ballI allI)
apply (rule hoare_cnvalid [OF modif [rule_format]])
apply assumption
done

lemma dynProcModifyReturnSameFaults_sound:
assumes valid_call: "\<And>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes valid_modif: 
    "\<forall>s \<in> P. \<forall>\<sigma>. \<forall>n. 
       \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)" 
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> return' s t = return s t"
shows "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>dynCall init p return c,Normal s\<rangle> =n\<Rightarrow> t"
  assume t_notin_F: "t \<notin> Fault ` F"
  assume P: "s \<in> P"
  with valid_modif 
  have valid_modif': "\<forall>\<sigma>. \<forall>n. 
    \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)"
    by blast
  from exec
  have "\<Gamma>\<turnstile>\<langle>call init (p s) return c,Normal s\<rangle> =n\<Rightarrow> t"
    by (cases rule: execn_dynCall_Normal_elim)
  then show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: execn_call_Normal_elim)
    fix bdy m t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> =Suc m\<Rightarrow> t" 
    assume n: "n = Suc m"
    from exec_body n bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s) ,Normal (init s)\<rangle> =n \<Rightarrow> Normal t'"
      by (auto simp add: intro: execn.Call)
    from cnvalidD [OF valid_modif' [rule_format, of n "init s"] ctxt this] P
    have "t' \<in> Modif (init s)"
      by auto
    with ret_modif have "Normal (return' s t') = Normal (return s t')"
      by simp
    with exec_body exec_c bdy n
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_call)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from cnvalidD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Abrupt t'" 
    assume n: "n = Suc m"
    assume t: "t = Abrupt (return s t')"
    also from exec_body n bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s) ,Normal (init s)\<rangle> =n \<Rightarrow> Abrupt t'"
      by (auto simp add: intro: execn.intros)
    from cnvalidD [OF valid_modif' [rule_format, of n "init s"] ctxt this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')" .
    with exec_body bdy n
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (auto intro: execn_callAbrupt)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from cnvalidD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m f
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Fault f" "n = Suc m"  and
      t: "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callFault)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from cnvalidD [OF valid_call ctxt this P] t t_notin_F
    show ?thesis
      by simp
  next
    fix bdy m
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> =m\<Rightarrow> Stuck" "n = Suc m" 
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callStuck)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    fix m
    assume "\<Gamma> (p s) = None"
    and  "n = Suc m" "t = Stuck"
    hence "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> =n\<Rightarrow> t"
      by (auto intro: execn_callUndefined)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> =n\<Rightarrow> t" 
      by (rule execn_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  qed
qed

lemma dynProcModifyReturnSameFaults:
assumes dyn_call: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) 
           \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) 
                             \<longrightarrow> return' s t = return s t"
assumes modif: 
    "\<forall>s \<in> P. \<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)" 
shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule dynProcModifyReturnSameFaults_sound 
        [where Modif=Modif and ModifAbr=ModifAbr,
           OF hoare_cnvalid [OF dyn_call] _ ret_modif ret_modifAbr])
apply (intro ballI allI)
apply (rule hoare_cnvalid [OF modif [rule_format]])
apply assumption
done


subsubsection {* Conjunction of Postcondition *}

lemma PostConjI_sound:
assumes valid_Q: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A" 
assumes valid_R: "\<forall>n. \<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P c R,B"
shows "\<Gamma>,\<Theta> \<Turnstile>n:\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> B)"
proof (rule cnvalidI)
  fix s t 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume t_notin_F: "t \<notin> Fault ` F"
  from valid_Q [rule_format] ctxt exec P t_notin_F have "t \<in> Normal ` Q \<union> Abrupt ` A"
    by (rule cnvalidD)
  moreover
  from valid_R [rule_format] ctxt exec P t_notin_F have "t \<in> Normal ` R \<union> Abrupt ` B"
    by (rule cnvalidD)
  ultimately show "t \<in> Normal ` (Q \<inter> R) \<union> Abrupt ` (A \<inter> B)"
    by blast
qed

lemma PostConjI: 
  assumes deriv_Q: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A" 
  assumes deriv_R: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c R,B"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> B)"
apply (rule hoare_complete')
apply (rule allI)
apply (rule PostConjI_sound)
using deriv_Q
apply (blast intro: hoare_cnvalid)
using deriv_R
apply (blast intro: hoare_cnvalid)
done

lemma Merge_PostConj_sound: 
  assumes validF: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  assumes validG: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/G\<^esub> P' c R,X"
  assumes F_G: "F \<subseteq> G"
  assumes P_P': "P \<subseteq> P'"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> X)"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
  with F_G have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/G\<^esub> P (Call p) Q,A" 
    by (auto intro: nvalid_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P" 
  with P_P' have P': "s \<in> P'"
    by auto
  assume t_noFault: "t \<notin> Fault ` F"
  show "t \<in> Normal ` (Q \<inter> R) \<union> Abrupt ` (A \<inter> X)"
  proof -
    from cnvalidD [OF validF [rule_format] ctxt exec P t_noFault]
    have "t \<in> Normal ` Q \<union> Abrupt ` A".
    moreover from this have "t \<notin> Fault ` G"
      by auto
    from cnvalidD [OF validG [rule_format] ctxt' exec P' this]
    have "t \<in> Normal ` R \<union> Abrupt ` X" .
    ultimately show ?thesis by auto
  qed
qed

lemma Merge_PostConj: 
  assumes validF: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  assumes validG: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/G\<^esub> P' c R,X"
  assumes F_G: "F \<subseteq> G"
  assumes P_P': "P \<subseteq> P'"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> X)"
apply (rule hoare_complete')
apply (rule allI)
apply (rule Merge_PostConj_sound [OF _ _ F_G P_P'])
using validF apply (blast intro:hoare_cnvalid)
using validG apply (blast intro:hoare_cnvalid)
done

subsubsection {* Weaken Context *}


lemma WeakenContext_sound:
  assumes valid_c: "\<forall>n. \<Gamma>,\<Theta>'\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  assumes valid_ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>'. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  with valid_ctxt
  have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>'. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
    by (simp add: cnvalid_def)
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  from valid_c [rule_format] ctxt' exec P t_notin_F
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
    by (rule cnvalidD)
qed

lemma WeakenContext: 
  assumes deriv_c: "\<Gamma>,\<Theta>'\<turnstile>\<^bsub>/F\<^esub> P c Q,A" 
  assumes deriv_ctxt: "\<forall>(P,p,Q,A)\<in>\<Theta>'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule WeakenContext_sound)
using deriv_c
apply (blast intro: hoare_cnvalid)
using deriv_ctxt
apply (blast intro: hoare_cnvalid)
done

subsubsection {* Guards and Guarantees *}

lemma SplitGuards_sound:
assumes valid_c1: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c\<^sub>1 Q,A"
assumes valid_c2: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c\<^sub>2 UNIV,UNIV"
assumes c: "(c\<^sub>1 \<inter>\<^sub>g c\<^sub>2) = Some c"
shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases t)
    case Normal
    with inter_guards_execn_noFault [OF c exec]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow> t" by simp
    from valid_c1 [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    case Abrupt
    with inter_guards_execn_noFault [OF c exec]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow> t" by simp
    from valid_c1 [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  next
    case (Fault f)
    with exec inter_guards_execn_Fault [OF c]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> =n\<Rightarrow> Fault f"
      by auto
    then show ?thesis
    proof (cases rule: disjE [consumes 1])
      assume "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow> Fault f"
      from Fault cnvalidD [OF valid_c1 [rule_format] ctxt this P] t_notin_F
      show ?thesis
        by blast
    next
      assume "\<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> =n\<Rightarrow> Fault f"
      from Fault cnvalidD [OF valid_c2 [rule_format] ctxt this P] t_notin_F
      show ?thesis
        by blast
    qed
  next
    case Stuck
    with inter_guards_execn_noFault [OF c exec]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> =n\<Rightarrow> t" by simp
    from valid_c1 [rule_format] ctxt this P t_notin_F
    show ?thesis
      by (rule cnvalidD)
  qed
qed

lemma SplitGuards: 
  assumes c: "(c\<^sub>1 \<inter>\<^sub>g c\<^sub>2) = Some c" 
  assumes deriv_c1: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c\<^sub>1 Q,A" 
  assumes deriv_c2: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c\<^sub>2 UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule SplitGuards_sound [OF _ _ c])
using deriv_c1
apply (blast intro: hoare_cnvalid)
using deriv_c2
apply (blast intro: hoare_cnvalid)
done

lemma CombineStrip_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  assumes valid_strip: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P (strip_guards (-F) c) UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto intro: nvalid_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases t)
    case (Normal t')
    from cnvalidD [OF valid [rule_format] ctxt' exec P] Normal 
    show ?thesis
      by auto
  next
    case (Abrupt t')
    from cnvalidD [OF valid [rule_format] ctxt' exec P] Abrupt 
    show ?thesis
      by auto
  next
    case (Fault f)
    show ?thesis
    proof (cases "f \<in> F")
      case True
      hence "f \<notin> -F" by simp
      with exec Fault
      have "\<Gamma>\<turnstile>\<langle>strip_guards (-F) c,Normal s\<rangle> =n\<Rightarrow> Fault f" 
        by (auto intro: execn_to_execn_strip_guards_Fault)
      from cnvalidD [OF valid_strip [rule_format] ctxt this P] Fault
      have False
        by auto
      thus ?thesis ..
    next
      case False
      with cnvalidD [OF valid [rule_format] ctxt' exec P] Fault
      show ?thesis
        by auto
    qed
  next
    case Stuck
    from cnvalidD [OF valid [rule_format] ctxt' exec P] Stuck
    show ?thesis
      by auto
  qed
qed

lemma CombineStrip: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  assumes deriv_strip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P (strip_guards (-F) c) UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule CombineStrip_sound)
apply  (iprover intro: hoare_cnvalid [OF deriv])
apply (iprover intro: hoare_cnvalid [OF deriv_strip])
done

lemma GuardsFlip_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  assumes validFlip: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/-F\<^esub> P c UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto intro: nvalid_augment_Faults)
  from ctxt have ctxtFlip: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/-F\<^esub> P (Call p) Q,A" 
    by (auto intro: nvalid_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases t)
    case (Normal t')
    from cnvalidD [OF valid [rule_format] ctxt' exec P] Normal 
    show ?thesis
      by auto
  next
    case (Abrupt t')
    from cnvalidD [OF valid [rule_format] ctxt' exec P] Abrupt 
    show ?thesis
      by auto
  next
    case (Fault f)
    show ?thesis
    proof (cases "f \<in> F")
      case True
      hence "f \<notin> -F" by simp
      with cnvalidD [OF validFlip [rule_format] ctxtFlip exec P] Fault
      have False
        by auto
      thus ?thesis ..
    next
      case False
      with cnvalidD [OF valid [rule_format] ctxt' exec P] Fault
      show ?thesis
        by auto
    qed
  next
    case Stuck
    from cnvalidD [OF valid [rule_format] ctxt' exec P] Stuck
    show ?thesis
      by auto
  qed
qed

lemma GuardsFlip: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  assumes derivFlip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/-F\<^esub> P c UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule GuardsFlip_sound)
apply  (iprover intro: hoare_cnvalid [OF deriv])
apply (iprover intro: hoare_cnvalid [OF derivFlip])
done

lemma MarkGuardsI_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P mark_guards f c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>mark_guards f c,Normal s\<rangle> =n\<Rightarrow> t" 
  from execn_mark_guards_to_execn [OF exec] obtain t' where
    exec_c: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t'" and
    t'_noFault: "\<not> isFault t' \<longrightarrow> t' = t"
    by blast
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof -
    from cnvalidD [OF valid [rule_format] ctxt exec_c P]
    have "t' \<in> Normal ` Q \<union> Abrupt ` A"
      by blast
    with t'_noFault
    show ?thesis
      by auto
  qed
qed

lemma MarkGuardsI: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P mark_guards f c Q,A"  
apply (rule hoare_complete')
apply (rule allI)
apply (rule MarkGuardsI_sound)
apply (iprover intro: hoare_cnvalid [OF deriv])
done

lemma MarkGuardsD_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P mark_guards f c Q,A" 
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t"
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases "isFault t")
    case True
    with execn_to_execn_mark_guards_Fault [OF exec ]
    obtain f' where "\<Gamma>\<turnstile>\<langle>mark_guards f c,Normal s\<rangle> =n\<Rightarrow> Fault f'"
      by (fastforce elim: isFaultE)
    from cnvalidD [OF valid [rule_format] ctxt this P]
    have False
      by auto
    thus ?thesis ..
  next
    case False
    from execn_to_execn_mark_guards [OF exec False]
    obtain f' where "\<Gamma>\<turnstile>\<langle>mark_guards f c,Normal s\<rangle> =n\<Rightarrow> t"
      by auto
    from cnvalidD [OF valid [rule_format] ctxt this P]
    show ?thesis
      by auto
  qed
qed

lemma MarkGuardsD: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P mark_guards f c Q,A" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule MarkGuardsD_sound)
apply (iprover intro: hoare_cnvalid [OF deriv])
done

lemma MergeGuardsI_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P merge_guards c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume exec_merge: "\<Gamma>\<turnstile>\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t"
  from execn_merge_guards_to_execn [OF exec_merge] 
  have exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" .
  assume P: "s \<in> P" 
  assume t_notin_F: "t \<notin> Fault ` F"
  from cnvalidD [OF valid [rule_format] ctxt exec P t_notin_F]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
qed

lemma MergeGuardsI: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P merge_guards c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule MergeGuardsI_sound)
apply (iprover intro: hoare_cnvalid [OF deriv])
done

lemma MergeGuardsD_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P merge_guards c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  from execn_to_execn_merge_guards [OF exec] 
  have exec_merge: "\<Gamma>\<turnstile>\<langle>merge_guards c,Normal s\<rangle> =n\<Rightarrow> t".
  assume P: "s \<in> P" 
  assume t_notin_F: "t \<notin> Fault ` F"
  from cnvalidD [OF valid [rule_format] ctxt exec_merge P t_notin_F]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
qed

lemma MergeGuardsD: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P merge_guards c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule MergeGuardsD_sound)
apply (iprover intro: hoare_cnvalid [OF deriv])
done


lemma SubsetGuards_sound: 
  assumes c_c': "c \<subseteq>\<^sub>g c'"
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P c' Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  from execn_to_execn_subseteq_guards [OF c_c' exec] obtain t' where
    exec_c': "\<Gamma>\<turnstile>\<langle>c',Normal s\<rangle> =n\<Rightarrow> t'" and
    t'_noFault: "\<not> isFault t' \<longrightarrow> t' = t"
    by blast
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  from cnvalidD [OF valid [rule_format] ctxt exec_c' P] t'_noFault t_noFault
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
    by auto
qed

lemma SubsetGuards: 
  assumes c_c': "c \<subseteq>\<^sub>g c'"
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c' Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule SubsetGuards_sound [OF c_c'])
apply (iprover intro: hoare_cnvalid [OF deriv])
done

lemma NormalizeD_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P (normalize c) Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  hence exec_norm: "\<Gamma>\<turnstile>\<langle>normalize c,Normal s\<rangle> =n\<Rightarrow> t" 
    by (rule execn_to_execn_normalize)
  assume P: "s \<in> P" 
  assume noFault: "t \<notin> Fault ` F"
  from cnvalidD [OF valid [rule_format] ctxt exec_norm P noFault]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
qed

lemma NormalizeD: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (normalize c) Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule NormalizeD_sound)
apply (iprover intro: hoare_cnvalid [OF deriv])
done

lemma NormalizeI_sound: 
  assumes valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P (normalize c) Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume "\<Gamma>\<turnstile>\<langle>normalize c,Normal s\<rangle> =n\<Rightarrow> t" 
  hence exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
    by (rule execn_normalize_to_execn)
  assume P: "s \<in> P" 
  assume noFault: "t \<notin> Fault ` F"
  from cnvalidD [OF valid [rule_format] ctxt exec P noFault]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
qed

lemma NormalizeI: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (normalize c) Q,A"
apply (rule hoare_complete')
apply (rule allI)
apply (rule NormalizeI_sound)
apply (iprover intro: hoare_cnvalid [OF deriv])
done


subsubsection {* Restricting the Procedure Environment *}

lemma nvalid_restrict_to_nvalid:
assumes valid_c: "\<Gamma>|\<^bsub>M\<^esub>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
shows "\<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A"
proof (rule nvalidI)
  fix s t
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof -
    from execn_to_execn_restrict [OF exec]
    obtain t' where
      exec_res: "\<Gamma>|\<^bsub>M\<^esub>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t'" and
      t_Fault: "\<forall>f. t = Fault f \<longrightarrow> t' \<in> {Fault f, Stuck}" and
      t'_notStuck: "t'\<noteq>Stuck \<longrightarrow> t'=t"
      by blast
    from t_Fault t_notin_F t'_notStuck have "t' \<notin> Fault ` F"
      by (cases t') auto
    with valid_c exec_res P 
    have "t' \<in> Normal ` Q \<union> Abrupt ` A"
      by (auto simp add: nvalid_def)
    with t'_notStuck
    show ?thesis
      by auto
  qed
qed

lemma valid_restrict_to_valid:
assumes valid_c: "\<Gamma>|\<^bsub>M\<^esub>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
shows "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
proof (rule validI)
  fix s t
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof -
    from exec_to_exec_restrict [OF exec]
    obtain t' where
      exec_res: "\<Gamma>|\<^bsub>M\<^esub>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t'" and
      t_Fault: "\<forall>f. t = Fault f \<longrightarrow> t' \<in> {Fault f, Stuck}" and
      t'_notStuck: "t'\<noteq>Stuck \<longrightarrow> t'=t"
      by blast
    from t_Fault t_notin_F t'_notStuck have "t' \<notin> Fault ` F"
      by (cases t') auto
    with valid_c exec_res P
    have "t' \<in> Normal ` Q \<union> Abrupt ` A"
      by (auto simp add: valid_def)
    with t'_notStuck
    show ?thesis
      by auto
  qed
qed

lemma augment_procs:
assumes deriv_c: "\<Gamma>|\<^bsub>M\<^esub>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
shows "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  apply (rule hoare_complete)
  apply (rule valid_restrict_to_valid)
  apply (insert hoare_sound [OF deriv_c])
  by (simp add: cvalid_def)

lemma augment_Faults:
assumes deriv_c: "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
assumes F: "F \<subseteq> F'"
shows "\<Gamma>,{}\<turnstile>\<^bsub>/F'\<^esub> P c Q,A"
  apply (rule hoare_complete)
  apply (rule valid_augment_Faults [OF _ F])
  apply (insert hoare_sound [OF deriv_c])
  by (simp add: cvalid_def)

end