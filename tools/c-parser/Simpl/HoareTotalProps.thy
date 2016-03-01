(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      HoarePartial.thy
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

section {* Properties of Total Correctness Hoare Logic *}

theory HoareTotalProps imports SmallStep HoareTotalDef HoarePartialProps begin

subsection {* Soundness *}

lemma hoaret_sound: 
 assumes hoare: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
 shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
using hoare
proof (induct)
  case (Skip \<Theta> F P A)
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P Skip P,A"
  proof (rule cvalidtI)
    fix s t
    assume "\<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow> t" "s \<in> P"
    thus "t \<in> Normal ` P \<union> Abrupt ` A"
      by cases auto
  next
    fix s show "\<Gamma>\<turnstile>Skip \<down> Normal s"
      by (rule terminates.intros)
  qed
next
  case (Basic \<Theta> F f P A)
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. f s \<in> P} (Basic f) P,A"
  proof (rule cvalidtI)
    fix s t
    assume "\<Gamma>\<turnstile>\<langle>Basic f,Normal s\<rangle> \<Rightarrow> t" "s \<in> {s. f s \<in> P}"
    thus "t \<in> Normal ` P \<union> Abrupt ` A"
      by cases auto
  next
    fix s show "\<Gamma>\<turnstile>Basic f \<down> Normal s"
      by (rule terminates.intros)
  qed
next
  case (Spec \<Theta> F r Q A)
  show "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)} Spec r Q,A"
  proof (rule cvalidtI)
    fix s t
    assume "\<Gamma>\<turnstile>\<langle>Spec r ,Normal s\<rangle> \<Rightarrow> t" 
           "s \<in> {s. (\<forall>t. (s, t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s, t) \<in> r)}"
    thus "t \<in> Normal ` Q \<union> Abrupt ` A"
      by cases auto
  next
    fix s show "\<Gamma>\<turnstile>Spec r \<down> Normal s"
      by (rule terminates.intros)
  qed
next
  case (Seq \<Theta> F P c1 R A c2 Q)
  have valid_c1: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c1 R,A" by fact
  have valid_c2: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> R c2 Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P Seq c1 c2 Q,A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow> t" 
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F"
    from exec P obtain r where
      exec_c1: "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> r" and exec_c2:  "\<Gamma>\<turnstile>\<langle>c2,r\<rangle> \<Rightarrow> t"
      by cases auto
    with t_notin_F have "r \<notin> Fault ` F"
      by (auto dest: Fault_end)
    from valid_c1 ctxt exec_c1 P this
    have r: "r \<in> Normal ` R \<union> Abrupt ` A"
      by (rule cvalidt_postD)
    show "t\<in>Normal ` Q \<union> Abrupt ` A"
    proof (cases r)
      case (Normal r')
      with exec_c2 r
      show "t\<in>Normal ` Q \<union> Abrupt ` A"
        apply -
        apply (rule cvalidt_postD [OF valid_c2 ctxt _ _ t_notin_F])
        apply auto
        done
    next
      case (Abrupt r')
      with exec_c2 have "t=Abrupt r'"
        by (auto elim: exec_elim_cases)
      with Abrupt r show ?thesis
        by auto
    next
      case Fault with r show ?thesis by blast
    next
      case Stuck with r show ?thesis by blast
    qed
  next
    fix s 
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume P: "s\<in>P"
    show "\<Gamma>\<turnstile>Seq c1 c2 \<down> Normal s"
    proof -
      from valid_c1 ctxt P
      have "\<Gamma>\<turnstile>c1\<down> Normal s"
        by (rule cvalidt_termD)
      moreover
      {
        fix r assume exec_c1: "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> r"
        have "\<Gamma>\<turnstile>c2 \<down> r"
        proof (cases r)
          case (Normal r')
          with cvalidt_postD [OF valid_c1 ctxt exec_c1 P]
          have r: "r\<in>Normal ` R"
            by auto
          with cvalidt_termD [OF valid_c2 ctxt] exec_c1
          show "\<Gamma>\<turnstile>c2 \<down> r"
            by auto
        qed auto        
      }
      ultimately show ?thesis
        by (iprover intro: terminates.intros)
    qed
  qed
next
  case (Cond \<Theta> F P b c1 Q A c2)
  have valid_c1: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> (P \<inter> b) c1 Q,A" by fact
  have valid_c2: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> (P \<inter> - b) c2 Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P Cond b c1 c2 Q,A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow> t"
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F"
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof (cases "s\<in>b")
      case True
      with exec have "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> t"
        by cases auto
      with P True 
      show ?thesis
        by - (rule cvalidt_postD [OF valid_c1 ctxt _ _ t_notin_F],auto)
    next
      case False
      with exec P have "\<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow> t"
        by cases auto
      with P False 
      show ?thesis
        by - (rule cvalidt_postD [OF valid_c2 ctxt _ _ t_notin_F],auto)
    qed
  next
    fix s
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume P: "s \<in> P"
    thus "\<Gamma>\<turnstile>Cond b c1 c2 \<down> Normal s"
      using cvalidt_termD [OF valid_c1 ctxt] cvalidt_termD [OF valid_c2 ctxt]
      by (cases "s \<in> b") (auto intro: terminates.intros)
  qed
next
  case (While r \<Theta> F P b c A)
  assume wf: "wf r"
  have valid_c: "\<forall>\<sigma>. \<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P \<inter> b) c ({t. (t, \<sigma>) \<in> r} \<inter> P),A"
    using While.hyps by iprover
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (While b c) (P \<inter> - b),A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume wprems: "\<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow> t" "s \<in> P" "t \<notin> Fault ` F"
    from wf
    have "\<And>t. \<lbrakk>\<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow> t; s \<in> P; t \<notin> Fault ` F\<rbrakk> 
                 \<Longrightarrow> t \<in> Normal ` (P \<inter> - b) \<union> Abrupt ` A"
    proof (induct)
      fix s t
      assume hyp: 
        "\<And>s' t. \<lbrakk>(s',s)\<in>r; \<Gamma>\<turnstile>\<langle>While b c,Normal s'\<rangle> \<Rightarrow> t; s' \<in> P; t \<notin> Fault ` F\<rbrakk>
                 \<Longrightarrow> t \<in> Normal ` (P \<inter> - b) \<union> Abrupt ` A"
      assume exec: "\<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow> t"
      assume P: "s \<in> P"
      assume t_notin_F: "t \<notin> Fault ` F"
      from exec
      show "t \<in> Normal ` (P \<inter> - b) \<union> Abrupt ` A"
      proof (cases)
        fix s'
        assume b: "s\<in>b"
        assume exec_c: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> s'" 
        assume exec_w: "\<Gamma>\<turnstile>\<langle>While b c,s'\<rangle> \<Rightarrow> t"
        from exec_w t_notin_F have "s' \<notin> Fault ` F"
          by (auto dest: Fault_end)
        from exec_c P b valid_c ctxt this
        have s': "s' \<in> Normal ` ({s'. (s', s) \<in> r} \<inter> P) \<union> Abrupt ` A"
          by (auto simp add: cvalidt_def validt_def valid_def)
        show ?thesis
        proof (cases s')
          case Normal 
          with exec_w s' t_notin_F
          show ?thesis
            by - (rule hyp,auto)
        next
          case Abrupt
          with exec_w have "t=s'"
            by (auto dest: Abrupt_end)
          with Abrupt s' show ?thesis
            by blast
        next
          case Fault
          with exec_w have "t=s'"
            by (auto dest: Fault_end)
          with Fault s' show ?thesis
            by blast
        next
          case Stuck
          with exec_w have "t=s'"
            by (auto dest: Stuck_end)
          with Stuck s' show ?thesis
            by blast
        qed
      next
        assume "s\<notin>b" "t=Normal s" with P show ?thesis by simp
      qed
    qed
    with wprems show "t \<in> Normal ` (P \<inter> - b) \<union> Abrupt ` A" by blast
  next
    fix s
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume "s \<in> P"
    with wf 
    show "\<Gamma>\<turnstile>While b c \<down> Normal s"
    proof (induct)
      fix s
      assume hyp: "\<And>s'. \<lbrakk>(s',s)\<in>r; s' \<in> P\<rbrakk> 
                         \<Longrightarrow> \<Gamma>\<turnstile>While b c \<down> Normal s'"
      assume P: "s \<in> P"
      show "\<Gamma>\<turnstile>While b c \<down> Normal s"
      proof (cases "s \<in> b")
        case False with P show ?thesis
          by (blast intro: terminates.intros)
      next
        case True
        with valid_c P ctxt
        have "\<Gamma>\<turnstile>c \<down> Normal s"
          by (simp add: cvalidt_def validt_def)
        moreover
        {
          fix s'
          assume exec_c: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> s'"
          have "\<Gamma>\<turnstile>While b c \<down> s'"
          proof (cases s')
            case (Normal s'')
            with exec_c P True valid_c ctxt
            have s': "s' \<in> Normal ` ({s'. (s', s) \<in> r} \<inter> P)"
              by (fastforce simp add: cvalidt_def validt_def valid_def)
            then show ?thesis
              by (blast intro: hyp)
          qed auto
        }
        ultimately
        show ?thesis
          by (blast intro: terminates.intros)
      qed
    qed
  qed
next
  case (Guard \<Theta> F g P c Q A  f)
  have valid_c: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> P) c Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> P) Guard f g c Q,A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow> t"
    assume t_notin_F: "t \<notin> Fault ` F"
    assume P:"s \<in> (g \<inter> P)"
    from exec P have "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t"
      by cases auto
    from valid_c ctxt this P t_notin_F
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
      by (rule cvalidt_postD)
  next
    fix s
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume P:"s \<in> (g \<inter> P)"
    thus "\<Gamma>\<turnstile>Guard f g c  \<down> Normal s"
      by (auto intro: terminates.intros cvalidt_termD [OF valid_c ctxt])
  qed
next
  case (Guarantee f F \<Theta> g P c Q A)
  have valid_c: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> P) c Q,A" by fact
  have f_F: "f \<in> F" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P Guard f g c Q,A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow> t"
    assume t_notin_F: "t \<notin> Fault ` F"
    assume P:"s \<in> P"
    from exec f_F t_notin_F have g: "s \<in> g"
      by cases auto
    with P have P': "s \<in> g \<inter> P"
      by blast
    from exec g have "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t"
      by cases auto
    from valid_c ctxt this P' t_notin_F
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
      by (rule cvalidt_postD)
  next
    fix s
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume P:"s \<in> P"
    thus "\<Gamma>\<turnstile>Guard f g c  \<down> Normal s"
      by (auto intro: terminates.intros cvalidt_termD [OF valid_c ctxt])
  qed
next
  case (CallRec P p Q A Specs r Specs_wf \<Theta>  F)
  have p: "(P,p,Q,A) \<in> Specs"  by fact
  have wf: "wf r" by fact
  have Specs_wf: 
    "Specs_wf = (\<lambda>p \<tau>. (\<lambda>(P,q,Q,A). (P \<inter> {s. ((s, q),\<tau>,p) \<in> r},q,Q,A)) ` Specs)" by fact
  from CallRec.hyps
  have valid_body: 
    "\<forall>(P, p, Q, A)\<in>Specs. p \<in> dom \<Gamma> \<and>
        (\<forall>\<tau>. \<Gamma>,\<Theta> \<union> Specs_wf p \<tau>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> P) the (\<Gamma> p) Q,A)" by auto
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  proof -
    {
      fix \<tau>p 
      assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
      from wf
      have "\<And>\<tau> p P Q A.  \<lbrakk>\<tau>p = (\<tau>,p); (P,p,Q,A) \<in> Specs\<rbrakk> \<Longrightarrow> 
                  \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> P) (the (\<Gamma> (p))) Q,A"    
      proof (induct \<tau>p rule: wf_induct [rule_format, consumes 1, case_names WF])
        case (WF \<tau>p \<tau> p P Q A)
        have \<tau>p: "\<tau>p = (\<tau>, p)" by fact
        have p: "(P, p, Q, A) \<in> Specs" by fact
        {
          fix q P' Q' A'
          assume q: "(P',q,Q',A') \<in> Specs"
          have "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' \<inter> {s. ((s,q), \<tau>,p) \<in> r}) (Call q) Q',A'"
          proof (rule validtI)
            fix s t
            assume exec_q: 
              "\<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow> t"
            assume Pre: "s \<in> P' \<inter> {s. ((s,q), \<tau>,p) \<in> r}"
            assume t_notin_F: "t \<notin> Fault ` F"
            from Pre q \<tau>p
            have valid_bdy: 
              "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s} \<inter> P') the (\<Gamma> q) Q',A'"
              by - (rule WF.hyps, auto)
            from Pre q
            have Pre': "s \<in> {s} \<inter> P'"
              by auto
            from exec_q show "t \<in> Normal ` Q' \<union> Abrupt ` A'"
            proof (cases)
              fix bdy 
              assume bdy: "\<Gamma> q = Some bdy"
              assume exec_bdy: "\<Gamma>\<turnstile>\<langle>bdy,Normal s\<rangle> \<Rightarrow> t"
              from valid_bdy [simplified bdy option.sel]  t_notin_F exec_bdy Pre'
              have "t \<in> Normal ` Q' \<union> Abrupt ` A'"
                by (auto simp add: validt_def valid_def)
              with Pre q 
              show ?thesis
                by auto
            next
              assume "\<Gamma> q = None"
              with q valid_body have False by auto
              thus ?thesis ..
            qed
          next
            fix s
            assume Pre: "s \<in> P' \<inter> {s. ((s,q), \<tau>,p) \<in> r}"
            from Pre q \<tau>p
            have valid_bdy: 
              "\<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s} \<inter> P') (the (\<Gamma> q)) Q',A'"
              by - (rule WF.hyps, auto)
            from Pre q
            have Pre': "s \<in> {s} \<inter> P'"
              by auto
            from valid_bdy ctxt Pre'
            have "\<Gamma>\<turnstile>the (\<Gamma> q) \<down> Normal s"
              by (auto simp add: validt_def)
            with valid_body q 
            show "\<Gamma>\<turnstile>Call q\<down> Normal s"
              by (fastforce intro: terminates.Call)
          qed
        }
        hence "\<forall>(P, p, Q, A)\<in>Specs_wf p \<tau>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P Call p Q,A"
          by (auto simp add: cvalidt_def Specs_wf)
        with ctxt have "\<forall>(P, p, Q, A)\<in>\<Theta> \<union> Specs_wf p \<tau>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P Call p Q,A"
          by auto
        with p valid_body 
        show "\<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> P) (the (\<Gamma> p)) Q,A"
          by (simp add: cvalidt_def) blast
      qed
    }
    note lem = this
    have valid_body': 
      "\<And>\<tau>. \<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A \<Longrightarrow> 
      \<forall>(P,p,Q,A)\<in>Specs. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<tau>} \<inter> P) (the (\<Gamma> p)) Q,A"
      by (auto intro: lem)
    show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    proof (rule cvalidtI)
      fix s t
      assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
      assume exec_call: "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow> t"
      assume P: "s \<in> P"
      assume t_notin_F: "t \<notin> Fault ` F"
      from exec_call show "t \<in> Normal ` Q \<union> Abrupt ` A"
      proof (cases)
        fix bdy 
        assume bdy: "\<Gamma> p = Some bdy"
        assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal s\<rangle> \<Rightarrow> t"
        from exec_body bdy p P t_notin_F 
          valid_body' [of "s", OF ctxt] 
          ctxt
        have "t \<in> Normal ` Q \<union> Abrupt ` A"
          apply (simp only: cvalidt_def validt_def valid_def) 
          apply (drule (1) bspec)
          apply auto
          done
        with p P 
        show ?thesis
          by simp
      next
        assume "\<Gamma> p = None"
        with p valid_body have False by auto
        thus ?thesis by simp
      qed
    next
      fix s
      assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
      assume P: "s \<in> P"
      show "\<Gamma>\<turnstile>Call p \<down> Normal s"
      proof -
        from ctxt P p valid_body' [of "s",OF ctxt]
        have "\<Gamma>\<turnstile>(the (\<Gamma> p)) \<down> Normal s"
          by (auto simp add: cvalidt_def validt_def)
        with valid_body p show ?thesis
          by (fastforce intro: terminates.Call)
      qed
    qed
  qed
next
  case (DynCom P \<Theta> F c Q A)
  hence valid_c: "\<forall>s\<in>P. \<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (c s) Q,A" by simp
  show "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P DynCom c Q,A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> \<Rightarrow> t" 
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F"
    from exec show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof (cases)
      assume "\<Gamma>\<turnstile>\<langle>c s,Normal s\<rangle> \<Rightarrow> t"      
      from cvalidt_postD [OF valid_c [rule_format, OF P] ctxt this P t_notin_F]
      show ?thesis .
    qed
  next
    fix s 
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume P: "s \<in> P"
    show "\<Gamma>\<turnstile>DynCom c \<down> Normal s"
    proof -
      from cvalidt_termD [OF valid_c [rule_format, OF P] ctxt P]
      have "\<Gamma>\<turnstile>c s \<down> Normal s" .
      thus ?thesis
        by (rule terminates.intros)
    qed
  qed
next
  case (Throw \<Theta> F A Q)
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> A Throw Q,A"
  proof (rule cvalidtI)
    fix s t
    assume "\<Gamma>\<turnstile>\<langle>Throw,Normal s\<rangle> \<Rightarrow> t" "s \<in> A"
    then show "t \<in> Normal ` Q \<union> Abrupt ` A"
      by cases simp
  next
    fix s
    show "\<Gamma>\<turnstile>Throw \<down> Normal s"
      by (rule terminates.intros)
  qed
next
  case (Catch \<Theta> F P c\<^sub>1 Q R c\<^sub>2 A)
  have valid_c1: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 Q,R" by fact
  have valid_c2: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A" by fact
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P Catch c\<^sub>1 c\<^sub>2 Q,A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow> t" 
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F"
    from exec show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof (cases)
      fix s'
      assume exec_c1: "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt s'" 
      assume exec_c2: "\<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s'\<rangle> \<Rightarrow> t"
      from cvalidt_postD [OF valid_c1 ctxt exec_c1 P]
      have "Abrupt s' \<in> Abrupt ` R"
        by auto
      with cvalidt_postD [OF valid_c2 ctxt] exec_c2 t_notin_F
      show ?thesis
        by fastforce
    next
      assume exec_c1: "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> t" 
      assume notAbr: "\<not> isAbr t"
      from cvalidt_postD [OF valid_c1 ctxt exec_c1 P] t_notin_F
      have "t \<in> Normal ` Q \<union> Abrupt ` R" .
      with notAbr
      show ?thesis
        by auto
    qed
  next
    fix s
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume P: "s \<in> P"
    show "\<Gamma>\<turnstile>Catch c\<^sub>1 c\<^sub>2 \<down> Normal s"  
    proof -
      from valid_c1 ctxt P
      have "\<Gamma>\<turnstile>c\<^sub>1\<down> Normal s"
        by (rule cvalidt_termD)
      moreover
      {
        fix r assume exec_c1: "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Abrupt r"
        from cvalidt_postD [OF valid_c1 ctxt exec_c1 P]
        have r: "Abrupt r\<in>Normal ` Q \<union> Abrupt ` R"
          by auto
        hence "Abrupt r\<in>Abrupt ` R" by fast
        with cvalidt_termD [OF valid_c2 ctxt] exec_c1
        have "\<Gamma>\<turnstile>c\<^sub>2 \<down> Normal r"
          by fast
      }
      ultimately show ?thesis
        by (iprover intro: terminates.intros)
    qed
  qed
next
  case (Conseq P \<Theta> F c Q A)
  hence adapt: 
    "\<forall>s \<in> P. (\<exists>P' Q' A'. (\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q',A') \<and> s \<in> P'\<and> Q' \<subseteq> Q \<and> A' \<subseteq> A)" by blast
  show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  proof (rule cvalidtI)
    fix s t
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
    assume P: "s \<in> P"
    assume t_notin_F: "t \<notin> Fault ` F"
    show "t \<in> Normal ` Q \<union> Abrupt ` A"
    proof -
      from adapt [rule_format, OF P]
      obtain P' and Q' and A' where 
        valid_P'_Q': "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q',A'"
        and weaken: "s \<in> P'" "Q' \<subseteq>  Q" "A'\<subseteq> A"
        by blast
      from exec valid_P'_Q' ctxt t_notin_F
      have P'_Q': "Normal s \<in> Normal ` P' \<longrightarrow> 
        t \<in> Normal ` Q' \<union> Abrupt ` A'"
        by (unfold cvalidt_def validt_def valid_def) blast
      hence "s \<in> P' \<longrightarrow> t \<in> Normal ` Q' \<union> Abrupt ` A'"
        by blast
      with weaken 
      show ?thesis
        by blast
    qed
  next
    fix s
    assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    assume P: "s \<in> P"
    show "\<Gamma>\<turnstile>c \<down> Normal s"
    proof -
      from P adapt
      obtain P' and Q' and  A' where 
        "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q',A'"
        "s \<in> P'"
        by blast
      with ctxt
      show ?thesis
        by (simp add: cvalidt_def validt_def)
    qed
  qed
next
  case (Asm P p Q A \<Theta> F)
  assume "(P, p, Q, A) \<in> \<Theta>"
  then show "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
    by (auto simp add: cvalidt_def )
next
  case ExFalso thus ?case by iprover
qed

lemma hoaret_sound':
"\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  apply (drule hoaret_sound)
  apply (simp add: cvalidt_def)
  done

theorem total_to_partial: 
 assumes total: "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" shows "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
proof -
  from total have "\<Gamma>,{}\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
    by (rule hoaret_sound)
  hence "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
    by (simp add: cvalidt_def validt_def cvalid_def)
  thus ?thesis
    by (rule hoare_complete)
qed

subsection {* Completeness *}

lemma MGT_valid:
"\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F \<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> \<Gamma>\<turnstile>c\<down>Normal s} c 
    {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t}, {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof (rule validtI) 
  fix s t
  assume "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
         "s \<in> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> \<Gamma>\<turnstile>c\<down>Normal s}"
         "t \<notin> Fault ` F"
  thus "t \<in> Normal ` {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t} \<union> 
            Abrupt ` {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    apply (cases t) 
    apply (auto simp add: final_notin_def)
    done
next
  fix s
  assume "s \<in> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> \<Gamma>\<turnstile>c\<down>Normal s}"
  thus "\<Gamma>\<turnstile>c\<down>Normal s"
    by blast
qed

text {* The consequence rule where the existential @{term Z} is instantiated
to @{term s}. Usefull in proof of @{text "MGT_lemma"}.*}
lemma ConseqMGT: 
  assumes modif: "\<forall>Z::'a. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z::'a assn) c (Q' Z),(A' Z)"
  assumes impl: "\<And>s. s \<in> P \<Longrightarrow> s \<in> P' s \<and> (\<forall>t. t \<in> Q' s \<longrightarrow> t \<in> Q) \<and> 
                                            (\<forall>t. t \<in> A' s \<longrightarrow> t \<in> A)"
  shows "\<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
using impl 
by - (rule conseq [OF modif],blast)

lemma MGT_implies_complete:
  assumes MGT: "\<forall>Z. \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                                 \<Gamma>\<turnstile>c\<down>Normal s}
                              c 
                            {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
                            {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  assumes valid: "\<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" 
  shows "\<Gamma>,{} \<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  using MGT
  apply (rule ConseqMGT) 
  apply (insert valid)
  apply (auto simp add: validt_def valid_def intro!: final_notinI)
  done

lemma conseq_extract_state_indep_prop: 
  assumes state_indep_prop:"\<forall>s \<in> P. R" 
  assumes to_show: "R \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  apply (rule Conseq)
  apply (clarify)
  apply (rule_tac x="P" in exI)
  apply (rule_tac x="Q" in exI)
  apply (rule_tac x="A" in exI)
  using state_indep_prop to_show
  by blast

lemma MGT_lemma:
  assumes MGT_Calls: 
    "\<forall>p \<in> dom \<Gamma>. \<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
       {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
           \<Gamma>\<turnstile>(Call p)\<down>Normal s}
             (Call p)
       {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
       {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  shows "\<And>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                          \<Gamma>\<turnstile>c\<down>Normal s} 
               c 
             {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof (induct c)
  case Skip
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>Skip \<down> Normal s} 
               Skip
            {t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Skip [THEN conseqPre])
       (auto elim: exec_elim_cases simp add: final_notin_def 
             intro: exec.intros terminates.intros)
next
  case (Basic f)
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Basic f,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>Basic f \<down> Normal s} 
                Basic f
              {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Basic [THEN conseqPre]) 
       (auto elim: exec_elim_cases simp add: final_notin_def 
             intro: exec.intros terminates.intros)
next
  case (Spec r)
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Spec r,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Spec r \<down> Normal s} 
                Spec r
              {t. \<Gamma>\<turnstile>\<langle>Spec r,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Spec r,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    apply (rule hoaret.Spec [THEN conseqPre])
    apply (clarsimp simp add: final_notin_def)
    apply (case_tac "\<exists>t. (Z,t) \<in> r")
    apply (auto elim: exec_elim_cases simp add: final_notin_def intro: exec.intros)
    done
next
  case (Seq c1 c2) 
  have hyp_c1: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                                \<Gamma>\<turnstile>c1\<down>Normal s}
                            c1 
                           {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
                           {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    using Seq.hyps by iprover
  have hyp_c2: "\<forall> Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                                 \<Gamma>\<turnstile>c2\<down>Normal s}
                              c2 
                            {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                            {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    using Seq.hyps by iprover
  from hyp_c1 
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                \<Gamma>\<turnstile>Seq c1 c2\<down>Normal s} c1 
    {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t \<and> \<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
        \<Gamma>\<turnstile>c2\<down>Normal t},
    {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule ConseqMGT)
       (auto dest: Seq_NoFaultStuckD1 [simplified] Seq_NoFaultStuckD2 [simplified]
             elim: terminates_Normal_elim_cases 
             intro: exec.intros)
  thus "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
                 \<Gamma>\<turnstile>Seq c1 c2\<down>Normal s} 
                Seq c1 c2
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule hoaret.Seq )
    show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t \<and>
                    \<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> \<Gamma>\<turnstile>c2 \<down> Normal t}
                 c2 
                {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    proof (rule ConseqMGT [OF hyp_c2],safe)
      fix r t
      assume "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal r" "\<Gamma>\<turnstile>\<langle>c2,Normal r\<rangle> \<Rightarrow> Normal t"
      then show "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t"
        by (rule exec.intros)
    next
      fix r t
      assume "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal r" "\<Gamma>\<turnstile>\<langle>c2,Normal r\<rangle> \<Rightarrow> Abrupt t"
      then show "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t"
        by (rule exec.intros)
    qed
  qed
next
  case (Cond b c1 c2) 
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                         \<Gamma>\<turnstile>c1\<down>Normal s} 
                     c1 
                   {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
                   {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    using Cond.hyps by iprover  
  hence "\<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                     \<Gamma>\<turnstile>(Cond b c1 c2)\<down>Normal s}\<inter>b) 
                c1 
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"  
    by (rule ConseqMGT)
       (fastforce simp add: final_notin_def intro: exec.CondTrue 
                 elim: terminates_Normal_elim_cases)
  moreover
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                               \<Gamma>\<turnstile>c2\<down>Normal s} 
                      c2 
                    {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                    {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"  
    using Cond.hyps by iprover  
  hence "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>(Cond b c1 c2)\<down>Normal s}\<inter>-b) 
                c2 
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}" 
    by (rule ConseqMGT)
       (fastforce simp add: final_notin_def intro: exec.CondFalse 
                 elim: terminates_Normal_elim_cases)
  ultimately
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
               \<Gamma>\<turnstile>(Cond b c1 c2)\<down>Normal s} 
               (Cond b c1 c2)
              {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Cond)       
next
  case (While b c)
  let ?unroll = "({(s,t). s\<in>b \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t})\<^sup>*"
  let ?P' = "\<lambda>Z. {t. (Z,t)\<in>?unroll \<and> 
                    (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                         \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                             (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and>
                    \<Gamma>\<turnstile>(While b c)\<down>Normal t}"
  let ?A = "\<lambda>Z. {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  let ?r = "{(t,s). \<Gamma>\<turnstile>(While b c)\<down>Normal s \<and> s\<in>b \<and> 
                    \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t}"
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>  
                  \<Gamma>\<turnstile>(While b c)\<down>Normal s} 
              (While b c)
              {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [where ?P'="\<lambda> Z. ?P' Z" 
                         and ?Q'="\<lambda> Z. ?P' Z \<inter> - b"])
    have wf_r: "wf ?r" by (rule wf_terminates_while)
    show "\<forall> Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (?P' Z) (While b c) (?P' Z \<inter> - b),(?A Z)"
    proof (rule allI, rule hoaret.While [OF wf_r])
      fix Z
      from While 
      have hyp_c: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
                                  \<Gamma>\<turnstile>c\<down>Normal s}
                                c
                              {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
                              {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}" by iprover
      show "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> ?P' Z  \<inter> b) c 
                       ({t. (t, \<sigma>) \<in> ?r} \<inter> ?P' Z),(?A Z)"
      proof (rule allI, rule ConseqMGT [OF hyp_c])
        fix \<sigma> s
        assume  "s\<in> {\<sigma>} \<inter>  
                   {t. (Z, t) \<in> ?unroll \<and> 
                      (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                           \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                               (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                    \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and>
                      \<Gamma>\<turnstile>(While b c)\<down>Normal t}
                   \<inter> b"
        then obtain 
          s_eq_\<sigma>: "s=\<sigma>" and
          Z_s_unroll: "(Z,s) \<in> ?unroll" and
          noabort:"\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)" and
          while_term:  "\<Gamma>\<turnstile>(While b c)\<down>Normal s" and
          s_in_b: "s\<in>b" 
          by blast
        show "s \<in> {t. t = s \<and> \<Gamma>\<turnstile>\<langle>c,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                       \<Gamma>\<turnstile>c\<down>Normal t} \<and>
        (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t} \<longrightarrow>
             t \<in> {t. (t,\<sigma>) \<in> ?r} \<inter>  
                 {t. (Z, t) \<in> ?unroll \<and> 
                     (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow>  e\<in>b 
                           \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                              (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and> 
                      \<Gamma>\<turnstile>(While b c)\<down>Normal t})  \<and> 
         (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t} \<longrightarrow>
             t \<in> {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t})"
          (is "?C1 \<and> ?C2 \<and> ?C3")
        proof (intro conjI)
          from Z_s_unroll noabort s_in_b while_term show ?C1 
            by (blast elim: terminates_Normal_elim_cases)
        next
          {
            fix t 
            assume s_t: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t"
            with s_eq_\<sigma> while_term s_in_b have "(t,\<sigma>) \<in> ?r"
              by blast
            moreover
            from Z_s_unroll s_t s_in_b 
            have "(Z, t) \<in> ?unroll"
              by (blast intro: rtrancl_into_rtrancl)
            moreover from while_term s_t s_in_b 
            have "\<Gamma>\<turnstile>(While b c)\<down>Normal t"
              by (blast elim: terminates_Normal_elim_cases)
            moreover note noabort
            ultimately 
            have "(t,\<sigma>) \<in> ?r \<and> (Z, t) \<in> ?unroll \<and> 
                  (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and>
                  \<Gamma>\<turnstile>(While b c)\<down>Normal t"
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
    assume P: "s \<in> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                       \<Gamma>\<turnstile>While b c \<down> Normal s}"
    hence WhileNoFault: "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by auto
    show "s \<in> ?P' s \<and> 
     (\<forall>t. t\<in>(?P' s \<inter> - b)\<longrightarrow>
          t\<in>{t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t})\<and>
     (\<forall>t. t\<in>?A s \<longrightarrow> t\<in>?A Z)"
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
      from P show "\<forall>t. t\<in>?A s \<longrightarrow> t\<in>?A Z"
        by simp
    qed
  qed
next
  case (Call p)
  from noStuck_Call
  have "\<forall>s \<in> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
                         \<Gamma>\<turnstile>Call p\<down> Normal s}.
          p \<in> dom \<Gamma>"
    by (fastforce simp add: final_notin_def)
  then show ?case
  proof (rule conseq_extract_state_indep_prop)
    assume p_defined: "p \<in> dom \<Gamma>"
    with MGT_Calls show
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>{s. s=Z \<and> 
                 \<Gamma>\<turnstile>\<langle>Call p ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))\<and>
                 \<Gamma>\<turnstile>Call  p\<down>Normal s}
                (Call p)
               {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      by (auto)
  qed
next
  case (DynCom c)
  have hyp: 
    "\<And>s'. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c s',Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                       \<Gamma>\<turnstile>c s'\<down>Normal s} c s'
      {t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using DynCom by simp
  have hyp':
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>{s. s = Z \<and> \<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
            \<Gamma>\<turnstile>DynCom c\<down>Normal s} 
         (c Z)
        {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule ConseqMGT [OF hyp]) 
       (fastforce simp add: final_notin_def intro: exec.intros 
          elim: terminates_Normal_elim_cases)
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>DynCom c\<down>Normal s}
                DynCom c
             {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Normal t},
             {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    apply (rule hoaret.DynCom)
    apply (clarsimp)
    apply (rule hyp' [simplified])
    done
next
  case (Guard f g c)
  have hyp_c: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                              \<Gamma>\<turnstile>c\<down>Normal s} 
                     c 
                   {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
                   {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Guard by iprover
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Guard f g c\<down> Normal s} 
                Guard f g c 
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (cases "f \<in> F")
    case True
    from hyp_c
    have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>(g \<inter> {s. s=Z \<and> 
                     \<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck}\<union> Fault ` (-F))\<and>
                     \<Gamma>\<turnstile>Guard f g c\<down> Normal s})
                   c
                 {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Normal t},
                 {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      apply (rule ConseqMGT)
      apply (insert True)
      apply  (auto simp add: final_notin_def intro: exec.intros 
                   elim: terminates_Normal_elim_cases)
      done
    from True this
    show ?thesis
      by (rule conseqPre [OF Guarantee]) auto
  next
    case False
    from hyp_c
    have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>(g \<inter> {s. s \<in> g \<and> s=Z \<and> 
                     \<Gamma>\<turnstile>\<langle>Guard f g c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck}\<union> Fault ` (-F))\<and>
                     \<Gamma>\<turnstile>Guard f g c\<down> Normal s} )
                   c
                 {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Normal t},
                 {t. \<Gamma>\<turnstile>\<langle>Guard f g c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      apply (rule ConseqMGT)
      apply clarify
      apply (frule Guard_noFaultStuckD [OF _ False])
      apply  (auto simp add: final_notin_def intro: exec.intros 
                   elim: terminates_Normal_elim_cases)
      done
    then show ?thesis
      apply (rule conseqPre [OF hoaret.Guard])
      apply clarify
      apply (frule Guard_noFaultStuckD [OF _ False])
      apply auto
      done
  qed
next
  case Throw
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Throw,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Throw \<down> Normal s}
              Throw
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule conseqPre [OF hoaret.Throw]) 
       (blast intro: exec.intros terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                        \<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s} 
                    c\<^sub>1
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  hence "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>Catch c\<^sub>1 c\<^sub>2 \<down> Normal s} 
                c\<^sub>1
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t \<and> \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal t \<and>
                   \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))}"
    by (rule ConseqMGT)
       (fastforce intro: exec.intros terminates.intros 
                 elim: terminates_Normal_elim_cases
                 simp add: final_notin_def)
  moreover
  have 
    "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                     \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s} c\<^sub>2
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  hence "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow>Abrupt s \<and> \<Gamma>\<turnstile>c\<^sub>2 \<down> Normal s \<and> 
                   \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))} 
               c\<^sub>2
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      by (rule ConseqMGT)
         (fastforce intro: exec.intros terminates.intros 
                   simp add: noFault_def')
  ultimately
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>Catch c\<^sub>1 c\<^sub>2 \<down> Normal s} 
                Catch c\<^sub>1 c\<^sub>2
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Catch )
qed


lemma Call_lemma':
 assumes Call_hyp: 
 "\<forall>q\<in>dom \<Gamma>. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
                       \<Gamma>\<turnstile>Call q\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                 (Call q)
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
 shows "\<And>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub>  
      {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and> 
                (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c \<in> redexes c')} 
              c 
      {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
      {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof (induct c)
  case Skip
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
                (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> Skip \<in> redexes c')}
               Skip
              {t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Skip [THEN conseqPre]) (blast intro: exec.Skip)
next
  case (Basic f)
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Basic f,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> 
                      Basic f \<in> redexes c')}
               Basic f 
              {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Basic [THEN conseqPre]) (blast intro: exec.Basic)
next
  case (Spec r)
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Spec r,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> 
                 Spec r \<in> redexes c')}
               Spec r 
              {t. \<Gamma>\<turnstile>\<langle>Spec r,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Spec r,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    apply (rule hoaret.Spec [THEN conseqPre]) 
    apply (clarsimp)
    apply (case_tac "\<exists>t. (Z,t) \<in> r")
    apply (auto elim: exec_elim_cases simp add: final_notin_def intro: exec.intros)
    done
next
  case (Seq c1 c2)
  have hyp_c1: 
    "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                     \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                 (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c1 \<in> redexes c')}
                c1 
               {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Seq.hyps by iprover
  have hyp_c2: 
    "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                 (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c2 \<in> redexes c')}
                c2 
               {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Seq.hyps (2) by iprover
  have c1: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
              (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> 
                    Seq c1 c2 \<in> redexes c')}
               c1
               {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t \<and> 
                   \<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                  (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal t) \<and> 
                        c2 \<in> redexes c')},
               {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp_c1],clarify,safe)
    assume "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
      by (blast dest: Seq_NoFaultStuckD1)
  next
    fix c'
    assume steps_c': "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)"
    assume red: "Seq c1 c2 \<in> redexes c'"
    from redexes_subset [OF red] steps_c'
    show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z) \<and> c1 \<in> redexes c'"
      by (auto iff: root_in_redexes)
  next
    fix t
    assume "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
            "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t"
    thus "\<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (blast dest: Seq_NoFaultStuckD2)
  next
    fix c' t
    assume steps_c': "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)" 
    assume red: "Seq c1 c2 \<in> redexes c'"
    assume exec_c1: "\<Gamma>\<turnstile> \<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t"
    show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal t) \<and> c2 \<in> redexes c'"
    proof -
      note steps_c'
      also
      from exec_impl_steps_Normal [OF exec_c1]
      have "\<Gamma>\<turnstile> (c1, Normal Z) \<rightarrow>\<^sup>* (Skip, Normal t)".
      from steps_redexes_Seq [OF this red] 
      obtain c'' where
        steps_c'': "\<Gamma>\<turnstile> (c', Normal Z) \<rightarrow>\<^sup>* (c'', Normal t)" and
        Skip: "Seq Skip c2 \<in> redexes c''"
        by blast
      note steps_c''
      also 
      have step_Skip: "\<Gamma>\<turnstile> (Seq Skip c2,Normal t) \<rightarrow> (c2,Normal t)"
        by (rule step.SeqSkip)
      from step_redexes [OF step_Skip Skip]
      obtain c''' where
        step_c''': "\<Gamma>\<turnstile> (c'', Normal t) \<rightarrow> (c''', Normal t)" and
        c2: "c2 \<in> redexes c'''"
        by blast
      note step_c'''
      finally show ?thesis
        using c2
        by blast
    qed
  next
    fix t 
    assume "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    thus "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t"
      by (blast intro: exec.intros)
  qed
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>     
                  \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
              (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> Seq c1 c2 \<in> redexes c')}
              Seq c1 c2 
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Seq [OF c1 ConseqMGT [OF hyp_c2]])
       (blast intro: exec.intros)
next
  case (Cond b c1 c2) 
  have hyp_c1:
       "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                        \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                    (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c1 \<in> redexes c')}
                   c1 
                  {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Cond.hyps by iprover
  have 
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
           \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
           (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> 
                 Cond b c1 c2 \<in> redexes c')}
           \<inter> b)
           c1 
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp_c1],safe)
    assume "Z \<in> b" "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (auto simp add: final_notin_def intro: exec.CondTrue)
  next  
    fix c'
    assume b: "Z \<in> b" 
    assume steps_c': "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)"
    assume redex_c': "Cond b c1 c2 \<in> redexes c'"
    show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z) \<and> c1 \<in> redexes c'"
    proof -
      note steps_c'
      also
      from b
      have "\<Gamma>\<turnstile>(Cond b c1 c2, Normal Z) \<rightarrow> (c1, Normal Z)"
        by (rule step.CondTrue)
      from step_redexes [OF this redex_c'] obtain c'' where
        step_c'': "\<Gamma>\<turnstile> (c', Normal Z) \<rightarrow> (c'', Normal Z)" and 
        c1: "c1 \<in> redexes c''"
        by blast
      note step_c''
      finally show ?thesis
        using c1
        by blast
    qed
  next
    fix t assume "Z \<in> b" "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t"
    thus "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t"
      by (blast intro: exec.CondTrue)
  next
    fix t assume "Z \<in> b" "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    thus "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t"
      by (blast intro: exec.CondTrue)
  qed
  moreover
  have hyp_c2:
       "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                     \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                    (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c2 \<in> redexes c')}
                   c2 
                  {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Cond.hyps by iprover
  have 
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
              \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
           (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal s) \<and> 
                 Cond b c1 c2 \<in> redexes c')}
           \<inter> -b)
           c2 
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp_c2],safe)
    assume "Z \<notin> b" "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (auto simp add: final_notin_def intro: exec.CondFalse)
  next
    fix c'
    assume b: "Z \<notin> b" 
    assume steps_c': "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)"
    assume redex_c': "Cond b c1 c2 \<in> redexes c'"
    show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z) \<and> c2 \<in> redexes c'"
    proof -
      note steps_c'
      also
      from b
      have "\<Gamma>\<turnstile>(Cond b c1 c2, Normal Z) \<rightarrow> (c2, Normal Z)"
        by (rule step.CondFalse)
      from step_redexes [OF this redex_c'] obtain c'' where
        step_c'': "\<Gamma>\<turnstile> (c', Normal Z) \<rightarrow> (c'', Normal Z)" and 
        c1: "c2 \<in> redexes c''"
        by blast
      note step_c''
      finally show ?thesis
        using c1
        by blast
    qed
  next
    fix t assume "Z \<notin> b" "\<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t"
    thus "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t"
      by (blast intro: exec.CondFalse)
  next
    fix t assume "Z \<notin> b" "\<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    thus "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t"
      by (blast intro: exec.CondFalse)
  qed
  ultimately
  show 
   "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
              \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
           (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> 
                 Cond b c1 c2 \<in> redexes c')}
           (Cond b c1 c2) 
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Cond)       
next
  case (While b c) 
  let ?unroll = "({(s,t). s\<in>b \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t})\<^sup>*"
  let ?P' = "\<lambda>Z. {t. (Z,t)\<in>?unroll \<and> 
                    (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                         \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                             (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and>
                    \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and> 
                  (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ 
                               (c',Normal t) \<and> While b c \<in> redexes c')}"
  let ?A = "\<lambda>Z. {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  let ?r = "{(t,s). \<Gamma>\<turnstile>(While b c)\<down>Normal s \<and> s\<in>b \<and>  
                    \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t}"
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
       {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
          (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>)\<rightarrow>\<^sup>+(c',Normal s) \<and> While b c \<in> redexes c')}
         (While b c) 
       {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t},
       {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [where ?P'="\<lambda> Z. ?P' Z" 
                         and ?Q'="\<lambda> Z. ?P' Z \<inter> - b"])
    have wf_r: "wf ?r" by (rule wf_terminates_while)
    show "\<forall> Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (?P' Z) (While b c) (?P' Z \<inter> - b),(?A Z)"
    proof (rule allI, rule hoaret.While [OF wf_r])
      fix Z
      from While 
      have hyp_c: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>
            {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and> 
               (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c \<in> redexes c')}
              c 
            {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
            {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}" by iprover
      show "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> ?P' Z  \<inter> b) c 
                       ({t. (t, \<sigma>) \<in> ?r} \<inter> ?P' Z),(?A Z)"
      proof (rule allI, rule ConseqMGT [OF hyp_c])
        fix \<tau> s
        assume  asm: "s\<in> {\<tau>} \<inter> 
                   {t. (Z, t) \<in> ?unroll \<and> 
                      (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                           \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                               (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                    \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and>
                     \<Gamma>\<turnstile>Call p\<down> Normal \<sigma> \<and>
                     (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ 
                                  (c',Normal t) \<and> While b c \<in> redexes c')}
                   \<inter> b"
        then obtain c' where  
          s_eq_\<tau>: "s=\<tau>" and
          Z_s_unroll: "(Z,s) \<in> ?unroll" and
          noabort:"\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)" and
          termi:  "\<Gamma>\<turnstile>Call p \<down> Normal \<sigma>" and
          reach: "\<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s)" and
          red_c': "While b c \<in> redexes c'" and
          s_in_b: "s\<in>b" 
          by blast
        obtain c'' where
          reach_c: "\<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c'',Normal s)" 
                   "Seq c (While b c) \<in> redexes c''"
        proof -
          note reach
          also from s_in_b  
          have "\<Gamma>\<turnstile>(While b c,Normal s) \<rightarrow> (Seq c (While b c),Normal s)"
            by (rule step.WhileTrue)
          from step_redexes [OF this red_c'] obtain c'' where
            step: "\<Gamma>\<turnstile> (c', Normal s) \<rightarrow> (c'', Normal s)" and
            red_c'': "Seq c (While b c) \<in> redexes c''"
            by blast
          note step
          finally
          show ?thesis 
            using red_c''
            by (blast intro: that)
        qed
        from reach termi 
        have "\<Gamma>\<turnstile>c' \<down> Normal s"
          by (rule steps_preserves_termination')
        from redexes_preserves_termination [OF this red_c']
        have termi_while: "\<Gamma>\<turnstile>While b c \<down> Normal s" .
        show "s \<in> {t. t = s \<and> \<Gamma>\<turnstile>\<langle>c,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                      \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
                   (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal t) \<and> c \<in> redexes c')} \<and>
        (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t} \<longrightarrow>
             t \<in> {t. (t,\<tau>) \<in> ?r} \<inter>  
                 {t. (Z, t) \<in> ?unroll \<and> 
                     (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow>  e\<in>b 
                           \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                              (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and> 
                      \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
                    (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal t) \<and> 
                          While b c \<in> redexes c')}) \<and> 
         (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t} \<longrightarrow>
             t \<in> {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t})"
          (is "?C1 \<and> ?C2 \<and> ?C3")
        proof (intro conjI)
          from Z_s_unroll noabort s_in_b termi reach_c show ?C1 
            apply clarsimp          
            apply (drule redexes_subset)
            apply simp
            apply (blast intro: root_in_redexes)
            done
        next
          {
            fix t 
            assume s_t: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t"
            with s_eq_\<tau> termi_while s_in_b have "(t,\<tau>) \<in> ?r"
              by blast
            moreover
            from Z_s_unroll s_t s_in_b 
            have "(Z, t) \<in> ?unroll"
              by (blast intro: rtrancl_into_rtrancl)
            moreover 
            obtain c'' where
              reach_c'': "\<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c'',Normal t)" 
                        "(While b c) \<in> redexes c''"
            proof -
              note reach_c (1)
              also from s_in_b  
              have "\<Gamma>\<turnstile>(While b c,Normal s)\<rightarrow> (Seq c (While b c),Normal s)"
                by (rule step.WhileTrue)
              have "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow>\<^sup>+
                        (While b c, Normal t)"
              proof -
                from exec_impl_steps_Normal [OF s_t]
                have "\<Gamma>\<turnstile> (c, Normal s) \<rightarrow>\<^sup>* (Skip, Normal t)".
                hence "\<Gamma>\<turnstile> (Seq c (While b c), Normal s) \<rightarrow>\<^sup>* 
                          (Seq Skip (While b c), Normal t)"
                  by (rule SeqSteps) auto
                moreover
                have "\<Gamma>\<turnstile>(Seq Skip (While b c), Normal t)\<rightarrow>(While b c, Normal t)"
                  by (rule step.SeqSkip)
                ultimately show ?thesis by (rule rtranclp_into_tranclp1)
              qed
              from steps_redexes' [OF this reach_c (2)]  
              obtain c''' where
                step: "\<Gamma>\<turnstile> (c'', Normal s) \<rightarrow>\<^sup>+ (c''', Normal t)" and
                red_c'': "While b c \<in> redexes c'''"
                by blast
              note step
              finally
              show ?thesis 
                using red_c''
                by (blast intro: that)
            qed
            moreover note noabort termi
            ultimately 
            have "(t,\<tau>) \<in> ?r \<and> (Z, t) \<in> ?unroll \<and> 
                  (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and>
                  \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
                    (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal t) \<and> 
                             While b c \<in> redexes c')"
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
    assume P: "s \<in> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                       \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                   (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> 
                         While b c \<in> redexes c')}"
    hence WhileNoFault: "\<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by auto
    show "s \<in> ?P' s \<and> 
     (\<forall>t. t\<in>(?P' s \<inter> - b)\<longrightarrow>
          t\<in>{t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t})\<and>
     (\<forall>t. t\<in>?A s \<longrightarrow> t\<in>?A Z)"
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
      show "\<forall>t. t\<in>(?P' s \<inter> - b)
            \<longrightarrow>t\<in>{t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Normal t}"
        by blast
    next
      from P show "\<forall>t. t\<in>?A s \<longrightarrow> t\<in>?A Z"
        by simp
    qed
  qed
next
  case (Call q)
  let ?P = "{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
               \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
              (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> Call q \<in> redexes c')}"
  from noStuck_Call
  have "\<forall>s \<in> ?P. q \<in> dom \<Gamma>"
    by (fastforce simp add: final_notin_def)
  then show ?case
  proof (rule conseq_extract_state_indep_prop)
    assume q_defined: "q \<in> dom \<Gamma>"
    from Call_hyp have
      "\<forall>q\<in>dom \<Gamma>. \<forall>Z. 
        \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
                        \<Gamma>\<turnstile>Call q\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                 (Call q)
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      by (simp add: exec_Call_body' noFaultStuck_Call_body' [simplified]
         terminates_Normal_Call_body)
    from Call_hyp q_defined have Call_hyp':
    "\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                     \<Gamma>\<turnstile>Call q\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                  (Call q)
                 {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Normal t},
                 {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      by auto
    show
     "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ?P
           (Call q) 
          {t. \<Gamma>\<turnstile>\<langle>Call q ,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Call q ,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    proof (rule ConseqMGT [OF Call_hyp'],safe)
      fix c'
      assume termi: "\<Gamma>\<turnstile>Call p \<down> Normal \<sigma>"
      assume steps_c': "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)" 
      assume red_c': "Call q \<in> redexes c'"
      show "\<Gamma>\<turnstile>Call q \<down> Normal Z"
      proof -
        from steps_preserves_termination' [OF steps_c' termi]
        have "\<Gamma>\<turnstile>c' \<down> Normal Z" .
        from redexes_preserves_termination [OF this red_c']
        show ?thesis .
      qed
    next
      fix c'
      assume termi: "\<Gamma>\<turnstile>Call p \<down> Normal \<sigma>"
      assume steps_c': "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)" 
      assume red_c': "Call q \<in> redexes c'"
      from redex_redexes [OF this]
      have "redex c' = Call q"
        by auto
      with termi steps_c' 
      show "((Z, q), \<sigma>, p) \<in> termi_call_steps \<Gamma>"
        by (auto simp add: termi_call_steps_def)
    qed
  qed
next
  case (DynCom c)
  have hyp: 
    "\<And>s'. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>
      {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c s',Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
            \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
          (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c s' \<in> redexes c')}
        (c s') 
       {t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using DynCom by simp
  have hyp':
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
               (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> DynCom c \<in> redexes c')}
        (c Z) 
       {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp],safe)
    assume "\<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    then show "\<Gamma>\<turnstile>\<langle>c Z,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (fastforce simp add: final_notin_def intro: exec.intros)
  next
    fix c'
    assume steps: "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)" 
    assume c': "DynCom c \<in> redexes c'"
    have "\<Gamma>\<turnstile> (DynCom c, Normal Z) \<rightarrow> (c Z,Normal Z)"
      by (rule step.DynCom)
    from step_redexes [OF this c'] obtain c'' where
      step: "\<Gamma>\<turnstile> (c', Normal Z) \<rightarrow> (c'', Normal Z)"  and c'': "c Z \<in> redexes c''"
      by blast
    note steps also note step 
    finally show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z) \<and> c Z \<in> redexes c'"
      using c'' by blast
  next
    fix t
    assume "\<Gamma>\<turnstile>\<langle>c Z,Normal Z\<rangle> \<Rightarrow> Normal t"
    thus "\<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Normal t"
      by (auto intro: exec.intros)
  next
    fix t
    assume "\<Gamma>\<turnstile>\<langle>c Z,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    thus "\<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Abrupt t"
      by (auto intro: exec.intros)
  qed
  show ?case
    apply (rule hoaret.DynCom)
    apply safe
    apply (rule hyp')
    done
next
  case (Guard f g c)
  have hyp_c: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
              \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and> 
            (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c \<in> redexes c')}
          c 
         {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
         {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Guard.hyps by iprover
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                  \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
            (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> Guard f g c \<in> redexes c')}
              Guard f g c  
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (cases "f \<in> F")
    case True
    have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> {s. s=Z \<and> 
                     \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
            (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and>
                  Guard f g c \<in> redexes c')})
              c  
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    proof (rule ConseqMGT [OF hyp_c], safe)
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" "Z\<in>g"
      thus "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
        by (auto simp add: final_notin_def intro: exec.intros)
    next
      fix c'
      assume steps: "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)"
      assume c': "Guard f g c \<in> redexes c'"
      assume "Z \<in> g"
      from this have "\<Gamma>\<turnstile>(Guard f g c,Normal Z) \<rightarrow> (c,Normal Z)"
        by (rule step.Guard)
      from step_redexes [OF this c'] obtain c'' where
        step: "\<Gamma>\<turnstile> (c', Normal Z) \<rightarrow> (c'', Normal Z)"  and c'': "c \<in> redexes c''"
        by blast
      note steps also note step 
      finally show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z) \<and> c \<in> redexes c'"
        using c'' by blast
    next
      fix t
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
             "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t" "Z \<in> g"
      thus "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t"
        by (auto simp add: final_notin_def intro: exec.intros )
    next
      fix t
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
              "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t" "Z \<in> g"
      thus "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t"
        by (auto simp add: final_notin_def intro: exec.intros )
    qed 
    from True this show ?thesis
      by (rule conseqPre [OF Guarantee]) auto 
  next
    case False
    have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> {s. s=Z \<and> 
                     \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
            (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and>
                  Guard f g c \<in> redexes c')})
              c  
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    proof (rule ConseqMGT [OF hyp_c], safe)
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
      thus "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
        using False
        by (cases "Z\<in> g") (auto simp add: final_notin_def intro: exec.intros)
    next
      fix c'
      assume steps: "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)"
      assume c': "Guard f g c \<in> redexes c'"

      assume "Z \<in> g"
      from this have "\<Gamma>\<turnstile>(Guard f g c,Normal Z) \<rightarrow> (c,Normal Z)"
        by (rule step.Guard)
      from step_redexes [OF this c'] obtain c'' where
        step: "\<Gamma>\<turnstile> (c', Normal Z) \<rightarrow> (c'', Normal Z)"  and c'': "c \<in> redexes c''"
        by blast
      note steps also note step 
      finally show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z) \<and> c \<in> redexes c'"
        using c'' by blast
    next
      fix t
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
        "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t"
      thus "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t"
        using False
        by (cases "Z\<in> g") (auto simp add: final_notin_def intro: exec.intros )
    next
      fix t
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
             "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t"
      thus "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t"
        using False
        by (cases "Z\<in> g") (auto simp add: final_notin_def intro: exec.intros )
    qed
    then show ?thesis
      apply (rule conseqPre [OF hoaret.Guard])
      apply clarify
      apply (frule Guard_noFaultStuckD [OF _ False])
      apply auto
      done
  qed
next
  case Throw
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Throw,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                  \<Gamma>\<turnstile>Call p\<down>Normal \<sigma> \<and>
                (\<exists>c'. \<Gamma>\<turnstile>(Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> Throw \<in> redexes c')}
              Throw
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule conseqPre [OF hoaret.Throw]) 
       (blast intro: exec.intros terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have hyp_c1:
   "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s= Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
                (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> 
                      c\<^sub>1 \<in> redexes c')}
               c\<^sub>1 
              {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  have hyp_c2:
   "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s= Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                     \<Gamma>\<turnstile>Call p\<down> Normal \<sigma> \<and>
                (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal s) \<and> c\<^sub>2 \<in> redexes c')}
               c\<^sub>2
              {t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  have
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
               \<Gamma>\<turnstile>Call p\<down> Normal \<sigma> \<and>
            (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>)\<rightarrow>\<^sup>+(c',Normal s) \<and>
                   Catch c\<^sub>1 c\<^sub>2 \<in> redexes c')}
            c\<^sub>1
           {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
           {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t \<and> 
               \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault`(-F)) \<and> \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
               (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal t) \<and> c\<^sub>2 \<in> redexes c')}"
  proof (rule ConseqMGT [OF hyp_c1],clarify,safe) 
    assume "\<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (fastforce simp add: final_notin_def intro: exec.intros)
  next
    fix c'
    assume steps: "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)" 
    assume c': "Catch c\<^sub>1 c\<^sub>2 \<in> redexes c'"
    from steps redexes_subset [OF this]
    show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z) \<and> c\<^sub>1 \<in> redexes c'"
      by (auto iff:  root_in_redexes)
  next
    fix t
    assume "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Normal t"
    thus "\<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t"
      by (auto intro: exec.intros)
  next
    fix t
    assume "\<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
      "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    thus "\<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (auto simp add: final_notin_def intro: exec.intros)
  next
    fix c' t
    assume steps_c': "\<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal Z)" 
    assume red: "Catch c\<^sub>1 c\<^sub>2 \<in> redexes c'"
    assume exec_c\<^sub>1: "\<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    show "\<exists>c'. \<Gamma>\<turnstile> (Call p, Normal \<sigma>) \<rightarrow>\<^sup>+ (c', Normal t) \<and> c\<^sub>2 \<in> redexes c'"
    proof -
      note steps_c'
      also
      from exec_impl_steps_Normal_Abrupt [OF exec_c\<^sub>1]
      have "\<Gamma>\<turnstile> (c\<^sub>1, Normal Z) \<rightarrow>\<^sup>* (Throw, Normal t)".
      from steps_redexes_Catch [OF this red] 
      obtain c'' where
        steps_c'': "\<Gamma>\<turnstile> (c', Normal Z) \<rightarrow>\<^sup>* (c'', Normal t)" and
        Catch: "Catch Throw c\<^sub>2 \<in> redexes c''"
        by blast
      note steps_c''
      also 
      have step_Catch: "\<Gamma>\<turnstile> (Catch Throw c\<^sub>2,Normal t) \<rightarrow> (c\<^sub>2,Normal t)"
        by (rule step.CatchThrow)
      from step_redexes [OF step_Catch Catch]
      obtain c''' where
        step_c''': "\<Gamma>\<turnstile> (c'', Normal t) \<rightarrow> (c''', Normal t)" and
        c2: "c\<^sub>2 \<in> redexes c'''"
        by blast
      note step_c'''
      finally show ?thesis
        using c2
        by blast
    qed
  qed
  moreover
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t \<and> 
                  \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                  \<Gamma>\<turnstile>Call p \<down> Normal \<sigma> \<and>
                  (\<exists>c'. \<Gamma>\<turnstile>(Call p,Normal \<sigma>) \<rightarrow>\<^sup>+ (c',Normal t) \<and> c\<^sub>2 \<in> redexes c')} 
               c\<^sub>2
              {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule ConseqMGT [OF hyp_c2]) (fastforce intro: exec.intros)
  ultimately show ?case
    by (rule hoaret.Catch)
qed


text {* To prove a procedure implementation correct it suffices to assume
       only the procedure specifications of procedures that actually
       occur during evaluation of the body.  
    *}

lemma Call_lemma:
 assumes A: 
 "\<forall>q \<in> dom \<Gamma>. \<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
                 {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Call q\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                 (Call q)
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
 assumes pdef: "p \<in> dom \<Gamma>"
 shows "\<And>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub>  
              ({\<sigma>} \<inter> {s. s=Z \<and>\<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>  
                                 \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal s}) 
                 the (\<Gamma> p) 
              {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Abrupt t}"
apply (rule conseqPre)
apply (rule Call_lemma' [OF A])
using pdef
apply (fastforce intro: terminates.intros tranclp.r_into_trancl [of "(step \<Gamma>)", OF step.Call] root_in_redexes)
done

lemma Call_lemma_switch_Call_body:
 assumes 
 call: "\<forall>q \<in> dom \<Gamma>. \<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
                 {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Call q\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                 (Call q)
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
 assumes p_defined: "p \<in> dom \<Gamma>"
 shows "\<And>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub>  
              ({\<sigma>} \<inter> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>  
                                 \<Gamma>\<turnstile>Call p\<down>Normal s}) 
                 the (\<Gamma> p) 
              {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
apply (simp only: exec_Call_body' [OF p_defined] noFaultStuck_Call_body' [OF p_defined] terminates_Normal_Call_body [OF p_defined])
apply (rule conseqPre)
apply (rule Call_lemma')
apply (rule call)
using p_defined
apply (fastforce intro: terminates.intros tranclp.r_into_trancl [of "(step \<Gamma>)", OF step.Call] 
root_in_redexes)
done

lemma MGT_Call:
"\<forall>p \<in> dom \<Gamma>. \<forall>Z. 
  \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
             \<Gamma>\<turnstile>(Call p)\<down>Normal s}
           (Call p)
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
apply (intro ballI allI)
apply (rule CallRec' [where Procs="dom \<Gamma>" and
    P="\<lambda>p Z. {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Call p\<down>Normal s}" and
    Q="\<lambda>p Z. {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t}" and
    A="\<lambda>p Z. {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}" and
    r="termi_call_steps \<Gamma>"
    ]) 
apply    simp
apply   simp
apply  (rule wf_termi_call_steps)
apply (intro ballI allI)
apply simp
apply (rule Call_lemma_switch_Call_body [rule_format, simplified])
apply  (rule hoaret.Asm)
apply  fastforce
apply assumption
done


lemma CollInt_iff: "{s. P s} \<inter> {s. Q s} = {s. P s \<and> Q s}"
  by auto

lemma image_Un_conv: "f ` (\<Union>p\<in>dom \<Gamma>. \<Union>Z. {x p Z}) =  (\<Union>p\<in>dom \<Gamma>. \<Union>Z. {f (x p Z)})"
  by (auto iff: not_None_eq)


text {* Another proof of @{text MGT_Call}, maybe a little more readable *}
lemma 
"\<forall>p \<in> dom \<Gamma>. \<forall>Z. 
  \<Gamma>,{} \<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
             \<Gamma>\<turnstile>(Call p)\<down>Normal s}
           (Call p)
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof -
  {
    fix p Z \<sigma>
    assume defined: "p \<in> dom \<Gamma>"
    def Specs == "(\<Union>p\<in>dom \<Gamma>. \<Union>Z. 
            {({s. s=Z \<and> 
              \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
              \<Gamma>\<turnstile>Call p\<down>Normal s},
             p,
             {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
             {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t})})"
    def Specs_wf == "(\<lambda>p \<sigma>. (\<lambda>(P,q,Q,A). 
                       (P \<inter> {s. ((s,q),\<sigma>,p) \<in> termi_call_steps \<Gamma>}, q, Q, A)) ` Specs)"
    have "\<Gamma>,Specs_wf p \<sigma>
            \<turnstile>\<^sub>t\<^bsub>/F\<^esub>({\<sigma>} \<inter>
                 {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                  \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal s}) 
                (the (\<Gamma> p))
               {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      apply (rule Call_lemma [rule_format, OF _ defined])
      apply (rule hoaret.Asm)
      apply (clarsimp simp add: Specs_wf_def Specs_def image_Un_conv)
      apply (rule_tac x=q in bexI)
      apply (rule_tac x=Z in exI)
      apply (clarsimp simp add: CollInt_iff)
      apply auto
      done
    hence "\<Gamma>,Specs_wf p \<sigma>
            \<turnstile>\<^sub>t\<^bsub>/F\<^esub>({\<sigma>} \<inter>
                 {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                  \<Gamma>\<turnstile>Call p\<down>Normal s}) 
                (the (\<Gamma> p))
               {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
      by (simp only: exec_Call_body' [OF defined] 
                   noFaultStuck_Call_body' [OF defined] 
                  terminates_Normal_Call_body [OF defined])
  } note bdy=this
  show ?thesis
    apply (intro ballI allI)
    apply (rule hoaret.CallRec [where Specs="(\<Union>p\<in>dom \<Gamma>. \<Union>Z. 
            {({s. s=Z \<and> 
              \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
              \<Gamma>\<turnstile>Call p\<down>Normal s},
             p,
             {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Normal t},
             {t. \<Gamma>\<turnstile>\<langle>Call p,Normal Z\<rangle> \<Rightarrow> Abrupt t})})", 
             OF _ wf_termi_call_steps [of \<Gamma>] refl])
    apply fastforce
    apply clarify
    apply (rule conjI)
    apply  fastforce
    apply (rule allI)
    apply (simp (no_asm_use) only : Un_empty_left)
    apply (rule bdy)
    apply auto
    done
qed


theorem hoaret_complete: "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (iprover intro: MGT_implies_complete MGT_lemma [OF MGT_Call])

lemma hoaret_complete': 
  assumes cvalid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof (cases "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A")
  case True
  hence "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
    by (rule hoaret_complete)
  thus "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
    by (rule hoaret_augment_context) simp
next
  case False
  with cvalid
  show ?thesis
    by (rule ExFalso)
qed

subsection {* And Now: Some Useful Rules *}

subsubsection {* Modify Return *}

lemma ProcModifyReturn_sound:
  assumes valid_call: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P call init p return' c Q,A"
  assumes valid_modif: 
  "\<forall>\<sigma>. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} (Call p) (Modif \<sigma>),(ModifAbr \<sigma>)" 
  assumes res_modif:
  "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> return' s t = return s t"
  assumes ret_modifAbr: 
  "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> return' s t = return s t"
  shows "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  then have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/UNIV\<^esub> P (Call p) Q,A"
    by (auto intro: valid_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>call init p return c,Normal s\<rangle> \<Rightarrow> t"
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  from exec
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: exec_call_Normal_elim)
    fix bdy t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> \<Rightarrow> t" 
    from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>(Call p ),Normal (init s)\<rangle> \<Rightarrow> Normal t'"
      by (auto simp add: intro: exec.intros)
    from cvalidD [OF valid_modif [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> Modif (init s)"
      by auto
    with res_modif have "Normal (return' s t') = Normal (return s t')"
      by simp
    with exec_body exec_c bdy 
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_call)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Abrupt t'" 
    assume t: "t = Abrupt (return s t')"
    also from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>(Call p),Normal (init s)\<rangle> \<Rightarrow> Abrupt t'"
      by (auto simp add: intro: exec.intros)
    from cvalidD [OF valid_modif [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')" .
    with exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_callAbrupt)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy f
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Fault f"  and
      t: "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callFault)
    from cvalidt_postD [OF valid_call ctxt this P] t t_notin_F
    show ?thesis
      by simp
  next
    fix bdy
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Stuck"  
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callStuck)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  next
    assume "\<Gamma> p = None" "t=Stuck"
    hence "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callUndefined)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  then have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/UNIV\<^esub> P (Call p) Q,A"
    by (auto intro: valid_augment_Faults)
  assume P: "s \<in> P"
  from valid_call ctxt P
  have call: "\<Gamma>\<turnstile>call init p return' c\<down> Normal s"
    by (rule cvalidt_termD)
  show "\<Gamma>\<turnstile>call init p return c \<down> Normal s"
  proof (cases "p \<in> dom \<Gamma>")
    case True
    with call obtain bdy where 
      bdy: "\<Gamma> p = Some bdy" and termi_bdy: "\<Gamma>\<turnstile>bdy \<down> Normal (init s)" and 
      termi_c: "\<forall>t. \<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t \<longrightarrow> 
                    \<Gamma>\<turnstile>c s t \<down> Normal (return' s t)"
      by cases auto 
    {
      fix t
      assume exec_bdy: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t"
      hence "\<Gamma>\<turnstile>c s t \<down> Normal (return s t)"
      proof -
        from exec_bdy bdy
        have "\<Gamma>\<turnstile>\<langle>(Call p ),Normal (init s)\<rangle> \<Rightarrow> Normal t"
          by (auto simp add: intro: exec.intros)
        from cvalidD [OF valid_modif [rule_format, of "init s"] ctxt' this] P 
          res_modif
        have "return' s t = return s t"
          by auto
        with termi_c exec_bdy show ?thesis by auto
      qed
    }
    with bdy termi_bdy
    show ?thesis
      by (iprover intro: terminates_call)
  next
    case False
    thus ?thesis
      by (auto intro: terminates_callUndefined)
  qed
qed

lemma ProcModifyReturn:
  assumes spec: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return' c) Q,A"
  assumes res_modif:
  "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes ret_modifAbr: 
  "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes modifies_spec:    
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} (Call p) (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
apply (rule hoaret_complete') 
apply (rule ProcModifyReturn_sound [where Modif=Modif and ModifAbr=ModifAbr, 
        OF _ _ res_modif ret_modifAbr])
apply (rule hoaret_sound [OF spec])
using modifies_spec
apply (blast intro: hoare_sound)
done

lemma ProcModifyReturnSameFaults_sound:
  assumes valid_call: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P call init p return' c Q,A"
  assumes valid_modif: 
  "\<forall>\<sigma>. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> {\<sigma>} Call p (Modif \<sigma>),(ModifAbr \<sigma>)" 
  assumes res_modif:
  "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> return' s t = return s t"
  assumes ret_modifAbr: 
  "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> return' s t = return s t"
  shows "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  assume exec: "\<Gamma>\<turnstile>\<langle>call init p return c,Normal s\<rangle> \<Rightarrow> t"
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  from exec
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: exec_call_Normal_elim)
    fix bdy t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> \<Rightarrow> t" 
    from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>(Call p) ,Normal (init s)\<rangle> \<Rightarrow> Normal t'"
      by (auto simp add: intro: exec.intros)
    from cvalidD [OF valid_modif [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> Modif (init s)"
      by auto
    with res_modif have "Normal (return' s t') = Normal (return s t')"
      by simp
    with exec_body exec_c bdy 
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_call)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy t'
    assume bdy: "\<Gamma> p = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Abrupt t'" 
    assume t: "t = Abrupt (return s t')"
    also 
    from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>Call p ,Normal (init s)\<rangle> \<Rightarrow> Abrupt t'"
      by (auto simp add: intro: exec.intros)
    from cvalidD [OF valid_modif [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')" .
    with exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_callAbrupt)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy f
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Fault f"  and
      t: "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callFault)
    from cvalidt_postD [OF valid_call ctxt this P] t t_notin_F
    show ?thesis
      by simp
  next
    fix bdy
    assume bdy: "\<Gamma> p = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Stuck"  
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callStuck)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  next
    assume "\<Gamma> p = None" "t=Stuck"
    hence "\<Gamma>\<turnstile>\<langle>call init p return' c,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callUndefined)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  assume P: "s \<in> P"
  from valid_call ctxt P
  have call: "\<Gamma>\<turnstile>call init p return' c\<down> Normal s"
    by (rule cvalidt_termD)
  show "\<Gamma>\<turnstile>call init p return c \<down> Normal s"
  proof (cases "p \<in> dom \<Gamma>")
    case True
    with call obtain bdy where 
      bdy: "\<Gamma> p = Some bdy" and termi_bdy: "\<Gamma>\<turnstile>bdy \<down> Normal (init s)" and 
      termi_c: "\<forall>t. \<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t \<longrightarrow> 
                    \<Gamma>\<turnstile>c s t \<down> Normal (return' s t)"
      by cases auto 
    {
      fix t
      assume exec_bdy: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t"
      hence "\<Gamma>\<turnstile>c s t \<down> Normal (return s t)"
      proof -
        from exec_bdy bdy
        have "\<Gamma>\<turnstile>\<langle>(Call p ),Normal (init s)\<rangle> \<Rightarrow> Normal t"
          by (auto simp add: intro: exec.intros)
        from cvalidD [OF valid_modif [rule_format, of "init s"] ctxt' this] P 
          res_modif
        have "return' s t = return s t"
          by auto
        with termi_c exec_bdy show ?thesis by auto
      qed
    }
    with bdy termi_bdy
    show ?thesis
      by (iprover intro: terminates_call)
  next
    case False
    thus ?thesis
      by (auto intro: terminates_callUndefined)
  qed
qed

lemma ProcModifyReturnSameFaults:
  assumes spec: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return' c) Q,A"
  assumes res_modif:
  "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes ret_modifAbr: 
  "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes modifies_spec:    
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} (Call p) (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
apply (rule hoaret_complete') 
apply (rule ProcModifyReturnSameFaults_sound [where Modif=Modif and ModifAbr=ModifAbr,
          OF _ _ res_modif ret_modifAbr])
apply (rule hoaret_sound [OF spec])
using modifies_spec
apply (blast intro: hoare_sound)
done


subsubsection {* DynCall *}


lemma dynProcModifyReturn_sound:
assumes valid_call: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes valid_modif: 
    "\<forall>s\<in>P. \<forall>\<sigma>. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} (Call (p s)) (Modif \<sigma>),(ModifAbr \<sigma>)" 
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> return' s t = return s t"
shows "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  then have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/UNIV\<^esub> P (Call p) Q,A"
    by (auto intro: valid_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>dynCall init p return c,Normal s\<rangle> \<Rightarrow> t"
  assume t_notin_F: "t \<notin> Fault ` F"
  assume P: "s \<in> P"
  with valid_modif 
  have valid_modif': 
    "\<forall>\<sigma>. \<Gamma>,\<Theta>\<Turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} (Call (p s)) (Modif \<sigma>),(ModifAbr \<sigma>)"
    by blast
  from exec
  have "\<Gamma>\<turnstile>\<langle>call init (p s) return c,Normal s\<rangle> \<Rightarrow> t"
    by (cases rule: exec_dynCall_Normal_elim)
  then show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: exec_call_Normal_elim)
    fix bdy t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> \<Rightarrow> t" 
    from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s),Normal (init s)\<rangle> \<Rightarrow> Normal t'"
      by (auto simp add: intro: exec.Call)
    from cvalidD [OF valid_modif' [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> Modif (init s)"
      by auto
    with ret_modif have "Normal (return' s t') = 
      Normal (return s t')"
      by simp
    with exec_body exec_c bdy
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_call)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Abrupt t'" 
    assume t: "t = Abrupt (return s t')"
    also from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s) ,Normal (init s)\<rangle> \<Rightarrow> Abrupt t'"
      by (auto simp add: intro: exec.intros)
    from cvalidD [OF valid_modif' [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')" .
    with exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_callAbrupt)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy f
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Fault f"  and
      t: "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callFault)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from cvalidt_postD [OF valid_call ctxt this P] t t_notin_F
    show ?thesis
      by blast
  next
    fix bdy
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Stuck"  
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callStuck)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  next
    fix bdy
    assume "\<Gamma> (p s) = None" "t=Stuck"
    hence "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callUndefined)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  then have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/UNIV\<^esub> P (Call p) Q,A"
    by (auto intro: valid_augment_Faults)
  assume P: "s \<in> P"
  from valid_call ctxt P
  have "\<Gamma>\<turnstile>dynCall init p return' c\<down> Normal s"
    by (rule cvalidt_termD)
  hence call: "\<Gamma>\<turnstile>call init (p s) return' c\<down> Normal s"
    by cases
  have "\<Gamma>\<turnstile>call init (p s) return c \<down> Normal s"
  proof (cases "p s \<in> dom \<Gamma>")
    case True
    with call obtain bdy where 
      bdy: "\<Gamma> (p s) = Some bdy" and termi_bdy: "\<Gamma>\<turnstile>bdy \<down> Normal (init s)" and 
      termi_c: "\<forall>t. \<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t \<longrightarrow> 
                    \<Gamma>\<turnstile>c s t \<down> Normal (return' s t)"
      by cases auto 
    {
      fix t
      assume exec_bdy: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t"
      hence "\<Gamma>\<turnstile>c s t \<down> Normal (return s t)"
      proof -
        from exec_bdy bdy
        have "\<Gamma>\<turnstile>\<langle>Call (p s),Normal (init s)\<rangle> \<Rightarrow> Normal t"
          by (auto simp add: intro: exec.intros)
        from cvalidD [OF valid_modif [rule_format, of s "init s"] ctxt' this] P 
          ret_modif
        have "return' s t = return s t"
          by auto
        with termi_c exec_bdy show ?thesis by auto
      qed
    }
    with bdy termi_bdy
    show ?thesis
      by (iprover intro: terminates_call)
  next
    case False
    thus ?thesis
      by (auto intro: terminates_callUndefined)
  qed
  thus "\<Gamma>\<turnstile>dynCall init p return c \<down> Normal s"
    by (iprover intro: terminates_dynCall)
qed

lemma dynProcModifyReturn:
assumes dyn_call: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) 
           \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) 
                             \<longrightarrow> return' s t = return s t"
assumes modif: 
    "\<forall>s \<in> P. \<forall>\<sigma>.  
       \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)" 
shows "\<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
apply (rule hoaret_complete')
apply (rule dynProcModifyReturn_sound 
        [where Modif=Modif and ModifAbr=ModifAbr,
            OF hoaret_sound [OF dyn_call] _ ret_modif ret_modifAbr])
apply (intro ballI allI)
apply (rule hoare_sound [OF modif [rule_format]])
apply assumption
done

lemma dynProcModifyReturnSameFaults_sound:
assumes valid_call: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes valid_modif: 
    "\<forall>s\<in>P. \<forall>\<sigma>. \<Gamma>,\<Theta> \<Turnstile>\<^bsub>/F\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)" 
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> return' s t = return s t"
shows "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  assume exec: "\<Gamma>\<turnstile>\<langle>dynCall init p return c,Normal s\<rangle> \<Rightarrow> t"
  assume t_notin_F: "t \<notin> Fault ` F"
  assume P: "s \<in> P"
  with valid_modif 
  have valid_modif': 
    "\<forall>\<sigma>. \<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> {\<sigma>} (Call (p s)) (Modif \<sigma>),(ModifAbr \<sigma>)"
    by blast
  from exec
  have "\<Gamma>\<turnstile>\<langle>call init (p s) return c,Normal s\<rangle> \<Rightarrow> t"
    by (cases rule: exec_dynCall_Normal_elim)
  then show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: exec_call_Normal_elim)
    fix bdy t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> \<Rightarrow> t" 
    from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s),Normal (init s)\<rangle> \<Rightarrow> Normal t'"
      by (auto simp add: intro: exec.intros)
    from cvalidD [OF valid_modif' [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> Modif (init s)"
      by auto
    with ret_modif have "Normal (return' s t') = 
      Normal (return s t')"
      by simp
    with exec_body exec_c bdy
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_call)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy t'
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Abrupt t'" 
    assume t: "t = Abrupt (return s t')"
    also from exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>Call (p s)  ,Normal (init s)\<rangle> \<Rightarrow> Abrupt t'"
      by (auto simp add: intro: exec.intros)
    from cvalidD [OF valid_modif' [rule_format, of "init s"] ctxt' this] P
    have "t' \<in> ModifAbr (init s)"
      by auto
    with ret_modifAbr have "Abrupt (return s t') = Abrupt (return' s t')"
      by simp
    finally have "t = Abrupt (return' s t')" .
    with exec_body bdy
    have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (auto intro: exec_callAbrupt)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from cvalidt_postD [OF valid_call ctxt this] P t_notin_F
    show ?thesis
      by simp
  next
    fix bdy f
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Fault f"  and
      t: "t = Fault f"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callFault)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from cvalidt_postD [OF valid_call ctxt this P] t t_notin_F
    show ?thesis
      by simp
  next
    fix bdy
    assume bdy: "\<Gamma> (p s) = Some bdy"
    assume "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Stuck"  
      "t = Stuck"
    with bdy have "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callStuck)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  next
    fix bdy
    assume "\<Gamma> (p s) = None" "t=Stuck"
    hence "\<Gamma>\<turnstile>\<langle>call init (p s) return' c ,Normal s\<rangle> \<Rightarrow> t"
      by (auto intro: exec_callUndefined)
    hence "\<Gamma>\<turnstile>\<langle>dynCall init p return' c,Normal s\<rangle> \<Rightarrow> t" 
      by (rule exec_dynCall)
    from valid_call ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def)
  assume P: "s \<in> P"
  from valid_call ctxt P
  have "\<Gamma>\<turnstile>dynCall init p return' c\<down> Normal s"
    by (rule cvalidt_termD)
  hence call: "\<Gamma>\<turnstile>call init (p s) return' c\<down> Normal s"
    by cases
  have "\<Gamma>\<turnstile>call init (p s) return c \<down> Normal s"
  proof (cases "p s \<in> dom \<Gamma>")
    case True
    with call obtain bdy where 
      bdy: "\<Gamma> (p s) = Some bdy" and termi_bdy: "\<Gamma>\<turnstile>bdy \<down> Normal (init s)" and 
      termi_c: "\<forall>t. \<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t \<longrightarrow> 
                    \<Gamma>\<turnstile>c s t \<down> Normal (return' s t)"
      by cases auto 
    {
      fix t
      assume exec_bdy: "\<Gamma>\<turnstile>\<langle>bdy,Normal (init s)\<rangle> \<Rightarrow> Normal t"
      hence "\<Gamma>\<turnstile>c s t \<down> Normal (return s t)"
      proof -
        from exec_bdy bdy
        have "\<Gamma>\<turnstile>\<langle>Call (p s),Normal (init s)\<rangle> \<Rightarrow> Normal t"
          by (auto simp add: intro: exec.intros)
        from cvalidD [OF valid_modif [rule_format, of s "init s"] ctxt' this] P 
          ret_modif
        have "return' s t = return s t"
          by auto
        with termi_c exec_bdy show ?thesis by auto
      qed
    }
    with bdy termi_bdy
    show ?thesis
      by (iprover intro: terminates_call)
  next
    case False
    thus ?thesis
      by (auto intro: terminates_callUndefined)
  qed
  thus "\<Gamma>\<turnstile>dynCall init p return c \<down> Normal s"
    by (iprover intro: terminates_dynCall)
qed

lemma dynProcModifyReturnSameFaults:
assumes dyn_call: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P dynCall init p return' c Q,A"
assumes ret_modif:
    "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> return' s t = return s t"
assumes ret_modifAbr: "\<forall>s t. t \<in> ModifAbr (init s) \<longrightarrow> return' s t = return s t"
assumes modif: 
    "\<forall>s \<in> P. \<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Call (p s) (Modif \<sigma>),(ModifAbr \<sigma>)" 
shows "\<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
apply (rule hoaret_complete')
apply (rule dynProcModifyReturnSameFaults_sound 
        [where Modif=Modif and ModifAbr=ModifAbr,
          OF hoaret_sound [OF dyn_call] _ ret_modif ret_modifAbr])
apply (intro ballI allI)
apply (rule hoare_sound [OF modif [rule_format]])
apply assumption
done

subsubsection {* Conjunction of Postcondition *}

lemma PostConjI_sound:
  assumes valid_Q: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes valid_R: "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c R,B"
  shows "\<Gamma>,\<Theta> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> B)"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  from valid_Q ctxt exec P t_notin_F have "t \<in> Normal ` Q \<union> Abrupt ` A"
    by (rule cvalidt_postD)
  moreover
  from valid_R ctxt exec P t_notin_F have "t \<in> Normal ` R \<union> Abrupt ` B"
    by (rule cvalidt_postD)
  ultimately show "t \<in> Normal ` (Q \<inter> R) \<union> Abrupt ` (A \<inter> B)"
    by blast
next 
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume P: "s \<in> P"
  from valid_Q ctxt P
  show "\<Gamma>\<turnstile>c \<down> Normal s"
    by (rule cvalidt_termD)
qed

lemma PostConjI:
  assumes deriv_Q: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" 
  assumes deriv_R: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c R,B"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> B)"
apply (rule hoaret_complete')
apply (rule PostConjI_sound)
apply (rule hoaret_sound [OF deriv_Q])
apply (rule hoaret_sound [OF deriv_R])
done


lemma Merge_PostConj_sound: 
  assumes validF: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes validG: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/G\<^esub> P' c R,X"
  assumes F_G: "F \<subseteq> G"
  assumes P_P': "P \<subseteq> P'"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> X)"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  with F_G have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/G\<^esub> P (Call p) Q,A" 
    by (auto intro: validt_augment_Faults)
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P" 
  with P_P' have P': "s \<in> P'"
    by auto
  assume t_noFault: "t \<notin> Fault ` F"
  show "t \<in> Normal ` (Q \<inter> R) \<union> Abrupt ` (A \<inter> X)"
  proof -
    from cvalidt_postD [OF validF [rule_format] ctxt exec P t_noFault]
    have "t \<in> Normal ` Q \<union> Abrupt ` A".
    moreover from this have "t \<notin> Fault ` G"
      by auto
    from cvalidt_postD [OF validG [rule_format] ctxt' exec P' this]
    have "t \<in> Normal ` R \<union> Abrupt ` X" .
    ultimately show ?thesis by auto
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume P: "s \<in> P"
  from validF ctxt P
  show "\<Gamma>\<turnstile>c \<down> Normal s"
    by (rule cvalidt_termD)
qed



lemma Merge_PostConj: 
  assumes validF: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes validG: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/G\<^esub> P' c R,X"
  assumes F_G: "F \<subseteq> G"
  assumes P_P': "P \<subseteq> P'"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> X)"
apply (rule hoaret_complete')
apply (rule Merge_PostConj_sound [OF _ _ F_G P_P'])
using validF apply (blast intro:hoaret_sound)
using validG apply (blast intro:hoaret_sound)
done


subsubsection {* Guards and Guarantees *}

lemma SplitGuards_sound:
  assumes valid_c1: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 Q,A"
  assumes valid_c2: "\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c\<^sub>2 UNIV,UNIV"
  assumes c: "(c\<^sub>1 \<inter>\<^sub>g c\<^sub>2) = Some c"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto simp add: validt_def) 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P"
  assume t_notin_F: "t \<notin> Fault ` F"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases t)
    case Normal
    with inter_guards_exec_noFault [OF c exec]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> t" by simp
    from valid_c1 ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  next
    case Abrupt
    with inter_guards_exec_noFault [OF c exec]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> t" by simp
    from valid_c1 ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  next
    case (Fault f)
    assume t: "t=Fault f"
    with exec inter_guards_exec_Fault [OF c]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Fault f \<or> \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow> Fault f"
      by auto
    then show ?thesis
    proof (cases rule: disjE [consumes 1])
      assume "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> Fault f"
      from cvalidt_postD [OF valid_c1 ctxt this P] t t_notin_F
      show ?thesis
        by blast
    next
      assume "\<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow> Fault f"
      from cvalidD [OF valid_c2 ctxt' this P] t t_notin_F
      show ?thesis
        by blast
    qed
  next
    case Stuck
    with inter_guards_exec_noFault [OF c exec]
    have "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> t" by simp
    from valid_c1 ctxt this P t_notin_F
    show ?thesis
      by (rule cvalidt_postD)
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume P: "s \<in> P"
  show "\<Gamma>\<turnstile>c \<down> Normal s"
  proof -
    from valid_c1 ctxt P
    have "\<Gamma>\<turnstile>c\<^sub>1 \<down> Normal s"
      by (rule cvalidt_termD)
    with c show ?thesis
      by (rule inter_guards_terminates)
  qed
qed

lemma SplitGuards: 
  assumes c: "(c\<^sub>1 \<inter>\<^sub>g c\<^sub>2) = Some c" 
  assumes deriv_c1: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 Q,A" 
  assumes deriv_c2: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c\<^sub>2 UNIV,UNIV" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
apply (rule hoaret_complete')
apply (rule SplitGuards_sound [OF _ _ c])
apply (rule hoaret_sound [OF deriv_c1])
apply (rule hoare_sound [OF deriv_c2])
done

lemma CombineStrip_sound:
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes valid_strip: "\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/{}\<^esub> P (strip_guards (-F) c) UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^bsub>/{}\<^esub> P (Call p) Q,A"
    by (auto simp add: validt_def)
  from ctxt have ctxt'': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto intro: valid_augment_Faults simp add: validt_def)
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases t)
    case (Normal t')
    from cvalidt_postD [OF valid ctxt'' exec P] Normal 
    show ?thesis
      by auto
  next
    case (Abrupt t')
    from cvalidt_postD [OF valid ctxt'' exec P] Abrupt 
    show ?thesis
      by auto
  next
    case (Fault f)
    show ?thesis
    proof (cases "f \<in> F")
      case True
      hence "f \<notin> -F" by simp
      with exec Fault
      have "\<Gamma>\<turnstile>\<langle>strip_guards (-F) c,Normal s\<rangle> \<Rightarrow> Fault f" 
        by (auto intro: exec_to_exec_strip_guards_Fault)
      from cvalidD [OF valid_strip ctxt' this P] Fault
      have False
        by auto
      thus ?thesis ..
    next
      case False
      with cvalidt_postD [OF valid ctxt'' exec P] Fault
      show ?thesis
        by auto
    qed
  next
    case Stuck
    from cvalidt_postD [OF valid ctxt'' exec P] Stuck
    show ?thesis
      by auto
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto intro: valid_augment_Faults simp add: validt_def)
  assume P: "s \<in> P"
  show "\<Gamma>\<turnstile>c \<down> Normal s"
  proof -
    from valid ctxt' P
    show "\<Gamma>\<turnstile>c \<down> Normal s"
      by (rule cvalidt_termD)
  qed
qed

lemma CombineStrip:
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes deriv_strip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P (strip_guards (-F) c) UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoaret_complete')
apply (rule CombineStrip_sound)
apply  (iprover intro: hoaret_sound [OF deriv])
apply (iprover intro: hoare_sound [OF deriv_strip])
done

lemma GuardsFlip_sound:
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes validFlip: "\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/-F\<^esub> P c UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  from ctxt have ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto intro: valid_augment_Faults simp add: validt_def)
  from ctxt have ctxtFlip: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^bsub>/-F\<^esub> P (Call p) Q,A" 
    by (auto intro: valid_augment_Faults simp add: validt_def)
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases t)
    case (Normal t')
    from cvalidt_postD [OF valid ctxt' exec P] Normal 
    show ?thesis
      by auto
  next
    case (Abrupt t')
    from cvalidt_postD [OF valid ctxt' exec P] Abrupt 
    show ?thesis
      by auto
  next
    case (Fault f)
    show ?thesis
    proof (cases "f \<in> F")
      case True
      hence "f \<notin> -F" by simp
      with cvalidD [OF validFlip ctxtFlip exec P] Fault
      have False
        by auto
      thus ?thesis ..
    next
      case False
      with cvalidt_postD [OF valid ctxt' exec P] Fault
      show ?thesis
        by auto
    qed
  next
    case Stuck
    from cvalidt_postD [OF valid ctxt' exec P] Stuck
    show ?thesis
      by auto
  qed
next
  fix s
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma> \<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A"
  hence ctxt': "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
    by (auto intro: valid_augment_Faults simp add: validt_def)
  assume P: "s \<in> P"
  show "\<Gamma>\<turnstile>c \<down> Normal s"
  proof -
    from valid ctxt' P
    show "\<Gamma>\<turnstile>c \<down> Normal s"
      by (rule cvalidt_termD)
  qed
qed


lemma GuardsFlip: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  assumes derivFlip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/-F\<^esub> P c UNIV,UNIV"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoaret_complete')
apply (rule GuardsFlip_sound)
apply  (iprover intro: hoaret_sound [OF deriv])
apply (iprover intro: hoare_sound [OF derivFlip])
done

lemma MarkGuardsI_sound: 
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P mark_guards f c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>mark_guards f c,Normal s\<rangle> \<Rightarrow> t" 
  from exec_mark_guards_to_exec [OF exec] obtain t' where
    exec_c: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t'" and
    t'_noFault: "\<not> isFault t' \<longrightarrow> t' = t"
    by blast
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof -
    from cvalidt_postD [OF valid [rule_format] ctxt exec_c P]
    have "t' \<in> Normal ` Q \<union> Abrupt ` A"
      by blast
    with t'_noFault
    show ?thesis
      by auto
  qed
next
  fix s 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume P: "s \<in> P" 
  from cvalidt_termD [OF valid ctxt P]
  have "\<Gamma>\<turnstile>c \<down> Normal s".
  thus "\<Gamma>\<turnstile>mark_guards f c \<down> Normal s"
    by (rule terminates_to_terminates_mark_guards)
qed

lemma MarkGuardsI: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P mark_guards f c Q,A"
apply (rule hoaret_complete')
apply (rule MarkGuardsI_sound)
apply (iprover intro: hoaret_sound [OF deriv])
done


lemma MarkGuardsD_sound: 
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P mark_guards f c Q,A" 
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases "isFault t")
    case True
    with exec_to_exec_mark_guards_Fault exec
    obtain f' where "\<Gamma>\<turnstile>\<langle>mark_guards f c,Normal s\<rangle> \<Rightarrow> Fault f'"
      by (fastforce elim: isFaultE)
    from cvalidt_postD [OF valid [rule_format] ctxt this P]
    have False
      by auto
    thus ?thesis ..
  next
    case False
    from exec_to_exec_mark_guards [OF exec False]
    obtain f' where "\<Gamma>\<turnstile>\<langle>mark_guards f c,Normal s\<rangle> \<Rightarrow> t"
      by auto
    from cvalidt_postD [OF valid [rule_format] ctxt this P]
    show ?thesis
      by auto
  qed
next
  fix s 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume P: "s \<in> P" 
  from cvalidt_termD [OF valid ctxt P]
  have "\<Gamma>\<turnstile>mark_guards f c \<down> Normal s".
  thus "\<Gamma>\<turnstile>c \<down> Normal s"
    by (rule terminates_mark_guards_to_terminates)
qed

lemma MarkGuardsD: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P mark_guards f c Q,A" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoaret_complete')
apply (rule MarkGuardsD_sound)
apply (iprover intro: hoaret_sound [OF deriv])
done

lemma MergeGuardsI_sound: 
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P merge_guards c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume exec_merge: "\<Gamma>\<turnstile>\<langle>merge_guards c,Normal s\<rangle> \<Rightarrow> t"
  from exec_merge_guards_to_exec [OF exec_merge] 
  have exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" .
  assume P: "s \<in> P" 
  assume t_notin_F: "t \<notin> Fault ` F"
  from cvalidt_postD [OF valid [rule_format] ctxt exec P t_notin_F]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
next
  fix s 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume P: "s \<in> P" 
  from cvalidt_termD [OF valid ctxt P]
  have "\<Gamma>\<turnstile>c \<down> Normal s".
  thus "\<Gamma>\<turnstile>merge_guards c \<down> Normal s"
    by (rule terminates_to_terminates_merge_guards)
qed

lemma MergeGuardsI: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P merge_guards c Q,A"
apply (rule hoaret_complete')
apply (rule MergeGuardsI_sound)
apply (iprover intro: hoaret_sound [OF deriv])
done

lemma MergeGuardsD_sound: 
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P merge_guards c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  from exec_to_exec_merge_guards [OF exec] 
  have exec_merge: "\<Gamma>\<turnstile>\<langle>merge_guards c,Normal s\<rangle> \<Rightarrow> t".
  assume P: "s \<in> P" 
  assume t_notin_F: "t \<notin> Fault ` F"
  from cvalidt_postD [OF valid [rule_format] ctxt exec_merge P t_notin_F]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
next
  fix s 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume P: "s \<in> P" 
  from cvalidt_termD [OF valid ctxt P]
  have "\<Gamma>\<turnstile>merge_guards c \<down> Normal s".
  thus "\<Gamma>\<turnstile>c \<down> Normal s"
    by (rule terminates_merge_guards_to_terminates)
qed

lemma MergeGuardsD: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P merge_guards c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
apply (rule hoaret_complete')
apply (rule MergeGuardsD_sound)
apply (iprover intro: hoaret_sound [OF deriv])
done


lemma SubsetGuards_sound: 
  assumes c_c': "c \<subseteq>\<^sub>g c'"
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c' Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  from exec_to_exec_subseteq_guards [OF c_c' exec] obtain t' where
    exec_c': "\<Gamma>\<turnstile>\<langle>c',Normal s\<rangle> \<Rightarrow> t'" and
    t'_noFault: "\<not> isFault t' \<longrightarrow> t' = t"
    by blast
  assume P: "s \<in> P" 
  assume t_noFault: "t \<notin> Fault ` {}"
  from cvalidt_postD [OF valid [rule_format] ctxt exec_c' P] t'_noFault t_noFault
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
    by auto
next
  fix s 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/{}\<^esub> P (Call p) Q,A" 
  assume P: "s \<in> P" 
  from cvalidt_termD [OF valid ctxt P]
  have termi_c': "\<Gamma>\<turnstile>c' \<down> Normal s".
  from cvalidt_postD [OF valid ctxt _ P]
  have noFault_c': "\<Gamma>\<turnstile>\<langle>c',Normal s\<rangle> \<Rightarrow>\<notin>Fault ` UNIV"
    by (auto simp add: final_notin_def)
  from termi_c' c_c' noFault_c'
  show "\<Gamma>\<turnstile>c \<down> Normal s"
    by (rule terminates_fewer_guards)
qed

lemma SubsetGuards: 
  assumes c_c': "c \<subseteq>\<^sub>g c'"
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c' Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
apply (rule hoaret_complete')
apply (rule SubsetGuards_sound [OF c_c'])
apply (iprover intro: hoaret_sound [OF deriv])
done

lemma NormalizeD_sound: 
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (normalize c) Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
  hence exec_norm: "\<Gamma>\<turnstile>\<langle>normalize c,Normal s\<rangle> \<Rightarrow> t" 
    by (rule exec_to_exec_normalize)
  assume P: "s \<in> P" 
  assume noFault: "t \<notin> Fault ` F"
  from cvalidt_postD [OF valid [rule_format] ctxt exec_norm P noFault]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
next
  fix s 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume P: "s \<in> P" 
  from cvalidt_termD [OF valid ctxt P]
  have "\<Gamma>\<turnstile>normalize c \<down> Normal s".
  thus "\<Gamma>\<turnstile>c \<down> Normal s"
    by (rule terminates_normalize_to_terminates)
qed

lemma NormalizeD: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (normalize c) Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
apply (rule hoaret_complete')
apply (rule NormalizeD_sound)
apply (iprover intro: hoaret_sound [OF deriv])
done

lemma NormalizeI_sound: 
  assumes valid: "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (normalize c) Q,A"
proof (rule cvalidtI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume "\<Gamma>\<turnstile>\<langle>normalize c,Normal s\<rangle> \<Rightarrow> t" 
  hence exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t" 
    by (rule exec_normalize_to_exec)
  assume P: "s \<in> P" 
  assume noFault: "t \<notin> Fault ` F"
  from cvalidt_postD [OF valid [rule_format] ctxt exec P noFault]
  show "t \<in> Normal ` Q \<union> Abrupt ` A".
next
  fix s 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A" 
  assume P: "s \<in> P" 
  from cvalidt_termD [OF valid ctxt P]
  have "\<Gamma>\<turnstile> c \<down> Normal s".
  thus "\<Gamma>\<turnstile>normalize c \<down> Normal s"
    by (rule terminates_to_terminates_normalize)
qed

lemma NormalizeI: 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (normalize c) Q,A"
apply (rule hoaret_complete')
apply (rule NormalizeI_sound)
apply (iprover intro: hoaret_sound [OF deriv])
done

subsubsection {* Restricting the Procedure Environment *}

lemma validt_restrict_to_validt:
assumes validt_c: "\<Gamma>|\<^bsub>M\<^esub>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
shows "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof -
  from validt_c
  have valid_c: "\<Gamma>|\<^bsub>M\<^esub>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A" by (simp add: validt_def)
  hence "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A" by (rule valid_restrict_to_valid)
  moreover
  {
    fix s
    assume P: "s \<in> P"
    have "\<Gamma>\<turnstile>c\<down>Normal s"
    proof -
      from P validt_c have "\<Gamma>|\<^bsub>M\<^esub>\<turnstile>c\<down>Normal s"
        by (auto simp add: validt_def)
      moreover
      from P valid_c
      have "\<Gamma>|\<^bsub>M\<^esub>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
        by (auto simp add: valid_def  final_notin_def)
      ultimately show ?thesis
        by (rule terminates_restrict_to_terminates)
    qed
   }
   ultimately show ?thesis
     by (auto simp add: validt_def)
qed


lemma augment_procs:
assumes deriv_c: "\<Gamma>|\<^bsub>M\<^esub>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
shows "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  apply (rule hoaret_complete)
  apply (rule validt_restrict_to_validt)
  apply (insert hoaret_sound [OF deriv_c])
  by (simp add: cvalidt_def)

subsubsection {* Miscellaneous *}

lemma augment_Faults:
assumes deriv_c: "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
assumes F: "F \<subseteq> F'"
shows "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F'\<^esub> P c Q,A"
  apply (rule hoaret_complete)
  apply (rule validt_augment_Faults [OF _ F])
  apply (insert hoaret_sound [OF deriv_c])
  by (simp add: cvalidt_def)

lemma TerminationPartial_sound:
  assumes "termination": "\<forall>s \<in> P. \<Gamma>\<turnstile>c\<down>Normal s"
  assumes partial_corr: "\<Gamma>,\<Theta>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
using "termination" partial_corr 
by (auto simp add: cvalidt_def validt_def cvalid_def)

lemma TerminationPartial:
  assumes partial_deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  assumes "termination": "\<forall>s \<in> P. \<Gamma>\<turnstile>c\<down>Normal s"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  apply (rule hoaret_complete')
  apply (rule TerminationPartial_sound [OF "termination"])
  apply (rule hoare_sound [OF partial_deriv])
  done

lemma TerminationPartialStrip:
  assumes partial_deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  assumes "termination": "\<forall>s \<in> P. strip F' \<Gamma>\<turnstile>strip_guards F' c\<down>Normal s"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof -
  from "termination" have "\<forall>s \<in> P. \<Gamma>\<turnstile>c\<down>Normal s"
    by (auto intro: terminates_strip_guards_to_terminates 
      terminates_strip_to_terminates)
  with partial_deriv
  show ?thesis
    by (rule TerminationPartial)
qed

lemma SplitTotalPartial:
  assumes termi: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q',A'"
  assumes part: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof -
  from hoaret_sound [OF termi] hoare_sound [OF part]
  have "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
    by (fastforce simp add: cvalidt_def validt_def cvalid_def valid_def)
  thus ?thesis
    by (rule hoaret_complete')
qed
   
lemma SplitTotalPartial':
  assumes termi: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/UNIV\<^esub> P c Q',A'"
  assumes part: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
proof -
  from hoaret_sound [OF termi] hoare_sound [OF part]
  have "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
    by (fastforce simp add: cvalidt_def validt_def cvalid_def valid_def)
  thus ?thesis
    by (rule hoaret_complete')
qed
 
end
