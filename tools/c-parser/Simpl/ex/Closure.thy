(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Closure.thy
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

section "Experiments with Closures"

theory Closure
imports "../Hoare"
begin


definition
"callClosure upd cl = Seq (Basic (upd (fst cl))) (Call (snd cl))"


definition
"dynCallClosure init upd cl return c =
  DynCom (\<lambda>s. call (upd (fst (cl s)) \<circ> init) (snd (cl s)) return c)"





lemma dynCallClosure_sound:
assumes adapt: 
  "P \<subseteq> {s. \<exists>P' Q' A'. \<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub> P' (callClosure upd (cl s)) Q',A' \<and>
                  init s \<in> P' \<and> 
                  (\<forall>t \<in> Q'. return s t \<in> R s t) \<and>
                  (\<forall>t \<in> A'. return s t \<in> A)}"
assumes res: "\<forall>s t n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
shows
"\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>P (dynCallClosure init upd cl return c) Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P Call p Q,A"
  assume exec: "\<Gamma>\<turnstile> \<langle>dynCallClosure init upd cl return c,Normal s\<rangle> =n\<Rightarrow> t" 
  from execn.Basic [where f="(upd (fst (cl s)))" and s="(init s)"]
  have exec_upd: "\<Gamma>\<turnstile>\<langle>Basic (upd (fst (cl s))),Normal (init s)\<rangle> =n\<Rightarrow> 
             Normal (((upd (fst (cl s))) \<circ> init) s)"
      by auto
  assume P: "s \<in> P"
  from P adapt obtain P' Q' A'
      where 
      valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub> P' (callClosure upd (cl s)) Q',A'" and
      init_P': "init s \<in> P'"  and
      R: "(\<forall>t \<in> Q'. return s t \<in> R s t)" and
      A: "(\<forall>t \<in> A'. return s t \<in> A)"
      by auto
  assume t_notin_F: "t \<notin> Fault ` F"
  from exec [simplified dynCallClosure_def]
  have exec_call:
      "\<Gamma>\<turnstile>\<langle>call (upd (fst (cl s)) \<circ> init) (snd (cl s)) return c,Normal s\<rangle> =n\<Rightarrow> t"
    by cases
  then
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof (cases rule: execn_call_Normal_elim)
    fix bdy m t'
    assume bdy: "\<Gamma> (snd (cl s)) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =m\<Rightarrow> Normal t'" 
    assume exec_c: "\<Gamma>\<turnstile>\<langle>c s t',Normal (return s t')\<rangle> =Suc m\<Rightarrow> t"
    assume n: "n = Suc m"
    have "\<Gamma>\<turnstile>\<langle>Basic init,Normal s\<rangle> =m\<Rightarrow> Normal (init s)" 
      by (rule execn.Basic)
    from bdy exec_body 
    have exec_callC:
      "\<Gamma>\<turnstile>\<langle>Call (snd (cl s)),Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =Suc m\<Rightarrow> Normal t'"
      by (rule execn.Call)
    from execn.Seq [OF exec_upd [simplified n]exec_callC]
    have exec_closure: "\<Gamma>\<turnstile> \<langle>callClosure upd (cl s),Normal (init s)\<rangle> =n\<Rightarrow> Normal t'"
      by (simp add: callClosure_def n)
    from cnvalidD [OF valid [rule_format] ctxt exec_closure init_P']
    have "t' \<in> Q'"
      by auto
    with R have "return s t' \<in> R s t'"
      by auto
    from cnvalidD [OF res [rule_format] ctxt exec_c [simplified n[symmetric]] this
         t_notin_F]
    show ?thesis
      by auto
  next
    fix bdy m t'
    assume bdy: "\<Gamma> (snd (cl s)) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =m\<Rightarrow> Abrupt t'" 
    assume t: "t=Abrupt (return s t')"
    assume n: "n = Suc m"
    from bdy exec_body 
    have exec_callC:
      "\<Gamma>\<turnstile>\<langle>Call (snd (cl s)),Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =Suc m\<Rightarrow> Abrupt t'"
      by (rule execn.Call)
    from execn.Seq [OF exec_upd [simplified n] exec_callC]
    have exec_closure: "\<Gamma>\<turnstile> \<langle>callClosure upd (cl s),Normal (init s)\<rangle> =n\<Rightarrow> Abrupt t'"
      by (simp add: callClosure_def n)

    from cnvalidD [OF valid [rule_format] ctxt exec_closure init_P']
    have "t' \<in> A'"
      by auto
    with A have "return s t' \<in> A"
      by auto
    with t show ?thesis
      by auto
  next
    fix bdy m f
    assume bdy: "\<Gamma> (snd (cl s)) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =m\<Rightarrow> Fault f" 
    assume t: "t=Fault f"
    assume n: "n = Suc m"
    from bdy exec_body 
    have exec_callC:
      "\<Gamma>\<turnstile>\<langle>Call (snd (cl s)),Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =Suc m\<Rightarrow> Fault f"
      by (rule execn.Call)
    from execn.Seq [OF exec_upd [simplified n] exec_callC]
    have exec_closure: "\<Gamma>\<turnstile> \<langle>callClosure upd (cl s),Normal (init s)\<rangle> =n\<Rightarrow> Fault f"
      by (simp add: callClosure_def n)
    from cnvalidD [OF valid [rule_format] ctxt exec_closure init_P'] t_notin_F t
    have False
      by auto
    thus ?thesis ..
  next
    fix bdy m 
    assume bdy: "\<Gamma> (snd (cl s)) = Some bdy"
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =m\<Rightarrow> Stuck" 
    assume t: "t=Stuck"
    assume n: "n = Suc m"
    from execn.Basic [where f="(upd (fst (cl s)))" and s="(init s)"]
    have exec_upd: "\<Gamma>\<turnstile>\<langle>Basic (upd (fst (cl s))),Normal (init s)\<rangle> =Suc m\<Rightarrow> 
             Normal (((upd (fst (cl s))) \<circ> init) s)"
      by auto
    from bdy exec_body 
    have exec_callC:
      "\<Gamma>\<turnstile>\<langle>Call (snd (cl s)),Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =Suc m\<Rightarrow> Stuck"
      by (rule execn.Call)
    from execn.Seq [OF exec_upd [simplified n] exec_callC]
    have exec_closure: "\<Gamma>\<turnstile> \<langle>callClosure upd (cl s),Normal (init s)\<rangle> =n\<Rightarrow> Stuck"
      by (simp add: callClosure_def n)
    from cnvalidD [OF valid [rule_format] ctxt exec_closure init_P'] t_notin_F t
    have False
      by auto
    thus ?thesis ..
  next
    fix m
    assume no_bdy: "\<Gamma> (snd (cl s)) = None"
    assume t: "t=Stuck"
    assume n: "n = Suc m"
    from no_bdy  
    have exec_callC:
      "\<Gamma>\<turnstile>\<langle>Call (snd (cl s)),Normal ((upd (fst (cl s)) \<circ> init) s)\<rangle> =Suc m\<Rightarrow> Stuck"
      by (rule execn.CallUndefined)
    from execn.Seq [OF exec_upd [simplified n]exec_callC]
    have exec_closure: "\<Gamma>\<turnstile> \<langle>callClosure upd (cl s),Normal (init s)\<rangle> =n\<Rightarrow> Stuck"
      by (simp add: callClosure_def n)
    from cnvalidD [OF valid [rule_format] ctxt exec_closure init_P'] t_notin_F t
    have False
      by auto
    thus ?thesis ..
  qed
qed

      
lemma dynCallClosure:
assumes adapt: "P \<subseteq> {s. \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub> P' (callClosure upd (cl s)) Q',A' \<and>
                  init s \<in> P' \<and> 
                  (\<forall>t \<in> Q'. return s t \<in> R s t) \<and>
                  (\<forall>t \<in> A'. return s t \<in> A)}"
assumes res: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
shows
"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P (dynCallClosure init upd cl return c) Q,A"
  apply (rule hoare_complete')
  apply (rule allI)
  apply (rule dynCallClosure_sound [where R=R])
  using adapt
  apply (blast intro: hoare_cnvalid)
  using res
  apply (blast intro: hoare_cnvalid)
  done

lemma in_subsetD: "\<lbrakk>P \<subseteq> P'; x \<in> P\<rbrakk> \<Longrightarrow> x \<in> P'"
  by blast

lemma dynCallClosureFix:
assumes adapt: "P \<subseteq> {s. \<exists>Z. cl'=cl s \<and>   
                  init s \<in> P' Z \<and> 
                  (\<forall>t \<in> Q' Z. return s t \<in> R s t) \<and>
                  (\<forall>t \<in> A' Z. return s t \<in> A)}"
assumes res: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub> (P' Z) (callClosure upd cl') (Q' Z),(A' Z)"
shows
"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P (dynCallClosure init upd cl return c) Q,A"
  apply (rule dynCallClosure [OF _ res])
  using adapt spec
  apply clarsimp
  apply (drule (1) in_subsetD)
  apply clarsimp
  apply (rule_tac x="P' Z" in exI)
  apply (rule_tac x="Q' Z" in exI)
  apply (rule_tac x="A' Z" in exI)
  apply blast
  done


lemma conseq_extract_pre:
             "\<lbrakk>\<forall>s \<in> P. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> ({s}) c Q,A\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  apply (rule hoarep.Conseq)
  apply clarify
  apply (rule_tac x="{s}" in exI)  
  apply (rule_tac x="Q" in exI)  
  apply (rule_tac x="A" in exI)  
  by simp



lemma app_closure_sound:
  assumes adapt: "P \<subseteq> {s. \<exists>P' Q' A'. \<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P' (callClosure upd (e',p)) Q',A' \<and>
                           upd x s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A}"
  assumes ap: "upd e = upd e' \<circ> upd x"     
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P (callClosure upd (e,p)) Q,A"
proof (rule cnvalidI)
  fix s t
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P Call p Q,A"
  assume exec_e: "\<Gamma>\<turnstile> \<langle>callClosure upd (e, p),Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume t: "t \<notin> Fault ` F"
  from P adapt obtain P' Q' A'
    where 
    valid: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub> P' (callClosure upd (e',p)) Q',A'" and
    init_P': "upd x s \<in> P'"  and
    Q: "Q' \<subseteq> Q" and
    A: "A' \<subseteq> A"
    by auto
  from exec_e [simplified callClosure_def] obtain s'
    where
    exec_e: "\<Gamma>\<turnstile> \<langle>Basic (upd (fst (e, p))),Normal s\<rangle> =n\<Rightarrow> s'"and
    exec_p: "\<Gamma>\<turnstile> \<langle>Call (snd (e, p)),s'\<rangle> =n\<Rightarrow> t"
    by cases
  from exec_e [simplified]
  have s': "s'=Normal (upd e s)"
    by cases simp
  from ap obtain s'' where
   s'': "upd x s = s''" and upd_e': "upd e' s''=upd e s" 
    by auto
  from ap s' execn.Basic [where f="(upd (fst (e', p)))" and s="upd x s" and \<Gamma>=\<Gamma>]
  have exec_e': "\<Gamma>\<turnstile> \<langle>Basic (upd (fst (e', p))),Normal (upd x s)\<rangle> =n\<Rightarrow> s'"
    by simp
  with exec_p
  have "\<Gamma>\<turnstile> \<langle>callClosure upd (e', p),Normal (upd x s)\<rangle> =n\<Rightarrow> t"
    by (auto simp add: callClosure_def intro: execn.Seq)
  from cnvalidD [OF valid [rule_format] ctxt this init_P'] t Q A
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
    by auto
qed

lemma app_closure:
  assumes adapt: "P \<subseteq> {s. \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' (callClosure upd (e',p)) Q',A' \<and>
                           upd x s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A}"
  assumes ap: "upd e = upd e' \<circ> upd x"     
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (callClosure upd (e,p)) Q,A"
  apply (rule hoare_complete')
  apply (rule allI)
  apply (rule app_closure_sound [where x=x and e'=e', OF _ ap])
  using adapt
  apply (blast intro: hoare_cnvalid)
  done

lemma app_closure_spec:
  assumes adapt: "P \<subseteq> {s. \<exists>Z. upd x s \<in> P' Z \<and> Q' Z \<subseteq> Q \<and> A' Z \<subseteq> A}"
  assumes ap: "upd e = upd e' \<circ> upd x"     
  assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P' Z) (callClosure upd (e',p)) (Q' Z),(A' Z)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (callClosure upd (e,p)) Q,A"
  apply (rule app_closure [OF _ ap])
  apply clarsimp
  using adapt spec
  apply -
  apply (drule (1) in_subsetD)
  apply clarsimp
  apply (rule_tac x="P' Z" in exI)
  apply (rule_tac x="Q' Z" in exI)
  apply (rule_tac x="A' Z" in exI)
  apply blast
  done

text {* Implementation of closures as association lists. *}

definition "gen_upd var es s = foldl (\<lambda>s (x,i). the (var x) i s) s es"
definition "ap es c \<equiv> (es@fst c,snd c)"

lemma gen_upd_app: "\<And>es'. gen_upd var (es@es') = gen_upd var es' \<circ> gen_upd var es"
  apply (induct es)
  apply  (rule ext)
  apply  (simp add: gen_upd_def)
  apply (rule ext)
  apply (simp add: gen_upd_def)
  done

lemma gen_upd_ap:
  "gen_upd var (fst (ap es (es',p))) = gen_upd var es' \<circ> gen_upd var es"
  by (simp add: gen_upd_app ap_def)

lemma ap_closure:
  assumes adapt: "P \<subseteq> {s. \<exists>P' Q' A'. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P' (callClosure (gen_upd var) c) Q',A' \<and>
                           gen_upd var es s \<in> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (callClosure (gen_upd var) (ap es c)) Q,A"
proof -
  obtain es' p where c: "c=(es',p)"
    by (cases c) 
  have "gen_upd var (fst (ap es (es',p))) = gen_upd var es' \<circ> gen_upd var es"
    by (simp add: gen_upd_ap)
  from app_closure [OF adapt [simplified c] this]
  show ?thesis
    by (simp add: c ap_def)
qed


lemma ap_closure_spec:
  assumes adapt: "P \<subseteq> {s. \<exists>Z. gen_upd var es s \<in> P' Z \<and> Q' Z \<subseteq> Q \<and> A' Z \<subseteq> A}"
  assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P' Z) (callClosure (gen_upd var) c) (Q' Z),(A' Z)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P (callClosure (gen_upd var) (ap es c)) Q,A"
proof -
  obtain es' p where c: "c=(es',p)"
    by (cases c) 
  have "gen_upd var (fst (ap es (es',p))) = gen_upd var es' \<circ> gen_upd var es"
    by (simp add: gen_upd_ap)
  from app_closure_spec [OF adapt [simplified c] this spec [simplified c]]
  show ?thesis
    by (simp add: c ap_def)
qed

end