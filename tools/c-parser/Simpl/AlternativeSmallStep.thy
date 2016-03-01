(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      AlternativeSmallStep.thy
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

section  {* Alternative Small Step Semantics *}

theory AlternativeSmallStep imports HoareTotalDef
begin


text {* 
This is the small-step semantics, which is described and used in my PhD-thesis \cite{Schirmer-PhD}. 
It decomposes the statement into a list of statements and finally executes the head.
So the redex is always the head of the list. The equivalence between termination
(based on the big-step semantics) and the absence of infinite computations in
this small-step semantics follows the same lines of reasoning as for
the new small-step semantics. However, it is technically more involved since
the configurations are more complicated. Thats why I switched to the new small-step
semantics in the "main trunk". I keep this alternative version and the important
proofs in this theory, so that one can compare both approaches.
*}


subsection {*Small-Step Computation: @{text "\<Gamma>\<turnstile>(cs, css, s) \<rightarrow> (cs', css', s')"}*}

type_synonym ('s,'p,'f) continuation = "('s,'p,'f) com list \<times> ('s,'p,'f) com list"
 
type_synonym ('s,'p,'f) config =
  "('s,'p,'f)com list \<times> ('s,'p,'f)continuation list \<times> ('s,'f) xstate"



inductive "step"::"[('s,'p,'f) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>/ _)" [81,81,81] 100)
  for \<Gamma>::"('s,'p,'f) body"
where
  Skip: "\<Gamma>\<turnstile>(Skip#cs,css,Normal s) \<rightarrow> (cs,css,Normal s)"
| Guard: "s\<in>g \<Longrightarrow> \<Gamma>\<turnstile>(Guard f g c#cs,css,Normal s) \<rightarrow> (c#cs,css,Normal s)"
  
| GuardFault: "s\<notin>g \<Longrightarrow> \<Gamma>\<turnstile>(Guard f g c#cs,css,Normal s) \<rightarrow> (cs,css,Fault f)"

| FaultProp: "\<Gamma>\<turnstile>(c#cs,css,Fault f) \<rightarrow> (cs,css,Fault f)" 
| FaultPropBlock: "\<Gamma>\<turnstile>([],(nrms,abrs)#css,Fault f) \<rightarrow> (nrms,css,Fault f)"
  (* FaultPropBlock: "\<Gamma>\<turnstile>([],cs#css,Fault) \<rightarrow> ([],css,Fault)"*)
    
| AbruptProp:  "\<Gamma>\<turnstile>(c#cs,css,Abrupt s) \<rightarrow> (cs,css,Abrupt s)"
 
| ExitBlockNormal: 
    "\<Gamma>\<turnstile>([],(nrms,abrs)#css,Normal s) \<rightarrow> (nrms,css,Normal s)"
| ExitBlockAbrupt: 
    "\<Gamma>\<turnstile>([],(nrms,abrs)#css,Abrupt s) \<rightarrow> (abrs,css,Normal s)"

| Basic: "\<Gamma>\<turnstile>(Basic f#cs,css,Normal s) \<rightarrow> (cs,css,Normal (f s))"

| Spec: "(s,t) \<in> r \<Longrightarrow> \<Gamma>\<turnstile>(Spec r#cs,css,Normal s) \<rightarrow> (cs,css,Normal t)"
| SpecStuck: "\<forall>t. (s,t) \<notin> r \<Longrightarrow> \<Gamma>\<turnstile>(Spec r#cs,css,Normal s) \<rightarrow> (cs,css,Stuck)"

| Seq: "\<Gamma>\<turnstile>(Seq c\<^sub>1 c\<^sub>2#cs,css,Normal s) \<rightarrow> (c\<^sub>1#c\<^sub>2#cs,css,Normal s)"

| CondTrue:  "s\<in>b \<Longrightarrow> \<Gamma>\<turnstile>(Cond b c\<^sub>1 c\<^sub>2#cs,css,Normal s) \<rightarrow> (c\<^sub>1#cs,css,Normal s)"
| CondFalse: "s\<notin>b \<Longrightarrow> \<Gamma>\<turnstile>(Cond b c\<^sub>1 c\<^sub>2#cs,css,Normal s) \<rightarrow> (c\<^sub>2#cs,css,Normal s)"

| WhileTrue: "\<lbrakk>s\<in>b\<rbrakk> 
              \<Longrightarrow> 
   \<Gamma>\<turnstile>(While b c#cs,css,Normal s) \<rightarrow> (c#While b c#cs,css,Normal s)"
| WhileFalse: "\<lbrakk>s\<notin>b\<rbrakk> 
               \<Longrightarrow> 
               \<Gamma>\<turnstile>(While b c#cs,css,Normal s) \<rightarrow> (cs,css,Normal s)"

| Call: "\<Gamma> p=Some bdy \<Longrightarrow>
         \<Gamma>\<turnstile>(Call p#cs,css,Normal s) \<rightarrow> ([bdy],(cs,Throw#cs)#css,Normal s)"

| CallUndefined: "\<Gamma> p=None \<Longrightarrow>
         \<Gamma>\<turnstile>(Call p#cs,css,Normal s) \<rightarrow> (cs,css,Stuck)"

| StuckProp: "\<Gamma>\<turnstile>(c#cs,css,Stuck) \<rightarrow> (cs,css,Stuck)" 
| StuckPropBlock: "\<Gamma>\<turnstile>([],(nrms,abrs)#css,Stuck) \<rightarrow> (nrms,css,Stuck)"

| DynCom: "\<Gamma>\<turnstile>(DynCom c#cs,css,Normal s) \<rightarrow> (c s#cs,css,Normal s)"

| Throw: "\<Gamma>\<turnstile>(Throw#cs,css,Normal s) \<rightarrow> (cs,css,Abrupt s)"
| Catch: "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2#cs,css,Normal s) \<rightarrow> ([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal s)"

lemmas step_induct = step.induct [of _ "(c,css,s)" "(c',css',s')", split_format (complete), 
case_names
Skip Guard GuardFault FaultProp FaultPropBlock AbruptProp ExitBlockNormal ExitBlockAbrupt
Basic Spec SpecStuck Seq CondTrue CondFalse WhileTrue WhileFalse Call CallUndefined
StuckProp StuckPropBlock DynCom Throw Catch, induct set]

inductive_cases step_elim_cases [cases set]:
 "\<Gamma>\<turnstile>(c#cs,css,Fault f) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],css,Fault f) \<rightarrow> u"
 "\<Gamma>\<turnstile>(c#cs,css,Stuck) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],css,Stuck) \<rightarrow> u"
 "\<Gamma>\<turnstile>(c#cs,css,Abrupt s) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],css,Abrupt s) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Skip#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Guard f g c#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Basic f#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Spec r#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Seq c1 c2#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Cond b c1 c2#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(While b c#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Call p#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(DynCom c#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Throw#cs,css,s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Catch c1 c2#cs,css,s) \<rightarrow> u"

inductive_cases step_Normal_elim_cases [cases set]:
 "\<Gamma>\<turnstile>(c#cs,css,Fault f) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],css,Fault f) \<rightarrow> u"
 "\<Gamma>\<turnstile>(c#cs,css,Stuck) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],css,Stuck) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],(nrms,abrs)#css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>([],(nrms,abrs)#css,Abrupt s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Skip#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Guard f g c#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Basic f#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Spec r#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Seq c1 c2#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Cond b c1 c2#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(While b c#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Call p#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(DynCom c#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Throw#cs,css,Normal s) \<rightarrow> u"
 "\<Gamma>\<turnstile>(Catch c1 c2#cs,css,Normal s) \<rightarrow> u"

abbreviation
 "step_rtrancl" :: "[('s,'p,'f) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
  where
  "\<Gamma>\<turnstile>cs0 \<rightarrow>\<^sup>* cs1     == (step \<Gamma>)\<^sup>*\<^sup>* cs0 cs1"

abbreviation

 "step_trancl" :: "[('s,'p,'f) body,('s,'p,'f) config,('s,'p,'f) config] \<Rightarrow> bool"
                                ("_\<turnstile> (_ \<rightarrow>\<^sup>+/ _)" [81,81,81] 100)
  where
  "\<Gamma>\<turnstile>cs0 \<rightarrow>\<^sup>+ cs1     == (step \<Gamma>)\<^sup>+\<^sup>+ cs0 cs1"


subsubsection {* Structural Properties of Small Step Computations *}

lemma Fault_app_steps: "\<Gamma>\<turnstile>(cs@xs,css,Fault f) \<rightarrow>\<^sup>* (xs,css,Fault f)"
proof (induct cs)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  have "\<Gamma>\<turnstile>(c#cs@xs, css, Fault f) \<rightarrow>\<^sup>* (xs, css, Fault f)"
  proof -
    have "\<Gamma>\<turnstile>(c#cs@xs, css, Fault f) \<rightarrow> (cs@xs, css, Fault f)"
      by (rule step.FaultProp)
    also 
    have "\<Gamma>\<turnstile>(cs@xs, css, Fault f) \<rightarrow>\<^sup>* (xs, css, Fault f)"
      by (rule Cons.hyps)
    finally show ?thesis .
  qed
  thus ?case
    by simp
qed

lemma Stuck_app_steps: "\<Gamma>\<turnstile>(cs@xs,css,Stuck) \<rightarrow>\<^sup>* (xs,css,Stuck)"
proof (induct cs)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  have "\<Gamma>\<turnstile>(c#cs@xs, css, Stuck) \<rightarrow>\<^sup>* (xs, css, Stuck)"
  proof -
    have "\<Gamma>\<turnstile>(c#cs@xs, css, Stuck) \<rightarrow> (cs@xs, css, Stuck)"
      by (rule step.StuckProp)
    also 
    have "\<Gamma>\<turnstile>(cs@xs, css, Stuck) \<rightarrow>\<^sup>* (xs, css, Stuck)"
      by (rule Cons.hyps)
    finally show ?thesis .
  qed
  thus ?case
    by simp
qed

text {* We can only append commands inside a block, if execution does not
        enter or exit a block.
      *}
lemma app_step:  
  assumes step: "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow> (cs',css',t)"
  shows "css=css' \<Longrightarrow> \<Gamma>\<turnstile>(cs@xs,css,s) \<rightarrow> (cs'@xs,css',t)"
using step
apply induct
apply (simp_all del: fun_upd_apply,(blast intro: step.intros)+)
done

text {* We can append whole blocks, without interfering with the actual
        block. Outer blocks do not influence execution of
        inner blocks. *}
lemma app_css_step:  
  assumes step: "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow> (cs',css',t)"
  shows "\<Gamma>\<turnstile>(cs,css@xs,s) \<rightarrow> (cs',css'@xs,t)"
using step
apply induct
apply (simp_all del: fun_upd_apply,(blast intro: step.intros)+)
done

ML {*
  ML_Thms.bind_thm ("trancl_induct3", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(ax, ay, az)"),
       ((("b", 0), Position.none), "(bx, by, bz)")] []
      @{thm tranclp_induct}));
*}

lemma app_css_steps:  
  assumes step: "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow>\<^sup>+ (cs',css',t)"
  shows "\<Gamma>\<turnstile>(cs,css@xs,s) \<rightarrow>\<^sup>+ (cs',css'@xs,t)"
apply(rule trancl_induct3 [OF step])
 apply (rule app_css_step [THEN tranclp.r_into_trancl [of "step \<Gamma>"]],assumption)
apply(blast intro:app_css_step tranclp_trans)
done

lemma step_Cons':  
  assumes step: "\<Gamma>\<turnstile>(ccs,css,s) \<rightarrow> (cs',css',t)"
  shows
  "\<And>c cs. ccs=c#cs \<Longrightarrow> \<exists>css''. css'=css''@css \<and>
      (if css''=[] then \<exists>p. cs'=p@cs
       else (\<exists>pnorm pabr. css''=[(pnorm@cs,pabr@cs)]))"
using step
by induct force+

lemma step_Cons:  
  assumes step: "\<Gamma>\<turnstile>(c#cs,css,s) \<rightarrow> (cs',css',t)"
  shows "\<exists>pcss. css'=pcss@css \<and>
         (if pcss=[] then \<exists>ps. cs'=ps@cs
          else (\<exists>pcs_normal pcs_abrupt. pcss=[(pcs_normal@cs,pcs_abrupt@cs)]))"
using step_Cons' [OF step]
by blast  


lemma step_Nil':  
  assumes step: "\<Gamma>\<turnstile>(cs,asscss,s) \<rightarrow> (cs',css',t)"
  shows
  "\<And>ass. \<lbrakk>cs=[]; asscss=ass@css; ass\<noteq>Nil\<rbrakk> \<Longrightarrow> 
          css'=tl ass@css \<and>
          (case s of 
             Abrupt s' \<Rightarrow> cs'=snd (hd ass) \<and> t=Normal s'
           |  _ \<Rightarrow> cs'=fst (hd ass) \<and> t=s)"
using step
by (induct) (fastforce simp add: neq_Nil_conv)+

lemma step_Nil:  
  assumes step: "\<Gamma>\<turnstile>([],ass@css,s) \<rightarrow> (cs',css',t)"
  assumes ass_not_Nil: "ass\<noteq>[]"
  shows "css'=tl ass@css \<and>
          (case s of 
             Abrupt s' \<Rightarrow> cs'=snd (hd ass) \<and> t=Normal s'
           |  _ \<Rightarrow> cs'=fst (hd ass) \<and> t=s)"
  using step_Nil' [OF step _ _ ass_not_Nil]
  by simp

lemma step_Nil'':  
  assumes step: "\<Gamma>\<turnstile>([],(pcs_normal,pcs_abrupt)#pcss@css,s) \<rightarrow> (cs',pcss@css,t)"
  shows "(case s of 
             Abrupt s' \<Rightarrow> cs'=pcs_abrupt \<and> t=Normal s'
           |  _ \<Rightarrow> cs'=pcs_normal \<and> t=s)"
  using step_Nil' [OF step, where ass ="(pcs_normal,pcs_abrupt)#pcss" and css="css"]
  by (auto split: xstate.splits)

lemma drop_suffix_css_step':
assumes step: "\<Gamma>\<turnstile>(cs,cssxs,s) \<rightarrow> (cs',css'xs,t)"
shows "\<And>css css' xs. \<lbrakk>cssxs = css@xs; css'xs=css'@xs\<rbrakk> 
     \<Longrightarrow> \<Gamma>\<turnstile>(cs,css,s) \<rightarrow> (cs',css',t)"
using step
apply induct
apply (fastforce intro: step.intros)+
done

lemma drop_suffix_css_step:
assumes step: "\<Gamma>\<turnstile>(cs,pcss@css,s) \<rightarrow> (cs',pcss'@css,t)"
shows "\<Gamma>\<turnstile>(cs,pcss,s) \<rightarrow> (cs',pcss',t)"
using step by (blast intro: drop_suffix_css_step')

lemma drop_suffix_hd_css_step': 
  assumes step: "\<Gamma>\<turnstile> (pcs,css,s) \<rightarrow> (cs',css'css,t)"
  shows "\<And>p ps cs pnorm pabr. \<lbrakk>pcs=p#ps@cs; css'css=(pnorm@cs,pabr@cs)#css\<rbrakk> 
         \<Longrightarrow> \<Gamma>\<turnstile> (p#ps,css,s) \<rightarrow> (cs',(pnorm,pabr)#css,t)"
using step
by induct (force intro: step.intros)+

lemma drop_suffix_hd_css_step'': 
  assumes step: "\<Gamma>\<turnstile> (p#ps@cs,css,s) \<rightarrow> (cs',(pnorm@cs,pabr@cs)#css,t)"
  shows  "\<Gamma>\<turnstile> (p#ps,css,s) \<rightarrow> (cs',(pnorm,pabr)#css,t)"
using drop_suffix_hd_css_step' [OF step]
by auto

lemma drop_suffix_hd_css_step: 
  assumes step: "\<Gamma>\<turnstile> (p#ps@cs,css,s) \<rightarrow> (cs',[(pnorm@ps@cs,pabr@ps@cs)]@css,t)"
  shows  "\<Gamma>\<turnstile> (p#ps,css,s) \<rightarrow> (cs',[(pnorm@ps,pabr@ps)]@css,t)"
proof -
  from step drop_suffix_hd_css_step'' [of _ p ps cs css s cs' "pnorm@ps" "pabr@ps" t]
  show ?thesis
    by auto
qed

lemma drop_suffix':  
  assumes step: "\<Gamma>\<turnstile>(csxs,css,s) \<rightarrow> (cs'xs,css',t)"
  shows "\<And>xs cs cs'. \<lbrakk>css=css'; csxs=cs@xs; cs'xs = cs'@xs; cs\<noteq>[] \<rbrakk> 
         \<Longrightarrow> \<Gamma>\<turnstile>(cs,css,s) \<rightarrow> (cs',css,t)"
using step
apply induct
apply (fastforce intro: step.intros simp add: neq_Nil_conv)+
done

lemma drop_suffix: 
  assumes step: "\<Gamma>\<turnstile>(c#cs@xs,css,s) \<rightarrow> (cs'@xs,css,t)" 
  shows "\<Gamma>\<turnstile>(c#cs,css,s) \<rightarrow> (cs',css,t)"
  by(rule drop_suffix' [OF step _ _ _]) auto

lemma drop_suffix_same_css_step: 
  assumes step: "\<Gamma>\<turnstile>(cs@xs,css,s) \<rightarrow> (cs'@xs,css,t)" 
  assumes not_Nil: "cs\<noteq>[]"
  shows "\<Gamma>\<turnstile>(cs,xss,s) \<rightarrow> (cs',xss,t)"
proof-
  from drop_suffix' [OF step _ _ _ not_Nil]
  have "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow> (cs',css,t)"
    by auto
  with drop_suffix_css_step [of _ cs "[]" css s cs' "[]" t]
  have "\<Gamma>\<turnstile> (cs, [], s) \<rightarrow> (cs', [], t)"
    by auto
  from app_css_step [OF this]
  show ?thesis
    by auto
qed
 
lemma Cons_change_css_step:
  assumes step: "\<Gamma>\<turnstile> (cs,css,s) \<rightarrow> (cs',css'@css,t)"
  shows "\<Gamma>\<turnstile> (cs,xss,s) \<rightarrow> (cs',css'@xss,t)"
proof -
  from step
    drop_suffix_css_step [where cs=cs and pcss="[]" and css=css and s=s
                             and cs'=cs' and pcss'=css' and t=t]
  have "\<Gamma>\<turnstile> (cs, [], s) \<rightarrow> (cs', css', t)"
    by auto
  from app_css_step [where xs=xss, OF this]
  show ?thesis
    by auto
qed

lemma Nil_change_css_step:
  assumes step: "\<Gamma>\<turnstile>([],ass@css,s) \<rightarrow> (cs',ass'@css,t)"
  assumes ass_not_Nil: "ass\<noteq>[]"
  shows "\<Gamma>\<turnstile>([],ass@xss,s) \<rightarrow> (cs',ass'@xss,t)"
proof -
  from step drop_suffix_css_step [of _ "[]" ass css s cs' ass' t]
  have "\<Gamma>\<turnstile> ([], ass, s) \<rightarrow> (cs', ass', t)"
    by auto
  from app_css_step [where xs=xss, OF this]
  show ?thesis
    by auto
qed

subsubsection {* Equivalence between Big and Small-Step Semantics *}
    
lemma exec_impl_steps:
  assumes exec: "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
  shows "\<And>cs css. \<Gamma>\<turnstile>(c#cs,css,s) \<rightarrow>\<^sup>* (cs,css,t)"
using exec
proof (induct)
  case Skip thus ?case by (blast intro: step.Skip)
next
  case Guard thus ?case by (blast intro: step.Guard rtranclp_trans)
next
  case GuardFault thus ?case by (blast intro: step.GuardFault)
next
  case FaultProp thus ?case by (blast intro: step.FaultProp)
next
  case Basic thus ?case by (blast intro: step.Basic)
next
  case Spec thus ?case by (blast intro: step.Spec)
next
  case SpecStuck thus ?case by (blast intro: step.SpecStuck)
next
  case Seq thus ?case by (blast intro: step.Seq rtranclp_trans)
next
  case CondTrue thus ?case by (blast intro: step.CondTrue rtranclp_trans)
next
  case CondFalse thus ?case by (blast intro: step.CondFalse rtranclp_trans)
next
  case WhileTrue thus ?case by (blast intro: step.WhileTrue rtranclp_trans)
next
  case WhileFalse thus ?case by (blast intro: step.WhileFalse)
next
  case (Call p bdy s s' cs css)
  have bdy: "\<Gamma> p = Some bdy" by fact
  have steps_body: "\<Gamma>\<turnstile>([bdy],(cs,Throw#cs)#css,Normal s) \<rightarrow>\<^sup>* 
                       ([],(cs,Throw#cs)#css, s')" by fact
  show ?case
  proof (cases s')
    case (Normal s'')
    note steps_body
    also from Normal have "\<Gamma>\<turnstile>([],(cs,Throw#cs)#css, s') \<rightarrow> (cs,css,s')"
      by (auto intro: step.intros)
    finally show ?thesis
      using bdy
      by (blast intro: step.Call rtranclp_trans)
  next
    case (Abrupt s'')
    with steps_body 
    have "\<Gamma>\<turnstile>([bdy],(cs,Throw#cs)#css,Normal s) \<rightarrow>\<^sup>* 
             ([],(cs,Throw#cs)#css, Abrupt s'')" by simp
    also have "\<Gamma>\<turnstile>([],(cs,Throw#cs)#css, Abrupt s'') \<rightarrow> (Throw#cs,css,Normal s'')"
      by (rule ExitBlockAbrupt)
    also have "\<Gamma>\<turnstile>(Throw#cs,css,Normal s'') \<rightarrow> (cs,css,Abrupt s'')"
      by (rule Throw)
    finally show ?thesis
      using bdy Abrupt
      by (auto intro: step.Call rtranclp_trans)
  next
    case Fault
    note steps_body
    also from Fault have "\<Gamma>\<turnstile>([],(cs,Throw#cs)#css, s') \<rightarrow> (cs,css,s')"
      by (auto intro: step.intros)
    finally show ?thesis
      using bdy
      by (blast intro: step.Call rtranclp_trans)
  next
    case Stuck
    note steps_body
    also from Stuck have "\<Gamma>\<turnstile>([],(cs,Throw#cs)#css, s') \<rightarrow> (cs,css,s')"
      by (auto intro: step.intros)
    finally show ?thesis
      using bdy
      by (blast intro: step.Call rtranclp_trans)
  qed
next
  case (CallUndefined p s cs css)
  have undef: "\<Gamma> p = None" by fact
  hence "\<Gamma>\<turnstile>(Call p # cs, css, Normal s) \<rightarrow> (cs, css, Stuck)"
    by (rule step.CallUndefined)
  thus ?case ..
next
  case StuckProp thus ?case by (blast intro: step.StuckProp rtrancl_trans)
next
  case DynCom thus ?case by (blast intro: step.DynCom rtranclp_trans)
next
   case Throw thus ?case by (blast intro: step.Throw)
next
  case AbruptProp thus ?case by (blast intro: step.AbruptProp)
next
  case (CatchMatch c\<^sub>1 s s' c\<^sub>2 s'' cs css) 
  have steps_c1: "\<Gamma>\<turnstile>([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal s) \<rightarrow>\<^sup>* 
                    ([],(cs,c\<^sub>2#cs)#css,Abrupt s')" by fact
  also
  have "\<Gamma>\<turnstile>([],(cs,c\<^sub>2#cs)#css,Abrupt s') \<rightarrow> (c\<^sub>2#cs,css,Normal s')"
    by (rule ExitBlockAbrupt)
  also 
  have steps_c2: "\<Gamma>\<turnstile>(c\<^sub>2#cs,css,Normal s') \<rightarrow>\<^sup>* (cs,css,s'')"  by fact
  finally
  show "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2 # cs, css, Normal s) \<rightarrow>\<^sup>* (cs, css, s'')"
    by (blast intro: step.Catch rtranclp_trans)
next
  case (CatchMiss c\<^sub>1 s s' c\<^sub>2 cs css) 
  assume notAbr: "\<not> isAbr s'"
  have steps_c1: "\<Gamma>\<turnstile>([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal s) \<rightarrow>\<^sup>* ([],(cs,c\<^sub>2#cs)#css,s')" by fact
  show "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2 # cs, css, Normal s) \<rightarrow>\<^sup>* (cs, css, s')"
  proof (cases s')
    case (Normal w)
    with steps_c1
    have "\<Gamma>\<turnstile>([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal s) \<rightarrow>\<^sup>* ([],(cs,c\<^sub>2#cs)#css,Normal w)"
      by simp
    also
    have "\<Gamma>\<turnstile>([],(cs,c\<^sub>2#cs)#css,Normal w) \<rightarrow> (cs,css,Normal w)"
      by (rule ExitBlockNormal)
    finally show ?thesis using Normal
      by (auto intro: step.Catch rtranclp_trans)
  next
    case Abrupt with notAbr show ?thesis by simp
  next
    case (Fault f)
    with steps_c1
    have "\<Gamma>\<turnstile>([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal s) \<rightarrow>\<^sup>* ([],(cs,c\<^sub>2#cs)#css,Fault f)"
      by simp
    also
    have "\<Gamma>\<turnstile>([],(cs,c\<^sub>2#cs)#css,Fault f) \<rightarrow> (cs,css,Fault f)"
      by (rule FaultPropBlock)
    finally show ?thesis using Fault
      by (auto intro: step.Catch rtranclp_trans)
  next
    case Stuck
    with steps_c1
    have "\<Gamma>\<turnstile>([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal s) \<rightarrow>\<^sup>* ([],(cs,c\<^sub>2#cs)#css,Stuck)"
      by simp
    also
    have "\<Gamma>\<turnstile>([],(cs,c\<^sub>2#cs)#css,Stuck) \<rightarrow> (cs,css,Stuck)"
      by (rule StuckPropBlock)
    finally show ?thesis using Stuck
      by (auto intro: step.Catch rtranclp_trans)
  qed
qed


inductive "execs"::"[('s,'p,'f) body,('s,'p,'f) com list,
                      ('s,'p,'f) continuation list,
                      ('s,'f) xstate,('s,'f) xstate] \<Rightarrow> bool"
                   ("_\<turnstile> \<langle>_,_,_\<rangle> \<Rightarrow> _" [50,50,50,50,50] 50)
  for \<Gamma>:: "('s,'p,'f) body"
where
  Nil: "\<Gamma>\<turnstile>\<langle>[],[],s\<rangle> \<Rightarrow> s"

| ExitBlockNormal: "\<Gamma>\<turnstile>\<langle>nrms,css,Normal s\<rangle> \<Rightarrow> t
                    \<Longrightarrow>
                    \<Gamma>\<turnstile>\<langle>[],(nrms,abrs)#css,Normal s\<rangle> \<Rightarrow> t"

| ExitBlockAbrupt: "\<Gamma>\<turnstile>\<langle>abrs,css,Normal s\<rangle> \<Rightarrow> t
                    \<Longrightarrow>
                    \<Gamma>\<turnstile>\<langle>[],(nrms,abrs)#css,Abrupt s\<rangle> \<Rightarrow> t"

| ExitBlockFault: "\<Gamma>\<turnstile>\<langle>nrms,css,Fault f\<rangle> \<Rightarrow> t
                    \<Longrightarrow>
                    \<Gamma>\<turnstile>\<langle>[],(nrms,abrs)#css,Fault f\<rangle> \<Rightarrow> t"

| ExitBlockStuck: "\<Gamma>\<turnstile>\<langle>nrms,css,Stuck\<rangle> \<Rightarrow> t
                    \<Longrightarrow>
                    \<Gamma>\<turnstile>\<langle>[],(nrms,abrs)#css,Stuck\<rangle> \<Rightarrow> t"

| Cons: "\<lbrakk>\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t; \<Gamma>\<turnstile>\<langle>cs,css,t\<rangle> \<Rightarrow> u\<rbrakk> 
         \<Longrightarrow> 
         \<Gamma>\<turnstile>\<langle>c#cs,css,s\<rangle> \<Rightarrow> u"


inductive_cases execs_elim_cases [cases set]:
 "\<Gamma>\<turnstile>\<langle>[],css,s\<rangle> \<Rightarrow> t"
 "\<Gamma>\<turnstile>\<langle>c#cs,css,s\<rangle> \<Rightarrow> t"

ML {*
  ML_Thms.bind_thm ("converse_rtrancl_induct3", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(cs, css, s)"),
       ((("b", 0), Position.none), "(cs', css', t)")] []
      @{thm converse_rtranclp_induct}));
*}

lemma execs_Fault_end: 
  assumes execs: "\<Gamma>\<turnstile>\<langle>cs,css,s\<rangle> \<Rightarrow> t" shows "s=Fault f\<Longrightarrow> t=Fault f"
  using execs
  by (induct) (auto dest: Fault_end)

lemma execs_Stuck_end: 
  assumes execs: "\<Gamma>\<turnstile>\<langle>cs,css,s\<rangle> \<Rightarrow> t" shows "s=Stuck \<Longrightarrow> t=Stuck"
  using execs
  by (induct) (auto dest: Stuck_end)


theorem steps_impl_execs: 
  assumes steps: "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow>\<^sup>* ([],[],t)" 
  shows "\<Gamma>\<turnstile>\<langle>cs,css,s\<rangle> \<Rightarrow> t"
using steps
proof (induct rule: converse_rtrancl_induct3 [consumes 1])
  show "\<Gamma>\<turnstile>\<langle>[],[],t\<rangle> \<Rightarrow> t" by (rule execs.Nil)
next
  fix cs css s cs' css' w
  assume step: "\<Gamma>\<turnstile>(cs,css, s) \<rightarrow> (cs',css', w)" 
  assume execs: "\<Gamma>\<turnstile>\<langle>cs',css',w\<rangle> \<Rightarrow> t"
  from step 
  show "\<Gamma>\<turnstile>\<langle>cs,css,s\<rangle> \<Rightarrow> t"
  proof (cases)
    case (Catch c1 c2 cs s)
    with execs obtain t' where
      exec_c1: "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> t'" and
      execs_rest: "\<Gamma>\<turnstile>\<langle>[],(cs, c2 # cs) # css,t'\<rangle> \<Rightarrow> t"
      by (clarsimp elim!: execs_elim_cases)
    have  "\<Gamma>\<turnstile>\<langle>Catch c1 c2 # cs,css,Normal s\<rangle> \<Rightarrow> t"
    proof (cases t')
      case (Normal t'')
      with exec_c1 have "\<Gamma>\<turnstile>\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow> t'"
        by (auto intro: exec.CatchMiss)
      moreover
      from execs_rest Normal have "\<Gamma>\<turnstile>\<langle>cs,css,t'\<rangle> \<Rightarrow> t"
        by (cases) auto
      ultimately show ?thesis
        by (rule execs.Cons)
    next
      case (Abrupt t'')
      from execs_rest Abrupt have "\<Gamma>\<turnstile>\<langle>c2#cs,css,Normal t''\<rangle> \<Rightarrow> t"
        by (cases) auto
      then obtain v where
          exec_c2: "\<Gamma>\<turnstile>\<langle>c2,Normal t''\<rangle> \<Rightarrow> v" and
          rest: "\<Gamma>\<turnstile>\<langle>cs,css,v\<rangle> \<Rightarrow> t"
        by cases
      from exec_c1 Abrupt exec_c2
      have "\<Gamma>\<turnstile>\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow> v"
        by  - (rule exec.CatchMatch, auto)
      from this rest
      show ?thesis
        by (rule execs.Cons)
    next
      case (Fault f)
      with exec_c1 have "\<Gamma>\<turnstile>\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow> Fault f"
        by (auto intro: exec.intros)
      moreover from execs_rest Fault have "\<Gamma>\<turnstile>\<langle>cs,css,Fault f\<rangle> \<Rightarrow> t"
        by (cases) auto
      ultimately show ?thesis
        by (rule execs.Cons)
    next
      case Stuck
      with exec_c1 have "\<Gamma>\<turnstile>\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow> Stuck"
        by (auto intro: exec.intros)
      moreover from execs_rest Stuck have "\<Gamma>\<turnstile>\<langle>cs,css,Stuck\<rangle> \<Rightarrow> t"
        by (cases) auto
      ultimately show ?thesis
        by (rule execs.Cons)
    qed
    with Catch show ?thesis by simp
  next
    case (Call p bdy cs s)
    have bdy: "\<Gamma> p = Some bdy" by fact
    from Call execs obtain t' where
      exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal s\<rangle> \<Rightarrow> t'" and
      execs_rest: 
            "\<Gamma>\<turnstile>\<langle>[],(cs,Throw#cs)#css ,t'\<rangle> \<Rightarrow> t"
       by (clarsimp elim!: execs_elim_cases)
    have "\<Gamma>\<turnstile>\<langle>Call p # cs,css,Normal s\<rangle> \<Rightarrow> t"
    proof (cases t')
      case (Normal t'')
      with exec_body bdy
      have "\<Gamma>\<turnstile>\<langle>Call p ,Normal s\<rangle> \<Rightarrow> Normal t''" 
        by (auto intro: exec.intros)
      moreover
      from execs_rest Normal
      have "\<Gamma>\<turnstile>\<langle>cs,css ,Normal t''\<rangle> \<Rightarrow> t" 
        by cases auto
      ultimately show ?thesis by (rule execs.Cons)
    next
      case (Abrupt t'')
      with exec_body bdy
      have "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow> Abrupt t''"
        by (auto intro: exec.intros)
      moreover
      from execs_rest Abrupt have 
        "\<Gamma>\<turnstile>\<langle>Throw # cs,css,Normal t''\<rangle> \<Rightarrow> t"
        by (cases) auto
      then obtain v where 
        "\<Gamma>\<turnstile>\<langle>Throw,Normal t''\<rangle> \<Rightarrow> v" and 
        rest: "\<Gamma>\<turnstile>\<langle>cs,css,v\<rangle> \<Rightarrow> t"
        by (clarsimp elim!: execs_elim_cases)
      moreover from this have "v=Abrupt t''"
        by (auto elim: exec_Normal_elim_cases)
      ultimately 
      show ?thesis by (auto intro: execs.Cons)
    next
      case (Fault f)
      with exec_body bdy have "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow> Fault f"
        by (auto intro: exec.intros)
      moreover from execs_rest Fault have "\<Gamma>\<turnstile>\<langle>cs,css,Fault f\<rangle> \<Rightarrow> t"
        by (cases) (auto elim: execs_elim_cases dest: Fault_end)
      ultimately 
      show ?thesis by (rule execs.Cons)
    next
      case Stuck
      with exec_body bdy have "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow> Stuck"
        by (auto intro: exec.intros)
      moreover from execs_rest Stuck have "\<Gamma>\<turnstile>\<langle>cs,css,Stuck\<rangle> \<Rightarrow> t"
        by (cases) (auto elim: execs_elim_cases dest: Stuck_end)
      ultimately 
      show ?thesis by (rule execs.Cons)
    qed 
    with Call show ?thesis by simp
  qed (insert execs,
      (blast intro:execs.intros exec.intros elim!: execs_elim_cases)+)
qed

theorem steps_impl_exec: 
  assumes steps: "\<Gamma>\<turnstile>([c],[],s) \<rightarrow>\<^sup>* ([],[],t)" 
  shows "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
using steps_impl_execs [OF steps]
by (blast elim: execs_elim_cases)

corollary steps_eq_exec: "\<Gamma>\<turnstile>([c],[],s) \<rightarrow>\<^sup>* ([],[],t) = \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
  by (blast intro: steps_impl_exec exec_impl_steps)


subsection {* Infinite Computations: @{text "inf \<Gamma> cs css s"}*}

definition inf :: 
 "[('s,'p,'f) body,('s,'p,'f) com list,('s,'p,'f) continuation list,('s,'f) xstate]
  \<Rightarrow> bool"
where "inf \<Gamma> cs css s = (\<exists>f. f 0 = (cs,css,s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f(Suc i)))"

lemma not_infI: "\<lbrakk>\<And>f. \<lbrakk>f 0 = (cs,css,s); \<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)\<rbrakk> \<Longrightarrow> False\<rbrakk>  
                \<Longrightarrow> \<not>inf \<Gamma> cs css s"
  by (auto simp add: inf_def)

subsection {* Equivalence of Termination and Absence of Infinite Computations *}


inductive "terminatess":: "[('s,'p,'f) body,('s,'p,'f) com list,
                            ('s,'p,'f) continuation list,('s,'f) xstate] \<Rightarrow> bool" 
                ("_\<turnstile>_,_ \<Down> _" [60,20,60] 89)
  for  \<Gamma>::"('s,'p,'f) body"
where
   Nil: "\<Gamma>\<turnstile>[],[]\<Down>s"

|  ExitBlockNormal: "\<Gamma>\<turnstile>nrms,css\<Down>Normal s
                     \<Longrightarrow> 
                     \<Gamma>\<turnstile>[],(nrms,abrs)#css\<Down>Normal s"

|  ExitBlockAbrupt: "\<Gamma>\<turnstile>abrs,css\<Down>Normal s
                     \<Longrightarrow> 
                     \<Gamma>\<turnstile>[],(nrms,abrs)#css\<Down>Abrupt s"

|  ExitBlockFault: "\<Gamma>\<turnstile>nrms,css\<Down>Fault f
                    \<Longrightarrow> 
                    \<Gamma>\<turnstile>[],(nrms,abrs)#css\<Down>Fault f"

|  ExitBlockStuck: "\<Gamma>\<turnstile>nrms,css\<Down>Stuck
                    \<Longrightarrow> 
                    \<Gamma>\<turnstile>[],(nrms,abrs)#css\<Down>Stuck"


|  Cons: "\<lbrakk>\<Gamma>\<turnstile>c\<down>s; (\<forall>t. \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>cs,css\<Down>t)\<rbrakk>
          \<Longrightarrow> 
          \<Gamma>\<turnstile>c#cs,css\<Down>s"
 
inductive_cases terminatess_elim_cases [cases set]:
 "\<Gamma>\<turnstile>[],css\<Down>t"
 "\<Gamma>\<turnstile>c#cs,css\<Down>t"

lemma terminatess_Fault: "\<And>cs. \<Gamma>\<turnstile>cs,css\<Down>Fault f"
proof (induct css)
  case Nil
  show "\<Gamma>\<turnstile>cs,[]\<Down>Fault f"
  proof (induct cs)
    case Nil show "\<Gamma>\<turnstile>[],[]\<Down>Fault f" by (rule terminatess.Nil)
  next
    case (Cons c cs)
    thus ?case
      by (auto intro: terminatess.intros terminates.intros dest: Fault_end)
  qed
next
  case (Cons d css)
  have hyp: "\<And>cs. \<Gamma>\<turnstile>cs,css\<Down>Fault f" by fact
  obtain nrms abrs where d: "d=(nrms,abrs)"  by (cases d) auto
  have "\<Gamma>\<turnstile>cs,(nrms,abrs)#css\<Down>Fault f"
  proof (induct cs)
    case Nil
    show "\<Gamma>\<turnstile>[],(nrms, abrs) # css\<Down>Fault f"
      by (rule terminatess.ExitBlockFault) (rule hyp)
  next
    case (Cons c cs)
    have hyp1: "\<Gamma>\<turnstile>cs,(nrms, abrs) # css\<Down>Fault f" by fact
    show "\<Gamma>\<turnstile>c#cs,(nrms, abrs)#css\<Down>Fault f"
      by (auto intro: hyp1 terminatess.Cons terminates.intros dest: Fault_end)
  qed
  with d show ?case by simp
qed

lemma terminatess_Stuck: "\<And>cs. \<Gamma>\<turnstile>cs,css\<Down>Stuck"
proof (induct css)
  case Nil
  show "\<Gamma>\<turnstile>cs,[]\<Down>Stuck"
  proof (induct cs)
    case Nil show "\<Gamma>\<turnstile>[],[]\<Down>Stuck" by (rule terminatess.Nil)
  next
    case (Cons c cs)
    thus ?case
      by (auto intro: terminatess.intros terminates.intros dest: Stuck_end)
  qed
next
  case (Cons d css)
  have hyp: "\<And>cs. \<Gamma>\<turnstile>cs,css\<Down>Stuck" by fact
  obtain nrms abrs where d: "d=(nrms,abrs)" by (cases d) auto
  have "\<Gamma>\<turnstile>cs,(nrms,abrs)#css\<Down>Stuck"
  proof (induct cs)
    case Nil
    show "\<Gamma>\<turnstile>[],(nrms, abrs) # css\<Down>Stuck"
      by (rule terminatess.ExitBlockStuck) (rule hyp)
  next
    case (Cons c cs)
    have hyp1: "\<Gamma>\<turnstile>cs,(nrms, abrs) # css\<Down>Stuck" by fact
    show "\<Gamma>\<turnstile>c#cs,(nrms, abrs)#css\<Down>Stuck"
      by (auto intro: hyp1 terminatess.Cons terminates.intros dest: Stuck_end)
  qed
  with d show ?case by simp
qed


lemma Basic_terminates: "\<Gamma>\<turnstile>Basic f \<down> t"
  by (cases t) (auto intro: terminates.intros)

lemma step_preserves_terminations: 
  assumes step: "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow> (cs',css',t)" 
  shows "\<Gamma>\<turnstile>cs,css\<Down>s \<Longrightarrow> \<Gamma>\<turnstile>cs',css'\<Down>t"
using step
proof (induct)
  case Skip thus ?case
    by (auto elim: terminates_Normal_elim_cases terminatess_elim_cases
             intro: exec.intros)
next
  case Guard thus ?case 
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
             intro: terminatess.intros terminates.intros exec.intros)
next
  case GuardFault thus ?case
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case FaultProp show ?case by (rule terminatess_Fault)
next
  case FaultPropBlock show ?case by (rule terminatess_Fault)
next
  case AbruptProp thus ?case
    by (blast elim: terminatess_elim_cases 
              intro: terminatess.intros)
next
  case ExitBlockNormal thus ?case
    by (blast elim: terminatess_elim_cases
              intro: terminatess.intros )
next
  case ExitBlockAbrupt thus ?case
    by (blast elim: terminatess_elim_cases
              intro: terminatess.intros )
next
  case Basic thus ?case 
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case Spec thus ?case 
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case SpecStuck thus ?case 
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case Seq thus ?case 
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case CondTrue thus ?case 
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case CondFalse thus ?case 
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case WhileTrue thus ?case
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case WhileFalse thus ?case
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case (Call p bdy cs css s)
  have bdy: "\<Gamma> p = Some bdy" by fact
  from Call obtain 
    term_body: "\<Gamma>\<turnstile>bdy \<down> Normal s" and
    term_rest: "\<forall>t. \<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>cs,css\<Down>t"
    by (fastforce elim!: terminatess_elim_cases terminates_Normal_elim_cases)
  show "\<Gamma>\<turnstile>[bdy],(cs,Throw # cs)#css\<Down>Normal s"
  proof (rule terminatess.Cons [OF term_body],clarsimp)
    fix t
    assume exec_body: "\<Gamma>\<turnstile>\<langle>bdy,Normal s\<rangle> \<Rightarrow> t"
    show "\<Gamma>\<turnstile>[],(cs,Throw # cs) # css\<Down>t"
    proof (cases t)
      case (Normal t')
      with exec_body bdy
      have "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow> Normal t'"
        by (auto intro: exec.intros)
      with term_rest have "\<Gamma>\<turnstile>cs,css\<Down>Normal t'"
        by iprover
      with Normal show ?thesis
        by (auto intro: terminatess.intros terminates.intros
                 elim: exec_Normal_elim_cases)
    next
      case (Abrupt t')
      with exec_body bdy
      have "\<Gamma>\<turnstile>\<langle>Call p,Normal s\<rangle> \<Rightarrow> Abrupt t'"
        by (auto intro: exec.intros)
      with term_rest have "\<Gamma>\<turnstile>cs,css\<Down>Abrupt t'"
        by iprover
      with Abrupt show ?thesis
        by (fastforce intro: terminatess.intros terminates.intros
                     elim: exec_Normal_elim_cases)
    next
      case Fault
      thus ?thesis
        by (iprover intro: terminatess_Fault)
    next
      case Stuck
      thus ?thesis
        by (iprover intro: terminatess_Stuck)
    qed
  qed
next
  case CallUndefined thus ?case
    by (iprover intro: terminatess_Stuck)
next
  case StuckProp show ?case by (rule terminatess_Stuck)
next
  case StuckPropBlock show ?case by (rule terminatess_Stuck)
next
  case DynCom thus ?case
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case Throw thus ?case
    by (blast elim: terminatess_elim_cases terminates_Normal_elim_cases
              intro: terminatess.intros terminates.intros exec.intros)
next
  case (Catch c1 c2 cs css s) 
  then obtain 
    term_c1: "\<Gamma>\<turnstile>c1 \<down> Normal s" and
    term_c2: "\<forall>s'. \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> Abrupt s' \<longrightarrow> \<Gamma>\<turnstile>c2 \<down> Normal s'"and
    term_rest: "\<forall>t. \<Gamma>\<turnstile>\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>cs,css\<Down>t"
    by (clarsimp elim!: terminatess_elim_cases terminates_Normal_elim_cases)
  show "\<Gamma>\<turnstile>[c1],(cs, c2 # cs) # css\<Down>Normal s"
  proof (rule terminatess.Cons [OF term_c1],clarsimp)
    fix t
    assume exec_c1: "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> t" 
    show "\<Gamma>\<turnstile>[],(cs, c2 # cs) # css\<Down>t"
    proof (cases t)
      case (Normal t')
      with exec_c1 have "\<Gamma>\<turnstile>\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow> t" 
        by (auto intro: exec.intros)
      with term_rest have "\<Gamma>\<turnstile>cs,css\<Down>t"
        by iprover
      with Normal show ?thesis
        by (iprover intro: terminatess.intros)
    next
      case (Abrupt t')
      with exec_c1 term_c2 have "\<Gamma>\<turnstile>c2 \<down> Normal t'"
        by auto
      moreover
      {
        fix w
        assume exec_c2: "\<Gamma>\<turnstile>\<langle>c2,Normal t'\<rangle> \<Rightarrow> w" 
        have "\<Gamma>\<turnstile>cs,css\<Down>w" 
        proof -
          from exec_c1 Abrupt exec_c2
          have "\<Gamma>\<turnstile>\<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow> w"
            by (auto intro: exec.intros)
          with term_rest show ?thesis by simp
        qed
      }
      ultimately
      show ?thesis using Abrupt
        by (auto intro: terminatess.intros)
    next
      case Fault thus ?thesis
        by (iprover intro: terminatess_Fault)
    next
      case Stuck thus ?thesis
        by (iprover intro: terminatess_Stuck)
    qed
  qed
qed


ML {*
  ML_Thms.bind_thm ("rtrancl_induct3", Split_Rule.split_rule @{context}
    (Rule_Insts.read_instantiate @{context}
      [((("a", 0), Position.none), "(ax, ay, az)"),
       ((("b", 0), Position.none), "(bx, by, bz)")] []
      @{thm rtranclp_induct}));
*}

lemma steps_preserves_terminations: 
  assumes steps: "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow>\<^sup>* (cs',css',t)" 
  shows "\<Gamma>\<turnstile>cs,css\<Down>s \<Longrightarrow> \<Gamma>\<turnstile>cs',css'\<Down>t"
using steps
proof (induct rule: rtrancl_induct3 [consumes 1])
  assume  "\<Gamma>\<turnstile>cs,css\<Down>s" then show "\<Gamma>\<turnstile>cs,css\<Down>s". 
next
  fix cs'' css'' w cs' css' t
  assume "\<Gamma>\<turnstile>(cs'',css'', w) \<rightarrow> (cs',css', t)" "\<Gamma>\<turnstile>cs,css\<Down>s \<Longrightarrow> \<Gamma>\<turnstile>cs'',css''\<Down>w"
         "\<Gamma>\<turnstile>cs,css\<Down>s"
  then show "\<Gamma>\<turnstile>cs',css'\<Down>t"
    by (blast dest: step_preserves_terminations)
qed

theorem steps_preserves_termination: 
  assumes steps: "\<Gamma>\<turnstile>([c],[],s) \<rightarrow>\<^sup>* (c'#cs',css',t)" 
  assumes term_c: "\<Gamma>\<turnstile>c\<down>s" 
  shows "\<Gamma>\<turnstile>c'\<down>t"
proof -
  from term_c have "\<Gamma>\<turnstile>[c],[]\<Down>s"
    by (auto intro: terminatess.intros)
  from steps this
  have "\<Gamma>\<turnstile>c'#cs',css'\<Down>t"
    by (rule steps_preserves_terminations)
  thus "\<Gamma>\<turnstile>c'\<down>t"
    by (auto elim: terminatess_elim_cases)
qed





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
  by(blast dest:renumber')

lemma not_inf_Fault': 
  assumes enum_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
  shows "\<And>k cs. f k = (cs,css,Fault m) \<Longrightarrow> False"
proof (induct css)
  case Nil
  have f_k: "f k = (cs,[],Fault m)" by fact
  have "\<And>k. f k = (cs,[],Fault m) \<Longrightarrow> False"
  proof (induct cs)
    case Nil 
    have "f k = ([], [], Fault m)" by fact
    moreover
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    ultimately show "False"
      by (fastforce elim: step_elim_cases)
  next
    case (Cons c cs)
    have fk: "f k = (c # cs, [], Fault m)" by fact
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    with fk have "f (Suc k) = (cs,[],Fault m)"
      by (fastforce elim: step_elim_cases)
    with enum_step Cons.hyps
    show False
      by blast
  qed
  from this f_k show False by blast
next
  case (Cons ds css)
  then obtain nrms abrs where ds: "ds=(nrms,abrs)" by (cases ds) auto
  have hyp: "\<And>k cs. f k = (cs,css,Fault m) \<Longrightarrow> False" by fact
  have "\<And>k. f k = (cs,(nrms,abrs)#css,Fault m) \<Longrightarrow> False"
  proof (induct cs)
    case Nil
    have fk: "f k = ([], (nrms, abrs) # css, Fault m)" by fact
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    with fk have "f (Suc k) = (nrms,css,Fault m)"
      by (fastforce elim: step_elim_cases)
    thus ?case
      by (rule hyp)
  next
    case (Cons c cs)
    have fk: "f k = (c#cs, (nrms, abrs) # css, Fault m)" by fact
    have hyp1: "\<And>k. f k = (cs, (nrms, abrs) # css, Fault m) \<Longrightarrow> False" by fact
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    with fk have "f (Suc k) = (cs,(nrms,abrs)#css,Fault m)"
      by (fastforce elim: step_elim_cases)
    thus ?case
      by (rule hyp1)
  qed
  with ds Cons.prems show False by auto
qed

lemma not_inf_Fault:
  "\<not> inf \<Gamma> cs css (Fault m)"
apply (rule not_infI)
apply (rule_tac f=f in not_inf_Fault' )
by auto

lemma not_inf_Stuck': 
  assumes enum_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
  shows "\<And>k cs. f k = (cs,css,Stuck) \<Longrightarrow> False"
proof (induct css)
  case Nil
  have f_k: "f k = (cs,[],Stuck)" by fact
  have "\<And>k. f k = (cs,[],Stuck) \<Longrightarrow> False"
  proof (induct cs)
    case Nil 
    have "f k = ([], [], Stuck)" by fact
    moreover
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    ultimately show "False"
      by (fastforce elim: step_elim_cases)
  next
    case (Cons c cs)
    have fk: "f k = (c # cs, [], Stuck)" by fact
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    with fk have "f (Suc k) = (cs,[],Stuck)"
      by (fastforce elim: step_elim_cases)
    with enum_step Cons.hyps
    show False
      by blast
  qed
  from this f_k show False .
next
  case (Cons ds css)
  then obtain nrms abrs where ds: "ds=(nrms,abrs)" by (cases ds) auto
  have hyp: "\<And>k cs. f k = (cs,css,Stuck) \<Longrightarrow> False" by fact
  have "\<And>k. f k = (cs,(nrms,abrs)#css,Stuck) \<Longrightarrow> False"
  proof (induct cs)
    case Nil
    have fk: "f k = ([], (nrms, abrs) # css, Stuck)" by fact
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    with fk have "f (Suc k) = (nrms,css,Stuck)"
      by (fastforce elim: step_elim_cases)
    thus ?case
      by (rule hyp)
  next
    case (Cons c cs)
    have fk: "f k = (c#cs, (nrms, abrs) # css, Stuck)" by fact
    have hyp1: "\<And>k. f k = (cs, (nrms, abrs) # css, Stuck) \<Longrightarrow> False" by fact
    from enum_step have "\<Gamma>\<turnstile>f k \<rightarrow> f (Suc k)"..
    with fk have "f (Suc k) = (cs,(nrms,abrs)#css,Stuck)"
      by (fastforce elim: step_elim_cases)
    thus ?case
      by (rule hyp1)
  qed
  with ds Cons.prems show False by auto
qed

lemma not_inf_Stuck:
  "\<not> inf \<Gamma> cs css Stuck"
apply (rule not_infI)
apply (rule_tac f=f in not_inf_Stuck')
by auto

lemma last_butlast_app: 
assumes butlast: "butlast as = xs @ butlast bs"
assumes not_Nil: "bs \<noteq> []" "as \<noteq> []"
assumes last: "fst (last as) = fst (last bs)" "snd (last as) = snd (last bs)"
shows "as = xs @ bs"
proof -
  from last have "last as = last bs"
    by (cases "last as",cases "last bs") simp
  moreover
  from not_Nil have "as = butlast as @ [last as]" "bs = butlast bs @ [last bs]"
    by auto
  ultimately show ?thesis
    using butlast
    by simp
qed


lemma last_butlast_tl:
assumes butlast: "butlast bs = x # butlast as" 
assumes not_Nil: "bs \<noteq> []" "as \<noteq> []" 
assumes last: "fst (last as) = fst (last bs)" "snd (last as) = snd (last bs)"
shows "as = tl bs"
proof -
  from last have "last as = last bs"
    by (cases "last as",cases "last bs") simp
  moreover
  from not_Nil have "as = butlast as @ [last as]" "bs = butlast bs @ [last bs]"
    by auto
  ultimately show ?thesis
    using butlast
    by simp
qed

locale inf =
fixes CS:: "('s,'p,'f) config \<Rightarrow> ('s, 'p,'f) com list"
  and CSS:: "('s,'p,'f) config \<Rightarrow> ('s, 'p,'f) continuation list"  
  and S:: "('s,'p,'f) config \<Rightarrow> ('s,'f) xstate"  
  defines CS_def : "CS \<equiv> fst"
  defines CSS_def : "CSS \<equiv> \<lambda>c. fst (snd c)"
  defines S_def: "S \<equiv> \<lambda>c. snd (snd c)"

lemma (in inf) steps_hd_drop_suffix:
assumes f_0: "f 0 = (c#cs,css,s)"
assumes f_step: "\<forall>i. \<Gamma>\<turnstile> f(i) \<rightarrow> f(Suc i)"  
assumes not_finished: "\<forall>i < k. \<not> (CS (f i) = cs \<and> CSS (f i) = css)"
assumes simul: "\<forall>i\<le>k.
        (if pcss i = [] then CSS (f i)=css \<and> CS (f i)=pcs i@cs 
                 else CS (f i)=pcs i \<and> 
                      CSS (f i)= butlast (pcss i)@
                              [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                              css)"
defines "p\<equiv>\<lambda>i. (pcs i, pcss i, S (f i))"
shows "\<forall>i<k. \<Gamma>\<turnstile> p i \<rightarrow> p (Suc i)"
using not_finished simul
proof (induct k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have simul: "\<forall>i\<le>Suc k.
        (if pcss i = [] then CSS (f i)=css \<and> CS (f i)=pcs i@cs 
                 else CS (f i)=pcs i \<and> 
                      CSS (f i)= butlast (pcss i)@
                              [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                              css)" by fact
  have not_finished': "\<forall>i < Suc k. \<not> (CS (f i) = cs \<and> CSS (f i) = css)" by fact
  with simul 
  have not_finished: "\<forall>i<Suc k. \<not> (pcs i = [] \<and> pcss i = [])"
    by (auto simp add: CS_def CSS_def S_def split: split_if_asm)
  show ?case
  proof (clarify)
    fix i
    assume i_le_Suc_k: "i < Suc k"
    show "\<Gamma>\<turnstile> p i \<rightarrow> p (Suc i)"
    proof (cases "i < k")
      case True
      with not_finished' simul Suc.hyps
      show ?thesis
        by auto
    next
      case False
      with i_le_Suc_k
      have eq_i_k: "i=k"
        by simp
      show "\<Gamma>\<turnstile>p i \<rightarrow> p (Suc i)"
      proof -
        obtain cs' css' t' where 
          f_Suc_i: "f (Suc i) = (cs', css', t')"
          by (cases "f (Suc i)")
        obtain cs'' css'' t'' where 
          f_i: "f i = (cs'',css'',t'')"
          by (cases "f i")
        from not_finished eq_i_k 
        have pcs_pcss_not_Nil: "\<not> (pcs i = [] \<and> pcss i = [])"
          by auto
        from simul [rule_format, of i] i_le_Suc_k f_i
        have pcs_pcss_i:
          "if pcss i = [] then css''=css \<and> cs''=pcs i@cs 
           else cs''=pcs i \<and> 
           css''= butlast (pcss i)@
                       [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                       css"
          by (simp add: CS_def CSS_def S_def cong: if_cong)
        from simul [rule_format, of "Suc i"] i_le_Suc_k f_Suc_i 
        have pcs_pcss_Suc_i: 
        "if pcss (Suc i) = [] then css' = css \<and> cs' = pcs (Suc i) @ cs
         else cs' = pcs (Suc i) \<and>
              css' = butlast (pcss (Suc i)) @
               [(fst (last (pcss (Suc i))) @ cs, snd (last (pcss (Suc i))) @ cs)] @ 
               css"
          by (simp add: CS_def CSS_def S_def cong: if_cong)
        show ?thesis
        proof (cases "pcss i = []")
          case True
          note pcss_Nil = this
          with pcs_pcss_i pcs_pcss_not_Nil obtain p ps where
            pcs_i: "pcs i = p#ps" and
            css'': "css''=css" and 
            cs'': "cs''=(p#ps)@cs"
            by (auto simp add: neq_Nil_conv)
          with f_i have "f i = (p#(ps@cs),css,t'')"
            by simp
          with f_Suc_i f_step [rule_format, of i]
          have step_css: "\<Gamma>\<turnstile> (p#(ps@cs),css,t'') \<rightarrow> (cs',css',t')"
            by simp
          from step_Cons' [OF this, of p "ps@cs"]
          obtain css''' where
            css''': "css' = css''' @ css" 
            "if css''' = [] then \<exists>p. cs' = p @ ps @ cs
            else (\<exists>pnorm pabr. css'''=[(pnorm @ ps @ cs,pabr @ ps @ cs)])"
            by auto
          show ?thesis
          proof (cases "css''' = []")
            case True
            with css'''
            obtain p' where 
              css': "css' = css" and
              cs': "cs' = p' @ ps @ cs"
              by auto
                (*from cs' css' f_Suc_i f_i [rule_format, of "Suc k"]
                have p_ps_not_Nil: "p'@ps \<noteq> Nil"
                by auto*)
            from css' cs' step_css 
            have step: "\<Gamma>\<turnstile> (p#(ps@cs),css,t'') \<rightarrow> (p'@ps@cs,css,t')"
              by simp
            hence "\<Gamma>\<turnstile> ((p#ps)@cs,css,t'') \<rightarrow> ((p'@ps)@cs,css,t')"
              by simp
            from drop_suffix_css_step' [OF drop_suffix_same_css_step [OF this], 
              where xs="css" and css="[]" and css'="[]"]
            have  "\<Gamma>\<turnstile> (p#ps,[],t'') \<rightarrow> (p'@ps,[],t')"
              by simp 
            moreover 
            from css' cs' pcs_pcss_Suc_i
            obtain "pcs (Suc i) = p'@ps" and "pcss (Suc i) = []"
              by (simp split: split_if_asm)
            ultimately show ?thesis
              using pcs_i pcss_Nil f_i f_Suc_i
              by (simp add: CS_def CSS_def S_def p_def)
          next
            case False
            with css'''
            obtain pnorm pabr where 
              css': "css'=css'''@css"
              "css'''=[(pnorm @ ps @ cs,pabr @ ps @ cs)]"
              by auto
            with css''' step_css 
            have "\<Gamma>\<turnstile> (p#ps@cs,css,t'') \<rightarrow> (cs',[(pnorm@ps@cs,pabr@ps@cs)]@css,t')"
              by simp
            then 
            have "\<Gamma>\<turnstile>(p#ps, css, t'') \<rightarrow> (cs', [(pnorm@ps, pabr@ps)] @ css, t')" 
              by (rule drop_suffix_hd_css_step)
            from drop_suffix_css_step' [OF this,
              where css="[]" and xs="css" and css'="[(pnorm@ps, pabr@ps)]"]
            have "\<Gamma>\<turnstile> (p#ps,[],t'') \<rightarrow> (cs',[(pnorm@ps, pabr@ps)],t')"
              by simp
            moreover
            from css' pcs_pcss_Suc_i
            obtain "pcs (Suc i) = cs'" "pcss (Suc i) = [(pnorm@ps, pabr@ps)]"
              apply (cases "pcss (Suc i)")
              apply (auto split: split_if_asm)
              done
            ultimately show ?thesis
              using pcs_i pcss_Nil f_i f_Suc_i   
              by (simp add: p_def CS_def CSS_def S_def)
          qed
        next
          case False
          note pcss_i_not_Nil = this
          with pcs_pcss_i obtain
            cs'': "cs''=pcs i" and  
            css'': "css''= butlast (pcss i)@
                            [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                            css"
            by auto
          from f_Suc_i f_i f_step [rule_format, of i]
          have step_i_full: "\<Gamma>\<turnstile> (cs'',css'',t'') \<rightarrow> (cs',css',t')"
            by simp
          show ?thesis
          proof (cases cs'')
            case (Cons c' cs)
            with step_Cons' [OF step_i_full]
            obtain css''' where css': "css' = css'''@css''"
              by auto
            with step_i_full 
            have "\<Gamma>\<turnstile> (cs'',css'',t'') \<rightarrow> (cs',css'''@css'',t')"
              by simp
            from Cons_change_css_step [OF this, where xss="pcss i"] Cons cs''
            have "\<Gamma>\<turnstile> (pcs i, pcss i,t'') \<rightarrow> (cs',css'''@pcss i,t')"
              by simp
            moreover
            from cs'' css'' css' False pcs_pcss_Suc_i
            obtain "pcs (Suc i) = cs'" "pcss (Suc i) = css'''@pcss i"
              apply (auto  split: split_if_asm)
              apply (drule (4) last_butlast_app)
              by simp
            ultimately show ?thesis
              using f_i f_Suc_i
              by (simp add: p_def CS_def CSS_def S_def)
          next
            case Nil
            note cs''_Nil = this
            show ?thesis
            proof (cases "butlast (pcss i)")
              case (Cons bpcs bpcss)
              with cs''_Nil step_i_full css''
              have "\<Gamma>\<turnstile> ([],[hd css'']@tl css'',t'') \<rightarrow> (cs',css',t')"
                by simp
              moreover
              from step_Nil [OF this]
              have css': "css'=tl css''"
                by simp
              ultimately have 
                step_i_full: "\<Gamma>\<turnstile> ([],[hd css'']@tl css'',t'') \<rightarrow> (cs',tl css'',t')"
                by simp
              from css'' Cons pcss_i_not_Nil
              have "hd css'' = hd (pcss i)"
                by (auto simp add: neq_Nil_conv split: split_if_asm)
              with cs'' cs''_Nil
                Nil_change_css_step [where ass="[hd css'']" and
                css="tl css''" and ass'="[]" and 
                xss="tl (pcss i)", simplified, OF step_i_full [simplified]]
              have "\<Gamma>\<turnstile> (pcs i,[hd (pcss i)]@tl (pcss i),t'') \<rightarrow> (cs',tl (pcss i),t')"
                by simp
              with pcss_i_not_Nil 
              have "\<Gamma>\<turnstile> (pcs i,pcss i,t'') \<rightarrow> (cs',tl (pcss i),t')"
                by simp
              moreover
              from css' css'' cs''_Nil Cons pcss_i_not_Nil pcs_pcss_Suc_i
              obtain "pcs (Suc i) = cs'" "pcss (Suc i) = tl (pcss i)" 
                apply (clarsimp  split: split_if_asm)
                apply (drule (4) last_butlast_tl)
                by simp
              ultimately show ?thesis
                using f_i f_Suc_i
                by (simp add: p_def CS_def CSS_def S_def)
            next
              case Nil
              with css'' pcss_i_not_Nil
              obtain pnorm pabr
                where css'': "css''= [(pnorm@cs,pabr@cs)]@css" and
                pcss_i: "pcss i = [(pnorm,pabr)]"
                by (force simp add: neq_Nil_conv split: split_if_asm)
              with cs''_Nil step_i_full
              have "\<Gamma>\<turnstile>([],[(pnorm@cs,pabr@cs)]@css,t'') \<rightarrow> (cs',css',t')"
                by simp
              from step_Nil [OF this]
              obtain 
                css': "css'=css" and
                cs': "(case t'' of
                         Abrupt s' \<Rightarrow> cs' = pabr @ cs \<and> t' = Normal s'
                       | _ \<Rightarrow> cs' = pnorm @ cs \<and> t' = t'')"
                by (simp cong: xstate.case_cong)
              let "?pcs_Suc_i " = "(case t'' of Abrupt s' \<Rightarrow> pabr | _ \<Rightarrow> pnorm)"
              from cs'
              have "\<Gamma>\<turnstile>([],[(pnorm,pabr)],t'') \<rightarrow> (?pcs_Suc_i,[],t')"
                by (auto intro: step.intros split: xstate.splits)
              moreover
              from css'' css' cs' pcss_i pcs_pcss_Suc_i
              obtain "pcs (Suc i) = ?pcs_Suc_i" "pcss (Suc i) = []"
                by (simp split: split_if_asm xstate.splits)
              ultimately
              show ?thesis
                using pcss_i cs'' cs''_Nil f_i f_Suc_i
                by (simp add: p_def CS_def CSS_def S_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma k_steps_to_rtrancl: 
  assumes steps: "\<forall>i<k. \<Gamma>\<turnstile> p i \<rightarrow> p (Suc i)"
  shows "\<Gamma>\<turnstile>p 0\<rightarrow>\<^sup>* p k"
using steps
proof (induct k)
  case 0 thus ?case by auto
next
  case (Suc k)
  have "\<forall>i<Suc k. \<Gamma>\<turnstile> p i \<rightarrow> p (Suc i)" by fact
  then obtain
  step_le_k: "\<forall>i<k. \<Gamma>\<turnstile> p i \<rightarrow> p (Suc i)" and step_k: "\<Gamma>\<turnstile> p k \<rightarrow> p (Suc k)"
    by auto
  from Suc.hyps [OF step_le_k]
  have "\<Gamma>\<turnstile> p 0 \<rightarrow>\<^sup>* p k".
  also note step_k
  finally show ?case .
qed

    

lemma (in inf) steps_hd_drop_suffix_finite:
assumes f_0: "f 0 = (c#cs,css,s)"
assumes f_step: "\<forall>i. \<Gamma>\<turnstile> f(i) \<rightarrow> f(Suc i)"  
assumes not_finished: "\<forall>i < k. \<not> (CS (f i) = cs \<and> CSS (f i) = css)"
assumes simul: "\<forall>i\<le>k.
        (if pcss i = [] then CSS (f i)=css \<and> CS (f i)=pcs i@cs 
                 else CS (f i)=pcs i \<and> 
                      CSS (f i)= butlast (pcss i)@
                              [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                              css)"
shows "\<Gamma>\<turnstile>([c],[],s) \<rightarrow>\<^sup>* (pcs k, pcss k, S (f k))"
proof -
  from steps_hd_drop_suffix [OF f_0 f_step not_finished simul]
  have "\<forall>i<k. \<Gamma>\<turnstile> (pcs i, pcss i, S (f i)) \<rightarrow> 
                  (pcs (Suc i), pcss (Suc i), S (f (Suc i)))".
  from k_steps_to_rtrancl [OF this]
  have "\<Gamma>\<turnstile> (pcs 0, pcss 0, S (f 0)) \<rightarrow>\<^sup>* (pcs k, pcss k, S (f k))".
  moreover from f_0 simul [rule_format, of 0]
  have "(pcs 0, pcss 0, S (f 0)) = ([c],[],s)"
    by (auto split: split_if_asm simp add: CS_def CSS_def S_def)
  ultimately show ?thesis by simp
qed

lemma (in inf) steps_hd_drop_suffix_infinite:
assumes f_0: "f 0 = (c#cs,css,s)"
assumes f_step: "\<forall>i. \<Gamma>\<turnstile> f(i) \<rightarrow> f(Suc i)"  
assumes not_finished: "\<forall>i. \<not> (CS (f i) = cs \<and> CSS (f i) = css)"
(*assumes not_finished: "\<forall>i. \<not> (pcs i = [] \<and> pcss i = [])"*)
assumes simul: "\<forall>i.
        (if pcss i = [] then CSS (f i)=css \<and> CS (f i)=pcs i@cs 
                 else CS (f i)=pcs i \<and> 
                      CSS (f i)= butlast (pcss i)@
                              [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                              css)"
defines "p\<equiv>\<lambda>i. (pcs i, pcss i, S (f i))"
shows "\<Gamma>\<turnstile> p i \<rightarrow> p (Suc i)"
proof -
  from steps_hd_drop_suffix [OF f_0 f_step, of "Suc i" pcss pcs] not_finished simul
  show ?thesis
    by (auto simp add: p_def)
qed

lemma (in inf) steps_hd_progress:
assumes f_0: "f 0 = (c#cs,css,s)"
assumes f_step: "\<forall>i. \<Gamma>\<turnstile> f(i) \<rightarrow> f(Suc i)"
assumes c_unfinished: "\<forall>i < k. \<not> (CS (f i) = cs \<and> CSS (f i) = css)"
shows "\<forall>i \<le> k. (\<exists>pcs pcss. 
          (if pcss = [] then CSS (f i)=css \<and> CS (f i)=pcs@cs 
           else CS (f i)=pcs  \<and> 
                CSS (f i)= butlast pcss@
                           [(fst (last pcss)@cs,(snd (last pcss))@cs)]@
                           css))"
using c_unfinished 
proof (induct k)
  case 0
  with f_0 show ?case
    by (simp add: CSS_def CS_def)
next
  case (Suc k)
  have c_unfinished: "\<forall>i<Suc k. \<not> (CS (f i) = cs \<and> CSS (f i) = css)" by fact
  hence c_unfinished': "\<forall>i< k. \<not> (CS (f i) = cs \<and> CSS (f i) = css)" by simp
  show ?case
  proof (clarify)
    fix i
    assume i_le_Suc_k: "i \<le> Suc k"
    show "\<exists>pcs pcss. 
          (if pcss = [] then CSS (f i)=css \<and> CS (f i)=pcs@cs 
           else CS (f i)=pcs  \<and> 
                CSS (f i)= butlast pcss@
                           [(fst (last pcss)@cs,(snd (last pcss))@cs)]@
                           css)"
    proof (cases "i < Suc k")
      case True
      with Suc.hyps [OF c_unfinished', rule_format, of i] c_unfinished
      show ?thesis
        by auto
    next
      case False
      with i_le_Suc_k have eq_i_Suc_k: "i=Suc k"
        by auto
      obtain cs' css' t' where 
        f_Suc_k: "f (Suc k) = (cs', css', t')"
        by (cases "f (Suc k)")
      obtain cs'' css'' t'' where 
        f_k: "f k = (cs'',css'',t'')"
        by (cases "f k")
      with Suc.hyps [OF c_unfinished',rule_format, of k] 
      obtain pcs pcss where  
        pcs_pcss_k: 
        "if pcss = [] then css'' = css \<and> cs'' = pcs @ cs
         else cs'' = pcs \<and>
              css'' = butlast pcss @ 
                           [(fst (last pcss) @ cs, snd (last pcss) @ cs)] @ 
                           css"
        by (auto simp add: CSS_def CS_def cong: if_cong)
      from c_unfinished [rule_format, of k] f_k pcs_pcss_k
      have pcs_pcss_empty: "\<not> (pcs = [] \<and> pcss = [])" 
        by (auto simp add: CS_def CSS_def S_def split: split_if_asm)
      show ?thesis
      proof (cases "pcss = []")
        case True
        note pcss_Nil = this
        with pcs_pcss_k pcs_pcss_empty obtain p ps where
          pcs_i: "pcs = p#ps" and
          css'': "css''=css" and 
          cs'': "cs''=(p#ps)@cs"
          by (cases "pcs") auto
        with f_k have "f k = (p#(ps@cs),css,t'')"
          by simp 
        with f_Suc_k f_step [rule_format, of k]
        have step_css: "\<Gamma>\<turnstile> (p#(ps@cs),css,t'') \<rightarrow> (cs',css',t')"
          by simp
        from step_Cons' [OF this, of p "ps@cs"]
        obtain css''' where
          css''': "css' = css''' @ css" 
          "if css''' = [] then \<exists>p. cs' = p @ ps @ cs
          else (\<exists>pnorm pabr. css'''=[(pnorm @ ps @ cs,pabr @ ps @ cs)])"
          by auto
        show ?thesis
        proof (cases "css''' = []")
          case True
          with css'''
          obtain p' where 
            css': "css' = css" and
            cs': "cs' = p' @ ps @ cs"
            by auto
          from css' cs' f_Suc_k
          show ?thesis
            apply (rule_tac x="p'@ps" in exI) 
            apply (rule_tac x="[]" in exI)
            apply (simp add: CSS_def CS_def eq_i_Suc_k)
            done
        next
          case False
          with css'''
          obtain pnorm pabr where 
            css': "css'=css'''@css"
            "css'''=[(pnorm @ ps @ cs,pabr @ ps @ cs)]"
            by auto
          with f_Suc_k eq_i_Suc_k
          show ?thesis
            apply (rule_tac x="cs'" in exI)
            apply (rule_tac x="[(pnorm@ps, pabr@ps)]" in exI) 
            by (simp add: CSS_def CS_def)
        qed
      next
        case False
        note pcss_k_not_Nil = this
        with pcs_pcss_k obtain
          cs'': "cs''=pcs" and  
          css'': "css''= butlast pcss@
                           [(fst (last pcss)@cs,(snd (last pcss))@cs)]@
                           css"
          by auto
        from f_Suc_k f_k f_step [rule_format, of k]
        have step_i_full: "\<Gamma>\<turnstile> (cs'',css'',t'') \<rightarrow> (cs',css',t')"
          by simp 
        show ?thesis
        proof (cases cs'')
          case (Cons c' cs)
          with step_Cons' [OF step_i_full]
          obtain css''' where css': "css' = css'''@css''"
            by auto
          with cs'' css'' f_Suc_k eq_i_Suc_k pcss_k_not_Nil
          show ?thesis
            apply (rule_tac x="cs'" in exI)
            apply (rule_tac x="css'''@pcss" in exI)
            by (clarsimp simp add: CSS_def CS_def butlast_append)
        next
          case Nil
          note cs''_Nil = this
          show ?thesis
          proof (cases "butlast pcss")
            case (Cons bpcs bpcss)
            with cs''_Nil step_i_full css''
            have "\<Gamma>\<turnstile> ([],[hd css'']@tl css'',t'') \<rightarrow> (cs',css',t')"
              by simp
            moreover
            from step_Nil [OF this]
            obtain css': "css'=tl css''" and
                   cs': "cs' = (case t'' of Abrupt s' \<Rightarrow> snd (hd css'') 
                                 | _ \<Rightarrow> fst (hd css''))"
              by (auto split: xstate.splits)
            from css'' Cons pcss_k_not_Nil
            have "hd css'' = hd pcss"
              by (auto simp add: neq_Nil_conv split: split_if_asm)
            with css' cs' css'' cs''_Nil Cons pcss_k_not_Nil f_Suc_k eq_i_Suc_k  
            show ?thesis
              apply (rule_tac x="cs'" in exI)
              apply (rule_tac x="tl pcss" in exI)
              apply (clarsimp split: xstate.splits 
                       simp add: CS_def CSS_def neq_Nil_conv split: split_if_asm)
              done
          next
            case Nil
            with css'' pcss_k_not_Nil
            obtain pnorm pabr
              where css'': "css''= [(pnorm@cs,pabr@cs)]@css" and
              pcss_k: "pcss = [(pnorm,pabr)]"
              by (force simp add: neq_Nil_conv split: split_if_asm)
            with cs''_Nil step_i_full
            have "\<Gamma>\<turnstile>([],[(pnorm@cs,pabr@cs)]@css,t'') \<rightarrow> (cs',css',t')"
              by simp
            from step_Nil [OF this]
            obtain 
              css': "css'=css" and
              cs': "(case t'' of
              Abrupt s' \<Rightarrow> cs' = pabr @ cs \<and> t' = Normal s'
              | _ \<Rightarrow> cs' = pnorm @ cs \<and> t' = t'')"
              by (simp cong: xstate.case_cong)
            let "?pcs_Suc_k " = "(case t'' of Abrupt s' \<Rightarrow> pabr | _ \<Rightarrow> pnorm)"
            from css'' css' cs' pcss_k f_Suc_k eq_i_Suc_k
            show ?thesis
              apply (rule_tac x="?pcs_Suc_k" in exI)
              apply (rule_tac x="[]" in exI)
              apply (simp split: xstate.splits add: CS_def CSS_def)
              done
          qed
        qed
      qed
    qed
  qed
qed
  
lemma (in inf) inf_progress:
assumes f_0: "f 0 = (c#cs,css,s)"
assumes f_step: "\<forall>i. \<Gamma>\<turnstile> f(i) \<rightarrow> f(Suc i)"
assumes unfinished: "\<forall>i. \<not> ((CS (f i) = cs) \<and> (CSS (f i) = css))"
shows "\<exists>pcs pcss. 
          (if pcss = [] then CSS (f i)=css \<and> CS (f i)=pcs@cs 
           else CS (f i)=pcs  \<and> 
                CSS (f i)= butlast pcss@
                           [(fst (last pcss)@cs,(snd (last pcss))@cs)]@
                           css)"
proof -
  from steps_hd_progress [OF f_0 f_step, of "i"] unfinished
  show ?thesis
    by auto
qed

lemma skolemize1: "\<forall>x. P x \<longrightarrow> (\<exists>y. Q x y) \<Longrightarrow> \<exists>f.\<forall>x. P x \<longrightarrow> Q x (f x)"
  by (rule choice) blast

lemma skolemize2: "\<forall>x. P x \<longrightarrow> (\<exists>y z. Q x y z) \<Longrightarrow> \<exists>f g.\<forall>x. P x \<longrightarrow> Q x (f x) (g x)"
apply (drule skolemize1)
apply (erule exE)
apply (drule skolemize1)
apply fast
done

lemma skolemize2': "\<forall>x.\<exists>y z. P x y z \<Longrightarrow> \<exists>f g.\<forall>x. P x (f x) (g x)"
apply (drule choice)
apply (erule exE)
apply (drule choice)
apply fast
done

theorem (in inf) inf_cases:
  fixes c::"('s,'p,'f) com"
  assumes inf: "inf \<Gamma> (c#cs) css s" 
  shows "inf \<Gamma> [c] [] s \<or> (\<exists>t. \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t \<and> inf \<Gamma> cs css t)"
proof -
  from inf obtain f where
    f_0: "f 0 = (c#cs,css,s)" and
    f_step: "(\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
    by (auto simp add: inf_def)
  show ?thesis
  proof (cases "\<exists>i. CS (f i) = cs \<and> CSS (f i) = css")
    case True
    def k\<equiv>"(LEAST i. CS (f i) = cs \<and> CSS (f i) = css)"
    from True
    obtain CS_f_k: "CS (f k) = cs" and CSS_f_k: "CSS (f k) = css" 
      apply -
      apply (erule exE)
      apply (drule LeastI)
      apply (simp add: k_def)
      done
    have less_k_prop: "\<forall>i<k. \<not> (CS (f i) = cs \<and> CSS (f i) = css)"
      apply (intro allI impI)
      apply (unfold k_def)
      apply (drule not_less_Least)
      apply simp
      done
    have "\<Gamma>\<turnstile>([c], [], s) \<rightarrow>\<^sup>* ([],[],S (f k))"
    proof -
      have "\<forall>i\<le>k. \<exists>pcs pcss. 
        (if pcss = [] then CSS (f i)=css \<and> CS (f i)=pcs@cs 
           else CS (f i)=pcs  \<and> 
                CSS (f i)= butlast pcss@
                           [(fst (last pcss)@cs,(snd (last pcss))@cs)]@
                           css)"
        by (rule steps_hd_progress 
        [OF f_0 f_step, where k=k, OF less_k_prop])
      from skolemize2 [OF this] obtain pcs pcss where
        pcs_pcss: 
            "\<forall>i\<le>k. 
               (if pcss i = [] then CSS (f i)=css \<and> CS (f i)=pcs i@cs 
                else CS (f i)=pcs i \<and> 
                     CSS (f i)= butlast (pcss i)@
                           [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                           css)"
        by iprover
      from pcs_pcss [rule_format, of k] CS_f_k CSS_f_k 
      have finished: "pcs k = []" "pcss k = []"
        by (auto simp add: CS_def CSS_def S_def split: split_if_asm)
      from pcs_pcss
      have simul: "\<forall>i\<le>k. (if pcss i = [] then CSS (f i)=css \<and> CS (f i)=pcs i@cs 
                   else CS (f i)=pcs i \<and> 
                     CSS (f i)= butlast (pcss i)@
                           [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                            css)"
        by auto
      from steps_hd_drop_suffix_finite [OF f_0 f_step less_k_prop simul] finished
      show ?thesis
        by simp
    qed
    hence "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> S (f k)"
      by (rule steps_impl_exec)
    moreover
    from CS_f_k CSS_f_k f_step
    have "inf \<Gamma> cs css (S (f k))"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (i + k)" in exI)
      apply simp
      apply (auto simp add: CS_def CSS_def S_def)
      done
    ultimately
    have "(\<exists>t. \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t \<and> inf \<Gamma> cs css t)"
      by blast
    thus ?thesis
      by simp
  next
    case False
    hence unfinished: "\<forall>i. \<not> ((CS (f i) = cs) \<and> (CSS (f i) = css))"
      by simp
    from inf_progress [OF f_0 f_step this]
    have "\<forall>i. \<exists>pcs pcss. 
          (if pcss = [] then CSS (f i)=css \<and> CS (f i)=pcs@cs 
           else CS (f i)=pcs  \<and> 
                CSS (f i)= butlast pcss@
                           [(fst (last pcss)@cs,(snd (last pcss))@cs)]@
                           css)"
      by auto
    from skolemize2' [OF this] obtain pcs pcss where 
      pcs_pcss: "\<forall>i. 
          (if pcss i = [] then CSS (f i)=css \<and> CS (f i)=pcs i@cs 
           else CS (f i)=pcs i  \<and> 
                CSS (f i)= butlast (pcss i)@
                           [(fst (last (pcss i))@cs,(snd (last (pcss i)))@cs)]@
                           css)"
      by iprover
    def "g" \<equiv> "\<lambda>i. (pcs i, pcss i, S (f i))"
    from pcs_pcss [rule_format, of 0] f_0
    have "g 0 = ([c],[],s)"
      by (auto split: split_if_asm simp add: CS_def CSS_def S_def g_def)
    moreover
    from steps_hd_drop_suffix_infinite [OF f_0 f_step unfinished pcs_pcss]
    have "\<forall>i. \<Gamma>\<turnstile>g i \<rightarrow> g (Suc i)"
      by (simp add: g_def)
    ultimately
    have "inf \<Gamma> [c] [] s"
      by (auto simp add: inf_def)
    thus ?thesis
      by simp
  qed
qed

lemma infE [consumes 1]:
  assumes inf: "inf \<Gamma> (c#cs) css s" 
  assumes cases: "inf \<Gamma> [c] [] s \<Longrightarrow> P"
                 "\<And>t. \<lbrakk>\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t; inf \<Gamma> cs css t\<rbrakk> \<Longrightarrow> P"
  shows P
using inf cases
apply -
apply (drule inf.inf_cases)
apply auto
done

lemma inf_Seq: 
  "inf \<Gamma> (Seq c1 c2#cs) css (Normal s) = inf \<Gamma> (c1#c2#cs) css (Normal s)" 
proof 
  assume "inf \<Gamma> (Seq c1 c2 # cs) css (Normal s)"
  then obtain f where 
    f_0: "f 0 = (Seq c1 c2#cs,css,Normal s)" and
    f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    by (auto simp add: inf_def)
  from f_step [rule_format, of 0] f_0
  have "f 1 = (c1#c2#cs,css,Normal s)"
    by (auto elim: step_Normal_elim_cases)
  with f_step show "inf \<Gamma> (c1#c2#cs) css (Normal s)"
    apply (simp add: inf_def)
    apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
    apply simp
    done
next
  assume "inf \<Gamma> (c1 # c2 # cs) css (Normal s)"
  then obtain f where 
    f_0: "f 0 = (c1# c2#cs,css,Normal s)" and
    f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    by (auto simp add: inf_def)
  def g\<equiv>"\<lambda>i. case i of 0 \<Rightarrow> (Seq c1 c2#cs,css,Normal s) | Suc j \<Rightarrow> f j" 
  with f_0 have
    "\<Gamma>\<turnstile>g 0 \<rightarrow> g (Suc 0)"
    by (auto intro: step.intros)
  moreover
  from f_step have "\<forall>i. i\<noteq>0 \<longrightarrow> \<Gamma>\<turnstile>g i \<rightarrow> g (Suc i)"
    by (auto simp add: g_def split: nat.splits)
  ultimately
  show "inf \<Gamma> (Seq c1 c2 # cs) css (Normal s)"
    apply (simp add: inf_def)
    apply (rule_tac x=g in exI)
    apply (simp add: g_def split: nat.splits)
    done
qed
 
lemma inf_WhileTrue: 
  assumes b: "s \<in> b"
  shows "inf \<Gamma> (While b c#cs) css (Normal s) = 
          inf \<Gamma> (c#While b c#cs) css (Normal s)" 
proof
  assume "inf \<Gamma> (While b c # cs) css (Normal s)"
  then obtain f where 
    f_0: "f 0 = (While b c#cs,css,Normal s)" and
    f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    by (auto simp add: inf_def)
  from b f_step [rule_format, of 0] f_0
  have "f 1 = (c#While b c#cs,css,Normal s)"
    by (auto elim: step_Normal_elim_cases)
  with f_step show "inf \<Gamma> (c # While b c # cs) css (Normal s)"
    apply (simp add: inf_def)
    apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
    apply simp
    done
next
  assume "inf \<Gamma> (c # While b c # cs) css (Normal s)"
  then obtain f where 
    f_0: "f 0 = (c # While b c #cs,css,Normal s)" and
    f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    by (auto simp add: inf_def)
  def h\<equiv>"\<lambda>i. case i of 0 \<Rightarrow> (While b c#cs,css,Normal s) | Suc j \<Rightarrow> f j" 
  with b f_0 have
    "\<Gamma>\<turnstile>h 0 \<rightarrow> h (Suc 0)"
    by (auto intro: step.intros)
  moreover
  from f_step have "\<forall>i. i\<noteq>0 \<longrightarrow> \<Gamma>\<turnstile>h i \<rightarrow> h (Suc i)"
    by (auto simp add: h_def split: nat.splits)
  ultimately
  show "inf \<Gamma> (While b c # cs) css (Normal s)"
    apply (simp add: inf_def)
    apply (rule_tac x=h in exI)
    apply (simp add: h_def split: nat.splits)
    done
qed

lemma inf_Catch:
"inf \<Gamma> (Catch c1 c2#cs) css (Normal s) = inf \<Gamma> [c1] ((cs,c2#cs)#css) (Normal s)"
proof
  assume "inf \<Gamma> (Catch c1 c2#cs) css (Normal s)"
  then obtain f where 
    f_0: "f 0 = (Catch c1 c2#cs,css,Normal s)" and
    f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    by (auto simp add: inf_def)
  from f_step [rule_format, of 0] f_0
  have "f 1 = ([c1],(cs,c2#cs)#css,Normal s)"
    by (auto elim: step_Normal_elim_cases)
  with f_step show "inf \<Gamma> [c1] ((cs,c2#cs)#css) (Normal s)"
    apply (simp add: inf_def)
    apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
    apply simp
    done
next
  assume "inf \<Gamma> [c1] ((cs,c2#cs)#css) (Normal s)"
  then obtain f where 
    f_0: "f 0 = ([c1],(cs,c2#cs)#css,Normal s)" and
    f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    by (auto simp add: inf_def)
  def h\<equiv>"\<lambda>i. case i of 0 \<Rightarrow> (Catch c1 c2#cs,css,Normal s) | Suc j \<Rightarrow> f j" 
  with f_0 have
    "\<Gamma>\<turnstile>h 0 \<rightarrow> h (Suc 0)"
    by (auto intro: step.intros)
  moreover
  from f_step have "\<forall>i. i\<noteq>0 \<longrightarrow> \<Gamma>\<turnstile>h i \<rightarrow> h (Suc i)"
    by (auto simp add: h_def split: nat.splits)
  ultimately
  show "inf \<Gamma> (Catch c1 c2 # cs) css (Normal s)"
    apply (simp add: inf_def)
    apply (rule_tac x=h in exI)
    apply (simp add: h_def split: nat.splits)
    done
qed

theorem terminates_impl_not_inf: 
  assumes termi: "\<Gamma>\<turnstile>c \<down> s"
  shows "\<not>inf \<Gamma> [c] [] s"
using termi
proof induct
  case (Skip s) thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Skip], [], Normal s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step [of 1]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Basic g s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Basic g], [], Normal s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Normal (g s))"
      by (auto elim: step_Normal_elim_cases)
    with f_step [of 1]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Spec r s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Spec r], [], Normal s)" 
    with f_step [of 0]
    have "\<Gamma>\<turnstile>([Spec r], [], Normal s) \<rightarrow> f (Suc 0)"
      by simp
    then show False
    proof (cases)
      fix t
      assume "(s, t) \<in> r" "f (Suc 0) = ([], [], Normal t)"
      with f_step [of 1]
      show False
        by (auto elim: step_elim_cases)
    next
      assume "\<forall>t. (s, t) \<notin> r" "f (Suc 0) = ([], [], Stuck)"
      with f_step [of 1]
      show False
        by (auto elim: step_elim_cases)
    qed
  qed
next
  case (Guard s g c m)
  have g: "s \<in> g" by fact
  have hyp: "\<not> inf \<Gamma> [c] [] (Normal s)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Guard m g c], [], Normal s)" 
    from g f_step [of 0] f_0
    have "f (Suc 0) = ([c],[],Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "inf \<Gamma> [c] [] (Normal s)"
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
    assume f_0: "f 0 = ([Guard m g c], [], Normal s)" 
    from g f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Fault m)"
      by (auto elim: step_Normal_elim_cases)
    with f_step [of 1]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Fault c m)
  thus ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([c], [], Fault m)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Fault m)"
      by (auto elim: step_Normal_elim_cases)
    with f_step [of 1]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Seq c1 s c2)
  have hyp_c1: "\<not> inf \<Gamma> [c1] [] (Normal s)" by fact
  have hyp_c2: "\<forall>s'. \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> \<Gamma>\<turnstile>c2 \<down> s' \<and> \<not> inf \<Gamma> [c2] [] s'" by fact
  have "\<not> inf \<Gamma> ([c1,c2]) [] (Normal s)"
  proof 
    assume "inf \<Gamma> [c1, c2] [] (Normal s)"
    then show False
    proof (cases rule: infE)
      assume "inf \<Gamma> [c1] [] (Normal s)"
      with hyp_c1 show ?thesis by simp
    next
      fix t
      assume "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> t" "inf \<Gamma> [c2] [] t"
      with hyp_c2 show ?thesis by simp
    qed
  qed
  thus ?case
    by (simp add: inf_Seq)
next
  case (CondTrue s b c1 c2)
  have b: "s \<in> b" by fact
  have hyp_c1: "\<not> inf \<Gamma> [c1] [] (Normal s)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Cond b c1 c2], [], Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = ([c1],[],Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "inf \<Gamma> [c1] [] (Normal s)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c1 show False by simp
  qed
next
  case (CondFalse s b c2 c1)
  have b: "s \<notin> b" by fact
  have hyp_c2: "\<not> inf \<Gamma> [c2] [] (Normal s)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Cond b c1 c2], [], Normal s)" 
    from b f_step [of 0] f_0
    have "f 1 = ([c2],[],Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "inf \<Gamma> [c2] [] (Normal s)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp_c2 show False by simp
  qed
next
  case (WhileTrue s b c)
  have b: "s \<in> b" by fact
  have hyp_c: "\<not> inf \<Gamma> [c] [] (Normal s)" by fact
  have hyp_w: "\<forall>s'. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> s' \<longrightarrow> 
                      \<Gamma>\<turnstile>While b c \<down> s' \<and> \<not> inf \<Gamma> [While b c] [] s'" by fact
  have "\<not> inf \<Gamma> [c,While b c] [] (Normal s)"
  proof 
    assume "inf \<Gamma> [c,While b c] [] (Normal s)"
    from this hyp_c hyp_w show False
      by (cases rule: infE) auto
  qed
  with b show ?case
    by (simp add: inf_WhileTrue)
next
  case (WhileFalse s b c)
  have b: "s \<notin> b" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([While b c], [], Normal s)" 
    from b f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step [of 1]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Call p bdy s)
  have bdy: "\<Gamma> p = Some bdy" by fact
  have hyp: "\<not> inf \<Gamma> [bdy] [] (Normal s)" by fact
  have not_inf_bdy:
    "\<not> inf \<Gamma> [bdy] [([],[Throw])] (Normal s)"
  proof 
    assume "inf \<Gamma> [bdy] [([],[Throw])] (Normal s)"
    then show False
    proof (rule infE)
      assume "inf \<Gamma> [bdy] [] (Normal s)"
      with hyp show False by simp
    next
      fix t
      assume "\<Gamma>\<turnstile>\<langle>bdy,Normal s\<rangle> \<Rightarrow> t"
      assume inf: "inf \<Gamma> [] [([], [Throw])] t"
      then obtain f where
        f_0: "f 0 = ([],[([], [Throw])],t)" and
        f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
        by (auto simp add: inf_def)
      show False
      proof (cases t)
        case (Normal t')
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([],[],(Normal t'))"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of "Suc 0"]
        show False
          by (auto elim: step.cases)
      next        
        case (Abrupt t')
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([Throw],[],(Normal t'))"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of "Suc 0"]
        have "f (Suc (Suc 0)) = ([],[],(Abrupt t'))"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of "Suc(Suc 0)"]
        show False
          by (auto elim: step.cases)
      next
        case (Fault m)
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([],[],Fault m)"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of 1]
        have "f (Suc (Suc 0)) = ([],[],Fault m)"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of "Suc (Suc 0)"]
        show False
          by (auto elim: step.cases)
      next
        case Stuck
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([],[],Stuck)"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of 1]
        have "f (Suc (Suc 0)) = ([],[],Stuck)"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of "Suc (Suc 0)"]
        show False
          by (auto elim: step.cases)
      qed
    qed
  qed   
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Call p], [], Normal s)" 
    from bdy f_step [of 0] f_0
    have "f (Suc 0) = 
              ([bdy],[([],[Throw])],Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step
    have "inf \<Gamma> [bdy] [([],[Throw])] (Normal s)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with not_inf_bdy
    show False by simp
  qed
next
  case (CallUndefined p s)
  have undef: "\<Gamma> p = None" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Call p], [], Normal s)" 
    from undef f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Stuck)"
      by (auto elim: step_Normal_elim_cases)
    with f_step [rule_format, of "Suc 0"]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Stuck c)
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([c], [], Stuck)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Stuck)"
      by (auto elim: step_elim_cases)
    with f_step [rule_format, of "Suc 0"]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (DynCom c s)
  have hyp: "\<not> inf \<Gamma> [(c s)] [] (Normal s)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([DynCom c], [], Normal s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = ([(c s)], [], Normal s)"
      by (auto elim: step_elim_cases)
    with f_step have "inf \<Gamma> [(c s)] [] (Normal s)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp
    with hyp
    show False by simp
  qed
next
  case (Throw s) 
  thus ?case 
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([Throw], [], Normal s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Abrupt s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step [of 1]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Abrupt c s)
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f_0: "f 0 = ([c], [], Abrupt s)" 
    from f_step [of 0] f_0
    have "f (Suc 0) = ([],[],Abrupt s)"
      by (auto elim: step_elim_cases)
    with f_step [rule_format, of "Suc 0"]
    show False
      by (auto elim: step_elim_cases)
  qed
next
  case (Catch c1 s c2)
  have hyp_c1: "\<not> inf \<Gamma> [c1] [] (Normal s)" by fact
  have hyp_c2: "\<forall>s'. \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> Abrupt s' \<longrightarrow>
                   \<Gamma>\<turnstile>c2 \<down> Normal s' \<and> \<not> inf \<Gamma> [c2] [] (Normal s')" by fact
  have "\<not> inf \<Gamma> [c1] [([],[c2])] (Normal s)"
  proof 
    assume "inf \<Gamma> [c1] [([],[c2])] (Normal s)"
    then show False
    proof (rule infE) 
      assume "inf \<Gamma> [c1] [] (Normal s)"
      with hyp_c1 show False by simp
    next
      fix t
      assume eval: "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> t" 
      assume inf: "inf \<Gamma> [] [([], [c2])] t"
      then obtain f where
        f_0: "f 0 = ([],[([], [c2] )],t)" and
        f_step: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
        by (auto simp add: inf_def)
      show False
      proof (cases t)
        case (Normal t')
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([],[],Normal t')"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of 1]
        show False
          by (auto elim: step_elim_cases)
      next
        case (Abrupt t')
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([c2],[],Normal t')"
          by (auto elim: step_Normal_elim_cases)
        with f_step eval Abrupt
        have "inf \<Gamma> [c2] [] (Normal t')"
          apply (simp add: inf_def)
          apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
          by simp
        with eval hyp_c2 Abrupt show False by simp
      next
        case (Fault m)
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([],[],Fault m)"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of 1]
        show False
          by (auto elim: step_elim_cases)
      next
        case Stuck
        with f_0 f_step [rule_format, of 0]
        have "f (Suc 0) = ([],[],Stuck)"
          by (auto elim: step_Normal_elim_cases)
        with f_step [rule_format, of 1]
        show False
          by (auto elim: step_elim_cases)
      qed
    qed
  qed
  thus ?case
    by (simp add: inf_Catch)
qed

lemma terminatess_impl_not_inf:
 assumes termi: "\<Gamma>\<turnstile>cs,css\<Down>s" 
  shows "\<not>inf \<Gamma> cs css s"
using termi
proof (induct)
  case (Nil s)
  show ?case
  proof (rule not_infI)
    fix f
    assume "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    hence "\<Gamma>\<turnstile>f 0 \<rightarrow> f (Suc 0)" 
      by simp
    moreover
    assume "f 0 = ([], [], s)"
    ultimately show False
      by (fastforce elim: step.cases)
  qed
next
  case (ExitBlockNormal nrms css s abrs)
  have hyp: "\<not> inf \<Gamma> nrms css (Normal s)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f0: "f 0 = ([], (nrms, abrs) # css, Normal s)"
    with f_step [of 0] have "f (Suc 0) = (nrms,css,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step have "inf \<Gamma> nrms css (Normal s)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp   
    with hyp show False ..
  qed
next
  case (ExitBlockAbrupt abrs css s nrms)
  have hyp: "\<not> inf \<Gamma> abrs css (Normal s)" by fact
  show ?case
  proof (rule not_infI)
    fix f
    assume f_step: "\<And>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
    assume f0: "f 0 = ([], (nrms, abrs) # css, Abrupt s)"
    with f_step [of 0] have "f (Suc 0) = (abrs,css,Normal s)"
      by (auto elim: step_Normal_elim_cases)
    with f_step have "inf \<Gamma> abrs css (Normal s)"
      apply (simp add: inf_def)
      apply (rule_tac x="\<lambda>i. f (Suc i)" in exI)
      by simp   
    with hyp show False ..
  qed
next
  case (ExitBlockFault nrms css f abrs)
  show ?case
    by (rule not_inf_Fault)
next
  case (ExitBlockStuck nrms css abrs)
  show ?case
    by (rule not_inf_Stuck)
next
  case (Cons c s cs css)
  have termi_c: "\<Gamma>\<turnstile>c \<down> s" by fact
  have hyp: "\<forall>t. \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t \<longrightarrow> \<Gamma>\<turnstile>cs,css\<Down>t \<and> \<not> inf \<Gamma> cs css t"  by fact
  show "\<not> inf \<Gamma> (c # cs) css s"
  proof 
    assume "inf \<Gamma> (c # cs) css s"
    thus False
    proof (rule infE)
      assume "inf \<Gamma> [c] [] s"
      with terminates_impl_not_inf [OF termi_c]
      show False ..
    next
      fix t
      assume "\<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t" "inf \<Gamma> cs css t"
      with hyp show False by simp
    qed
  qed
qed

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

corollary terminatess_impl_no_inf_chain:
 assumes terminatess: "\<Gamma>\<turnstile>cs,css\<Down>s"
 shows "\<not>(\<exists>f. f 0 = (cs,css,s) \<and> (\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f(Suc i)))"
proof -
  have "wf({(y,x). \<Gamma>\<turnstile>(cs,css,s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
  proof (rule wf_trancl)
    show "wf {(y, x). \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}"
    proof (simp only: wf_iff_no_infinite_down_chain,clarify,simp)
      fix f
      assume "\<forall>i. \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
      hence "\<exists>f. f 0 = (cs, css, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
        by (rule renumber [to_pred])
      moreover from terminatess
      have "\<not> (\<exists>f. f 0 = (cs, css, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
        by (rule terminatess_impl_not_inf [unfolded inf_def])
      ultimately show False
        by simp
    qed
  qed
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i)
                 \<in> {(y, x). \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+)"
    by (simp add: wf_iff_no_infinite_down_chain)
  thus ?thesis
  proof (rule contrapos_nn)
    assume "\<exists>f. f 0 = (cs, css, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i))"
    then obtain f where
      f0: "f 0 = (cs, css, s)" and
      seq: "\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f (Suc i)"
      by iprover
    show 
      "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
    proof (rule exI [where x=f],rule allI)
      fix i
      show "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow> y}\<^sup>+"
      proof -   
        {
          fix i have "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow>\<^sup>* f i"
          proof (induct i)
            case 0 show "\<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* f 0"
              by (simp add: f0)
          next
            case (Suc n)
            have "\<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* f n"  by fact
            with seq show "\<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* f (Suc n)"
              by (blast intro: tranclp_into_rtranclp rtranclp_trans)
          qed
        }
        hence "\<Gamma>\<turnstile>(cs,css,s) \<rightarrow>\<^sup>* f i"
          by iprover
        with seq have
          "(f (Suc i), f i) \<in> {(y, x). \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* x \<and> \<Gamma>\<turnstile>x \<rightarrow>\<^sup>+ y}"
          by clarsimp
        moreover 
        have "\<forall>y. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ y\<longrightarrow>\<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* f i\<longrightarrow>\<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* y"
          by (blast intro: tranclp_into_rtranclp rtranclp_trans)
        ultimately 
        show ?thesis 
          by (subst lem)
      qed
    qed
  qed
qed

corollary terminates_impl_no_inf_chain:
 "\<Gamma>\<turnstile>c\<down>s \<Longrightarrow> \<not>(\<exists>f. f 0 = ([c],[],s) \<and> (\<forall>i::nat. \<Gamma>\<turnstile>f i \<rightarrow>\<^sup>+ f(Suc i)))"
  by (rule terminatess_impl_no_inf_chain) (iprover intro: terminatess.intros)


definition
 termi_call_steps :: "('s,'p,'f) body \<Rightarrow> (('s \<times> 'p) \<times> ('s \<times> 'p))set"
where
"termi_call_steps \<Gamma> =
 {((t,q),(s,p)). \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal s \<and> 
       (\<exists>css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal s) \<rightarrow>\<^sup>+ ([the (\<Gamma> q)],css,Normal t))}"

text {* Sequencing computations, or more exactly continuation stacks *}
primrec seq:: "(nat \<Rightarrow> 'a list) \<Rightarrow> nat \<Rightarrow> 'a list"
where
"seq css 0 = []" |
"seq css (Suc i) = css i@seq css i"


theorem wf_termi_call_steps: "wf (termi_call_steps \<Gamma>)"
proof (simp only: termi_call_steps_def wf_iff_no_infinite_down_chain,
       clarify,simp)
  fix S
  assume inf:
     "\<forall>i. (\<lambda>(t,q) (s,p). \<Gamma>\<turnstile>(the (\<Gamma> p)) \<down> Normal s \<and>
                 (\<exists>css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal s) \<rightarrow>\<^sup>+ ([the (\<Gamma> q)],css,Normal t)))
           (S (Suc i)) (S i)"
  obtain s p where "s = (\<lambda>i. fst (S i))" and "p = (\<lambda>i. snd (S i))" 
    by auto
  with inf
  have inf':
     "\<forall>i. \<Gamma>\<turnstile>(the (\<Gamma> (p i))) \<down> Normal (s i) \<and>
                 (\<exists>css. \<Gamma>\<turnstile>([the (\<Gamma> (p i))],[],Normal (s i)) \<rightarrow>\<^sup>+ 
                           ([the (\<Gamma> (p (Suc i)))],css,Normal (s (Suc i))))"
    apply -
    apply (rule allI)
    apply (erule_tac x=i in allE)
    apply auto
    done
  show False
  proof -
    from inf' -- {* Skolemization of css with axiom of choice *}
    have "\<exists>css. \<forall>i. \<Gamma>\<turnstile>(the (\<Gamma> (p i))) \<down> Normal (s i) \<and>
                 \<Gamma>\<turnstile>([the (\<Gamma> (p i))],[],Normal (s i)) \<rightarrow>\<^sup>+ 
                           ([the (\<Gamma> (p (Suc i)))],css i,Normal (s (Suc i)))"
      apply -
      apply (rule choice)
      by blast
    then obtain css where
      termi_css: "\<forall>i. \<Gamma>\<turnstile>(the (\<Gamma> (p i))) \<down> Normal (s i)" and
      step_css: "\<forall>i. \<Gamma>\<turnstile>([the (\<Gamma> (p i))],[],Normal (s i)) \<rightarrow>\<^sup>+ 
                         ([the (\<Gamma> (p (Suc i)))],css i,Normal (s (Suc i)))"
      by blast
    def f == "\<lambda>i. ([the (\<Gamma> (p i))], seq css i,Normal (s i)::('a,'c) xstate)"
    have "f 0 = ([the (\<Gamma> (p 0))],[],Normal (s 0))"
      by (simp add: f_def)
    moreover
    have "\<forall>i. \<Gamma>\<turnstile> (f i) \<rightarrow>\<^sup>+ (f (i+1))"
    proof 
      fix i
      from step_css [rule_format, of i]
      have "\<Gamma>\<turnstile>([the (\<Gamma> (p i))], [], Normal (s i)) \<rightarrow>\<^sup>+ 
              ([the (\<Gamma> (p (Suc i)))], css i, Normal (s (Suc i)))".
      from app_css_steps [OF this,simplified]
      have "\<Gamma>\<turnstile>([the (\<Gamma> (p i))], seq css i, Normal (s i)) \<rightarrow>\<^sup>+ 
              ([the (\<Gamma> (p (Suc i)))], css i@seq css i, Normal (s (Suc i)))".
      thus "\<Gamma>\<turnstile> (f i) \<rightarrow>\<^sup>+ (f (i+1))"
        by (simp add: f_def)
    qed
    moreover from termi_css [rule_format, of 0]
    have "\<not> (\<exists>f. (f 0 = ([the (\<Gamma> (p 0))],[],Normal (s 0)) \<and> 
                 (\<forall>i. \<Gamma>\<turnstile>(f i) \<rightarrow>\<^sup>+ f(Suc i))))"
      by (rule terminates_impl_no_inf_chain)
    ultimately show False
      by auto
  qed
qed

text {* An alternative proof using Hilbert-choice instead of axiom of choice.*}
theorem "wf (termi_call_steps \<Gamma>)"
proof (simp only: termi_call_steps_def wf_iff_no_infinite_down_chain,
       clarify,simp)
  fix S
  assume inf:
     "\<forall>i. (\<lambda>(t,q) (s,p). \<Gamma>\<turnstile>(the (\<Gamma> p)) \<down> Normal s \<and>
                 (\<exists>css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal s) \<rightarrow>\<^sup>+ ([the (\<Gamma> q)],css,Normal t)))
           (S (Suc i)) (S i)"
  obtain s p where "s = (\<lambda>i. fst (S i))" and "p = (\<lambda>i. snd (S i))" 
    by auto
  with inf
  have inf':
     "\<forall>i. \<Gamma>\<turnstile>(the (\<Gamma> (p i))) \<down> Normal (s i) \<and>
                 (\<exists>css. \<Gamma>\<turnstile>([the (\<Gamma> (p i))],[],Normal (s i)) \<rightarrow>\<^sup>+ 
                           ([the (\<Gamma> (p (Suc i)))],css,Normal (s (Suc i))))"
    apply -
    apply (rule allI)
    apply (erule_tac x=i in allE)
    apply auto
    done
  show "False"
  proof -
    def CSS \<equiv> "\<lambda>i. (SOME css.  
                      \<Gamma>\<turnstile>([the (\<Gamma> (p i))],[], Normal (s i)) \<rightarrow>\<^sup>+
                      ([the (\<Gamma> (p (i+1)))],css,Normal (s (i+1))))"
    def f == "\<lambda>i. ([the (\<Gamma> (p i))], seq CSS i,Normal (s i)::('a,'c) xstate)"
    have "f 0 = ([the (\<Gamma> (p 0))],[],Normal (s 0))"
      by (simp add: f_def)
    moreover
    have "\<forall>i. \<Gamma>\<turnstile> (f i) \<rightarrow>\<^sup>+ (f (i+1))"
    proof 
      fix i
      from inf' [rule_format, of i] obtain css where
         css: "\<Gamma>\<turnstile>([the (\<Gamma> (p i))],[],Normal (s i)) \<rightarrow>\<^sup>+ 
                ([the (\<Gamma> (p (i+1)))],css,Normal (s (i+1)))"
        by fastforce
      hence "\<Gamma>\<turnstile>([the (\<Gamma> (p i))], seq CSS i, Normal (s i)) \<rightarrow>\<^sup>+ 
                  ([the (\<Gamma> (p (i+1)))], CSS i @ seq CSS i, Normal (s (i+1)))"
        apply -
        apply (unfold CSS_def)
        apply (rule someI2 
              [where P="\<lambda>css. 
                    \<Gamma>\<turnstile>([the (\<Gamma> (p i))],[],Normal (s i))\<rightarrow>\<^sup>+
                         ([the (\<Gamma> (p (i+1)))],css, Normal (s (i+1)))"])
        apply (rule css)
        apply (fastforce dest: app_css_steps)
        done
      thus "\<Gamma>\<turnstile> (f i) \<rightarrow>\<^sup>+ (f (i+1))"
        by (simp add: f_def)
    qed
    moreover from inf' [rule_format, of 0]
    have "\<Gamma>\<turnstile>the (\<Gamma> (p 0)) \<down> Normal (s 0)" 
      by iprover
    then have "\<not> (\<exists>f. (f 0 = ([the (\<Gamma> (p 0))],[],Normal (s 0)) \<and> 
                 (\<forall>i. \<Gamma>\<turnstile>(f i) \<rightarrow>\<^sup>+ f(Suc i))))"
      by (rule terminates_impl_no_inf_chain)
    ultimately show False
      by auto
  qed
qed

lemma not_inf_implies_wf: assumes not_inf: "\<not> inf \<Gamma> cs css s"
  shows "wf {(c2,c1). \<Gamma> \<turnstile> (cs,css,s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma> \<turnstile> c1 \<rightarrow> c2}"
proof (simp only: wf_iff_no_infinite_down_chain,clarify, simp)
  fix f
  assume "\<forall>i. \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* f i \<and> \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)"
  hence "\<exists>f. f 0 = (cs, css, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i))"
    by (rule renumber [to_pred])
  moreover from not_inf
  have "\<not> (\<exists>f. f 0 = (cs, css, s) \<and> (\<forall>i. \<Gamma>\<turnstile>f i \<rightarrow> f (Suc i)))"
    by (unfold inf_def)
  ultimately show False
    by simp
qed

lemma wf_implies_termi_reach:
assumes wf: "wf {(c2,c1). \<Gamma> \<turnstile> (cs,css,s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma> \<turnstile> c1 \<rightarrow> c2}"
shows "\<And>cs1 css1 s1. \<lbrakk>\<Gamma> \<turnstile> (cs,css,s) \<rightarrow>\<^sup>* c1;  c1=(cs1,css1,s1)\<rbrakk>\<Longrightarrow> \<Gamma>\<turnstile>cs1,css1\<Down>s1"
using wf 
proof (induct c1, simp)
  fix cs1 css1 s1
  assume reach: "\<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* (cs1, css1, s1)"
  assume hyp_raw: "\<And>y cs2 css2 s2. \<lbrakk>\<Gamma> \<turnstile> (cs1,css1,s1) \<rightarrow> (cs2,css2,s2);
                 \<Gamma> \<turnstile> (cs,css,s) \<rightarrow>\<^sup>* (cs2,css2,s2); y=(cs2,css2,s2)\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>cs2,css2\<Down>s2"
  have hyp: "\<And>cs2 css2 s2. \<lbrakk>\<Gamma> \<turnstile> (cs1,css1,s1) \<rightarrow> (cs2,css2,s2)\<rbrakk> \<Longrightarrow> 
                 \<Gamma>\<turnstile>cs2,css2\<Down>s2"
    apply -
    apply (rule hyp_raw)
    apply   assumption
    using reach 
    apply  simp
    apply (rule refl)
    done
  show "\<Gamma>\<turnstile>cs1,css1\<Down>s1"
  proof (cases s1)
    case (Normal s1')
    show ?thesis
    proof (cases cs1)
      case Nil
      note cs1_Nil = this
      show ?thesis
      proof (cases css1)
        case Nil
        with cs1_Nil show ?thesis
          by (auto intro: terminatess.intros)
      next
        case (Cons nrms_abrs css1')
        then obtain nrms abrs where nrms_abrs: "nrms_abrs=(nrms,abrs)"
          by (cases "nrms_abrs")
        have "\<Gamma> \<turnstile> ([],(nrms,abrs)#css1',Normal s1') \<rightarrow> (nrms,css1',Normal s1')"
          by (rule step.intros)
        from hyp [simplified cs1_Nil Cons nrms_abrs Normal, OF this]
        have "\<Gamma>\<turnstile>nrms,css1'\<Down>Normal s1'".
        from ExitBlockNormal [OF this] cs1_Nil Cons nrms_abrs Normal
        show ?thesis
          by auto
      qed
    next
      case (Cons c1 cs1')
      have "\<Gamma>\<turnstile>c1#cs1',css1\<Down>Normal s1'"
      proof (cases c1)
        case Skip
        have "\<Gamma> \<turnstile> (Skip#cs1',css1,Normal s1') \<rightarrow> (cs1',css1,Normal s1')"
          by (rule step.intros)
        from hyp [simplified Cons Skip Normal, OF this]
        have "\<Gamma>\<turnstile>cs1',css1\<Down>Normal s1'".
        with Normal Skip show ?thesis
          by (auto intro: terminatess.intros terminates.intros 
                  elim: exec_Normal_elim_cases)
      next
        case (Basic f)
        have "\<Gamma> \<turnstile> (Basic f#cs1',css1,Normal s1') \<rightarrow> (cs1',css1,Normal (f s1'))"
          by (rule step.intros)
        from hyp [simplified Cons Basic Normal, OF this]
        have "\<Gamma>\<turnstile>cs1',css1\<Down>Normal (f s1')".
        with Normal Basic show ?thesis
          by (auto intro: terminatess.intros terminates.intros 
                  elim: exec_Normal_elim_cases)
      next
        case (Spec r)
        with Normal show ?thesis
          apply simp
          apply (rule terminatess.Cons)
          apply  (fastforce intro: terminates.intros)
          apply (clarify)
          apply (erule exec_Normal_elim_cases)
          apply  clarsimp
          apply  (rule hyp)
          apply  (fastforce intro: step.intros simp add: Cons Spec Normal )
          apply (fastforce intro: terminatess_Stuck)
          done
      next
        case (Seq c\<^sub>1 c\<^sub>2)
        have "\<Gamma> \<turnstile> (Seq c\<^sub>1 c\<^sub>2#cs1',css1,Normal s1') \<rightarrow> (c\<^sub>1#c\<^sub>2#cs1',css1,Normal s1')"
          by (rule step.intros)
        from hyp [simplified Cons Seq Normal, OF this]
        have "\<Gamma>\<turnstile>c\<^sub>1 # c\<^sub>2 # cs1',css1\<Down>Normal s1'".
        with Normal Seq show ?thesis
          by (fastforce intro: terminatess.intros terminates.intros
                   elim: terminatess_elim_cases exec_Normal_elim_cases)
      next
        case (Cond b c\<^sub>1 c\<^sub>2)
        show ?thesis
        proof (cases "s1' \<in> b")
          case True
          hence "\<Gamma>\<turnstile>(Cond b c\<^sub>1 c\<^sub>2#cs1',css1,Normal s1') \<rightarrow> (c\<^sub>1#cs1',css1,Normal s1')"
            by (rule step.intros)
          from hyp [simplified Cons Cond Normal, OF this]
          have "\<Gamma>\<turnstile>c\<^sub>1 # cs1',css1\<Down>Normal s1'".
          with Normal Cond True show ?thesis
            by (fastforce intro: terminatess.intros terminates.intros
              elim: terminatess_elim_cases exec_Normal_elim_cases)
        next
          case False
          hence "\<Gamma>\<turnstile>(Cond b c\<^sub>1 c\<^sub>2#cs1',css1,Normal s1') \<rightarrow> (c\<^sub>2#cs1',css1,Normal s1')"
            by (rule step.intros)
          from hyp [simplified Cons Cond Normal, OF this]
          have "\<Gamma>\<turnstile>c\<^sub>2 # cs1',css1\<Down>Normal s1'".
          with Normal Cond False show ?thesis
            by (fastforce intro: terminatess.intros terminates.intros
              elim: terminatess_elim_cases exec_Normal_elim_cases)
        qed
      next
        case (While b c')
        show ?thesis
        proof (cases "s1' \<in> b")
          case True
          then have "\<Gamma>\<turnstile>(While b c' # cs1', css1, Normal s1') \<rightarrow> 
                       (c' # While b c' # cs1', css1, Normal s1')"
            by (rule step.intros)
          from hyp [simplified Cons While Normal, OF this]
          have "\<Gamma>\<turnstile>c' # While b c' # cs1',css1\<Down>Normal s1'".
          with Cons While True Normal
          show ?thesis
            by (fastforce intro: terminatess.intros terminates.intros exec.intros 
                    elim: terminatess_elim_cases exec_Normal_elim_cases)
        next
          case False
          then 
          have "\<Gamma>\<turnstile>(While b c' # cs1', css1, Normal s1') \<rightarrow> (cs1', css1, Normal s1')"
            by (rule step.intros)
          from hyp [simplified Cons While Normal, OF this]
          have "\<Gamma>\<turnstile>cs1',css1\<Down>Normal s1'".
          with Cons While False Normal
          show ?thesis
            by (fastforce intro: terminatess.intros terminates.intros exec.intros 
                    elim: terminatess_elim_cases exec_Normal_elim_cases)
        qed
      next
        case (Call p)
        show ?thesis
        proof (cases "\<Gamma> p")
          case None
          with Call Normal show ?thesis
            by (fastforce intro: terminatess.intros terminates.intros terminatess_Stuck
                 elim: exec_Normal_elim_cases)
        next
          case (Some bdy)
          then
          have "\<Gamma> \<turnstile> (Call p#cs1',css1,Normal s1') \<rightarrow> 
                    ([bdy],(cs1',Throw#cs1')#css1,Normal s1')"
            by (rule step.intros)
          from hyp [simplified Cons Call Normal Some, OF this]
          have "\<Gamma>\<turnstile>[bdy],(cs1', Throw # cs1') # css1\<Down>Normal s1'".
          with Some Call Normal show ?thesis
            apply simp
            apply (rule terminatess.intros)
            apply (blast elim: terminatess_elim_cases intro: terminates.intros)
            apply clarify
            apply (erule terminatess_elim_cases)
            apply (erule exec_Normal_elim_cases)
            prefer 2
            apply  simp
            apply (erule_tac x=t in allE)
            apply (case_tac t)
            apply (auto intro: terminatess_Stuck terminatess_Fault exec.intros 
                    elim: terminatess_elim_cases exec_Normal_elim_cases)
            done
        qed
      next
        case (DynCom c')
        have "\<Gamma> \<turnstile> (DynCom c'#cs1',css1,Normal s1') \<rightarrow> (c' s1'#cs1',css1,Normal s1')"
          by (rule step.intros)
        from hyp [simplified Cons DynCom Normal, OF this]
        have "\<Gamma>\<turnstile>c' s1'#cs1',css1\<Down>Normal s1'".
        with Normal DynCom show ?thesis
          by (fastforce intro: terminatess.intros terminates.intros exec.intros 
                    elim: terminatess_elim_cases exec_Normal_elim_cases)
      next
        case (Guard f g c')
        show ?thesis
        proof (cases "s1' \<in> g")
          case True
          then have "\<Gamma> \<turnstile> (Guard f g c'#cs1',css1,Normal s1') \<rightarrow> (c'#cs1',css1,Normal s1')"
            by (rule step.intros)
          from hyp [simplified Cons Guard Normal, OF this]
          have "\<Gamma>\<turnstile>c'#cs1',css1\<Down>Normal s1'".
          with Normal Guard True show ?thesis
            by (fastforce intro: terminatess.intros terminates.intros exec.intros 
                    elim: terminatess_elim_cases exec_Normal_elim_cases)
        next
          case False
          with Guard Normal show ?thesis
            by (fastforce intro: terminatess.intros terminatess_Fault 
                                terminates.intros  
                 elim:  exec_Normal_elim_cases)
        qed
      next
        case Throw
        have "\<Gamma> \<turnstile> (Throw#cs1',css1,Normal s1') \<rightarrow> (cs1',css1,Abrupt s1')"
          by (rule step.intros)
        from hyp [simplified Cons Throw Normal, OF this]
        have "\<Gamma>\<turnstile>cs1',css1\<Down>Abrupt s1'".
        with Normal Throw show ?thesis
          by (auto intro: terminatess.intros terminates.intros 
                  elim: exec_Normal_elim_cases)
      next
        case (Catch c\<^sub>1 c\<^sub>2)
        have "\<Gamma> \<turnstile> (Catch c\<^sub>1 c\<^sub>2#cs1',css1,Normal s1') \<rightarrow> 
                  ([c\<^sub>1], (cs1',c\<^sub>2#cs1')# css1,Normal s1')"
          by (rule step.intros)
        from hyp [simplified Cons Catch Normal, OF this]
        have "\<Gamma>\<turnstile>[c\<^sub>1],(cs1', c\<^sub>2 # cs1') # css1\<Down>Normal s1'".
        with Normal Catch show ?thesis
          by (fastforce intro: terminatess.intros terminates.intros exec.intros 
                    elim: terminatess_elim_cases exec_Normal_elim_cases)
      qed       
      with Cons Normal show ?thesis
        by simp
    qed
  next
    case (Abrupt s1')
    show ?thesis
    proof (cases cs1)
      case Nil
      note cs1_Nil = this
      show ?thesis
      proof (cases css1)
        case Nil
        with cs1_Nil show ?thesis by (auto intro: terminatess.intros)
      next
        case (Cons nrms_abrs css1')
        then obtain nrms abrs where nrms_abrs: "nrms_abrs=(nrms,abrs)"
          by (cases "nrms_abrs")
        have "\<Gamma> \<turnstile> ([],(nrms,abrs)#css1',Abrupt s1') \<rightarrow> (abrs,css1',Normal s1')"
          by (rule step.intros)
        from hyp [simplified cs1_Nil Cons nrms_abrs Abrupt, OF this]
        have "\<Gamma>\<turnstile>abrs,css1'\<Down>Normal s1'".
        from ExitBlockAbrupt [OF this] cs1_Nil Cons nrms_abrs Abrupt
        show ?thesis
          by auto
      qed
    next
      case (Cons c1 cs1')
      have "\<Gamma>\<turnstile>c1#cs1',css1\<Down>Abrupt s1'"
      proof -
        have "\<Gamma> \<turnstile> (c1#cs1',css1,Abrupt s1') \<rightarrow> (cs1',css1,Abrupt s1')"
          by (rule step.intros)
        from hyp [simplified Cons Abrupt, OF this]
        have "\<Gamma>\<turnstile>cs1',css1\<Down>Abrupt s1'".
        with Cons Abrupt
        show ?thesis
          by (fastforce intro: terminatess.intros terminates.intros exec.intros 
                    elim: terminatess_elim_cases exec_Normal_elim_cases)
      qed
      with Cons Abrupt show ?thesis by simp
    qed
  next
    case (Fault f)
    thus ?thesis by (auto intro: terminatess_Fault)
  next
    case Stuck
    thus ?thesis by (auto intro: terminatess_Stuck)
  qed
qed

lemma not_inf_impl_terminatess:
  assumes not_inf: "\<not> inf \<Gamma> cs css s"
  shows "\<Gamma>\<turnstile>cs,css\<Down>s"
proof -
  from not_inf_implies_wf [OF not_inf]
  have wf: "wf {(c2, c1). \<Gamma>\<turnstile>(cs, css, s) \<rightarrow>\<^sup>* c1 \<and> \<Gamma>\<turnstile>c1 \<rightarrow> c2}".
  show ?thesis
    by (rule wf_implies_termi_reach [OF wf]) auto
qed

lemma not_inf_impl_terminates:
  assumes not_inf: "\<not> inf \<Gamma> [c] [] s"
  shows "\<Gamma>\<turnstile>c\<down>s"
proof -
  from not_inf_impl_terminatess [OF not_inf]
  have "\<Gamma>\<turnstile>[c],[]\<Down>s".
  thus ?thesis
    by (auto elim: terminatess_elim_cases)
qed

theorem terminatess_iff_not_inf: 
  "\<Gamma>\<turnstile>cs,css\<Down>s = (\<not> inf \<Gamma> cs css s)"
  apply rule
  apply  (erule terminatess_impl_not_inf)
  apply (erule not_inf_impl_terminatess)
  done

corollary terminates_iff_not_inf: 
  "\<Gamma>\<turnstile>c\<down>s = (\<not> inf \<Gamma> [c] [] s)"
  apply (rule)
  apply  (erule terminates_impl_not_inf)
  apply (erule not_inf_impl_terminates)
  done

subsection {* Completeness of Total Correctness Hoare Logic*}

lemma ConseqMGT: 
  assumes modif: "\<forall>Z::'a. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z::'a assn) c (Q' Z),(A' Z)"
  assumes impl: "\<And>s. s \<in> P \<Longrightarrow> s \<in> P' s \<and> (\<forall>t. t \<in> Q' s \<longrightarrow> t \<in> Q) \<and> 
                                            (\<forall>t. t \<in> A' s \<longrightarrow> t \<in> A)"
  shows "\<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
using impl 
by - (rule conseq [OF modif],blast)

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

lemma Call_lemma':
 assumes Call_hyp: 
 "\<forall>q\<in>dom \<Gamma>. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
                       \<Gamma>\<turnstile>Call q\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                 (Call q)
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
 shows "\<And>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub>  
      {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and> 
                (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c#cs,css,Normal s))} 
              c 
      {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
      {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
proof (induct c)
  case Skip
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
                (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Skip # cs,css,Normal s))}
               Skip
              {t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Skip,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Skip [THEN conseqPre]) (blast intro: exec.Skip)
next
  case (Basic f)
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Basic f,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Basic f#cs,css,Normal s))}
               Basic f 
              {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Basic f,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule hoaret.Basic [THEN conseqPre]) (blast intro: exec.Basic)
next
  case (Spec r)
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Spec r,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Spec r#cs,css,Normal s))}
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
                     \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                 (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c1#cs,css,Normal s))}
                c1 
               {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Seq.hyps by iprover
  have hyp_c2: 
    "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                 (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c2#cs,css,Normal s))}
                c2 
               {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
               {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Seq.hyps by iprover
  have c1: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
              (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Seq c1 c2#cs,css,Normal s))}
               c1
               {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t \<and> 
                   \<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                   \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                  (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c2#cs,css,Normal t))},
               {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp_c1],clarify,safe)
    assume "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
      by (blast dest: Seq_NoFaultStuckD1)
  next
    fix cs css
    assume "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Seq c1 c2 # cs,css,Normal Z)"
    thus "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c1 # cs,css, Normal Z)"
      by (blast intro: rtranclp_into_tranclp1 [THEN tranclp_into_rtranclp]
                 step.Seq)
  next
    fix t
    assume "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
            "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t"
    thus "\<Gamma>\<turnstile>\<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (blast dest: Seq_NoFaultStuckD2)
  next
    fix cs css t
    assume "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Seq c1 c2#cs,css,Normal Z)"
    also have "\<Gamma>\<turnstile>(Seq c1 c2 # cs,css,Normal Z) \<rightarrow> (c1#c2#cs,css,Normal Z)"
      by (rule step.Seq)
    also assume "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t" 
    hence "\<Gamma>\<turnstile> (c1#c2#cs,css,Normal Z) \<rightarrow>\<^sup>* (c2#cs,css,Normal t)"
      by (rule exec_impl_steps)
    finally
    show "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c2 # cs,css, Normal t)"
      by iprover
  next
    fix t 
    assume "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    thus "\<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t"
      by (blast intro: exec.intros)
  qed
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>     
                  \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
              (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Seq c1 c2#cs,css,Normal s))}
              Seq c1 c2 
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Seq c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  by (rule hoaret.Seq [OF c1 ConseqMGT [OF hyp_c2]])  
     (blast intro: exec.intros)
next
  case (Cond b c1 c2) 
  have hyp_c1:
       "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                        \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                    (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[], Normal \<sigma>) \<rightarrow>\<^sup>* (c1#cs,css,Normal s))}
                   c1 
                  {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Cond.hyps by iprover
  have 
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
           \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
           (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Cond b c1 c2#cs,css,Normal s))}
           \<inter> b)
           c1 
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp_c1],safe)
    assume "Z \<in> b" "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c1,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (auto simp add: final_notin_def intro: exec.CondTrue)
  next  
    fix cs css 
    assume "Z \<in> b" 
      "\<Gamma>\<turnstile>([the (\<Gamma> p)],[], Normal \<sigma>) \<rightarrow>\<^sup>* (Cond b c1 c2 # cs,css, Normal Z)"
    thus "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[], Normal \<sigma>) \<rightarrow>\<^sup>* (c1 # cs,css, Normal Z)"
      by (blast intro: rtranclp_into_tranclp1 [THEN tranclp_into_rtranclp] 
          step.CondTrue)
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
                     \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                    (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c2#cs,css,Normal s))}
                   c2 
                  {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Normal t},
                  {t. \<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Cond.hyps by iprover
  have 
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
              \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
           (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>*(Cond b c1 c2#cs,css, Normal s))}
           \<inter> -b)
           c2 
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Normal t},
          {t. \<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp_c2],safe)
    assume "Z \<notin> b" "\<Gamma>\<turnstile>\<langle>Cond b c1 c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (auto simp add: final_notin_def intro: exec.CondFalse)
  next
    fix cs css
    assume "Z \<notin> b" 
      "\<Gamma>\<turnstile>([the (\<Gamma> p)],[], Normal \<sigma>) \<rightarrow>\<^sup>* (Cond b c1 c2 # cs,css, Normal Z)"
    thus "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[], Normal \<sigma>) \<rightarrow>\<^sup>* (c2 # cs,css,Normal Z)"
      by (blast intro: rtranclp_into_tranclp1 [THEN tranclp_into_rtranclp] 
          step.CondFalse)
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
              \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
           (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Cond b c1 c2#cs,css,Normal s))}
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
                    \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and> 
                  (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* 
                               (While b c#cs,css,Normal t))}"
  let ?A = "\<lambda>Z. {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  let ?r = "{(t,s). \<Gamma>\<turnstile>(While b c)\<down>Normal s \<and> s\<in>b \<and>  
                    \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t}"
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
       {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
          (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>)\<rightarrow>\<^sup>*(While b c#cs,css,Normal s))}
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
                \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and> 
               (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c # cs,css,Normal s))}
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
                     \<Gamma>\<turnstile>the (\<Gamma> p)\<down> Normal \<sigma> \<and>
                     (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* 
                                  (While b c#cs,css,Normal t))}
                   \<inter> b"
        then obtain cs css where  
          s_eq_\<tau>: "s=\<tau>" and
          Z_s_unroll: "(Z,s) \<in> ?unroll" and
          noabort:"\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)" and
          termi:  "\<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma>" and
          reach: "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* 
                    (While b c#cs,css,Normal s)"and
          s_in_b: "s\<in>b" 
          by blast
        have reach_c: 
          "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c#While b c#cs,css,Normal s)"
        proof -
          note reach
          also from s_in_b  
          have "\<Gamma>\<turnstile>(While b c#cs,css,Normal s)\<rightarrow> 
                  (c#While b c#cs,css,Normal s)"
            by (rule step.WhileTrue)
          finally
          show ?thesis .
        qed
        from reach termi have
          termi_while: "\<Gamma>\<turnstile>While b c \<down> Normal s"
          by (rule steps_preserves_termination)
        show "s \<in> {t. t = s \<and> \<Gamma>\<turnstile>\<langle>c,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                      \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
                   (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c#cs,css,Normal t))} \<and>
        (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal t} \<longrightarrow>
             t \<in> {t. (t,\<tau>) \<in> ?r} \<inter>  
                 {t. (Z, t) \<in> ?unroll \<and> 
                     (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow>  e\<in>b 
                           \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                              (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and> 
                      \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
                    (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* 
                                 (While b c # cs,css,Normal t))}) \<and> 
         (\<forall>t. t \<in> {t. \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt t} \<longrightarrow>
             t \<in> {t. \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt t})"
          (is "?C1 \<and> ?C2 \<and> ?C3")
        proof (intro conjI)
          from Z_s_unroll noabort s_in_b termi reach_c show ?C1 
            by blast
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
            have "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (While b c#cs,css,Normal t)"
            proof -
              note reach_c
              also from s_t
              have "\<Gamma>\<turnstile>(c#While b c#cs,css,Normal s)\<rightarrow>\<^sup>*
                      (While b c#cs,css, Normal t)"
                by (rule exec_impl_steps)
              finally show ?thesis .
            qed
            moreover note noabort termi
            ultimately 
            have "(t,\<tau>) \<in> ?r \<and> (Z, t) \<in> ?unroll \<and> 
                  (\<forall>e. (Z,e)\<in>?unroll \<longrightarrow> e\<in>b
                        \<longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                            (\<forall>u. \<Gamma>\<turnstile>\<langle>c,Normal e\<rangle> \<Rightarrow>Abrupt u \<longrightarrow> 
                                  \<Gamma>\<turnstile>\<langle>While b c,Normal Z\<rangle> \<Rightarrow> Abrupt u)) \<and>
                  \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
                    (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* 
                                 (While b c # cs,css, Normal t))"
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
                       \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                   (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* 
                                (While b c#cs,css,Normal s))}"
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
               \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
              (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* 
                  (Call q # cs,css,Normal s))}"
  from noStuck_Call
  have "\<forall>s \<in> ?P. q \<in> dom \<Gamma>"
    by (fastforce simp add: final_notin_def)
  then show ?case
  proof (rule conseq_extract_state_indep_prop)
    assume q_defined: "q \<in> dom \<Gamma>"
    from Call_hyp have
      "\<forall>q\<in>dom \<Gamma>. \<forall>Z. 
        \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>{s. s=Z \<and> \<Gamma>\<turnstile>\<langle>the (\<Gamma> q),Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>
                        \<Gamma>\<turnstile>(the (\<Gamma> q))\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                 (Call q)
                {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> q),Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> q),Normal Z\<rangle> \<Rightarrow> Abrupt t}"
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
      fix cs css
      assume 
        "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>)\<rightarrow>\<^sup>* (Call q # cs,css,Normal Z)"
        "\<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma>"
      hence "\<Gamma>\<turnstile>Call q \<down> Normal Z"
        by (rule steps_preserves_termination)
      with q_defined show "\<Gamma>\<turnstile>Call q \<down> Normal Z"
        by (auto elim: terminates_Normal_elim_cases)
    next
      fix cs css
      assume reach: 
        "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Call q#cs,css,Normal Z)"
      moreover have "\<Gamma>\<turnstile>(Call q # cs,css, Normal Z) \<rightarrow> 
                        ([the (\<Gamma> q)],(cs,Throw#cs)#css, Normal Z)"
        by (rule step.Call) (insert q_defined,auto)
      ultimately
      have "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>+ ([the (\<Gamma> q)],(cs,Throw#cs)#css,Normal Z)"
        by (rule rtranclp_into_tranclp1)
      moreover
      assume termi: "\<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma>"
      ultimately
      show "((Z,q), \<sigma>,p) \<in> termi_call_steps \<Gamma>"
        by (auto simp add: termi_call_steps_def)
    qed
  qed
next
  case (DynCom c)
  have hyp: 
    "\<And>s'. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>
      {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>c s',Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
            \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
          (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c s'#cs,css,Normal s))}
        (c s') 
       {t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c s',Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using DynCom by simp
  have hyp':
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>DynCom c,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
               (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (DynCom c#cs,css,Normal s))}
        (c Z) 
       {t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (rule ConseqMGT [OF hyp],safe)
    assume "\<Gamma>\<turnstile>\<langle>DynCom c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    then show "\<Gamma>\<turnstile>\<langle>c Z,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (fastforce simp add: final_notin_def intro: exec.intros)
  next
    fix cs css
    assume "\<Gamma>\<turnstile>([the (\<Gamma> p)], [], Normal \<sigma>) \<rightarrow>\<^sup>* (DynCom c # cs, css, Normal Z)"
    also have "\<Gamma>\<turnstile>(DynCom c # cs, css, Normal Z) \<rightarrow> (c Z#cs,css,Normal Z)"
      by (rule step.DynCom)
    finally
    show "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)], [], Normal \<sigma>) \<rightarrow>\<^sup>* (c Z # cs, css, Normal Z)"
      by blast
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
              \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and> 
            (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c#cs,css,Normal s))}
          c 
         {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Normal t},
         {t. \<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Guard.hyps by iprover
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                  \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
            (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Guard f g c#cs,css,Normal s))}
              Guard f g c  
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
  proof (cases "f \<in> F")
    case True
    have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (g \<inter> {s. s=Z \<and> 
                     \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                 \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
            (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Guard f g c#cs,css,Normal s))})
              c  
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    proof (rule ConseqMGT [OF hyp_c], safe)
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" "Z\<in>g"
      thus "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
        by (auto simp add: final_notin_def intro: exec.intros)
    next
      fix cs css
      assume "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Guard f g c#cs,css,Normal Z)"
      also
      assume "Z \<in> g"
      hence "\<Gamma>\<turnstile>(Guard f g c#cs,css,Normal Z) \<rightarrow> (c#cs,css,Normal Z)" 
        by (rule step.Guard)
      finally show "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c#cs,css,Normal Z)"
        by iprover
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
                 \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
            (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Guard f g c#cs,css,Normal s))})
              c  
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    proof (rule ConseqMGT [OF hyp_c], safe)
      assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))" 
      thus "\<Gamma>\<turnstile>\<langle>c,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
        using False
        by (cases "Z\<in> g") (auto simp add: final_notin_def intro: exec.intros)
    next
      fix cs css
      assume "\<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (Guard f g c#cs,css,Normal Z)"
      also assume "\<Gamma>\<turnstile>\<langle>Guard f g c ,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      hence "Z \<in> g"
        using False by (auto simp add: final_notin_def intro: exec.GuardFault)
      hence "\<Gamma>\<turnstile>(Guard f g c#cs,css,Normal Z) \<rightarrow> (c#cs,css,Normal Z)" 
        by (rule step.Guard)
      finally show "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c#cs,css,Normal Z)"
        by iprover
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
                  \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal \<sigma> \<and>
                (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[], Normal \<sigma>) \<rightarrow>\<^sup>* (Throw#cs,css,Normal s))}
              Throw
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>Throw,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    by (rule conseqPre [OF hoaret.Throw]) 
       (blast intro: exec.intros terminates.intros)
next
  case (Catch c\<^sub>1 c\<^sub>2)
  have hyp_c1:
   "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s= Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
                (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c\<^sub>1# cs, css,Normal s))}
               c\<^sub>1 
              {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  have hyp_c2:
   "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s= Z \<and> \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                     \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
                (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c\<^sub>2# cs, css,Normal s))}
               c\<^sub>2
              {t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},{t. \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
    using Catch.hyps by iprover
  have
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. s = Z \<and> \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
               \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
            (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>)\<rightarrow>\<^sup>*(Catch c\<^sub>1 c\<^sub>2 #cs,css,Normal s))}
            c\<^sub>1
           {t. \<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow> Normal t},
           {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t \<and> 
               \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault`(-F)) \<and> \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
               (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c\<^sub>2# cs, css,Normal t))}"
  proof (rule ConseqMGT [OF hyp_c1],clarify,safe) 
    assume "\<Gamma>\<turnstile>\<langle>Catch c\<^sub>1 c\<^sub>2,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
    thus "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F))"
      by (fastforce simp add: final_notin_def intro: exec.intros)
  next
    fix cs css
    assume "\<Gamma>\<turnstile>([the (\<Gamma> p)], [], Normal \<sigma>) \<rightarrow>\<^sup>* (Catch c\<^sub>1 c\<^sub>2 # cs, css, Normal Z)"
    also have
      "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2 # cs, css, Normal Z) \<rightarrow> ([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal Z)"
      by (rule step.Catch)
    finally
    show "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)], [], Normal \<sigma>) \<rightarrow>\<^sup>* (c\<^sub>1 # cs, css, Normal Z)"
      by iprover
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
    fix cs css t
    assume "\<Gamma>\<turnstile>([the (\<Gamma> p)], [], Normal \<sigma>) \<rightarrow>\<^sup>* (Catch c\<^sub>1 c\<^sub>2 # cs, css, Normal Z)"
    also have
      "\<Gamma>\<turnstile>(Catch c\<^sub>1 c\<^sub>2 # cs, css, Normal Z) \<rightarrow> ([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal Z)"
      by (rule step.Catch)
    also
    assume "\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t"
    hence "\<Gamma>\<turnstile>([c\<^sub>1],(cs,c\<^sub>2#cs)#css,Normal Z) \<rightarrow>\<^sup>* ([],(cs,c\<^sub>2#cs)#css,Abrupt t)"
      by (rule exec_impl_steps)
    also
    have "\<Gamma>\<turnstile>([],(cs,c\<^sub>2#cs)#css,Abrupt t) \<rightarrow> (c\<^sub>2#cs,css,Normal t)"
      by (rule step.intros)
    finally
    show "\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)], [], Normal \<sigma>) \<rightarrow>\<^sup>* (c\<^sub>2 # cs, css, Normal t)"
      by iprover
  qed
  moreover
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {t. \<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal Z\<rangle> \<Rightarrow> Abrupt t \<and> 
                  \<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal t\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                  \<Gamma>\<turnstile>the (\<Gamma> p) \<down> Normal \<sigma> \<and>
                  (\<exists>cs css. \<Gamma>\<turnstile>([the (\<Gamma> p)],[],Normal \<sigma>) \<rightarrow>\<^sup>* (c\<^sub>2# cs, css,Normal t))} 
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
 assumes 
 Call: "\<forall>q \<in> dom \<Gamma>. \<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
                 {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>Call q,Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and> 
                    \<Gamma>\<turnstile>Call q\<down>Normal s \<and> ((s,q),(\<sigma>,p)) \<in> termi_call_steps \<Gamma>}
                 (Call q)
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Normal t},
                {t. \<Gamma>\<turnstile>\<langle>Call q,Normal Z\<rangle> \<Rightarrow> Abrupt t}"
 shows "\<And>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub>  
              ({\<sigma>} \<inter> {s. s=Z \<and> \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal s\<rangle> \<Rightarrow>\<notin>({Stuck} \<union> Fault ` (-F)) \<and>  
                                 \<Gamma>\<turnstile>the (\<Gamma> p)\<down>Normal s}) 
                 the (\<Gamma> p) 
              {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Normal t},
              {t. \<Gamma>\<turnstile>\<langle>the (\<Gamma> p),Normal Z\<rangle> \<Rightarrow> Abrupt t}"
apply (rule conseqPre)
apply (rule Call_lemma')
apply (rule Call)
apply blast
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
apply blast
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
      apply (rule Call_lemma [rule_format])
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

end