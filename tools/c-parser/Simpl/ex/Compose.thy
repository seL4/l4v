(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Compose.thy
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

section "Experiments on State Composition"


theory Compose imports "../HoareTotalProps" begin

text {*
We develop some theory to support state-space modular development of programs.
These experiments aim at the representation of state-spaces with records.
If we use @{text "statespaces"} instead we get this kind of compositionality for free.
*}


subsection {* Changing the State-Space *}

(* Lift a command on statespace 'b to work on statespace 'a *)
 
definition lift\<^sub>f:: "('S \<Rightarrow> 's) \<Rightarrow> ('S \<Rightarrow> 's \<Rightarrow> 'S) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('S \<Rightarrow> 'S)"
  where "lift\<^sub>f prj inject f = (\<lambda>S. inject S (f (prj S)))"

definition lift\<^sub>s:: "('S \<Rightarrow> 's) \<Rightarrow> 's set \<Rightarrow> 'S set"
  where "lift\<^sub>s prj A = {S. prj S \<in> A}"

definition lift\<^sub>r:: "('S \<Rightarrow> 's) \<Rightarrow> ('S \<Rightarrow> 's \<Rightarrow> 'S) \<Rightarrow> ('s \<times> 's) set 
                       \<Rightarrow> ('S \<times> 'S) set"
where
"lift\<^sub>r prj inject R = {(S,T). (prj S,prj T) \<in> R \<and> T=inject S (prj T)}"


primrec lift\<^sub>c:: "('S \<Rightarrow> 's) \<Rightarrow> ('S \<Rightarrow> 's \<Rightarrow> 'S) \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('S,'p,'f) com"
where
"lift\<^sub>c prj inject Skip = Skip" |
"lift\<^sub>c prj inject (Basic f) = Basic (lift\<^sub>f prj inject f)" |
"lift\<^sub>c prj inject (Spec r) = Spec (lift\<^sub>r prj inject r)" |
"lift\<^sub>c prj inject (Seq c\<^sub>1 c\<^sub>2)  = 
  (Seq (lift\<^sub>c prj inject c\<^sub>1) (lift\<^sub>c prj inject c\<^sub>2))" |
"lift\<^sub>c prj inject (Cond b c\<^sub>1 c\<^sub>2) = 
  Cond (lift\<^sub>s prj b) (lift\<^sub>c prj inject c\<^sub>1) (lift\<^sub>c prj inject c\<^sub>2)" |
"lift\<^sub>c prj inject (While b c) = 
  While (lift\<^sub>s prj b) (lift\<^sub>c prj inject c)" |
"lift\<^sub>c prj inject (Call p) = Call p" |
"lift\<^sub>c prj inject (DynCom c) = DynCom (\<lambda>s. lift\<^sub>c prj inject (c (prj s)))" |
"lift\<^sub>c prj inject (Guard f g c) = Guard f (lift\<^sub>s prj g) (lift\<^sub>c prj inject c)" |
"lift\<^sub>c prj inject Throw = Throw" |
"lift\<^sub>c prj inject (Catch c\<^sub>1 c\<^sub>2) = 
  Catch (lift\<^sub>c prj inject c\<^sub>1) (lift\<^sub>c prj inject c\<^sub>2)"



lemma lift\<^sub>c_Skip: "(lift\<^sub>c prj inject c = Skip) = (c = Skip)"
  by (cases c) auto 

lemma lift\<^sub>c_Basic: 
  "(lift\<^sub>c prj inject c = Basic lf) = (\<exists>f. c = Basic f \<and> lf = lift\<^sub>f prj inject f)"
  by (cases c) auto

lemma lift\<^sub>c_Spec:
  "(lift\<^sub>c prj inject c = Spec lr) = (\<exists>r. c = Spec r \<and> lr = lift\<^sub>r prj inject r)"
  by (cases c) auto

lemma lift\<^sub>c_Seq: 
  "(lift\<^sub>c prj inject c = Seq lc\<^sub>1 lc\<^sub>2) = 
     (\<exists> c\<^sub>1 c\<^sub>2. c = Seq c\<^sub>1 c\<^sub>2 \<and>
               lc\<^sub>1 = lift\<^sub>c prj inject c\<^sub>1 \<and> lc\<^sub>2 = lift\<^sub>c prj inject c\<^sub>2 )"
    by (cases c) auto

lemma lift\<^sub>c_Cond:
  "(lift\<^sub>c prj inject c = Cond lb lc\<^sub>1 lc\<^sub>2) = 
     (\<exists>b c\<^sub>1 c\<^sub>2. c = Cond b c\<^sub>1 c\<^sub>2 \<and> lb = lift\<^sub>s prj b \<and>
                lc\<^sub>1 = lift\<^sub>c prj inject c\<^sub>1 \<and> lc\<^sub>2 = lift\<^sub>c prj inject c\<^sub>2 )"
  by (cases c) auto

lemma lift\<^sub>c_While:
  "(lift\<^sub>c prj inject c = While lb lc') = 
     (\<exists>b c'. c = While b c' \<and> lb = lift\<^sub>s prj b \<and> 
               lc' = lift\<^sub>c prj inject c')"
  by (cases c) auto

lemma lift\<^sub>c_Call: 
  "(lift\<^sub>c prj inject c = Call p) = (c = Call p)"
  by (cases c) auto

lemma lift\<^sub>c_DynCom:
  "(lift\<^sub>c prj inject c = DynCom lc) = 
     (\<exists>C. c=DynCom C \<and> lc = (\<lambda>s. lift\<^sub>c prj inject (C (prj s))))"
  by (cases c) auto

lemma lift\<^sub>c_Guard: 
  "(lift\<^sub>c prj inject c = Guard f lg lc') =
     (\<exists>g c'. c = Guard f g c' \<and> lg = lift\<^sub>s prj g \<and> 
             lc' = lift\<^sub>c prj inject c')"
   by (cases c) auto

lemma lift\<^sub>c_Throw: 
  "(lift\<^sub>c prj inject c = Throw) = (c = Throw)"
  by (cases c) auto

lemma lift\<^sub>c_Catch: 
  "(lift\<^sub>c prj inject c = Catch lc\<^sub>1 lc\<^sub>2) = 
     (\<exists> c\<^sub>1 c\<^sub>2. c = Catch c\<^sub>1 c\<^sub>2 \<and>
               lc\<^sub>1 = lift\<^sub>c prj inject c\<^sub>1 \<and> lc\<^sub>2 = lift\<^sub>c prj inject c\<^sub>2 )"
    by (cases c) auto



definition xstate_map:: "('S \<Rightarrow> 's) \<Rightarrow> ('S,'f) xstate \<Rightarrow> ('s,'f) xstate"
where
"xstate_map g x = (case x of
                      Normal s \<Rightarrow> Normal (g s)
                    | Abrupt s \<Rightarrow> Abrupt (g s)
                    | Fault f \<Rightarrow> Fault f
                    | Stuck \<Rightarrow> Stuck)"

lemma xstate_map_simps [simp]:
"xstate_map g (Normal s) = Normal (g s)"
"xstate_map g (Abrupt s) = Abrupt (g s)"
"xstate_map g (Fault f) = (Fault f)"
"xstate_map g Stuck = Stuck"
  by (auto simp add: xstate_map_def)

lemma xstate_map_Normal_conv: 
  "xstate_map g S = Normal s = (\<exists>s'. S=Normal s' \<and> s = g s')"
  by (cases S) auto

lemma xstate_map_Abrupt_conv: 
  "xstate_map g S = Abrupt s = (\<exists>s'. S=Abrupt s' \<and> s = g s')"
  by (cases S) auto

lemma xstate_map_Fault_conv: 
  "xstate_map g S = Fault f = (S=Fault f)"
  by (cases S) auto

lemma xstate_map_Stuck_conv: 
  "xstate_map g S = Stuck = (S=Stuck)"
  by (cases S) auto

lemmas xstate_map_convs = xstate_map_Normal_conv xstate_map_Abrupt_conv
 xstate_map_Fault_conv xstate_map_Stuck_conv

definition state:: "('s,'f) xstate \<Rightarrow> 's"
where
"state x = (case x of
               Normal s \<Rightarrow> s
             | Abrupt s \<Rightarrow> s
             | Fault g \<Rightarrow> undefined
             | Stuck \<Rightarrow> undefined)"

lemma state_simps [simp]:
"state (Normal s) = s"
"state (Abrupt s) = s"
  by (auto simp add: state_def )


locale lift_state_space = 
  fixes project::"'S \<Rightarrow> 's"
  fixes "inject"::"'S \<Rightarrow> 's \<Rightarrow> 'S"
  fixes "project\<^sub>x"::"('S,'f) xstate \<Rightarrow> ('s,'f) xstate"
  fixes "lift\<^sub>e"::"('s,'p,'f) body \<Rightarrow> ('S,'p,'f) body"
  fixes lift\<^sub>c:: "('s,'p,'f) com \<Rightarrow> ('S,'p,'f) com"
  fixes lift\<^sub>f:: "('s \<Rightarrow> 's) \<Rightarrow> ('S \<Rightarrow> 'S)"
  fixes lift\<^sub>s:: "'s set \<Rightarrow> 'S set"
  fixes lift\<^sub>r:: "('s \<times> 's) set \<Rightarrow> ('S \<times> 'S) set"
  assumes proj_inj_commute: "\<And>S s.  project (inject S s) = s"
  defines "lift\<^sub>c \<equiv> Compose.lift\<^sub>c project inject"
  defines "project\<^sub>x \<equiv> xstate_map project"
  defines "lift\<^sub>e \<equiv> (\<lambda>\<Gamma> p. map_option lift\<^sub>c (\<Gamma> p))"
  defines "lift\<^sub>f \<equiv> Compose.lift\<^sub>f project inject"
  defines "lift\<^sub>s \<equiv> Compose.lift\<^sub>s project"
  defines "lift\<^sub>r \<equiv> Compose.lift\<^sub>r project inject"


lemma (in lift_state_space) lift\<^sub>f_simp:
 "lift\<^sub>f f \<equiv> \<lambda>S. inject S (f (project S))" 
  by (simp add: lift\<^sub>f_def Compose.lift\<^sub>f_def)

lemma (in lift_state_space) lift\<^sub>s_simp:
  "lift\<^sub>s A \<equiv> {S. project S \<in> A}"
  by  (simp add: lift\<^sub>s_def Compose.lift\<^sub>s_def)

lemma (in lift_state_space) lift\<^sub>r_simp:
"lift\<^sub>r R \<equiv> {(S,T). (project S,project T) \<in> R \<and> T=inject S (project T)}"
  by  (simp add: lift\<^sub>r_def Compose.lift\<^sub>r_def)

(* Causes loop when instantiating locale
lemmas (in lift_state_space) lift\<^sub>f_simp  = Compose.lift\<^sub>f_def 
 [of project "inject", folded lift\<^sub>f_def]
lemmas (in lift_state_space) lift\<^sub>s_simp  = Compose.lift\<^sub>s_def 
 [of project, folded lift\<^sub>s_def]
lemmas (in lift_state_space) lift\<^sub>r_simp  = Compose.lift\<^sub>r_def 
 [of project "inject", folded lift\<^sub>r_def]
*)
lemma (in lift_state_space) lift\<^sub>c_Skip_simp [simp]:
 "lift\<^sub>c Skip = Skip"
  by (simp add: lift\<^sub>c_def)
lemma (in lift_state_space) lift\<^sub>c_Basic_simp [simp]:
"lift\<^sub>c (Basic f) = Basic (lift\<^sub>f f)"
  by (simp add: lift\<^sub>c_def lift\<^sub>f_def)
lemma (in lift_state_space) lift\<^sub>c_Spec_simp [simp]:
"lift\<^sub>c (Spec r) = Spec (lift\<^sub>r r)"
  by (simp add: lift\<^sub>c_def lift\<^sub>r_def)
lemma (in lift_state_space) lift\<^sub>c_Seq_simp [simp]:
"lift\<^sub>c (Seq c\<^sub>1 c\<^sub>2)  = 
  (Seq (lift\<^sub>c c\<^sub>1) (lift\<^sub>c c\<^sub>2))"
  by (simp add: lift\<^sub>c_def)
lemma (in lift_state_space) lift\<^sub>c_Cond_simp [simp]:
"lift\<^sub>c (Cond b c\<^sub>1 c\<^sub>2) = 
  Cond (lift\<^sub>s b) (lift\<^sub>c c\<^sub>1) (lift\<^sub>c c\<^sub>2)"
  by (simp add: lift\<^sub>c_def lift\<^sub>s_def)
lemma (in lift_state_space) lift\<^sub>c_While_simp [simp]:
"lift\<^sub>c (While b c) = 
  While (lift\<^sub>s b) (lift\<^sub>c c)"
  by (simp add: lift\<^sub>c_def lift\<^sub>s_def)
lemma (in lift_state_space) lift\<^sub>c_Call_simp [simp]:
"lift\<^sub>c (Call p) = Call p"
  by (simp add: lift\<^sub>c_def)
lemma (in lift_state_space) lift\<^sub>c_DynCom_simp [simp]:
"lift\<^sub>c (DynCom c) = DynCom (\<lambda>s. lift\<^sub>c (c (project s)))"
  by (simp add: lift\<^sub>c_def)
lemma (in lift_state_space) lift\<^sub>c_Guard_simp [simp]:
"lift\<^sub>c (Guard f g c) = Guard f (lift\<^sub>s g) (lift\<^sub>c c)"
  by (simp add: lift\<^sub>c_def lift\<^sub>s_def)
lemma (in lift_state_space) lift\<^sub>c_Throw_simp [simp]:
"lift\<^sub>c Throw = Throw"
  by (simp add: lift\<^sub>c_def)
lemma (in lift_state_space) lift\<^sub>c_Catch_simp [simp]:
"lift\<^sub>c (Catch c\<^sub>1 c\<^sub>2) = 
  Catch (lift\<^sub>c c\<^sub>1) (lift\<^sub>c c\<^sub>2)"
  by (simp add: lift\<^sub>c_def)

lemma (in lift_state_space) project\<^sub>x_def': 
"project\<^sub>x s \<equiv> (case s of
                 Normal s \<Rightarrow> Normal (project s)
                | Abrupt s \<Rightarrow> Abrupt (project s)
                | Fault f \<Rightarrow> Fault f
                | Stuck \<Rightarrow> Stuck)"
  by (simp add: xstate_map_def project\<^sub>x_def)

lemma (in lift_state_space) lift\<^sub>e_def': 
  "lift\<^sub>e \<Gamma> p \<equiv> (case \<Gamma> p of Some bdy \<Rightarrow> Some (lift\<^sub>c bdy) | None \<Rightarrow> None)"  
  by (simp add: lift\<^sub>e_def map_option_case)




text {*
The problem is that @{term "(lift\<^sub>c project inject \<circ> \<Gamma>)"} is quite
a strong premise. The problem is that @{term "\<Gamma>"} is a function here.
A map would be better. We only have to lift those procedures in the domain
of @{term "\<Gamma>"}:
@{text "\<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' p = Some lift\<^sub>c project inject bdy"}.
We then can com up with theorems that allow us to extend the domains
of @{term \<Gamma>} and preserve validity.
*}


lemma (in lift_state_space) 
"{(S,T). \<exists>t. (project S,t) \<in> r \<and> T=inject S t}
 \<subseteq> {(S,T). (project S,project T) \<in> r \<and> T=inject S (project T)}"
  apply clarsimp
  apply (rename_tac S t)
  apply (simp add: proj_inj_commute)
  done

lemma (in lift_state_space) 
"{(S,T). (project S,project T) \<in> r \<and> T=inject S (project T)} 
 \<subseteq> {(S,T). \<exists>t. (project S,t) \<in> r \<and> T=inject S t}"
  apply clarsimp
  apply (rename_tac S T)
  apply (rule_tac x="project T" in exI)
  apply simp
  done


lemma (in lift_state_space) lift_exec: 
assumes exec_lc: "(lift\<^sub>e \<Gamma>)\<turnstile>\<langle>lc,s\<rangle> \<Rightarrow> t"
shows "\<And>c. \<lbrakk> lift\<^sub>c c = lc\<rbrakk> \<Longrightarrow> 
              \<Gamma>\<turnstile>\<langle>c,project\<^sub>x s\<rangle> \<Rightarrow>  project\<^sub>x t"
using exec_lc
proof (induct)
  case Skip thus ?case
    by (auto simp add: project\<^sub>x_def lift\<^sub>c_Skip lift\<^sub>c_def intro: exec.Skip)
next
  case Guard thus ?case
    by (auto simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def lift\<^sub>c_Guard lift\<^sub>c_def
      intro: exec.Guard)
next
  case GuardFault thus ?case
    by (auto simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def lift\<^sub>c_Guard lift\<^sub>c_def
      intro: exec.GuardFault)
next
  case FaultProp thus ?case
    by (fastforce simp add: project\<^sub>x_def)
next
  case Basic
  thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>c_Basic lift\<^sub>f_def Compose.lift\<^sub>f_def 
      lift\<^sub>c_def
        proj_inj_commute
        intro: exec.Basic)
next
  case Spec
  thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>c_Spec lift\<^sub>f_def Compose.lift\<^sub>f_def  
        lift\<^sub>r_def Compose.lift\<^sub>r_def lift\<^sub>c_def
        proj_inj_commute
        intro: exec.Spec)
next
  case (SpecStuck s r)
  thus ?case
    apply (simp add: project\<^sub>x_def)
    apply (clarsimp simp add: lift\<^sub>c_Spec lift\<^sub>c_def)
    apply (unfold lift\<^sub>r_def Compose.lift\<^sub>r_def)
    apply (rule exec.SpecStuck)
    apply (rule allI)
    apply (erule_tac x="inject s t" in allE)
    apply clarsimp
    apply (simp add: proj_inj_commute)
    done
next
  case Seq 
  thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>c_Seq lift\<^sub>c_def intro: exec.intros)
next
  case CondTrue
  thus ?case
     by (auto simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def lift\<^sub>c_Cond lift\<^sub>c_def
         intro: exec.CondTrue)
next
  case CondFalse
  thus ?case
     by (auto simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def lift\<^sub>c_Cond lift\<^sub>c_def
         intro: exec.CondFalse)
next
  case WhileTrue
  thus ?case
     by (fastforce simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def 
         lift\<^sub>c_While lift\<^sub>c_def
         intro: exec.WhileTrue)
next
  case WhileFalse
  thus ?case
     by (fastforce simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def 
         lift\<^sub>c_While lift\<^sub>c_def
         intro: exec.WhileFalse)
next
  case Call 
  thus ?case
    by (fastforce simp add: 
               project\<^sub>x_def lift\<^sub>c_Call lift\<^sub>f_def Compose.lift\<^sub>f_def lift\<^sub>c_def
               lift\<^sub>e_def
          intro: exec.Call)
next
  case CallUndefined
  thus ?case
    by (fastforce simp add: 
               project\<^sub>x_def lift\<^sub>c_Call lift\<^sub>f_def Compose.lift\<^sub>f_def lift\<^sub>c_def
               lift\<^sub>e_def
          intro: exec.CallUndefined)
next
  case StuckProp thus ?case
    by (fastforce simp add: project\<^sub>x_def)
next
  case DynCom
  thus ?case
    by (fastforce simp add: 
               project\<^sub>x_def lift\<^sub>c_DynCom lift\<^sub>f_def Compose.lift\<^sub>f_def lift\<^sub>c_def
          intro: exec.DynCom)
next
  case Throw thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>c_Throw lift\<^sub>c_def intro: exec.Throw)
next
  case AbruptProp thus ?case
    by (fastforce simp add: project\<^sub>x_def)
next
  case CatchMatch 
  thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>c_Catch lift\<^sub>c_def intro: exec.CatchMatch)
next
  case (CatchMiss c\<^sub>1 s t c\<^sub>2 c) 
  thus ?case
    by (cases t)
       (fastforce simp add: project\<^sub>x_def lift\<^sub>c_Catch lift\<^sub>c_def intro: exec.CatchMiss)+
qed

lemma (in lift_state_space) lift_exec': 
assumes exec_lc: "(lift\<^sub>e \<Gamma>)\<turnstile>\<langle>lift\<^sub>c c,s\<rangle> \<Rightarrow> t"
shows "\<Gamma>\<turnstile>\<langle>c,project\<^sub>x s\<rangle> \<Rightarrow> project\<^sub>x t"
  using lift_exec [OF exec_lc]
  by simp



lemma (in lift_state_space) lift_valid: 
  assumes valid: "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows 
   "(lift\<^sub>e \<Gamma>)\<Turnstile>\<^bsub>/F\<^esub> (lift\<^sub>s P) (lift\<^sub>c c) (lift\<^sub>s Q),(lift\<^sub>s A)"
proof (rule validI)
  fix s t
  assume lexec:
    "(lift\<^sub>e \<Gamma>)\<turnstile>\<langle>lift\<^sub>c c,Normal s\<rangle> \<Rightarrow> t"
  assume lP: "s \<in> lift\<^sub>s P"
  assume noFault: "t \<notin> Fault ` F"
  show "t \<in> Normal ` lift\<^sub>s Q \<union> Abrupt ` lift\<^sub>s A"
  proof -
    from lexec
    have "\<Gamma>\<turnstile> \<langle>c,project\<^sub>x (Normal s)\<rangle> \<Rightarrow> (project\<^sub>x t)"
      by (rule lift_exec) (simp_all)
    moreover
    from lP have "project s \<in> P"
      by (simp add: lift\<^sub>s_def Compose.lift\<^sub>s_def project\<^sub>x_def)
    ultimately 
    have "project\<^sub>x t \<in> Normal ` Q \<union> Abrupt ` A"
      using valid noFault
      apply (clarsimp simp add: valid_def project\<^sub>x_def)
      apply (cases t)
      apply auto
      done
    thus ?thesis
      apply (simp add: lift\<^sub>s_def Compose.lift\<^sub>s_def)
      apply (cases t)
      apply (auto simp add: project\<^sub>x_def)
      done
  qed
qed

lemma (in lift_state_space) lift_hoarep: 
  assumes deriv: "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows 
   "(lift\<^sub>e \<Gamma>),{}\<turnstile>\<^bsub>/F\<^esub> (lift\<^sub>s P) (lift\<^sub>c c) (lift\<^sub>s Q),(lift\<^sub>s A)"
apply (rule hoare_complete)
apply (insert hoare_sound [OF deriv])
apply (rule lift_valid)
apply (simp add: cvalid_def)
done

lemma (in lift_state_space) lift_hoarep': 
  "\<forall>Z. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> (P Z) c (Q Z),(A Z) \<Longrightarrow>
    \<forall>Z. (lift\<^sub>e \<Gamma>),{}\<turnstile>\<^bsub>/F\<^esub> (lift\<^sub>s (P Z)) (lift\<^sub>c c) 
                                  (lift\<^sub>s (Q Z)),(lift\<^sub>s (A Z))"
apply (iprover intro: lift_hoarep)
done



lemma (in lift_state_space) lift_termination:
assumes termi: "\<Gamma>\<turnstile>c\<down>s"
shows "\<And>S. project\<^sub>x S = s \<Longrightarrow> 
  lift\<^sub>e \<Gamma> \<turnstile>(lift\<^sub>c c)\<down>S"
  using termi
proof (induct)
  case Skip thus ?case
    by (clarsimp simp add: terminates.Skip project\<^sub>x_def xstate_map_convs)
next
  case Basic thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs intro: terminates.intros) 
next
  case Spec thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs intro: terminates.intros) 
next
  case Guard thus ?case
    by (auto simp add: project\<^sub>x_def xstate_map_convs intro: terminates.intros) 
next
  case GuardFault thus ?case
    by (auto simp add: project\<^sub>x_def xstate_map_convs lift\<^sub>s_def Compose.lift\<^sub>s_def
           intro: terminates.intros) 
next
  case Fault thus ?case by (clarsimp simp add: project\<^sub>x_def xstate_map_convs)
next
  case (Seq c1 s c2)
  have "project\<^sub>x S = Normal s" by fact
  then obtain s' where S: "S=Normal s'" and s: "s = project s'"
    by (auto simp add: project\<^sub>x_def xstate_map_convs)
  from Seq have "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c1 \<down> S"
    by simp
  moreover
  {
    fix w
    assume exec_lc1: "lift\<^sub>e \<Gamma>\<turnstile>\<langle>lift\<^sub>c c1,Normal s'\<rangle> \<Rightarrow> w"
    have "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c2 \<down> w"
    proof (cases w)
      case (Normal w')
      with lift_exec [where c=c1, OF exec_lc1] s
      have "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> Normal (project w')"
        by (simp add: project\<^sub>x_def)
      from Seq.hyps (3) [rule_format, OF this] Normal
      show "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c2 \<down> w"
        by (auto simp add: project\<^sub>x_def xstate_map_convs)
    qed (auto)
  }
  ultimately show ?case
    using S s
    by (auto intro: terminates.intros)
next
  case CondTrue thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def xstate_map_convs 
      intro: terminates.intros) 
next
  case CondFalse thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def xstate_map_convs 
      intro: terminates.intros) 
next
  case (WhileTrue s b c)
  have "project\<^sub>x S = Normal s" by fact
  then obtain s' where S: "S=Normal s'" and s: "s = project s'"
    by (auto simp add: project\<^sub>x_def xstate_map_convs)
  from WhileTrue have "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c \<down> S"
    by simp
  moreover
  {
    fix w
    assume exec_lc: "lift\<^sub>e \<Gamma>\<turnstile>\<langle>lift\<^sub>c c,Normal s'\<rangle> \<Rightarrow> w"
    have "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c (While b c) \<down> w"
    proof (cases w)
      case (Normal w')
      with lift_exec [where c=c, OF exec_lc] s
      have "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal (project w')"
        by (simp add: project\<^sub>x_def)
      from WhileTrue.hyps (4) [rule_format, OF this] Normal
      show "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c (While b c) \<down> w"
        by (auto simp add: project\<^sub>x_def xstate_map_convs)
    qed (auto)
  }
  ultimately show ?case
    using S s
    by (auto intro: terminates.intros)      
next
  case WhileFalse thus ?case
    by (fastforce simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def xstate_map_convs 
      intro: terminates.intros) 
next
  case Call thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs lift\<^sub>e_def
      intro: terminates.intros) 
next
  case CallUndefined thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs lift\<^sub>e_def
      intro: terminates.intros) 
next
  case Stuck thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs)
next
  case DynCom thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs 
      intro: terminates.intros)
next
  case Throw thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs 
      intro: terminates.intros)
next
  case Abrupt thus ?case
    by (fastforce simp add: project\<^sub>x_def xstate_map_convs 
      intro: terminates.intros)
next
  case (Catch c1 s c2) 
  have "project\<^sub>x S = Normal s" by fact
  then obtain s' where S: "S=Normal s'" and s: "s = project s'"
    by (auto simp add: project\<^sub>x_def xstate_map_convs)
  from Catch have "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c1 \<down> S"
    by simp
  moreover
  {
    fix w
    assume exec_lc1: "lift\<^sub>e \<Gamma>\<turnstile>\<langle>lift\<^sub>c c1,Normal s'\<rangle> \<Rightarrow> Abrupt w"
    have "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c2 \<down> Normal w"
    proof -
      from lift_exec [where c=c1, OF exec_lc1] s
      have "\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> \<Rightarrow> Abrupt (project w)"
        by (simp add: project\<^sub>x_def)
      from Catch.hyps (3) [rule_format, OF this] 
      show "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c2 \<down> Normal w"
        by (auto simp add: project\<^sub>x_def xstate_map_convs)
    qed
  }
  ultimately show ?case
    using S s
    by (auto intro: terminates.intros)
qed

lemma (in lift_state_space) lift_termination':
assumes termi: "\<Gamma>\<turnstile>c\<down>project\<^sub>x S"
shows "lift\<^sub>e \<Gamma> \<turnstile>(lift\<^sub>c c)\<down>S"
  using lift_termination [OF termi]
  by iprover


lemma (in lift_state_space) lift_validt: 
  assumes valid: "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "(lift\<^sub>e \<Gamma>)\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> (lift\<^sub>s P) (lift\<^sub>c c) (lift\<^sub>s Q),(lift\<^sub>s A)"
proof -
  from valid
  have "(lift\<^sub>e \<Gamma>)\<Turnstile>\<^bsub>/F\<^esub> (lift\<^sub>s P) (lift\<^sub>c c) (lift\<^sub>s Q),(lift\<^sub>s A)"
    by (auto intro: lift_valid simp add: validt_def)
  moreover
  {
    fix S
    assume "S \<in> lift\<^sub>s P"
    hence "project S \<in> P"
      by (simp add: lift\<^sub>s_def Compose.lift\<^sub>s_def)
    with valid have "\<Gamma>\<turnstile>c \<down> project\<^sub>x (Normal S)"
      by (simp add: validt_def project\<^sub>x_def)
    hence "lift\<^sub>e \<Gamma>\<turnstile>lift\<^sub>c c \<down> Normal S"
      by (rule lift_termination')
  }
  ultimately show ?thesis
    by (simp add: validt_def)
qed

lemma (in lift_state_space) lift_hoaret: 
  assumes deriv: "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows 
   "(lift\<^sub>e \<Gamma>),{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (lift\<^sub>s P) (lift\<^sub>c c) (lift\<^sub>s Q),(lift\<^sub>s A)"
apply (rule hoaret_complete)
apply (insert hoaret_sound [OF deriv])
apply (rule lift_validt)
apply (simp add: cvalidt_def)
done
    
  
locale lift_state_space_ext = lift_state_space +
  assumes inj_proj_commute: "\<And>S. inject S (project S) = S"
  assumes inject_last: "\<And>S s t. inject (inject S s) t = inject S t"


(* \<exists>x. state t = inject (state s) x *)
lemma (in lift_state_space_ext) lift_exec_inject_same: 
assumes exec_lc: "(lift\<^sub>e \<Gamma>)\<turnstile>\<langle>lc,s\<rangle> \<Rightarrow> t"
shows "\<And>c. \<lbrakk>lift\<^sub>c c = lc; t \<notin> (Fault ` UNIV) \<union> {Stuck}\<rbrakk> \<Longrightarrow> 
              state t = inject (state s) (project (state t))"
using exec_lc
proof (induct)
  case Skip thus ?case
    by (clarsimp simp add: inj_proj_commute)
next
  case Guard thus ?case
    by (clarsimp simp add: lift\<^sub>c_Guard lift\<^sub>c_def)
next
  case GuardFault thus ?case
    by simp
next
  case FaultProp thus ?case by simp
next
  case Basic thus ?case
    by (clarsimp simp add: lift\<^sub>f_def Compose.lift\<^sub>f_def 
        proj_inj_commute lift\<^sub>c_Basic lift\<^sub>c_def)
next
  case (Spec r) thus ?case
    by (clarsimp simp add: Compose.lift\<^sub>r_def lift\<^sub>c_Spec lift\<^sub>c_def)
next
  case SpecStuck
  thus ?case by simp
next
  case (Seq lc1 s s' lc2 t c) 
  have t: "t \<notin> Fault ` UNIV \<union> {Stuck}" by fact
  have "lift\<^sub>c c = Seq lc1 lc2" by fact
  then obtain c1 c2 where
    c: "c = Seq c1 c2" and
    lc1: "lc1 = lift\<^sub>c c1" and
    lc2: "lc2 = lift\<^sub>c c2"
    by (auto simp add: lift\<^sub>c_Seq lift\<^sub>c_def)
  show ?case
  proof (cases s')
    case (Normal s'')
    from Seq.hyps (2) [OF lc1 [symmetric]] this
    have "s'' = inject s (project s'')"
      by auto
    moreover from Seq.hyps (4) [OF lc2 [symmetric]] Normal t 
    have "state t = inject s'' (project (state t))"
      by auto
    ultimately have "state t = inject (inject s (project s'')) (project (state t))"
      by simp
    then show ?thesis
      by (simp add: inject_last)
  next
    case (Abrupt s'')
    from Seq.hyps (2) [OF lc1 [symmetric]] this
    have "s'' = inject s (project s'')"
      by auto
    moreover from Seq.hyps (4) [OF lc2 [symmetric]] Abrupt t 
    have "state t = inject s'' (project (state t))"
      by auto
    ultimately have "state t = inject (inject s (project s'')) (project (state t))"
      by simp
    then show ?thesis
      by (simp add: inject_last)
  next
    case (Fault f)
    with Seq
    have "t = Fault f"
      by (auto dest: Fault_end)
    with t have False by simp
    thus ?thesis ..
  next
    case Stuck
    with Seq
    have "t = Stuck"
      by (auto dest: Stuck_end)
    with t have False by simp
    thus ?thesis ..
  qed
next
  case CondTrue thus ?case
    by (clarsimp simp add: lift\<^sub>c_Cond lift\<^sub>c_def)
next
  case CondFalse thus ?case
    by (clarsimp simp add: lift\<^sub>c_Cond lift\<^sub>c_def)
next
  case (WhileTrue s lb lc' s' t c)
  have t: "t \<notin> Fault ` UNIV \<union> {Stuck}" by fact
  have lw: "lift\<^sub>c c = While lb lc'" by fact
  then obtain b c' where 
    c: "c = While b c'" and
    lb: "lb = lift\<^sub>s b" and
    lc: "lc' = lift\<^sub>c c'"
    by (auto simp add: lift\<^sub>c_While lift\<^sub>s_def lift\<^sub>c_def)
  show ?case
  proof (cases s')
    case (Normal s'')
    from WhileTrue.hyps (3) [OF lc [symmetric]] this
    have "s'' = inject s (project s'')"
      by auto
    moreover from WhileTrue.hyps (5) [OF lw] Normal t 
    have "state t = inject s'' (project (state t))"
      by auto
    ultimately have "state t = inject (inject s (project s'')) (project (state t))"
      by simp
    then show ?thesis
      by (simp add: inject_last)
  next
    case (Abrupt s'')
    from WhileTrue.hyps (3) [OF lc [symmetric]] this
    have "s'' = inject s (project s'')"
      by auto
    moreover from WhileTrue.hyps (5) [OF lw] Abrupt t 
    have "state t = inject s'' (project (state t))"
      by auto
    ultimately have "state t = inject (inject s (project s'')) (project (state t))"
      by simp
    then show ?thesis
      by (simp add: inject_last)
  next
    case (Fault f)
    with WhileTrue
    have "t = Fault f"
      by (auto dest: Fault_end)
    with t have False by simp
    thus ?thesis ..
  next
    case Stuck
    with WhileTrue
    have "t = Stuck"
      by (auto dest: Stuck_end)
    with t have False by simp
    thus ?thesis ..
  qed
next
  case WhileFalse thus ?case
    by (clarsimp simp add: lift\<^sub>c_While inj_proj_commute)
next
  case Call thus ?case
    by (clarsimp simp add: inject_last lift\<^sub>c_Call lift\<^sub>e_def lift\<^sub>c_def)
next
  case CallUndefined thus ?case by simp
next
  case StuckProp thus ?case by simp
next
  case DynCom
  thus ?case
    by (clarsimp simp add: lift\<^sub>c_DynCom lift\<^sub>c_def)
next
  case Throw thus ?case
    by (simp add: inj_proj_commute)
next
  case AbruptProp thus ?case by (simp add: inj_proj_commute)
next
  case (CatchMatch lc1 s s' lc2 t c) 
  have t: "t \<notin> Fault ` UNIV \<union> {Stuck}" by fact
  have "lift\<^sub>c c = Catch lc1 lc2" by fact
  then obtain c1 c2 where
    c: "c = Catch c1 c2" and
    lc1: "lc1 = lift\<^sub>c c1" and
    lc2: "lc2 = lift\<^sub>c c2"
    by (auto simp add: lift\<^sub>c_Catch lift\<^sub>c_def)
  from CatchMatch.hyps (2) [OF lc1 [symmetric]] this
  have "s' = inject s (project s')"
    by auto
  moreover
  from CatchMatch.hyps (4) [OF lc2 [symmetric]] t
  have "state t = inject s' (project (state t))"
    by auto
  ultimately have "state t = inject (inject s (project s')) (project (state t))"
    by simp
  then show ?case
    by (simp add: inject_last)
next
  case CatchMiss
  thus ?case
    by (clarsimp simp add: lift\<^sub>c_Catch lift\<^sub>c_def)
qed

lemma (in lift_state_space_ext) valid_inject_project:
 assumes noFaultStuck: 
  "\<Gamma>\<turnstile>\<langle>c,Normal (project \<sigma>)\<rangle> \<Rightarrow>\<notin>(Fault ` UNIV \<union> {Stuck})"
 shows "lift\<^sub>e \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> {\<sigma>} lift\<^sub>c c 
                {t. t=inject \<sigma> (project t)}, {t. t=inject \<sigma> (project t)}"
proof (rule validI)
  fix s t
  assume exec: "lift\<^sub>e \<Gamma>\<turnstile>\<langle>lift\<^sub>c c,Normal s\<rangle> \<Rightarrow> t"
  assume P: "s \<in> {\<sigma>}"
  assume noFault: "t \<notin> Fault ` F"
  show "t \<in> Normal ` {t. t = inject \<sigma> (project t)} \<union> 
        Abrupt ` {t. t = inject \<sigma> (project t)}"
  proof -
    from lift_exec [OF exec]
    have "\<Gamma>\<turnstile>\<langle>c,project\<^sub>x (Normal s)\<rangle> \<Rightarrow> project\<^sub>x t"
      by simp
    with noFaultStuck P have t: "t \<notin> Fault ` UNIV \<union> {Stuck}"
      by (auto simp add: final_notin_def project\<^sub>x_def)
    from lift_exec_inject_same [OF exec refl this] P
    have "state t = inject \<sigma> (project (state t))"
      by simp
    with t show ?thesis
      by (cases t) auto
  qed
qed

lemma (in lift_state_space_ext) lift_exec_inject_same': 
assumes exec_lc: "(lift\<^sub>e \<Gamma>)\<turnstile>\<langle>lift\<^sub>c c,S\<rangle> \<Rightarrow> T"
shows "\<And>c. \<lbrakk>T \<notin> (Fault ` UNIV) \<union> {Stuck}\<rbrakk> \<Longrightarrow> 
              state T = inject (state S) (project (state T))"
  using lift_exec_inject_same [OF exec_lc]
  by simp

lemma (in lift_state_space_ext) valid_lift_modifies:
  assumes valid: "\<forall>s. \<Gamma>\<Turnstile>\<^bsub>/F\<^esub> {s} c (Modif s),(ModifAbr s)"
  shows "(lift\<^sub>e \<Gamma>)\<Turnstile>\<^bsub>/F\<^esub> {S} (lift\<^sub>c c) 
           {T. T \<in> lift\<^sub>s (Modif (project S)) \<and> T=inject S (project T)},
           {T. T \<in> lift\<^sub>s (ModifAbr (project S)) \<and> T=inject S (project T)}"
proof (rule validI)
  fix s t
  assume exec: "lift\<^sub>e \<Gamma>\<turnstile>\<langle>lift\<^sub>c c,Normal s\<rangle> \<Rightarrow> t"
  assume P: "s \<in> {S}"
  assume noFault: "t \<notin> Fault ` F"
  show "t \<in> Normal `
                 {t \<in> lift\<^sub>s (Modif (project S)).
                  t = inject S (project t)} \<union>
                 Abrupt `
                 {t \<in> lift\<^sub>s (ModifAbr (project S)).
                  t = inject S (project t)}"
  proof -
    from lift_exec [OF exec]
    have "\<Gamma>\<turnstile> \<langle>c,project\<^sub>x (Normal s)\<rangle> \<Rightarrow> project\<^sub>x t"
      by auto
    moreover
    from noFault have "project\<^sub>x t \<notin> Fault ` F"
      by (cases "t") (auto simp add: project\<^sub>x_def)
    ultimately   
    have "project\<^sub>x t \<in> 
            Normal ` (Modif (project s)) \<union> Abrupt ` (ModifAbr (project s))"
      using valid [rule_format, of "(project s)"]
      by (auto simp add: valid_def project\<^sub>x_def)
    hence "t \<in> Normal ` lift\<^sub>s (Modif (project s)) \<union> 
               Abrupt ` lift\<^sub>s (ModifAbr (project s))"
      by (cases t) (auto simp add: project\<^sub>x_def lift\<^sub>s_def Compose.lift\<^sub>s_def)
    moreover
    from this
    have "t \<notin> Fault ` UNIV \<union> {Stuck}"
      by (cases t) auto
    from lift_exec_inject_same [OF exec _ this]
    have "state t = inject (state (Normal s)) (project (state t))"
      by simp
    ultimately show ?thesis
      using P by auto
  qed
qed

lemma (in lift_state_space_ext) hoare_lift_modifies:
  assumes deriv: "\<forall>\<sigma>. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<forall>\<sigma>. (lift\<^sub>e \<Gamma>),{}\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} (lift\<^sub>c c) 
           {T. T \<in> lift\<^sub>s (Modif (project \<sigma>)) \<and> T=inject \<sigma> (project T)},
           {T. T \<in> lift\<^sub>s (ModifAbr (project \<sigma>)) \<and> T=inject \<sigma> (project T)}"
apply (rule allI)
apply (rule hoare_complete)
apply (rule valid_lift_modifies)
apply (rule allI)
apply (insert hoare_sound [OF deriv [rule_format]])
apply (simp add: cvalid_def)
done

lemma (in lift_state_space_ext) hoare_lift_modifies':
  assumes deriv: "\<forall>\<sigma>. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} c (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<forall>\<sigma>. (lift\<^sub>e \<Gamma>),{}\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} (lift\<^sub>c c) 
           {T. T \<in> lift\<^sub>s (Modif (project \<sigma>)) \<and> 
                   (\<exists>T'. T=inject \<sigma> T')},
           {T. T \<in> lift\<^sub>s (ModifAbr (project \<sigma>)) \<and> 
                   (\<exists>T'. T=inject \<sigma> T')}"
apply (rule allI)
apply (rule HoarePartialDef.conseq [OF hoare_lift_modifies [OF deriv]])
apply blast
done

subsection {* Renaming Procedures *}

primrec rename:: "('p \<Rightarrow> 'q) \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'q,'f) com"
where
"rename N Skip = Skip" |
"rename N (Basic f) = Basic f" |
"rename N (Spec r) = Spec r" |
"rename N (Seq c\<^sub>1 c\<^sub>2)  = (Seq (rename N c\<^sub>1) (rename N c\<^sub>2))" |
"rename N (Cond b c\<^sub>1 c\<^sub>2) = Cond b (rename N c\<^sub>1) (rename N c\<^sub>2)" |
"rename N (While b c) = While b (rename N c)" |
"rename N (Call p) = Call (N p)" |
"rename N (DynCom c) = DynCom (\<lambda>s. rename N (c s))" |
"rename N (Guard f g c) = Guard f g (rename N c)" |
"rename N Throw = Throw" |
"rename N (Catch c\<^sub>1 c\<^sub>2) = Catch (rename N c\<^sub>1) (rename N c\<^sub>2)"

lemma rename_Skip: "rename h c = Skip = (c=Skip)"
  by (cases c) auto

lemma rename_Basic: 
  "(rename h c = Basic f) = (c=Basic f)"
  by (cases c) auto

lemma rename_Spec:
  "(rename h c = Spec r) = (c=Spec r)"
  by (cases c) auto

lemma rename_Seq: 
  "(rename h c = Seq rc\<^sub>1 rc\<^sub>2) = 
     (\<exists> c\<^sub>1 c\<^sub>2. c = Seq c\<^sub>1 c\<^sub>2 \<and>
               rc\<^sub>1 = rename h c\<^sub>1 \<and> rc\<^sub>2 = rename h c\<^sub>2 )"
    by (cases c) auto

lemma rename_Cond:
  "(rename h c = Cond b rc\<^sub>1 rc\<^sub>2) = 
     (\<exists>c\<^sub>1 c\<^sub>2. c = Cond b c\<^sub>1 c\<^sub>2  \<and> rc\<^sub>1 = rename h c\<^sub>1 \<and> rc\<^sub>2 = rename h c\<^sub>2 )"
  by (cases c) auto

lemma rename_While:
  "(rename h c = While b rc') = (\<exists>c'. c = While b c' \<and> rc' = rename h c')"
  by (cases c) auto

lemma rename_Call: 
  "(rename h c = Call q) = (\<exists>p. c = Call p \<and> q=h p)"
  by (cases c) auto

lemma rename_DynCom:
  "(rename h c = DynCom rc) = (\<exists>C. c=DynCom C \<and> rc = (\<lambda>s. rename h (C s)))"
  by (cases c) auto

lemma rename_Guard: 
  "(rename h c = Guard f g rc') =
     (\<exists>c'. c = Guard f g c' \<and> rc' = rename h c')"
   by (cases c) auto

lemma rename_Throw: 
  "(rename h c = Throw) = (c = Throw)"
  by (cases c) auto

lemma rename_Catch: 
  "(rename h c = Catch rc\<^sub>1 rc\<^sub>2) = 
     (\<exists>c\<^sub>1 c\<^sub>2. c = Catch c\<^sub>1 c\<^sub>2 \<and> rc\<^sub>1 = rename h c\<^sub>1 \<and> rc\<^sub>2 = rename h c\<^sub>2 )"
    by (cases c) auto

lemma exec_rename_to_exec:
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (h p) = Some (rename h bdy)"
  assumes exec: "\<Gamma>'\<turnstile>\<langle>rc,s\<rangle> \<Rightarrow> t"
  shows "\<And>c. rename h c = rc\<Longrightarrow>  \<exists>t'. \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t' \<and> (t'=Stuck \<or> t'=t)"
using exec
proof (induct)
  case Skip thus ?case by (fastforce intro: exec.intros simp add: rename_Skip)
next
  case Guard thus ?case by (fastforce intro: exec.intros simp add: rename_Guard)
next
  case GuardFault thus ?case by (fastforce intro: exec.intros simp add: rename_Guard)
next
  case FaultProp thus ?case by (fastforce intro: exec.intros)
next
  case Basic thus ?case by (fastforce intro: exec.intros simp add: rename_Basic)
next
  case Spec thus ?case by (fastforce intro: exec.intros simp add: rename_Spec)
next
  case SpecStuck thus ?case by (fastforce intro: exec.intros simp add: rename_Spec)
next
  case Seq thus ?case by (fastforce intro: exec.intros simp add: rename_Seq)
next
  case CondTrue thus ?case by (fastforce intro: exec.intros simp add: rename_Cond)
next
  case CondFalse thus ?case by (fastforce intro: exec.intros simp add: rename_Cond)
next
  case WhileTrue thus ?case by (fastforce intro: exec.intros simp add: rename_While)
next
  case WhileFalse thus ?case by (fastforce intro: exec.intros simp add: rename_While)
next
  case (Call p rbdy s t)
  have rbdy: "\<Gamma>' p = Some rbdy" by fact
  have "rename h c = Call p" by fact
  then obtain q where c: "c=Call q" and p: "p=h q"
    by (auto simp add: rename_Call)
  show ?case
  proof (cases "\<Gamma> q")
    case None
    with c show ?thesis by (auto intro: exec.CallUndefined)
  next
    case (Some bdy)
    from \<Gamma> [rule_format, OF this] p rbdy
    have "rename h bdy = rbdy" by simp
    with Call.hyps c Some
    show ?thesis
      by (fastforce intro: exec.intros)
  qed
next
  case (CallUndefined p s)
  have undef: "\<Gamma>' p = None" by fact
  have "rename h c = Call p" by fact
  then obtain q where c: "c=Call q" and p: "p=h q"
    by (auto simp add: rename_Call)
  from undef p \<Gamma> have "\<Gamma> q = None"
    by (cases "\<Gamma> q") auto
  with p c show ?case
    by (auto intro: exec.intros)
next
  case StuckProp thus ?case by (fastforce intro: exec.intros)
next
  case DynCom thus ?case by (fastforce intro: exec.intros simp add: rename_DynCom)
next
  case Throw thus ?case by (fastforce intro: exec.intros simp add: rename_Throw)
next
  case AbruptProp thus ?case by (fastforce intro: exec.intros)
next
  case CatchMatch thus ?case by (fastforce intro: exec.intros simp add: rename_Catch)
next
  case CatchMiss thus ?case by (fastforce intro: exec.intros simp add: rename_Catch)
qed



lemma exec_rename_to_exec':
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes exec: "\<Gamma>'\<turnstile>\<langle>rename N c,s\<rangle> \<Rightarrow> t"
  shows "\<exists>t'. \<Gamma>\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t' \<and> (t'=Stuck \<or> t'=t)"
  using exec_rename_to_exec [OF \<Gamma> exec]
  by  auto


    
lemma valid_to_valid_rename:
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes valid: "\<Gamma>\<Turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>'\<Turnstile>\<^bsub>/F\<^esub> P (rename N c) Q,A"
proof (rule validI)
  fix s t
  assume execr: "\<Gamma>'\<turnstile> \<langle>rename N c,Normal s\<rangle> \<Rightarrow> t" 
  assume P: "s \<in> P" 
  assume noFault: "t \<notin> Fault ` F"
  show "t \<in> Normal ` Q \<union> Abrupt ` A"
  proof -
    from exec_rename_to_exec [OF \<Gamma> execr] 
    obtain t' where
      exec: "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t'"  and t': "(t' = Stuck \<or> t' = t)"
      by auto
    with valid noFault P show ?thesis
      by (auto simp add: valid_def)
  qed
qed

lemma hoare_to_hoare_rename:
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes deriv: "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>',{}\<turnstile>\<^bsub>/F\<^esub> P (rename N c) Q,A"
apply (rule hoare_complete)
apply (insert hoare_sound [OF deriv])
apply (rule valid_to_valid_rename)
apply  (rule \<Gamma>)
apply (simp add: cvalid_def)
done

lemma hoare_to_hoare_rename':
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes deriv: "\<forall>Z. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> (P Z) c (Q Z),(A Z)"
  shows "\<forall>Z. \<Gamma>',{}\<turnstile>\<^bsub>/F\<^esub> (P Z) (rename N c) (Q Z),(A Z)"
apply rule
apply (rule hoare_to_hoare_rename [OF \<Gamma>])
apply (rule deriv[rule_format])
done

lemma terminates_to_terminates_rename:
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes termi: "\<Gamma>\<turnstile> c \<down> s"
  assumes noStuck: "\<Gamma>\<turnstile> \<langle>c,s\<rangle> \<Rightarrow>\<notin>{Stuck}" 
  shows "\<Gamma>'\<turnstile> rename N c \<down> s"
using termi noStuck
proof (induct)
  case Skip thus ?case by (fastforce intro: terminates.intros)
next
  case Basic thus ?case by (fastforce intro: terminates.intros)
next
  case Spec thus ?case by (fastforce intro: terminates.intros)
next
  case Guard thus ?case by (fastforce intro: terminates.intros 
    simp add: final_notin_def exec.intros)
next
  case GuardFault thus ?case by (fastforce intro: terminates.intros)
next
  case Fault thus ?case by (fastforce intro: terminates.intros)
next
  case Seq
  thus ?case
    by (force intro!: terminates.intros exec.intros dest: exec_rename_to_exec [OF \<Gamma>]
         simp add: final_notin_def)
next
  case CondTrue thus ?case by (fastforce intro: terminates.intros 
    simp add: final_notin_def exec.intros)
next
  case CondFalse thus ?case by (fastforce intro: terminates.intros 
    simp add: final_notin_def exec.intros)
next
  case (WhileTrue s b c)
  have s_in_b: "s \<in> b" by fact
  have noStuck: "\<Gamma>\<turnstile> \<langle>While b c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}" by fact
  with s_in_b have "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
    by (auto simp add: final_notin_def intro: exec.intros)
  with WhileTrue.hyps have "\<Gamma>'\<turnstile>rename N c \<down> Normal s"
    by simp
  moreover
  {
    fix t
    assume exec_rc: "\<Gamma>'\<turnstile> \<langle>rename N c,Normal s\<rangle> \<Rightarrow> t"
    have "\<Gamma>'\<turnstile> While b (rename N c) \<down> t"
    proof -
      from exec_rename_to_exec [OF \<Gamma> exec_rc] obtain t'
        where exec_c: "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> t'" and t': "(t' = Stuck \<or> t' = t)"
        by auto
      with s_in_b noStuck obtain "t'=t" and "\<Gamma>\<turnstile> \<langle>While b c,t\<rangle> \<Rightarrow>\<notin>{Stuck}"
        by (auto simp add: final_notin_def intro: exec.intros)
      with exec_c WhileTrue.hyps
      show ?thesis
        by auto
    qed
  }
  ultimately show ?case
    using s_in_b
    by (auto intro: terminates.intros)
next
  case WhileFalse thus ?case by (fastforce intro: terminates.intros)
next
  case (Call p bdy s)
  have "\<Gamma> p = Some bdy" by fact
  from \<Gamma> [rule_format, OF this]
  have bdy': "\<Gamma>' (N p) = Some (rename N bdy)".
  from Call have "\<Gamma>'\<turnstile>rename N bdy \<down> Normal s"
    by (auto simp add: final_notin_def intro: exec.intros)
  with bdy' have "\<Gamma>'\<turnstile>Call (N p) \<down> Normal s"
    by (auto intro: terminates.intros)
  thus ?case by simp
next
  case (CallUndefined p s)
  have "\<Gamma> p = None" "\<Gamma>\<turnstile> \<langle>Call p,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}" by fact+
  hence False by (auto simp add: final_notin_def intro: exec.intros)
  thus ?case ..
next
  case Stuck thus ?case by (fastforce intro: terminates.intros)
next
  case DynCom thus ?case by (fastforce intro: terminates.intros 
    simp add: final_notin_def exec.intros)
next
  case Throw thus ?case by (fastforce intro: terminates.intros)
next
  case Abrupt thus ?case by (fastforce intro: terminates.intros)
next
  case (Catch c1 s c2)
  have noStuck: "\<Gamma>\<turnstile> \<langle>Catch c1 c2,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}" by fact
  hence "\<Gamma>\<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
    by (fastforce simp add: final_notin_def intro: exec.intros)
  with Catch.hyps have "\<Gamma>'\<turnstile>rename N c1 \<down> Normal s"
    by auto
  moreover
  {
    fix t
    assume exec_rc1:"\<Gamma>'\<turnstile> \<langle>rename N c1,Normal s\<rangle> \<Rightarrow> Abrupt t"
    have "\<Gamma>'\<turnstile>rename N c2 \<down> Normal t"
    proof -
      from exec_rename_to_exec [OF \<Gamma> exec_rc1] obtain t'
        where exec_c: "\<Gamma>\<turnstile> \<langle>c1,Normal s\<rangle> \<Rightarrow> t'" and "(t' = Stuck \<or> t' = Abrupt t)"
        by auto
      with noStuck have t': "t'=Abrupt t" 
        by (fastforce simp add: final_notin_def intro: exec.intros)
      with exec_c noStuck have "\<Gamma>\<turnstile> \<langle>c2,Normal t\<rangle> \<Rightarrow>\<notin>{Stuck}"
        by (auto simp add: final_notin_def intro: exec.intros)
      with exec_c t' Catch.hyps
      show ?thesis
        by auto
    qed
  }
  ultimately show ?case
    by (auto intro: terminates.intros)
qed

lemma validt_to_validt_rename:
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes valid: "\<Gamma>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>'\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> P (rename N c) Q,A"
proof -
  from valid
  have "\<Gamma>'\<Turnstile>\<^bsub>/F\<^esub> P (rename N c) Q,A"
    by (auto intro: valid_to_valid_rename [OF \<Gamma>] simp add: validt_def)
  moreover
  {
    fix s
    assume "s \<in> P"
    with valid obtain "\<Gamma>\<turnstile>c \<down> (Normal s)" "\<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow>\<notin>{Stuck}"
      by (auto simp add: validt_def valid_def final_notin_def)
    from terminates_to_terminates_rename [OF \<Gamma> this]
    have "\<Gamma>'\<turnstile>rename N c \<down> Normal s"
      .
  }
  ultimately show ?thesis
    by (simp add: validt_def)
qed

lemma hoaret_to_hoaret_rename:
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes deriv: "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  shows "\<Gamma>',{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (rename N c) Q,A"
apply (rule hoaret_complete)
apply (insert hoaret_sound [OF deriv])
apply (rule validt_to_validt_rename)
apply  (rule \<Gamma>)
apply (simp add: cvalidt_def)
done

lemma hoaret_to_hoaret_rename':
  assumes \<Gamma>: "\<forall>p bdy. \<Gamma> p = Some bdy \<longrightarrow> \<Gamma>' (N p) = Some (rename N bdy)"
  assumes deriv: "\<forall>Z. \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) c (Q Z),(A Z)"
  shows "\<forall>Z. \<Gamma>',{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) (rename N c) (Q Z),(A Z)"
apply rule
apply (rule hoaret_to_hoaret_rename [OF \<Gamma>])
apply (rule deriv[rule_format])
done

lemma lift\<^sub>c_whileAnno [simp]: "lift\<^sub>c prj inject (whileAnno b I V c) =
    whileAnno (lift\<^sub>s prj b) 
              (lift\<^sub>s prj I) (lift\<^sub>r prj inject V) (lift\<^sub>c prj inject c)"
  by (simp add: whileAnno_def)

lemma lift\<^sub>c_block [simp]: "lift\<^sub>c prj inject (block init bdy return c) = 
  block (lift\<^sub>f prj inject init) (lift\<^sub>c prj inject bdy) 
        (\<lambda>s. (lift\<^sub>f prj inject (return (prj s))))
        (\<lambda>s t. lift\<^sub>c prj inject (c (prj s) (prj t)))"
  by (simp add: block_def)

(*
lemma lift\<^sub>c_block [simp]: "lift\<^sub>c prj inject (block init bdy return c) = 
  block (lift\<^sub>f prj inject init) (lift\<^sub>c prj inject bdy) 
        (\<lambda>s t. inject s (return (prj s) (prj t)))
        (\<lambda>s t. lift\<^sub>c prj inject (c (prj s) (prj t)))"
  apply (simp add: block_def)
  apply (simp add: lift\<^sub>f_def)
*)
lemma lift\<^sub>c_call [simp]: "lift\<^sub>c prj inject (call init p return c) = 
  call (lift\<^sub>f prj inject init) p 
        (\<lambda>s. (lift\<^sub>f prj inject (return (prj s))))
        (\<lambda>s t. lift\<^sub>c prj inject (c (prj s) (prj t)))"
  by (simp add: call_def lift\<^sub>c_block)

lemma rename_whileAnno [simp]: "rename h (whileAnno b I V c) =
   whileAnno b I V (rename h c)"
  by (simp add: whileAnno_def)

lemma rename_block [simp]: "rename h (block init bdy return c) =
  block init (rename h bdy) return (\<lambda>s t. rename h (c s t))"
  by (simp add: block_def)

lemma rename_call [simp]: "rename h (call init p return c) =
  call init (h p) return (\<lambda>s t. rename h (c s t))"
  by (simp add: call_def)


end


