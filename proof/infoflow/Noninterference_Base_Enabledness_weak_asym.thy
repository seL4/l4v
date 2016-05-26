(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Noninterference_Base_Enabledness_weak_asym
imports "../../lib/Simulation"
begin

text {*
  This file contains the final output of Nikolas Stott's work as a visiting
  practicum exchange student in the second half of 2012. It defines
  noninterference conditions for systems that are not ``enabled'' (i.e. where
  not every event is always executable in every state). It defines
  a new unwinding condition for such systems and proves that, with the existing
  unwinding conditions, these imply the noninterference conditions.
  The given unwinding conditions are not equivalent to the noninterference
  conditions (they are strictly stronger), as far as we could tell.
*}

lemma un_eq:
  "\<lbrakk>S = S'; T = T'\<rbrakk> \<Longrightarrow> S \<union> T = S' \<union> T'"
  apply auto
  done

lemma Un_eq:
  "\<lbrakk>\<And> x y. \<lbrakk>x \<in> xs; y \<in> ys\<rbrakk> \<Longrightarrow> P x = Q y; \<exists> x. x \<in> xs; \<exists> y. y \<in> ys\<rbrakk> \<Longrightarrow> (\<Union>x\<in>xs. P x) = (\<Union>y\<in>ys. Q y)"
  apply auto
  done

lemma Int_eq:
  "\<lbrakk>\<And> x y. \<lbrakk>x \<in> xs; y \<in> ys\<rbrakk> \<Longrightarrow> P x = Q y; \<exists> x. x \<in> xs; \<exists> y. y \<in> ys\<rbrakk> \<Longrightarrow> (\<Inter>x\<in>xs. P x) = (\<Inter>y\<in>ys. Q y)"
  apply auto
  done

lemma Un_eq_Int:
  assumes ex: "\<exists> x. x \<in> xs"
  assumes ey: "\<exists> y. y \<in> ys"
  assumes a: "\<And> x y. \<lbrakk>x \<in> xs; y \<in> ys\<rbrakk> \<Longrightarrow> S x = S' y"
  shows "(\<Union>x\<in>xs. S x) = (\<Inter>x\<in>ys. S' x)"
  apply(rule equalityI)
   apply(clarsimp)
   apply(drule a, assumption, simp)
  apply clarsimp
  apply(insert ex ey)
  apply clarsimp
  apply(frule a, assumption)
  apply fastforce
  done

primrec Run :: "('e \<Rightarrow> ('s \<times> 's) set) \<Rightarrow> 'e list \<Rightarrow> ('s \<times> 's) set" where
  "Run Stepf []     = Id" |
  "Run Stepf (a#as) = Stepf a O Run Stepf as"


lemma Run_mid':
  shows
  "\<forall> s u bs. (s,u) \<in> Run Stepf (as @ bs)  \<longrightarrow> (\<exists> t. (s,t) \<in> Run Stepf as \<and> (t,u) \<in> Run Stepf bs)"
  proof(induct as)
  case Nil show ?case
   apply(clarsimp)
   done
  next
  case (Cons a as) show ?case
  apply(clarsimp simp: relcomp_def)
  apply(drule "Cons.hyps"[rule_format])
  apply fastforce
  done
qed

lemma Run_mid:
  "(s,u) \<in> Run Stepf (as @ bs) \<Longrightarrow> (\<exists> t. (s,t) \<in> Run Stepf as \<and> (t,u) \<in> Run Stepf bs)"
  apply(erule Run_mid'[rule_format])
  done

lemma Run_ConsI:
  "\<exists>t. (s,t)\<in>Stepf a \<and>(t,u)\<in> Run Stepf as \<Longrightarrow> (s,u)\<in> Run Stepf (a#as)"
  apply(auto)
  done

lemma Run_ConsD:
  "(s,u) \<in> Run Stepf (a#as) \<Longrightarrow> (\<exists> t. (s,t) \<in> Stepf a \<and> (t,u) \<in> Run Stepf as)"
  apply(subgoal_tac "a#as = [a]@as")
   apply(drule subst,assumption)
   apply(drule Run_mid,simp)
  apply(auto)
  done

lemma Run_trans:
  "\<lbrakk> (s,t) \<in> Run Stepf as; (t,u) \<in> Run Stepf bs \<rbrakk> \<Longrightarrow> (s,u) \<in> Run Stepf (as @ bs)"
  by (induct as arbitrary: s t u bs) auto

lemma Run_app:
  "Run Stepf (as @ bs) = (Run Stepf as) O (Run Stepf bs)"
  apply(rule equalityI)
   apply(fastforce dest: Run_mid)
  apply(fastforce intro: Run_trans)
  done

(* we define the top-level properties for any enabled system *)
locale system =
  fixes A :: "('a,'s,'e) data_type"  
  and s0 :: "'s"  (* an initial state *)

context system begin

definition reachable where
  "reachable s \<equiv> \<exists> js. s \<in> execution A s0 js"

definition Step where
  "Step a \<equiv> {(s,s') . s' \<in> execution A s [a]}"

(* Executable should make sense only if the states are reachable.
   'reachable s' in the second equation is to make sure that the first state of the computation is reachable,
   the following become trivial by future lemma 'reachable_Step' *)
primrec Executable where
"Executable [] s = reachable s"|
"Executable (a#as) s = (reachable s \<and> (\<exists>s'. (s,s') \<in> Step a \<and> Executable as s'))"

(* An alternative definition of Executability for a sequence of actions,
   which, assuming the state is reachable, is equivalent to the previous one (proved later)*)
definition Executable' where
"Executable' as s \<equiv> reachable s \<longrightarrow> (\<exists>t. t\<in>execution A s as)"

definition obs_det where
  "obs_det \<equiv> \<forall> s js. \<exists> s'. execution A s js = {s'}"

lemma obs_detD:
  "obs_det \<Longrightarrow> \<exists> s'. execution A s js = {s'}" by (simp add: obs_det_def)

definition no_abs where
  "no_abs \<equiv> \<forall> x. Init A (Fin A x) = {x}"
   
lemma no_absD:
  "no_abs \<Longrightarrow> Init A (Fin A x) = {x}" by (simp add: no_abs_def)

end

(* we define the unwinding conditions for systems for which a running
   a sequence of events is equivalent to performing a sequence of individual
   steps: one for each event in the sequence in turn  *)
locale Step_system = system A s0
  for A :: "('a,'s,'e) data_type" and s0 :: "'s"  +
  assumes reachable_s0: "reachable s0"
  assumes execution_Run: "reachable s \<Longrightarrow> execution A s as = {s'. (s,s') \<in> Run Step as}"


context Step_system begin

lemma execution_Run':
  "s \<in> execution A s0 js \<Longrightarrow> execution A s as = {s'. (s,s') \<in> Run Step as}"
  apply(rule execution_Run)
  apply(fastforce simp: reachable_def)
  done


lemma reachable_execution:
  "\<lbrakk>reachable s; s' \<in> execution A s js\<rbrakk> \<Longrightarrow> reachable s'"
  apply(clarsimp simp: reachable_def)
  apply(rule_tac x="jsa @ js" in exI)
  apply(frule execution_Run'[where s=s and as=js])
  apply(simp add: execution_Run[where s=s0, simplified reachable_s0])
  apply(fastforce simp: Run_app)
  done


lemma reachable_Step:
  "\<lbrakk>reachable s; (s,s') \<in> Step a\<rbrakk> \<Longrightarrow> reachable s'"
  apply(erule reachable_execution)
  apply(simp add: Step_def)
  done

(*We prove that Executable and Executable' are equivalent*)
lemma Executable'I:
  "\<lbrakk>Executable as s\<rbrakk> \<Longrightarrow> Executable' as s"
  apply(clarsimp simp: Executable'_def)
  apply(induct as arbitrary: s)
   apply(fastforce simp :execution_Run)
  apply(clarsimp)
  apply(drule_tac x=s' in meta_spec)
  apply(frule reachable_Step,assumption)
  apply(fastforce intro:Run_ConsI simp:execution_Run)
  done

lemma Executable'D:
  "\<lbrakk>reachable s; Executable' as s\<rbrakk> \<Longrightarrow> Executable as s"
  apply(clarsimp simp: Executable'_def)
  apply(induct as arbitrary:s)
   apply(simp)
  apply(simp add:execution_Run del: Run.simps)
  apply(blast intro:reachable_Step dest:Run_ConsD)
  done

lemma Executable_Executable'_equiv:
  "reachable s \<Longrightarrow> Executable as s = Executable' as s"
  apply(rule iffI)
   apply(blast intro: Executable'I)
  apply(blast dest: Executable'D)
  done

end

locale Init_Fin_system = system A s0
  for A :: "('a,'s,'e) data_type" and s0 :: "'s"  +
  assumes reachable_s0: "reachable s0"
  assumes Fin_Init: "reachable s \<Longrightarrow> Fin A ` Init A s = {s}"
  assumes Init_Fin: "x \<in> Init A (Fin A x)"
  assumes obs_det_or_no_abs: "obs_det \<or> no_abs"


(* when Init is the inverse image of Fin, the above assumptions are met by a system
   for which Fin is injective, or one that appears deterministic to an observer *)
locale Init_inv_Fin_system = system A s0
  for A :: "('a,'s,'e) data_type" and s0 :: "'s" +
  assumes Fin_Init_s0: "s0 \<in> Fin A ` Init A s0"
  assumes Init_inv_Fin: "Init A s = {s'. Fin A s' = s}"
  assumes Fin_inj: "obs_det \<or> inj (Fin A)"

sublocale Init_inv_Fin_system \<subseteq> Init_Fin_system
  apply(unfold_locales)
     apply(simp add: reachable_def)
     apply(rule_tac x="[]" in exI)
     apply(simp add: execution_def steps_def)
     apply(simp add: Fin_Init_s0)
    apply(simp add: Init_inv_Fin)
    apply(simp add: image_def)
    apply(fastforce simp: reachable_def execution_def)
   apply(simp add: Init_inv_Fin)
  apply(case_tac "obs_det", blast)
  apply(rule disjI2)
  apply(clarsimp simp: no_abs_def Init_inv_Fin)
  apply(insert Fin_inj)
  apply clarsimp
  apply(auto dest: injD)
  done

context Init_Fin_system begin


lemma execution_subset_Run:
  "reachable s \<Longrightarrow> execution A s as \<subseteq> {s'. (s,s') \<in> Run Step as}"
  apply(induct as arbitrary: s rule: rev_induct)
   apply(simp add: execution_def steps_def Fin_Init)
  apply(simp add: execution_def steps_def)
  apply(rule subsetI)
  apply clarsimp
  apply(rule Run_trans)
   apply blast
  apply(cut_tac x=xc in Init_Fin)
  apply(clarsimp simp: Step_def execution_def steps_def)
  apply blast
  done

lemma Run_subset_execution:
  "\<lbrakk>no_abs; reachable s\<rbrakk> \<Longrightarrow> {s'. (s,s') \<in> Run Step as} \<subseteq> execution A s as"
  apply(induct as arbitrary: s rule: rev_induct)
   apply(simp add: execution_def steps_def Fin_Init)
  apply(simp add: execution_def steps_def)
  apply(rule subsetI)
  apply clarsimp
  apply(drule Run_mid)
  apply clarsimp
  apply(drule_tac x=s in meta_spec)
  apply clarsimp
  apply(drule_tac subsetD)
   apply blast
  apply(clarsimp simp: Image_def image_def Step_def execution_def steps_def)
  apply(rule_tac x=xc in exI)
  apply clarsimp
  apply(rule_tac x=xd in bexI)
   apply assumption
  apply(drule_tac x=xb in no_absD)
  by simp

lemma Run_det:
  "obs_det \<Longrightarrow> \<exists> s'. {s'. (s,s') \<in> Run Step as} = {s'}"
  apply(induct as arbitrary: s rule: rev_induct)
   apply simp
  apply(simp add: Run_app relcomp_def)
  apply(drule_tac x=s in meta_spec)
  apply clarsimp
  apply(drule_tac s=s' and js="[x]" in obs_detD)
  apply (clarsimp simp: Step_def)
  apply(rule_tac x="s'a" in exI)
  apply (auto dest: equalityD1)
  done
  
lemma eq:
  "\<lbrakk>S \<subseteq> T; \<exists> x. S = {x}; \<exists> y. T = {y}\<rbrakk> \<Longrightarrow> S = T"
  apply blast
  done

lemma execution_Run:
  "reachable s \<Longrightarrow> execution A s as = {s'. (s,s') \<in> Run Step as}"
  apply(rule disjE[OF obs_det_or_no_abs])
   apply(rule eq)
     apply(erule execution_subset_Run)
    apply(erule obs_detD)
   apply(erule Run_det)
  apply(rule equalityI)
   apply(erule execution_subset_Run)
  apply(erule (1) Run_subset_execution)
  done

end

sublocale Init_Fin_system \<subseteq> Step_system
  apply(unfold_locales)
   apply(rule reachable_s0)
  apply(erule execution_Run)
  done


locale noninterference_policy =
  fixes dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"        (* dynamic dom assignment *)
  fixes uwr :: "'d \<Rightarrow> ('s \<times> 's) set"
  fixes policy :: "('d \<times> 'd) set"     (* who can send info to whom *)
  fixes out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"        (* observable parts of d in state s *)
  fixes schedDomain :: "'d"
  assumes uwr_equiv_rel: "equiv UNIV (uwr u)"
  assumes schedIncludesCurrentDom:
    "(s,t) \<in> uwr schedDomain \<Longrightarrow> dom e s = dom e t"
  assumes schedFlowsToAll:
    "(schedDomain,d) \<in> policy"
  assumes schedNotGlobalChannel:
    "(x,schedDomain) \<in> policy \<Longrightarrow> x = schedDomain"


context noninterference_policy begin

abbreviation uwr2 :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_/ \<sim>_\<sim>/ _)" [50,100,50] 1000) 
where "s \<sim>u\<sim> t \<equiv> (s,t) \<in> uwr u"

abbreviation policy2 :: "'d \<Rightarrow> 'd \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"u \<leadsto> v \<equiv> (u,v) \<in> policy"

lemma uwr_refl:
  "s \<sim>(u::'d)\<sim> s"
  apply(cut_tac u=u in uwr_equiv_rel)
  apply(clarsimp simp: equiv_def)
  apply(blast dest: refl_onD)
  done

lemma uwr_sym:
  "x \<sim>(u::'d)\<sim> y \<Longrightarrow> y \<sim>u\<sim> x"
  apply(cut_tac u=u in uwr_equiv_rel)
  apply(clarsimp simp: equiv_def)
  apply(blast dest: symD)
  done

lemma uwr_trans:
  "\<lbrakk>x \<sim>(u::'d)\<sim> y; y \<sim>u\<sim> z\<rbrakk> \<Longrightarrow> x \<sim>u\<sim> z"
  apply(cut_tac u=u in uwr_equiv_rel)
  apply(clarsimp simp: equiv_def)
  apply(blast dest: transD)
  done

definition sameFor_dom :: "'s \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool"  ("(_/ \<approx>_\<approx>/ _)" [50,100,50] 1000) where
 "s \<approx>us\<approx> t \<equiv> \<forall>u\<in>us. (s,t) \<in> uwr u"

lemma sameFor_subset_dom: "\<lbrakk>s \<approx>(x::'d set)\<approx> t; y \<subseteq> x\<rbrakk> \<Longrightarrow> s \<approx>y\<approx> t"
  by(fastforce simp: sameFor_dom_def)


lemma sameFor_inter_domI: "s \<approx>(S::'d set)\<approx> t \<Longrightarrow> s \<approx>(S \<inter> B)\<approx> t"
  by(auto simp: sameFor_dom_def)


lemma sameFor_sym_dom:
  "s \<approx>(S::'d set)\<approx> t \<Longrightarrow> t \<approx>S\<approx> s"
  by(auto simp: sameFor_dom_def uwr_sym)

end

locale noninterference_system = Step_system A s0 + noninterference_policy dom uwr policy out schedDomain
  for A :: "('a,'s,'e) data_type" 
  and s0 :: "'s"
  and dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"  
  and uwr :: "'d \<Rightarrow> ('s \<times> 's) set"
  and policy :: "('d \<times> 'd) set"
  and out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"
  and schedDomain :: "'d"



context noninterference_system begin

(* We change the definition of sources y adding ' \<union> {u} ' in the second equation.
  This is needed in the case where 'a#as' is not executable, to ensure 'u\<in>sources as s u'
  We show later that assuming the sequence is executable, this definition is equivalent to the previous definition of sources*)
primrec  
 sources :: "'e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set" where
 sources_Nil: "sources [] s u = {u}"|
 sources_Cons: "sources (a#as) s u = (\<Union>{sources as s' u| s'. (s,s') \<in> Step a}) \<union> 
      {w. w = dom a s \<and> (\<exists> v s'. dom a s \<leadsto> v \<and> (s,s') \<in> Step a \<and> v \<in> sources as s' u)} \<union> {u}"

declare sources_Nil [simp del]     
declare sources_Cons [simp del]     


(* The definitions of obs_equiv and uwr_equiv are now assymmetric and take into account executability of the sequences of actions
   This is necessary to prove lemma Noninfluence_gen *)
definition 
  obs_equiv :: "'s \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> 'd \<Rightarrow> bool"  
where
  "obs_equiv s as t bs d \<equiv> (Executable' as s \<longrightarrow> Executable' bs t) \<and> (\<forall> s' t'. s' \<in> execution A s as \<and> t' \<in> execution A t bs \<longrightarrow>
                out d s' = out d t')"


definition 
  uwr_equiv :: "'s \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> 'd \<Rightarrow> bool"  
where
  "uwr_equiv s as t bs d \<equiv> (Executable' as s \<longrightarrow> Executable' bs t) \<and> 
                           (\<forall> s' t'. s' \<in> execution A s as \<and> t' \<in> execution A t bs
                             \<longrightarrow> s' \<sim>d\<sim> t')"



text {* Nonleakage *}
definition
  Nonleakage :: "bool" where
  "Nonleakage \<equiv> \<forall>as s u t. reachable s \<and> reachable t \<longrightarrow> 
     s \<sim>schedDomain\<sim> t \<longrightarrow>
     s \<approx>(sources as s u)\<approx> t \<longrightarrow> obs_equiv s as t as u"

text {* A generalisation of Nonleakage. *}
definition Nonleakage_gen :: "bool" where
  "Nonleakage_gen \<equiv> \<forall>as s u t. reachable s \<and> reachable t \<longrightarrow>
     s \<sim>schedDomain\<sim> t \<longrightarrow>
         s \<approx>(sources as s u)\<approx> t \<longrightarrow> uwr_equiv s as t as u"


lemma uwr_equiv_trans:
  "\<lbrakk>reachable t; uwr_equiv s as t bs x; uwr_equiv t bs u cs x\<rbrakk> \<Longrightarrow> uwr_equiv s as u cs x"
  apply(clarsimp simp: uwr_equiv_def Executable'_def)
  apply(blast intro: uwr_trans)
  done


primrec gen_purge :: "('e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set) \<Rightarrow> 'd \<Rightarrow> 'e list \<Rightarrow> 's set \<Rightarrow> 'e list" 
where
  Nil : "gen_purge sf u []     ss = []" |
  Cons: "gen_purge sf u (a#as) ss = 
            (if (\<exists>s\<in>ss. dom a s \<in> sf (a#as) s u) then 
               a#gen_purge sf u as (\<Union>s\<in>ss. {s'. (s,s') \<in> Step a})
             else 
               gen_purge sf u as ss)"



definition ipurge where
 "ipurge \<equiv> gen_purge sources"

lemma ipurge_Nil:
  "ipurge u [] ss = []"
  by(auto simp: ipurge_def)

lemma ipurge_Cons: 
  "ipurge u (a#as) ss = 
     (if (\<exists> s\<in>ss. dom a s \<in> sources (a#as) s u) then 
         a#ipurge u as (\<Union>s\<in>ss. {s'. (s,s') \<in> Step a})
      else 
         ipurge u as ss)"
  by (auto simp: ipurge_def)


lemma gen_purge_shortens:
  "length (gen_purge sf u as ss) \<le> length as"
  apply(induct as arbitrary: ss)
   apply(simp)
  apply(clarsimp)
  apply(rule le_trans)
   apply assumption
  apply simp
  done

lemma ipurge_shortens:
  "length(ipurge u as s) \<le> length as"
  apply(auto simp add:gen_purge_shortens ipurge_def)
  done


lemma INT_cong':
  assumes a: "\<And> x. Q x \<Longrightarrow> P x = P' x"
  shows
  "\<Inter>{P x|x. Q x} = \<Inter>{P' x|x. Q x}"
  apply (auto simp: a)
  done
   

text {* Standard Noninterfernce *}

definition
  Noninterference :: "bool" where
 "Noninterference \<equiv>
  \<forall> u as s. reachable s \<longrightarrow> 
         (obs_equiv s as s (ipurge u as {s}) u)"

lemma obs_equiv_trans:
  "\<lbrakk>reachable t; obs_equiv s as t bs u; obs_equiv t bs x cs u\<rbrakk> \<Longrightarrow> obs_equiv s as x cs u"
  apply(clarsimp simp: obs_equiv_def Executable'_def)
  apply(blast)
  done

text {* Noninfluence -- the combination of Noninterference and 
   Nonleakage. 

   We add the assumption about equivalence wrt the scheduler's domain, as
   is common in e.g. GVW.*}
definition
  Noninfluence  :: "bool" where
 "Noninfluence \<equiv>
  \<forall> u as s t. reachable s \<and> reachable t \<longrightarrow>
      s \<approx>(sources as s u)\<approx> t \<longrightarrow>  s \<sim>schedDomain\<sim> t \<longrightarrow>
            obs_equiv s as t (ipurge u as {t}) u"


lemma notin_policyI:
  "\<lbrakk>dom a s \<notin> sources (a # list) s u; \<exists> s'. (s,s') \<in> Step a \<and> ua \<in> sources list s' u\<rbrakk> \<Longrightarrow>
   (dom a s,ua) \<notin> policy"
  apply(clarsimp simp: sources_Cons)
  done

text {* This stronger condition is needed
   to make the induction proof work for Noninterference. It can be viewed
   as a generalisation of Noninfluence; hence its name here.
*}
definition
  Noninfluence_gen :: "bool" where
 "Noninfluence_gen \<equiv>
  \<forall> u as s ts. reachable s \<and> (\<forall> t \<in> ts. reachable t) \<longrightarrow>
      (\<forall>t \<in> ts. s \<approx>(sources as s u)\<approx> t) \<longrightarrow>  (\<forall>t \<in> ts. s \<sim>schedDomain\<sim> t) \<longrightarrow>  
            (\<forall>t \<in> ts. uwr_equiv s as t (ipurge u as ts) u)"

definition
  Noninfluence_uwr  :: "bool" where
 "Noninfluence_uwr \<equiv>
  \<forall> u as s t. reachable s \<and> reachable t \<longrightarrow>
      s \<approx>(sources as s u)\<approx> t \<longrightarrow>  s \<sim>schedDomain\<sim> t \<longrightarrow>
         uwr_equiv s as t (ipurge u as {t}) u"

definition
  Noninfluence_strong_uwr :: "bool" where
 "Noninfluence_strong_uwr \<equiv>
  \<forall> u as bs s t. reachable s  \<and> reachable t \<longrightarrow>
      s \<approx>(sources as s u)\<approx> t \<longrightarrow>  s \<sim>schedDomain\<sim> t \<longrightarrow>
         ipurge u as {s} = ipurge u bs {s} \<longrightarrow>
               uwr_equiv s as t bs u"




definition output_consistent :: "bool" where
  "output_consistent \<equiv> \<forall> u s s'. s \<sim>u\<sim> s'  \<longrightarrow> (out u s = out u s')"

definition confidentiality_u_strong :: "bool" where
  "confidentiality_u_strong \<equiv> \<forall> a u s t.  reachable s \<and> reachable t \<longrightarrow>
    s \<sim>schedDomain\<sim> t \<longrightarrow>
    ((dom a s \<leadsto> u) \<longrightarrow> s \<sim>dom a s\<sim> t) \<longrightarrow> 
      s \<sim>u\<sim> t \<longrightarrow>
      (\<forall> s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step a \<longrightarrow>
        s' \<sim>u\<sim> t')"


definition integrity_u :: "bool" where
  "integrity_u \<equiv> \<forall> a u s. reachable  s \<longrightarrow> 
   (dom a s,u) \<notin> policy  \<longrightarrow>
   (\<forall> s'. (s,s') \<in> Step a \<longrightarrow> s \<sim>u\<sim> s')"

(*<*)
(* integrity_u actually guarantees this (seemingly) stronger condition *)
definition integrity_u_more :: "bool" where
  "integrity_u_more \<equiv> \<forall> a u s. reachable s \<longrightarrow> 
   (dom a s,u) \<notin> policy \<longrightarrow>
   (\<forall> s' t. s \<sim>u\<sim> t \<and> (s,s') \<in> Step a \<longrightarrow> s' \<sim>u\<sim> t)"

lemma integrity_u_more:
  "integrity_u \<Longrightarrow> integrity_u_more"
  apply(clarsimp simp: integrity_u_more_def integrity_u_def)
  apply(blast dest: uwr_sym uwr_trans)
  done
  

lemma integrity_uD:
  "\<lbrakk>integrity_u; reachable s; (dom a s,u) \<notin> policy;
    s \<sim>u\<sim> t; (s,s') \<in> Step a\<rbrakk> \<Longrightarrow> 
   s' \<sim>u\<sim> t"
  apply(drule integrity_u_more)
  apply(simp add: integrity_u_more_def)
  done




text {*
  A weaker version of @{prop confidentiality_u_strong} that, with
  @{prop integrity_u}, implies it.
*}
definition confidentiality_u where
  "confidentiality_u \<equiv> \<forall> a u s t.  reachable s \<and> reachable t \<longrightarrow>
    s \<sim>schedDomain\<sim> t \<longrightarrow> dom a s \<leadsto> u \<longrightarrow> s \<sim>(dom a s)\<sim> t \<longrightarrow> 
      s \<sim>u\<sim> t \<longrightarrow> 
        (\<forall> s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step a \<longrightarrow> s' \<sim>u\<sim> t')"

lemma impCE':
  "\<lbrakk>P \<longrightarrow> Q; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R; \<not> P \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  apply auto
  done

lemma confidentiality_u:
  "\<lbrakk>confidentiality_u; integrity_u\<rbrakk> \<Longrightarrow>
  confidentiality_u_strong"
  apply(clarsimp simp: confidentiality_u_strong_def)
  apply(erule impCE')
   apply(subst (asm) confidentiality_u_def, blast)
  apply(frule integrity_uD, simp+)
  apply(drule_tac s=t and t="s'" in integrity_uD)
      apply assumption
     apply(drule_tac e=a in schedIncludesCurrentDom)
     apply simp
    apply(blast intro: uwr_sym)
   apply assumption
  apply(erule uwr_sym)
  done

lemma obs_equivI:
  "\<lbrakk>output_consistent; uwr_equiv s as t bs ob\<rbrakk> \<Longrightarrow> obs_equiv s as t bs ob"
  apply(clarsimp simp: obs_equiv_def)
  apply(auto simp: uwr_equiv_def output_consistent_def)
  done

lemma Noninfluence_uwr_Noninfluence:
  "\<lbrakk>output_consistent; Noninfluence_uwr\<rbrakk> \<Longrightarrow> Noninfluence"
  apply(clarsimp simp: Noninfluence_def)
  apply(erule obs_equivI)
  apply(auto simp: Noninfluence_uwr_def)
  done


lemma sched_equiv_preserved:
  "\<lbrakk>confidentiality_u_strong;  reachable s; reachable t;
   s \<sim>schedDomain\<sim> t; (s,s') \<in> Step a; (t,t') \<in> Step a\<rbrakk> \<Longrightarrow>
   s' \<sim>schedDomain\<sim> t'"
  apply(case_tac "dom a s = schedDomain")
   apply(subst (asm) confidentiality_u_strong_def)
   apply(drule_tac x=a in spec)
   apply(drule_tac x=schedDomain in spec)
   apply(drule_tac x=s in spec)
   apply(drule_tac x=t in spec)
   apply blast
  apply(subst (asm) confidentiality_u_strong_def)
  apply(blast intro: schedNotGlobalChannel)
  done

lemma sched_equiv_preserved_left:
  "\<lbrakk>integrity_u; s \<sim>schedDomain\<sim> t;
    dom a s \<noteq> schedDomain; (s,s') \<in> Step a; reachable s\<rbrakk> \<Longrightarrow> 
    s' \<sim>schedDomain\<sim> t"
  apply(blast intro: integrity_uD schedNotGlobalChannel)
  done       

lemma Noninfluence_gen_Noninterference:
  "\<lbrakk>output_consistent; Noninfluence_gen\<rbrakk> \<Longrightarrow> Noninterference"
  apply(clarsimp simp: Noninterference_def Noninfluence_gen_def)
  apply(erule_tac x=u in allE)
  apply(erule_tac x=as in allE)
  apply(erule_tac x=s in allE)
  apply(erule_tac x="{s}" in allE)
  apply(clarsimp simp: sameFor_dom_def uwr_refl Executable_Executable'_equiv)
  apply(blast intro: obs_equivI)
  done

lemma Noninfluence_gen_Noninfluence:
  "\<lbrakk>output_consistent; Noninfluence_gen\<rbrakk> \<Longrightarrow> Noninfluence"
  apply(clarsimp simp: Noninfluence_def Noninfluence_gen_def)
  apply(erule_tac x=u in allE)
  apply(erule_tac x=as in allE)
  apply(erule_tac x=s in allE)
  apply(erule_tac x="{t}" in allE)
  apply(clarsimp simp:uwr_refl)
  apply(blast intro: obs_equivI)
  done

lemma Noninfluence_gen_Noninfluence_uwr:
  "\<lbrakk>Noninfluence_gen\<rbrakk> \<Longrightarrow> Noninfluence_uwr"
  apply(clarsimp simp: Noninfluence_uwr_def Noninfluence_gen_def)
  done

end

(* we define the unwinding conditions for any system *)
locale unwinding_system = Step_system A +  noninterference_policy dom uwr policy out schedDomain
  for A :: "('a,'s,'e) data_type" 
  and dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"  
  and uwr :: "'d \<Rightarrow> ('s \<times> 's) set"
  and policy :: "('d \<times> 'd) set"
  and out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"
  and schedDomain :: "'d"



sublocale unwinding_system \<subseteq> noninterference_system
  apply(unfold_locales)
  done

context unwinding_system begin

(* This is our unwinding condition on executability *)
definition executable_u where
"executable_u \<equiv> \<forall>s t a. reachable s \<and> reachable t \<and> (s,t)\<in>uwr schedDomain \<and> (\<exists>s'. (s,s')\<in>Step a) \<longrightarrow> (\<exists>t'. (t,t')\<in>Step a)"


lemma executable_uD:
  "\<lbrakk>executable_u; reachable s; reachable t; (s,s')\<in>Step a; (s,t)\<in> uwr schedDomain\<rbrakk> \<Longrightarrow> \<exists>t'. (t,t')\<in>Step a"
  apply(fastforce simp:executable_u_def)
  done

(* We immediatly derive a global version *)
lemma Executable_u[rule_format]:
  "\<lbrakk>executable_u ; confidentiality_u_strong ; reachable s ; reachable t ; s \<sim>schedDomain\<sim> t
 ; Executable as s\<rbrakk> \<Longrightarrow> Executable as t"
  apply(induct as arbitrary:s t)
   apply simp_all
  apply(blast intro:reachable_Step sched_equiv_preserved dest:executable_uD)
  done

(* The symmetric/negative version*)
lemma not_Executable_u[rule_format]:
  "\<lbrakk>executable_u; confidentiality_u_strong ; reachable s ; reachable t ; s \<sim>schedDomain\<sim> t
 ; \<not>(Executable as s) \<rbrakk> \<Longrightarrow> \<not>(Executable as t)"
  apply(blast intro: Executable_u uwr_sym)
  done


lemma sources_refl:
  "u \<in> sources as s u"
  apply(case_tac as)
  by (auto simp: sources_Nil sources_Cons)


lemma schedDomain_in_sources_Cons:
  "(s,s')\<in> Step a \<Longrightarrow> dom a s = schedDomain \<Longrightarrow> dom a s \<in> sources (a#as) s u"
  apply(unfold sources_Cons)
  apply(erule ssubst)
  apply(rule UnI1)
  apply(rule UnI2)
  apply(clarsimp)
  apply(rule_tac x=u in exI)
  apply(safe)
   apply(rule schedFlowsToAll)
  apply(blast intro:sources_refl)
  done


lemma insert_eq:
  "u=v ==> s=t ==> insert u s = insert v t"
  apply auto
  done

lemma notin_sources_ConsD[rule_format]:
  "dom a s \<notin> sources (a#as) s u --> (\<forall>s'. (s,s')\<in>Step a \<longrightarrow> dom a s \<notin> sources as s' u) & (\<forall>s' v. (dom a s,v)\<notin>policy \<or> (s,s') \<notin> Step a \<or> v \<notin> sources as s' u)"
  apply (clarsimp simp: sources_Cons)
  apply blast
  done

    
lemma sources_eq':
  "executable_u \<and> confidentiality_u_strong \<and> s \<sim>schedDomain\<sim> t \<and> reachable s \<and> reachable t \<longrightarrow> sources as s u = sources as t u"
  apply(induct as arbitrary:s t)
   apply(simp add:sources_Nil)
  apply(clarsimp simp:sources_Cons)
  apply(rule insert_eq,blast)
  apply(rule un_eq)
   apply(rule set_eqI, rule iffI)
    apply(clarsimp,rule_tac x="sources as s' u" in exI,simp)
    apply(frule executable_uD,simp_all)
    apply(blast intro:reachable_Step sched_equiv_preserved)
   apply(clarsimp,rule_tac x="sources as s' u" in exI,simp)
   apply(frule_tac s=t in executable_uD,simp_all)
    apply(blast intro:uwr_sym)
   apply(blast intro:reachable_Step sched_equiv_preserved)
  apply safe
     apply(blast intro: schedIncludesCurrentDom)
    apply(rule_tac x=v in exI)
    apply(frule_tac e=a in schedIncludesCurrentDom,simp)
    apply(drule executable_uD,simp_all,clarsimp)
    apply(blast intro:reachable_Step sched_equiv_preserved)
   apply(blast intro: schedIncludesCurrentDom sym)
  apply(rule_tac x=v in exI)
  apply(frule_tac e=a in schedIncludesCurrentDom,simp)
  apply(drule_tac s=t in executable_uD,simp_all, clarsimp simp:uwr_sym)
  apply(blast intro:reachable_Step sched_equiv_preserved)
  done

lemma sources_eq:
  "\<lbrakk>executable_u; confidentiality_u_strong; s \<sim>schedDomain\<sim> t; reachable s; reachable t\<rbrakk> \<Longrightarrow> 
  sources as s u = sources as t u"
  apply(rule sources_eq'[rule_format],simp)
  done


lemma sameFor_sources_dom:
  "\<lbrakk>s \<approx>(sources (a#as) s u)\<approx> t; dom a s \<leadsto> x; x \<in> sources as s' u; (s,s') \<in> Step a\<rbrakk> \<Longrightarrow>
   s \<sim>(dom a s)\<sim> t"
  apply(simp add: sameFor_dom_def)
  apply(erule bspec)
  apply(subst sources_Cons)
  apply blast
  done

lemma sources_unwinding_step:
  "\<lbrakk>s \<approx>(sources (a#as) s u)\<approx> t; s \<sim>schedDomain\<sim> t; confidentiality_u_strong;
    (s,s') \<in> Step a; (t,t') \<in> Step a; reachable s; reachable t\<rbrakk>  \<Longrightarrow>
    s' \<approx>(sources as s' u)\<approx> t'"
  apply(clarsimp simp: sameFor_dom_def sources_Cons)
  apply(fastforce simp: confidentiality_u_strong_def)
  done

lemma ex_bex_comm:
  "\<exists>y\<in>s. \<exists>x. P x y \<Longrightarrow> \<exists>x. \<exists>y\<in> s. P x y"
  apply auto
  done

lemma ipurge_break:
  "ipurge u as {} = []"
  apply(induct as)
   apply(simp add:ipurge_Nil)
  apply(simp add:ipurge_Cons)
  done

lemma ipurge_eq':
  "(\<forall> s t. s\<in>ss \<and> t\<in>ts \<longrightarrow> s \<sim>schedDomain\<sim> t \<and> reachable s \<and> reachable t) \<and>
  ((\<exists>s. s\<in>ss) = (\<exists>t. t\<in>ts)) \<and>
  confidentiality_u_strong \<and> executable_u \<and> integrity_u
   \<longrightarrow> ipurge u as ss = ipurge u as ts"
  apply(induct as arbitrary: ss ts)
   apply(simp add:ipurge_Nil)
  apply(simp add:ipurge_Cons)
  apply(intro conjI impI,elim conjE)
     apply(drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec)
     apply(drule_tac x="\<Union>s\<in>ts. {s'. (s, s') \<in> local.Step a}" in meta_spec)
     apply(erule impE)
      apply clarsimp
      apply(intro allI conjI impI, elim conjE bexE)
        apply(drule_tac x=sc in spec, drule_tac x=sd in spec)
        apply(fastforce dest: sched_equiv_preserved)
       apply(elim conjE bexE,
             drule_tac x=sc in spec, drule_tac x=sd in spec,
             fastforce intro: reachable_Step)+
     apply(erule iffE,erule impE,blast)
      apply(rule iffI,rule ex_bex_comm,clarsimp)
       apply(rule_tac x=t in bexI[rotated],assumption)
       apply(rule executable_uD,simp_all)
      apply blast
     apply(clarsimp, rule ex_bex_comm)
     apply(blast intro:executable_uD uwr_sym)
    apply safe[1]
     apply(drule_tac x=t in bspec,assumption)
     apply(erule notE)
     apply(drule_tac x=s in spec, drule_tac x=t in spec,clarsimp)
     apply(frule_tac e=a in schedIncludesCurrentDom)
     apply(erule subst,rule subst, rule sources_eq)
          apply assumption+
    apply(erule notE,blast)
   apply safe[1]
    apply(drule_tac x=sa in bspec,assumption)
    apply(erule notE)
    apply(drule_tac x=sa in spec, drule_tac x=s in spec,clarsimp)
    apply(frule_tac e=a in schedIncludesCurrentDom)
    apply(erule subst,rule subst, rule_tac s=s in sources_eq)
          apply (assumption+,rule uwr_sym,assumption+)
    apply(drule_tac e=a in schedIncludesCurrentDom)
    apply simp
   apply(erule notE,fastforce)
  apply(blast intro: ipurge_break)
  done

lemma ipurge_eq:
  "\<lbrakk>s \<sim>schedDomain\<sim> t; reachable s; reachable t;
    confidentiality_u_strong; executable_u; integrity_u\<rbrakk> \<Longrightarrow> 
   ipurge u as {s} = ipurge u as {t}"
  apply(rule ipurge_eq'[rule_format], simp add: uwr_refl)
  done


lemma dom_in_sources_Cons:
  "\<lbrakk>confidentiality_u_strong; integrity_u; executable_u; 
    reachable s; reachable t;
    s \<approx>(sources (a#as) s u)\<approx> t; s \<sim>schedDomain\<sim> t;
    (dom a s \<in> sources (a#as) s u)\<rbrakk> \<Longrightarrow> 
    (dom a t \<in> sources (a#as) t u)"
  apply(subgoal_tac "dom a s = dom a t")
   apply(fastforce dest: sources_eq)
  apply(blast intro: schedIncludesCurrentDom)
  done

lemma dom_notin_sources_Cons:
  "\<lbrakk>confidentiality_u_strong; integrity_u; executable_u; 
    reachable s; reachable t;
    s \<approx>(sources (a#as) s u)\<approx> t; s \<sim>schedDomain\<sim> t;
    (dom a s \<notin> sources (a#as) s u)\<rbrakk> \<Longrightarrow> 
    (dom a t \<notin> sources (a#as) t u)"
  apply(subgoal_tac "dom a s = dom a t")
   apply(fastforce dest: sources_eq)
  apply(blast intro: schedIncludesCurrentDom)
  done


lemma uwr_equiv_Cons_bothI:
   "\<lbrakk>reachable s; reachable t; executable_u; (s,t)\<in>uwr schedDomain;
    \<forall> s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step a \<longrightarrow> uwr_equiv s' as t' bs u\<rbrakk> \<Longrightarrow>
    uwr_equiv s (a # as) t (a # bs) u"
  apply(clarsimp simp: uwr_equiv_def execution_Run)
  apply(safe)
   apply(frule Executable'D,fastforce)
   apply(rule Executable'I,clarsimp)
   apply(subst (asm) executable_u_def)
   apply(blast intro:reachable_Step Executable'D Executable'I)
  apply(fastforce simp:reachable_Step execution_Run Executable'_def)
  done

lemma uwr_equiv_Cons_leftI:
   "\<lbrakk>reachable s; \<forall> s'. (s,s') \<in> Step a \<longrightarrow> uwr_equiv s' as t bs u\<rbrakk> \<Longrightarrow>
    uwr_equiv s (a # as) t bs u"
  apply(clarsimp simp: uwr_equiv_def execution_Run reachable_Step Executable'_def)
  apply blast
  done

lemma uwr_equiv_eq:
  "\<lbrakk>uwr_equiv s as t bs u; execution A t bs = execution A r cs; Executable cs r; Executable bs t\<rbrakk> \<Longrightarrow>
    uwr_equiv s as r cs u"
  apply(unfold uwr_equiv_def)
  apply(blast intro: Executable'I)
  done


lemma Executable_ipurge:
  "\<lbrakk>confidentiality_u_strong; integrity_u; executable_u; reachable s; Executable as s; s\<in>ss\<rbrakk> \<Longrightarrow> Executable (ipurge u as ss) s"
  apply(induct as arbitrary:s ss)
   apply(simp add:ipurge_Nil)
  apply(clarsimp simp: ipurge_Cons)
  apply safe
   apply(drule_tac x=s' in meta_spec, drule_tac x="(\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a})" in meta_spec)
   apply(blast intro:reachable_Step)
  apply(drule_tac x=s in meta_spec, drule_tac x=ss in meta_spec)
  apply simp
  apply(drule impI, erule impE,simp_all)
  apply(subgoal_tac "dom a s \<noteq> schedDomain")
   apply(subgoal_tac "(s,s')\<in>uwr schedDomain")
    apply(rule_tac s=s' in Executable_u)
         apply(blast intro: reachable_Step uwr_sym)+
   apply(rule integrity_uD[THEN uwr_sym],simp_all add: uwr_refl)
   apply(blast intro: schedNotGlobalChannel)
  apply(rule notI)
  apply(frule schedDomain_in_sources_Cons,fastforce+) 
  done 


(* Best. Proof. Ever. *)
lemma Noninfluence_gen:
  "\<lbrakk>confidentiality_u_strong; integrity_u; executable_u\<rbrakk> \<Longrightarrow> Noninfluence_gen"
  apply(subst Noninfluence_gen_def)
  apply(rule allI, rule allI)
  apply(induct_tac as)
   apply(fastforce simp:Executable'I sameFor_dom_def ipurge_Nil sources_Nil uwr_equiv_def execution_Run)
  apply(clarsimp simp: ipurge_Cons)
  apply(intro conjI,clarsimp)
   apply(rule uwr_equiv_Cons_bothI)
       apply(blast+)[3]
    apply(drule_tac x=t in bspec,assumption,blast)
   apply clarsimp
   apply(erule_tac x="s'" in allE,erule_tac x="\<Union>t\<in>ts. {t'. (t,t') \<in> Step a}" in allE)
   apply(erule impE,blast intro: reachable_Step)
   apply(erule impE,clarsimp,rename_tac ta tb)
    apply(rule_tac t=ta in sources_unwinding_step,blast+)[1]
   apply(erule impE,clarsimp,rename_tac ta tb)
    apply(rule_tac s=s and t=ta in sched_equiv_preserved)
         apply (simp_all)[6]
   apply blast
  apply clarsimp
  apply(rule uwr_equiv_Cons_leftI,blast)
  apply safe
  apply(drule_tac x=s' in spec, drule_tac x=ts in spec)
  apply(erule impE,blast intro: reachable_Step)
  apply(erule impE,clarsimp simp: sameFor_dom_def)
   apply(drule_tac x=x in bspec,assumption, drule_tac x=ua in bspec)
    apply(fastforce simp: sources_Cons)
   apply(subgoal_tac "dom a s \<notin> sources (a # list) s u")
    apply(drule notin_sources_ConsD,clarsimp)
    apply(erule_tac x=s' in allE, erule impE, assumption,erule_tac x=ua in allE)
    apply(blast intro:integrity_uD)
   apply(drule_tac x=t in bspec,assumption)+
   apply(simp add: schedIncludesCurrentDom)
   apply(subgoal_tac "sources (a # list) s u = sources (a # list) t u",blast)
   apply(rule sources_eq,simp add: executable_u_def,assumption+)
  apply(erule impE,clarsimp)
   apply(rule integrity_uD,simp_all)
  apply(case_tac "dom a s \<noteq> schedDomain")
   apply(blast dest:schedNotGlobalChannel)
  apply(drule_tac x=t in bspec,assumption)
  apply(erule notE,subst sources_Cons)
  apply(subst (asm) executable_u_def)
  apply(erule_tac x=s in allE, erule_tac x=t in allE, erule_tac x=a in allE,simp)
  apply(erule impE,blast)
  apply(rule disjI2)+
  apply(rule_tac x=u in exI)
  apply(rule conjI)
   apply(drule_tac x=t in bspec,assumption)+
   apply(frule_tac e=a in schedIncludesCurrentDom,simp)
   apply(rule schedFlowsToAll)
  apply(fastforce simp:sources_refl)
  done


lemma obs_equiv_Cons_bothI:
   "\<lbrakk>reachable s; reachable t; executable_u; (s,t)\<in>uwr schedDomain;
    \<forall> s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step a \<longrightarrow> obs_equiv s' as t' bs u\<rbrakk> \<Longrightarrow>
   obs_equiv s (a # as) t (a # bs) u"
  apply(clarsimp simp: obs_equiv_def execution_Run)
  apply(safe)
   apply(frule Executable'D,fastforce)
   apply(rule Executable'I,clarsimp)
   apply(subst (asm) executable_u_def,erule_tac x=s in allE, erule_tac x=t in allE, erule_tac x=a in allE,clarsimp)
   apply(erule impE,blast,clarsimp)
   apply(drule_tac x=s' in spec, drule_tac x=t' in spec,safe)
    apply(blast intro:Executable'I)
   apply(blast intro:reachable_Step Executable'D)
  apply(fastforce simp:reachable_Step execution_Run Executable'_def)
  done

lemma Nonleakage:
  "\<lbrakk>confidentiality_u_strong; executable_u; output_consistent\<rbrakk> \<Longrightarrow> Nonleakage"
  apply(subst Nonleakage_def)
  apply(rule allI)
  apply(induct_tac as)
   apply(clarsimp simp:obs_equiv_def)
   apply(simp add: Executable'I execution_Run output_consistent_def sameFor_dom_def sources_refl)
  apply(clarsimp)
  apply(rule obs_equiv_Cons_bothI,assumption+)
  apply(blast intro:reachable_Step sched_equiv_preserved sources_unwinding_step)
  done
   
(*In fact, if as is executable, sources as s u matches the result of sources' as s u, where sources' is the usual formulation :*)
primrec  
 sources' :: "'e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set" where
 sources'_Nil: "sources' [] s u = {u}"|
 sources'_Cons: "sources' (a#as) s u = (\<Union>{sources' as s' u| s'. (s,s') \<in> Step a}) \<union> 
      {w. w = dom a s \<and> (\<exists> v s'. dom a s \<leadsto> v \<and> (s,s') \<in> Step a \<and> v \<in> sources' as s' u)}"

declare sources'_Nil [simp del]     
declare sources'_Cons [simp del] 

lemma insert_eq_left:
  "u\<in>s \<Longrightarrow> s = t \<Longrightarrow> insert u s = t"
  apply auto
  done

lemma sources'_refl:
  "reachable s \<and> Executable as s \<Longrightarrow> u \<in> sources' as s u"
  apply(induct as arbitrary: s)
   apply(simp add: sources'_Nil)
  apply(clarsimp simp: sources'_Cons)
  apply(blast intro:reachable_Step)
  done

lemma sources_sources'_equiv:
"\<lbrakk>executable_u; confidentiality_u_strong; reachable s; Executable as s\<rbrakk> \<Longrightarrow> sources as s u = sources' as s u"
  apply(induct as arbitrary:s)
   apply(simp add: sources'_Nil sources_Nil)
  apply(simp add: sources'_Cons sources_Cons)
  apply(rule insert_eq_left)
   apply(rule UnI1)
   apply clarsimp
   apply(rule_tac x="sources as s' u" in exI)
   apply(rule conjI,rule_tac x=s' in exI,simp)
   apply(blast intro:reachable_Step sources'_refl)
  apply(rule un_eq)
   apply(rule set_eqI,rule iffI)
    apply(clarsimp)
    apply(rule_tac x="sources as s'a u" in exI,simp)
    apply(rule_tac x=s'a in exI,simp)
    apply(drule_tac x=s'a in meta_spec)
    apply(frule_tac s'=s'a in reachable_Step,simp,simp)
    apply(drule impI,erule impE)
     apply(rule Executable_u,simp_all add:uwr_refl)
     apply(blast intro:reachable_Step)
    apply(rule sched_equiv_preserved,simp_all add:uwr_refl)
   apply clarsimp
   apply(rule_tac x="sources' as s'a u" in exI,simp)
   apply(rule_tac x=s'a in exI,simp)
   apply(drule_tac x=s'a in meta_spec)
   apply(frule_tac s'=s'a in reachable_Step,simp,simp)
   apply(drule impI,erule impE)
    apply(rule Executable_u,simp_all add:uwr_refl)
    apply(blast intro:reachable_Step)
   apply(rule sched_equiv_preserved,simp_all add:uwr_refl)
  apply safe
   apply(rule_tac x=v in exI,simp)
   apply(rule_tac x=s'a in exI,simp)
   apply(drule_tac x=s'a in meta_spec)
   apply(frule_tac s'=s'a in reachable_Step,simp,simp)
   apply(drule impI,erule impE)
    apply(rule Executable_u,simp_all add:uwr_refl)
    apply(blast intro:reachable_Step)
   apply(rule sched_equiv_preserved,simp_all add:uwr_refl)
  apply(rule_tac x=v in exI,simp)
  apply(rule_tac x=s'a in exI,simp)
  apply(drule_tac x=s'a in meta_spec)
  apply(frule_tac s'=s'a in reachable_Step,simp,simp)
  apply(drule impI,erule impE)
   apply(rule Executable_u,simp_all add:uwr_refl)
   apply(blast intro:reachable_Step)
  apply(rule sched_equiv_preserved,simp_all add:uwr_refl)
  done



lemma Noninterference:
  "\<lbrakk>confidentiality_u; output_consistent; integrity_u; executable_u\<rbrakk> \<Longrightarrow> 
   Noninterference"
  apply(rule Noninfluence_gen_Noninterference)
   apply assumption
  apply(blast intro: Noninfluence_gen confidentiality_u)
  done

lemma Noninfluence:
  "\<lbrakk>confidentiality_u; output_consistent; integrity_u; executable_u\<rbrakk> \<Longrightarrow> 
   Noninfluence"
  apply(rule Noninfluence_gen_Noninfluence)
   apply assumption
  apply(blast intro: Noninfluence_gen confidentiality_u)
  done


lemma Noninfluence_uwr:
  "\<lbrakk>confidentiality_u; integrity_u; executable_u\<rbrakk> \<Longrightarrow> 
   Noninfluence_uwr"
  apply(rule Noninfluence_gen_Noninfluence_uwr)
  apply(blast intro: Noninfluence_gen confidentiality_u)
  done

 
lemma sources_Step:
  "\<lbrakk>reachable s; (dom a s, u) \<notin> policy; (s,s')\<in>Step a\<rbrakk> \<Longrightarrow>
  sources [a] s u = {u}"
  apply(auto simp add: sources_Cons sources_Nil)
  done

lemma sources_Step_2:
  "\<lbrakk>reachable s; (dom a s, u) \<in> policy; (s,s')\<in>Step a\<rbrakk> \<Longrightarrow>
  sources [a] s u = {dom a s,u}"
  apply(auto simp: sources_Cons sources_Nil)
  done

lemma execution_Nil:
  "reachable s \<Longrightarrow> execution A s [] = {s}"
  apply(simp add: execution_Run)
  done

lemma execution_executable:
  "s' \<in> execution A s [a] ==> (s,s')\<in>Step a"
  apply(auto simp add: Step_def execution_Run)
  done

lemma executable_execution:
  "reachable s ==> (s,s')\<in>Step a ==> \<exists>s'. s' \<in> execution A s [a]"
  apply(auto simp add: execution_Run)
  done

lemma Noninfluence_gen_confidentiality_u:
  "Noninfluence_gen \<Longrightarrow> confidentiality_u"
  apply(clarsimp simp: Noninfluence_gen_def confidentiality_u_def)
  apply(drule_tac x=u in spec, drule_tac x="[a]" in spec)
  apply(drule_tac x=s in spec, drule_tac x="{t}" in spec)
  apply(simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def ipurge_Cons ipurge_Nil  add: schedIncludesCurrentDom)
  done

lemma Noninfluence_strong_uwr_confidentiality_u:
  "Noninfluence_strong_uwr \<Longrightarrow> confidentiality_u"
  apply(clarsimp simp: Noninfluence_strong_uwr_def confidentiality_u_def)
  apply(drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply(drule_tac x=s in spec, drule_tac x=t in spec)
  apply(simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done


(* A potentially useful lemma if executable_u changes and then Executable_u takes into account equivalency with respect to sources: 
   The equivalent of sources_unwinding_step if a is purged *)
lemma sources_unwinding_step_aux:
  "\<lbrakk>s \<approx>(sources (a#as) s u)\<approx> t; s \<sim>schedDomain\<sim> t; integrity_u;
     (s,s') \<in> Step a; reachable s; reachable t; dom a s \<notin>sources (a#as) s u\<rbrakk>  \<Longrightarrow>
    s' \<approx>(sources as s' u)\<approx> t"
  apply(clarsimp simp: sameFor_dom_def sources_Cons)
  apply(blast intro: integrity_uD)
  done

(* with this lemma, 'sameFor_dom _ (sources as _ u) _' is (decreadingly) preserved through an sequence and its ipurge *)
lemma sources_unwinding_step2:
  "\<lbrakk>s \<approx>(sources (a#as) s u)\<approx> t; s \<sim>schedDomain\<sim> t; integrity_u; confidentiality_u_strong; executable_u;
     (s,s') \<in> Step a; reachable s; reachable t; dom a t \<notin>sources (a#as) t u\<rbrakk>  \<Longrightarrow>
    s' \<approx>(sources as s' u)\<approx> t"
  apply(rule_tac s=s and t=t in sources_unwinding_step_aux,simp_all)
  apply(subgoal_tac "dom a s = dom a t")
   apply(fastforce dest: sources_eq)
  apply(blast intro: schedIncludesCurrentDom)
  done


(* Assuming the sequence of actions is executable, 
   the unwinding conditions imply that the sources of a sequence and its ipurge are the same*)
lemma sources_ipurge:
  "s\<in>ss \<Longrightarrow> executable_u \<Longrightarrow> integrity_u \<Longrightarrow> confidentiality_u_strong \<Longrightarrow>
    Executable as s\<Longrightarrow> sources (ipurge u as ss) s u = sources as s u"
  apply(induct as arbitrary:s ss)
   apply(clarsimp simp:sources_Nil ipurge_Nil)
  apply(subst ipurge_Cons)
  apply(case_tac "\<exists>s\<in>ss. dom a s \<in> sources (a # as) s u ")
   defer
   apply(clarsimp)
   apply(drule_tac x=s in meta_spec,drule_tac x=ss in meta_spec)
   apply(clarsimp)
   apply(drule impI,erule impE)
    apply(rule Executable_u,simp_all)
     apply(blast intro:reachable_Step)
    apply(drule_tac x=s in bspec,assumption)
    apply(rule integrity_uD,simp_all)
     apply(erule contrapos_nn)
     apply(drule schedNotGlobalChannel)
     apply(rule schedDomain_in_sources_Cons,simp_all add:uwr_refl)
   apply(subgoal_tac "(dom a s, schedDomain) \<notin> policy")
    apply(subst sources_Cons)
    apply clarsimp
    apply(rule insert_eq_left[THEN sym])
     apply(blast intro:sources_refl)
    apply(rule equalityI)
     apply(clarsimp|rule conjI)+
      apply(subst sources_eq,simp_all)
       apply(rule uwr_sym)
       apply(rule integrity_uD,simp_all add:uwr_refl)
      apply(blast intro:reachable_Step)
     apply clarsimp
     apply(drule_tac x=s in bspec,assumption)
     apply(drule notin_sources_ConsD,blast)
    apply(rule subsetI)
    apply(rule UnI1,simp)
    apply(rule_tac x="sources as s u" in exI,simp)
    apply(rule_tac x=s' in exI,simp)
    apply(rule sources_eq,simp_all)
     apply(rule integrity_uD[THEN uwr_sym],simp_all add:uwr_refl)
    apply(blast intro:reachable_Step)
   apply(drule_tac x=s in bspec,assumption)
   apply(erule contrapos_nn)
   apply(drule schedNotGlobalChannel)
   apply(rule schedDomain_in_sources_Cons,simp_all)
  apply(clarsimp)
  apply(subst sources_Cons)+
  apply(rule un_eq,simp_all)
  apply(rule un_eq)
   apply(rule set_eqI,rule iffI)
    apply clarsimp
    apply(rule_tac x="sources (ipurge u as (\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a})) s'a u" in exI,simp)
    apply(rule_tac x=s'a in exI,simp)
    apply(drule_tac x=s'a in meta_spec,drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec)
    apply(drule_tac t=s'a in Executable_u,simp_all)
       apply(blast intro:reachable_Step)+
     apply(blast intro:sched_equiv_preserved uwr_refl)
    apply simp
    apply(drule impI,erule impE,blast,blast)
   apply clarsimp
   apply(rule_tac x="sources as s'a u" in exI,simp)
   apply(rule_tac x=s'a in exI,simp)
   apply(drule_tac x=s'a in meta_spec,drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec)
   apply(drule_tac t=s'a in Executable_u,simp_all)
      apply(blast intro:reachable_Step)+
    apply(blast intro:sched_equiv_preserved uwr_refl)
   apply simp
   apply(drule impI,erule impE,blast,blast)
  apply safe
   apply(rule_tac x=v in exI,simp)
   apply(rule_tac x=s'a in exI,simp)
   apply(drule_tac x=s'a in meta_spec,drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec,simp)
   apply(drule_tac t=s'a in Executable_u,simp_all)
      apply(blast intro:reachable_Step)+
    apply(blast intro:sched_equiv_preserved uwr_refl,simp)
   apply(drule impI,erule impE,blast)
   apply blast
  apply(rule_tac x=v in exI,simp)
  apply(rule_tac x=s'a in exI,simp)
  apply(drule_tac x=s'a in meta_spec,drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec,simp)
  apply(drule_tac t=s'a in Executable_u,simp_all)
     apply(blast intro:reachable_Step)+
   apply(blast intro:sched_equiv_preserved uwr_refl,simp)
  apply(drule impI,erule impE,blast)
  apply blast
  done

(*Using the previous lemma, we can show that ipurge is idempotent,assuming the sequence is executable*)
lemma ipurge_idem':
  "s\<in>ss \<longrightarrow> executable_u \<longrightarrow> integrity_u \<longrightarrow> confidentiality_u_strong \<longrightarrow>
    Ball ss reachable \<longrightarrow> Ball ss (Executable as) \<longrightarrow>
    (\<forall>s t. s\<in>ss \<and>t\<in>ss \<longrightarrow> (s,t)\<in>uwr schedDomain) \<longrightarrow>
     ipurge u (ipurge u as ss) ss = ipurge u as ss"
  apply(induct as arbitrary: s ss)
   apply(simp add:ipurge_Nil)
  apply(subst ipurge_Cons)+
  apply(case_tac "\<exists>s\<in>ss. dom a s \<in> sources (a # as) s u")
   apply clarsimp
   apply(subst ipurge_Cons)
   apply(case_tac "\<exists>s\<in>ss. dom a s \<in> sources (a # ipurge u as (\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a})) s u")
    apply clarsimp
    apply(drule_tac x=sa in bspec,assumption,clarsimp)
    apply(drule_tac x=s' in meta_spec,drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec)
    apply(erule impE,blast intro:reachable_Step)
    apply(erule impE,blast intro:reachable_Step)
    apply(erule impE,clarsimp,rule Executable_u,simp_all)
      apply(blast intro:reachable_Step)
     apply(blast intro:reachable_Step)
    apply(rule sched_equiv_preserved,simp_all)
    apply(erule impE,blast intro:sched_equiv_preserved)
    apply blast
   apply(drule_tac x=sa in bspec,assumption) back back
   apply(subst (asm) sources_ipurge[THEN sym],simp_all)
   apply(subst (asm)ipurge_Cons)
   apply(case_tac " \<exists>s\<in>ss. dom a s \<in> sources (a # as) s u")
    apply clarsimp
   apply clarsimp
   apply(drule notin_sources_ConsD)
   apply(drule_tac x=sa in bspec,assumption)+
   apply clarsimp
   apply(drule_tac x=s' in spec,simp)+
   apply(subst (asm) sources_ipurge,simp_all)
    apply(rule Executable_u,simp_all)
     apply(blast intro:reachable_Step)
    apply(rule integrity_uD,simp_all)
    apply(erule contrapos_nn)
    apply(drule schedNotGlobalChannel)
    apply(rule schedDomain_in_sources_Cons,simp_all)
   apply(frule notin_sources_ConsD,clarsimp)
   apply(drule_tac x=s' in spec,simp)+
   apply(erule notE,subst sources_eq,simp_all) back
     apply(rule integrity_uD,simp_all)
     apply(erule contrapos_nn)
     apply(drule schedNotGlobalChannel)
     apply(rule schedDomain_in_sources_Cons,simp_all)
    apply(blast intro:reachable_Step)
   apply(subgoal_tac "sources as s' u = sources as sa u")
    apply(simp)
   apply(rule sources_eq,simp_all)
    apply(rule integrity_uD,simp_all)
    apply(erule contrapos_nn)
    apply(drule schedNotGlobalChannel)
    apply(rule schedDomain_in_sources_Cons,simp_all)
   apply(blast intro:reachable_Step)
  apply clarsimp
  apply(drule_tac x=s in meta_spec, drule_tac x=ss in meta_spec,simp_all)
  apply(erule impE,clarsimp)
  apply(drule_tac x=s in bspec,assumption,erule exE,clarsimp)
  apply(rule_tac s=s' in Executable_u,simp_all)
   apply(blast intro:reachable_Step)
  apply(rule integrity_uD,simp_all)
  apply(drule_tac x=s in bspec,assumption)
  apply(erule contrapos_nn)
  apply(drule schedNotGlobalChannel)
  apply(rule schedDomain_in_sources_Cons,simp_all)
  done


lemma ipurge_idem:
  "executable_u \<Longrightarrow> integrity_u \<Longrightarrow> confidentiality_u_strong \<Longrightarrow>
    Executable as s \<Longrightarrow>
     ipurge u (ipurge u as {s}) {s} = ipurge u as {s}"
  apply(rule ipurge_idem'[rule_format],simp_all add:uwr_refl)
  apply(case_tac as,simp_all)
  done


(* When we delete the executability assumption, we still have an inclusion*)
lemma sources_subset_sources_ipurge:
  "s\<in>ss \<Longrightarrow> reachable s \<Longrightarrow> executable_u \<Longrightarrow> integrity_u \<Longrightarrow> confidentiality_u_strong \<Longrightarrow>
    sources as s u \<subseteq> sources (ipurge u as ss) s u"
  apply(induct as arbitrary:s ss)
   apply(simp add:sources_Nil ipurge_Nil)
  apply(subst ipurge_Cons)
  apply(case_tac "\<exists>s\<in>ss. dom a s \<in> sources (a # as) s u")
   apply(clarsimp)
   apply(subst (asm) sources_Cons)
   apply safe[1]
     apply(drule_tac x=s' in meta_spec,drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec,simp)
     apply(frule reachable_Step,simp,simp)
     apply(drule impI,erule impE,blast)
     apply(rule subsetD,simp_all)
     apply(erule subset_trans)
     apply(subst sources_Cons)
     apply(rule subsetI)
     apply(rule UnI1)+
     apply clarsimp
     apply(rule_tac x="sources (ipurge u as (\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a})) s' u" in exI,simp,blast)
    apply(subst sources_Cons)
    apply(rule UnI1,rule UnI2)
    apply clarsimp
    apply(rule_tac x=v in exI,simp)
    apply(rule_tac x=s' in exI,simp)
    apply(drule_tac x=s' in meta_spec,drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec)
    apply(blast intro:reachable_Step)
   apply(rule sources_refl)
  apply(drule_tac x=s in bspec,assumption)
  apply(drule notin_sources_ConsD,clarsimp)
  apply(subst (asm) sources_Cons,clarsimp)
  apply safe
    apply(rule sources_refl)
   apply(drule_tac x=s in meta_spec, drule_tac x=ss in meta_spec,simp)
   apply(rule subsetD,simp)
   apply(subst sources_eq,simp_all)
   apply(rule integrity_uD[THEN uwr_sym],simp_all add:uwr_refl)
   apply(drule_tac x=s' in spec,simp)+
   apply(rule notI,drule schedNotGlobalChannel)
   apply(erule_tac x=u in allE,erule impE,simp add:schedFlowsToAll)
   apply(blast intro:sources_refl)
  apply(blast intro:reachable_Step)
  done

(* the previous inclusion if sufficient to prove that ipurge is idempotent, even if the sequence is not executable *)
lemma ipurge_idemp_gen:
  "s\<in>ss \<longrightarrow> executable_u \<longrightarrow> integrity_u \<longrightarrow> confidentiality_u_strong \<longrightarrow>
    Ball ss reachable \<longrightarrow>
     ipurge u (ipurge u as ss) ss = ipurge u as ss"
  apply(induct as arbitrary: s ss)
   apply(simp add:ipurge_Nil)
  apply(subst ipurge_Cons)+
  apply(case_tac "\<exists>s\<in>ss. dom a s \<in> sources (a # as) s u")
   apply clarsimp
   apply(subst ipurge_Cons)
   apply(case_tac "\<exists>s\<in>ss. dom a s \<in> sources (a # ipurge u as (\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a})) s u")
    apply clarsimp
    apply(case_tac "\<exists>s'. s'\<in>(\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a})")
     apply clarsimp
     apply(drule_tac x=s' in meta_spec, drule_tac x="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in meta_spec)
     apply(erule impE,blast)
     apply(erule impE,blast intro:reachable_Step)
     apply blast
    apply(clarsimp simp:ipurge_break)
   apply clarsimp
   apply(subst (asm) sources_Cons,clarsimp)
   apply(erule disjE)
    apply(drule_tac x=s in bspec,assumption, blast intro:sources_refl)
   apply(erule disjE,clarsimp)
    apply(drule_tac x=sa in bspec,assumption,drule notin_sources_ConsD,clarsimp)
    apply(drule_tac x=s' in spec,simp)+
    apply(cut_tac s=s' and u=u and as=as and ss="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in sources_subset_sources_ipurge,simp_all)
     apply(blast)
    apply(blast intro:reachable_Step)
   apply(drule subsetD,assumption,blast)
  apply clarsimp
  apply(drule_tac x=sa in bspec,assumption,drule notin_sources_ConsD) 
  apply clarsimp
  apply(drule_tac x=s' in spec,simp)+
  apply(drule_tac x=v in spec,simp)
  apply(cut_tac s=s' and u=u and as=as and ss="\<Union>s\<in>ss. {s'. (s, s') \<in> local.Step a}" in sources_subset_sources_ipurge,simp_all)
     apply(blast)
    apply(blast intro:reachable_Step)
   apply(drule subsetD,assumption,blast)
  done

lemma ipurge_idemp:
  "executable_u \<Longrightarrow> integrity_u \<Longrightarrow> confidentiality_u_strong \<Longrightarrow>
   reachable s \<Longrightarrow> ipurge u (ipurge u as {s}) {s} = ipurge u as {s}"
  apply(rule ipurge_idemp_gen[rule_format])
      apply(auto simp add:uwr_refl)
  done


(* This is the kind of lemma we would need with any unwinding condition *)
lemma dom_dom_in_policy_example[rule_format]:
  "executable_u \<longrightarrow> confidentiality_u_strong \<longrightarrow> integrity_u\<longrightarrow>
  reachable s \<longrightarrow> Executable (b#as) s \<longrightarrow> (s,s')\<in>Step a \<longrightarrow> (\<not> Executable (b#as) s') \<longrightarrow>
  dom a s \<notin> sources (a#b#as) s u \<longrightarrow>
  (dom a s,dom b s)\<in>policy"
  apply clarsimp
  apply(frule_tac s'=s' in reachable_Step,simp+)
  apply(subgoal_tac "\<exists>t'. (s',t')\<in>Step b")
   apply(clarsimp,drule_tac x=t' in spec,simp)
   apply(erule notE,rule Executable_u,simp_all)
     apply(blast intro:reachable_Step)+
   apply(rule sched_equiv_preserved,simp_all)
   apply(rule integrity_uD[THEN uwr_sym],simp_all)
   apply(erule contrapos_nn,drule schedNotGlobalChannel)
   apply(rule schedDomain_in_sources_Cons,simp_all add:uwr_refl)
  apply(rule executable_uD,simp_all)
  apply(rule integrity_uD[THEN uwr_sym],simp_all)
  apply(erule contrapos_nn,drule schedNotGlobalChannel)
  apply(rule schedDomain_in_sources_Cons,simp_all add:uwr_refl)
done



(* we just define 'enabled' here to show it is preserved by our refinement *)

definition enabled where
"enabled \<equiv> (\<forall>s a. reachable s \<longrightarrow> (\<exists>s'. (s,s')\<in>Step a))"

lemma enabled_executable_u:
  "enabled \<Longrightarrow> executable_u"
  apply(clarsimp simp:enabled_def executable_u_def)
  done

lemma ipurge_idem_enabled:
  "enabled \<Longrightarrow> integrity_u \<Longrightarrow> confidentiality_u_strong \<Longrightarrow>
   reachable s \<Longrightarrow>
   ipurge u (ipurge u as {s}) {s} = ipurge u as {s}"
  apply(rule ipurge_idemp,simp_all)
   apply(blast intro:enabled_executable_u)
  done

end


locale complete_unwinding_system = unwinding_system +
  assumes  policy_refl:
  "(u,u) \<in> policy"

context complete_unwinding_system begin

lemma Noninfluence_gen_integrity_u:
  "Noninfluence_gen \<Longrightarrow> integrity_u"
  apply(clarsimp simp: Noninfluence_gen_def integrity_u_def)
  apply(drule_tac x=u in spec, drule_tac x="[a]" in spec)
  apply(drule_tac x=s in spec, drule_tac x="{s}" in spec)
  apply(simp add: sources_Step sameFor_dom_def uwr_equiv_def Step_def ipurge_Cons ipurge_Nil add: uwr_refl policy_refl execution_Nil uwr_sym)
  apply(case_tac "dom a s=u")
   apply(clarsimp simp:Executable'_def ipurge_Nil policy_refl)+
  apply(fastforce simp:execution_Run uwr_sym)
  done


lemma Noninfluence_strong_uwr_integrity_u: "Noninfluence_strong_uwr \<Longrightarrow> integrity_u"
  apply(clarsimp simp: Noninfluence_strong_uwr_def integrity_u_def)
  apply(drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply(drule_tac x=s in spec, drule_tac x=s in spec)
  apply(simp add: sources_Step sameFor_dom_def uwr_refl uwr_equiv_def Step_def ipurge_Cons ipurge_Nil)
  apply(case_tac "dom a s = u",simp)
   apply(blast intro: policy_refl)
  apply(clarsimp simp:sources_Cons sources_Nil Executable'_def execution_Nil ipurge_Nil)
  apply(blast intro:uwr_sym)
  done

lemma Noninfluence_strong_uwr_executable_u: "Noninfluence_strong_uwr \<Longrightarrow> executable_u"
  apply(clarsimp simp: Noninfluence_strong_uwr_def executable_u_def uwr_equiv_def)
  apply(drule_tac x=schedDomain in spec)
  apply(drule_tac x="[a]" in spec)+
  apply(drule_tac x=s in spec, drule_tac x=t in spec)
  apply(erule impE,blast)
  apply(erule impE)
   apply(clarsimp simp:sources_Cons sources_Nil sameFor_dom_def)
   apply(blast dest:schedNotGlobalChannel)
  apply(erule impE,blast)+
  apply(simp add: Executable'_def Step_def,blast)
  done

lemma Noninfluence_strong_uwr_Noninfluence_gen:
  "Noninfluence_strong_uwr \<Longrightarrow> Noninfluence_gen"
  apply(rule Noninfluence_gen)
    apply(rule confidentiality_u)
     apply(rule Noninfluence_strong_uwr_confidentiality_u,assumption)
    apply(rule Noninfluence_strong_uwr_integrity_u,assumption)+
  apply(rule Noninfluence_strong_uwr_executable_u,assumption)
  done


(* Experimenting with other unwinding conditions *)

text {*
Properties alternative unwinding conditions for executability should verify :
- Noninfluence_gen \<longrightarrow> executable_u
- executable_u \<and> (other assumptions) \<and> Executable as s \<longrightarrow> Executable (ipurge u as {s}) s
- executable_u \<and> (other assumptions) \<and> Executable as s \<longrightarrow> Executable as t
- executable_u \<and> (other assumptions) \<and> \<not>Executable as s \<longrightarrow> sources as s u = sources as t u
- executable_u \<and> (other assumptions) \<longrightarrow> ipurge u as {s} = ipurge u as {t}
- lemma dom_dom_in_policy_example stated above and/or lemma example stated below

Intuitions on alternative unwinding conditions and possible changes to the theory :
- the unwinding condition should state : (s,t)\<in>uwr (dom a s)
- the problem arises when the action is purged, so there are 3 possible fixes :
  - add assumptions to the unwinding condition (difficult to combine with 'Noninfluence_gen \<longrightarrow> executable_u'
  - change the definition of sources/ipurge, to purge an action iff it doesn't affect, directly or indirectly the target domain,
    or any domain involved in the computation
  - break symmetry in the unwinding condition (uwr_equiv is assymmetric, why not the unwinding condition ?)

The key lemma to obtain is Executable_u, the global version of the local property stated by the unwinding condition.
Assumptions that are reasonable are :
- the states are reachable,
- they are equivalent with respect to schedDomain,
- they are equivalent with respect to 'sources as s u' (<-- what 'u' ?)

Lemmas that may be helpful in proving that property are dom_dom_in_policy (above) and example (below).

*}



definition executable_u_weak where
"executable_u_weak \<equiv> \<forall>s t a.
   reachable s \<and>
   reachable t \<and> s \<sim>schedDomain\<sim> t \<and> s \<sim>dom a s\<sim>t \<and> (\<exists>s'. (s,s')\<in>Step a) \<longrightarrow>
   (\<exists>t'. (t,t')\<in>Step a)"


lemma executable_u_weak_executable_u:
  "executable_u \<Longrightarrow> executable_u_weak"
  apply(fastforce simp:executable_u_def executable_u_weak_def)
  done

lemma executable_u_weakD:
  "\<lbrakk>executable_u_weak; reachable s; reachable t; (s,t)\<in>uwr schedDomain; (s,t)\<in>uwr (dom a s); (s,s')\<in>Step a\<rbrakk> \<Longrightarrow> \<exists>t'. (t,t')\<in>Step a"
  apply(fastforce simp: executable_u_weak_def)
  done

(* This is an example illustrating the use of the unwinding condition *)
lemma example:
  "\<lbrakk>integrity_u; executable_u_weak; reachable s; (s,s')\<in> Step a; 
   \<exists>s''.(s',s'')\<in>Step b; (dom a s, dom b s') \<notin> policy\<rbrakk> \<Longrightarrow> \<exists>s'.(s,s')\<in>Step b"
  apply(clarsimp simp: executable_u_weak_def)
  apply(erule_tac x=s' in allE, erule_tac x=s in allE, erule_tac x=b in allE,simp)
  apply(erule impE, safe)
     apply(blast intro:reachable_Step)
    apply(rule integrity_uD,simp_all add:uwr_refl)
    apply(rule notI,drule schedNotGlobalChannel)
    apply(erule notE,clarsimp simp:schedFlowsToAll)
   apply(rule integrity_uD,simp_all add:uwr_refl)
  apply blast
  done


(* This lemma, consequence of the example, shows the importance of the link between executability and the policy *)
  lemma dom_dom_in_policyI:
  "reachable s \<Longrightarrow>
   integrity_u \<Longrightarrow> executable_u_weak \<Longrightarrow> confidentiality_u_strong \<Longrightarrow>
    Executable [a, b] s \<Longrightarrow> \<not> Executable [b] s \<Longrightarrow> dom a s \<leadsto> dom b s "
  apply(rule classical, erule notE)
  apply clarsimp
  apply(frule_tac s'=s' in example,simp_all)
    apply blast
   apply(subgoal_tac "dom b s = dom b s'")
    apply simp
   apply(rule schedIncludesCurrentDom)
   apply(rule integrity_uD[THEN uwr_sym],simp_all add:uwr_refl)
   apply(case_tac "dom a s=schedDomain")
    apply(erule notE,simp add:schedFlowsToAll)
   apply(blast intro:schedNotGlobalChannel)
  apply(blast intro:reachable_Step)
  done



lemma self_step_eq:
  "\<lbrakk>reachable s ; confidentiality_u_strong ; (s,s')\<in>Step a\<rbrakk> \<Longrightarrow> (\<forall>s' t'.(s,s')\<in>Step a \<and> (s,t')\<in>Step a \<longrightarrow> (\<forall>d. (s',t')\<in> uwr d))"
  apply(clarsimp simp: confidentiality_u_strong_def)
  apply(erule_tac x=a in allE, erule_tac x=d in allE,erule_tac x=s in allE,erule_tac x=s in allE)
  apply(simp add: uwr_refl)
  done


lemma allDomains_step_equiv[rule_format]:
  "\<lbrakk>confidentiality_u_strong; reachable s; reachable t;
    \<forall>d. (s,t)\<in>uwr d\<rbrakk> \<Longrightarrow>
   (\<forall>s' t'. (s,s')\<in> Step a \<and> (t,t')\<in> Step a \<longrightarrow> (\<forall>d. (s',t')\<in> uwr d))"
  apply(fastforce simp:confidentiality_u_strong_def)
  done


lemma Executable_u_strong[rule_format]:
  "\<forall>s t a. reachable s \<and> reachable t \<and> (\<forall>d. (s,t)\<in>uwr d) \<and>
   Executable as s \<and> executable_u_weak \<and> confidentiality_u_strong \<longrightarrow> Executable as t"
  apply(induct as)
   apply simp
  apply clarsimp
  apply(subst (asm) executable_u_weak_def)
  apply(erule_tac x=s in allE, erule_tac x=t in allE, erule_tac x=a in allE)
  apply(blast dest:allDomains_step_equiv intro:reachable_Step)
  done


(*Use in sources_eq' proof to simplify steps*)
lemma Executable_StepD:
  "\<lbrakk>executable_u_weak ; confidentiality_u_strong ; reachable s ; (s,s')\<in>Step a; Executable (a#as) s\<rbrakk> \<Longrightarrow> Executable as s'"
  apply(clarsimp)
  apply(frule self_step_eq,auto)
  apply(erule_tac x=s'a in allE, erule_tac x=s' in allE,simp)
  apply(frule_tac s=s in reachable_Step,assumption)
  apply(frule_tac s=s and s'=s'a in reachable_Step,assumption)
  apply(rule Executable_u_strong,fastforce)
  done

(*Use in sources_eq' proof to simplify steps*)
lemma ExecutableD2:
  "\<lbrakk>executable_u_weak; confidentiality_u_strong; reachable s; reachable t; \<forall>d.(s,t)\<in> uwr d; (t,t')\<in> Step a; (s,s')\<in>Step a; Executable as s'\<rbrakk> \<Longrightarrow> Executable as t'"
  apply(rule Executable_u_strong[rule_format,where s=s'],simp)
  apply(rule conjI,blast intro:reachable_Step)+
  apply(clarsimp,rule_tac s=s and t=t in allDomains_step_equiv)
      apply blast+
  done


lemma sources_eq':
  "executable_u_weak \<and> confidentiality_u_strong \<and> s \<sim>schedDomain\<sim> t \<and>
   reachable s \<and> reachable t \<and> Executable as s \<and> Executable as t \<longrightarrow> sources as s u = sources as t u"
   proof (induct as arbitrary: s t)
  case Nil show ?case
   apply(simp add: sources_Nil)
   done
  next
  case (Cons a as) 
show ?case
  apply(clarsimp simp: sources_Cons)
  apply(rule insert_eq,simp)
  apply(rule un_eq,rule set_eqI,rule iffI)
    apply(erule_tac t="\<Union>{sources as t' u|t'. (t,t') \<in> Step a}" in subst[rotated])
    apply(simp only: Union_eq, simp only: UNION_eq[symmetric])
    apply(rule Un_eq)
      apply clarsimp
      apply(rule "Cons.hyps"[rule_format])
      apply simp
      apply(rule conjI)
       apply(blast intro: sched_equiv_preserved)
      apply(rule conjI,blast intro!: reachable_Step)+
       apply(rule conjI)
        apply(fastforce intro: ExecutableD2 simp:uwr_refl)
       apply(fastforce intro: ExecutableD2 simp:uwr_refl)
      apply(fastforce)
     apply(fastforce)
    apply(erule_tac t="\<Union>{sources as s' u|s'. (s,s') \<in> Step a}" in subst[rotated])
    apply(simp only: Union_eq, simp only: UNION_eq[symmetric])
    apply(rule Un_eq)
      apply clarsimp
      apply(rule "Cons.hyps"[rule_format])
      apply simp
      apply(rule conjI, blast intro: sched_equiv_preserved uwr_sym reachable_Step)+
      apply(rule conjI)
       apply(fastforce intro: ExecutableD2 simp:uwr_refl)
      apply(rule_tac s=s' and t=s'c in Executable_u_strong,clarsimp)
      apply(rule conjI,blast intro: reachable_Step)+
      apply(clarsimp,blast intro:self_step_eq[rule_format])
     apply(fastforce)
    apply(fastforce)
   apply(clarsimp simp: schedIncludesCurrentDom)
   apply safe
    apply(rule_tac x=v in exI,simp)
    apply(rule_tac x=s'a in exI,simp)
    apply(erule_tac t="sources as s'a u" in subst[rotated])
    apply(rule "Cons.hyps"[rule_format],simp)
    apply(rule conjI, blast intro:sched_equiv_preserved uwr_sym reachable_Step)+
    apply(rule ExecutableD2,simp_all add:uwr_refl)
   apply(rule_tac x=v in exI,simp)
   apply(rule_tac x=s' in exI,simp)
   apply(erule_tac t="sources as s' u" in subst[rotated])
   apply(rule "Cons.hyps"[rule_format])
   apply(rule conjI, blast intro: sched_equiv_preserved uwr_sym reachable_Step)+
   apply(rule conjI)
    apply(fastforce intro: ExecutableD2 simp:uwr_refl)+
  done
 qed


lemma sources_eq:
  "\<lbrakk>executable_u_weak; confidentiality_u_strong; s \<sim>schedDomain\<sim> t; reachable s; reachable t;  Executable as s; Executable as t\<rbrakk> \<Longrightarrow> 
  sources as s u = sources as t u"
  apply(rule sources_eq'[rule_format], simp)
  done


lemma in_policy:
  "\<lbrakk>integrity_u; reachable s; (s,s')\<in>Step a; (s,t)\<in>uwr u; (s',t)\<notin>uwr u\<rbrakk>\<Longrightarrow>(dom a s,u)\<in>policy"
  apply(auto dest:integrity_uD)
  done


lemma uwr_equiv_Cons_bothI:
   "\<lbrakk>reachable s; reachable t; executable_u_weak; (s,t)\<in>uwr schedDomain; (s,t)\<in>uwr (dom a s);
    \<forall> s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step a \<longrightarrow> uwr_equiv s' as t' bs u\<rbrakk> \<Longrightarrow>
    uwr_equiv s (a # as) t (a # bs) u"
  apply(clarsimp simp: uwr_equiv_def execution_Run)
  apply(safe)
   apply(frule Executable'D,fastforce)
   apply(rule Executable'I,clarsimp)
   apply(subst (asm) executable_u_weak_def,erule_tac x=s in allE,
      erule_tac x=t in allE, erule_tac x=a in allE,clarsimp)
   apply(erule impE,blast,safe)
   apply(blast dest:Executable'D reachable_Step Executable'I)
  apply(fastforce simp:reachable_Step execution_Run Executable'_def)
  done

lemma uwr_equiv_Cons_leftI:
   "\<lbrakk>reachable s; \<forall> s'. (s,s') \<in> Step a \<longrightarrow> uwr_equiv s' as t bs u\<rbrakk> \<Longrightarrow>
    uwr_equiv s (a # as) t bs u"
  apply(clarsimp simp: uwr_equiv_def execution_Run reachable_Step Executable'_def)
  apply fastforce
  done

lemma Noninfluence_gen_executable_u_weak:
  "Noninfluence_gen \<Longrightarrow> executable_u_weak"
  apply(clarsimp simp: executable_u_weak_def Noninfluence_gen_def)
  apply(drule_tac x="dom a s" in spec)
  apply(erule_tac x="[a]" in allE,
        erule_tac x=s in allE, erule_tac x="{t}" in allE)
  apply(clarsimp simp:uwr_equiv_def Executable'_def)
  apply(erule impE,fastforce simp:sources_Cons sources_Nil sameFor_dom_def)
  apply(erule conjE)
  apply(erule impE, fastforce simp:execution_Run)
  apply(frule_tac e=a in schedIncludesCurrentDom)
  apply(fastforce simp:ipurge_Cons ipurge_Nil sources_Cons sources_Nil Step_def)
  done

end

end
