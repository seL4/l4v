(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Hoare.thy
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

section {* Auxiliary Definitions/Lemmas to Facilitate Hoare Logic *}
theory Hoare imports HoarePartial HoareTotal begin


syntax 

"_hoarep_emptyFaults"::
"[('s,'p,'f) body,('s,'p) quadruple set,
   'f set,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
    ("(3_,_/\<turnstile> (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoarep_emptyCtx"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
    ("(3_/\<turnstile>\<^bsub>'/_\<^esub> (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoarep_emptyCtx_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
    ("(3_/\<turnstile> (_/ (_)/ _,/_))" [61,1000,20,1000,1000]60)

"_hoarep_noAbr"::
"[('s,'p,'f) body,('s,'p) quadruple set,'f set,
    's assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_,_/\<turnstile>\<^bsub>'/_\<^esub> (_/ (_)/ _))" [61,60,60,1000,20,1000]60)

"_hoarep_noAbr_emptyFaults"::
"[('s,'p,'f) body,('s,'p) quadruple set,'s assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_,_/\<turnstile> (_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoarep_emptyCtx_noAbr"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_/\<turnstile>\<^bsub>'/_\<^esub> (_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoarep_emptyCtx_noAbr_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_/\<turnstile> (_/ (_)/ _))" [61,1000,20,1000]60)



"_hoaret_emptyFaults"::
"[('s,'p,'f) body,('s,'p) quadruple set,
    's assn,('s,'p,'f) com, 's assn,'s assn] => bool"
    ("(3_,_/\<turnstile>\<^sub>t (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoaret_emptyCtx"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
    ("(3_/\<turnstile>\<^sub>t\<^bsub>'/_\<^esub> (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoaret_emptyCtx_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
    ("(3_/\<turnstile>\<^sub>t (_/ (_)/ _,/_))" [61,1000,20,1000,1000]60)

"_hoaret_noAbr"::
"[('s,'p,'f) body,'f set, ('s,'p) quadruple set,
    's assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_,_/\<turnstile>\<^sub>t\<^bsub>'/_\<^esub> (_/ (_)/ _))" [61,60,60,1000,20,1000]60)

"_hoaret_noAbr_emptyFaults"::
"[('s,'p,'f) body,('s,'p) quadruple set,'s assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_,_/\<turnstile>\<^sub>t (_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoaret_emptyCtx_noAbr"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_/\<turnstile>\<^sub>t\<^bsub>'/_\<^esub> (_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoaret_emptyCtx_noAbr_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn] => bool"
    ("(3_/\<turnstile>\<^sub>t (_/ (_)/ _))" [61,1000,20,1000]60)


syntax (ASCII)

"_hoarep_emptyFaults"::
"[('s,'p,'f) body,('s,'p) quadruple set,
     's assn,('s,'p,'f) com, 's assn,'s assn] \<Rightarrow> bool"
   ("(3_,_/|- (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoarep_emptyCtx"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
   ("(3_/|-'/_ (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoarep_emptyCtx_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
   ("(3_/|-(_/ (_)/ _,/_))" [61,1000,20,1000,1000]60)

"_hoarep_noAbr"::
"[('s,'p,'f) body,('s,'p) quadruple set,'f set,
   's assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_,_/|-'/_ (_/ (_)/ _))" [61,60,60,1000,20,1000]60)

"_hoarep_noAbr_emptyFaults"::
"[('s,'p,'f) body,('s,'p) quadruple set,'s assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_,_/|-(_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoarep_emptyCtx_noAbr"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_/|-'/_ (_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoarep_emptyCtx_noAbr_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_/|-(_/ (_)/ _))" [61,1000,20,1000]60)

"_hoaret_emptyFault"::
"[('s,'p,'f) body,('s,'p) quadruple set,
     's assn,('s,'p,'f) com, 's assn,'s assn] => bool"
   ("(3_,_/|-t (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoaret_emptyCtx"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
   ("(3_/|-t'/_ (_/ (_)/ _,/_))" [61,60,1000,20,1000,1000]60)

"_hoaret_emptyCtx_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn,'s assn] => bool"
   ("(3_/|-t(_/ (_)/ _,/_))" [61,1000,20,1000,1000]60)

"_hoaret_noAbr"::
"[('s,'p,'f) body,('s,'p) quadruple set,'f set,
   's assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_,_/|-t'/_ (_/ (_)/ _))" [61,60,60,1000,20,1000]60)

"_hoaret_noAbr_emptyFaults"::
"[('s,'p,'f) body,('s,'p) quadruple set,'s assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_,_/|-t(_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoaret_emptyCtx_noAbr"::
"[('s,'p,'f) body,'f set,'s assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_/|-t'/_ (_/ (_)/ _))" [61,60,1000,20,1000]60)

"_hoaret_emptyCtx_noAbr_emptyFaults"::
"[('s,'p,'f) body,'s assn,('s,'p,'f) com, 's assn] => bool"
   ("(3_/|-t(_/ (_)/ _))" [61,1000,20,1000]60)

translations
 

 "\<Gamma>\<turnstile> P c Q,A"  == "\<Gamma>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A" 
 "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"  == "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q,A"

 "\<Gamma>,\<Theta>\<turnstile> P c Q"  == "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q"
 "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q"  == "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,{}"
 "\<Gamma>,\<Theta>\<turnstile> P c Q,A" == "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A" 

 "\<Gamma>\<turnstile> P c Q"    ==  "\<Gamma>\<turnstile>\<^bsub>/{}\<^esub> P c Q"
 "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> P c Q"  == "\<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> P c Q"
 "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> P c Q"  <=  "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> P c Q,{}"
 "\<Gamma>\<turnstile> P c Q"    <=  "\<Gamma>\<turnstile> P c Q,{}"




 "\<Gamma>\<turnstile>\<^sub>t P c Q,A"   == "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
 "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"  == "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"

 "\<Gamma>,\<Theta>\<turnstile>\<^sub>t P c Q"   == "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q"
 "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q" == "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,{}"
 "\<Gamma>,\<Theta>\<turnstile>\<^sub>t P c Q,A"   == "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
 
 "\<Gamma>\<turnstile>\<^sub>t P c Q"    == "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q"
 "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q"  == "\<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q"
 "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q"  <=  "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,{}"
 "\<Gamma>\<turnstile>\<^sub>t P c Q"    <=  "\<Gamma>\<turnstile>\<^sub>t P c Q,{}"


term "\<Gamma>\<turnstile> P c Q"
term "\<Gamma>\<turnstile> P c Q,A"

term "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> P c Q"
term "\<Gamma>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"

term "\<Gamma>,\<Theta>\<turnstile> P c Q"
term "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q"

term "\<Gamma>,\<Theta>\<turnstile> P c Q,A"
term "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A"


term "\<Gamma>\<turnstile>\<^sub>t P c Q"
term "\<Gamma>\<turnstile>\<^sub>t P c Q,A"

term "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q"
term "\<Gamma>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"

term "\<Gamma>,\<Theta>\<turnstile> P c Q"
term "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q"

term "\<Gamma>,\<Theta>\<turnstile> P c Q,A"
term "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"


locale hoare =
  fixes \<Gamma>::"('s,'p,'f) body" 


primrec assoc:: "('a \<times>'b) list \<Rightarrow> 'a \<Rightarrow> 'b "
where
"assoc [] x = undefined" |
"assoc (p#ps) x = (if fst p = x then (snd p) else assoc ps x)"

lemma conjE_simp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)"
  by rule simp_all

lemma CollectInt_iff: "{s. P s} \<inter> {s. Q s} = {s. P s \<and> Q s}"
  by auto

lemma Compl_Collect:"-(Collect b) = {x. \<not>(b x)}"
  by fastforce

lemma Collect_False: "{s. False} = {}"
  by simp

lemma Collect_True: "{s. True} = UNIV"
  by simp

lemma triv_All_eq: "\<forall>x. P \<equiv> P"
  by simp

lemma triv_Ex_eq: "\<exists>x. P \<equiv> P"
  by simp

lemma Ex_True: "\<exists>b. b"
   by blast

lemma Ex_False: "\<exists>b. \<not>b"
  by blast

definition mex::"('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "mex P = Ex P"

definition meq::"'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "meq s Z = (s = Z)"

lemma subset_unI1: "A \<subseteq> B \<Longrightarrow> A \<subseteq> B \<union> C" 
  by blast

lemma subset_unI2: "A \<subseteq> C \<Longrightarrow> A \<subseteq> B \<union> C" 
  by blast

lemma split_paired_UN: "(\<Union>p. (P p)) = (\<Union>a b. (P (a,b)))" 
  by auto

lemma in_insert_hd: "f \<in> insert f X"
  by simp
 
lemma lookup_Some_in_dom: "\<Gamma> p = Some bdy \<Longrightarrow> p \<in> dom \<Gamma>"
  by auto

lemma unit_object: "(\<forall>u::unit. P u) = P ()"
  by auto

lemma unit_ex: "(\<exists>u::unit. P u) = P ()"
  by auto

lemma unit_meta: "(\<And>(u::unit). PROP P u) \<equiv> PROP P ()"
  by auto

lemma unit_UN: "(\<Union>z::unit. P z) = P ()"
  by auto

lemma subset_singleton_insert1: "y = x \<Longrightarrow> {y} \<subseteq> insert x A"
  by auto

lemma subset_singleton_insert2: "{y} \<subseteq> A \<Longrightarrow> {y} \<subseteq> insert x A"
  by auto

lemma in_Specs_simp: "(\<forall>x\<in>\<Union>Z. {(P Z, p, Q Z, A Z)}. Prop x) =
       (\<forall>Z. Prop (P Z,p,Q Z,A Z))"
  by auto

lemma in_set_Un_simp: "(\<forall>x\<in>A \<union> B. P x) = ((\<forall>x \<in> A. P x) \<and> (\<forall>x \<in> B. P x))"
  by auto

lemma split_all_conj: "(\<forall>x. P x \<and> Q x) = ((\<forall>x. P x) \<and> (\<forall>x. Q x))"
  by blast

lemma image_Un_single_simp: "f ` (\<Union>Z. {P Z}) = (\<Union>Z. {f (P Z)}) "
  by auto



lemma measure_lex_prod_def': 
  "f <*mlex*> r \<equiv> ({(x,y). (x,y) \<in> measure f \<or> f x=f y \<and> (x,y) \<in>  r})"
  by (auto simp add: mlex_prod_def inv_image_def)

lemma in_measure_iff: "(x,y) \<in> measure f = (f x < f y)"
  by (simp add: measure_def inv_image_def)

lemma in_lex_iff: 
  "((a,b),(x,y)) \<in> r <*lex*> s = ((a,x) \<in> r \<or> (a=x \<and> (b,y)\<in>s))"
  by (simp add: lex_prod_def)

lemma in_mlex_iff:
  "(x,y) \<in> f <*mlex*> r = (f x < f y \<or> (f x=f y \<and> (x,y) \<in> r))"
  by (simp add: measure_lex_prod_def' in_measure_iff)

lemma in_inv_image_iff: "(x,y) \<in> inv_image r f = ((f x, f y) \<in> r)" 
  by (simp add: inv_image_def)

text {* This is actually the same as @{thm [source] wf_mlex}. However, this basic
proof took me so long that I'm not willing to delete it.
*}
lemma wf_measure_lex_prod [simp,intro]:
  assumes wf_r: "wf r"
  shows "wf (f <*mlex*> r)"
proof (rule ccontr)
  assume " \<not> wf (f <*mlex*> r)"
  then
  obtain g where "\<forall>i. (g (Suc i), g i) \<in> f <*mlex*> r"
    by (auto simp add: wf_iff_no_infinite_down_chain)
  hence g: "\<forall>i. (g (Suc i), g i) \<in> measure f \<or>
    f (g (Suc i)) = f (g i) \<and> (g (Suc i), g i) \<in> r"
    by (simp add: measure_lex_prod_def')
  hence le_g: "\<forall>i. f (g (Suc i)) \<le> f (g i)"
    by (auto simp add: in_measure_iff order_le_less)
  have "wf (measure f)"
    by simp
  hence " \<forall>Q. (\<exists>x. x \<in> Q) \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> measure f \<longrightarrow> y \<notin> Q)"
    by (simp add: wf_eq_minimal)
  from this [rule_format, of "g ` UNIV"]
  have "\<exists>z. z \<in> range g \<and> (\<forall>y. (y, z) \<in> measure f \<longrightarrow> y \<notin> range g)"
    by auto
  then obtain z where 
    z: "z \<in> range g" and
    min_z: "\<forall>y. f y < f z \<longrightarrow> y \<notin> range g"
    by (auto simp add: in_measure_iff)
  from z obtain k where 
    k: "z = g k"
    by auto
  have "\<forall>i. k \<le> i \<longrightarrow> f (g i) = f (g k)" 
  proof (intro allI impI) 
    fix i
    assume "k \<le> i" then show "f (g i) = f (g k)"
    proof (induct i)
      case 0
      have "k \<le> 0" by fact hence "k = 0" by simp
      thus "f (g 0) = f (g k)"
        by simp
    next
      case (Suc n)
      have k_Suc_n: "k \<le> Suc n" by fact
      then show "f (g (Suc n)) = f (g k)"
      proof (cases "k = Suc n")
        case True
        thus ?thesis by simp
      next
        case False
        with k_Suc_n
        have "k \<le> n"
          by simp
        with Suc.hyps
        have n_k: "f (g n) = f (g k)" by simp
        from le_g have le: "f (g (Suc n)) \<le> f (g n)"
          by simp
        show ?thesis
        proof (cases "f (g (Suc n)) = f (g n)")
          case True with n_k show ?thesis by simp
        next
          case False
          with le have "f (g (Suc n)) < f (g n)"
            by simp
          with n_k k have "f (g (Suc n)) < f z"
            by simp
          with min_z have "g (Suc n) \<notin> range g"
            by blast
          hence False by simp
          thus ?thesis
            by simp
        qed
      qed
    qed
  qed
  with k [symmetric] have "\<forall>i. k \<le> i \<longrightarrow> f (g i) = f z" 
    by simp
  hence "\<forall>i. k \<le> i \<longrightarrow> f (g (Suc i)) = f (g i)"
    by simp
  with g have "\<forall>i. k \<le> i \<longrightarrow> (g (Suc i),(g i)) \<in> r"
    by (auto simp add: in_measure_iff order_less_le )
  hence "\<forall>i. (g (Suc (i+k)),(g (i+k))) \<in> r"
    by simp
  then
  have "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> r"
    by - (rule exI [where x="\<lambda>i. g (i+k)"],simp) 
  with wf_r show False
    by (simp add: wf_iff_no_infinite_down_chain)
qed

lemmas all_imp_to_ex = all_simps (5)  
(*"!!P Q. (ALL x. P x --> Q) = ((EX x. P x) --> Q)"

 Avoid introduction of existential quantification of states on negative
 position.
*)

lemma all_imp_eq_triv: "(\<forall>x. x = k \<longrightarrow> Q) = Q"
                       "(\<forall>x. k = x \<longrightarrow> Q) = Q"
  by auto
  
end