(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      VcgExTotal.thy
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

section {* Examples for Total Correctness *}

theory VcgExTotal imports "../HeapList" "../Vcg" begin

record 'g vars = "'g state" +
  A_' :: nat
  I_' :: nat
  M_' :: nat
  N_' :: nat
  R_' :: nat
  S_' :: nat
  Abr_':: string


lemma "\<Gamma>\<turnstile>\<^sub>t \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          WHILE \<acute>M \<noteq> a
          INV \<lbrace>\<acute>S = \<acute>M * b \<and> \<acute>M \<le> a\<rbrace>
          VAR MEASURE a - \<acute>M
          DO \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply (auto)
done

lemma "\<Gamma>\<turnstile>\<^sub>t \<lbrace>\<acute>I \<le> 3\<rbrace> 
     WHILE \<acute>I < 10 INV \<lbrace>\<acute>I\<le> 10\<rbrace> VAR MEASURE 10 - \<acute>I
     DO
       \<acute>I :== \<acute>I + 1 
     OD
  \<lbrace>\<acute>I = 10\<rbrace>"
apply vcg
apply auto
done

text {* Total correctness of a nested loop. In the inner loop we have to 
express that the loop variable of the outer loop is not changed. We use
@{text "FIX"} to introduce a new logical variable
*}

lemma "\<Gamma>\<turnstile>\<^sub>t \<lbrace>\<acute>M=0 \<and> \<acute>N=0\<rbrace> 
      WHILE (\<acute>M < i) 
      INV \<lbrace>\<acute>M \<le> i \<and> (\<acute>M \<noteq> 0 \<longrightarrow> \<acute>N = j) \<and> \<acute>N \<le> j\<rbrace>
      VAR MEASURE (i - \<acute>M)
      DO
         \<acute>N :== 0;;
         WHILE (\<acute>N < j)
         FIX m. 
         INV \<lbrace>\<acute>M=m \<and> \<acute>N \<le> j\<rbrace>
         VAR MEASURE (j - \<acute>N)
         DO
           \<acute>N :== \<acute>N + 1
         OD;;
       \<acute>M :== \<acute>M + 1
       OD
       \<lbrace>\<acute>M=i \<and> (\<acute>M\<noteq>0 \<longrightarrow> \<acute>N=j)\<rbrace>"
apply vcg
apply simp_all
apply arith
done

primrec fac:: "nat \<Rightarrow> nat"
where
"fac 0 = 1" |
"fac (Suc n) = (Suc n) * fac n"

lemma fac_simp [simp]: "0 < i \<Longrightarrow>  fac i = i * fac (i - 1)"
  by (cases i) simp_all

procedures
  Fac (N | R) = "IF \<acute>N = 0 THEN \<acute>R :== 1
                       ELSE CALL Fac(\<acute>N - 1,\<acute>R);;
                            \<acute>R :== \<acute>N * \<acute>R
                       FI"

lemma (in Fac_impl) Fac_spec:
  shows "\<forall>n. \<Gamma>\<turnstile>\<^sub>t \<lbrace>\<acute>N=n\<rbrace> \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac n\<rbrace>"
  apply (hoare_rule HoareTotal.ProcRec1 [where r="measure (\<lambda>(s,p). \<^bsup>s\<^esup>N)"])
  apply vcg
  apply simp
  done



procedures
  p91(R,N | R) = "IF 100 < \<acute>N THEN \<acute>R :== \<acute>N - 10
                      ELSE \<acute>R :== CALL p91(\<acute>R,\<acute>N+11);; 
                           \<acute>R :== CALL p91(\<acute>R,\<acute>R) FI"

  
  p91_spec: "\<forall>n. \<Gamma>\<turnstile>\<^sub>t \<lbrace>\<acute>N=n\<rbrace> \<acute>R :== PROC p91(\<acute>R,\<acute>N) 
                        \<lbrace>if 100 < n then \<acute>R = n - 10 else \<acute>R = 91\<rbrace>,{}"

lemma (in p91_impl) p91_spec:
  shows "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} \<acute>R :== PROC p91(\<acute>R,\<acute>N) 
                       \<lbrace>if 100 < \<^bsup>\<sigma>\<^esup>N then \<acute>R = \<^bsup>\<sigma>\<^esup>N - 10 else \<acute>R = 91\<rbrace>,{}"
  apply (hoare_rule HoareTotal.ProcRec1 [where r="measure (\<lambda>(s,p). 101 - \<^bsup>s\<^esup>N)"])
  apply vcg
  apply clarsimp
  apply arith
  done

record globals_list = 
  next_' :: "ref \<Rightarrow> ref"
  cont_' :: "ref \<Rightarrow> nat"

record 'g list_vars = "'g state" +
  p_'    :: "ref"
  q_'    :: "ref"
  r_'    :: "ref"
  root_' :: "ref"
  tmp_'  :: "ref"

procedures
  append(p,q|p) = 
    "IF \<acute>p=Null THEN \<acute>p :== \<acute>q ELSE \<acute>p\<rightarrow>\<acute>next :== CALL append(\<acute>p\<rightarrow>\<acute>next,\<acute>q) FI"

lemma (in append_impl)
  shows 
   "\<forall>\<sigma> Ps Qs. \<Gamma>\<turnstile>\<^sub>t 
      \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<rbrace>  
       \<acute>p :== PROC append(\<acute>p,\<acute>q) 
      \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
   apply (hoare_rule HoareTotal.ProcRec1
            [where r="measure (\<lambda>(s,p). length (list \<^bsup>s\<^esup>p \<^bsup>s\<^esup>next))"])
   apply vcg
   apply (fastforce  simp add: List_list)
   done


lemma (in append_impl)
  shows 
   "\<forall>\<sigma> Ps Qs. \<Gamma>\<turnstile>\<^sub>t 
      \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<rbrace>  
       \<acute>p :== PROC append(\<acute>p,\<acute>q) 
      \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
   apply (hoare_rule HoareTotal.ProcRec1
            [where r="measure (\<lambda>(s,p). length (list \<^bsup>s\<^esup>p \<^bsup>s\<^esup>next))"])
   apply vcg
   apply (fastforce  simp add: List_list)
   done

lemma (in append_impl)
  shows
  append_spec: 
   "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t ({\<sigma>} \<inter> \<lbrace>islist \<acute>p \<acute>next\<rbrace>)  \<acute>p :== PROC append(\<acute>p,\<acute>q) 
    \<lbrace>\<forall>Ps Qs. List \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>next Ps \<and>  List \<^bsup>\<sigma>\<^esup>q \<^bsup>\<sigma>\<^esup>next Qs \<and> set Ps \<inter> set Qs = {} 
     \<longrightarrow>
     List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
   apply (hoare_rule HoareTotal.ProcRec1
            [where r="measure (\<lambda>(s,p). length (list \<^bsup>s\<^esup>p \<^bsup>s\<^esup>next))"])
   apply vcg
   apply fastforce
   done
 
lemma "\<Gamma>\<turnstile>\<lbrace>List \<acute>p \<acute>next Ps\<rbrace>
       \<acute>q :== Null;;
       WHILE \<acute>p \<noteq> Null INV \<lbrace>\<exists>Ps' Qs'. List \<acute>p \<acute>next Ps' \<and> List \<acute>q \<acute>next Qs' \<and>
                             set Ps' \<inter> set Qs' = {} \<and>
                             rev Ps' @ Qs' = rev Ps\<rbrace> 
        DO
         \<acute>r :== \<acute>p;; \<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
         \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; \<acute>q :== \<acute>r
       OD;;
       \<acute>p :==\<acute>q
       \<lbrace>List \<acute>p \<acute>next (rev Ps)\<rbrace> "
apply vcg 
apply   clarsimp
apply  clarsimp
apply force
apply simp
done

lemma conjI2: "\<lbrakk>Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P \<and> Q"
by blast

procedures Rev(p|p) =
      "\<acute>q :== Null;;
       WHILE \<acute>p \<noteq> Null 
       DO
         \<acute>r :== \<acute>p;; \<lbrace>\<acute>p \<noteq> Null\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
         \<lbrace>\<acute>r \<noteq> Null\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; \<acute>q :== \<acute>r
       OD;;
       \<acute>p :==\<acute>q"
 Rev_spec: 
  "\<forall>Ps. \<Gamma>\<turnstile>\<^sub>t \<lbrace>List \<acute>p \<acute>next Ps\<rbrace> \<acute>p :== PROC Rev(\<acute>p) \<lbrace>List \<acute>p \<acute>next (rev Ps)\<rbrace>"
 Rev_modifies:
  "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} \<acute>p :== PROC Rev(\<acute>p) {t. t may_only_modify_globals \<sigma> in [next]}"

text {* We only need partial correctness of modifies clause!*}



lemma upd_hd_next:
  assumes p_ps: "List p next (p#ps)"
  shows "List (next p) (next(p := q)) ps"
proof -
  from p_ps
  have "p \<notin> set ps" 
    by auto
  with p_ps show ?thesis
    by simp
qed

lemma (in Rev_impl) shows
 Rev_spec: 
  "\<forall>Ps. \<Gamma>\<turnstile>\<^sub>t \<lbrace>List \<acute>p \<acute>next Ps\<rbrace> \<acute>p :== PROC Rev(\<acute>p) \<lbrace>List \<acute>p \<acute>next (rev Ps)\<rbrace>"
apply (hoare_rule HoareTotal.ProcNoRec1)
apply (hoare_rule anno =
       "\<acute>q :== Null;;
       WHILE \<acute>p \<noteq> Null INV \<lbrace>\<exists>Ps' Qs'. List \<acute>p \<acute>next Ps' \<and> List \<acute>q \<acute>next Qs' \<and>
                             set Ps' \<inter> set Qs' = {} \<and>
                             rev Ps' @ Qs' = rev Ps\<rbrace>
       VAR MEASURE (length (list \<acute>p \<acute>next) )
        DO
         \<acute>r :== \<acute>p;; \<lbrace>\<acute>p \<noteq> Null\<rbrace>\<longmapsto>\<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
         \<lbrace>\<acute>r \<noteq> Null\<rbrace>\<longmapsto>\<acute>r\<rightarrow>\<acute>next :== \<acute>q;; \<acute>q :== \<acute>r
       OD;;
       \<acute>p :==\<acute>q" in HoareTotal.annotateI)
apply vcg 
apply   clarsimp
apply  clarsimp
apply  (rule conjI2)
apply   force
apply  clarsimp
apply  (subgoal_tac "List p next (p#ps)")
prefer 2 apply simp
apply  (frule_tac q=q in upd_hd_next)
apply  (simp only: List_list)
apply  simp
apply simp
done


lemma (in Rev_impl) shows
 Rev_modifies:
  "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV \<^esub>{\<sigma>} \<acute>p :== PROC Rev(\<acute>p) {t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (vcg spec=modifies)
done

lemma "\<Gamma>\<turnstile>\<^sub>t \<lbrace>List \<acute>p \<acute>next Ps\<rbrace>
       \<acute>q :== Null;;
       WHILE \<acute>p \<noteq> Null INV \<lbrace>\<exists>Ps' Qs'. List \<acute>p \<acute>next Ps' \<and> List \<acute>q \<acute>next Qs' \<and>
                             set Ps' \<inter> set Qs' = {} \<and>
                             rev Ps' @ Qs' = rev Ps\<rbrace>
       VAR MEASURE (length (list \<acute>p \<acute>next) )
        DO
         \<acute>r :== \<acute>p;; \<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
         \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; \<acute>q :== \<acute>r
       OD;;
       \<acute>p :==\<acute>q
       \<lbrace>List \<acute>p \<acute>next (rev Ps)\<rbrace> "
apply vcg 
apply   clarsimp
apply  clarsimp
apply  (rule conjI2)
apply   force
apply  clarsimp
apply  (subgoal_tac "List p next (p#ps)")
prefer 2 apply simp
apply  (frule_tac q=q in upd_hd_next)
apply  (simp only: List_list)
apply  simp
apply simp
done




procedures 
  pedal(N,M) = "IF 0 < \<acute>N THEN
                            IF 0 < \<acute>M THEN CALL coast(\<acute>N- 1,\<acute>M- 1) FI;;
                            CALL pedal(\<acute>N- 1,\<acute>M)
                         FI"

and
 
  coast(N,M) = "CALL pedal(\<acute>N,\<acute>M);;
                         IF 0 < \<acute>M THEN CALL coast(\<acute>N,\<acute>M- 1) FI"


ML {* ML_Thms.bind_thm ("HoareTotal_ProcRec2", Hoare.gen_proc_rec @{context} Hoare.Total 2)*}


lemma (in pedal_coast_clique)
  shows "(\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace>  PROC pedal(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>) \<and>
         (\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC coast(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>)"
  apply (hoare_rule HoareTotal_ProcRec2
          [where ?r= "inv_image (measure (\<lambda>m. m) <*lex*> 
                                  measure (\<lambda>p. if p = coast_'proc then 1 else 0))
                      (\<lambda>(s,p). (\<^bsup>s\<^esup>N + \<^bsup>s\<^esup>M,p))"])
  apply simp_all
  apply  vcg
  apply  simp
  apply vcg
  apply simp
  done

lemma (in pedal_coast_clique)
  shows "(\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC pedal(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>) \<and>
         (\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC coast(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>)"
  apply (hoare_rule HoareTotal_ProcRec2
          [where ?r= "inv_image (measure (\<lambda>m. m) <*lex*> 
                                  measure (\<lambda>p. if p = coast_'proc then 1 else 0))
                      (\<lambda>(s,p). (\<^bsup>s\<^esup>N + \<^bsup>s\<^esup>M,p))"])
  apply simp_all
  apply  vcg
  apply  simp
  apply vcg
  apply simp
  done




lemma (in pedal_coast_clique)
  shows "(\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC pedal(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>) \<and>
         (\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC coast(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>)"
  apply(hoare_rule HoareTotal_ProcRec2
     [where ?r= "measure (\<lambda>(s,p). \<^bsup>s\<^esup>N + \<^bsup>s\<^esup>M + (if p = coast_'proc then 1 else 0))"])
  apply simp_all
  apply  vcg
  apply  simp
  apply  arith
  apply vcg
  apply simp
  done


lemma (in pedal_coast_clique) 
  shows "(\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC pedal(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>) \<and>
         (\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC coast(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>)"
  apply(hoare_rule HoareTotal_ProcRec2
     [where ?r= "(\<lambda>(s,p). \<^bsup>s\<^esup>N) <*mlex*> (\<lambda>(s,p). \<^bsup>s\<^esup>M) <*mlex*>
                 measure (\<lambda>(s,p). if p = coast_'proc then 1 else 0)"])
   apply  simp_all
   apply  vcg
   apply  simp
   apply vcg
   apply simp
   done


lemma (in pedal_coast_clique)
  shows "(\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC pedal(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>) \<and>
         (\<Gamma>\<turnstile>\<^sub>t \<lbrace>True\<rbrace> PROC coast(\<acute>N,\<acute>M) \<lbrace>True\<rbrace>)"
  apply(hoare_rule HoareTotal_ProcRec2
     [where ?r= "measure (\<lambda>s. \<^bsup>s\<^esup>N + \<^bsup>s\<^esup>M) <*lex*> 
                 measure (\<lambda>p. if p = coast_'proc then 1 else 0)"])
   apply simp_all
   apply  vcg
   apply  simp
   apply vcg
   apply simp
   done


end