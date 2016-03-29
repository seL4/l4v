(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      ClosureEx.thy
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

theory ClosureEx
imports "../Vcg" "../Simpl_Heap" Closure
begin


record globals = 
 cnt_' :: "ref \<Rightarrow> nat"
 alloc_' :: "ref list"
 free_' :: "nat"
record 'g vars = "'g state" +
 p_':: ref
 r_':: nat
 n_':: nat
 m_':: nat
 c_':: "(string \<times> ref) list \<times> string"
 d_':: "(string \<times> ref) list \<times> string"
 e_':: "(string \<times> nat) list \<times> string"


definition "var\<^sub>n = [''n''\<mapsto> (\<lambda>x. n_'_update (\<lambda>_. x)),
                    ''m''\<mapsto> (\<lambda>x. m_'_update (\<lambda>_. x))]"
definition "upd\<^sub>n = gen_upd var\<^sub>n"

lemma upd\<^sub>n_ap: "upd\<^sub>n (fst (ap es (es',p))) = upd\<^sub>n es' \<circ> upd\<^sub>n es"
  by (simp add: upd\<^sub>n_def gen_upd_ap)


lemma
"\<Gamma>\<turnstile>\<lbrace>\<acute>n=n\<^sub>0 \<and> (\<forall>i j. \<Gamma>\<turnstile> \<lbrace>\<acute>n=i \<and> \<acute>m=j\<rbrace> callClosure upd\<^sub>n \<acute>e \<lbrace>\<acute>r=i + j\<rbrace>)\<rbrace> 
      \<acute>e :== (ap [(''n'',\<acute>n)] \<acute>e) 
   \<lbrace>\<forall>j. \<Gamma>\<turnstile> \<lbrace>\<acute>m=j\<rbrace> callClosure upd\<^sub>n \<acute>e \<lbrace>\<acute>r=n\<^sub>0 + j\<rbrace>\<rbrace>"
apply vcg_step
apply clarify
apply (rule ap_closure [where var=var\<^sub>n, folded upd\<^sub>n_def])
apply clarsimp
apply (rename_tac s s')
apply (erule_tac x="n_' s" in allE) 
apply (erule_tac x="m_' s'" in allE) 
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply (assumption)
apply (simp add: upd\<^sub>n_def gen_upd_def var\<^sub>n_def)
done


definition "var = [''p''\<mapsto> (\<lambda>x. p_'_update (\<lambda>_. x))]"
definition "upd = gen_upd var"

procedures Inc(p|r) =
 "\<acute>p\<rightarrow>\<acute>cnt :== \<acute>p\<rightarrow>\<acute>cnt + 1;;
  \<acute>r :== \<acute>p\<rightarrow>\<acute>cnt"

lemma (in Inc_impl)
 "\<forall>i p. \<Gamma>\<turnstile> \<lbrace>\<acute>p\<rightarrow>\<acute>cnt = i\<rbrace> \<acute>r :== PROC Inc(\<acute>p) \<lbrace>\<acute>r=i+1 \<and> \<acute>p\<rightarrow>\<acute>cnt = i+1\<rbrace>"
  apply vcg
  apply simp
  done
  
procedures (imports Inc_signature) NewCounter(|c) =
"\<acute>p :== NEW 1 [\<acute>cnt :== 0];;
 \<acute>c :== ([(''p'',\<acute>p)],Inc_'proc)" 


locale NewCounter_impl' = NewCounter_impl + Inc_impl
lemma (in NewCounter_impl')
shows 
  "\<forall>alloc. \<Gamma>\<turnstile> \<lbrace>1 \<le> \<acute>free\<rbrace> \<acute>c :== PROC NewCounter() 
          \<lbrace>\<exists>p. p\<rightarrow>\<acute>cnt = 0 \<and>
               (\<forall>i. \<Gamma>\<turnstile> \<lbrace>p\<rightarrow>\<acute>cnt = i\<rbrace> callClosure upd \<acute>c \<lbrace>\<acute>r=i+1 \<and> p\<rightarrow>\<acute>cnt = i+1\<rbrace>)\<rbrace>"
apply vcg
apply simp
apply (rule_tac x="new (set alloc)" in exI)
apply simp
apply (simp add: callClosure_def)
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
apply (simp add: upd_def var_def gen_upd_def)
done

lemma (in NewCounter_impl')

shows 
  "\<forall>alloc. \<Gamma>\<turnstile> \<lbrace>1 \<le> \<acute>free\<rbrace> \<acute>c :== PROC NewCounter() 
          \<lbrace>\<exists>p. p\<rightarrow>\<acute>cnt = 0 \<and>
               (\<forall>i. \<Gamma>\<turnstile> \<lbrace>p\<rightarrow>\<acute>cnt = i\<rbrace> callClosure upd \<acute>c \<lbrace>\<acute>r=i+1 \<and> p\<rightarrow>\<acute>cnt = i+1\<rbrace>)\<rbrace>"
apply vcg
apply simp
apply (rule_tac x="new (set alloc)" in exI)
apply simp
apply (simp add: callClosure_def)
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
apply (simp add: upd_def var_def gen_upd_def)
done

lemma (in NewCounter_impl')
shows NewCounter_spec:
  "\<forall>alloc. \<Gamma>\<turnstile> \<lbrace>1 \<le> \<acute>free \<and> \<acute>alloc=alloc\<rbrace> \<acute>c :== PROC NewCounter() 
          \<lbrace>\<exists>p. p \<notin> set alloc \<and> p \<in> set \<acute>alloc \<and> p \<noteq> Null \<and> p\<rightarrow>\<acute>cnt = 0 \<and>
               (\<forall>i. \<Gamma>\<turnstile> \<lbrace>p\<rightarrow>\<acute>cnt = i\<rbrace> callClosure upd \<acute>c \<lbrace>\<acute>r=i+1 \<and> p\<rightarrow>\<acute>cnt = i+1\<rbrace>)\<rbrace>"
apply vcg
apply clarsimp
apply (rule_tac x="new (set alloc)" in exI)
apply simp
apply (simp add: callClosure_def)
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
apply (simp add: upd_def var_def gen_upd_def)
done



lemma "\<Gamma>\<turnstile>\<lbrace>\<exists>p. p \<noteq> Null \<and> p\<rightarrow>\<acute>cnt = i \<and>
              (\<forall>i. \<Gamma>\<turnstile> \<lbrace>p\<rightarrow>\<acute>cnt = i\<rbrace> callClosure upd \<acute>c \<lbrace>\<acute>r=i+1 \<and> p\<rightarrow>\<acute>cnt = i+1\<rbrace>)\<rbrace>
           dynCallClosure (\<lambda>s. s) upd c_' (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) 
                         (\<lambda>s t. Basic (\<lambda>u. u\<lparr>r_' := r_' t\<rparr>))
           \<lbrace>\<acute>r=i+1\<rbrace>"
apply (rule conseq_extract_pre)
apply clarify
apply (rule dynCallClosureFix)
apply (simp only: Ball_def)
prefer 3
apply (assumption)
prefer 2
apply vcg_step
apply vcg_step
apply (simp only: simp_thms)
apply clarsimp
done

lemma (in NewCounter_impl')
 shows "\<Gamma>\<turnstile> \<lbrace>1 \<le> \<acute>free\<rbrace> 
             \<acute>c :== CALL NewCounter ();;
             dynCallClosure (\<lambda>s. s) upd c_' (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) 
                         (\<lambda>s t. Basic (\<lambda>u. u\<lparr>r_' := r_' t\<rparr>))
           \<lbrace>\<acute>r=1\<rbrace>"
apply vcg_step
apply (rule dynCallClosure)
prefer 2
apply vcg_step
apply vcg_step
apply vcg_step
apply clarsimp
apply (erule_tac x=0 in allE)
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply (assumption)
apply simp
done


lemma (in NewCounter_impl')
 shows "\<Gamma>\<turnstile> \<lbrace>1 \<le> \<acute>free\<rbrace> 
             \<acute>c :== CALL NewCounter ();;
             dynCallClosure (\<lambda>s. s) upd c_' (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) 
                         (\<lambda>s t. Basic (\<lambda>u. u\<lparr>r_' := r_' t\<rparr>));;
             dynCallClosure (\<lambda>s. s) upd c_' (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) 
                         (\<lambda>s t. Basic (\<lambda>u. u\<lparr>r_' := r_' t\<rparr>))
           \<lbrace>\<acute>r=2\<rbrace>"
apply vcg_step
apply (rule dynCallClosure)
prefer 2
apply vcg_step
apply vcg_step
apply vcg_step
apply (rule dynCallClosure)
apply vcg_step
apply vcg_step
apply vcg_step

apply clarsimp
apply (subgoal_tac "\<Gamma>\<turnstile> \<lbrace>p\<rightarrow>\<acute>cnt = 0\<rbrace> callClosure upd (c_' t) \<lbrace>\<acute>r = Suc 0 \<and> p\<rightarrow>\<acute>cnt = Suc 0\<rbrace>")
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply assumption
apply clarsimp
apply (erule_tac x=1 in allE)
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply assumption
apply clarsimp
apply (erule allE)
apply assumption
done


lemma (in NewCounter_impl')
 shows "\<Gamma>\<turnstile> \<lbrace>1 \<le> \<acute>free\<rbrace> 
             \<acute>c :== CALL NewCounter ();;
             \<acute>d :== \<acute>c;;
             dynCallClosure (\<lambda>s. s) upd c_' (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) 
                         (\<lambda>s t. Basic (\<lambda>u. u\<lparr>n_' := r_' t\<rparr>));;
             dynCallClosure (\<lambda>s. s) upd d_' (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) 
                         (\<lambda>s t. Basic (\<lambda>u. u\<lparr>m_' := r_' t\<rparr>));;
             \<acute>r :== \<acute>n + \<acute>m
           \<lbrace>\<acute>r=3\<rbrace>"

apply vcg_step
apply vcg_step
apply (rule dynCallClosure)
prefer 2
apply vcg_step
apply vcg_step
apply vcg_step
apply (rule dynCallClosure)
apply vcg_step
apply vcg_step
apply vcg_step
apply vcg_step
apply clarsimp
apply (subgoal_tac "\<Gamma>\<turnstile> \<lbrace>p\<rightarrow>\<acute>cnt = 0\<rbrace> callClosure upd (c_' t) \<lbrace>\<acute>r = Suc 0 \<and> p\<rightarrow>\<acute>cnt = Suc 0\<rbrace>")
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply assumption
apply clarsimp
apply (erule_tac x=1 in allE)
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply assumption
apply clarsimp
apply (erule allE)
apply assumption
done

end