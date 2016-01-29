(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      ProcParEx.thy
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

section "Examples for Procedures as Parameters"

theory ProcParEx imports "../Vcg" begin


lemma DynProcProcPar':
 assumes adapt: "P \<subseteq> {s. p s = q \<and>
         (\<exists>Z. init s \<in> P' Z \<and>
              (\<forall>t \<in> Q' Z. return s t \<in> R s t) \<and>
              (\<forall>t \<in> A' Z. return s t \<in> A))}"
 assumes result: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>(R s t) result s t Q,A" 
 assumes q: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>(P' Z) Call q (Q' Z),(A' Z)"
 shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>P dynCall init p return result Q,A"
apply (rule HoarePartial.DynProcProcPar [OF _ result q])
apply (insert adapt)
apply fast
done


lemma conseq_exploit_pre':
             "\<lbrakk>\<forall>s \<in> S. \<Gamma>,\<Theta> \<turnstile> ({s} \<inter> P) c Q,A\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile> (P \<inter> S)c Q,A"
  apply (rule HoarePartialDef.Conseq)
  apply clarify
  by (metis IntI insertI1 subset_refl)


lemma conseq_exploit_pre'':
             "\<lbrakk>\<forall>Z. \<forall>s \<in> S Z.  \<Gamma>,\<Theta> \<turnstile> ({s} \<inter> P Z) c (Q Z),(A Z)\<rbrakk>
              \<Longrightarrow>
              \<forall>Z. \<Gamma>,\<Theta>\<turnstile> (P Z \<inter> S Z)c (Q Z),(A Z)"
  apply (rule allI)
  apply (rule conseq_exploit_pre')
  apply blast
  done

lemma conseq_exploit_pre''':
             "\<lbrakk>\<forall>s \<in> S. \<forall>Z. \<Gamma>,\<Theta> \<turnstile> ({s} \<inter> P Z) c (Q Z),(A Z)\<rbrakk>
              \<Longrightarrow>
              \<forall>Z. \<Gamma>,\<Theta>\<turnstile> (P Z \<inter> S)c (Q Z),(A Z)"
  apply (rule allI)
  apply (rule conseq_exploit_pre')
  apply blast
  done


  
record 'g vars = "'g state" +
  compare_' :: string
  n_'   :: nat
  m_'   :: nat
  b_'   :: bool
  k_'  :: nat
 


procedures compare(n,m|b) = "NoBody"
print_locale! compare_signature


context compare_signature
begin
declare [[hoare_use_call_tr' = false]]
term "\<acute>b :== CALL compare(\<acute>n,\<acute>m)"
term "\<acute>b :== DYNCALL \<acute>compare(\<acute>n,\<acute>m)"
declare [[hoare_use_call_tr' = true]]
term "\<acute>b :== DYNCALL \<acute>compare(\<acute>n,\<acute>m)"
end


procedures
  LEQ (n,m | b) = "\<acute>b :== \<acute>n \<le> \<acute>m"
  LEQ_spec: "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>}  PROC LEQ(\<acute>n,\<acute>m,\<acute>b) \<lbrace>\<acute>b = (\<^bsup>\<sigma>\<^esup>n \<le> \<^bsup>\<sigma>\<^esup>m)\<rbrace>"
  LEQ_modifies: "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} PROC LEQ(\<acute>n,\<acute>m,\<acute>b) {t. t may_only_modify_globals \<sigma> in []}"



definition mx:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "mx leq a b = (if leq a b then a else b)"

procedures
  Max (compare, n, m | k) = 
  "\<acute>b :== DYNCALL \<acute>compare(\<acute>n,\<acute>m);;
   IF \<acute>b THEN \<acute>k :== \<acute>n ELSE \<acute>k :== \<acute>m FI"

  Max_spec: "\<And>leq. \<forall>\<sigma>. \<Gamma>\<turnstile> 
  ({\<sigma>} \<inter> {s. (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<^bsup>s\<^esup>compare(\<acute>n,\<acute>m) \<lbrace>\<acute>b = (leq \<^bsup>\<tau>\<^esup>n \<^bsup>\<tau>\<^esup>m)\<rbrace>) \<and> 
              (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<^bsup>s\<^esup>compare(\<acute>n,\<acute>m) {t. t may_only_modify_globals \<tau> in []})})
    PROC Max(\<acute>compare,\<acute>n,\<acute>m,\<acute>k)
  \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"


lemma (in Max_impl ) Max_spec1: 
shows
"\<forall>\<sigma> leq. \<Gamma>\<turnstile> 
  ({\<sigma>} \<inter> \<lbrace> (\<forall>\<tau>. \<Gamma>\<turnstile>{\<tau>} \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) \<lbrace>\<acute>b = (leq \<^bsup>\<tau>\<^esup>n \<^bsup>\<tau>\<^esup>m)\<rbrace>) \<and> 
      (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) {t. t may_only_modify_globals \<tau> in []})\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
proof -
  fix \<sigma>:: "('a,'b) vars_scheme" and s::"('a,'b) vars_scheme" and leq
   assume compare_spec: 
       "\<forall>\<tau>. \<Gamma>\<turnstile>{\<tau>} \<acute>b :== PROC \<^bsup>s\<^esup>compare(\<acute>n,\<acute>m) \<lbrace>\<acute>b = leq \<^bsup>\<tau>\<^esup>n \<^bsup>\<tau>\<^esup>m\<rbrace>"
 
  assume compare_modifies:
        "\<forall>\<tau>. \<Gamma>\<turnstile>{\<tau>} \<acute>b :== PROC \<^bsup>s\<^esup>compare(\<acute>n,\<acute>m) 
                {t. t may_only_modify_globals \<tau> in []}"

   show "\<Gamma>\<turnstile>({s} \<inter> {\<sigma>})
            \<acute>b :== DYNCALL \<acute>compare (\<acute>n,\<acute>m);;
            IF \<acute>b THEN \<acute>k :== \<acute>n ELSE \<acute>k :== \<acute>m FI
            \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
     apply vcg
     apply (clarsimp simp add: mx_def)
     done
 qed


lemma (in Max_impl) Max_spec2: 
shows
"\<forall>\<sigma> leq. \<Gamma>\<turnstile> 
  ({\<sigma>} \<inter> \<lbrace>(\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) \<lbrace>\<acute>b = (leq \<^bsup>\<tau>\<^esup>n \<^bsup>\<tau>\<^esup>m)\<rbrace>) \<and> 
      (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) {t. t may_only_modify_globals \<tau> in []})\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply (clarsimp simp add: mx_def)
done

lemma (in Max_impl) Max_spec3: 
shows
"\<forall>n m leq. \<Gamma>\<turnstile> 
  (\<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace>  \<inter> 
   \<lbrace>(\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) \<lbrace>\<acute>b = (leq \<^bsup>\<tau>\<^esup>n \<^bsup>\<tau>\<^esup>m)\<rbrace>) \<and> 
     (\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) {t. t may_only_modify_globals \<tau> in []})\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq n m\<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply (clarsimp simp add: mx_def)
done

lemma (in Max_impl) Max_spec4: 
shows
"\<forall>n m leq. \<Gamma>\<turnstile> 
  (\<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace> \<inter> \<lbrace>\<forall>\<tau>. \<Gamma>\<turnstile> {\<tau>} \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) \<lbrace>\<acute>b = (leq \<^bsup>\<tau>\<^esup>n \<^bsup>\<tau>\<^esup>m)\<rbrace>\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq n m\<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply (clarsimp simp add: mx_def)
done

locale Max_test = Max_spec + LEQ_spec + LEQ_modifies 
lemma (in Max_test) 

  shows
  "\<Gamma>\<turnstile> {\<sigma>} \<acute>k :== CALL Max(LEQ_'proc,\<acute>n,\<acute>m) \<lbrace>\<acute>k = mx (op \<le>) \<^bsup>\<sigma>\<^esup>n \<^bsup>\<sigma>\<^esup>m\<rbrace>"
proof -
  note Max_spec = Max_spec [where leq="(op \<le>)"]
  show ?thesis
    apply vcg
    apply (clarsimp)
    apply (rule conjI)
    apply (rule LEQ_spec [simplified])
    apply (rule LEQ_modifies [simplified])
    done
qed


lemma (in Max_impl) Max_spec5:
shows
"\<forall>n m leq. \<Gamma>\<turnstile> 
  (\<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace> \<inter> \<lbrace>\<forall>n' m'. \<Gamma>\<turnstile> \<lbrace>\<acute>n=n' \<and> \<acute>m=m'\<rbrace> \<acute>b :== PROC \<acute>compare(\<acute>n,\<acute>m) \<lbrace>\<acute>b = (leq n' m')\<rbrace>\<rbrace>)
    \<acute>k :== PROC Max(\<acute>compare,\<acute>n,\<acute>m)
  \<lbrace>\<acute>k = mx leq n m\<rbrace>"
term "\<lbrace>{s. \<^bsup>s\<^esup>n = n' \<and> \<^bsup>s\<^esup>m = m'} = X\<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (intro allI)
apply (rule conseq_exploit_pre')
apply (rule)
apply clarify
apply vcg
apply clarsimp
apply (clarsimp simp add: mx_def)
done

lemma (in LEQ_impl)
 LEQ_spec: "\<forall>n m. \<Gamma>\<turnstile> \<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace>  PROC LEQ(\<acute>n,\<acute>m,\<acute>b) \<lbrace>\<acute>b = (n \<le> m)\<rbrace>"
  apply vcg
  done


locale Max_test' = Max_impl + LEQ_impl
lemma (in Max_test') 
  shows
  "\<forall>n m. \<Gamma>\<turnstile> \<lbrace>\<acute>n=n \<and> \<acute>m=m\<rbrace> \<acute>k :== CALL Max(LEQ_'proc,\<acute>n,\<acute>m) \<lbrace>\<acute>k = mx (op \<le>) n m\<rbrace>"
proof -
  note Max_spec = Max_spec5
  show ?thesis
    apply vcg
    apply (rule_tac x="op \<le>" in exI)
    apply clarsimp
    apply (rule LEQ_spec [rule_format])
    done
qed

end
