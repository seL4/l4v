(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      HoareTotal.thy
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

section {* Derived Hoare Rules for Total Correctness *}

theory HoareTotal imports HoareTotalProps begin 

lemma conseq_no_aux:
  "\<lbrakk>\<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q',A';
    \<forall>s. s \<in> P \<longrightarrow> (s\<in>P' \<and> (Q' \<subseteq> Q)\<and> (A' \<subseteq> A))\<rbrakk>
  \<Longrightarrow>
  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (rule conseq [where P'="\<lambda>Z. P'" and Q'="\<lambda>Z. Q'" and A'="\<lambda>Z. A'"]) auto

text {* If for example a specification for a "procedure pointer" parameter 
is in the precondition we can extract it with this rule *}
lemma conseq_exploit_pre:
             "\<lbrakk>\<forall>s \<in> P. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s} \<inter> P) c Q,A\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  apply (rule Conseq)
  apply clarify
  apply (rule_tac x="{s} \<inter> P" in exI)  
  apply (rule_tac x="Q" in exI)  
  apply (rule_tac x="A" in exI)  
  by simp


lemma conseq:"\<lbrakk>\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z);
              \<forall>s. s \<in> P \<longrightarrow> (\<exists> Z. s\<in>P' Z \<and> (Q' Z \<subseteq> Q)\<and> (A' Z \<subseteq> A))\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (rule Conseq') blast


lemma Lem:"\<lbrakk>\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z);
            P \<subseteq> {s. \<exists> Z. s\<in>P' Z \<and> (Q' Z \<subseteq> Q) \<and> (A' Z \<subseteq> A)}\<rbrakk>
              \<Longrightarrow>
              \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (lem x c) Q,A"
  apply (unfold lem_def) 
  apply (erule conseq)
  apply blast
  done


lemma LemAnno:
assumes conseq:  "P \<subseteq> {s. \<exists>Z. s\<in>P' Z \<and> 
                     (\<forall>t. t \<in> Q' Z \<longrightarrow> t \<in> Q) \<and> (\<forall>t. t \<in> A' Z \<longrightarrow> t \<in> A)}"
assumes lem: "\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (lem x c) Q,A"
  apply (rule Lem [OF lem])
  using conseq
  by blast

lemma LemAnnoNoAbrupt:
assumes conseq:  "P \<subseteq>  {s. \<exists>Z. s\<in>P' Z \<and> (\<forall>t. t \<in> Q' Z \<longrightarrow> t \<in> Q)}"
assumes lem: "\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),{}"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (lem x c) Q,{}"
  apply (rule Lem [OF lem])
  using conseq
  by blast

lemma TrivPost: "\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),(A' Z)
                 \<Longrightarrow>
                 \<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c UNIV,UNIV"
apply (rule allI)
apply (erule conseq)
apply auto
done

lemma TrivPostNoAbr: "\<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c (Q' Z),{}
                 \<Longrightarrow>
                 \<forall>Z. \<Gamma>,\<Theta> \<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) c UNIV,{}"
apply (rule allI)
apply (erule conseq)
apply auto
done

lemma DynComConseq:
  assumes "P \<subseteq> {s. \<exists>P' Q' A'.  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P' (c s) Q',A' \<and> P \<subseteq> P' \<and> Q' \<subseteq> Q \<and> A' \<subseteq> A}" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P DynCom c Q,A"
  using assms
  apply -
  apply (rule hoaret.DynCom)
  apply clarsimp
  apply (rule hoaret.Conseq)
  apply clarsimp
  apply blast
  done

lemma SpecAnno: 
 assumes consequence: "P \<subseteq> {s. (\<exists> Z. s\<in>P' Z \<and> (Q' Z \<subseteq> Q) \<and> (A' Z \<subseteq> A))}"
 assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) (c Z) (Q' Z),(A' Z)"
 assumes bdy_constant:  "\<forall>Z. c Z = c undefined"
 shows   "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (specAnno P' c Q' A') Q,A"
proof -
  from spec bdy_constant
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) (c undefined) (Q' Z),(A' Z)"
    apply - 
    apply (rule allI)
    apply (erule_tac x=Z in allE)
    apply (erule_tac x=Z in allE)
    apply simp
    done
  with consequence show ?thesis
    apply (simp add: specAnno_def)
    apply (erule conseq)
    apply blast
    done
qed



lemma SpecAnno': 
 "\<lbrakk>P \<subseteq> {s.  \<exists> Z. s\<in>P' Z \<and> 
            (\<forall>t. t \<in> Q' Z \<longrightarrow>  t \<in> Q) \<and> (\<forall>t. t \<in> A' Z \<longrightarrow> t \<in>  A)};
   \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) (c Z) (Q' Z),(A' Z);
   \<forall>Z. c Z = c undefined
  \<rbrakk> \<Longrightarrow>
    \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (specAnno P' c Q' A') Q,A"
apply (simp only: subset_iff [THEN sym])
apply (erule (1) SpecAnno)
apply assumption
done

lemma SpecAnnoNoAbrupt: 
 "\<lbrakk>P \<subseteq> {s.  \<exists> Z. s\<in>P' Z \<and> 
            (\<forall>t. t \<in> Q' Z \<longrightarrow>  t \<in> Q)};
   \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) (c Z) (Q' Z),{};
   \<forall>Z. c Z = c undefined
  \<rbrakk> \<Longrightarrow>
    \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (specAnno P' c Q' (\<lambda>s. {})) Q,A"
apply (rule SpecAnno')
apply auto
done

lemma Skip: "P \<subseteq> Q \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Skip Q,A"
  by (rule hoaret.Skip [THEN conseqPre],simp)

lemma Basic: "P \<subseteq> {s. (f s) \<in> Q} \<Longrightarrow>  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Basic f) Q,A"
  by (rule hoaret.Basic [THEN conseqPre])

lemma BasicCond: 
  "\<lbrakk>P \<subseteq> {s. (b s \<longrightarrow> f s\<in>Q) \<and> (\<not> b s \<longrightarrow> g s\<in>Q)}\<rbrakk> \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Basic (\<lambda>s. if b s then f s else g s) Q,A"
  apply (rule Basic)
  apply auto
  done

lemma Spec: "P \<subseteq> {s. (\<forall>t. (s,t) \<in> r \<longrightarrow> t \<in> Q) \<and> (\<exists>t. (s,t) \<in> r)} 
            \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Spec r) Q,A"
by (rule hoaret.Spec [THEN conseqPre])

lemma SpecIf: 
  "\<lbrakk>P \<subseteq> {s. (b s \<longrightarrow> f s \<in> Q) \<and> (\<not> b s \<longrightarrow> g s \<in> Q \<and> h s \<in> Q)}\<rbrakk> \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Spec (if_rel b f g h) Q,A"
  apply (rule Spec)
  apply (auto simp add: if_rel_def)
  done

lemma Seq [trans, intro?]: 
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 R,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Seq c\<^sub>1 c\<^sub>2 Q,A"
  by (rule hoaret.Seq)

lemma SeqSwap: 
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c2 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c1 R,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Seq c1 c2 Q,A"
  by (rule Seq)

lemma BSeq:
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 R,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (bseq c\<^sub>1 c\<^sub>2) Q,A"
  by (unfold bseq_def) (rule Seq)

lemma Cond: 
  assumes wp: "P \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>P\<^sub>1) \<and> (s\<notin>b \<longrightarrow> s\<in>P\<^sub>2)}" 
  assumes deriv_c1: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q,A" 
  assumes deriv_c2: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c\<^sub>1 c\<^sub>2) Q,A"
proof (rule hoaret.Cond [THEN conseqPre])
  from deriv_c1 
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. (s \<in> b \<longrightarrow> s \<in> P\<^sub>1) \<and> (s \<notin> b \<longrightarrow> s \<in> P\<^sub>2)} \<inter> b) c\<^sub>1 Q,A"
    by (rule conseqPre) blast
next
  from deriv_c2 
  show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. (s \<in> b \<longrightarrow> s \<in> P\<^sub>1) \<and> (s \<notin> b \<longrightarrow> s \<in> P\<^sub>2)} \<inter> - b) c\<^sub>2 Q,A"
    by (rule conseqPre) blast
qed (insert wp)


lemma CondSwap: 
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P1 c1 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P2 c2 Q,A; 
    P \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>P1) \<and> (s\<notin>b \<longrightarrow> s\<in>P2)}\<rbrakk>
   \<Longrightarrow> 
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c1 c2) Q,A"
  by (rule Cond)

lemma Cond': 
  "\<lbrakk>P \<subseteq> {s. (b \<subseteq> P1) \<and> (- b \<subseteq> P2)};\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P1 c1 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P2 c2 Q,A\<rbrakk>
   \<Longrightarrow> 
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c1 c2) Q,A"
  by (rule CondSwap) blast+

lemma CondInv: 
  assumes wp: "P \<subseteq> Q" 
  assumes inv: "Q \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>P\<^sub>1) \<and> (s\<notin>b \<longrightarrow> s\<in>P\<^sub>2)}" 
  assumes deriv_c1: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 Q,A" 
  assumes deriv_c2: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c\<^sub>1 c\<^sub>2) Q,A"
proof -
  from wp inv
  have "P \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>P\<^sub>1) \<and> (s\<notin>b \<longrightarrow> s\<in>P\<^sub>2)}"
    by blast
  from Cond [OF this deriv_c1 deriv_c2]
  show ?thesis .
qed

lemma CondInv': 
  assumes wp: "P \<subseteq> I" 
  assumes inv: "I \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>P\<^sub>1) \<and> (s\<notin>b \<longrightarrow> s\<in>P\<^sub>2)}" 
  assumes wp': "I \<subseteq> Q"
  assumes deriv_c1: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P\<^sub>1 c\<^sub>1 I,A" 
  assumes deriv_c2: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P\<^sub>2 c\<^sub>2 I,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c\<^sub>1 c\<^sub>2) Q,A"
proof -
  from CondInv [OF wp inv deriv_c1 deriv_c2]
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c\<^sub>1 c\<^sub>2) I,A" .
  from conseqPost [OF this wp' subset_refl]
  show ?thesis .
qed


lemma switchNil:
  "P \<subseteq> Q \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P (switch v []) Q,A"
  by (simp add: Skip)
 
lemma switchCons:
  "\<lbrakk>P \<subseteq> {s. (v s \<in> V \<longrightarrow> s \<in> P\<^sub>1) \<and> (v s \<notin> V \<longrightarrow> s \<in> P\<^sub>2)}; 
        \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P\<^sub>1 c Q,A;
        \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P\<^sub>2 (switch v vs) Q,A\<rbrakk>
\<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P (switch v ((V,c)#vs)) Q,A"
  by (simp add: Cond)

 
lemma Guard:
 "\<lbrakk>P \<subseteq> g \<inter> R; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Guard f g c Q,A"
apply (rule HoareTotalDef.Guard [THEN conseqPre, of _ _ _ _ R])
apply (erule conseqPre)
apply auto
done

lemma GuardSwap:
 "\<lbrakk> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; P \<subseteq> g \<inter> R\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Guard f g c Q,A"
  by (rule Guard)

lemma Guarantee:
 "\<lbrakk>P \<subseteq> {s. s \<in> g \<longrightarrow> s \<in> R}; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; f \<in> F\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Guard f g c) Q,A"
apply (rule Guarantee [THEN conseqPre, of _ _ _ _ _ "{s. s \<in> g \<longrightarrow> s \<in> R}"])
apply   assumption
apply  (erule conseqPre)
apply auto
done

lemma GuaranteeSwap:
 "\<lbrakk> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; P \<subseteq> {s. s \<in> g \<longrightarrow> s \<in> R}; f \<in> F\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Guard f g c) Q,A"
  by (rule Guarantee)


lemma GuardStrip:
 "\<lbrakk>P \<subseteq> R; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; f \<in> F\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Guard f g c) Q,A"
apply (rule Guarantee [THEN conseqPre])
apply auto
done

lemma GuardStripSwap:
 "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; P \<subseteq> R; f \<in> F\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Guard f g c) Q,A"
  by (rule GuardStrip)

lemma GuaranteeStrip:
 "\<lbrakk>P \<subseteq> R; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; f \<in> F\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (guaranteeStrip f g c) Q,A"
  by (unfold guaranteeStrip_def) (rule GuardStrip)

lemma GuaranteeStripSwap:
 "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; P \<subseteq> R; f \<in> F\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (guaranteeStrip f g c) Q,A"
  by (unfold guaranteeStrip_def) (rule GuardStrip)

lemma GuaranteeAsGuard:
 "\<lbrakk>P \<subseteq> g \<inter> R; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P guaranteeStrip f g c Q,A"
  by (unfold guaranteeStrip_def) (rule Guard)

lemma GuaranteeAsGuardSwap:
 "\<lbrakk> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c Q,A; P \<subseteq> g \<inter> R\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P guaranteeStrip f g c Q,A"
  by (rule GuaranteeAsGuard)

lemma GuardsNil:
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> 
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (guards [] c) Q,A"
  by simp

lemma GuardsCons:
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Guard f g (guards gs c) Q,A \<Longrightarrow> 
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (guards ((f,g)#gs) c) Q,A"
  by simp

lemma GuardsConsGuaranteeStrip:
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P guaranteeStrip f g (guards gs c) Q,A \<Longrightarrow> 
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (guards (guaranteeStripPair f g#gs) c) Q,A"
  by (simp add: guaranteeStripPair_def guaranteeStrip_def)

lemma While: 
  assumes P_I: "P \<subseteq> I" 
  assumes deriv_body: 
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I \<inter> b) c ({t. (t, \<sigma>) \<in> V} \<inter> I),A"
  assumes I_Q: "I \<inter> -b \<subseteq> Q" 
  assumes wf: "wf V"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnno  b I V c) Q,A"
proof -
  from wf deriv_body P_I I_Q
  show ?thesis
    apply (unfold whileAnno_def)
    apply (erule conseqPrePost [OF HoareTotalDef.While]) 
    apply auto
    done
qed



lemma WhileInvPost: 
  assumes P_I: "P \<subseteq> I" 
  assumes termi_body: 
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/UNIV\<^esub> ({\<sigma>} \<inter> I \<inter> b) c ({t. (t, \<sigma>) \<in> V} \<inter> P),A"
  assumes deriv_body: 
  "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (I \<inter> b) c I,A"
  assumes I_Q: "I \<inter> -b \<subseteq> Q" 
  assumes wf: "wf V"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnno  b I V c) Q,A"
proof -
  have "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I \<inter> b) c ({t. (t, \<sigma>) \<in> V} \<inter> I),A"
  proof 
    fix \<sigma>
    from hoare_sound [OF deriv_body] hoaret_sound [OF termi_body [rule_format, of \<sigma>]]
    have "\<Gamma>,\<Theta>\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I \<inter> b) c ({t. (t, \<sigma>) \<in> V} \<inter> I),A"
      by (fastforce simp add: cvalidt_def validt_def cvalid_def valid_def)
    then
    show "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I \<inter> b) c ({t. (t, \<sigma>) \<in> V} \<inter> I),A"
      by (rule hoaret_complete')
  qed

  from While [OF P_I this I_Q wf]
  show ?thesis .
qed

(* *)
lemma "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<inter> b) c Q,A \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P \<inter> b) (Seq c (Guard f Q Skip)) Q,A"
oops

text {* @{term "J"} will be instantiated by tactic with @{term "gs' \<inter> I"} for
  those guards that are not stripped.*} 
lemma WhileAnnoG:
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (guards gs 
                    (whileAnno  b J V (Seq c (guards gs Skip)))) Q,A 
        \<Longrightarrow> 
        \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnnoG gs b I V c) Q,A"
  by (simp add: whileAnnoG_def whileAnno_def while_def)

text {* This form stems from @{term "strip_guards F (whileAnnoG gs b I V c)"} *} 
lemma WhileNoGuard': 
  assumes P_I: "P \<subseteq> I" 
  assumes deriv_body: "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I \<inter> b) c ({t. (t, \<sigma>) \<in> V} \<inter> I),A"
  assumes I_Q: "I \<inter> -b \<subseteq> Q" 
  assumes wf: "wf V"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnno b I V (Seq c Skip)) Q,A"
  apply (rule While [OF P_I _ I_Q wf])
  apply (rule allI)
  apply (rule Seq)
  apply  (rule deriv_body [rule_format])
  apply (rule hoaret.Skip)
  done

lemma WhileAnnoFix:
assumes consequence: "P \<subseteq> {s. (\<exists> Z. s\<in>I Z \<and> (I Z \<inter> -b \<subseteq> Q)) }"
assumes bdy: "\<forall>Z \<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I Z \<inter> b) (c Z) ({t. (t, \<sigma>) \<in> V Z} \<inter> I Z),A"
assumes bdy_constant:  "\<forall>Z. c Z = c undefined"
assumes wf: "\<forall>Z. wf (V Z)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnnoFix b I V c) Q,A"
proof -
  from bdy bdy_constant
  have bdy': "\<And>Z. \<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I Z \<inter> b) (c undefined) 
               ({t. (t, \<sigma>) \<in> V Z} \<inter> I Z),A"
    apply - 
    apply (erule_tac x=Z in allE)
    apply (erule_tac x=Z in allE)
    apply simp
    done
  have "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (I Z) (whileAnnoFix b I V c) (I Z \<inter> -b),A"
    apply rule
    apply (unfold whileAnnoFix_def)
    apply (rule hoaret.While)
    apply (rule wf [rule_format])
    apply (rule bdy')
    done
  then
  show ?thesis
    apply (rule conseq)
    using consequence
    by blast
qed

lemma WhileAnnoFix':
assumes consequence: "P \<subseteq> {s. (\<exists> Z. s\<in>I Z \<and> 
                               (\<forall>t. t \<in> I Z \<inter> -b \<longrightarrow> t \<in> Q)) }"
assumes bdy: "\<forall>Z \<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> I Z \<inter> b) (c Z) ({t. (t, \<sigma>) \<in> V Z} \<inter> I Z),A"
assumes bdy_constant:  "\<forall>Z. c Z = c undefined"
assumes wf: "\<forall>Z. wf (V Z)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnnoFix b I V c) Q,A"
  apply (rule WhileAnnoFix [OF _ bdy bdy_constant wf])
  using consequence by blast

lemma WhileAnnoGFix:
assumes whileAnnoFix:
  "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (guards gs 
                (whileAnnoFix  b J V (\<lambda>Z. (Seq (c Z) (guards gs Skip))))) Q,A"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnnoGFix gs b I V c) Q,A"
  using whileAnnoFix
  by (simp add: whileAnnoGFix_def whileAnnoFix_def while_def)

lemma Bind:
  assumes adapt: "P \<subseteq> {s. s \<in> P' s}" 
  assumes c: "\<forall>s. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' s) (c (e s)) Q,A"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (bind e c) Q,A" 
apply (rule conseq [where P'="\<lambda>Z. {s. s=Z \<and> s \<in> P' Z}" and Q'="\<lambda>Z. Q" and 
A'="\<lambda>Z. A"])
apply  (rule allI)
apply  (unfold bind_def)
apply  (rule HoareTotalDef.DynCom)
apply  (rule ballI)
apply  clarsimp
apply  (rule conseqPre)
apply   (rule c [rule_format])
apply  blast
using adapt
apply blast
done

lemma Block:
assumes adapt: "P \<subseteq> {s. init s \<in> P' s}"
assumes bdy: "\<forall>s. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' s) bdy {t. return s t \<in> R s t},{t. return s t \<in> A}"
assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (block init bdy return c) Q,A" 
apply (rule conseq [where P'="\<lambda>Z. {s. s=Z \<and> init s \<in> P' Z}" and Q'="\<lambda>Z. Q" and 
A'="\<lambda>Z. A"])
prefer 2
using adapt
apply  blast
apply (rule allI)
apply (unfold block_def)
apply (rule HoareTotalDef.DynCom)
apply (rule ballI)
apply clarsimp
apply (rule_tac R="{t. return Z t \<in> R Z t}" in SeqSwap )
apply  (rule_tac  P'="\<lambda>Z'. {t. t=Z' \<and> return Z t \<in> R Z t}" and 
          Q'="\<lambda>Z'. Q" and A'="\<lambda>Z'. A" in conseq)
prefer 2 apply simp
apply  (rule allI)
apply  (rule HoareTotalDef.DynCom)
apply  (clarsimp)
apply  (rule SeqSwap)
apply   (rule c [rule_format])
apply  (rule Basic)
apply  clarsimp
apply (rule_tac R="{t. return Z t \<in> A}" in HoareTotalDef.Catch)
apply  (rule_tac R="{i. i \<in> P' Z}" in Seq)
apply   (rule Basic)
apply   clarsimp
apply  simp
apply  (rule bdy [rule_format])
apply (rule SeqSwap)
apply  (rule Throw)
apply (rule Basic)
apply simp
done

lemma BlockSwap:
assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
assumes bdy: "\<forall>s. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' s) bdy {t. return s t \<in> R s t},{t. return s t \<in> A}"
assumes adapt: "P \<subseteq> {s. init s \<in> P' s}"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (block init bdy return c) Q,A"
  using adapt bdy c
  by (rule Block)

lemma BlockSpec:
  assumes adapt: "P \<subseteq> {s. \<exists>Z. init s \<in> P' Z \<and> 
                             (\<forall>t. t \<in> Q' Z \<longrightarrow> return s t \<in> R s t) \<and>
                             (\<forall>t. t \<in> A' Z \<longrightarrow> return s t \<in> A)}"
  assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
  assumes bdy: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) bdy (Q' Z),(A' Z)" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (block init bdy return c) Q,A" 
apply (rule conseq [where P'="\<lambda>Z. {s. init s \<in> P' Z \<and> 
                             (\<forall>t. t \<in> Q' Z \<longrightarrow> return s t \<in> R s t) \<and>
                             (\<forall>t. t \<in> A' Z \<longrightarrow> return s t \<in> A)}" and Q'="\<lambda>Z. Q" and 
A'="\<lambda>Z. A"])
prefer 2
using adapt
apply  blast
apply (rule allI)
apply (unfold block_def)
apply (rule HoareTotalDef.DynCom)
apply (rule ballI)
apply clarsimp
apply (rule_tac R="{t. return s t \<in> R s t}" in SeqSwap )
apply  (rule_tac  P'="\<lambda>Z'. {t. t=Z' \<and> return s t \<in> R s t}" and 
          Q'="\<lambda>Z'. Q" and A'="\<lambda>Z'. A" in conseq)
prefer 2 apply simp
apply  (rule allI)
apply  (rule HoareTotalDef.DynCom)
apply  (clarsimp)
apply  (rule SeqSwap)
apply   (rule c [rule_format])
apply  (rule Basic)
apply  clarsimp
apply (rule_tac R="{t. return s t \<in> A}" in HoareTotalDef.Catch)
apply  (rule_tac R="{i. i \<in> P' Z}" in Seq)
apply   (rule Basic)
apply   clarsimp
apply  simp
apply  (rule conseq [OF bdy])
apply  clarsimp
apply  blast
apply (rule SeqSwap)
apply  (rule Throw)
apply (rule Basic)
apply simp
done


lemma Throw: "P \<subseteq> A \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Throw Q,A"
  by (rule hoaret.Throw [THEN conseqPre])

lemmas Catch = hoaret.Catch
lemma CatchSwap: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 Q,R\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Catch c\<^sub>1 c\<^sub>2 Q,A"
  by (rule hoaret.Catch)

lemma raise: "P \<subseteq> {s. f s \<in> A} \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P raise f Q,A"
  apply (simp add: raise_def)
  apply (rule Seq)
  apply  (rule Basic)
  apply  (assumption)
  apply (rule Throw)
  apply (rule subset_refl)
  done

lemma condCatch: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 Q,((b \<inter> R) \<union> (-b \<inter> A));\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A\<rbrakk> 
                  \<Longrightarrow>  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P condCatch c\<^sub>1 b c\<^sub>2 Q,A"
  apply (simp add: condCatch_def)
  apply (rule Catch)
  apply  assumption
  apply (rule CondSwap)
  apply   (assumption)
  apply  (rule hoaret.Throw)
  apply blast
  done

lemma condCatchSwap: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> R c\<^sub>2 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c\<^sub>1 Q,((b \<inter> R) \<union> (-b \<inter> A))\<rbrakk> 
                     \<Longrightarrow>  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P condCatch c\<^sub>1 b c\<^sub>2 Q,A"
  by (rule condCatch)


lemma ProcSpec:
  assumes adapt: "P \<subseteq> {s. \<exists>Z. init s \<in> P' Z \<and> 
                             (\<forall>t. t \<in> Q' Z \<longrightarrow> return s t \<in> R s t) \<and>
                             (\<forall>t. t \<in> A' Z \<longrightarrow> return s t \<in> A)}"
  assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
  assumes p: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) Call p (Q' Z),(A' Z)" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
using adapt c p
apply (unfold call_def) 
by (rule BlockSpec)

lemma ProcSpec':
  assumes adapt: "P \<subseteq> {s. \<exists>Z. init s \<in> P' Z \<and> 
                             (\<forall>t \<in> Q' Z. return s t \<in> R s t) \<and>
                             (\<forall>t \<in> A' Z. return s t \<in> A)}"
  assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
  assumes p: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) Call p (Q' Z),(A' Z)" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
apply (rule ProcSpec [OF _ c p])
apply (insert adapt)
apply clarsimp
apply (drule (1) subsetD)
apply (clarsimp)
apply (rule_tac x=Z in exI)
apply blast
done


lemma ProcSpecNoAbrupt:
  assumes adapt: "P \<subseteq> {s. \<exists>Z. init s \<in> P' Z \<and> 
                             (\<forall>t. t \<in> Q' Z \<longrightarrow> return s t \<in> R s t)}"
  assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
  assumes p: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) Call p (Q' Z),{}" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
apply (rule ProcSpec [OF _ c p])
using adapt
apply simp
done

lemma FCall:  
"\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return (\<lambda>s t. c (result t))) Q,A
\<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (fcall init p return result c) Q,A"
  by (simp add: fcall_def)

lemma ProcRec:
  assumes deriv_bodies:  
   "\<forall>p\<in>Procs. 
    \<forall>\<sigma> Z. \<Gamma>,\<Theta>\<union>(\<Union>q\<in>Procs. \<Union>Z. 
       {(P q Z \<inter> {s. ((s,q), \<sigma>,p) \<in> r},q,Q q Z,A q Z)})
        \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)"
  assumes wf: "wf r"
  assumes Procs_defined: "Procs \<subseteq> dom \<Gamma>"
  shows "\<forall>p\<in>Procs. \<forall>Z.  
  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>(P p Z) Call p (Q p Z),(A p Z)"
  by (intro strip)
     (rule HoareTotalDef.CallRec' 
     [OF _  Procs_defined wf deriv_bodies],
     simp_all)

lemma ProcRec':
  assumes ctxt: 
   "\<Theta>'=(\<lambda>\<sigma> p. \<Theta>\<union>(\<Union>q\<in>Procs. 
                   \<Union>Z. {(P q Z \<inter> {s. ((s,q), \<sigma>,p) \<in> r},q,Q q Z,A q Z)}))"
  assumes deriv_bodies:   
   "\<forall>p\<in>Procs. 
    \<forall>\<sigma> Z. \<Gamma>,\<Theta>' \<sigma> p\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)"
  assumes wf: "wf r"
  assumes Procs_defined: "Procs \<subseteq> dom \<Gamma>"
  shows "\<forall>p\<in>Procs. \<forall>Z.  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>(P p Z) Call p (Q p Z),(A p Z)"
  using ctxt deriv_bodies
  apply simp
  apply (erule ProcRec [OF _ wf Procs_defined])
  done
 

lemma ProcRecList:
  assumes deriv_bodies:  
   "\<forall>p\<in>set Procs. 
    \<forall>\<sigma> Z. \<Gamma>,\<Theta>\<union>(\<Union>q\<in>set Procs. \<Union>Z. 
       {(P q Z \<inter> {s. ((s,q), \<sigma>,p) \<in> r},q,Q q Z,A q Z)})
        \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P p Z) (the (\<Gamma> p)) (Q p Z),(A p Z)"
  assumes wf: "wf r"
  assumes dist: "distinct Procs"
  assumes Procs_defined: "set Procs \<subseteq> dom \<Gamma>"
  shows "\<forall>p\<in>set Procs. \<forall>Z.  
  \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>(P p Z) Call p (Q p Z),(A p Z)"
  using deriv_bodies wf Procs_defined
  by (rule ProcRec)

lemma  ProcRecSpecs:
  "\<lbrakk>\<forall>\<sigma>. \<forall>(P,p,Q,A) \<in> Specs. 
     \<Gamma>,\<Theta>\<union> ((\<lambda>(P,q,Q,A). (P \<inter> {s. ((s,q),(\<sigma>,p)) \<in> r},q,Q,A)) ` Specs)
      \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P) (the (\<Gamma> p)) Q,A;
    wf r;
    \<forall>(P,p,Q,A) \<in> Specs. p \<in> dom \<Gamma>\<rbrakk>
  \<Longrightarrow> \<forall>(P,p,Q,A) \<in> Specs. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Call p) Q,A"
apply (rule ballI)
apply (case_tac x)
apply (rename_tac x P p Q A)
apply simp
apply (rule hoaret.CallRec)
apply auto
done

lemma ProcRec1:
  assumes deriv_body:  
   "\<forall>\<sigma> Z. \<Gamma>,\<Theta>\<union>(\<Union>Z. {(P Z \<inter> {s. ((s,p), \<sigma>,p) \<in> r},p,Q Z,A Z)})
           \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P Z) (the (\<Gamma> p)) (Q Z),(A Z)"
  assumes wf: "wf r"
  assumes p_defined: "p \<in> dom \<Gamma>"
  shows "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) Call p (Q Z),(A Z)"
proof -
  from deriv_body wf p_defined
  have "\<forall>p\<in>{p}. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) Call p (Q Z),(A Z)"
    apply - 
    apply (rule ProcRec [where  A="\<lambda>p. A" and P="\<lambda>p. P" and Q="\<lambda>p. Q"])
    apply simp_all
    done
  thus ?thesis
    by simp
qed

lemma ProcNoRec1:
  assumes deriv_body:  
   "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) (the (\<Gamma> p)) (Q Z),(A Z)"
  assumes p_defined: "p \<in> dom \<Gamma>"
  shows "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) Call p (Q Z),(A Z)"
proof -
  have "\<forall>\<sigma> Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P Z) (the (\<Gamma> p)) (Q Z),(A Z)"
    by (blast intro: conseqPre deriv_body [rule_format])
  with p_defined have "\<forall>\<sigma> Z. \<Gamma>,\<Theta>\<union>(\<Union>Z. {(P Z \<inter> {s. ((s,p), \<sigma>,p) \<in> {}},
                         p,Q Z,A Z)})
             \<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({\<sigma>} \<inter> P Z) (the (\<Gamma> p)) (Q Z),(A Z)"
    by (blast intro: hoaret_augment_context)
  from this  
  show ?thesis 
    by (rule ProcRec1) (auto simp add: p_defined) 
qed

lemma ProcBody:
 assumes WP: "P \<subseteq> P'"
 assumes deriv_body: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' body Q,A" 
 assumes body: "\<Gamma> p = Some body"
 shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Call p Q,A"
apply (rule conseqPre [OF _ WP])
apply (rule ProcNoRec1 [rule_format, where P="\<lambda>Z. P'" and Q="\<lambda>Z. Q" and A="\<lambda>Z. A"]) 
apply  (insert body)
apply  simp
apply  (rule hoaret_augment_context [OF deriv_body])
apply  blast
apply fastforce
done

lemma CallBody:
assumes adapt: "P \<subseteq> {s. init s \<in> P' s}"
assumes bdy: "\<forall>s. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' s) body {t. return s t \<in> R s t},{t. return s t \<in> A}"
assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
assumes body: "\<Gamma> p = Some body"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
apply (unfold call_def)
apply (rule Block [OF adapt _ c])
apply (rule allI)
apply (rule ProcBody [where \<Gamma>=\<Gamma>, OF _ bdy [rule_format] body])
apply simp
done

lemmas ProcModifyReturn = HoareTotalProps.ProcModifyReturn
lemmas ProcModifyReturnSameFaults = HoareTotalProps.ProcModifyReturnSameFaults

lemma ProcModifyReturnNoAbr:
  assumes spec: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return' c) Q,A"
  assumes result_conform:
      "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes modifies_spec:  
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call p (Modif \<sigma>),{}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
by (rule ProcModifyReturn [OF spec result_conform _ modifies_spec]) simp


lemma ProcModifyReturnNoAbrSameFaults:
  assumes spec: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return' c) Q,A"
  assumes result_conform:
      "\<forall>s t. t \<in> Modif (init s) \<longrightarrow> (return' s t) = (return s t)"
  assumes modifies_spec:  
  "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Call p (Modif \<sigma>),{}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (call init p return c) Q,A"
by (rule ProcModifyReturnSameFaults [OF spec result_conform _ modifies_spec]) simp


lemma DynProc: 
  assumes adapt: "P \<subseteq> {s. \<exists>Z. init s \<in> P' s Z \<and>
                          (\<forall>t. t \<in> Q' s Z \<longrightarrow>  return s t \<in> R s t) \<and>
                          (\<forall>t. t \<in> A' s Z \<longrightarrow> return s t \<in> A)}"
  assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
  assumes p: "\<forall>s\<in> P. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' s Z) Call (p s) (Q' s Z),(A' s Z)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P dynCall init p return c Q,A"
apply (rule conseq [where P'="\<lambda>Z. {s. s=Z \<and> s \<in> P}"
  and Q'="\<lambda>Z. Q" and A'="\<lambda>Z. A"])
prefer 2
using adapt
apply  blast
apply (rule allI)
apply (unfold dynCall_def call_def block_def)
apply (rule HoareTotalDef.DynCom)
apply clarsimp
apply (rule HoareTotalDef.DynCom)
apply clarsimp
apply (frule in_mono [rule_format, OF adapt])
apply clarsimp
apply (rename_tac Z')
apply (rule_tac R="Q' Z Z'" in Seq)
apply  (rule CatchSwap)
apply   (rule SeqSwap)
apply    (rule Throw) 
apply    (rule subset_refl)
apply   (rule Basic)
apply   (rule subset_refl)
apply  (rule_tac R="{i. i \<in> P' Z Z'}" in Seq)
apply   (rule Basic) 
apply   clarsimp
apply  simp
apply  (rule_tac Q'="Q' Z Z'" and A'="A' Z Z'" in conseqPost)
using p
apply    clarsimp
apply   simp
apply  clarsimp
apply  (rule_tac  P'="\<lambda>Z''. {t. t=Z'' \<and> return Z t \<in> R Z t}" and 
          Q'="\<lambda>Z''. Q" and A'="\<lambda>Z''. A" in conseq)
prefer 2 apply simp
apply (rule allI)
apply (rule HoareTotalDef.DynCom)
apply clarsimp
apply (rule SeqSwap)
apply  (rule c [rule_format])
apply (rule Basic)
apply clarsimp
done

lemma DynProc': 
  assumes adapt: "P \<subseteq> {s. \<exists>Z. init s \<in> P' s Z \<and>
                          (\<forall>t \<in> Q' s Z. return s t \<in> R s t) \<and>
                          (\<forall>t \<in> A' s Z. return s t \<in> A)}"
  assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
  assumes p: "\<forall>s\<in> P. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' s Z) Call (p s) (Q' s Z),(A' s Z)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P dynCall init p return c Q,A"
proof -
  from adapt have "P \<subseteq> {s. \<exists>Z. init s \<in> P' s Z \<and>
                          (\<forall>t. t \<in> Q' s Z \<longrightarrow>  return s t \<in> R s t) \<and>
                          (\<forall>t. t \<in> A' s Z \<longrightarrow> return s t \<in> A)}"
    by blast
  from this c p show ?thesis
    by (rule DynProc)
qed

lemma DynProcStaticSpec: 
assumes adapt: "P \<subseteq> {s. s \<in> S \<and> (\<exists>Z. init s \<in> P' Z  \<and> 
                            (\<forall>\<tau>. \<tau> \<in> Q' Z \<longrightarrow> return s \<tau> \<in> R s \<tau>) \<and>
                            (\<forall>\<tau>. \<tau> \<in> A' Z \<longrightarrow> return s \<tau> \<in> A))}"
assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
assumes spec: "\<forall>s\<in>S. \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) Call (p s) (Q' Z),(A' Z)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -
  from adapt have P_S: "P \<subseteq> S"
    by blast
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P \<inter> S) (dynCall init p return c) Q,A"
    apply (rule DynProc [where P'="\<lambda>s Z. P' Z" and Q'="\<lambda>s Z. Q' Z" 
                         and A'="\<lambda>s Z. A' Z", OF _ c])
    apply  clarsimp
    apply  (frule in_mono [rule_format, OF adapt])
    apply  clarsimp
    using spec
    apply clarsimp
    done
  thus ?thesis
    by (rule conseqPre) (insert P_S,blast)
qed



lemma DynProcProcPar: 
assumes adapt: "P \<subseteq> {s. p s = q \<and> (\<exists>Z. init s \<in> P' Z  \<and> 
                            (\<forall>\<tau>. \<tau> \<in> Q' Z \<longrightarrow> return s \<tau> \<in> R s \<tau>) \<and>
                            (\<forall>\<tau>. \<tau> \<in> A' Z \<longrightarrow> return s \<tau> \<in> A))}"
assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) Call q (Q' Z),(A' Z)"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
  apply (rule DynProcStaticSpec [where S="{s. p s = q}",simplified, OF adapt c])
  using spec
  apply simp
  done


lemma DynProcProcParNoAbrupt: 
assumes adapt: "P \<subseteq> {s. p s = q \<and> (\<exists>Z. init s \<in> P' Z  \<and> 
                            (\<forall>\<tau>. \<tau> \<in> Q' Z \<longrightarrow> return s \<tau> \<in> R s \<tau>))}"
assumes c: "\<forall>s t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (R s t) (c s t) Q,A"
assumes spec: "\<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P' Z) Call q (Q' Z),{}"
shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -  
  have "P \<subseteq> {s. p s = q \<and> (\<exists> Z. init s \<in> P' Z \<and> 
                      (\<forall>t. t \<in> Q' Z \<longrightarrow> return s t \<in> R s t) \<and>
                      (\<forall>t. t \<in> {} \<longrightarrow> return s t \<in> A))}"
    (is "P \<subseteq> ?P'")
  proof 
    fix s
    assume P: "s\<in>P"
    with adapt obtain Z where
      Pre: "p s = q \<and> init s \<in> P' Z" and
      adapt_Norm: "\<forall>\<tau>. \<tau> \<in> Q' Z \<longrightarrow> return s \<tau> \<in> R s \<tau>" 
      by blast
    from  adapt_Norm 
    have "\<forall>t. t \<in> Q' Z \<longrightarrow> return s t \<in> R s t"
      by auto
    then
    show "s\<in>?P'"
      using Pre by blast
  qed
  note P = this
  show ?thesis
    apply -
    apply (rule DynProcStaticSpec [where S="{s. p s = q}",simplified, OF P c])
    apply (insert spec)
    apply auto
    done
qed

lemma DynProcModifyReturnNoAbr: 
  assumes to_prove: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return' c) Q,A"
  assumes ret_nrm_modif: "\<forall>s t. t \<in> (Modif (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes modif_clause: 
            "\<forall>s \<in> P. \<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call (p s)  (Modif \<sigma>),{}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -
  from ret_nrm_modif
  have "\<forall>s t. t  \<in> (Modif (init s)) 
        \<longrightarrow> return' s t = return s t"
    by iprover
  then 
  have ret_nrm_modif': "\<forall>s t. t \<in> (Modif (init s)) 
                      \<longrightarrow> return' s t = return s t"
    by simp
  have ret_abr_modif': "\<forall>s t. t \<in> {} 
                        \<longrightarrow> return' s t = return s t"
    by simp
  from to_prove ret_nrm_modif' ret_abr_modif' modif_clause show ?thesis
    by (rule dynProcModifyReturn)
qed

lemma ProcDynModifyReturnNoAbrSameFaults: 
  assumes to_prove: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return' c) Q,A"
  assumes ret_nrm_modif: "\<forall>s t. t \<in> (Modif (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes modif_clause: 
            "\<forall>s \<in> P. \<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} (Call (p s)) (Modif \<sigma>),{}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -
  from ret_nrm_modif
  have "\<forall>s t. t  \<in> (Modif (init s)) 
        \<longrightarrow> return' s t = return s t"
    by iprover
  then
  have ret_nrm_modif': "\<forall>s t. t \<in> (Modif (init s)) 
                      \<longrightarrow> return' s t = return s t"
    by simp
  have ret_abr_modif': "\<forall>s t. t \<in> {} 
                        \<longrightarrow> return' s t = return s t"
    by simp
  from to_prove ret_nrm_modif' ret_abr_modif' modif_clause show ?thesis
    by (rule dynProcModifyReturnSameFaults)
qed

lemma ProcProcParModifyReturn: 
  assumes q: "P \<subseteq> {s. p s = q} \<inter> P'"
   --{* @{thm[source] DynProcProcPar} introduces the same constraint as first conjunction in 
         @{term P'}, so the vcg can simplify it. *}
  assumes to_prove: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' (dynCall init p return' c) Q,A"
  assumes ret_nrm_modif: "\<forall>s t. t \<in> (Modif (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes ret_abr_modif: "\<forall>s t. t \<in> (ModifAbr (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes modif_clause: 
          "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} (Call q) (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -
  from to_prove have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return' c) Q,A"
    by (rule conseqPre) blast
  from this ret_nrm_modif 
       ret_abr_modif 
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return c) Q,A"
    by (rule dynProcModifyReturn) (insert modif_clause,auto)
  from this q show ?thesis
    by (rule conseqPre) 
qed



lemma ProcProcParModifyReturnSameFaults: 
  assumes q: "P \<subseteq> {s. p s = q} \<inter> P'"
   --{* @{thm[source] DynProcProcPar} introduces the same constraint as first conjunction in 
         @{term P'}, so the vcg can simplify it. *}
  assumes to_prove: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' (dynCall init p return' c) Q,A"
  assumes ret_nrm_modif: "\<forall>s t. t \<in> (Modif (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes ret_abr_modif: "\<forall>s t. t \<in> (ModifAbr (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes modif_clause: 
          "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} Call q (Modif \<sigma>),(ModifAbr \<sigma>)"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -
  from to_prove 
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return' c) Q,A"
    by (rule conseqPre) blast
  from this ret_nrm_modif 
       ret_abr_modif 
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return c) Q,A"
    by (rule dynProcModifyReturnSameFaults) (insert modif_clause,auto)
  from this q show ?thesis
    by (rule conseqPre) 
qed

lemma ProcProcParModifyReturnNoAbr: 
  assumes q: "P \<subseteq> {s. p s = q} \<inter> P'"
   --{* @{thm[source] DynProcProcParNoAbrupt} introduces the same constraint as 
      first conjunction in @{term P'}, so the vcg can simplify it. *}
  assumes to_prove: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' (dynCall init p return' c) Q,A"
  assumes ret_nrm_modif: "\<forall>s t. t \<in> (Modif (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes modif_clause: 
            "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} (Call q) (Modif \<sigma>),{}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -
  from to_prove have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return' c) Q,A"
    by (rule conseqPre) blast
  from this ret_nrm_modif 
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return c) Q,A"
    by (rule DynProcModifyReturnNoAbr) (insert modif_clause,auto)
  from this q show ?thesis
    by (rule conseqPre) 
qed


lemma ProcProcParModifyReturnNoAbrSameFaults: 
  assumes q: "P \<subseteq> {s. p s = q} \<inter> P'"
      --{* @{thm[source] DynProcProcParNoAbrupt} introduces the same constraint as 
      first conjunction in @{term P'}, so the vcg can simplify it. *}
  assumes to_prove: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' (dynCall init p return' c) Q,A"
  assumes ret_nrm_modif: "\<forall>s t. t \<in> (Modif (init s)) 
                            \<longrightarrow> return' s t = return s t"
  assumes modif_clause: 
            "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> {\<sigma>} (Call q) (Modif \<sigma>),{}"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (dynCall init p return c) Q,A"
proof -
  from to_prove have 
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return' c) Q,A"
    by (rule conseqPre) blast
  from this ret_nrm_modif 
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> ({s. p s = q} \<inter> P') (dynCall init p return c) Q,A"
    by (rule ProcDynModifyReturnNoAbrSameFaults) (insert modif_clause,auto)
  from this q show ?thesis
    by (rule conseqPre) 
qed

lemma MergeGuards_iff: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P merge_guards c Q,A = \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A"
  by (auto intro: MergeGuardsI MergeGuardsD)

lemma CombineStrip': 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c' Q,A"
  assumes deriv_strip_triv: "\<Gamma>,{}\<turnstile>\<^bsub>/{}\<^esub> P c'' UNIV,UNIV"
  assumes c'': "c''= mark_guards False (strip_guards (-F) c')"
  assumes c: "merge_guards c = merge_guards (mark_guards False c')"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
proof -
  from deriv_strip_triv have deriv_strip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c'' UNIV,UNIV"
    by (auto intro: hoare_augment_context)
  from deriv_strip [simplified c'']
  have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P (strip_guards (- F) c') UNIV,UNIV"
    by (rule HoarePartialProps.MarkGuardsD)
  with deriv 
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c' Q,A"
    by (rule CombineStrip)
  hence "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P mark_guards False c' Q,A"
    by (rule MarkGuardsI)
  hence "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P merge_guards (mark_guards False c') Q,A"
    by (rule MergeGuardsI)
  hence "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P merge_guards c Q,A"
    by (simp add: c)
  thus ?thesis
    by (rule MergeGuardsD)
qed

lemma CombineStrip'': 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{True}\<^esub> P c' Q,A"
  assumes deriv_strip_triv: "\<Gamma>,{}\<turnstile>\<^bsub>/{}\<^esub> P c'' UNIV,UNIV"
  assumes c'': "c''= mark_guards False (strip_guards ({False}) c')"
  assumes c: "merge_guards c = merge_guards (mark_guards False c')"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> P c Q,A"
  apply (rule CombineStrip' [OF deriv deriv_strip_triv _ c]) 
  apply (insert c'')
  apply (subgoal_tac "- {True} = {False}")
  apply auto
  done

lemma AsmUN:
  "(\<Union>Z. {(P Z, p, Q Z,A Z)}) \<subseteq> \<Theta> 
  \<Longrightarrow> 
  \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) (Call p) (Q Z),(A Z)"
  by (blast intro: hoaret.Asm)


lemma hoaret_to_hoarep':
  "\<forall>Z. \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) p (Q Z),(A Z) \<Longrightarrow> \<forall>Z. \<Gamma>,{}\<turnstile>\<^bsub>/F\<^esub> (P Z) p (Q Z),(A Z)"
  by (iprover intro: total_to_partial)

lemma augment_context': 
  "\<lbrakk>\<Theta> \<subseteq> \<Theta>'; \<forall>Z. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z)  p (Q Z),(A Z)\<rbrakk> 
   \<Longrightarrow> \<forall>Z. \<Gamma>,\<Theta>'\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) p (Q Z),(A Z)"
  by (iprover intro: hoaret_augment_context)


lemma augment_emptyFaults:
 "\<lbrakk>\<forall>Z. \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/{}\<^esub> (P Z) p (Q Z),(A Z)\<rbrakk> \<Longrightarrow> 
    \<forall>Z. \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) p (Q Z),(A Z)"
  by (blast intro: augment_Faults)

lemma augment_FaultsUNIV:
 "\<lbrakk>\<forall>Z. \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P Z) p (Q Z),(A Z)\<rbrakk> \<Longrightarrow> 
    \<forall>Z. \<Gamma>,{}\<turnstile>\<^sub>t\<^bsub>/UNIV\<^esub> (P Z) p (Q Z),(A Z)"
  by (blast intro: augment_Faults)

lemma PostConjI [trans]:
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c R,B\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> B)"
  by (rule PostConjI)

lemma PostConjI' :
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c R,B\<rbrakk> 
  \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> B)"
  by (rule PostConjI) iprover+

lemma PostConjE [consumes 1]: 
  assumes conj: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c (Q \<inter> R),(A \<inter> B)" 
  assumes E: "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c R,B\<rbrakk> \<Longrightarrow> S"
  shows "S"
proof -
  from conj have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" by (rule conseqPost) blast+
  moreover
  from conj have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c R,B" by (rule conseqPost) blast+
  ultimately show "S" 
    by (rule E)
qed

subsubsection {* Rules for Single-Step Proof \label{sec:hoare-isar} *}

text {*
 We are now ready to introduce a set of Hoare rules to be used in
 single-step structured proofs in Isabelle/Isar.  

 \medskip Assertions of Hoare Logic may be manipulated in
 calculational proofs, with the inclusion expressed in terms of sets
 or predicates.  Reversed order is supported as well.
*}


lemma annotateI [trans]:
"\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P anno Q,A; c = anno\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A" 
  by (simp)

lemma annotate_normI:
  assumes deriv_anno: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>P anno Q,A" 
  assumes norm_eq: "normalize c = normalize anno" 
  shows "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub>P c Q,A"
proof -
  from HoareTotalProps.NormalizeI [OF deriv_anno] norm_eq
  have "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F \<^esub>P normalize c Q,A"
    by simp
  from NormalizeD [OF this]
  show ?thesis .
qed


lemma annotateWhile:
"\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnnoG gs b I V c) Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (while gs b c) Q,A"
  by (simp add: whileAnnoG_def)


lemma reannotateWhile:
"\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnnoG gs b I V c) Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnnoG gs b J V c) Q,A"
  by (simp add: whileAnnoG_def)

lemma reannotateWhileNoGuard:
"\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnno b I V c) Q,A\<rbrakk> \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (whileAnno b J V c) Q,A"
  by (simp add: whileAnno_def)

lemma [trans] : "P' \<subseteq> P \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P' c Q,A"
  by (rule conseqPre)
 
lemma [trans]: "Q \<subseteq> Q' \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c Q',A"
  by (rule conseqPost) blast+

lemma [trans]:
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. P s} c Q,A \<Longrightarrow> (\<And>s. P' s \<longrightarrow> P s) \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. P' s} c Q,A"
  by (rule conseqPre) auto

lemma [trans]:
    "(\<And>s. P' s \<longrightarrow> P s) \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. P s} c Q,A \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. P' s} c Q,A"
  by (rule conseqPre) auto

lemma [trans]:
    "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c {s. Q s},A \<Longrightarrow> (\<And>s. Q s \<longrightarrow> Q' s) \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c {s. Q' s},A"
  by (rule conseqPost) auto

lemma [trans]:
    "(\<And>s. Q s \<longrightarrow> Q' s) \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c {s. Q s},A \<Longrightarrow> \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P c {s. Q' s},A"
  by (rule conseqPost) auto

lemma [intro?]: "\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P Skip P,A"
  by (rule Skip) auto

lemma CondInt [trans,intro?]:
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P \<inter> b) c1 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> (P \<inter> - b) c2 Q,A\<rbrakk>
   \<Longrightarrow>
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> P (Cond b c1 c2) Q,A"
  by (rule Cond) auto
 
lemma CondConj [trans, intro?]:
  "\<lbrakk>\<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. P s \<and> b s} c1 Q,A; \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. P s \<and> \<not> b s} c2 Q,A\<rbrakk>
   \<Longrightarrow> 
   \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<^bsub>/F\<^esub> {s. P s} (Cond {s. b s} c1 c2) Q,A"
  by (rule Cond) auto
end

