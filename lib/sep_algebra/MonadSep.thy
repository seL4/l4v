(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory MonadSep
imports
  Sep_Algebra_L4v
  "../LemmaBucket"
begin

locale sep_lifted =
  fixes lft :: "'a \<Rightarrow> 's :: sep_algebra"
begin

abbreviation
  lift :: "('s \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("<_>")
where
  "<P> s \<equiv> P (lft s)"

lemma hoare_gen_lifted_asm:
  "(P \<Longrightarrow> \<lbrace>\<lambda>s. P' (lft s)\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. (P' and K P) (lft s)\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto intro: hoare_assume_pre)

lemma mapM_x_sep_inv':
  includes no_pre
  assumes f:
   "\<And>R x. x \<in> S \<Longrightarrow>
     \<lbrace>\<lambda>s.<P x \<and>* I \<and>* R> s \<and> I' s\<rbrace>
      f x
     \<lbrace>\<lambda>_ s.<Q x \<and>* I \<and>* R> s \<and> I' s\<rbrace>"
  shows
   "set xs \<subseteq> S \<Longrightarrow>
     \<lbrace>\<lambda>s.<\<And>* map P xs \<and>* I \<and>* R> s \<and> I' s\<rbrace>
      mapM_x f xs
     \<lbrace>\<lambda>_ s.<\<And>* map Q xs \<and>* I \<and>* R> s \<and> I' s\<rbrace>"
proof (induct xs arbitrary: R)
  case Nil
  thus ?case by (simp add: mapM_x_Nil)
next
  case (Cons x xs)
  thus ?case
    apply (simp add: sep_conj_assoc mapM_x_Cons)
    apply (wp)
     apply (insert Cons.hyps [where R1="Q x ** R"])[1]
     apply (simp add: sep_conj_ac)
    apply (insert f [where R1="R ** \<And>* map P xs" and x1=x ])[1]
    apply (simp add: sep_conj_ac)
    done
qed

lemmas mapM_x_sep_inv = mapM_x_sep_inv' [OF _ subset_refl]
lemmas mapM_x_sep = mapM_x_sep_inv [where I' = \<top>, simplified]
lemmas mapM_x_sep' = mapM_x_sep [where I=\<box>, simplified]

lemma mapM_x_set_sep_inv:
  "\<lbrakk>distinct xs; set xs = X; (\<And>R x. x \<in> X \<Longrightarrow> \<lbrace><P x \<and>* I \<and>* R> and I'\<rbrace> f x \<lbrace>\<lambda>_. <Q x \<and>* I \<and>* R> and I'\<rbrace>)\<rbrakk> \<Longrightarrow>
  \<lbrace><(\<And>* x \<in> X. P x) \<and>* I \<and>* R> and I'\<rbrace> mapM_x f xs \<lbrace>\<lambda>_. <(\<And>* x \<in> X. Q x) \<and>* I \<and>* R> and I'\<rbrace>"
  apply (clarsimp simp: pred_conj_def)
  apply (drule mapM_x_sep_inv [where R=R])
  apply (subst (asm) sep_list_conj_sep_map_set_conj, assumption)+
  apply assumption
  done

lemmas mapM_x_set_sep' = mapM_x_set_sep_inv [where I' = \<top>, simplified]

lemma mapM_x_set_sep:
  "\<lbrakk>distinct xs; \<And>R x. x \<in> set xs \<Longrightarrow> \<lbrace><P x \<and>* I \<and>* R>\<rbrace> f x \<lbrace>\<lambda>_. <Q x \<and>* I \<and>* R>\<rbrace>\<rbrakk>
 \<Longrightarrow> \<lbrace><(\<And>* x \<in> set xs. P x) \<and>* I \<and>* R>\<rbrace> mapM_x f xs \<lbrace>\<lambda>_. <(\<And>* x \<in> set xs. Q x) \<and>* I \<and>* R>\<rbrace>"
  by (erule mapM_x_set_sep', simp+)

lemma sep_list_conj_map_singleton_wp:
  "\<lbrakk>x \<in> set xs; \<And>R. \<lbrace><P \<and>* I x \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* I x \<and>* R>\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace><P \<and>* \<And>* map I xs \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* \<And>* map I xs \<and>* R>\<rbrace>"
  apply (rule hoare_chain [where P="<P \<and>* I x \<and>* \<And>* map I (remove1 x xs) \<and>* R>" and
                                 Q="\<lambda>_. <Q \<and>* I x \<and>* \<And>* map I (remove1 x xs) \<and>* R>"])
    apply fastforce
   apply (subst (asm) sep_list_conj_map_remove1, assumption)
   apply (sep_select_asm 3)
   apply (sep_solve)
  apply (subst sep_list_conj_map_remove1, sep_solve+)
  done

lemma sep_set_conj_map_singleton_wp:
  "\<lbrakk>finite xs; x \<in> xs; \<And>R. \<lbrace><P \<and>* I x \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* I x \<and>* R>\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace><P \<and>* (\<And>* x\<in>xs. I x) \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* (\<And>* x\<in>xs. I x) \<and>* R>\<rbrace>"
  apply (rule hoare_chain [where P="<P \<and>* I x \<and>* (\<And>* x\<in>xs - {x}. I x) \<and>* R>" and
                                 Q="\<lambda>_. <Q \<and>* I x \<and>* (\<And>* x\<in>xs - {x}. I x) \<and>* R>"], assumption)
   apply (subst (asm) sep.prod.remove, assumption+)
   apply sep_solve
  apply (subst sep.prod.remove, assumption+)
  apply sep_solve
  done

lemma sep_list_conj_submap_wp:
  "\<lbrakk>set xs \<subseteq> set ys; distinct xs; distinct ys;
   \<And>R. \<lbrace><P \<and>* \<And>* map I xs \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* \<And>* map I xs \<and>* R>\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace><P \<and>* \<And>* map I ys \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* \<And>* map I ys \<and>* R>\<rbrace>"
  apply (subst sep_list_con_map_filter [where t="\<lambda>x. x \<in> set xs" and xs=ys, THEN sym])
  apply (subst sep_list_con_map_filter [where t="\<lambda>x. x \<in> set xs" and xs=ys, THEN sym])
  apply (subgoal_tac "set [x\<leftarrow>ys . x \<in> set xs] = set xs")
   apply (subst sep_list_conj_eq [where xs="[x\<leftarrow>ys . x \<in> set xs]" and ys=xs], clarsimp+)
   apply (subst sep_list_conj_eq [where xs="[x\<leftarrow>ys . x \<in> set xs]" and ys=xs], clarsimp+)
   apply (clarsimp simp: sep_conj_assoc)
  apply auto
  done

(* This just saves some rearranging later. *)
lemma sep_list_conj_submap_wp':
  "\<lbrakk>set xs \<subseteq> set ys; distinct xs; distinct ys;
   \<And>R. \<lbrace><P \<and>* \<And>* map I xs \<and>* S \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* \<And>* map I xs \<and>* S \<and>* R>\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace><P \<and>* \<And>* map I ys \<and>* S \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* \<And>* map I ys \<and>* S \<and>* R>\<rbrace>"
  apply (cut_tac sep_list_conj_submap_wp [where P="P \<and>* S" and Q="Q \<and>* S" and
       I=I and R=R and ys=ys and xs=xs and f=f])
  apply (fastforce simp: sep_conj_ac)+
  done

lemma sep_set_conj_subset_wp:
  "\<lbrakk>xs \<subseteq> ys; finite xs; finite ys;
   \<And>R. \<lbrace><P \<and>* (\<And>* x \<in> xs. I x) \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* (\<And>* x \<in> xs. I x) \<and>* R>\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace><P \<and>* (\<And>* x \<in> ys. I x) \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* (\<And>* x \<in> ys. I x) \<and>* R>\<rbrace>"
  apply (subst sep_map_set_conj_restrict [where t="\<lambda>x. x \<in> xs" and xs=ys], assumption)
  apply (subst sep_map_set_conj_restrict [where t="\<lambda>x. x \<in> xs" and xs=ys], assumption)
  apply (subgoal_tac "{x \<in> ys. x \<in> xs} = xs")
   apply (clarsimp simp: sep_conj_assoc)
  apply auto
  done

(* This just saves some rearranging later. *)
lemma sep_set_conj_subset_wp':
  "\<lbrakk>xs \<subseteq> ys; finite xs; finite ys;
   \<And>R. \<lbrace><P \<and>* (\<And>* x \<in> xs. I x) \<and>* S \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* (\<And>* x \<in> xs. I x) \<and>* S \<and>* R>\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace><P \<and>* (\<And>* x \<in> ys. I x) \<and>* S \<and>* R>\<rbrace> f \<lbrace>\<lambda>_. <Q \<and>* (\<And>* x \<in> ys. I x) \<and>* S \<and>* R>\<rbrace>"
  apply (cut_tac sep_set_conj_subset_wp [where P="P \<and>* S" and Q="Q \<and>* S" and
       I=I and R=R and ys=ys and xs=xs and f=f])
  apply (fastforce simp: sep_conj_ac)+
  done

end

end
