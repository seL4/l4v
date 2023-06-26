(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory CorresK_Lemmas
imports
  "Lib.CorresK_Method"
  "ExecSpec.Syscall_H"
  "ASpec.Syscall_A"
begin

lemma corres_throwError_str [corresK_concrete_rER]:
  "corres_underlyingK sr nf nf' (r (Inl a) (Inl b)) r \<top> \<top> (throwError a) (throw b)"
  "corres_underlyingK sr nf nf' (r (Inl a) (Inl b)) r \<top> \<top> (throwError a) (throwError b)"
 by (simp add: corres_underlyingK_def)+

lemma corresK_use_guard:
  "(F \<Longrightarrow> corres_underlyingK sr nf nf' F r Q Q' f g) \<Longrightarrow> corres_underlyingK sr nf nf' F r Q Q' f g"
  by (simp add: corres_underlyingK_def)

lemma mapME_x_corresK_inv:
  assumes x: "\<And>x. corres_underlyingK sr nf nf' (F x) (f \<oplus> dc) (P x) (P' x) (m x) (m' x)"
  assumes y: "\<And>x P. \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>x. P\<rbrace>,-" "\<And>x P'. \<lbrace>P'\<rbrace> m' x \<lbrace>\<lambda>x. P'\<rbrace>,-"
  shows      "corres_underlyingK sr nf nf' (xs = ys \<and> (\<forall>x \<in> set xs. F x)) (f \<oplus> dc) (\<lambda>s. \<forall>x \<in> set xs. P x s) (\<lambda>s. \<forall>y \<in> set ys. P' y s)
                              (mapME_x m xs) (mapME_x m' ys)"
  apply (rule corresK_use_guard, elim conjE)
  subgoal premises prems
  unfolding \<open>xs = ys\<close>
  proof (induct ys)
    case Nil
    show ?case
      by (simp add: mapME_x_def sequenceE_x_def returnOk_def corres_underlyingK_def)
  next
    case (Cons z zs)
    from Cons have IH:
      "corres_underlyingK sr nf nf' (\<forall>x\<in>set zs. F x) (f \<oplus> dc) (\<lambda>s. \<forall>x\<in>set zs. P x s) (\<lambda>s. \<forall>y\<in>set zs. P' y s)
                       (mapME_x m zs) (mapME_x m' zs)" by (auto simp add:  dc_def)
    show ?case
      apply (simp add: mapME_x_def sequenceE_x_def)
      apply (fold mapME_x_def sequenceE_x_def dc_def)
      apply (corresKsimp corresK: x IH wp: y)
      done
  qed
  done

lemma corresK_mapM:
  assumes S: "set (zip xs ys) \<subseteq> S"
  assumes z: "\<And>x y. corres_protect ((x, y) \<in> S) \<Longrightarrow> corres_underlyingK R nf nf' (F x y) r' P P' (f x) (f' y)"
  assumes w: "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
             "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P'\<rbrace> f' y \<lbrace>\<lambda>rv. P'\<rbrace>"
  shows      "corres_underlyingK R nf nf'
                  ((length xs = length ys) \<and>
                   (r [] []) \<and> (\<forall>x xs y ys. r xs ys \<longrightarrow> r' x y \<longrightarrow> r (x # xs) (y # ys)) \<and>
                  (\<forall>(x,y)\<in>S. F x y)) r P P' (mapM f xs) (mapM f' ys)"
  unfolding corres_underlyingK_def
  apply (rule impI, rule corres_mapM[of r r' S])
  using assms unfolding corres_underlyingK_def by (auto simp: corres_protect_def)

definition
  "F_all2 F xs ys =
    (\<exists>F'.
      (\<forall>x y xs ys.
        (F' x y \<longrightarrow> list_all2 F' xs ys \<longrightarrow> F x y xs ys)) \<and> list_all2 F' xs ys)"


lemma F_all2_pointwise[simp]:
  "F_all2 (\<lambda>x y _ _. F x y) xs ys = list_all2 F xs ys"
  apply (rule iffI)
  apply (clarsimp simp: F_all2_def)
  subgoal for F'
  apply (rule list_all2_induct_suffixeq[where Q=F']; simp)
  apply (drule_tac x=x in spec)
  apply (drule_tac x=y in spec)
  apply fastforce
  done
  apply (clarsimp simp:F_all2_def)
  apply (rule_tac x=F in exI)
  apply clarsimp
  done

lemma F_all2_list:
   "F xs ys \<Longrightarrow> \<exists>F'. (\<forall>xs ys. (F xs ys = list_all2 F' xs ys)) \<Longrightarrow> F_all2 (\<lambda>_ _ xs ys. F xs ys) xs ys"
  apply (clarsimp simp: F_all2_def)
  apply (rule_tac x=F' in exI)
  by auto

lemma list_all2_conjD:
  "list_all2 (\<lambda>x y. Q x y \<and> P x y) xs ys \<Longrightarrow> list_all2 Q xs ys \<and> list_all2 P xs ys"
  by (induct rule: list_all2_induct; simp)


lemma
  list_all2_to_list_all:
  "list_all2 P xs xs = list_all (\<lambda>x. P x x) xs"
  by (induct xs;simp)

lemma list_all_mem_subset:
  "list_all (\<lambda>y. y \<in> set xs) ys = (set ys \<subseteq> set xs)"
  by (induct ys; simp)

lemma F_all2_eq:
  "(\<And>x xs'. x \<in> set xs \<Longrightarrow> set xs' \<subseteq> set xs \<Longrightarrow> F x x xs' xs') \<Longrightarrow> F_all2 F xs xs"
 apply (simp add: F_all2_def)
 apply (rule_tac x="\<lambda>x y. x \<in> set xs \<and> x = y" in exI)
 apply (intro conjI impI allI)
 apply (drule list_all2_conjD)
 apply (simp add: list.rel_eq)
 apply (simp add: list_all2_to_list_all list_all_mem_subset)
 apply (rule list.rel_refl_strong;simp)
 done

lemma F_all2_conjI:
  "F_all2 F xs ys \<Longrightarrow> F_all2 F' xs ys \<Longrightarrow>
    F_all2 (\<lambda>x y xs ys. F x y xs ys \<and> F' x y xs ys) xs ys"
  apply (clarsimp simp: F_all2_def)
  apply (rule_tac x="\<lambda>x y. F'a x y \<and> F'aa x y" in exI)
  by (auto dest: list_all2_conjD intro: list_all2_conj)

lemma corresK_mapM_list_all2:
  assumes x: "\<And>x y xs ys. corres_underlyingK sr nf nf' (F x y xs ys) r' (I (x#xs)) (I' (y#ys)) (f x) (f' y)"
  assumes "\<And>x y xs. \<lbrakk> S x y; suffix (x#xs) as \<rbrakk> \<Longrightarrow> \<lbrace> I  (x#xs) \<rbrace> f  x \<lbrace> \<lambda>rv. I  xs \<rbrace>"
  assumes "\<And>x y ys. \<lbrakk> S x y; suffix (y#ys) cs \<rbrakk> \<Longrightarrow> \<lbrace> I' (y#ys) \<rbrace> f' y \<lbrace> \<lambda>rv. I' ys \<rbrace>"
  shows "corres_underlyingK sr nf nf'
          (r [] [] \<and> (\<forall> x y xs ys. r' x y \<longrightarrow> r xs ys \<longrightarrow> r (x # xs) (y # ys)) \<and>
            list_all2 S as cs \<and> F_all2 F as cs)
                            r (I as) (I' cs) (mapM f as) (mapM f' cs)"
  unfolding corres_underlyingK_def
  apply (clarsimp simp: F_all2_def)
  subgoal for F'
  apply (rule corres_mapM_list_all2[of r r' "\<lambda>x y. S x y \<and> F' x y"]; (rule assms | assumption | clarsimp)?)
  apply (rule x[THEN corresK_unlift])
  apply (drule list_all2_conjD)
  apply (clarsimp simp: assms | assumption)+
  apply (rule list_all2_conj; simp)
  done
  done

lemma corresK_discard_rv:
  assumes A[corresK]: "corres_underlyingK sr nf nf' F r' P P' a c"
  shows "corres_underlyingK sr nf nf' F dc P P' (do x \<leftarrow> a; return () od) (do x \<leftarrow> c; return () od)"
  by corresKsimp

lemma corresK_mapM_mapM_x:
  assumes "corres_underlyingK sr nf nf' F r' P P' (mapM f as) (mapM f' cs)"
  shows "corres_underlyingK sr nf nf' F dc P P' (mapM_x f as) (mapM_x f' cs)"
  unfolding mapM_x_mapM by (rule corresK_discard_rv, rule assms)

lemmas corresK_mapM_x_list_all2
  = corresK_mapM_list_all2[where r'=dc,
                           THEN corresK_mapM_mapM_x[where r'=dc],
                           simplified]
lemmas corresK_mapM_x
  = corresK_mapM[where r'=dc,
                 THEN corresK_mapM_mapM_x[where r'=dc],
                 simplified]

lemma corresK_subst_both: "g' = f' \<Longrightarrow> g = f \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' g g'" by simp

lemma if_fun_true: "(if A then B else (\<lambda>_. True)) = (\<lambda>s. (A  \<longrightarrow> B s))" by simp

lemmas corresK_whenE [corresK_splits] =
  corresK_if[THEN
    corresK_subst_both[OF whenE_def[THEN meta_eq_to_obj_eq] whenE_def[THEN meta_eq_to_obj_eq]],
    OF _ corresK_returnOk[where r="f \<oplus> dc" for f], simplified, simplified if_fun_true]

lemmas corresK_head_splits[corresK_splits] =
  corresK_split[where d="return", simplified]
  corresK_splitE[where d="returnOk", simplified]
  corresK_split[where b="return", simplified]
  corresK_splitE[where b="returnOk", simplified]

lemmas corresK_modify =
  corres_modify[atomized, @corresK_convert]

lemmas corresK_modifyT = corresK_modify[where P=\<top> and P'=\<top>, simplified]

lemma corresK_Id:
  "(nf' \<Longrightarrow> no_fail P' g) \<Longrightarrow>
    corres_underlyingK Id nf nf' (f = g \<and> (\<forall>rv. r rv rv)) r (\<lambda>_. True) P' f g"
  apply (rule corresK_assume_guard)
  apply (rule corres_Id;simp)
  done

lemmas [corresK] =
  corresK_Id[where nf'=False and r="(=)",simplified]
  corresK_Id[where nf'=False,simplified]
  corresK_Id[where nf'=True and r="(=)", simplified]
  corresK_Id[where nf'=True, simplified]

lemma corresK_unit_rv_eq_any[corresK_concrete_r]:
  "corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
    corres_underlyingK sr nf nf' F
      (\<lambda>(x :: unit) (y :: unit). x = y) P P' f f'"
  apply (clarsimp simp add: corres_underlyingK_def)
  apply (erule corres_rel_imp)
  apply simp
  done

lemma corresK_unit_rv_dc_any[corresK_concrete_r]:
  "corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
    corres_underlyingK sr nf nf' F
      (\<lambda>(x :: unit) (y :: unit). dc x y) P P' f f'"
  apply (clarsimp simp add: corres_underlyingK_def)
  apply (erule corres_rel_imp)
  apply simp
  done

end
