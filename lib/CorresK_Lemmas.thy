(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)


theory CorresK_Lemmas
imports Corres_Method "../spec/design/Syscall_H" "../spec/abstract/Syscall_A"
begin

lemma corres_throwError_str [corres_concrete_rER]:
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
      apply (corressimp corresK: x IH wp: y)
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
  apply (rule corresK_use_guard, elim conjE)
  subgoal premises prems
proof (insert \<open>length xs = length ys\<close>, insert S, induct xs ys rule: list_induct2)
  case Nil
  show ?case
    by (simp add: mapM_def sequence_def corres_underlyingK_def)
next
  case (Cons a as b bs)
  from Cons have P: "(a, b) \<in> S"
    by simp
  from Cons have Q: "corres_underlyingK R nf nf' ((\<forall>x y. (x,y) \<in> set (zip as bs) \<longrightarrow> F x y)) r P P' (mapM f as) (mapM f' bs)"
    apply -
    apply (corres_pre)
    apply (erule meta_mp)
    by (clarsimp simp: prems)+
  show ?case
    apply (simp add: mapM_Cons)
    apply (corressimp corresK: z Q wp: P simp: corres_protect_def)
      apply (rule corres_rv_proveT)
      apply (fastforce simp: prems)
      apply (corressimp wp: w | rule P | rule hoare_drop_imps)+
      apply (insert prems Cons)
      apply (auto)
    done
qed
done

lemma corresK_mapM_x:
  assumes S: "(set (zip xs ys) \<subseteq> S)"
  assumes x: "\<And>x y. corres_protect ((x, y) \<in> S) \<Longrightarrow> corres_underlyingK sr nf nf' (F x y) dc P P' (f x) (f' y)"
  assumes y: "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
             "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P'\<rbrace> f' y \<lbrace>\<lambda>rv. P'\<rbrace>"
  shows      "corres_underlyingK sr nf nf'
                (length xs = length ys \<and> (\<forall>(x,y)\<in>S. F x y)) dc P P' (mapM_x f xs) (mapM_x f' ys)"
  apply (simp add: mapM_x_mapM)
  apply (corressimp corresK: corresK_mapM[where S=S and r=dc and r'=dc] x wp: y simp: S | assumption)+
  done

lemma corresK_subst_both: "g' = f' \<Longrightarrow> g = f \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' g g'" by simp

lemma if_fun_true: "(if A then B else (\<lambda>_. True)) = (\<lambda>s. (A  \<longrightarrow> B s))" by simp

lemmas corresK_whenE [corres_splits] =
  corresK_if[THEN
    corresK_subst_both[OF whenE_def[THEN meta_eq_to_obj_eq] whenE_def[THEN meta_eq_to_obj_eq]],
    OF _ corresK_returnOk[where r="f \<oplus> dc" for f], simplified, simplified if_fun_true]

lemmas corresK_head_splits[corres_splits] =
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
  corresK_Id[where nf'=False and r="op =",simplified]
  corresK_Id[where nf'=False,simplified]
  corresK_Id[where nf'=True and r="op =", simplified]
  corresK_Id[where nf'=True, simplified]

lemma corresK_unit_rv_eq_any[corres_concrete_r]:
  "corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
    corres_underlyingK sr nf nf' F
      (\<lambda>(x :: unit) (y :: unit). x = y) P P' f f'"
  apply (clarsimp simp add: corres_underlyingK_def)
  apply (erule corres_rel_imp)
  apply simp
  done

lemma corresK_unit_rv_dc_any[corres_concrete_r]:
  "corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
    corres_underlyingK sr nf nf' F
      (\<lambda>(x :: unit) (y :: unit). dc x y) P P' f f'"
  apply (clarsimp simp add: corres_underlyingK_def)
  apply (erule corres_rel_imp)
  apply simp
  done

end