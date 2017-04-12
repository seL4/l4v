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
      apply (corressimp corresK: x IH wp: y corres_rv_defer_left)
      by (auto split: sum.splits)
  qed
  done

end