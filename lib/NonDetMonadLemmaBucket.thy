(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory NonDetMonadLemmaBucket
imports
  Lib
  More_NonDetMonadVCG
  More_Monad
  Monad_Equations
  Monad_Commute
  No_Fail
  No_Throw
  CutMon
  Oblivious
  Injection_Handler
  WhileLoopRulesCompleteness
  "Word_Lib.Distinct_Prop" (* for distinct_tuple_helper *)
begin

lemma distinct_tuple_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. distinct (x # xs rv s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. distinct (x # (map fst (zip (xs rv s) (ys rv s))))\<rbrace>"
  apply (erule hoare_strengthen_post)
  apply (erule distinct_prefix)
  apply (simp add: map_fst_zip_prefix)
  done


lemma mapME_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapME f xs \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  apply (induct xs)
   apply (simp add: mapME_def sequenceE_def)
   apply wp
   apply simp
  apply (simp add: mapME_Cons)
  apply (wp x|simp)+
  done

lemmas mapME_wp' = mapME_wp [OF _ subset_refl]

lemma mapM_x_inv_wp2:
  assumes post: "\<And>s. \<lbrakk> I s; V [] s \<rbrakk> \<Longrightarrow> Q s"
  and     hr: "\<And>a as. suffix (a # as) xs \<Longrightarrow> \<lbrace>\<lambda>s. I s \<and> V (a # as) s\<rbrace> m a \<lbrace>\<lambda>r s. I s \<and> V as s\<rbrace>"
  shows   "\<lbrace>I and V xs\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
proof (induct xs rule: list_induct_suffix)
  case Nil thus ?case
    apply (simp add: mapM_x_Nil)
    apply wp
    apply (clarsimp intro!: post)
    done
next
  case (Cons x xs)
  thus ?case
    apply (simp add: mapM_x_Cons)
    apply wp
     apply (wp hr)
    apply assumption
    done
qed

lemma mapM_x_inv_wp3:
  fixes m :: "'b \<Rightarrow> ('a, unit) nondet_monad"
  assumes hr: "\<And>a as bs. xs = as @ [a] @ bs \<Longrightarrow>
     \<lbrace>\<lambda>s. I s \<and> V as s\<rbrace> m a \<lbrace>\<lambda>r s. I s \<and> V (as @ [a]) s\<rbrace>"
  shows   "\<lbrace>\<lambda>s. I s \<and> V [] s\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv s. I s \<and> V xs s\<rbrace>"
  using hr
proof (induct xs rule: rev_induct)
  case Nil thus ?case
    apply (simp add: mapM_x_Nil)
    done
next
  case (snoc x xs)
  show ?case
    apply (simp add: mapM_append_single)
    apply (wp snoc.prems)
      apply simp
     apply (rule snoc.hyps [OF snoc.prems])
     apply simp
    apply assumption
    done
qed

lemma mapME_x_inv_wp:
  assumes x: "\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>P\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>E\<rbrace>"
  apply (induct xs)
   apply (simp add: mapME_x_def sequenceE_x_def)
   apply wp
  apply (simp add: mapME_x_def sequenceE_x_def)
  apply (fold mapME_x_def sequenceE_x_def)
  apply wp
   apply (rule x)
  apply assumption
  done

lemma mapM_upd:
  assumes "\<And>x rv s s'. (rv,s') \<in> fst (f x s) \<Longrightarrow> x \<in> set xs \<Longrightarrow> (rv, g s') \<in> fst (f x (g s))"
  shows "(rv,s') \<in> fst (mapM f xs s) \<Longrightarrow> (rv, g s') \<in> fst (mapM f xs (g s))"
  using assms
proof (induct xs arbitrary: rv s s')
  case Nil
  thus ?case by (simp add: mapM_Nil return_def)
next
  case (Cons z zs)
  from Cons.prems
  show ?case
    apply (clarsimp simp: mapM_Cons in_monad)
    apply (drule Cons.prems, simp)
    apply (rule exI, erule conjI)
    apply (erule Cons.hyps)
    apply (erule Cons.prems)
    apply simp
    done
qed

lemma gets_the_validE_R_wp:
  "\<lbrace>\<lambda>s. f s \<noteq> None \<and> isRight (the (f s)) \<and> Q (theRight (the (f s))) s\<rbrace>
     gets_the f
   \<lbrace>Q\<rbrace>,-"
  apply (simp add: gets_the_def validE_R_def validE_def)
  apply (wp | wpc | simp add: assert_opt_def)+
  apply (clarsimp split: split: sum.splits)
  done

lemma return_bindE:
  "isRight v \<Longrightarrow> return v >>=E f = f (theRight v)"
  by (clarsimp simp: isRight_def return_returnOk)

lemma no_fail_mapM_wp:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> no_fail (P x) (f x)"
  assumes "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P x\<rbrace> f y \<lbrace>\<lambda>_. P x\<rbrace>"
  shows "no_fail (\<lambda>s. \<forall>x \<in> set xs. P x s) (mapM f xs)"
  using assms
proof (induct xs)
  case Nil
  thus ?case by (simp add: mapM_empty)
next
  case (Cons z zs)
  show ?case
    apply (clarsimp simp: mapM_Cons)
    apply (wp Cons.prems Cons.hyps hoare_vcg_const_Ball_lift|simp)+
    done
qed

lemma list_case_return: (* FIXME lib: move to Lib *)
  "(case xs of [] \<Rightarrow> return v | y # ys \<Rightarrow> return (f y ys))
    = return (case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> f y ys)"
  by (simp split: list.split)

lemma lifted_if_collapse: (* FIXME lib: move to Lib *)
  "(if P then \<top> else f) = (\<lambda>s. \<not>P \<longrightarrow> f s)"
  by auto

lemmas list_case_return2 = list_case_return (* FIXME lib: eliminate *)

lemma no_fail_mapM:
  "\<forall>x. no_fail \<top> (f x) \<Longrightarrow> no_fail \<top> (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  apply (wp|fastforce)+
  done

lemma filterM_preserved:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. P\<rbrace> \<rbrakk>
      \<Longrightarrow> \<lbrace>P\<rbrace> filterM m xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct xs)
   apply (wp | simp | erule meta_mp | drule meta_spec)+
  done

lemma filterM_distinct1:
  "\<lbrace>\<top> and K (P \<longrightarrow> distinct xs)\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. (P \<longrightarrow> distinct rv) \<and> set rv \<subseteq> set xs\<rbrace>"
  apply (rule hoare_gen_asm, erule rev_mp)
  apply (rule rev_induct [where xs=xs])
   apply (clarsimp | wp)+
  apply (simp add: filterM_append)
  apply (erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext[rotated], rule hoare_vcg_prop)
  apply (wp, clarsimp)
  apply blast
  done

lemma filterM_subset:
  "\<lbrace>\<top>\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. set rv \<subseteq> set xs\<rbrace>"
  by (rule hoare_chain, rule filterM_distinct1[where P=False], simp_all)

lemma filterM_all:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P y\<rbrace> m x \<lbrace>\<lambda>rv. P y\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. \<forall>x \<in> set xs. P x s\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. P x s\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. set rv \<subseteq> set xs \<and> (\<forall>x \<in> set xs. P x s)"
              in hoare_strengthen_post)
   apply (wp filterM_subset hoare_vcg_const_Ball_lift filterM_preserved)
    apply simp+
  apply blast
  done

lemma filterM_distinct:
  "\<lbrace>K (distinct xs)\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. distinct rv\<rbrace>"
  by (rule hoare_chain, rule filterM_distinct1[where P=True], simp_all)

lemma mapM_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  apply wp
   apply (rule x, clarsimp)
  apply simp
  done

lemma mapM_wp':
  assumes x: "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule mapM_wp)
   apply (erule x)
  apply simp
  done

lemma mapM_set:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. Q x\<rbrace>"
  assumes "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P and Q y\<rbrace> f x \<lbrace>\<lambda>_. Q y\<rbrace>"
  shows "\<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>_ s. \<forall>x \<in> set xs. Q x s\<rbrace>"
using assms
proof (induct xs)
  case Nil show ?case
    by (simp add: mapM_def sequence_def) wp
next
  case (Cons y ys)
  have PQ_inv: "\<And>x. x \<in> set ys \<Longrightarrow> \<lbrace>P and Q y\<rbrace> f x \<lbrace>\<lambda>_. P and Q y\<rbrace>"
    apply (simp add: pred_conj_def)
    apply (rule hoare_pre)
     apply (wp Cons|simp)+
    done
  show ?case
    apply (simp add: mapM_Cons)
    apply wp
     apply (rule hoare_vcg_conj_lift)
      apply (rule hoare_strengthen_post)
       apply (rule mapM_wp')
       apply (erule PQ_inv)
      apply simp
     apply (wp Cons|simp)+
    done
qed

lemma mapM_x_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (subst mapM_x_mapM) (wp mapM_wp x)

lemma no_fail_mapM':
  assumes rl: "\<And>x. no_fail (\<lambda>_. P x) (f x)"
  shows "no_fail (\<lambda>_. \<forall>x \<in> set xs. P x) (mapM f xs)"
proof (induct xs)
  case Nil thus ?case by (simp add: mapM_def sequence_def)
next
  case (Cons x xs)

  have nf: "no_fail (\<lambda>_. P x) (f x)" by (rule rl)
  have ih: "no_fail (\<lambda>_. \<forall>x \<in> set xs. P x) (mapM f xs)" by (rule Cons)

  show ?case
    apply (simp add: mapM_Cons)
    apply (rule no_fail_pre)
    apply (wp nf ih)
    apply simp
    done
qed

lemma det_mapM:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> det (f x)"
  shows      "set xs \<subseteq> S \<Longrightarrow> det (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons x)
  done

lemma det_zipWithM_x:
  assumes x: "\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> det (f x y)"
  shows      "det (zipWithM_x f xs ys)"
  apply (simp add: zipWithM_x_mapM)
  apply (rule bind_detI)
   apply (rule det_mapM [where S="set (zip xs ys)"])
    apply (clarsimp simp add: x)
   apply simp
  apply simp
  done

lemma empty_fail_sequence_x :
  assumes "\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m"
  shows "empty_fail (sequence_x ms)" using assms
  by (induct ms) (auto simp: sequence_x_def)

lemma mapME_set:
  assumes  est: "\<And>x. \<lbrace>R\<rbrace> f x \<lbrace>P\<rbrace>, -"
  and     invp: "\<And>x y. \<lbrace>R and P x\<rbrace> f y \<lbrace>\<lambda>_. P x\<rbrace>, -"
  and     invr: "\<And>x. \<lbrace>R\<rbrace> f x \<lbrace>\<lambda>_. R\<rbrace>, -"
  shows "\<lbrace>R\<rbrace> mapME f xs \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. P x s\<rbrace>, -"
proof (rule hoare_post_imp_R [where Q' = "\<lambda>rv s. R s \<and> (\<forall>x \<in> set rv. P x s)"], induct xs)
  case Nil
  thus ?case by (simp add: mapME_Nil | wp returnOKE_R_wp)+
next
  case (Cons y ys)

  have minvp: "\<And>x. \<lbrace>R and P x\<rbrace> mapME f ys \<lbrace>\<lambda>_. P x\<rbrace>, -"
    apply (rule hoare_pre)
     apply (rule_tac Q' = "\<lambda>_ s. R s \<and> P x s" in hoare_post_imp_R)
      apply (wp mapME_wp' invr invp)+
      apply simp
     apply simp
    apply simp
    done

  show ?case
    apply (simp add: mapME_Cons)
    apply (wp)
     apply (rule_tac Q' = "\<lambda>xs s. (R s \<and> (\<forall>x \<in> set xs. P x s)) \<and> P x s" in hoare_post_imp_R)
      apply (wp Cons.hyps minvp)
     apply simp
    apply (fold validE_R_def)
    apply simp
    apply (wp invr est)
    apply simp
    done
qed clarsimp


lemma empty_fail_mapM_x [simp]:
  "(\<And>x. empty_fail (a x)) \<Longrightarrow> empty_fail (mapM_x a xs)"
  apply (induct_tac xs)
   apply (clarsimp simp: mapM_x_Nil)
  apply (clarsimp simp: mapM_x_Cons)
  done

lemma valid_isRight_theRight_split:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q True rv s\<rbrace>,\<lbrace>\<lambda>e s. \<forall>v. Q False v s\<rbrace> \<Longrightarrow>
     \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q (isRight rv) (theRight rv) s\<rbrace>"
  apply (simp add: validE_def)
  apply (erule hoare_strengthen_post)
  apply (simp add: isRight_def split: sum.split_asm)
  done

lemma mapM_upd_inv:
  assumes f: "\<And>x rv. (rv,s) \<in> fst (f x s) \<Longrightarrow> x \<in> set xs \<Longrightarrow> (rv, g s) \<in> fst (f x (g s))"
  assumes inv: "\<And>x. \<lbrace>(=) s\<rbrace> f x \<lbrace>\<lambda>_. (=) s\<rbrace>"
  shows "(rv,s) \<in> fst (mapM f xs s) \<Longrightarrow> (rv, g s) \<in> fst (mapM f xs (g s))"
  using f inv
proof (induct xs arbitrary: rv s)
  case Nil
  thus ?case by (simp add: mapM_Nil return_def)
next
  case (Cons z zs)
  from Cons.prems
  show ?case
    apply (clarsimp simp: mapM_Cons in_monad)
    apply (frule use_valid, assumption, rule refl)
    apply clarsimp
    apply (drule Cons.prems, simp)
    apply (rule exI, erule conjI)
    apply (drule Cons.hyps)
      apply simp
     apply assumption
    apply simp
    done
qed

lemma case_option_find_give_me_a_map:
  "case_option a return (find f xs)
    = liftM theLeft
      (mapME (\<lambda>x. if (f x) then throwError x else returnOk ()) xs
        >>=E (\<lambda>x. assert (\<forall>x \<in> set xs. \<not> f x)
                >>= (\<lambda>_. liftM (Inl :: 'a \<Rightarrow> 'a + unit) a)))"
  apply (induct xs)
   apply simp
   apply (simp add: liftM_def mapME_Nil)
  apply (simp add: mapME_Cons split: if_split)
  apply (clarsimp simp add: throwError_def bindE_def bind_assoc
                            liftM_def)
  apply (rule bind_cong [OF refl])
  apply (simp add: lift_def throwError_def returnOk_def split: sum.split)
  done

end
