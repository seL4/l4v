(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory DetWPLib
imports HaskellLemmaBucket
begin

definition
  "det_wp P f \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>r. f s = ({r}, False))"

lemma det_result:
  "\<lbrakk> det_wp P f; \<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. fst (f s) = {(rv, s)}\<rbrace>"
  by (fastforce simp: det_wp_def valid_def split_def)

lemma det_wp_use:
  "det_wp P f \<Longrightarrow> P s \<Longrightarrow> (fst (f s) = {s'}) = (s' \<in> fst (f s))"
  by (fastforce simp: det_wp_def)

lemma det_wp_det:
  "det f \<Longrightarrow> det_wp \<top> f"
  by (clarsimp simp: det_def det_wp_def)

lemma det_wp_no_fail:
  "det_wp P f \<Longrightarrow> no_fail P f"
  by (fastforce simp: det_wp_def no_fail_def)

lemma det_wp_bind [wp]:
  "\<lbrakk> det_wp P f; \<And>rv. det_wp (Q rv) (g rv); \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> det_wp (P and P') (f >>= (\<lambda>rv. g rv))"
  apply (simp add: det_wp_def valid_def split_def bind_def)
  apply fastforce
  done

lemma det_wp_pre[wp_pre]:
  "det_wp P' f \<Longrightarrow> (\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> det_wp P f"
  by (simp add: det_wp_def)

lemma det_wp_return [wp]:
  "det_wp \<top> (return x)"
  by (simp add: det_wp_def return_def)

lemma det_wp_case_option [wp]:
  "\<lbrakk> x = None \<Longrightarrow> det_wp P f;
     \<And>y. x = Some y \<Longrightarrow> det_wp (Q y) (g y) \<rbrakk> \<Longrightarrow>
  det_wp (\<lambda>s. (x = None \<longrightarrow> P s) \<and> (\<forall>y. x = Some y \<longrightarrow> Q y s)) (case_option f g x)"
  by (cases x) auto

lemma det_wp_mapM [wp]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> det_wp (P x) (f x)"
  assumes "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P x\<rbrace> f y \<lbrace>\<lambda>_. P x\<rbrace>"
  shows "det_wp (\<lambda>s. \<forall>x \<in> set xs. P x s) (mapM f xs)" using assms
proof (induct xs)
  case Nil thus ?case
    by (simp add: mapM_Nil) (rule det_wp_pre, wp)
next
  case (Cons z zs)
  show ?case
  apply (simp add: mapM_Cons)
  apply (rule det_wp_pre)
   apply (wp Cons.hyps Cons.prems hoare_vcg_const_Ball_lift|simp)+
  done
qed

lemma det_wp_get [wp]:
  "det_wp \<top> get"
  by (simp add: get_def det_wp_def)

lemma det_wp_gets [wp]:
  "det_wp \<top> (gets f)"
  by (simp add: simpler_gets_def det_wp_def)

lemma det_wp_fail [wp]:
  "det_wp \<bottom> fail"
  by (simp add: fail_def det_wp_def)

lemma det_wp_assert [wp]:
  "det_wp (\<lambda>_. P) (assert P)"
  by (simp add: assert_def det_wp_fail det_wp_return)

lemma det_wp_stateAssert [wp]:
  "det_wp P (stateAssert P xs)"
  apply (simp add: stateAssert_def)
  apply (rule det_wp_pre, wp)
  apply simp
  done

lemma det_wp_select_f:
  "det_wp (\<lambda>_. P s) f \<Longrightarrow> det_wp (\<lambda>_. P s) (select_f (f s))"
  apply (clarsimp simp: select_f_def det_wp_def)
  apply (erule_tac x=s in allE)
  apply clarsimp
  done

lemma det_wp_modify [wp]:
  "det_wp \<top> (modify f)"
  by (simp add: det_wp_def simpler_modify_def)

(* DetWP.thy:det_wp_liftM line 31 annotation [wp]*)
lemma det_wp_liftM [wp]:
  "det_wp P g \<Longrightarrow> det_wp P (liftM f g)"
  apply (simp add: liftM_def)
  apply (rule det_wp_pre)
   apply (wp|simp)+
  done


(* DetWP.thy:det_wp_when line 37 annotation [wp]*)
lemma det_wp_when [wp]:
  "det_wp P f \<Longrightarrow> det_wp (\<lambda>s. Q \<longrightarrow> P s) (when Q f)"
  by (clarsimp simp: when_def det_wp_return)

(* DetWP.thy:det_wp_unless line 41 annotation [wp]*)
lemma det_wp_unless [wp]:
  "det_wp P f \<Longrightarrow> det_wp (\<lambda>s. \<not>Q \<longrightarrow> P s) (unless Q f)"
  by (simp add: unless_def det_wp_when)

(* DetWP.thy:det_wp_assert_opt line 38 annotation [wp]*)
lemma det_wp_assert_opt :
  "det_wp (\<lambda>_. x \<noteq> None) (assert_opt x)"
  apply (simp add: assert_opt_def)
  apply (rule det_wp_pre, wp)
  apply simp
  done

lemma gets_the_det_wp[wp]:
  "det_wp (\<lambda>s. \<exists>v. f s = Some v) (gets_the f)"
  apply (simp add: gets_the_def)
  apply (rule det_wp_pre)
   apply (wpsimp wp: det_wp_assert_opt)
  apply fastforce
  done

lemma gets_map_det_wp[wp]:
  "det_wp (\<lambda>s. \<exists>y. f s p = Some y) (gets_map f p)"
  unfolding gets_map_def
  by (wpsimp wp: det_wp_assert_opt)

lemma det_wp_def2:
  "det_wp P f = (\<forall>s. P s \<longrightarrow> (\<not> snd (f s)) \<and> (\<exists>r. r \<in> fst (f s) \<and> (\<forall>r'. r' \<in> fst (f s) \<longrightarrow> r' = r)))"
  apply (clarsimp simp: det_wp_def)
  apply (subst singleton_iff[symmetric])
  apply (intro iffI conjI impI allI)
    apply fastforce
   apply fastforce
  apply clarsimp
  apply (rename_tac s)
  apply (drule_tac x=s in spec)
  apply clarsimp
  apply (rename_tac r)
  apply (rule_tac x=r in exI)
  apply (rule sym)
  apply (subst split_pairs)
  apply fastforce
  done

lemma whileLoop_result_det_wp_intermediate:
  "\<lbrakk>det_wp P (B r); C r s; P s;
    (r', s') \<in> fst (B r s); (Some (r, s), Some (r'', s'')) \<in> whileLoop_results C B\<rbrakk>
   \<Longrightarrow> (Some (r', s'), Some (r'', s'')) \<in> whileLoop_results C B"
  apply (clarsimp simp: det_wp_def2)
  apply (erule whileLoop_results_cases_valid)
   apply fastforce
  apply blast
  done

lemma det_wp_whileLoop:
  assumes det: "\<And>r. det_wp (P r and C r) (B r)"
  assumes inv: " \<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
  assumes ef: "\<And>r. empty_fail (B r)"
  assumes termin: "\<And>r s. \<lbrakk>P r s; C r s\<rbrakk> \<Longrightarrow> whileLoop_terminates C B r s"
  shows "det_wp (P r) (whileLoop C B r)"
  apply (clarsimp simp: det_wp_def2)
  apply (intro context_conjI)
   apply (fastforce simp: no_fail_whileLoop[OF det[THEN det_wp_no_fail] termin inv])
  apply (insert empty_fail_whileLoop[where C=C and B=B and r=r, rotated] ef)
  apply clarsimp
  apply (frule (1) empty_failD3)
  apply (clarsimp simp: not_empty_eq)
  apply (rename_tac r' s')
  apply (rule_tac x=r' in exI)
  apply (rule_tac x=s' in exI)
  apply simp
  apply (intro allI)
  apply (rename_tac rv state)
  apply (rule_tac P="P r s" in imp_elim)
    apply (rule_tac I="\<lambda>r s r' s'. P r s \<longrightarrow> (rv, state) \<in> fst (whileLoop C B r s)
                                   \<longrightarrow> rv = r' \<and> state = s'"
                 in in_whileLoop_induct)
      apply fastforce
     apply (simp add: whileLoop_cond_fail return_def)
    apply clarsimp
    apply (elim impE)
      apply (fastforce elim: use_valid[where f="B _ "] intro: inv)
     apply (clarsimp simp: whileLoop_def)
     apply (rule whileLoop_result_det_wp_intermediate)
         apply (clarsimp simp: det_wp_def2)
         apply force+
       using det
       apply (fastforce simp: no_fail_def det_wp_def2)
      apply fastforce+
  done

end
