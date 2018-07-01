(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

lemma det_wp_pre:
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

end
