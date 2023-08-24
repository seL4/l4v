(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Lemmas
  imports Trace_Monad
begin

section \<open>General Lemmas Regarding the Interference Trace Monad\<close>

subsection \<open>Congruence Rules for the Function Package\<close>

\<comment> \<open>FIXME: where should this go\<close>
lemma in_mres:
  "(tr, Result (rv, s)) \<in> S \<Longrightarrow> (rv, s) \<in> mres S"
  by (fastforce simp: mres_def intro: image_eqI[rotated])

lemma bind_apply_cong':
  "\<lbrakk>f s = f' s'; (\<forall>rv st. (rv, st) \<in> mres (f s) \<longrightarrow> g rv st = g' rv st)\<rbrakk>
   \<Longrightarrow> bind f g s = bind f' g' s'"
  apply (simp add: bind_def)
  apply (rule SUP_cong; simp?)
  apply (clarsimp split: tmres.split)
  apply (drule spec2, drule mp, erule in_mres)
  apply simp
  done

lemmas bind_apply_cong = bind_apply_cong'[rule_format, fundef_cong]

lemma bind_cong[fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s s'. (v, s') \<in> fst (f' s) \<Longrightarrow> g v s' = g' v s' \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  by (auto simp: bind_def Let_def split_def intro: rev_image_eqI)

lemma bindE_cong[fundef_cong]:
  "\<lbrakk> M = M' ; \<And>v s s'. (Inr v, s') \<in> fst (M' s) \<Longrightarrow> N v s' = N' v s' \<rbrakk> \<Longrightarrow> bindE M N = bindE M' N'"
  by (auto simp: bindE_def lift_def split: sum.splits intro!: bind_cong)

lemma bindE_apply_cong[fundef_cong]:
  "\<lbrakk> f s = f' s'; \<And>rv st. (Inr rv, st) \<in> fst (f' s') \<Longrightarrow> g rv st = g' rv st \<rbrakk>
  \<Longrightarrow> (f >>=E g) s = (f' >>=E g') s'"
  by (auto simp: bindE_def lift_def split: sum.splits intro!: bind_apply_cong)

lemma K_bind_apply_cong[fundef_cong]:
  "\<lbrakk> f st = f' st' \<rbrakk> \<Longrightarrow> K_bind f arg st = K_bind f' arg' st'"
  by simp

lemma when_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> when C m s = when C' m' s'"
  by (simp add: when_def)

lemma unless_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unless C m s = unless C' m' s'"
  by (simp add: when_def unless_def)

lemma whenE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> whenE C m s = whenE C' m' s'"
  by (simp add: whenE_def)

lemma unlessE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unlessE C m s = unlessE C' m' s'"
  by (simp add: unlessE_def)

subsection \<open>Simplifying Monads\<close>

lemma nested_bind[simp]:
  "do x <- do y <- f; return (g y) od; h x od = do y <- f; h (g y) od"
  by (clarsimp simp: bind_def Let_def split_def return_def)

lemma bind_dummy_ret_val:
  "do y \<leftarrow> a; b od = do a; b od"
  by simp

lemma fail_update[iff]:
  "fail (f s) = fail s"
  by (simp add: fail_def)

lemma fail_bind[simp]:
  "fail >>= f = fail"
  by (simp add: bind_def fail_def)

lemma fail_bindE[simp]:
  "fail >>=E f = fail"
  by (simp add: bindE_def bind_def fail_def)

lemma assert_A_False[simp]:
  "assert False = fail"
  by (simp add: assert_def)

lemma assert_A_True[simp]:
  "assert True = return ()"
  by (simp add: assert_def)

lemma assert_False[simp]:
  "assert False >>= f = fail"
  by simp

lemma assert_True[simp]:
  "assert True >>= f = f ()"
  by simp

lemma assertE_False[simp]:
  "assertE False >>=E f = fail"
  by (simp add: assertE_def)

lemma assertE_True[simp]:
  "assertE True >>=E f = f ()"
  by (simp add: assertE_def)

lemma when_False_bind[simp]:
  "when False g >>= f = f ()"
  by (rule ext) (simp add: when_def bind_def return_def)

lemma when_True_bind[simp]:
  "when True g >>= f = g >>= f"
  by (simp add: when_def bind_def return_def)

lemma whenE_False_bind[simp]:
  "whenE False g >>=E f = f ()"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma whenE_True_bind[simp]:
  "whenE True g >>=E f = g >>=E f"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma when_True[simp]:
  "when True X = X"
  by (clarsimp simp: when_def)

lemma when_False[simp]:
  "when False X = return ()"
  by (clarsimp simp: when_def)

lemma unless_False[simp]:
  "unless False X = X"
  by (clarsimp simp: unless_def)

lemma unlessE_False[simp]:
  "unlessE False f = f"
  unfolding unlessE_def by fastforce

lemma unless_True[simp]:
  "unless True X = return ()"
  by (clarsimp simp: unless_def)

lemma unlessE_True[simp]:
  "unlessE True f = returnOk ()"
  unfolding unlessE_def by fastforce

lemma unlessE_whenE:
  "unlessE P = whenE (\<not>P)"
  by (rule ext) (simp add: unlessE_def whenE_def)

lemma unless_when:
  "unless P = when (\<not>P)"
  by (rule ext) (simp add: unless_def when_def)

lemma gets_to_return[simp]:
  "gets (\<lambda>s. v) = return v"
  by (clarsimp simp: gets_def put_def get_def bind_def return_def)

lemma assert_opt_Some:
  "assert_opt (Some x) = return x"
  by (simp add: assert_opt_def)

lemma assertE_liftE:
  "assertE P = liftE (assert P)"
  by (simp add: assertE_def assert_def liftE_def returnOk_def)

lemma liftE_handleE'[simp]:
  "(liftE a <handle2> b) = liftE a"
  by (clarsimp simp: liftE_def handleE'_def)

lemma liftE_handleE[simp]:
  "(liftE a <handle> b) = liftE a"
  unfolding handleE_def by simp

lemma alternative_bind:
  "((a \<sqinter> b) >>= c) = ((a >>= c) \<sqinter> (b >>= c))"
  by (fastforce simp add: alternative_def bind_def split_def)

lemma alternative_refl:
  "(a \<sqinter> a) = a"
  by (simp add: alternative_def)

lemma alternative_com:
  "(f \<sqinter> g) = (g \<sqinter> f)"
  by (auto simp: alternative_def)

lemma liftE_alternative:
  "liftE (a \<sqinter> b) = (liftE a \<sqinter> liftE b)"
  by (simp add: liftE_def alternative_bind)


subsection \<open>Lifting and Alternative Basic Definitions\<close>

lemma liftE_liftM:
  "liftE = liftM Inr"
  by (auto simp: liftE_def liftM_def)

lemma liftME_liftM:
  "liftME f = liftM (case_sum Inl (Inr \<circ> f))"
  unfolding liftME_def liftM_def bindE_def returnOk_def lift_def
  apply (rule ext, rename_tac x)
  apply (rule_tac f="bind x" in arg_cong)
  apply (fastforce simp: throwError_def split: sum.splits)
  done

lemma liftE_bindE:
  "liftE a >>=E b = a >>= b"
  by (simp add: liftE_def bindE_def lift_def bind_assoc)

lemma liftM_id[simp]:
  "liftM id = id"
  by (auto simp: liftM_def)

lemma liftM_bind:
  "liftM t f >>= g = f >>= (\<lambda>x. g (t x))"
  by (simp add: liftM_def bind_assoc)

lemma gets_bind_ign:
  "gets f >>= (\<lambda>x. m) = m"
  by (simp add: bind_def simpler_gets_def)

lemma exec_get:
  "(get >>= f) x = f x x"
  by (simp add: get_def bind_def)

lemmas get_bind_apply = exec_get (* FIXME lib: eliminate *)

lemma exec_gets:
  "(gets f >>= m) s = m (f s) s"
  by (simp add: simpler_gets_def bind_def)

lemma bind_eqI:
  "\<lbrakk> f = f'; \<And>x. g x = g' x \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  by (auto simp: bind_def split_def)

lemma condition_split:
  "P (condition C a b s) \<longleftrightarrow> (C s \<longrightarrow> P (a s)) \<and> (\<not>C s \<longrightarrow> P (b s))"
  by (clarsimp simp: condition_def)

lemma condition_split_asm:
  "P (condition C a b s) \<longleftrightarrow> (\<not>(C s \<and> \<not> P (a s) \<or> \<not>C s \<and> \<not>P (b s)))"
  by (clarsimp simp: condition_def)

lemmas condition_splits = condition_split condition_split_asm

lemma condition_true_triv[simp]:
  "condition (\<lambda>_. True) A B = A"
  by (fastforce split: condition_splits)

lemma condition_false_triv[simp]:
  "condition (\<lambda>_. False) A B = B"
  by (fastforce split: condition_splits)

lemma condition_true:
  "P s \<Longrightarrow> condition P A B s = A s"
  by (clarsimp simp: condition_def)

lemma condition_false:
  "\<not> P s \<Longrightarrow> condition P A B s = B s"
  by (clarsimp simp: condition_def)

lemmas arg_cong_bind = arg_cong2[where f=bind]
lemmas arg_cong_bind1 = arg_cong_bind[OF refl ext]

end
