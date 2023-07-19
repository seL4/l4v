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


subsection \<open>Simplifying Monads\<close>

lemma fail_update[iff]:
  "fail (f s) = fail s"
  by (simp add: fail_def)

lemma assert_A_True[simp]:
  "assert True = return ()"
  by (simp add: assert_def)


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
  "liftM t f >>= g = (f >>= (\<lambda>x. g (t x)))"
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

end
