(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* The oblivious predicate and supporting lemmas.

   "oblivious f m" expresses that execution of the monad m is oblivious to the effects of the
   function f on the state *)

theory Oblivious
  imports
    Monads.In_Monad
    Monads.NonDetMonadVCG
begin


definition
  oblivious :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) nondet_monad \<Rightarrow> bool" where
 "oblivious f m \<equiv> \<forall>s. (\<forall>(rv, s') \<in> fst (m s). (rv, f s') \<in> fst (m (f s)))
                    \<and> (\<forall>(rv, s') \<in> fst (m (f s)). \<exists>s''. (rv, s'') \<in> fst (m s) \<and> s' = f s'')
                    \<and> snd (m (f s)) = snd (m s)"


lemma oblivious_return[simp]:
  "oblivious f (return x)"
  by (simp add: oblivious_def return_def)

lemma oblivious_fail[simp]:
  "oblivious f fail"
  by (simp add: oblivious_def fail_def)

lemma oblivious_assert[simp]:
  "oblivious f (assert x)"
  by (simp add: assert_def)

lemma oblivious_assert_opt[simp]:
  "oblivious f (assert_opt fn)"
  by (simp add: assert_opt_def split: option.splits)

lemma oblivious_bind:
  "\<lbrakk> oblivious f m; \<And>rv. oblivious f (m' rv) \<rbrakk> \<Longrightarrow> oblivious f (m >>= m')"
  apply (simp add: oblivious_def)
  apply (rule allI)
  apply (erule allE)
  apply (intro conjI)
    apply (drule conjunct1)
    apply (clarsimp simp: in_monad)
    apply fastforce
   apply (drule conjunct2, drule conjunct1)
   apply (clarsimp simp: in_monad)
   apply fastforce
  apply (clarsimp simp: bind_def disj_commute)
  apply (rule disj_cong [OF refl])
  apply (rule iffI)
   apply (clarsimp simp: split_def)
   apply fastforce
  apply clarsimp
  apply (drule(1) bspec)
  apply (clarsimp simp: split_def)
  apply (drule (1) bspec)
  apply (rule bexI [rotated], assumption)
  apply clarsimp
  done

lemma oblivious_gets[simp]:
  "oblivious f (gets f') = (\<forall>s. f' (f s) = f' s)"
  by (fastforce simp add: oblivious_def simpler_gets_def)

lemma oblivious_liftM:
  "oblivious f m \<Longrightarrow> oblivious f (liftM g m)"
  by (simp add: liftM_def oblivious_bind)

lemma oblivious_modify[simp]:
  "oblivious f (modify f') = (\<forall>s. f' (f s) = f (f' s))"
  apply (simp add: oblivious_def simpler_modify_def)
  apply (rule ball_cong[where A=UNIV, OF refl, simplified])
  apply fastforce
  done

lemma oblivious_modify_swap:
  "oblivious f m \<Longrightarrow> (modify f >>= (\<lambda>rv. m)) = (m >>= (\<lambda>rv. modify f))"
  apply (clarsimp simp: bind_def simpler_modify_def)
  apply (rule ext)+
  apply (case_tac "m (f s)", clarsimp)
  apply (simp add: oblivious_def)
  apply (drule_tac x=s in spec)
  apply (rule conjI)
   apply (rule set_eqI)
   apply (rule iffI)
    apply (drule conjunct2, drule conjunct1)
    apply (drule_tac x=x in bspec, simp)
    apply clarsimp
    apply (rule_tac x="((), s'')" in bexI)
     apply simp
    apply simp
   apply (drule conjunct1)
   apply fastforce
  apply (drule conjunct2)+
  apply fastforce
  done

lemma oblivious_returnOk[simp]:
  "oblivious f (returnOk e)"
  by (simp add: returnOk_def)

lemma oblivious_assertE[simp]:
  "oblivious f (assertE P)"
  by (simp add: assertE_def split: if_split)

lemma oblivious_throwError[simp]:
  "oblivious f (throwError e)"
  by (simp add: throwError_def)

lemma oblivious_bindE:
  "\<lbrakk> oblivious u f; \<And>v. oblivious u (g v) \<rbrakk> \<Longrightarrow> oblivious u (f >>=E (\<lambda>v. g v))"
  apply (simp add: bindE_def)
  apply (erule oblivious_bind)
  apply (simp add: lift_def split: sum.split)
  done

lemma oblivious_catch:
  "\<lbrakk> oblivious u f; \<And>v. oblivious u (g v) \<rbrakk> \<Longrightarrow> oblivious u (catch f g)"
  apply (simp add: catch_def)
  apply (erule oblivious_bind)
  apply (simp split: sum.split)
  done

lemma oblivious_when[simp]:
  "oblivious f (when P m) = (P \<longrightarrow> oblivious f m)"
  by (simp add: when_def split: if_split)

lemma oblivious_whenE[simp]:
  "oblivious f (whenE P g) = (P \<longrightarrow> oblivious f g)"
  by (simp add: whenE_def split: if_split)

lemma select_f_oblivious[simp]:
  "oblivious f (select_f v)"
  by (simp add: oblivious_def select_f_def)

lemma oblivious_select:
  "oblivious f (select S)"
  by (simp add: oblivious_def select_def)

end