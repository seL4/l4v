(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_In_Monad
  imports Trace_Lemmas
begin

section \<open>Reasoning directly about states\<close>

(* Lemmas about terms of the form "(v, s') \<in> mres (m s)" *)

lemma in_throwError:
  "((v, s') \<in> mres (throwError e s)) = (v = Inl e \<and> s' = s)"
  by (simp add: throwError_def return_def mres_def)

lemma in_returnOk:
  "((v', s') \<in> mres (returnOk v s)) = (v' = Inr v \<and> s' = s)"
  by (simp add: returnOk_def return_def mres_def)

lemma in_bind:
  "((r,s') \<in> mres ((do x \<leftarrow> f; g x od) s)) =
   (\<exists>s'' x. (x, s'') \<in> mres (f s) \<and> (r, s') \<in> mres (g x s''))"
  by (force simp: bind_def split_def mres_def split: tmres.splits)

lemma in_bindE_R:
  "((Inr r,s') \<in> mres ((doE x \<leftarrow> f; g x odE) s)) =
  (\<exists>s'' x. (Inr x, s'') \<in> mres (f s) \<and> (Inr r, s') \<in> mres (g x s''))"
  unfolding bindE_def lift_def split_def in_bind
  by (force simp: throwError_def return_def mres_def split: sum.splits)

lemma in_bindE_L:
  "((Inl r, s') \<in> mres ((doE x \<leftarrow> f; g x odE) s)) \<Longrightarrow>
   (\<exists>s'' x. (Inr x, s'') \<in> mres (f s) \<and> (Inl r, s') \<in> mres (g x s'')) \<or> ((Inl r, s') \<in> mres (f s))"
  by (simp add: bindE_def in_bind)
     (force simp: return_def throwError_def lift_def split_def mres_def split: sum.splits if_split_asm)

lemma in_return:
  "(r, s') \<in> mres (return v s) = (r = v \<and> s' = s)"
  by (simp add: return_def mres_def)

lemma in_liftE:
  "((v, s') \<in> mres (liftE f s)) = (\<exists>v'. v = Inr v' \<and> (v', s') \<in> mres (f s))"
  by (force simp: liftE_def in_bind in_return)

lemma in_whenE:
  "((v, s') \<in> mres (whenE P f s)) = ((P \<longrightarrow> (v, s') \<in> mres (f s)) \<and> (\<not>P \<longrightarrow> v = Inr () \<and> s' = s))"
  by (simp add: whenE_def in_returnOk)

lemma inl_whenE:
  "((Inl x, s') \<in> mres (whenE P f s)) = (P \<and> (Inl x, s') \<in> mres (f s))"
  by (auto simp add: in_whenE)

lemma inr_in_unlessE_throwError[termination_simp]:
  "(Inr (), s') \<in> mres (unlessE P (throwError E) s) = (P \<and> s'=s)"
  by (simp add: unlessE_def returnOk_def throwError_def in_return)

lemma in_fail:
  "r \<in> mres (fail s) = False"
  by (simp add: fail_def mres_def)

lemma in_assert:
  "(r, s') \<in> mres (assert P s) = (P \<and> s' = s)"
  by (simp add: assert_def return_def fail_def mres_def)

lemma in_assertE:
  "(r, s') \<in> mres (assertE P s) = (P \<and> r = Inr () \<and> s' = s)"
  by (simp add: assertE_def returnOk_def return_def fail_def mres_def)

lemma in_assert_opt:
  "(r, s') \<in> mres (assert_opt v s) = (v = Some r \<and> s' = s)"
  by (auto simp: assert_opt_def in_fail in_return split: option.splits)

lemma in_get:
  "(r, s') \<in> mres (get s) = (r = s \<and> s' = s)"
  by (simp add: get_def mres_def)

lemma in_gets:
  "(r, s') \<in> mres (gets f s) = (r = f s \<and> s' = s)"
  by (simp add: simpler_gets_def mres_def)

lemma in_put:
  "(r, s') \<in> mres (put x s) = (s' = x \<and> r = ())"
  by (simp add: put_def mres_def)

lemma in_when:
  "(v, s') \<in> mres (when P f s) = ((P \<longrightarrow> (v, s') \<in> mres (f s)) \<and> (\<not>P \<longrightarrow> v = () \<and> s' = s))"
  by (simp add: when_def in_return)

lemma in_unless:
  "(v, s') \<in> mres (unless P f s) = ((\<not> P \<longrightarrow> (v, s') \<in> mres (f s)) \<and> (P \<longrightarrow> v = () \<and> s' = s))"
  by (simp add: unless_def in_when)

lemma in_unlessE:
  "(v, s') \<in> mres (unlessE P f s) = ((\<not> P \<longrightarrow> (v, s') \<in> mres (f s)) \<and> (P \<longrightarrow> v = Inr () \<and> s' = s))"
  by (simp add: unlessE_def in_returnOk)

lemma inl_unlessE:
  "((Inl x, s') \<in> mres (unlessE P f s)) = (\<not> P \<and> (Inl x, s') \<in> mres (f s))"
  by (auto simp add: in_unlessE)

lemma in_modify:
  "(v, s') \<in> mres (modify f s) = (s'=f s \<and> v = ())"
  by (auto simp add: modify_def bind_def get_def put_def mres_def)

lemma gets_the_in_monad:
  "((v, s') \<in> mres (gets_the f s)) = (s' = s \<and> f s = Some v)"
  by (auto simp: gets_the_def in_bind in_gets in_assert_opt split: option.split)

lemma in_alternative:
  "(r,s') \<in> mres ((f \<sqinter> g) s) = ((r,s') \<in> mres (f s) \<or> (r,s') \<in> mres (g s))"
  by (auto simp add: alternative_def mres_def)

lemma in_liftM:
  "((r, s') \<in> mres (liftM t f s)) = (\<exists>r'. (r', s') \<in> mres (f s) \<and> r = t r')"
  by (simp add: liftM_def in_return in_bind)

lemma in_bindE:
  "(rv, s') \<in> mres ((f >>=E (\<lambda>rv'. g rv')) s) =
   ((\<exists>ex. rv = Inl ex \<and> (Inl ex, s') \<in> mres (f s)) \<or>
    (\<exists>rv' s''. (rv, s') \<in> mres (g rv' s'') \<and> (Inr rv', s'') \<in> mres (f s)))"
  apply (clarsimp simp: bindE_def in_bind lift_def in_throwError)
  apply (safe del: disjCI; strengthen subst[where P="\<lambda>x. x \<in> mres (f s)", mk_strg I _ E];
         auto simp: in_throwError split: sum.splits)
  done

lemmas in_monad = inl_whenE in_whenE in_liftE in_bind in_bindE_L
                  in_bindE_R in_returnOk in_throwError in_fail
                  in_assertE in_assert in_return in_assert_opt
                  in_get in_gets in_put in_when inl_unlessE in_unlessE
                  in_unless in_modify gets_the_in_monad
                  in_alternative in_liftM

lemma bind_det_exec:
  "mres (a s) = {(r,s')} \<Longrightarrow> mres ((a >>= b) s) = mres (b r s')"
  by (simp add: in_bind set_eq_iff)

lemma in_bind_det_exec:
  "mres (a s) = {(r,s')} \<Longrightarrow> (s'' \<in> mres ((a >>= b) s)) = (s'' \<in> mres (b r s'))"
  by (cases s'', simp add: in_bind)

lemma exec_put:
  "(put s' >>= m) s = m () s'"
  by (simp add: bind_def put_def mres_def split_def)

lemma bind_execI:
  "\<lbrakk> (r'',s'') \<in> mres (f s); \<exists>x \<in> mres (g r'' s''). P x \<rbrakk> \<Longrightarrow> \<exists>x \<in> mres ((f >>= g) s). P x"
  by (force simp: Bex_def in_bind)

end
