(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory In_Monad
  imports NonDetMonadLemmas
begin

section \<open>Reasoning directly about states\<close>

(* Lemmas about terms of the form "(v, s') \<in> fst (m s)" *)

lemma in_throwError:
  "((v, s') \<in> fst (throwError e s)) = (v = Inl e \<and> s' = s)"
  by (simp add: throwError_def return_def)

lemma in_returnOk:
  "((v', s') \<in> fst (returnOk v s)) = (v' = Inr v \<and> s' = s)"
  by (simp add: returnOk_def return_def)

lemma in_bind:
  "((r,s') \<in> fst ((do x \<leftarrow> f; g x od) s)) =
   (\<exists>s'' x. (x, s'') \<in> fst (f s) \<and> (r, s') \<in> fst (g x s''))"
  by (force simp: bind_def split_def)

lemma in_bindE_R:
  "((Inr r,s') \<in> fst ((doE x \<leftarrow> f; g x odE) s)) =
  (\<exists>s'' x. (Inr x, s'') \<in> fst (f s) \<and> (Inr r, s') \<in> fst (g x s''))"
  unfolding bindE_def lift_def split_def bind_def
  by (force simp: throwError_def return_def split: sum.splits)

lemma in_bindE_L:
  "((Inl r, s') \<in> fst ((doE x \<leftarrow> f; g x odE) s)) \<Longrightarrow>
   (\<exists>s'' x. (Inr x, s'') \<in> fst (f s) \<and> (Inl r, s') \<in> fst (g x s'')) \<or> ((Inl r, s') \<in> fst (f s))"
  by (simp add: bindE_def bind_def)
     (force simp: return_def throwError_def lift_def split_def split: sum.splits if_split_asm)

lemma in_liftE:
  "((v, s') \<in> fst (liftE f s)) = (\<exists>v'. v = Inr v' \<and> (v', s') \<in> fst (f s))"
  by (force simp add: liftE_def bind_def return_def split_def)

lemma in_whenE:
  "((v, s') \<in> fst (whenE P f s)) = ((P \<longrightarrow> (v, s') \<in> fst (f s)) \<and> (\<not>P \<longrightarrow> v = Inr () \<and> s' = s))"
  by (simp add: whenE_def in_returnOk)

lemma inl_whenE:
  "((Inl x, s') \<in> fst (whenE P f s)) = (P \<and> (Inl x, s') \<in> fst (f s))"
  by (auto simp add: in_whenE)

lemma inr_in_unlessE_throwError[termination_simp]:
  "(Inr (), s') \<in> fst (unlessE P (throwError E) s) = (P \<and> s'=s)"
  by (simp add: unlessE_def returnOk_def throwError_def return_def)

lemma in_fail:
  "r \<in> fst (fail s) = False"
  by (simp add: fail_def)

lemma in_return:
  "(r, s') \<in> fst (return v s) = (r = v \<and> s' = s)"
  by (simp add: return_def)

lemma in_assert:
  "(r, s') \<in> fst (assert P s) = (P \<and> s' = s)"
  by (simp add: assert_def return_def fail_def)

lemma in_assertE:
  "(r, s') \<in> fst (assertE P s) = (P \<and> r = Inr () \<and> s' = s)"
  by (simp add: assertE_def returnOk_def return_def fail_def)

lemma in_assert_opt:
  "(r, s') \<in> fst (assert_opt v s) = (v = Some r \<and> s' = s)"
  by (auto simp: assert_opt_def in_fail in_return split: option.splits)

lemma in_get:
  "(r, s') \<in> fst (get s) = (r = s \<and> s' = s)"
  by (simp add: get_def)

lemma in_gets:
  "(r, s') \<in> fst (gets f s) = (r = f s \<and> s' = s)"
  by (simp add: simpler_gets_def)

lemma in_put:
  "(r, s') \<in> fst (put x s) = (s' = x \<and> r = ())"
  by (simp add: put_def)

lemma in_when:
  "(v, s') \<in> fst (when P f s) = ((P \<longrightarrow> (v, s') \<in> fst (f s)) \<and> (\<not>P \<longrightarrow> v = () \<and> s' = s))"
  by (simp add: when_def in_return)

lemma in_modify:
  "(v, s') \<in> fst (modify f s) = (s'=f s \<and> v = ())"
  by (simp add: modify_def bind_def get_def put_def)

lemma gets_the_in_monad:
  "((v, s') \<in> fst (gets_the f s)) = (s' = s \<and> f s = Some v)"
  by (auto simp: gets_the_def in_bind in_gets in_assert_opt split: option.split)

lemma in_alternative:
  "(r,s') \<in> fst ((f \<sqinter> g) s) = ((r,s') \<in> fst (f s) \<or> (r,s') \<in> fst (g s))"
  by (simp add: alternative_def)

lemma in_liftM:
  "((r, s') \<in> fst (liftM t f s)) = (\<exists>r'. (r', s') \<in> fst (f s) \<and> r = t r')"
  by (simp add: liftM_def return_def bind_def Bex_def)

lemmas handy_liftM_lemma = in_liftM (* FIXME lib: eliminate *)

lemma in_bindE:
  "(rv, s') \<in> fst ((f >>=E (\<lambda>rv'. g rv')) s) =
   ((\<exists>ex. rv = Inl ex \<and> (Inl ex, s') \<in> fst (f s)) \<or>
    (\<exists>rv' s''. (rv, s') \<in> fst (g rv' s'') \<and> (Inr rv', s'') \<in> fst (f s)))"
  by (force simp: bindE_def bind_def lift_def throwError_def return_def  split: sum.splits)

(* FIXME lib: remove unlessE_whenE + unless_when here and replace with in_unless lemmas *)
lemmas in_monad = inl_whenE in_whenE in_liftE in_bind in_bindE_L
                  in_bindE_R in_returnOk in_throwError in_fail
                  in_assertE in_assert in_return in_assert_opt
                  in_get in_gets in_put in_when unlessE_whenE
                  unless_when in_modify gets_the_in_monad
                  in_alternative in_liftM

lemma bind_det_exec:
  "fst (a s) = {(r,s')} \<Longrightarrow> fst ((a >>= b) s) = fst (b r s')"
  by (simp add: bind_def)

lemma in_bind_det_exec:
  "fst (a s) = {(r,s')} \<Longrightarrow> (s'' \<in> fst ((a >>= b) s)) = (s'' \<in> fst (b r s'))"
  by (simp add: bind_def)

lemma exec_put:
  "(put s' >>= m) s = m () s'"
  by (simp add: bind_def put_def)

lemma bind_execI:
  "\<lbrakk> (r'',s'') \<in> fst (f s); \<exists>x \<in> fst (g r'' s''). P x \<rbrakk> \<Longrightarrow> \<exists>x \<in> fst ((f >>= g) s). P x"
  by (force simp: in_bind split_def bind_def)

end
