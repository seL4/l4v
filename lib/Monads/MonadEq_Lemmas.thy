(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas that support the monad_eq method. Either things that go into the[monad_eq] set
   or that are needed for such lemmas. Usually about "snd (f s)" or "x \<in> fst (f s)" where f
   is a nondet monad.

   If you are planning to use the monad_eq method, this is the theory you should import.

   See MonadEq.thy for definition and description of the method. *)

theory MonadEq_Lemmas
  imports MonadEq
begin

lemma snd_return[monad_eq]:
  "\<not> snd (return a b)"
  unfolding return_def by simp

lemma snd_throwError[monad_eq]:
  "\<not> snd (throwError e s)"
  unfolding throwError_def by (simp add: snd_return)

lemma snd_lift_Inr[monad_eq]:
  "snd (lift b (Inr r) t) = snd (b r t)"
  unfolding lift_def by simp

lemma snd_lift_Inl[monad_eq]:
  "\<not> snd (lift b (Inl r) t)"
  unfolding lift_def by (simp add: snd_throwError)

lemma snd_fail[monad_eq]:
  "snd (fail s)"
  by (clarsimp simp: fail_def)

lemma not_snd_bindD:
  "\<lbrakk> \<not> snd ((a >>= b) s); (rv, s') \<in> fst (a s) \<rbrakk> \<Longrightarrow> \<not> snd (a s) \<and> \<not> snd (b rv s')"
  by (fastforce simp: bind_def)

lemma not_snd_bindI1:
  "\<not> snd ((a >>= b) s) \<Longrightarrow> \<not> snd (a s)"
  by (fastforce simp: bind_def)

lemma not_snd_bindI2:
  "\<lbrakk> \<not> snd ((a >>= b) s); (rv, s') \<in> fst (a s) \<rbrakk> \<Longrightarrow> \<not> snd (b rv s')"
  by (fastforce simp: bind_def)

lemma in_returns[monad_eq]:
  "(r, s) \<in> fst (return r s)"
  "(Inr r, s) \<in> fst (returnOk r s)"
  by (simp add: in_monad)+

lemma fst_return:
  "fst (return v s) = {(v, s)}"
  by (simp add: return_def)

lemma in_bind_split[monad_eq]:
  "(rv \<in> fst ((f >>= g) s)) =
  (\<exists>rv'. rv' \<in> fst (f s) \<and> rv \<in> fst (g (fst rv') (snd rv')))"
  apply (cases rv)
  apply (fastforce simp add: in_bind)
  done

lemma Inr_in_liftE_simp[monad_eq]:
  "((Inr rv, x) \<in> fst (liftE fn s)) = ((rv, x) \<in> fst (fn s))"
  by (simp add: in_monad)

lemma gets_the_member:
  "(x, s') \<in> fst (gets_the f s) = (f s = Some x \<and> s' = s)"
  by (case_tac "f s", simp_all add: gets_the_def
            simpler_gets_def bind_def in_assert_opt)

lemma fst_throwError_returnOk:
  "fst (throwError e s) = {(Inl e, s)}"
  "fst (returnOk v s) = {(Inr v, s)}"
  by (simp add: throwError_def returnOk_def return_def)+

lemma not_snd_bindE_I1:
  "\<not> snd ((a >>=E b) s) \<Longrightarrow> \<not> snd (a s)"
  unfolding bindE_def
  by (erule not_snd_bindI1)

lemma snd_assert[monad_eq]:
  "snd (assert P s) = (\<not> P)"
  by (clarsimp simp: fail_def return_def assert_def)

lemma not_snd_assert :
  "(\<not> snd (assert P s)) = P"
  by (metis snd_assert)

lemma snd_assert_opt[monad_eq]:
  "snd (assert_opt f s) = (f = None)"
  by (monad_eq simp: assert_opt_def split: option.splits)

declare in_assert_opt[monad_eq]

lemma not_snd_bindD':
  "\<lbrakk>\<not> snd ((a >>= b) s); \<not> snd (a s) \<Longrightarrow> (rv, s') \<in> fst (a s)\<rbrakk> \<Longrightarrow> \<not> snd (a s) \<and> \<not> snd (b rv s')"
  apply (frule not_snd_bindI1)
  apply (erule not_snd_bindD)
  apply simp
  done

lemma snd_bind[monad_eq]:
  "snd ((a >>= b) s) = (snd (a s) \<or> (\<exists>r s'. (r, s') \<in> fst (a s) \<and> snd (b r s')))"
  apply (clarsimp simp add: bind_def Bex_def image_def)
  apply (subst surjective_pairing, subst prod.inject, force)
  done

lemma in_lift[monad_eq]:
  "(rv, s') \<in> fst (lift M v s) =
    (case v of Inl x \<Rightarrow> rv = Inl x \<and> s' = s
             | Inr x \<Rightarrow> (rv, s') \<in> fst (M x s))"
  apply (clarsimp simp: lift_def throwError_def return_def split: sum.splits)
  done

lemma snd_lift[monad_eq]:
  "snd (lift M a b) = (\<exists>x. a = Inr x \<and> snd (M x b))"
  apply (clarsimp simp: lift_def throwError_def return_def split: sum.splits)
  done

lemma snd_bindE[monad_eq]:
  "snd ((a >>=E b) s) = (snd (a s) \<or> (\<exists>r s'. (r, s') \<in> fst (a s) \<and> (\<exists>a. r = Inr a \<and> snd (b a s'))))"
  apply (clarsimp simp: bindE_def)
  apply monad_eq
  done

lemma snd_get[monad_eq]:
  "snd (get s) = False"
  by (simp add: get_def)

lemma snd_gets[monad_eq]:
  "snd (gets f s) = False"
  by (simp add: gets_def snd_bind snd_get snd_return)

lemma in_handleE'[monad_eq]:
  "((rv, s') \<in> fst ((f <handle2> g) s)) =
    ((\<exists>ex. rv = Inr ex \<and> (Inr ex, s') \<in> fst (f s)) \<or>
     (\<exists>rv' s''. (rv, s') \<in> fst (g rv' s'') \<and> (Inl rv', s'') \<in> fst (f s)))"
  apply (clarsimp simp: handleE'_def)
  apply (rule iffI)
   apply (subst (asm) in_bind_split)
   apply (clarsimp simp: return_def split: sum.splits)
   apply (case_tac a)
    apply (erule allE, erule (1) impE)
    apply clarsimp
   apply (erule allE, erule (1) impE)
   apply clarsimp
  apply (subst in_bind_split)
  apply (clarsimp simp: return_def split: sum.splits)
  apply blast
  done

lemma in_handleE[monad_eq]:
  "(a, b) \<in> fst ((A <handle> B) s) =
    ((\<exists>x. a = Inr x \<and> (Inr x, b) \<in> fst (A s)) \<or>
     (\<exists>r t. (Inl r, t) \<in> fst (A s) \<and> (a, b) \<in> fst (B r t)))"
  apply (unfold handleE_def)
  apply (monad_eq split: sum.splits)
  apply blast
  done

lemma snd_handleE'[monad_eq]:
  "snd ((A <handle2> B) s) = (snd (A s) \<or> (\<exists>r s'. (r, s')\<in>fst (A s) \<and> (\<exists>a. r = Inl a \<and> snd (B a s'))))"
  apply (clarsimp simp: handleE'_def)
  apply (monad_eq simp: Bex_def split: sum.splits)
  apply (metis sum.sel(1) sum.distinct(1) sumE)
  done

lemma snd_handleE[monad_eq]:
  "snd ((A <handle> B) s) = (snd (A s) \<or> (\<exists>r s'. (r, s')\<in>fst (A s) \<and> (\<exists>a. r = Inl a \<and> snd (B a s'))))"
  apply (unfold handleE_def)
  apply (rule snd_handleE')
  done

declare in_liftE[monad_eq]

lemma snd_liftE[monad_eq]:
  "snd ((liftE x) s) = snd (x s)"
  by (clarsimp simp: liftE_def snd_bind snd_return)

lemma snd_returnOk[monad_eq]:
  "\<not> snd (returnOk x s)"
  by (clarsimp simp: returnOk_def return_def)

lemma snd_when[monad_eq]:
  "snd (when P M s) = (P \<and> snd (M s))"
  by (clarsimp simp: when_def return_def)

lemma in_condition[monad_eq]:
  "((a, b) \<in> fst (condition C L R s)) = ((C s \<longrightarrow> (a, b) \<in> fst (L s)) \<and> (\<not> C s \<longrightarrow> (a, b) \<in> fst (R s)))"
  by (rule condition_split)

lemma snd_condition[monad_eq]:
  "(snd (condition C L R s)) = ((C s \<longrightarrow> snd (L s)) \<and> (\<not> C s \<longrightarrow> snd (R s)))"
  by (rule condition_split)

lemma empty_fail_spec [simp]: "empty_fail (state_select F)"
  by (clarsimp simp: state_select_def empty_fail_def)

declare snd_fail [simp]

declare snd_returnOk [simp, monad_eq]

lemma in_catch[monad_eq]:
  "(r, t) \<in> fst ((M <catch> E) s)
       = ((Inr r, t) \<in> fst (M s)
             \<or> (\<exists>r' s'. ((Inl r', s') \<in> fst (M s)) \<and> (r, t) \<in> fst (E r' s')))"
  apply (rule iffI)
   apply (clarsimp simp: catch_def in_bind in_return split: sum.splits)
   apply (metis sumE)
  apply (clarsimp simp: catch_def in_bind in_return split: sum.splits)
  apply (metis sum.sel(1) sum.distinct(1) sum.inject(2))
  done

lemma snd_catch[monad_eq]:
  "snd ((M <catch> E) s)
       = (snd (M s)
             \<or> (\<exists>r' s'. ((Inl r', s') \<in> fst (M s)) \<and> snd (E r' s')))"
  apply (rule iffI)
   apply (clarsimp simp: catch_def snd_bind snd_return split: sum.splits)
  apply (clarsimp simp: catch_def snd_bind snd_return split: sum.splits)
  apply force
  done

declare in_get[monad_eq]

lemma returnOk_cong: "\<lbrakk> \<And>s. B a s = B' a s \<rbrakk> \<Longrightarrow> ((returnOk a) >>=E B) = ((returnOk a) >>=E B')"
  by monad_eq

lemma in_state_assert [monad_eq, simp]:
  "(rv, s') \<in> fst (state_assert P s) = (rv = () \<and> s' = s \<and> P s)"
  apply (monad_eq simp: state_assert_def)
  apply metis
  done

lemma snd_state_assert[monad_eq]:
  "snd (state_assert P s) = (\<not> P s)"
  by (monad_eq simp: state_assert_def Bex_def)

lemma in_select[monad_eq]:
  "(rv, s') \<in> fst (select S s) = (s' = s \<and> rv \<in> S)"
  by (fastforce simp: select_def)

lemma snd_select[monad_eq]:
  "\<not> snd (select S s)"
  by (clarsimp simp: select_def)

lemma snd_put[monad_eq]:
  "\<not> snd (put t s)"
  by (clarsimp simp: put_def)

lemma snd_modify[monad_eq]:
  "\<not> snd (modify t s)"
  by (clarsimp simp: modify_def put_def get_def bind_def)

lemma snd_gets_the[monad_eq]:
  "snd (gets_the X s) = (X s = None)"
  by (monad_eq simp: gets_the_def gets_def get_def)

end
