(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas about no_throw. Usually should have a conclusion "no_throw P m".
   Includes some monad equations that have no_throw as a main assumption.  *)

theory No_Throw
  imports
    WhileLoopRules
    MonadEq_Lemmas
begin

(* Alternative definition of no_throw; easier to work with than unfolding validE. *)
lemma no_throw_def':
  "no_throw P A = (\<forall>s. P s \<longrightarrow> (\<forall>(r, t) \<in> fst (A s). (\<exists>x. r = Inr x)))"
  by (clarsimp simp: no_throw_def validE_def2 split_def split: sum.splits)

lemma no_throw_returnOk [simp]:
  "no_throw P (returnOk a)"
  unfolding no_throw_def
  by wp

lemma no_throw_liftE [simp]:
  "no_throw P (liftE x)"
  by (wpsimp simp: liftE_def no_throw_def validE_def)

lemma no_throw_bindE:
  "\<lbrakk> no_throw A X; \<And>a. no_throw B (Y a); \<lbrace> A \<rbrace> X \<lbrace> \<lambda>_. B \<rbrace>,\<lbrace> \<lambda>_ _. True \<rbrace> \<rbrakk>
   \<Longrightarrow> no_throw A (X >>=E Y)"
  unfolding no_throw_def
  apply (rule seqE[rotated])
   apply force
  apply (rule hoare_validE_cases; simp)
  done

lemma no_throw_bindE_simple:
  "\<lbrakk> no_throw \<top> L; \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L >>=E R)"
  apply (erule no_throw_bindE)
   apply assumption
  apply wp
  done

lemma no_throw_handleE_simple:
  notes hoare_vcg_prop[wp del]
  shows "\<lbrakk> \<And>x. no_throw \<top> L \<or> no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle> R)"
  unfolding no_throw_def
  apply atomize
  apply clarsimp
  apply (erule disjE)
   apply (wpsimp wp: hoare_vcg_prop[where f="R x" for x])
    apply assumption
   apply simp
  apply (rule handleE_wp)
   apply (erule_tac x=x in allE)
   apply assumption
  apply wp
  done

lemma no_throw_handle2:
  "\<lbrakk> \<And>a. no_throw Y (B a); \<lbrace> X \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_. Y \<rbrace> \<rbrakk> \<Longrightarrow> no_throw X (A <handle2> B)"
  apply (clarsimp simp: no_throw_def' handleE'_def bind_def)
  apply (clarsimp simp: validE_def valid_def)
  apply (erule allE, erule (1) impE)
  apply (drule (1) bspec)
  apply (clarsimp simp: return_def split: sum.splits)
  apply force
  done

lemma no_throw_handle:
  "\<lbrakk> \<And>a. no_throw Y (B a); \<lbrace> X \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_. Y \<rbrace> \<rbrakk> \<Longrightarrow> no_throw X (A <handle> B)"
  unfolding handleE_def
  by (rule no_throw_handle2)

lemma no_throw_fail[simp]:
  "no_throw P fail"
  by (clarsimp simp: no_throw_def)

lemma bindE_fail_propagates:
  "\<lbrakk> no_throw \<top> A; empty_fail A \<rbrakk> \<Longrightarrow> A >>=E (\<lambda>_. fail) = fail"
  by (fastforce simp: no_throw_def validE_def valid_def bind_def empty_fail_def
                      bindE_def split_def fail_def NonDetMonad.lift_def throwError_def
                split: sum.splits)

lemma whileLoopE_nothrow:
  "\<lbrakk> \<And>x. no_throw \<top> (B x) \<rbrakk> \<Longrightarrow> no_throw \<top> (whileLoopE C B x)"
  unfolding no_throw_def
  apply (rule validE_whileLoopE [where I="\<lambda>_ _. True"])
    apply simp
   apply (rule validE_weaken; force)
  apply simp
  done

lemma handleE'_nothrow_lhs:
  "\<lbrakk> no_throw \<top> L \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle2> R)"
  unfolding no_throw_def
  apply (rule handleE'_wp[rotated])
   apply assumption
  apply simp
  done

lemma handleE'_nothrow_rhs:
  "\<lbrakk> \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle2> R)"
  unfolding no_throw_def
  apply (rule handleE'_wp)
   apply assumption
  apply (rule hoareE_TrueI)
  done

lemma handleE_nothrow_lhs:
  "no_throw \<top> L \<Longrightarrow> no_throw \<top> (L <handle> R)"
  by (metis handleE'_nothrow_lhs handleE_def)

lemma handleE_nothrow_rhs:
  "\<lbrakk> \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle> R)"
  by (metis no_throw_handleE_simple)

lemma condition_nothrow:
  "\<lbrakk> no_throw \<top> L; no_throw \<top> R \<rbrakk> \<Longrightarrow> no_throw \<top> (condition C L R)"
  by (clarsimp simp: condition_def no_throw_def validE_def2)

lemma no_throw_Inr:
  "\<lbrakk> x \<in> fst (A s); no_throw P A; P s \<rbrakk> \<Longrightarrow> \<exists>y. fst x = Inr y"
  by (fastforce simp: no_throw_def' split: sum.splits)

lemma no_throw_handleE':
  "no_throw \<top> A \<Longrightarrow> (A <handle2> B) = A"
  apply (rule monad_eqI)
    apply monad_eq
    apply (fastforce dest: no_throw_Inr)
   apply monad_eq
   apply (metis (lifting) fst_conv no_throw_Inr)
  apply monad_eq
  apply (fastforce dest: no_throw_Inr)
  done

lemma no_throw_handleE:
  "no_throw \<top> A \<Longrightarrow> (A <handle> B) = A"
  unfolding handleE_def
  by (auto simp: no_throw_handleE')

lemma bindE_handleE_join:
  "no_throw \<top> A \<Longrightarrow> (A >>=E (\<lambda>x. (B x) <handle> C)) = ((A >>=E B <handle> C))"
  apply (monad_eq simp: Bex_def Ball_def no_throw_def')
  apply blast
  done

end