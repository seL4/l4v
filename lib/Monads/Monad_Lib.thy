(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* This theory collects the minimum constant definitions and lemmas for the monad definition
   theories (NonDetMonad, TraceMonad etc). Only things that are necessary for these and needed
   by more than one of them should go in here. *)

theory Monad_Lib
  imports Main
begin

(* This might have been better as an input abbreviation, but a lot of proofs break if we change it *)
definition
  fun_app :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 10) where
  "f $ x \<equiv> f x"

declare fun_app_def [iff]

lemma fun_app_cong[fundef_cong]:
  "\<lbrakk> f x = f' x' \<rbrakk> \<Longrightarrow> (f $ x) = (f' $ x')"
  by simp

lemma fun_app_apply_cong[fundef_cong]:
  "f x y = f' x' y' \<Longrightarrow> (f $ x) y = (f' $ x') y'"
  by simp

definition
 "swp f \<equiv> \<lambda>x y. f y x"

lemma swp_apply[simp]: "swp f y x = f x y"
  by (simp add: swp_def)

definition "K \<equiv> \<lambda>x y. x"

lemma K_apply[simp]:
  "K x y = x"
  by (simp add: K_def)

(* FIXME: eliminate *)
declare K_def [simp]

lemma o_const_simp[simp]:
  "(\<lambda>x. C) \<circ> f = (\<lambda>x. C)"
  by (simp add: o_def)

definition
  zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith f xs ys \<equiv> map (case_prod f) (zip xs ys)"

lemma zipWith_Nil[simp]:
  "zipWith f xs [] = []"
  unfolding zipWith_def by simp

lemma zipWith_nth:
  "\<lbrakk> n < min (length xs) (length ys) \<rbrakk> \<Longrightarrow> zipWith f xs ys ! n = f (xs ! n) (ys ! n)"
  unfolding zipWith_def by simp

lemma length_zipWith [simp]:
  "length (zipWith f xs ys) = min (length xs) (length ys)"
  unfolding zipWith_def by simp

lemmas None_upd_eq = fun_upd_idem[where y=None]

lemma sum_all_ex[simp]:
  "(\<forall>a. x \<noteq> Inl a) = (\<exists>a. x = Inr a)"
  "(\<forall>a. x \<noteq> Inr a) = (\<exists>a. x = Inl a)"
  by (metis Inr_not_Inl sum.exhaust)+

end