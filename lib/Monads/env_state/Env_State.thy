(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Env_State
  imports Main
begin

section "The Environment State"

record 'c monad_state_record =
  env :: 'c

type_synonym ('c, 's) monad_state = "('c, 's) monad_state_record_scheme"

type_synonym ('c, 's) mpred = "('c, 's) monad_state \<Rightarrow> bool"

abbreviation monad_state :: "'c \<Rightarrow> 's \<Rightarrow> ('c, 's) monad_state" where
  "monad_state c \<equiv> \<lambda>s. \<lparr> env = c, \<dots> = s \<rparr>"

abbreviation mstate :: "('c, 's) monad_state \<Rightarrow> 's" where
  "mstate \<equiv> monad_state_record.more"

abbreviation with_env_of :: "('c, 's) monad_state \<Rightarrow> 't \<Rightarrow> ('c, 't) monad_state" where
  "with_env_of s \<equiv> monad_state (env s)"

definition map_state :: "('s \<Rightarrow> 't) \<Rightarrow> ('c, 's) monad_state \<Rightarrow> ('c, 't) monad_state"
  where
  "map_state f \<equiv> \<lambda>s. with_env_of s (f (mstate s))"

definition const_env ::
  "(('c, 's) monad_state \<Rightarrow> ('d, 't) monad_state) \<Rightarrow> ('c, 's) monad_state \<Rightarrow> ('c, 't) monad_state"
  where
  "const_env f \<equiv> \<lambda>s. with_env_of s (mstate (f s))"

definition is_const_env :: "(('c, 's) monad_state \<Rightarrow> ('c, 't) monad_state) \<Rightarrow> bool"
  where
  "is_const_env f \<equiv> \<forall>s. env (f s) = env s"

subsection \<open>Basic properties about the Environment State\<close>

(* When the reader state is unit, the `mstate` field is the only relevant information *)
lemmas mstate_cong = arg_cong[where f=mstate]
lemmas mstate_cong_unit = mstate_cong[where 'a=unit]

lemma monad_state_unit_collapse[simp]:
  "monad_state () (mstate s) = s"
  by (cases s) simp

lemma with_env_of_mstate[simp]:
  "with_env_of s (mstate s) = s"
  by (cases s, auto)

lemma eq_with_env_of_mstate[simp]:
  "(s = with_env_of s s') = (mstate s = s')"
  by (cases s, auto)

lemma with_env_of_eq_mstate: (* not simp, can lead to non-termination *)
  "(with_env_of s s' = s) = (mstate s = s')"
  by (cases s, auto)

lemma mstate_map_state[simp]:
  "mstate (map_state f s) = f (mstate s)"
  by (simp add: map_state_def)

lemma env_map_state[simp]:
  "env (map_state f s) = env s"
  by (simp add: map_state_def)

lemma map_state_monad_state[simp]:
  "map_state f (monad_state c s) = monad_state c (f s)"
  by (simp add: map_state_def)

lemma mstate_const_env[simp]:
  "mstate (const_env f s) = mstate (f s)"
  by (simp add: const_env_def)

lemma env_const_env[simp]:
  "env (const_env f s) = env s"
  by (simp add: const_env_def)

lemma const_env_monad_state[simp]:
  "const_env f (monad_state c s) = monad_state c (mstate (f (monad_state c s)))"
  by (simp add: map_state_def)

lemma const_env_idem[simp]:
  "const_env (const_env f) = const_env f"
  by (simp add: const_env_def)

lemma is_const_env_const_env:
  "is_const_env (const_env f)"
  by (simp add: is_const_env_def)

lemma is_const_env_id:
  "is_const_env f \<Longrightarrow> const_env f = f"
  by (auto simp: is_const_env_def const_env_def)

end
