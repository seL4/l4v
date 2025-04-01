(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Nondet_Env
  imports Nondet_Monad
begin

subsection \<open>Basic properties about the Environment State\<close>

(* When the reader state is unit, the `mstate` field is the only relevant information *)
lemmas mstate_cong = arg_cong[where f=mstate]
lemmas mstate_cong_unit = mstate_cong[where 'a=unit]

lemma monad_state_unit_collapse[simp]:
  "monad_state () (mstate s) = s"
  by (cases s) simp

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
