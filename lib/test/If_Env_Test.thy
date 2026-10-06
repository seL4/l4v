(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory If_Env_Test
imports Lib.If_Env
begin

(* unset variable: no effect *)
context
  notes [[if_env IF_ENV_TEST_UNSET_VARIABLE [simp_trace]]]
begin
ML_val \<open>@{assert} (not (Config.get @{context} Raw_Simplifier.simp_trace))\<close>
end

(* L4V_ARCH is always set here *)
context
  notes [[if_env L4V_ARCH [simp_trace, simp_depth_limit = 42]]]
begin
ML_val \<open>@{assert} (Config.get @{context} Raw_Simplifier.simp_trace)\<close>
ML_val \<open>@{assert} (Config.get @{context} Raw_Simplifier.simp_depth_limit = 42)\<close>
end

(* effect is limited to the context block *)
ML_val \<open>@{assert} (not (Config.get @{context} Raw_Simplifier.simp_trace))\<close>


(* works anywhere where you can use attributes *)
named_theorems test
declare refl[if_env IF_ENV_TEST_UNSET_VARIABLE [test]]
(* empty: *)
ML_val \<open>@{assert} (null (Named_Theorems.get @{context} @{named_theorems test}))\<close>

declare refl[if_env L4V_ARCH [test]]
(* not empty: *)
ML_val \<open>@{assert} ((not o null) (Named_Theorems.get @{context} @{named_theorems test}))\<close>


(* Check locale contexts *)

locale if_env_test =
  fixes x :: nat
begin

(* unset variable: no effect *)
context
  notes [[if_env IF_ENV_TEST_UNSET_VARIABLE [simp_trace]]]
begin
ML_val \<open>@{assert} (not (Config.get @{context} Raw_Simplifier.simp_trace))\<close>
end

(* L4V_ARCH is always set here *)
context
  notes [[if_env L4V_ARCH [simp_trace, simp_depth_limit = 42]]]
begin
ML_val \<open>@{assert} (Config.get @{context} Raw_Simplifier.simp_trace)\<close>
ML_val \<open>@{assert} (Config.get @{context} Raw_Simplifier.simp_depth_limit = 42)\<close>
end

(* effect is limited to the context block *)
ML_val \<open>@{assert} (not (Config.get @{context} Raw_Simplifier.simp_trace))\<close>

end

context if_env_test
begin
ML_val \<open>@{assert} (not (Config.get @{context} Raw_Simplifier.simp_trace))\<close>
end

end
