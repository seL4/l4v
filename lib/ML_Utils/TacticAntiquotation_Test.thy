(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Basic tests for the @{inline_tactic} and @{inline_method} antiquotations. *)

theory TacticAntiquotation_Test
imports
  TacticAntiquotation
begin

text \<open>Simple tests.\<close>

text \<open>Example proof.\<close>
lemma
  fixes fib :: "nat \<Rightarrow> nat"
  shows
  "\<lbrakk> fib 0 = 0;
     fib (Suc 0) = Suc 0;
     \<forall>n. fib (Suc (Suc n)) = fib n + fib (Suc n)
   \<rbrakk> \<Longrightarrow> fib n < 2^n"
  apply (induct n rule: less_induct)
  apply (rename_tac n, case_tac n)
   apply fastforce
  apply (rename_tac n, case_tac n)
   apply (clarsimp simp only:, simp)
  apply (clarsimp simp add: mult_2)
  apply (rule add_less_le_mono)
   apply (metis trans_less_add2 lessI less_trans)
  apply (fastforce simp only: mult_2[symmetric] power_Suc[symmetric]
                   intro: less_imp_le)
  done

text \<open>Let's uglify this proof\<dots>\<close>

(* Test that we can save a tactic and call it in another context.
 * (For this to work, the antiquoter has to dynamically parse and eval
 *  the method text each time the tactic is run) *)
ML \<open>
val stored_tactic = @{inline_tactic "rename_tac n, case_tac n"};
val stored_method = @{inline_method "rule add_less_le_mono"};
\<close>

lemma
  fixes fib :: "nat \<Rightarrow> nat"
  shows
  "\<lbrakk> fib 0 = 0;
     fib (Suc 0) = Suc 0;
     \<forall>n. fib (Suc (Suc n)) = fib n + fib (Suc n)
   \<rbrakk> \<Longrightarrow> fib n < 2^n"
  apply (tactic \<open>@{inline_tactic "induct n rule: less_induct"}\<close>)
  apply (tactic \<open>stored_tactic\<close>)
   apply (tactic \<open>@{inline_tactic fastforce}\<close>)
  apply (tactic \<open>stored_tactic\<close>)
   apply (tactic \<open>@{inline_tactic "clarsimp simp only:"} THEN @{inline_tactic "simp"}\<close>)
  apply (tactic \<open>NO_CONTEXT_TACTIC @{context}
                    (@{inline_method "clarsimp simp add: mult_2"} [])\<close>)
  apply (tactic \<open>NO_CONTEXT_TACTIC @{context} (stored_method [])\<close>)
   apply (tactic \<open>@{inline_tactic "metis trans_less_add2 lessI less_trans"}\<close>)
  apply (tactic \<open>@{inline_tactic "fastforce simp only: mult_2[symmetric] power_Suc[symmetric]
                                            intro: less_imp_le"}\<close>)
  done

end