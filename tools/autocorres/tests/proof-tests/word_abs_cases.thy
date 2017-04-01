(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory word_abs_cases imports
  "../../AutoCorres"
begin

(* extra optimization for word_abs (currently does not work) *)
lemma INT_MIN_MAX_smod: "\<And>a b :: int. \<lbrakk> INT_MIN \<le> b; b \<le> INT_MAX; b \<noteq> 0 \<rbrakk> \<Longrightarrow> INT_MIN \<le> a smod b \<and> a smod b \<le> INT_MAX"
  apply (case_tac "b > 0")
   apply (rule conjI)
    apply (case_tac "a \<ge> 0")
     apply (frule_tac a = a and b = b in smod_int_compares(2))
      apply assumption
     apply (simp add: INT_MIN_def)
    apply (subgoal_tac "0 \<ge> a")
     apply (frule_tac a = a and b = b in smod_int_compares(3))
      apply assumption
     apply (simp add: INT_MIN_def INT_MAX_def)
    apply arith
   apply (case_tac "a \<ge> 0")
    apply (frule_tac a = a and b = b in smod_int_compares(1))
     apply assumption
    apply arith
   apply (subgoal_tac "0 \<ge> a")
    apply (frule_tac a = a and b = b in smod_int_compares(4))
     apply assumption
    apply arith
   apply arith
  apply (subgoal_tac "0 > b")
   apply (rule conjI)
    apply (case_tac "a \<ge> 0")
     apply (frule_tac a = a and b = b in smod_int_compares(6))
      apply assumption
     apply simp
    apply (subgoal_tac "0 \<ge> a")
     apply (frule_tac a = a and b = b in smod_int_compares(8))
      apply assumption
     apply (simp add: INT_MIN_def)
    apply arith
   apply (case_tac "a \<ge> 0")
    apply (frule_tac a = a and b = b in smod_int_compares(5))
     apply assumption
    apply (simp add: INT_MIN_def INT_MAX_def)
   apply (subgoal_tac "0 \<ge> a")
    apply (frule_tac a = a and b = b in smod_int_compares(7))
     apply assumption
    apply (simp add: INT_MAX_def)
   apply arith
  apply arith
  done
lemma [unfolded INT_MIN_def INT_MAX_def, simplified, L2flow]:
  "simp_expr (INT_MIN \<le> b \<and> b \<le> INT_MAX \<and> b \<noteq> 0) (INT_MIN \<le> a smod b) True"
  by (simp add: simp_expr_def INT_MIN_MAX_smod)
lemma [unfolded INT_MIN_def INT_MAX_def, simplified, L2flow]:
  "simp_expr (INT_MIN \<le> b \<and> b \<le> INT_MAX \<and> b \<noteq> 0) (a smod b \<le> INT_MAX) True"
  by (simp add: simp_expr_def INT_MIN_MAX_smod)

install_C_file "word_abs_cases.c"
autocorres [
  unsigned_word_abs = callee_flat_u_abs
             caller_flat_u_aa
             caller_flat_u_an
] "word_abs_cases.c"

context word_abs_cases begin

  declare K_bind_def[simp del]

  thm callee_flat_s'_def caller_flat_s'_def

  thm callee_flat_u_abs'_def callee_flat_u_noabs'_def
  thm caller_flat_u_aa'_def caller_flat_u_an'_def caller_flat_u_na'_def caller_flat_u_nn'_def

  thm callee_deep_s'.simps caller_deep_s'_def

  thm mutual_s1'.simps mutual_s2'.simps

  thm cross'_def gcd_s_rec'.simps gcd_s_loop'_def

  lemma int_max: "2147483647 \<le> a \<Longrightarrow> sint (n :: sword32) \<le> a"
    using INT_MIN_MAX_lemmas(10)[where s = n, unfolded INT_MAX_def]
    by arith
  lemma int_min: "a \<le> -2147483648 \<Longrightarrow> a \<le> sint (n :: sword32)"
    using INT_MIN_MAX_lemmas(11)[where s = n, unfolded INT_MIN_def]
    by arith
  lemma oguard_True: "(\<And>s. P s) \<Longrightarrow> DO oguard P; f OD = f"
    by (monad_eq simp: oguard_def obind_def K_bind_def)

  thm gcd_s_loop'_def gcd_s_loop'_def [simplified int_min int_max oguard_True]

  thm sum'_def sum'_def[simplified, folded INT_MAX_def[simplified] INT_MIN_def[simplified]]
end

end