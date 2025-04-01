(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Nondet_Lemmas
  imports Nondet_Monad
begin

section \<open>General Lemmas about the Non-Deterministic State Monad\<close>

subsection \<open>Congruence Rules for the Function Package\<close>

lemma bind_cong[fundef_cong]:
  "\<lbrakk> f = f';
     \<And>v s s'. (v, s') \<in> fst (f' s) \<Longrightarrow> g v (with_env_of s s') = g' v (with_env_of s s') \<rbrakk>
   \<Longrightarrow> f >>= g = f' >>= g'"
  by (auto simp: bind_def split_def)

lemma bind_apply_cong [fundef_cong]:
  "\<lbrakk> f s = f' s';
     \<And>rv st. (rv, st) \<in> fst (f' s') \<Longrightarrow> g rv (with_env_of s st) = g' rv (with_env_of s' st) \<rbrakk>
   \<Longrightarrow> (f >>= g) s = (f' >>= g') s'"
  by (auto simp: bind_def split_def)

lemma bindE_cong[fundef_cong]:
  "\<lbrakk> M = M';
     \<And>v s s'. (Inr v, s') \<in> fst (M' s) \<Longrightarrow> N v (with_env_of s s') = N' v (with_env_of s s') \<rbrakk>
   \<Longrightarrow> bindE M N = bindE M' N'"
  by (auto simp: bindE_def lift_def split: sum.splits intro!: bind_cong)

lemma return_no_const:
  "mstate s = mstate s' \<Longrightarrow> return x s = return x s'"
  by (simp add: return_def)

lemma throwError_no_const:
  "mstate s = mstate s' \<Longrightarrow> throwError e s = throwError e s'"
  by (fastforce simp: throwError_def intro: return_no_const)

lemma bindE_apply_cong[fundef_cong]:
  "\<lbrakk> f s = f' s';
     \<And>rv st. (Inr rv, st) \<in> fst (f' s') \<Longrightarrow> g rv (with_env_of s st) = g' rv (with_env_of s' st) \<rbrakk>
  \<Longrightarrow> (f >>=E g) s = (f' >>=E g') s'"
  by (auto simp: bindE_def lift_def split: sum.splits intro!: bind_apply_cong throwError_no_const)

lemma K_bind_apply_cong[fundef_cong]:
  "\<lbrakk> f st = f' st' \<rbrakk> \<Longrightarrow> K_bind f arg st = K_bind f' arg' st'"
  by simp

lemma when_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> when C m s = when C' m' s'"
  by (simp add: when_def)

lemma unless_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unless C m s = unless C' m' s'"
  by (simp add: when_def unless_def)

lemma whenE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> whenE C m s = whenE C' m' s'"
  by (simp add: whenE_def)

lemma unlessE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unlessE C m s = unlessE C' m' s'"
  by (simp add: unlessE_def)


subsection \<open>Simplifying Monads\<close>

lemma nested_bind[simp]:
  "do x <- do y <- f; return (g y) od; h x od = do y <- f; h (g y) od"
  by (clarsimp simp: bind_def Let_def split_def return_def)

lemma bind_dummy_ret_val:
  "do y \<leftarrow> a; b od = do a; b od"
  by simp

lemma fail_update[iff]:
  "fail (f s) = fail s"
  by (simp add: fail_def)

lemma fail_bind[simp]:
  "fail >>= f = fail"
  by (simp add: bind_def fail_def)

lemma fail_bindE[simp]:
  "fail >>=E f = fail"
  by (simp add: bindE_def bind_def fail_def)

lemma assert_A_False[simp]:
  "assert False = fail"
  by (simp add: assert_def)

lemma assert_A_True[simp]:
  "assert True = return ()"
  by (simp add: assert_def)

lemma assert_False[simp]:
  "assert False >>= f = fail"
  by simp

lemma assert_True[simp]:
  "assert True >>= f = f ()"
  by simp

lemma assertE_False[simp]:
  "assertE False >>=E f = fail"
  by (simp add: assertE_def)

lemma assertE_True[simp]:
  "assertE True >>=E f = f ()"
  by (simp add: assertE_def)

lemma when_False_bind[simp]:
  "when False g >>= f = f ()"
  by (rule ext) (simp add: when_def bind_def return_def)

lemma when_True_bind[simp]:
  "when True g >>= f = g >>= f"
  by (simp add: when_def bind_def return_def)

lemma whenE_False_bind[simp]:
  "whenE False g >>=E f = f ()"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma whenE_True_bind[simp]:
  "whenE True g >>=E f = g >>=E f"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma when_True[simp]:
  "when True X = X"
  by (clarsimp simp: when_def)

lemma when_False[simp]:
  "when False X = return ()"
  by (clarsimp simp: when_def)

lemma unless_False[simp]:
  "unless False X = X"
  by (clarsimp simp: unless_def)

lemma unlessE_False[simp]:
  "unlessE False f = f"
  unfolding unlessE_def by fastforce

lemma unless_True[simp]:
  "unless True X = return ()"
  by (clarsimp simp: unless_def)

lemma unlessE_True[simp]:
  "unlessE True f = returnOk ()"
  unfolding unlessE_def by fastforce

lemma unlessE_whenE:
  "unlessE P = whenE (\<not>P)"
  by (rule ext) (simp add: unlessE_def whenE_def)

lemma unless_when:
  "unless P = when (\<not>P)"
  by (rule ext) (simp add: unless_def when_def)

lemma gets_to_return[simp]:
  "gets (\<lambda>s. v) = return v"
  by (clarsimp simp: gets_def put_def get_def bind_def return_def)

lemma assert_opt_Some:
  "assert_opt (Some x) = return x"
  by (simp add: assert_opt_def)

lemma assertE_liftE:
  "assertE P = liftE (assert P)"
  by (simp add: assertE_def assert_def liftE_def returnOk_def)

lemma liftE_handleE'[simp]:
  "(liftE a <handle2> b) = liftE a"
  by (clarsimp simp: liftE_def handleE'_def)

lemma liftE_handleE[simp]:
  "(liftE a <handle> b) = liftE a"
  unfolding handleE_def by simp

lemma alternative_bind:
  "((a \<sqinter> b) >>= c) = ((a >>= c) \<sqinter> (b >>= c))"
  by (fastforce simp add: alternative_def bind_def split_def)

lemma alternative_refl:
  "(a \<sqinter> a) = a"
  by (simp add: alternative_def)

lemma alternative_com:
  "(f \<sqinter> g) = (g \<sqinter> f)"
  by (auto simp: alternative_def)

lemma liftE_alternative:
  "liftE (a \<sqinter> b) = (liftE a \<sqinter> liftE b)"
  by (simp add: liftE_def alternative_bind)


subsection \<open>Lifting and Alternative Basic Definitions\<close>

lemma liftE_liftM:
  "liftE = liftM Inr"
  by (auto simp: liftE_def liftM_def)

lemma liftME_liftM:
  "liftME f = liftM (case_sum Inl (Inr \<circ> f))"
  unfolding liftME_def liftM_def bindE_def returnOk_def lift_def
  apply (rule ext)
  apply (rule arg_cong[where f="bind m" for m])
  apply (fastforce simp: throwError_def split: sum.splits)
  done

lemma liftE_bindE:
  "liftE a >>=E b = a >>= b"
  by (simp add: liftE_def bindE_def lift_def bind_assoc)

lemma liftM_id[simp]:
  "liftM id = id"
  by (auto simp: liftM_def)

lemma liftM_bind:
  "liftM t f >>= g = f >>= (\<lambda>x. g (t x))"
  by (simp add: liftM_def bind_assoc)

lemma gets_bind_ign:
  "gets f >>= (\<lambda>x. m) = m"
  by (simp add: bind_def simpler_gets_def)

lemma exec_get:
  "(get >>= f) x = f x x"
  by (simp add: get_def bind_def)

lemmas get_bind_apply = exec_get (* FIXME lib: eliminate *)

lemma exec_gets:
  "(gets f >>= m) s = m (f s) s"
  by (simp add: simpler_gets_def bind_def)

lemma bind_eqI:
  "\<lbrakk> f = f'; \<And>x. g x = g' x \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  by (auto simp: bind_def split_def)

lemma condition_split:
  "P (condition C a b s) \<longleftrightarrow> (C s \<longrightarrow> P (a s)) \<and> (\<not>C s \<longrightarrow> P (b s))"
  by (clarsimp simp: condition_def)

lemma condition_split_asm:
  "P (condition C a b s) \<longleftrightarrow> (\<not>(C s \<and> \<not> P (a s) \<or> \<not>C s \<and> \<not>P (b s)))"
  by (clarsimp simp: condition_def)

lemmas condition_splits = condition_split condition_split_asm

lemma condition_true_triv[simp]:
  "condition (\<lambda>_. True) A B = A"
  by (fastforce split: condition_splits)

lemma condition_false_triv[simp]:
  "condition (\<lambda>_. False) A B = B"
  by (fastforce split: condition_splits)

lemma condition_true:
  "P s \<Longrightarrow> condition P A B s = A s"
  by (clarsimp simp: condition_def)

lemma condition_false:
  "\<not> P s \<Longrightarrow> condition P A B s = B s"
  by (clarsimp simp: condition_def)

lemmas arg_cong_bind = arg_cong2[where f=bind]
lemmas arg_cong_bind1 = arg_cong_bind[OF refl ext]


subsection \<open>Low-level monadic reasoning\<close>

lemma monad_eqI [intro]:
  "\<lbrakk> \<And>r t s. (r, t) \<in> fst (A s) \<Longrightarrow> (r, t) \<in> fst (B s);
     \<And>r t s. (r, t) \<in> fst (B s) \<Longrightarrow> (r, t) \<in> fst (A s);
     \<And>x. snd (A x) = snd (B x) \<rbrakk>
  \<Longrightarrow> A = B" for A :: "('c, 's, 'a) nondet_monad"
  by (fastforce intro!: set_eqI prod_eqI)

lemma monad_state_eqI [intro]:
  "\<lbrakk> \<And>r t. (r, t) \<in> fst (A s) \<Longrightarrow> (r, t) \<in> fst (B s');
     \<And>r t. (r, t) \<in> fst (B s') \<Longrightarrow> (r, t) \<in> fst (A s);
     snd (A s) = snd (B s') \<rbrakk>
  \<Longrightarrow> A s = B s'" for A :: "('c, 's, 'a) nondet_monad"
  by (fastforce intro!: set_eqI prod_eqI)


subsection \<open>General @{const whileLoop} reasoning\<close>

definition whileLoop_terminatesE ::
  "('a \<Rightarrow> ('c,'s) mpred) \<Rightarrow> ('a \<Rightarrow> ('c, 's, 'e + 'a) nondet_monad) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
  where
  "whileLoop_terminatesE C B c \<equiv>
     \<lambda>r. whileLoop_terminates (\<lambda>r s. case r of Inr v \<Rightarrow> C v s | _ \<Rightarrow> False) (lift B) c (Inr r)"

lemma whileLoop_cond_fail:
  "\<not> C x s \<Longrightarrow> whileLoop C B x s = return x s"
  by (auto simp: return_def whileLoop_def
           intro: whileLoop_results.intros whileLoop_terminates.intros
           elim: whileLoop_results.cases)

lemma whileLoopE_cond_fail:
  "\<not> C x s \<Longrightarrow> whileLoopE C B x s = returnOk x s"
  unfolding whileLoopE_def returnOk_def
  by (auto intro: whileLoop_cond_fail)

lemma whileLoop_results_simps_no_move[simp]:
  "(Some x, Some x) \<in> whileLoop_results C B c \<longleftrightarrow> \<not>C (fst x) (monad_state c (snd x))"
  (is "?LHS x \<longleftrightarrow> ?RHS x")
proof (rule iffI)
  assume "?LHS x"
  then have "(\<exists>a. Some x = Some a) \<longrightarrow> ?RHS (the (Some x))"
   by (induct rule: whileLoop_results.induct, auto)
  thus "?RHS x"
    by clarsimp
next
  assume "?RHS x"
  thus "?LHS x"
    by (metis surjective_pairing whileLoop_results.intros(1))
qed

lemma whileLoop_unroll:
  "whileLoop C B r = condition (C r) (B r >>= whileLoop C B) (return r)"
  (is "?LHS r = ?RHS r")
proof -
  have "\<And>r s. \<not> C r s \<Longrightarrow> ?LHS r s = ?RHS r s"
    by (clarsimp simp: whileLoop_cond_fail condition_def bind_def return_def)
  moreover
  have "\<And>r s. C r s \<Longrightarrow> ?LHS r s = (B r >>= whileLoop C B) s"
    apply (rule monad_state_eqI)
      apply (clarsimp simp: whileLoop_def bind_def split_def)
      apply (subst (asm) whileLoop_results_simps_valid)
      apply fastforce
     apply (clarsimp simp: whileLoop_def bind_def split_def)
     apply (subst whileLoop_results.simps)
     apply fastforce
    apply (clarsimp simp: whileLoop_def bind_def split_def)
    apply (subst whileLoop_results.simps)
    apply (subst whileLoop_terminates.simps)
    apply fastforce
    done
  ultimately
  show ?thesis by (fastforce simp: condition_def)
qed

lemma whileLoop_unroll':
  "whileLoop C B r = condition (C r) (B r) (return r) >>= whileLoop C B"
  apply (subst whileLoop_unroll)
  apply (auto simp: condition_def bind_def return_def split_def whileLoop_cond_fail)
  done

lemma whileLoopE_unroll:
  "whileLoopE C B r = condition (C r) (B r >>=E whileLoopE C B) (returnOk r)"
  unfolding whileLoopE_def
  apply (rule ext)
  apply (subst whileLoop_unroll)
  apply (clarsimp simp: bindE_def returnOk_def lift_def split: condition_splits)
  apply (rule arg_cong[where f="\<lambda>a. (B r >>= a) x" for x])
  apply (rule ext)+
  apply (clarsimp simp: lift_def split: sum.splits)
  apply (subst whileLoop_unroll)
  apply (clarsimp simp: condition_false throwError_def)
  done

lemma whileLoopE_unroll':
  "whileLoopE C B r = condition (C r) (B r) (returnOk r) >>=E whileLoopE C B"
  apply (subst whileLoopE_unroll)
  apply (fastforce simp: condition_def bindE_def bind_def lift_def split_def whileLoopE_cond_fail
                         returnOk_def return_def)
  done

end
