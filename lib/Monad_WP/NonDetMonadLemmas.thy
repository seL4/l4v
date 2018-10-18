(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory NonDetMonadLemmas
imports NonDetMonad
begin

section "General Lemmas Regarding the Nondeterministic State Monad"

subsection "Congruence Rules for the Function Package"

lemma bind_cong[fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s s'. (v, s') \<in> fst (f' s) \<Longrightarrow> g v s' = g' v s' \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  apply (rule ext)
  apply (auto simp: bind_def Let_def split_def intro: rev_image_eqI)
  done

lemma bind_apply_cong [fundef_cong]:
  "\<lbrakk> f s = f' s'; \<And>rv st. (rv, st) \<in> fst (f' s') \<Longrightarrow> g rv st = g' rv st \<rbrakk>
       \<Longrightarrow> (f >>= g) s = (f' >>= g') s'"
  apply (simp add: bind_def)
  apply (auto simp: split_def intro: SUP_cong [OF refl] intro: rev_image_eqI)
  done

lemma bindE_cong[fundef_cong]:
  "\<lbrakk> M = M' ; \<And>v s s'. (Inr v, s') \<in> fst (M' s) \<Longrightarrow> N v s' = N' v s' \<rbrakk> \<Longrightarrow> bindE M N = bindE M' N'"
  apply (simp add: bindE_def)
  apply (rule bind_cong)
   apply (rule refl)
  apply (unfold lift_def)
  apply (case_tac v, simp_all)
  done

lemma bindE_apply_cong[fundef_cong]:
  "\<lbrakk> f s = f' s'; \<And>rv st. (Inr rv, st) \<in> fst (f' s') \<Longrightarrow> g rv st = g' rv st \<rbrakk>
  \<Longrightarrow> (f >>=E g) s = (f' >>=E g') s'"
  apply (simp add: bindE_def)
  apply (rule bind_apply_cong)
   apply assumption
  apply (case_tac rv, simp_all add: lift_def)
  done

lemma K_bind_apply_cong[fundef_cong]:
  "\<lbrakk> f st = f' st' \<rbrakk> \<Longrightarrow> K_bind f arg st = K_bind f' arg' st'"
  by simp

lemma when_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> whenE C m s = whenE C' m' s'"
  by (simp add: whenE_def)

lemma unless_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unlessE C m s = unlessE C' m' s'"
  by (simp add: unlessE_def)

lemma whenE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> whenE C m s = whenE C' m' s'"
  by (simp add: whenE_def)

lemma unlessE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unlessE C m s = unlessE C' m' s'"
  by (simp add: unlessE_def)

subsection "Simplifying Monads"

lemma nested_bind [simp]:
  "do x <- do y <- f; return (g y) od; h x od =
   do y <- f; h (g y) od"
  apply (clarsimp simp add: bind_def)
  apply (rule ext)
  apply (clarsimp simp add: Let_def split_def return_def)
  done

lemma fail_bind [simp]:
  "fail >>= f = fail"
  by (simp add: bind_def fail_def)

lemma fail_bindE [simp]:
  "fail >>=E f = fail"
  by (simp add: bindE_def bind_def fail_def)

lemma assert_False [simp]:
  "assert False >>= f = fail"
  by (simp add: assert_def)

lemma assert_True [simp]:
  "assert True >>= f = f ()"
  by (simp add: assert_def)

lemma assertE_False [simp]:
  "assertE False >>=E f = fail"
  by (simp add: assertE_def)

lemma assertE_True [simp]:
  "assertE True >>=E f = f ()"
  by (simp add: assertE_def)

lemma when_False_bind [simp]:
  "when False g >>= f = f ()"
  by (rule ext) (simp add: when_def bind_def return_def)

lemma when_True_bind [simp]:
  "when True g >>= f = g >>= f"
  by (simp add: when_def bind_def return_def)

lemma whenE_False_bind [simp]:
  "whenE False g >>=E f = f ()"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma whenE_True_bind [simp]:
  "whenE True g >>=E f = g >>=E f"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma when_True [simp]: "when True X = X"
  by (clarsimp simp: when_def)

lemma when_False [simp]: "when False X = return ()"
  by (clarsimp simp: when_def)

lemma unless_False [simp]: "unless False X = X"
  by (clarsimp simp: unless_def)

lemma unlessE_False [simp]: "unlessE False f = f"
  unfolding unlessE_def by fastforce

lemma unless_True [simp]: "unless True X = return ()"
  by (clarsimp simp: unless_def)

lemma unlessE_True [simp]: "unlessE True f = returnOk ()"
  unfolding unlessE_def by fastforce

lemma unlessE_whenE:
  "unlessE P = whenE (~P)"
  by (rule ext)+ (simp add: unlessE_def whenE_def)

lemma unless_when:
  "unless P = when (~P)"
  by (rule ext)+ (simp add: unless_def when_def)

lemma gets_to_return [simp]: "gets (\<lambda>s. v) = return v"
  by (clarsimp simp: gets_def put_def get_def bind_def return_def)

lemma assert_opt_Some:
  "assert_opt (Some x) = return x"
  by (simp add: assert_opt_def)

lemma assertE_liftE:
  "assertE P = liftE (assert P)"
  by (simp add: assertE_def assert_def liftE_def returnOk_def)

lemma liftE_handleE' [simp]: "((liftE a) <handle2> b) = liftE a"
  apply (clarsimp simp: liftE_def handleE'_def)
  done

lemma liftE_handleE [simp]: "((liftE a) <handle> b) = liftE a"
  apply (unfold handleE_def)
  apply simp
  done

lemma condition_split:
  "P (condition C a b s) = ((((C s) \<longrightarrow> P (a s)) \<and> (\<not> (C s) \<longrightarrow> P (b s))))"
  apply (clarsimp simp: condition_def)
  done

lemma condition_split_asm:
  "P (condition C a b s) = (\<not> (C s \<and> \<not> P (a s) \<or> \<not> C s \<and> \<not> P (b s)))"
  apply (clarsimp simp: condition_def)
  done

lemmas condition_splits = condition_split condition_split_asm

lemma condition_true_triv [simp]:
  "condition (\<lambda>_. True) A B = A"
  apply (rule ext)
  apply (clarsimp split: condition_splits)
  done

lemma condition_false_triv [simp]:
  "condition (\<lambda>_. False) A B = B"
  apply (rule ext)
  apply (clarsimp split: condition_splits)
  done

lemma condition_true: "\<lbrakk> P s \<rbrakk> \<Longrightarrow> condition P A B s = A s"
  apply (clarsimp simp: condition_def)
  done

lemma condition_false: "\<lbrakk> \<not> P s \<rbrakk> \<Longrightarrow> condition P A B s = B s"
  apply (clarsimp simp: condition_def)
  done

lemmas arg_cong_bind = arg_cong2[where f=bind]
lemmas arg_cong_bind1 = arg_cong_bind[OF refl ext]

section "Low-level monadic reasoning"

lemma monad_eqI [intro]:
  "\<lbrakk> \<And>r t s. (r, t) \<in> fst (A s) \<Longrightarrow> (r, t) \<in> fst (B s);
     \<And>r t s. (r, t) \<in> fst (B s) \<Longrightarrow> (r, t) \<in> fst (A s);
     \<And>x. snd (A x) = snd (B x) \<rbrakk>
  \<Longrightarrow> (A :: ('s, 'a) nondet_monad) = B"
  apply (fastforce intro!: set_eqI prod_eqI)
  done

lemma monad_state_eqI [intro]:
  "\<lbrakk> \<And>r t. (r, t) \<in> fst (A s) \<Longrightarrow> (r, t) \<in> fst (B s');
     \<And>r t. (r, t) \<in> fst (B s') \<Longrightarrow> (r, t) \<in> fst (A s);
     snd (A s) = snd (B s') \<rbrakk>
  \<Longrightarrow> (A :: ('s, 'a) nondet_monad) s = B s'"
  apply (fastforce intro!: set_eqI prod_eqI)
  done

subsection "General whileLoop reasoning"

definition
  "whileLoop_terminatesE C B \<equiv> (\<lambda>r.
     whileLoop_terminates (\<lambda>r s. case r of Inr v \<Rightarrow> C v s | _ \<Rightarrow> False) (lift B) (Inr r))"

lemma whileLoop_cond_fail:
    "\<lbrakk> \<not> C x s \<rbrakk> \<Longrightarrow> (whileLoop C B x s) = (return x s)"
  apply (auto simp: return_def whileLoop_def
       intro: whileLoop_results.intros
              whileLoop_terminates.intros
       elim!: whileLoop_results.cases)
  done

lemma whileLoopE_cond_fail:
    "\<lbrakk> \<not> C x s \<rbrakk> \<Longrightarrow> (whileLoopE C B x s) = (returnOk x s)"
  apply (clarsimp simp: whileLoopE_def returnOk_def)
  apply (auto intro: whileLoop_cond_fail)
  done

lemma whileLoop_results_simps_no_move [simp]:
  shows "((Some x, Some x) \<in> whileLoop_results C B) = (\<not> C (fst x) (snd x))"
    (is "?LHS x = ?RHS x")
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
  "(whileLoop C B r) =  ((condition (C r) (B r >>= (whileLoop C B)) (return r)))"
  (is "?LHS r = ?RHS r")
proof -
  have cond_fail: "\<And>r s. \<not> C r s \<Longrightarrow> ?LHS r s = ?RHS r s"
    apply (subst whileLoop_cond_fail, simp)
    apply (clarsimp simp: condition_def bind_def return_def)
    done

  have cond_pass: "\<And>r s. C r s \<Longrightarrow> whileLoop C B r s = (B r >>= (whileLoop C B)) s"
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

  show ?thesis
    apply (rule ext)
    apply (metis cond_fail cond_pass condition_def)
    done
qed

lemma whileLoop_unroll':
    "(whileLoop C B r) = ((condition (C r) (B r) (return r)) >>= (whileLoop C B))"
  apply (rule ext)
  apply (subst whileLoop_unroll)
  apply (clarsimp simp: condition_def bind_def return_def split_def)
  apply (subst whileLoop_cond_fail, simp)
  apply (clarsimp simp: return_def)
  done

lemma whileLoopE_unroll:
  "(whileLoopE C B r) =  ((condition (C r) (B r >>=E (whileLoopE C B)) (returnOk r)))"
  apply (rule ext)
  apply (unfold whileLoopE_def)
  apply (subst whileLoop_unroll)
  apply (clarsimp simp: whileLoopE_def bindE_def returnOk_def split: condition_splits)
  apply (clarsimp simp: lift_def)
  apply (rule_tac f="\<lambda>a. (B r >>= a) x" in arg_cong)
  apply (rule ext)+
  apply (clarsimp simp: lift_def split: sum.splits)
  apply (subst whileLoop_unroll)
  apply (subst condition_false)
   apply fastforce
  apply (clarsimp simp: throwError_def)
  done

lemma whileLoopE_unroll':
  "(whileLoopE C B r) =  ((condition (C r) (B r) (returnOk r)) >>=E (whileLoopE C B))"
  apply (rule ext)
  apply (subst whileLoopE_unroll)
  apply (clarsimp simp: condition_def bindE_def bind_def returnOk_def return_def lift_def split_def)
  apply (subst whileLoopE_cond_fail, simp)
  apply (clarsimp simp: returnOk_def return_def)
  done

(* These lemmas are useful to apply to rules to convert valid rules into
 * a format suitable for wp. *)

lemma valid_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>"
  by (auto simp add: valid_def no_fail_def split: prod.splits)

lemma validNF_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>!"
  by (auto simp add: valid_def validNF_def no_fail_def split: prod.splits)

lemma validE_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>, \<lbrace> \<lambda>rv s. E s0 rv s \<rbrace>) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s')
        \<and> (\<forall>rv s'. E s0 rv s' \<longrightarrow> E' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>"
  by (auto simp add: validE_def valid_def no_fail_def split: prod.splits sum.splits)

lemma validE_NF_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>, \<lbrace> \<lambda>rv s. E s0 rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s')
        \<and> (\<forall>rv s'. E s0 rv s' \<longrightarrow> E' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>!"
  by (auto simp add: validE_NF_def validE_def valid_def no_fail_def split: prod.splits sum.splits)

lemma validNF_conjD1: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. Q rv s \<and> Q' rv s \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_conjD2: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. Q rv s \<and> Q' rv s \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q' \<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

end
