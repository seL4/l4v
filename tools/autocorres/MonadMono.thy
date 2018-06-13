(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Facts about recursive functions with measure parameter.
 * Any recursive functions from AutoCorres are monotonic in the measure,
 * which allows us to use the "measure_call" mechanism for calling them.
 *)
theory MonadMono
imports
  NonDetMonadEx
  "Lib.OptionMonadWP"
begin

(*
 * Call function f by returning all of its possible results.
 * The call succeeds if any measure value succeeds.
 *)
definition "measure_call f \<equiv>
    \<lambda>s. ({(r', s'). \<exists>m. (r', s') \<in> fst (f m s)}, \<forall>m. snd (f m s))"

(*
 * monad_mono gives preconditions for functions so that measure_call will
 * return meaningful results.
 *
 * The preconditions are:
 *
 * - If the measure is increased, the function never returns fewer
 *   results. (Monotonicity condition)
 *
 * - If the function succeeds with some measure, it will not fail with
 *   a larger measure, and will return exactly the same results.
 *
 * The monotonicity condition is technically not needed, but all our
 * functions satisfy it anyway and it makes intermediate proofs easier.
 *)
definition "monad_mono f \<equiv>
     (\<forall>(x :: nat) y s. x < y \<longrightarrow>
         (fst (f x s) \<subseteq> fst (f y s) \<and>
          (\<not> snd (f x s) \<longrightarrow> \<not> snd (f y s) \<and> fst (f x s) = fst (f y s))))"

(* Basic monad_mono lemmas *)
lemma monad_mono_incl: "\<lbrakk> monad_mono f; \<not> snd (f m s) \<rbrakk> \<Longrightarrow> fst (f m' s) \<subseteq> fst (f m s)"
  using less_linear[where x = m and y = m']
  by (auto simp: monad_mono_def)

(* wp rules for function calls *)
lemma call_all_valid [wp]:
    "\<lbrakk> \<forall> m. valid P (x m) Q; monad_mono x \<rbrakk> \<Longrightarrow> valid P (measure_call x) Q"
  apply (clarsimp simp: valid_def measure_call_def monad_mono_def)
  by blast

lemma call_all_validNF [wp]:
    "\<lbrakk>  validNF P (x m) Q; monad_mono x \<rbrakk> \<Longrightarrow> validNF P (measure_call x) Q"
  apply (clarsimp simp: measure_call_def validNF_def valid_def no_fail_def)
  apply (metis in_mono split_conv monad_mono_incl)
  done

(* Alternative definition of monad_mono, suitable for induction *)
definition "monad_mono_step f m \<equiv>
  (\<forall>s. fst (f m s) \<subseteq> fst (f (Suc m) s) \<and>
       (\<not> snd (f m s) \<longrightarrow> \<not> snd (f (Suc m) s) \<and> fst (f m s) = fst (f (Suc m) s)))"

lemma monad_mono_alt_def: "monad_mono f = (\<forall>m. monad_mono_step f m)"
  apply (rule iffI)
   apply (fastforce simp: monad_mono_def monad_mono_step_def)
  apply (unfold monad_mono_def monad_mono_step_def)
  apply clarify
  apply (subst (asm) atomize_all[symmetric])+
  proof -
    fix x y :: nat
    fix s
    assume suc: "\<And>m s. fst (f m s) \<subseteq> fst (f (Suc m) s) \<and>
              (\<not> snd (f m s) \<longrightarrow> \<not> snd (f (Suc m) s) \<and> fst (f m s) = fst (f (Suc m) s))"
       and less: "x < y"
    thus "fst (f x s) \<subseteq> fst (f y s) \<and>
          (\<not> snd (f x s) \<longrightarrow> \<not> snd (f y s) \<and> fst (f x s) = fst (f y s))"
      apply (induct x)
       apply (induct y)
        apply blast
       apply blast
      (* induct bureaucracy... *)
      proof -
        fix x :: nat
        assume less: "Suc x < y"
        thus "fst (f (Suc x) s) \<subseteq> fst (f y s) \<and>
           (\<not> snd (f (Suc x) s) \<longrightarrow> \<not> snd (f y s) \<and> fst (f (Suc x) s) = fst (f y s))"
          apply (induct y)
           apply blast
          apply (case_tac "Suc x < y")
           using suc apply blast
          apply (case_tac "Suc x = y")
           using suc apply blast
          apply simp
          done
       qed
  qed

lemmas monad_mono_step = iffD2[OF monad_mono_alt_def, rule_format]

lemma monad_mono_step_const: "monad_mono_step (\<lambda>_. f) m"
  by (simp add: monad_mono_step_def)

(* nondet_monad rules *)
lemma monad_mono_step_in_monad:
  "\<lbrakk> monad_mono_step f m; (r', s') \<in> fst (f m s) \<rbrakk> \<Longrightarrow> (r', s') \<in> fst (f (Suc m) s)"
  apply (clarsimp simp: monad_mono_step_def)
  apply blast
  done

lemma monad_mono_step_snd_monad:
  "\<lbrakk> monad_mono_step f m; \<not> snd (f m s) \<rbrakk> \<Longrightarrow> \<not> snd (f (Suc m) s)"
  by (clarsimp simp: monad_mono_step_def)

lemma monad_mono_step_bexI:
  "\<lbrakk> monad_mono_step f m; (r', s') \<in> fst (f m s); P r' s' \<rbrakk> \<Longrightarrow> \<exists>(r', s') \<in> fst (f (Suc m) s). P r' s'"
  apply (drule (1) monad_mono_step_in_monad)
  apply force
  done

lemma monad_mono_stepI [intro]:
  "\<lbrakk> \<And>s r' s'. (r', s') \<in> fst (f m s) \<Longrightarrow> (r', s') \<in> fst (f (Suc m) s);
     \<And>s. \<not> snd (f m s) \<Longrightarrow> \<not> snd (f (Suc m) s);
     \<And>s r' s'. \<lbrakk> \<not> snd (f m s); \<not> snd (f (Suc m) s); (r', s') \<in> fst (f (Suc m) s) \<rbrakk>
                \<Longrightarrow> (r', s') \<in> fst (f m s)
   \<rbrakk> \<Longrightarrow> monad_mono_step f m"
  apply (clarsimp simp: monad_mono_step_def)
  apply fast
  done

lemma monad_mono_step_bind:
  "\<lbrakk> monad_mono_step f m; \<And>x. monad_mono_step (\<lambda>m. g m x) m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. (f m) >>= (g m)) m"
  apply atomize
  apply rule
    apply (monad_eq)
    apply (metis monad_mono_step_in_monad)
   apply (monad_eq simp: Ball_def)
   apply (metis monad_mono_step_def)
  apply (monad_eq simp: Ball_def)
  apply (unfold monad_mono_step_def)
  apply blast
  done

lemma monad_mono_step_bindE:
  "\<lbrakk> monad_mono_step f m; \<And>x. monad_mono_step (\<lambda>m. g m x) m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. (f m) >>=E (g m)) m"
  apply (unfold bindE_def)
  apply (rule monad_mono_step_bind)
   apply simp
  apply (monad_eq simp: monad_mono_step_def NonDetMonad.lift_def
      split: sum.splits)
  done

lemma monad_mono_step_liftE:
  "monad_mono_step f m \<Longrightarrow> monad_mono_step (\<lambda>m. liftE (f m)) m"
  apply (unfold liftE_def)
  apply (erule monad_mono_step_bind)
  apply (rule monad_mono_step_const)
  done

lemma monad_mono_step_handleE':
  "\<lbrakk> monad_mono_step f m; \<And>x. monad_mono_step (\<lambda>m. g m x) m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. f m <handle2> g m) m"
  apply atomize
  apply rule
    apply (monad_eq)
    apply (metis monad_mono_step_in_monad)
   apply (monad_eq simp: Ball_def)
   apply (metis monad_mono_step_def)
  apply (monad_eq simp: Ball_def)
  apply (fastforce simp: monad_mono_step_def)
  done

lemma monad_mono_step_handleE:
  "\<lbrakk> monad_mono_step f m; \<And>x. monad_mono_step (\<lambda>m. g m x) m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. f m <handle> g m) m"
  by (simp add: handleE_def monad_mono_step_handleE')

lemma monad_mono_step_condition:
  "\<lbrakk> monad_mono_step f m; monad_mono_step g m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. condition C (f m) (g m)) m"
  apply rule
    apply (monad_eq simp: monad_mono_step_def, blast)+
  done

lemma fst_whileLoop_is_exs_valid:
  "((a, b) \<in> fst (whileLoop C B i s)) = \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B i \<exists>\<lbrace> \<lambda>rv s. rv = a \<and> s = b \<rbrace>"
  by (clarsimp simp: exs_valid_def Bex_def)

lemma not_snd_whileLoop_is_validNF:
  "(\<not> snd (whileLoop C B i s)) = \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B i \<lbrace> \<lambda>_ _. True \<rbrace>!"
  by (clarsimp simp: validNF_alt_def)

lemma monad_mono_step_whileLoop:
  assumes body_mono: "\<And>x. monad_mono_step (\<lambda>m. B m x) m"
  shows "monad_mono_step (\<lambda>m. whileLoop C (B m) i) m"
proof -
  {
    fix a b s
    have "(a, b) \<in> fst (whileLoop C (B m) i s) \<Longrightarrow>
             (a, b) \<in> fst (whileLoop C (B (Suc m)) i s)"
      apply (clarsimp simp: fst_whileLoop_is_exs_valid)
      apply (subst (asm) exs_valid_whileLoop_complete [symmetric])
      apply (erule exE | erule conjE)+
      apply (rule_tac T=T and R=R in exs_valid_whileLoop)
         apply clarsimp
        apply (cut_tac x=r in body_mono)
        apply (clarsimp simp: monad_mono_step_def exs_valid_def split_def)
        apply blast
       apply simp
      apply blast
      done
  }
  note A = this

  {
    fix a b s
    have "\<lbrakk> \<not> snd (whileLoop C (B m) i s);
                  (a, b) \<in> fst (whileLoop C (B (Suc m)) i s) \<rbrakk>
              \<Longrightarrow> (a, b) \<in> fst (whileLoop C (B m) i s)"
      apply (clarsimp simp: fst_whileLoop_is_exs_valid)
      apply (subst (asm) exs_valid_whileLoop_complete [symmetric])
      apply (subst (asm) not_snd_whileLoop_complete)
      apply (erule exE | erule conjE)+
      apply (rule_tac T="\<lambda>r s. T r s \<and> I r s" and R=Ra in exs_valid_whileLoop)
         apply simp
        apply (cut_tac x=r in body_mono)
        apply (clarsimp simp: monad_mono_step_def exs_valid_def split_def Bex_def)
        apply metis
       apply simp
      apply (clarsimp simp: exs_valid_def Bex_def)
      done
  }
  note B = this

  {
    fix i s
    have "\<lbrakk>\<not> snd (whileLoop C (B m) i s) \<rbrakk> \<Longrightarrow>
                  \<not> snd (whileLoop C (B (Suc m)) i s)"
      apply (subst (asm) not_snd_whileLoop_complete)
      apply (erule exE | erule conjE)+
      apply (rule_tac I="I" and R=R in not_snd_whileLoop)
        apply clarsimp
       apply (cut_tac x=r in body_mono)
       apply (clarsimp simp: monad_mono_step_def validNF_alt_def)
       apply blast
      apply simp
      done
  }
  note C = this

  show ?thesis
    apply (clarsimp simp: monad_mono_step_def)
    apply (metis prod.exhaust subsetI subset_antisym A B C)
    done
qed

lemma monad_mono_step_whileLoopE:
  "\<lbrakk> \<And>x. monad_mono_step (\<lambda>m. B m x) m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. whileLoopE C (B m) i) m"
  apply (unfold whileLoopE_def)
  apply (subgoal_tac "\<And>x. monad_mono_step (\<lambda>m. lift (B m) x) m")
  apply (erule monad_mono_step_whileLoop)
  apply (unfold lift_def)
  apply rule
    apply (clarsimp split: prod.splits sum.splits)
    apply (fastforce dest: monad_mono_step_in_monad)
   apply (clarsimp split: prod.splits sum.splits simp: monad_mono_step_def)+
  done


(* measure_call for the option monad. *)
definition "measure_ocall f \<equiv> \<lambda>s. f (SOME m. f m s \<noteq> None) s"

definition "option_monad_mono f \<equiv>
  \<forall>(x :: nat) y s. x < y \<longrightarrow>
    (case f y s of None \<Rightarrow> f x s = None
                 | Some r \<Rightarrow> f x s = None \<or> f x s = Some r)"

lemma option_monad_mono_eq:
  "(\<And>m. f m = gets_the (f' m)) \<Longrightarrow> monad_mono f = option_monad_mono f'"
  apply (clarsimp simp: monad_mono_def option_monad_mono_def gets_the_def
    gets_def get_def assert_opt_def return_def fail_def bind_def' split: option.splits)
  apply (rule iff_allI iff_impI)+
  apply (rule_tac t = "\<forall>r. f' x s = Some r \<longrightarrow> (\<exists>r'. f' y s = Some r') \<and> (\<forall>r'. f' y s = Some r' \<longrightarrow> r = r')"
              and s = "\<forall>r. f' x s = Some r \<longrightarrow> f' y s = Some r" in subst)
   apply (force intro: iff_allI iff_impI)
  apply (rule iffI)
   apply (metis (hide_lams, no_types) option.exhaust)
  apply force
  done

lemma measure_ocall_ovalid [wp]:
    "\<lbrakk> \<forall> m. ovalid P (x m) Q; option_monad_mono x \<rbrakk> \<Longrightarrow> ovalid P (measure_ocall x) Q"
  by (clarsimp simp: ovalid_def measure_ocall_def option_monad_mono_def)

lemma measure_ocall_ovalidNF [wp]:
    "\<lbrakk> ovalidNF P (x m) Q; option_monad_mono x \<rbrakk> \<Longrightarrow> ovalidNF P (measure_ocall x) Q"
  apply (clarsimp simp: measure_ocall_def option_monad_mono_def ovalidNF_def)
  apply (rule_tac a = m in someI2)
   apply simp
  apply (metis (lifting, full_types) linorder_neqE_nat option.distinct(1) option.simps(5))
  done

end
