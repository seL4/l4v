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
 * L1 definitions and basic lemmas.
 *)

theory L1Defs
imports CCorresE MonadMono
begin

(* Definitions of constants used in the SimplConv output. *)
type_synonym 's L1_monad = "('s, unit + unit) nondet_monad"
definition "L1_seq (A :: 's L1_monad) (B :: 's L1_monad) \<equiv> (A >>=E (\<lambda>_. B)) :: 's L1_monad"
definition "L1_skip \<equiv> returnOk () :: 's L1_monad"
definition "L1_modify m \<equiv> liftE (modify m) :: 's L1_monad"
definition "L1_condition c (A :: 's L1_monad) (B :: 's L1_monad) \<equiv> condition c A B"
definition "L1_catch (A :: 's L1_monad) (B :: 's L1_monad) \<equiv> (A <handle> (\<lambda>_. B))"
definition "L1_while c (A :: 's L1_monad) \<equiv> (whileLoopE (\<lambda>_. c) (\<lambda>_. A) ())"
definition "L1_throw \<equiv> throwError () :: 's L1_monad"
definition "L1_spec r \<equiv> liftE (spec r) :: 's L1_monad"
definition "L1_guard c \<equiv> (liftE (guard c)) :: 's L1_monad"
definition "L1_init v \<equiv> (doE x \<leftarrow> liftE (select UNIV); liftE (modify (v (\<lambda>_. x))) odE) :: 's L1_monad"
definition "L1_call scope_setup (dest_fn :: 's L1_monad) scope_teardown return_xf \<equiv>
    doE
        s \<leftarrow> liftE get;
        ((doE liftE (modify scope_setup);
              dest_fn odE)
         <handle> (\<lambda>_. fail));
        t \<leftarrow> liftE get;
        liftE (modify (scope_teardown s));
        liftE (modify (return_xf t))
    odE"
definition "L1_fail \<equiv> fail :: 's L1_monad"
definition "L1_recguard n b \<equiv> (condition (\<lambda>s. n = (0 :: nat)) fail b) :: 's L1_monad"
definition "L1_set_to_pred S \<equiv> \<lambda>s. s \<in> S"
definition "recguard_dec (n :: nat) \<equiv> n - 1"

lemmas L1_defs = L1_seq_def L1_skip_def L1_modify_def L1_condition_def
    L1_catch_def L1_while_def L1_throw_def L1_spec_def L1_guard_def
    L1_fail_def L1_init_def L1_recguard_def L1_set_to_pred_def

lemmas L1_defs' =
   L1_seq_def L1_skip_def L1_modify_def [folded modifyE_def] L1_condition_def L1_catch_def
   L1_while_def L1_throw_def L1_spec_def [folded specE_def] L1_guard_def [folded guardE_def]
   L1_fail_def L1_init_def [folded modifyE_def selectE_def] L1_recguard_def L1_set_to_pred_def

declare L1_set_to_pred_def [simp]

(* Our corres rule converting from the deeply-embedded SIMPL to a shallow embedding. *)
definition
  L1corres :: "bool \<Rightarrow> ('p \<Rightarrow> ('s, 'p, 'e) com option)
                     \<Rightarrow> ('s, unit + unit) nondet_monad \<Rightarrow> ('s, 'p, 'e) com \<Rightarrow> bool"
where
  "L1corres check_term \<Gamma> \<equiv>
   \<lambda>A C. \<forall>s. \<not> snd (A s) \<longrightarrow>
       ((\<forall>t. \<Gamma> \<turnstile> \<langle>C, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
        (case t of
              Normal s' \<Rightarrow> (Inr (), s') \<in> fst (A s)
            | Abrupt s' \<Rightarrow> (Inl (), s') \<in> fst (A s)
            | _ \<Rightarrow> False))
        \<and> (check_term \<longrightarrow> \<Gamma> \<turnstile> C \<down> Normal s))"

lemma L1corres_alt_def: "L1corres ct \<Gamma> = ccorresE (\<lambda>x. x) ct \<Gamma> \<top> UNIV"
  apply (rule ext)+
  apply (clarsimp simp: L1corres_def ccorresE_def)
  done

(* Wrapper for calling un-translated functions. *)
definition
  "L1_call_simpl check_term Gamma proc
    = do s \<leftarrow> get;
         assert (check_term \<longrightarrow> Gamma \<turnstile> Call proc \<down> Normal s);
         xs \<leftarrow> select {t. Gamma \<turnstile> \<langle>Call proc, Normal s\<rangle> \<Rightarrow> t};
         case xs :: (_, strictc_errortype) xstate of
             Normal s \<Rightarrow> liftE (put s)
           | Abrupt s \<Rightarrow> do put s; throwError () od
           | Fault ft \<Rightarrow> fail
           | Stuck \<Rightarrow> fail
      od"

lemma L1corres_call_simpl:
  "L1corres ct Gamma (L1_call_simpl ct Gamma proc) (Call proc)"
  apply (clarsimp simp: L1corres_def L1_call_simpl_def in_monad
                        exec_get assert_def)
  apply (case_tac t, simp_all add: in_monad in_select)
     apply (auto simp: in_monad snd_bind select_def)
  done


lemma L1corres_skip:
  "L1corres ct \<Gamma> L1_skip SKIP"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: liftE_def return_def L1_skip_def returnOk_def)
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
   apply (clarsimp simp: split_def return_def bindE_def bind_def)
  apply clarify
  apply (rule terminates.Skip)
  done

lemma L1corres_throw:
  "L1corres ct \<Gamma> L1_throw Throw"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: ccorresE_def L1_throw_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
   apply (clarsimp simp: throwError_def return_def)
  apply clarify
  apply (rule terminates.Throw)
  done

lemma L1corres_seq:
  "\<lbrakk> L1corres ct \<Gamma> L L'; L1corres ct \<Gamma> R R' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> (L1_seq L R) (L' ;; R')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_seq_def)
  apply (rule ccorresE_Seq)
  apply auto
  done

lemma L1corres_modify:
  "L1corres ct \<Gamma> (L1_modify m) (Basic m)"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: liftE_def modify_def get_def put_def bind_def L1_modify_def)
  apply (clarsimp simp: ccorresE_def)
  apply (auto elim: exec_Normal_elim_cases simp: split_def return_def intro: terminates.Basic)
  done

lemma L1corres_condition:
  "\<lbrakk> L1corres ct \<Gamma> L L'; L1corres ct \<Gamma> R R' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> (L1_condition (L1_set_to_pred c) L R) (Cond c L' R')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_defs)
  apply (rule ccorresE_Cond_match)
    apply (erule ccorresE_guard_imp, simp+)[1]
   apply (erule ccorresE_guard_imp, simp+)[1]
  apply simp
  done

lemma L1corres_catch:
  "\<lbrakk> L1corres ct \<Gamma> L L'; L1corres ct \<Gamma> R R' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> (L1_catch L R) (Catch L' R')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_catch_def)
  apply (erule ccorresE_Catch)
  apply force
  done

lemma L1corres_while:
  "\<lbrakk> L1corres ct \<Gamma> B B' \<rbrakk> \<Longrightarrow>
      L1corres ct \<Gamma> (L1_while (L1_set_to_pred c) B) (While c B')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_defs)
  apply (rule ccorresE_While)
   apply clarsimp
  apply simp
  done

lemma L1corres_guard:
  "\<lbrakk> L1corres ct \<Gamma> B B' \<rbrakk> \<Longrightarrow>
      L1corres ct \<Gamma> (L1_seq (L1_guard (L1_set_to_pred c)) B) (Guard f c B')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: ccorresE_def L1_defs)
  apply (erule_tac x=s in allE)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (monad_eq simp: Bex_def split: xstate.splits)
    apply blast
   apply (monad_eq simp: Bex_def split: xstate.splits)
  apply (monad_eq simp: Bex_def split: xstate.splits)
  apply (fastforce intro!: terminates.Guard)
  done

lemma L1corres_spec:
  "L1corres ct \<Gamma> (L1_spec x) (Spec x)"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: ccorresE_def L1_spec_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (clarsimp simp: liftE_def spec_def bind_def return_def)
   apply (clarsimp simp: liftE_def spec_def bind_def return_def)
  apply clarify
  apply (rule terminates.Spec)
  done

lemma L1_init_alt_def:
  "L1_init upd \<equiv> L1_spec {(s, t). \<exists>v. t = upd (\<lambda>_. v) s}"
  apply (rule eq_reflection)
  apply (clarsimp simp: L1_defs bind_liftE_distrib [symmetric])
  apply (rule arg_cong [where f=liftE])
  apply (fastforce simp: spec_def select_def simpler_modify_def bind_def)
  done

lemma L1corres_init:
  "L1corres ct \<Gamma> (L1_init upd) (lvar_nondet_init accessor upd)"
  by (auto simp: L1_init_alt_def lvar_nondet_init_def intro: L1corres_spec)

lemma L1corres_guarded_spec:
  "L1corres ct \<Gamma> (L1_spec R) (guarded_spec_body F R)"
  apply (clarsimp simp: L1corres_alt_def ccorresE_def L1_spec_def guarded_spec_body_def)
  apply (force simp: liftE_def spec_def bind_def return_def
               elim: exec_Normal_elim_cases intro: terminates.Guard terminates.Spec)
  done

lemma liftE_get_bindE:
  "(liftE get >>=E B) = (\<lambda>s. B s s)"
  apply (monad_eq simp: Ball_def Bex_def)
  done

lemma L1corres_call:
  "(\<And>m. L1corres ct \<Gamma> (\<lambda>s. dest_fn m s) (Call dest)) \<Longrightarrow>
    L1corres ct \<Gamma>
        (L1_call scope_setup (measure_call dest_fn) scope_teardown f)
        (call scope_setup dest scope_teardown (\<lambda>_ t. Basic (f t)))"
  apply (clarsimp simp: L1corres_alt_def)
  apply (unfold call_def block_def L1_call_def)
  apply (rule ccorresE_DynCom)
  apply clarsimp
  apply (rule ccorresE_get)
  apply clarsimp
  apply (rule ccorresE_assume_pre, clarsimp)
  apply (rule ccorresE_guard_imp_stronger)
    apply (rule ccorresE_Seq)
     apply (rule ccorresE_Catch)
      apply (rule ccorresE_Seq)
       apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
      apply (clarsimp simp: measure_call_def ccorresE_def)
      apply (case_tac t)
         apply fastforce+
     apply (rule ccorresE_fail)
    apply (rule ccorresE_DynCom)
    apply (rule ccorresE_get)
    apply (rule ccorresE_assume_pre, clarsimp)
    apply (rule ccorresE_guard_imp)
      apply (rule ccorresE_Seq)
       apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
      apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
     apply simp
    apply simp
   apply simp
  apply simp
  done

lemma L1corres_reccall:
  "\<lbrakk> L1corres ct \<Gamma> (dest_fn m) (Call dest) \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma>
        (L1_call scope_setup (dest_fn m) scope_teardown f)
        (call scope_setup dest scope_teardown (\<lambda>_ t. Basic (f t)))"
  apply (clarsimp simp: L1corres_alt_def)
  apply (unfold call_def block_def L1_call_def)
  apply (rule ccorresE_DynCom)
  apply clarsimp
  apply (rule ccorresE_get)
  apply clarsimp
  apply (rule ccorresE_assume_pre, clarsimp)
  apply (rule ccorresE_guard_imp_stronger)
    apply (rule ccorresE_Seq)
     apply (rule ccorresE_Catch)
      apply (rule ccorresE_Seq)
       apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
      apply assumption
     apply (rule ccorresE_fail)
    apply (rule ccorresE_DynCom)
    apply (rule ccorresE_get)
    apply (rule ccorresE_assume_pre, clarsimp)
    apply (rule ccorresE_guard_imp)
      apply (rule ccorresE_Seq)
       apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
      apply (rule L1corres_modify[unfolded L1_modify_def L1corres_alt_def])
     apply simp
    apply simp
   apply simp
  apply simp
  done

lemma L1corres_fail:
  "L1corres ct \<Gamma> L1_fail X"
  apply (clarsimp simp: L1corres_alt_def)
  apply (clarsimp simp: L1_fail_def)
  apply (rule ccorresE_fail)
  done

lemma L1corres_recguard:
  "L1corres ct \<Gamma> A B \<Longrightarrow> L1corres ct \<Gamma> (L1_recguard n A) B"
  apply (clarsimp simp: L1_recguard_def)
  apply (case_tac "n = 0")
   apply clarsimp
   apply (rule L1corres_fail [unfolded L1_fail_def])
  apply clarsimp
  done

lemma L1corres_recguard_0:
  "L1corres ct \<Gamma> (L1_recguard 0 x) y"
  apply (clarsimp simp: L1_recguard_def)
  apply (rule L1corres_fail [unfolded L1_fail_def])
  done

lemma L1_recguard_cong [fundef_cong, cong]:
  "\<lbrakk> n = n'; n \<noteq> 0 \<Longrightarrow> b = b' \<rbrakk> \<Longrightarrow> L1_recguard n b = L1_recguard n' b'"
  apply (clarsimp simp: L1_recguard_def)
  done

lemma L1corres_prepend_unknown_var':
  "\<lbrakk> L1corres ct \<Gamma> A C; \<And>s::'s::type. X (\<lambda>_::'a::type. (X' s)) s = s \<rbrakk> \<Longrightarrow> L1corres ct \<Gamma> (L1_seq (L1_init X) A) C"
  apply atomize
  apply (clarsimp simp: L1corres_alt_def)
  apply (unfold L1_seq_def)
  apply (rule ccorresE_symb_exec_l, assumption)
   apply (subst L1_init_def)
   apply (clarsimp simp: exs_valid_def)
   apply (monad_eq simp: Bex_def)
   apply metis
  apply (subst L1_init_def)
  apply (wp del: hoare_vcg_prop)
  done

lemma L1_catch_seq_join: "no_throw \<top> A \<Longrightarrow> L1_seq A (L1_catch B C) = (L1_catch (L1_seq A B) C)"
  apply (monad_eq simp: L1_seq_def L1_catch_def Bex_def
             Ball_def no_throw_def' split: sum.splits)
  apply blast
  done

lemma no_throw_L1_init [simp]: "no_throw P (L1_init f)"
  apply (unfold L1_init_def)
  apply (rule no_throw_bindE [where B=\<top>])
    apply simp
   apply simp
  apply wp
  done

lemma L1corres_prepend_unknown_var:
  "\<lbrakk> L1corres ct \<Gamma> (L1_catch A B) C; \<And>s. X (\<lambda>_::'d::type. (X' s)) s = s \<rbrakk>
         \<Longrightarrow> L1corres ct \<Gamma> (L1_catch (L1_seq (L1_init X) A) B) C"
  apply atomize
  apply (clarsimp simp: L1corres_alt_def)
  apply (unfold L1_seq_def L1_catch_def)
  apply (subst bindE_handleE_join [symmetric])
   apply simp
  apply (erule L1corres_prepend_unknown_var' [unfolded L1_seq_def L1_spec_def L1corres_alt_def])
  apply force
  done

lemma L1corres_prepend_unknown_var_recguard:
  "\<lbrakk> L1corres ct \<Gamma> (L1_recguard n A) C; \<And>s. X (\<lambda>_::'a::type. X' s) s = s\<rbrakk>
    \<Longrightarrow> L1corres ct \<Gamma> (L1_recguard n (L1_seq (L1_init X) A)) C"
  apply (clarsimp simp: L1_recguard_def)
  apply (case_tac n)
   apply clarsimp
  apply clarsimp
  apply (erule L1corres_prepend_unknown_var')
  apply assumption
  done

lemma L1corres_Call:
  "\<lbrakk> \<Gamma> X' = Some Z'; L1corres ct \<Gamma> Z Z' \<rbrakk> \<Longrightarrow>
    L1corres ct \<Gamma> Z (Call X')"
  apply (clarsimp simp: L1corres_alt_def)
  apply (erule (1) ccorresE_Call)
  done

lemma L1_call_corres [fundef_cong]:
  "\<lbrakk> scope_setup = scope_setup';
     dest_fn = dest_fn';
     scope_teardown = scope_teardown';
     return_xf = return_xf' \<rbrakk> \<Longrightarrow>
    L1_call scope_setup dest_fn scope_teardown return_xf =
    L1_call scope_setup' dest_fn' scope_teardown' return_xf'"
  apply (clarsimp simp: L1_call_def)
  done

(* Saying \<And>measure is the same thing as \<And>s *)
lemma L1corres_measure_from_state:
  "\<And>\<Gamma> l1_f m f. (\<And>(measure' :: nat). L1corres ct \<Gamma> (l1_f measure') f) \<Longrightarrow> L1corres ct \<Gamma> (\<lambda>s. l1_f (m s) s) f"
  apply (unfold L1corres_def)
  apply simp
  done

declare recguard_dec_def [termination_simp]

(*
 * Implementation of functions that have no bodies.
 *
 * For example, if the user has a call to an "extern" function,
 * but no body is available to the C parser, we do not have any
 * SIMPL to translate. We instead use the following definition.
 *)

definition "UNDEFINED_FUNCTION \<equiv> False"

definition
  undefined_function_body :: "('a, int, strictc_errortype) com"
where
  "undefined_function_body \<equiv> Guard UndefinedFunction {x. UNDEFINED_FUNCTION} SKIP"

lemma L1corres_undefined_call:
    "L1corres ct \<Gamma> ((L1_seq (L1_guard (L1_set_to_pred {x. UNDEFINED_FUNCTION})) L1_skip)) (Call X')"
  by (clarsimp simp: L1corres_def L1_defs UNDEFINED_FUNCTION_def)

(* L1 monad_mono rules *)
lemma monad_mono_step_recguard_dec_Suc:
  "monad_mono_step (\<lambda>m. f m) m \<Longrightarrow> monad_mono_step (\<lambda>m. f (recguard_dec m)) (Suc m)"
  by (simp add: monad_mono_step_def recguard_dec_def)

lemma L1_seq_monad_mono_step:
  "\<lbrakk> monad_mono_step f m; monad_mono_step g m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. L1_seq (f m) (g m)) m"
  by (simp add: L1_seq_def monad_mono_step_bindE)

lemma L1_condition_monad_mono_step:
  "\<lbrakk> monad_mono_step f m; monad_mono_step g m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. L1_condition C (f m) (g m)) m"
  by (simp add: L1_condition_def monad_mono_step_condition)

lemma L1_catch_monad_mono_step:
  "\<lbrakk> monad_mono_step f m; monad_mono_step g m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. L1_catch (f m) (g m)) m"
  by (simp add: L1_catch_def monad_mono_step_handleE)

lemma L1_while_monad_mono_step:
  "monad_mono_step B m \<Longrightarrow> monad_mono_step (\<lambda>m. L1_while C (B m)) m"
  by (simp add: L1_while_def monad_mono_step_whileLoopE)

lemma L1_recguard_monad_mono_step:
  "monad_mono_step f m \<Longrightarrow> monad_mono_step (\<lambda>m. L1_recguard m (f m)) m"
  by (simp add: L1_recguard_def monad_mono_step_def condition_def fail_def)

lemma L1_reccall_monad_mono_step:
  "monad_mono_step f m
   \<Longrightarrow> monad_mono_step (\<lambda>m. L1_call scope_setup (f m) scope_teardown return_xf) m"
  apply (simp add: L1_call_def)
  apply (force intro: monad_mono_step_bindE monad_mono_step_const monad_mono_step_handleE)
  done

(* unused *)
lemma L1_call_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_call scope_setup (measure_call f) scope_teardown return_xf) m"
  by (rule monad_mono_step_const)

lemma L1_skip_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_skip) m"
  by (rule monad_mono_step_const)

lemma L1_modify_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_modify f) m"
  by (rule monad_mono_step_const)

lemma L1_throw_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_throw) m"
  by (rule monad_mono_step_const)

lemma L1_spec_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_spec r) m"
  by (rule monad_mono_step_const)

lemma L1_guard_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_guard g) m"
  by (rule monad_mono_step_const)

lemma L1_fail_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_fail) m"
  by (rule monad_mono_step_const)

lemma L1_init_monad_mono_step:
  "monad_mono_step (\<lambda>_. L1_init v) m"
  by (rule monad_mono_step_const)

lemmas L1_monad_mono_step_rules =
  monad_mono_step_const
  L1_while_monad_mono_step
  L1_recguard_monad_mono_step
  L1_catch_monad_mono_step
  L1_seq_monad_mono_step
  L1_condition_monad_mono_step
  L1_reccall_monad_mono_step
  monad_mono_step_recguard_dec_Suc

(* Base case *)
lemma monad_mono_step_L1_recguard_0:
  "monad_mono_step (\<lambda>m. L1_recguard m (x m)) 0"
  by (monad_eq simp: monad_mono_step_def L1_recguard_def)


(* Unfolding rules to run prior to L1 translation. *)
named_theorems L1unfold
(* L1 postprocessing rules, used by ExceptionRewrite and SimplConv. *)
named_theorems L1except

end
