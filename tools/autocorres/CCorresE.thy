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
 * A simple CCorres framework extension supporting exceptions on the monadic side.
 *)

theory CCorresE
imports SimplBucket NonDetMonadEx
begin

(*
 * A special form of "ccorres" where either side may throw an
 * exception if the other also throws an exception.
 *)
definition
  ccorresE :: "('t \<Rightarrow> 's) \<Rightarrow> bool \<Rightarrow> ('p \<Rightarrow> ('t, 'p, 'ee) com option)
                        \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t set)
                        \<Rightarrow> ('s, unit + unit) nondet_monad \<Rightarrow> ('t, 'p, 'ee) com \<Rightarrow> bool"
where
  "ccorresE st check_term \<Gamma> G G' \<equiv>
   \<lambda>m c. \<forall>s. G (st s) \<and> (s \<in> G') \<and> \<not> snd (m (st s)) \<longrightarrow>
  ((\<forall>t. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
   (case t of
         Normal s' \<Rightarrow> (Inr (), st s') \<in> fst (m (st s))
       | Abrupt s' \<Rightarrow> (Inl (), st s') \<in> fst (m (st s))
       | _ \<Rightarrow> False))
   \<and> (check_term \<longrightarrow> \<Gamma> \<turnstile> c \<down> Normal s))"

lemma ccorresE_cong:
  "\<lbrakk> \<And>s. P s = P' s;
     \<And>s. (s \<in> Q) = (s \<in> Q');
     \<And>s. P' s \<Longrightarrow> f s = f' s;
     \<And>s x. s \<in> Q' \<Longrightarrow> \<Gamma>\<turnstile> \<langle>g, Normal s\<rangle> \<Rightarrow> x = \<Gamma>\<turnstile> \<langle>g', Normal s\<rangle> \<Rightarrow> x \<rbrakk> \<Longrightarrow>
  ccorresE st ct \<Gamma> P Q f g = ccorresE st ct \<Gamma> P' Q' f' g"
  apply atomize
  apply (clarsimp simp: ccorresE_def split: xstate.splits)
  apply (rule iffI)
   apply clarsimp
  apply clarsimp
  done

lemma ccorresE_guard_imp:
  "\<lbrakk> ccorresE st ct \<Gamma> Q Q' A B; \<And>s. P s \<Longrightarrow> Q s; \<And>t. t \<in> P' \<Longrightarrow> t \<in> Q' \<rbrakk>  \<Longrightarrow> ccorresE st ct \<Gamma> P P' A B"
  apply atomize
  apply (clarsimp simp: ccorresE_def split: xstate.splits)
  done

lemma ccorresE_guard_imp_stronger:
  "\<lbrakk> ccorresE st ct \<Gamma> Q Q' A B;
     \<And>s. \<lbrakk> P (st s); s \<in> P' \<rbrakk> \<Longrightarrow> Q (st s);
     \<And>s. \<lbrakk> P (st s); s \<in> P' \<rbrakk> \<Longrightarrow> s \<in> Q' \<rbrakk> \<Longrightarrow>
  ccorresE st ct \<Gamma> P P' A B"
  apply atomize
  apply (clarsimp simp: ccorresE_def split_def split: xstate.splits)
  done

lemma ccorresE_assume_pre:
  "\<lbrakk> \<And>s. \<lbrakk> G (st s); s \<in> G' \<rbrakk> \<Longrightarrow>
         ccorresE st ct \<Gamma> (G and (\<lambda>s'. s' = st s)) (G' \<inter> {t'. t' = s}) A B \<rbrakk> \<Longrightarrow>
     ccorresE st ct \<Gamma> G G' A B"
  apply atomize
  apply (clarsimp simp: ccorresE_def)
  done

lemma ccorresE_Seq:
  "\<lbrakk> ccorresE st ct \<Gamma> \<top> UNIV L L';
     ccorresE st ct \<Gamma> \<top> UNIV R R' \<rbrakk> \<Longrightarrow>
   ccorresE st ct \<Gamma> \<top> UNIV (doE _ \<leftarrow> L; R odE) (L' ;; R')"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
   apply (clarsimp simp: bindE_def split: xstate.splits)
   apply (frule not_snd_bindI1)
   apply (rotate_tac 1, erule allE, erule impE, force)
   apply (monad_eq simp: split_def Bex_def Ball_def split: sum.splits)
   apply (case_tac s', simp_all)[1]
     apply fast
    apply (erule exec_elim_cases)
    apply fastforce
   apply (erule exec_elim_cases)
   apply clarsimp
   apply auto[1]
  apply clarsimp
  apply (rule terminates.Seq)
   apply monad_eq
  apply (monad_eq simp: Bex_def split_def split: xstate.splits)
  apply (metis Abrupt xstate.exhaust)
  done

lemma ccorresE_Cond:
  "\<lbrakk> ccorresE st ct \<Gamma> \<top> C A L';
     ccorresE st ct \<Gamma> \<top> (UNIV - C) A R' \<rbrakk> \<Longrightarrow>
   ccorresE st ct \<Gamma> \<top> UNIV A (Cond C L' R')"
  apply (clarsimp simp: ccorresE_def pred_neg_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (erule_tac x=s in allE, erule impE, fastforce, fastforce)
   apply (erule_tac x=s in allE, erule impE, fastforce, fastforce)
  apply clarsimp
  apply (case_tac "s \<in> C")
   apply (rule terminates.CondTrue, assumption)
   apply (erule allE, erule impE, fastforce)
   apply clarsimp
  apply (rule terminates.CondFalse, assumption)
  apply (erule allE, erule impE, fastforce)
  apply clarsimp
  done

lemma ccorresE_Cond_match:
  "\<lbrakk> ccorresE st ct \<Gamma> C C' L L';
     ccorresE st ct \<Gamma> (not C) (UNIV - C') R R';
     \<And>s. C (st s) = (s \<in> C') \<rbrakk> \<Longrightarrow>
   ccorresE st ct \<Gamma> \<top> UNIV (condition C L R) (Cond C' L' R')"
  apply atomize
  apply (clarsimp simp: ccorresE_def pred_neg_def condition_def)
  apply (erule_tac x=s in allE)+
  apply (auto elim!: exec_Normal_elim_cases intro: terminates.CondTrue terminates.CondFalse)
  done

lemma ccorresE_Guard:
  "\<lbrakk> ccorresE st ct \<Gamma> \<top> G X Y \<rbrakk> \<Longrightarrow>  ccorresE st ct \<Gamma> \<top> G X (Guard F G Y)"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases, auto)[1]
  apply clarsimp
  apply (rule terminates.Guard, assumption)
  apply force
  done

lemma ccorresE_Catch:
  "\<lbrakk>ccorresE st ct \<Gamma> \<top> UNIV A A'; ccorresE st ct \<Gamma> \<top> UNIV B B'\<rbrakk> \<Longrightarrow>
    ccorresE st ct \<Gamma> \<top> UNIV (A <handle> (\<lambda>_. B)) (TRY A' CATCH B' END)"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x=s in allE)
   apply (erule exec_Normal_elim_cases)
    apply (monad_eq simp: Bex_def Ball_def split: xstate.splits)
    apply metis
   apply (monad_eq simp: Bex_def Ball_def split: xstate.splits)
   apply fastforce
  apply (monad_eq simp: Bex_def Ball_def split: xstate.splits)
  apply (erule allE, erule (1) impE)
  apply clarsimp
  apply (erule terminates.Catch)
  apply clarsimp
  done

lemma ccorresE_Call:
  "\<lbrakk> \<Gamma> X' = Some Z'; ccorresE st ct \<Gamma> \<top> UNIV Z Z' \<rbrakk> \<Longrightarrow>
    ccorresE st ct \<Gamma> \<top> UNIV Z (Call X')"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (clarsimp)
   apply clarsimp
  apply clarify
  apply (erule terminates.Call)
  apply (erule allE, erule (1) impE)
  apply clarsimp
  done

lemma ccorresE_exec_Normal:
    "\<lbrakk> ccorresE st ct \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Normal t; s \<in> G'; G (st s); \<not> snd (B (st s)) \<rbrakk> \<Longrightarrow> (Inr (), st t) \<in> fst (B (st s))"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_Abrupt:
    "\<lbrakk> ccorresE st ct \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Abrupt t; s \<in> G'; G (st s); \<not> snd (B (st s)) \<rbrakk> \<Longrightarrow> (Inl (), st t) \<in> fst (B (st s))"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_Fault:
    "\<lbrakk> ccorresE st ct \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Fault f; s \<in> G'; G (st s); \<not> snd (B (st s)) \<rbrakk> \<Longrightarrow> P"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_Stuck:
    "\<lbrakk> ccorresE st ct \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> Stuck; s \<in> G'; G (st s); \<not> snd (B (st s)) \<rbrakk> \<Longrightarrow> P"
  apply (clarsimp simp: ccorresE_def)
  apply force
  done

lemma ccorresE_exec_cases [consumes 5]:
    "\<lbrakk> ccorresE st ct \<Gamma> G G' B B'; \<Gamma>\<turnstile> \<langle>B', Normal s\<rangle> \<Rightarrow> s'; s \<in> G'; G (st s); \<not> snd (B (st s));
                  \<And>t'. \<lbrakk> s' = Normal t'; (Inr (), st t') \<in> fst (B (st s)) \<rbrakk> \<Longrightarrow> R;
                  \<And>t'. \<lbrakk> s' = Abrupt t'; (Inl (), st t') \<in> fst (B (st s)) \<rbrakk> \<Longrightarrow> R
                  \<rbrakk> \<Longrightarrow> R"
  apply atomize
  apply (case_tac s')
     apply (drule ccorresE_exec_Normal, auto)[1]
    apply (drule ccorresE_exec_Abrupt, auto)[1]
   apply (drule ccorresE_exec_Fault, auto)[1]
  apply (drule ccorresE_exec_Stuck, auto)[1]
  done

lemma ccorresE_terminates:
  "\<lbrakk> ccorresE st ct \<Gamma> \<top> UNIV B B'; \<not> snd (B (st s)); ct \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> B' \<down> Normal s"
   by (clarsimp simp: ccorresE_def)

lemma exec_While_final_inv':
  assumes exec: "\<Gamma>\<turnstile> \<langle>b, x\<rangle> \<Rightarrow> s'"
   shows
  "\<lbrakk> b = While C B; x = Normal s;
    \<And>s. \<lbrakk> s \<notin> C \<rbrakk> \<Longrightarrow> I s (Normal s);
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Normal t'; I t' s' \<rbrakk> \<Longrightarrow> I t s';
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Abrupt t' \<rbrakk> \<Longrightarrow> I t (Abrupt t');
    \<And>t. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Stuck \<rbrakk> \<Longrightarrow> I t Stuck;
    \<And>t f. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Fault f \<rbrakk> \<Longrightarrow> I t (Fault f) \<rbrakk>
    \<Longrightarrow> I s s'"
  using exec
  apply (induct arbitrary: s rule: exec.induct, simp_all)
  apply clarsimp
  apply atomize
  apply clarsimp
  apply (erule allE, erule (1) impE)
  apply (erule exec_elim_cases, auto)
  done

lemma exec_While_final_inv:
  "\<lbrakk> \<Gamma>\<turnstile> \<langle>While C B, Normal s\<rangle> \<Rightarrow> s';
    \<And>s. \<lbrakk> s \<notin> C \<rbrakk> \<Longrightarrow> I s (Normal s);
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Normal t'; I t' s' \<rbrakk> \<Longrightarrow> I t s';
    \<And>t t'. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Abrupt t' \<rbrakk> \<Longrightarrow> I t (Abrupt t');
    \<And>t. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Stuck \<rbrakk> \<Longrightarrow> I t Stuck;
    \<And>t f. \<lbrakk> t \<in> C; \<Gamma>\<turnstile> \<langle>B, Normal t\<rangle> \<Rightarrow> Fault f \<rbrakk> \<Longrightarrow> I t (Fault f) \<rbrakk>
    \<Longrightarrow> I s s'"
   apply (erule exec_While_final_inv', (rule refl)+, simp_all)
   done

lemma not_snd_loop_terminatesE:
  "\<not> snd (whileLoopE C B r s) \<Longrightarrow> whileLoop_terminatesE C B r s"
  by (clarsimp simp: whileLoopE_def
      whileLoop_terminatesE_def whileLoop_def)

lemma ccorresE_termination':
  assumes no_fail: "\<not> snd (whileLoopE CC BB r s)"
  and s_match: "s = st s' \<and> CC = (\<lambda>_. C) \<and> BB = (\<lambda>_. B)"
  and corres: "ccorresE st ct \<Gamma> \<top> UNIV B B'"
  and cond_match: "\<And>s. C (st s) = (s \<in> C')"
  and ct: "ct"
  shows "\<Gamma>\<turnstile> While C' B' \<down> Normal s'"
  apply (insert not_snd_loop_terminatesE[OF no_fail] s_match)
  apply (insert no_fail)
  apply (induct arbitrary: s' rule: whileLoop_terminatesE_induct [where C=CC and B=BB])
   apply clarsimp
   apply (rule terminates.WhileFalse)
   apply (clarsimp simp: cond_match)
  apply (clarsimp simp: s_match split_def split: sum.splits)
  apply (insert corres)[1]
  apply (clarsimp simp: ccorresE_def s_match)
  apply (frule (1) snd_whileLoopE_first_step)
  apply (erule allE, erule (1) impE)
  apply (clarsimp simp: ct)
  apply (rule terminates.intros)
    apply (clarsimp simp: cond_match)
   apply clarsimp
  apply clarsimp
  apply (erule allE, erule (1) impE)
  apply (clarsimp split: sum.splits xstate.splits)
  apply (erule (1) my_BallE)
  apply clarsimp
  apply (erule allE, erule impE, rule refl)
  apply clarsimp
  apply (drule (1) snd_whileLoopE_unfold)
   apply simp
  apply simp
  done

lemma ccorresE_termination:
  assumes no_fail: "\<not> snd (whileLoopE (\<lambda>_. C) (\<lambda>_. B) r s)"
  and s_match: "s = st s'"
  and corres: "ccorresE st ct \<Gamma> \<top> UNIV B B'"
  and cond_match: "\<And>s. C (st s) = (s \<in> C')"
  and ct: "ct"
  shows "\<Gamma>\<turnstile> While C' B' \<down> Normal s'"
  apply (auto intro: ccorresE_termination' [OF no_fail _ corres _ ct] simp: s_match cond_match)
  done

lemma ccorresE_While:
  assumes body_refines: "ccorresE st ct \<Gamma> \<top> UNIV B B'"
      and cond_match: "\<And>s. C (st s) = (s \<in> C')"
    shows "ccorresE st ct \<Gamma> G G' (whileLoopE (\<lambda>_. C) (\<lambda>_. B) ()) (While C' B')"
 proof (clarsimp simp: ccorresE_def, rule conjI, clarsimp)
  fix s t
  assume guard_abs: "G (st s)"
  assume guard_conc: "s \<in> G'"

  assume no_fail: "\<not> snd (whileLoopE (\<lambda>_. C) (\<lambda>_. B) () (st s))"
  assume conc_steps: "\<Gamma>\<turnstile> \<langle>While C' B', Normal s\<rangle> \<Rightarrow> t"
  show "case t of
        Normal s' \<Rightarrow> (Inr (), st s') \<in> fst (whileLoopE (\<lambda>_. C) (\<lambda>_. B) () (st s))
      | Abrupt s' \<Rightarrow> (Inl (), st s') \<in> fst (whileLoopE (\<lambda>_. C) (\<lambda>_. B) () (st s))
      | _ \<Rightarrow> False"
    apply (insert no_fail, erule rev_mp)
    apply (rule exec_While_final_inv [OF conc_steps])
        apply clarsimp
        apply (subst whileLoopE_cond_fail)
         apply (force simp: cond_match)
        apply (force simp: in_returnOk)
       apply clarsimp
       apply (insert ccorresE_exec_Normal [OF body_refines])[1]
       apply clarsimp
       apply atomize
       apply (erule allE2, erule (1) impE)
       apply (frule snd_whileLoopE_first_step, force simp: cond_match)
       apply clarsimp
       apply (erule impE)
        apply (erule (1) snd_whileLoopE_unfold)
        apply (force simp: cond_match)
       apply (clarsimp split: xstate.splits)
        apply (subst whileLoopE_unroll)
        apply (monad_eq simp: cond_match)
        apply blast
       apply (subst whileLoopE_unroll)
       apply (monad_eq simp: cond_match)
      apply clarsimp
      apply (insert ccorresE_exec_Abrupt [OF body_refines])[1]
      apply clarsimp
      apply atomize
      apply (erule allE2, erule (1) impE)
      apply (frule snd_whileLoopE_first_step, force simp: cond_match)
      apply clarsimp
      apply (subst whileLoopE_unroll)
      apply (clarsimp simp: in_bindE in_returnOk cond_match split: condition_splits)
     apply (insert ccorresE_exec_Stuck [OF body_refines])[1]
     apply (rule impI)
     apply (frule snd_whileLoopE_first_step)
      apply (force simp: cond_match)
     apply force
    apply (insert ccorresE_exec_Fault [OF body_refines])[1]
    apply (rule impI)
    apply (frule snd_whileLoopE_first_step)
     apply (force simp: cond_match)
    apply force
    done
next
  fix s
  assume guard_abs: "G (st s)"
  assume guard_conc: "s \<in> G'"
  assume no_fail: "\<not> snd (whileLoopE (\<lambda>_. C) (\<lambda>_. B) () (st s))"
  show "ct \<longrightarrow> \<Gamma>\<turnstile>While C' B' \<down> Normal s"
    apply clarify
    apply (rule ccorresE_termination [OF no_fail])
       apply (rule refl)
      apply (rule body_refines)
     apply (rule cond_match)
    apply simp
    done
qed

lemma ccorresE_get:
  "(\<And>s. ccorresE st ct \<Gamma> (P and (\<lambda>s'. s' = s)) Q (L s) R) \<Longrightarrow> ccorresE st ct \<Gamma> P Q ((liftE get) >>=E L) R"
  apply atomize
  apply (clarsimp simp: liftE_def get_def bindE_def lift_def bind_def return_def)
  apply (clarsimp simp: ccorresE_def)
  done

lemma ccorresE_fail:
  "ccorresE st ct \<Gamma> P Q fail R"
  apply (clarsimp simp: ccorresE_def fail_def)
  done

lemma ccorresE_DynCom:
  "\<lbrakk> \<And>t. \<lbrakk> t \<in> P' \<rbrakk> \<Longrightarrow> ccorresE st ct \<Gamma> P (P' \<inter> {t'. t' = t}) A (B t) \<rbrakk> \<Longrightarrow> ccorresE st ct \<Gamma> P P' A (DynCom B)"
  apply atomize
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
   apply (erule allE, erule(1) impE)
   apply clarsimp
  apply clarify
  apply (rule terminates.DynCom)
  apply clarsimp
  done

lemma ccorresE_Catch_nothrow:
  "\<lbrakk>ccorresE st ct \<Gamma> \<top> UNIV A A'; \<not> exceptions_thrown A'\<rbrakk> \<Longrightarrow>
    ccorresE st ct \<Gamma> \<top> UNIV A (TRY A' CATCH B' END)"
  apply (clarsimp simp: ccorresE_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (frule exceptions_thrown_not_abrupt, simp, simp)
    apply simp
   apply simp
  apply clarify
  apply (rule terminates.Catch)
   apply clarsimp
  apply clarsimp
  apply (drule (1) exceptions_thrown_not_abrupt)
   apply simp
  apply simp
  done

lemma ccorresE_symb_exec_l:
  "\<lbrakk> \<And>x. ccorresE st ct \<Gamma> (P' x) Q (B x) C;
    \<And>s. P s \<Longrightarrow> \<lbrace> (=) s \<rbrace> A \<exists>\<lbrace> \<lambda>r' s'. (\<exists>a. r' = Inr a) \<and> s = s' \<rbrace>;
    \<lbrace> P \<rbrace> A \<lbrace> P' \<rbrace>,\<lbrace> \<lambda>_ _. False \<rbrace> \<rbrakk>
   \<Longrightarrow> ccorresE st ct \<Gamma> P Q (A >>=E B) C"
  apply atomize
  apply (clarsimp simp: ccorresE_def validE_def valid_def exs_valid_def)
  apply (erule allE, erule impE, assumption)+
  apply (clarsimp)
  apply (erule (1) my_BallE)
  apply clarsimp
  apply (erule_tac x=aa and y=s in allE2)
  apply clarsimp
  apply (monad_eq simp: Bex_def Ball_def split: xstate.splits)
  apply fastforce
  done

lemma ccorresE_no_fail_term:
  " \<lbrakk> ccorresE st ct \<Gamma> G G' A B; no_fail G A; s \<in> G'; G (st s); ct \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> B \<down> Normal s"
  apply (clarsimp simp: ccorresE_def no_fail_def)
  done

end
