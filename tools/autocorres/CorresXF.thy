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
 * A stronger version of the "corres" framework, allowing return
 * relationships to reference state data.
 *)

theory CorresXF
imports
  CCorresE
  NonDetMonadEx
begin

(*
 * Refinement with return extraction on the concrete side:
 *
 * For any step on the concrete side, there is an equivalent step on
 * the abstract side.
 *
 * If the abstract step fails, we don't need refinement to hold.
 *)

definition "corresXF_simple st xf P M M' \<equiv>
  \<forall>s. (P s \<and> \<not> snd (M (st s))) \<longrightarrow> (\<forall>(r', t') \<in> fst (M' s).
        (xf r' t', st t') \<in> fst (M (st s))) \<and> \<not> snd (M' s)"

(*
 * A definition better suited to dealing with monads with exceptions.
 *)
definition "corresXF st ret_xf ex_xf P A C \<equiv>
    \<forall>s. P s \<and> \<not> snd (A (st s)) \<longrightarrow>
        (\<forall>(r, t) \<in> fst (C s).
          case r of
             Inl r \<Rightarrow> (Inl (ex_xf r t), st t) \<in> fst (A (st s))
           | Inr r \<Rightarrow> (Inr (ret_xf r t), st t) \<in> fst (A (st s)))
        \<and> \<not> snd (C s)"

(* corresXF can be defined in terms of corresXF_simple. *)
lemma corresXF_simple_corresXF:
  "(corresXF_simple st
       (\<lambda>x s. case x of
           Inl r \<Rightarrow> Inl (ex_state r s)
         | Inr r \<Rightarrow> (Inr (ret_state r s))) P M M')
  = (corresXF st ret_state ex_state P M M')"
  apply (clarsimp simp: corresXF_simple_def corresXF_def)
  apply (rule iffI)
   apply clarsimp
   apply (erule allE, erule impE, force)
   apply (clarsimp split: sum.splits cong del: unit.case_cong)
   apply (erule (1) my_BallE)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=s in allE)
  apply (clarsimp split: sum.splits cong del: unit.case_cong)
  apply (erule (1) my_BallE)
  apply clarsimp
  done

lemma corresXF_simpleI: "\<lbrakk>
    \<And>s' t' r'. \<lbrakk>P s'; \<not> snd (M (st s')); (r', t') \<in> fst (M' s')\<rbrakk>
        \<Longrightarrow> (xf r' t', st t') \<in> fst (M (st s'));
    \<And>s'. \<lbrakk>P s'; \<not> snd (M (st s')) \<rbrakk> \<Longrightarrow> \<not> snd (M' s')
  \<rbrakk> \<Longrightarrow> corresXF_simple st xf P M M'"
  apply atomize
  apply (clarsimp simp: corresXF_simple_def)
  done

lemma corresXF_I: "\<lbrakk>
    \<And>s' t' r'. \<lbrakk>P s'; \<not> snd (M (st s')); (Inr r', t') \<in> fst (M' s')\<rbrakk>
        \<Longrightarrow> (Inr (ret_state r' t'), st t') \<in> fst (M (st s'));
    \<And>s' t' r'. \<lbrakk>P s'; \<not> snd (M (st s')); (Inl r', t') \<in> fst (M' s')\<rbrakk>
        \<Longrightarrow> (Inl (ex_state r' t'), st t') \<in> fst (M (st s'));
    \<And>s'. \<lbrakk>P s'; \<not> snd (M (st s')) \<rbrakk> \<Longrightarrow> \<not> snd (M' s')
  \<rbrakk> \<Longrightarrow> corresXF st ret_state ex_state P M M'"
  apply atomize
  apply (clarsimp simp: corresXF_def)
  apply (erule_tac x=s in allE, erule (1) impE)
  apply (erule_tac x=s in allE, erule (1) impE)
  apply (erule_tac x=s in allE, erule (1) impE)
  apply (clarsimp split: sum.splits)
  apply auto
  done

lemma corresXF_assume_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s'; s = st s' \<rbrakk> \<Longrightarrow> corresXF st xf_normal xf_exception P L R \<rbrakk> \<Longrightarrow> corresXF st xf_normal xf_exception P L R"
  apply atomize
  apply (clarsimp simp: corresXF_def)
  apply force
  done

lemma corresXF_guard_imp:
  "\<lbrakk> corresXF st xf_normal xf_exception Q f g; \<And>s. P s \<Longrightarrow> Q s \<rbrakk>
      \<Longrightarrow> corresXF st xf_normal xf_exception P f g"
  apply (clarsimp simp: corresXF_def)
  done

lemma corresXF_return:
  "\<lbrakk> \<And>s. \<lbrakk> P s \<rbrakk> \<Longrightarrow> xf_normal b s = a \<rbrakk> \<Longrightarrow>
     corresXF st xf_normal xf_exception P (returnOk a) (returnOk b)"
  apply (clarsimp simp: corresXF_def return_def returnOk_def)
  done

lemma corresXF_getsE:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> ret (g s) s = f (st s) \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (getsE f) (getsE g)"
  apply (monad_eq simp: corresXF_def getsE_def modifyE_def Ball_def split: sum.splits)
  done

lemma corresXF_insert_guard:
  "\<lbrakk> corresXF st ret ex Q A C; \<And>s. \<lbrakk> P s \<rbrakk> \<Longrightarrow> G (st s) \<longrightarrow> Q s  \<rbrakk> \<Longrightarrow>
        corresXF st ret ex P (guardE G >>=E (\<lambda>_. A)) C "
  apply (monad_eq simp: corresXF_def getsE_def modifyE_def Ball_def guardE_def split: sum.splits)
  done

lemma corresXF_exec_abs_guard:
  "corresXF st ret_xf ex_xf (\<lambda>s. P s \<and> G (st s)) (A ()) C \<Longrightarrow> corresXF st ret_xf ex_xf P (guardE G >>=E A) C"
  apply (clarsimp simp: guardE_def liftE_bindE)
  apply (monad_eq simp: corresXF_def Ball_def split: sum.splits)
  done

lemma corresXF_simple_exec:
  "\<lbrakk> corresXF_simple st xf P A B; (r', s') \<in> fst (B s); \<not> snd (A (st s)); P s \<rbrakk>
      \<Longrightarrow> (xf r' s', st s') \<in> fst (A (st s))"
  apply (fastforce simp: corresXF_simple_def)
  done

lemma corresXF_simple_fail:
  "\<lbrakk> corresXF_simple st xf P A B; snd (B s); P s \<rbrakk>
      \<Longrightarrow> snd (A (st s))"
  apply (fastforce simp: corresXF_simple_def)
  done

lemma corresXF_simple_no_fail:
  "\<lbrakk> corresXF_simple st xf P A B; \<not> snd (A (st s)); P s \<rbrakk>
      \<Longrightarrow> \<not> snd (B s)"
  apply (fastforce simp: corresXF_simple_def)
  done

lemma corresXF_exec_normal:
  "\<lbrakk> corresXF st ret ex P A B; (Inr r', s') \<in> fst (B s); \<not> snd (A (st s)); P s \<rbrakk>
      \<Longrightarrow> (Inr (ret r' s'), st s') \<in> fst (A (st s))"
  using corresXF_simple_exec
  apply (clarsimp simp: corresXF_def)
  apply (clarsimp split: sum.splits)
  apply (erule_tac x=s in allE)
  apply clarsimp
  apply (erule (1) my_BallE)
  apply clarsimp
  done

lemma corresXF_exec_except:
  "\<lbrakk> corresXF st ret ex P A B; (Inl r', s') \<in> fst (B s); \<not> snd (A (st s)); P s \<rbrakk>
      \<Longrightarrow> (Inl (ex r' s'), st s') \<in> fst (A (st s))"
  apply (clarsimp simp: corresXF_def)
  apply (erule allE, erule impE, force)
  apply (clarsimp)
  apply (erule (1) my_BallE)
  apply (clarsimp split: sum.splits)
  done

lemma corresXF_exec_fail:
  "\<lbrakk> corresXF st ret ex P A B; snd (B s); P s \<rbrakk>
      \<Longrightarrow> snd (A (st s))"
  apply (subst (asm) corresXF_simple_corresXF[symmetric])
  apply (auto elim!: corresXF_simple_fail)
  done

lemma corresXF_intermediate:
    "\<lbrakk> corresXF st ret_xf ex_xf P A' C;
         corresXF id (\<lambda>r s. r) (\<lambda>r s. r) (\<lambda>s. \<exists>x. s = st x \<and> P x) A A' \<rbrakk> \<Longrightarrow>
        corresXF st ret_xf ex_xf P A C"
  apply (clarsimp simp: corresXF_def split: sum.splits)
  apply fast
  done


(*
 * We can join two "corresXF_simple" statements together, if we can
 * show that the second statement's precondition always holds after
 * executing the first statement.
 *)
lemma corresXF_simple_join:
  assumes left_refines: "corresXF_simple st xf P L L'"
  and right_refines: "\<And>x y. corresXF_simple st xf' (P' x y) (R x) (R' y)"
  and precond_established: "\<lbrace> Q \<rbrace> L' \<lbrace> \<lambda>r s. P' (xf r s) r s \<rbrace>"
  and q_implies_p: "\<And>s. Q s \<Longrightarrow> P s"
  shows "corresXF_simple st xf' Q (L >>= R) (L' >>= R')"
  (is "corresXF_simple _ _ _ ?abs ?conc")
proof (rule corresXF_simpleI)
  fix s' t' r'
  let ?s = "st s'"
  let ?t = "st t'"
  let ?r = "xf' r' t'"
  assume s'_valid: "Q s'"
    and abs_no_fail: " \<not> snd (?abs ?s)"
    and final_state_exists: "(r', t') \<in> fst (?conc s')"
  show "(?r, ?t) \<in> fst (?abs ?s)"
  proof -
    (* Give a name to the middle concrete state "mid_s'". *)
    obtain mid_s' mid_r'
      where "(mid_r', mid_s') \<in> fst (L' s') \<and> (r', t') \<in> fst (R' mid_r' mid_s')"
      by (metis final_state_exists in_bind)
    note mid_asms = this

    (* mid_s' obeys the second refinement's precondition. *)
    have mid_s'_valid: "P' (xf mid_r' mid_s') mid_r' mid_s'"
      using mid_asms precond_established s'_valid use_valid
      by fastforce

    have left_refinement_step: "(xf mid_r' mid_s', st mid_s') \<in> fst (L ?s)"
      apply (insert left_refines s'_valid abs_no_fail mid_asms q_implies_p)
      apply (drule not_snd_bindI1)
      apply (clarsimp simp: corresXF_simple_def)
      apply force
      done

    have right_refinement_step: "(xf' r' t', st t') \<in> fst (R (xf mid_r' mid_s') (st mid_s'))"
      apply (insert right_refines [where x="xf mid_r' mid_s'" and y="mid_r'"])
      apply (insert mid_s'_valid abs_no_fail mid_asms)
      apply (clarsimp simp: corresXF_simple_def)
      apply (drule not_snd_bindI2)
       apply (rule left_refinement_step)
      apply force
      done

    show ?thesis
      apply (clarsimp simp: in_bind)
      apply (insert left_refinement_step right_refinement_step)
      apply force
      done
  qed
next
  fix s' t' r'
  let ?s = "st s'"
  let ?t = "st t'"
  assume s'_valid: "Q s'"
    and abs_no_fail: " \<not> snd (?abs ?s)"
  show "\<not> snd (?conc s')"
    apply (insert left_refines right_refines s'_valid abs_no_fail precond_established)
    apply (insert not_snd_bindI1 [OF abs_no_fail] q_implies_p)
    apply atomize
    apply (clarsimp simp: snd_bind)
    apply (clarsimp simp: corresXF_simple_def)
    apply (frule (2) use_valid)
    apply force
    done
qed

lemma corresXF_join:
  "\<lbrakk> corresXF st V E P L L'; \<And>x y. corresXF st V' E (P' x y) (R x) (R' y); \<lbrace> Q \<rbrace> L' \<lbrace> \<lambda>r s. P' (V r s) r s \<rbrace>, \<lbrace> \<lambda>_. \<top> \<rbrace>; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
    corresXF st V' E Q (L >>=E R) (L' >>=E R')"
  apply (subst (asm) corresXF_simple_corresXF[symmetric])+
  apply (subst corresXF_simple_corresXF[symmetric])
  apply (unfold bindE_def)
  apply (erule corresXF_simple_join [where P'="\<lambda>a b s. (case b of Inl r \<Rightarrow> a = Inl (E r s) | Inr r \<Rightarrow> a = Inr (V r s) \<and> P' (theRight a) r s)"])
    apply (simp add: corresXF_simple_def split: sum.splits unit.splits)
    apply (clarsimp simp: NonDetMonad.lift_def
      throwError_def return_def split: sum.splits
      cong del: unit.case_cong)
    apply fastforce
   apply (fastforce simp: NonDetMonad.validE_def split: sum.splits cong del: unit.case_cong)
  apply simp
  done

lemma corresXF_except:
  "\<lbrakk> corresXF st V E P L L'; \<And>x y. corresXF st V E' (P' x y) (R x) (R' y); \<lbrace> Q \<rbrace> L' \<lbrace> \<lambda>_. \<top> \<rbrace>, \<lbrace> \<lambda>r s. P' (E r s) r s \<rbrace>; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
    corresXF st V E' Q ( L <handle2> R) (L' <handle2> R')"
  apply (subst (asm) corresXF_simple_corresXF[symmetric])+
  apply (subst corresXF_simple_corresXF[symmetric])
  apply (unfold handleE'_def)
  apply (erule corresXF_simple_join [where P'="\<lambda>a b s. (case b of Inr r \<Rightarrow> a = Inr (V r s) | Inl r \<Rightarrow> a = Inl (E r s) \<and> P' (theLeft a) r s)"])
    apply (simp add: corresXF_simple_def split: sum.splits unit.splits)
    apply (clarsimp simp: NonDetMonad.lift_def throwError_def
      return_def split: sum.splits unit.splits cong del:
      unit.case_cong)
    apply fastforce
   apply (clarsimp simp: NonDetMonad.validE_def split: sum.splits cong del: unit.case_cong)
  apply simp
  done

lemma corresXF_cond:
  "\<lbrakk> corresXF st V E P L L'; corresXF st V E P R R'; \<And>s. P s \<Longrightarrow> A (st s) = A' s \<rbrakk> \<Longrightarrow>
    corresXF st V E P (condition A L R) (condition A' L' R')"
  apply atomize
  apply (clarsimp simp: corresXF_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=s in allE)
  apply (clarsimp split: condition_splits)
  done

(* The concrete loop "B" terminates if the abstract loop "A" also terminates. *)
lemma corresXF_simple_loop_terminates:
  assumes induct: "whileLoop_terminates C' A r' s'"
     and s_match1: "s' = st s"
     and s_match2: "r' = xf r s"
     and body_corres: "\<And>x y. corresXF_simple st xf (\<lambda>s. P y s \<and> x = xf y s) (A x) (B y)"
     and no_fail: "\<not> snd (whileLoop C' A r' s')"
     and cond_match: "\<And>s r. P r s \<Longrightarrow> C r s = C' (xf r s) (st s)"
     and precond: "P r s"
     and pred_inv: "\<And>r. \<lbrace> \<lambda>s. P r s \<and> C r s \<and> \<not> snd (whileLoop C' A (xf r s) (st s)) \<rbrace> B r \<lbrace> \<lambda>r s. P r s \<rbrace>"
  shows "whileLoop_terminates C B r s"
  apply (insert induct s_match1 s_match2 no_fail precond)
  apply (induct arbitrary: r s rule: whileLoop_terminates.induct)
   apply (rule whileLoop_terminates.intros)
   apply (clarsimp simp: cond_match)
  apply clarsimp
  apply (insert body_corres)
  apply (clarsimp simp: corresXF_simple_def)
  apply (frule snd_whileLoop_first_step)
   apply (clarsimp simp: cond_match)
  apply atomize
  apply clarsimp
  apply (erule allE2)
  apply (erule impE)
   apply (erule conjI)
   apply (clarsimp simp: cond_match)
  apply clarsimp
  apply (rule whileLoop_terminates.intros(2))
   apply (clarsimp simp: cond_match)
  apply (clarsimp split: sum.splits)
  apply (erule (1) my_BallE)
  apply clarsimp
  apply (erule (1) my_BallE)
  apply clarsimp
  apply (erule_tac x=a and y=b in allE2)
  apply clarsimp
  apply (frule use_valid [OF _ pred_inv])
    apply (clarsimp simp: no_fail_def)
   apply (clarsimp simp: cond_match)
  apply (frule (1) snd_whileLoop_unfold)
   apply simp
  apply simp
  done

lemma validE_by_corresXF:
     "\<lbrakk> corresXF st ret_xf ex_xf P A C;
       \<And>r s. Q' (ret_xf r s) (st s) \<Longrightarrow> Q r s;
       \<And>r s. E' (ex_xf r s) (st s) \<Longrightarrow> E r s;
       validE P' A Q' E';
       no_fail P' A;
       \<And>s. P s \<Longrightarrow> P' (st s) \<rbrakk>
     \<Longrightarrow> validE P C Q E"
  apply atomize
  apply (clarsimp simp: corresXF_def validE_def valid_def no_fail_def split_def split: sum.splits)
  apply fastforce
  done

lemma nofail_by_corresXF:
     "\<lbrakk> corresXF st ret_xf ex_xf (\<lambda>s. P' (st s)) A C;
        no_fail  P' A;
        \<And>s. P s \<Longrightarrow> P' (st s) \<rbrakk> \<Longrightarrow>
      no_fail P C"
  apply (clarsimp simp: corresXF_def validE_def valid_def no_fail_def split_def split: sum.splits)
  done

lemma corresXF_simple_snd_whileLoop:
  assumes body_corres: "\<And>x y. corresXF_simple st xf (\<lambda>s. P x s \<and> y = xf x s) (A y) (B x)"
  and cond_match: "\<And>s r. P r s \<Longrightarrow> C r s = C' (xf r s) (st s)"
  and pred_inv: "\<And>r. \<lbrace> \<lambda>s. P r s \<and> C r s \<and> \<not> snd (whileLoop C' A (xf r s) (st s)) \<rbrace> B r \<lbrace> \<lambda>r s. P r s \<rbrace>"
  and pred_eq: "\<And>s. P' x s \<Longrightarrow> y = xf x s"
  and pred_imply: "\<And>s. P' x s \<Longrightarrow> P x s"
  and P: "P' x s"
  and no_fail_abs: "\<not> snd (whileLoop C' A y (st s))"
  shows "\<not> snd (whileLoop C B x s)"
proof -
  (* If the concrete body fails, so will the abstract body. *)
  have conc_fail_impl_abs_fail:
       "\<And>r s. \<lbrakk> P r s; snd (B r s) \<rbrakk> \<Longrightarrow> snd (A (xf r s) (st s))"
    by (metis (mono_tags) body_corres corresXF_simple_fail)

  have pred_eq': "y = xf x s"
    by (auto intro: pred_eq P)

  (* If the abstract loop terminates, so will the concrete
   * loop. *)
  have loop_term: "whileLoop_terminates C' A (xf x s) (st s) \<Longrightarrow> whileLoop_terminates C B x s"
    apply (erule corresXF_simple_loop_terminates [where xf=xf and st=st and P="\<lambda>r s. P r s"])
          apply simp
         apply simp
        apply fact
       apply (metis P no_fail_abs pred_eq)
      apply fact
     apply (metis P pred_imply)
    apply fact
    done

 (* Assume that the concrete spec fails. Thus,
   * the abstract spec will also fail. *)
  {
    assume conc_fail: "snd (whileLoop C B x s)"
    have "snd (whileLoop C' A (xf x s) (st s))"
      using pred_imply [OF P] pred_eq'
      proof (induct arbitrary: y rule: snd_whileLoop_induct [OF conc_fail])
        (* If the concrete loop doesn't terminate,
         * we need to prove that the abstract loop fails. *)
        fix i
        assume no_term: "\<not> whileLoop_terminates C B x s"
        show ?thesis
          by (metis loop_term no_term snd_conv whileLoop_def)
      next
        fix r s i
        assume conc_body_fail: "snd (B r s)"
        assume cond_true: "C r s"
        assume pred_eq: "i = xf r s"
        assume P: "P r s"

        (* If the concrete body is going to fail, so must the
         * abstract body. *)
        have "snd (A (xf r s) (st s))"
          by (metis P conc_body_fail conc_fail_impl_abs_fail pred_eq)

        thus "snd (whileLoop C' A (xf r s) (st s))"
          by (metis P cond_match cond_true pred_eq snd_whileLoop_first_step)
      next
        fix r s i r' s'
        assume P: "P r s"
        assume cond_true: "C r s"
        assume conc_step: "(r', s') \<in> fst (B r s)"
        assume conc_fail: "snd (whileLoop C B r' s')"
        assume cond_induct: "\<And>i. \<lbrakk> P r' s'; i = xf r' s' \<rbrakk> \<Longrightarrow> snd (whileLoop C' A (xf r' s') (st s'))"
        assume pred_eq: "i = xf r s"

        show "snd (whileLoop C' A (xf r s) (st s))"
        proof (rule ccontr)
          assume abs_no_fail: "\<not> snd (whileLoop C' A (xf r s) (st s))"

          (* As the abstract doesn't fail, it must refine. *)
          have abs_step: "(xf r' s', st s') \<in> fst (A (xf r s) (st s))"
            apply (rule corresXF_simple_exec [OF body_corres conc_step _ ])
             apply (rule snd_whileLoop_first_step [OF abs_no_fail])
             apply (metis cond_true cond_match P)
            apply (clarsimp simp: P pred_imply)
            done

          (* The intermediate step fulfills the precondition. *)
          have P_step: "P r' s'"
            apply (rule use_valid [OF conc_step pred_inv])
            apply (metis cond_true P pred_eq abs_no_fail)
            done

          (* Inductive condition is true. *)
          have abs_induct: "snd (whileLoop C' A (xf r' s') (st s'))"
            by (metis P_step cond_induct)

          show False
            by (metis (full_types) P abs_induct abs_no_fail abs_step cond_match cond_true pred_eq snd_whileLoop_unfold)
        qed
      qed
  }

  thus "\<not> snd (whileLoop C B x s)"
    by (metis no_fail_abs pred_eq')
qed

lemma corresXF_simple_while:
  assumes body_corres: "\<And>x y. corresXF_simple st xf (\<lambda>s. P x s \<and> y = xf x s) (A y) (B x)"
  and cond_match: "\<And>s r. P r s \<Longrightarrow> C r s = C' (xf r s) (st s)"
  and pred_inv: "\<And>r. \<lbrace> \<lambda>s. P r s \<and> C r s \<and> \<not> snd (whileLoop C' A (xf r s) (st s)) \<rbrace> B r \<lbrace> \<lambda>r s. P r s \<rbrace>"
  and pred_imply: "\<And>s. P' x s \<Longrightarrow> P x s"
  and pred_init: "\<And>s. P' x s \<Longrightarrow> y = xf x s"
  shows "corresXF_simple st xf (P' x) (whileLoop C' A y) (whileLoop C B x)"
proof (clarsimp simp: corresXF_simple_def, rule conjI, clarsimp)
  fix r s t
  assume P: "P' x s"
  assume no_fail: "\<not> snd (whileLoop C' A y (st s))"
  assume result: "(r, t) \<in> fst (whileLoop C B x s)"

  have pred_eq': "y = xf x s"
    by (auto intro: pred_init P)

  have "\<not> snd (whileLoop C B x s)"
    apply (rule corresXF_simple_snd_whileLoop [where B=B and C=C and P=P,
        OF body_corres cond_match pred_inv pred_init])
    apply (simp | fact)+
    done

  have "(xf r t, st t) \<in> fst (whileLoop C' A (xf x s) (st s))"
    using result pred_imply [OF P] no_fail pred_eq'
    proof (induct arbitrary: y rule: in_whileLoop_induct)
      (* If the condition is false... *)
      fix r r' s
      assume neg_cond: "\<not> C r s"
      assume P: "P r s"
      assume match': "r' = xf r s"

      (* The while loop is never executed. *)
      have "(whileLoop C' A (xf r s) (st s)) = (return (xf r s) (st s))"
        by (metis P cond_match neg_cond match' whileLoop_cond_fail)

      (* Thus, we trivally refine. *)
      thus "(xf r s, st s) \<in> fst (whileLoop C' A (xf r s) (st s))"
        by (metis in_return)
    next
      (* Otherwise, we hit the inductive case. *)
      fix r s r' s' r'' s'' i
      assume cond: "C r s"
      assume step: "(r', s') \<in> fst (B r s)"
      assume rest: "(r'', s'') \<in> fst (whileLoop C B r' s')"
      assume abs_induct: "\<And>y. \<lbrakk> P r' s'; \<not> snd (whileLoop C' A y (st s')); y = xf r' s' \<rbrakk>
                 \<Longrightarrow> (xf r'' s'', st s'') \<in> fst (whileLoop C' A (xf r' s') (st s'))"
      assume no_fail: "\<not> snd (whileLoop C' A i (st s))"
      assume precond: "P r s"
      assume match': "i = xf r s"

      (* The abstract condition is also true. *)
      have abs_cond: "C' (xf r s) (st s)"
        by (metis cond cond_match precond)

      (* Abstract step doesn't fail. *)
      have abs_no_fail: "\<not> snd (A (xf r s) (st s))"
        by (metis abs_cond no_fail snd_whileLoop_first_step match')

      (* P is true on the intermediate state. *)
      have mid_P: "P r' s'"
        apply (insert use_valid [where f="B r", OF step pred_inv])
        apply (metis cond no_fail precond match')
        done

      (* The intermediate abstract state refines. *)
      have abs_step: "(xf r' s', st s') \<in> fst (A (xf r s) (st s))"
        apply (rule corresXF_simple_exec [OF body_corres])
        apply (rule step)
         apply (insert snd_whileLoop_first_step [OF no_fail])
         apply (metis abs_cond match')
        apply (metis precond)
        done

      (* Further, our assumptions for the abstract inductive case
       * are true. *)
      have "(xf r'' s'', st s'') \<in> fst (whileLoop C' A (xf r' s') (st s'))"
        by (metis abs_cond abs_induct abs_step mid_P no_fail match'
           snd_whileLoop_unfold)

      (* The intermediate abstract state refines. *)
      thus "(xf r'' s'', st s'') \<in> fst (whileLoop C' A (xf r s) (st s))"
        apply (subst whileLoop_unroll)
        apply (monad_eq simp: abs_cond abs_step)
        apply (metis abs_step)
        done
   qed

   thus "(xf r t, st t) \<in> fst (whileLoop C' A y (st s))"
     by (metis P pred_init)
next
  fix s
  assume P: "P' x s"
  assume no_fail: "\<not> snd (whileLoop C' A y (st s))"

  show "\<not> snd (whileLoop C B x s)"
    apply (rule corresXF_simple_snd_whileLoop [OF body_corres])
    apply fact+
    done
qed

lemma corresXF_simple_weaken_pre:
  "\<lbrakk> corresXF_simple st xf P A C; \<And>s. P' s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> corresXF_simple st xf P' A C"
  by (clarsimp simp: corresXF_simple_def)

lemma corresXF_simple_cong:
  "\<lbrakk> st = st'; xf = xf'; \<And>s. P s = P' s; \<And>s. P' s \<Longrightarrow> A (st s) = A' (st s); \<And>s. P' s \<Longrightarrow> B s = B' s \<rbrakk>
      \<Longrightarrow>  corresXF_simple st xf P A B = corresXF_simple st xf P' A' B'"
  by (auto simp: corresXF_simple_def)

lemma corresXF_while:
  assumes body_corres: "\<And>x y. corresXF st ret ex (\<lambda>s. P x s \<and> y = ret x s) (\<lambda>s. A y s) (B x)"
  and cond_match: "\<And>s r. P r s \<Longrightarrow> C r s = C' (ret r s) (st s)"
  and pred_inv: "\<And>r. \<lbrace> \<lambda>s. P r s \<and> C r s \<and> \<not> snd (whileLoopE C' A (ret r s) (st s)) \<rbrace>
                          B r \<lbrace> \<lambda>r s. P r s \<rbrace>,\<lbrace> \<lambda>_ _. True \<rbrace>"
  and init_match: "\<And>s. P' x s \<Longrightarrow> y = ret x s"
  and pred_imply: "\<And>s. P' x s \<Longrightarrow> P x s"
  shows "corresXF st ret ex (P' x) (whileLoopE C' A y) (whileLoopE C B x)"
  apply (subst corresXF_simple_corresXF[symmetric])
  apply (clarsimp simp: whileLoopE_def)
  apply (rule corresXF_simple_weaken_pre)
   apply (rule corresXF_simple_while [where
      P ="\<lambda>x s. (case x of Inl _ \<Rightarrow> True| Inr v \<Rightarrow>  P v s)"
                  and P'="\<lambda>x s. P' (theRight x) s"])
       apply (insert body_corres)[1]
       apply (subst (asm) corresXF_simple_corresXF[symmetric])
       apply atomize
       apply (erule_tac x="theRight x" in allE)
       apply (clarsimp simp: corresXF_simple_def NonDetMonad.lift_def
      throwError_def return_def split: sum.splits)
      apply (clarsimp simp: cond_match split: sum.splits)
     apply (clarsimp simp: lift_def split: sum.splits)
     apply (cut_tac  pred_inv [unfolded validE_def, simplified lift_def])
     apply (erule hoare_chain)
      apply (monad_eq simp: NonDetMonad.lift_def whileLoopE_def split: sum.splits)
     apply monad_eq
    apply (clarsimp simp: pred_imply split: sum.splits)
   apply (clarsimp simp: init_match pred_imply)
  apply clarsimp
  done

lemma corresXF_name_pre:
  "\<lbrakk> \<And>s'. corresXF st ret ex (\<lambda>s. P s \<and> s = s') A C \<rbrakk> \<Longrightarrow>
           corresXF st ret ex P A C"
  by (clarsimp simp: corresXF_def)

lemma corresXF_guarded_while_body:
  "corresXF st ret ex P A B \<Longrightarrow>
      corresXF st ret ex P
             (doE r \<leftarrow> A; _ \<leftarrow> guardE (G r); returnOk r odE) B"
    apply (monad_eq simp: corresXF_def guardE_def split_def split: sum.splits)
    apply force
    done

lemma corresXF_guarded_while:
  assumes body_corres: "\<And>x y. corresXF st ret ex (\<lambda>s. P x s \<and> y = ret x s) (\<lambda>s. A y s) (B x)"
  and cond_match: "\<And>s r. \<lbrakk> P r s; G (ret r s) (st s) \<rbrakk> \<Longrightarrow> C r s = C' (ret r s) (st s)"
  and pred_inv: "\<And>r. \<lbrace> \<lambda>s. P r s \<and> C r s \<and> \<not> snd (whileLoopE C' A (ret r s) (st s)) \<and> G (ret r s) (st s) \<rbrace>
                          B r \<lbrace> \<lambda>r s. G (ret r s) (st s) \<longrightarrow> P r s \<rbrace>,\<lbrace> \<lambda>_ _. True \<rbrace>"
  and pred_imply: "\<And>s. \<lbrakk> G y (st s); P' x s \<rbrakk> \<Longrightarrow> P x s"
  and init_match: "\<And>s. \<lbrakk> G y (st s); P' x s \<rbrakk> \<Longrightarrow> y = ret x s"
  shows "corresXF st ret ex (P' x)
      (doE
         _ \<leftarrow> guardE (G y);
         whileLoopE C' (\<lambda>i. (doE
            r \<leftarrow> A i;
            _ \<leftarrow> guardE (G r);
            returnOk r
          odE)) y
       odE)
      (whileLoopE C B x)"
proof -
  have new_body_fails_more:
    "\<And>i s. snd (whileLoopE C' A i s) \<Longrightarrow>
                snd ((whileLoopE C' (\<lambda>i.
                       (doE r \<leftarrow> A i;
                            _ \<leftarrow> guardE (G r);
                            returnOk r
                        odE))) i s)"
    apply (unfold whileLoopE_def)
    apply (erule snd_whileLoop_subset)
     apply (monad_eq simp: guardE_def split: sum.splits prod.splits)
     apply (case_tac r')
      apply clarsimp
     apply clarsimp
    apply monad_eq
    done

  note new_body_corres = body_corres [THEN corresXF_guarded_while_body]

  show ?thesis
    apply (rule corresXF_exec_abs_guard)
    apply (rule corresXF_name_pre)
    apply (rule corresXF_assume_pre)
    apply clarsimp
    apply (rule corresXF_guard_imp)
     apply (rule_tac P'="\<lambda>x s. P' x s \<and> s = s'" in corresXF_while [
         where P="\<lambda>x s. P x s \<and> G (ret x s) (st s)"])
         apply (rule corresXF_guard_imp)
          apply (rule new_body_corres)
         apply (clarsimp)
        apply (clarsimp)
        apply (rule cond_match, simp, simp)
       apply (cut_tac r=r in pred_inv)
       apply (clarsimp simp: validE_def2 split: sum.splits)
       apply (erule_tac x=s in allE)
       apply clarsimp
       apply (frule snd_whileLoopE_first_step)
        apply (clarsimp simp: cond_match)
       apply (subgoal_tac "\<not> snd (A (ret r s) (st s))")
        apply (frule (1) corresXF_exec_normal [OF new_body_corres])
         apply (clarsimp)
        apply (erule impE)
         apply (erule contrapos_nn)
         apply (erule new_body_fails_more)
        apply (erule (1) my_BallE)
        apply clarsimp
        apply (monad_eq simp: cond_match guardE_def split_def  split: sum.splits)
       apply (drule snd_whileLoopE_first_step)
        apply (clarsimp simp: cond_match)
       apply monad_eq
      apply clarsimp
      apply (metis init_match)
     apply (clarsimp simp: init_match)
     apply (metis init_match pred_imply)
    apply (clarsimp simp: pred_imply)
  done
qed

(* Merge of lemmas ccorresE and corresXF. *)
definition "ac_corres st check_termination \<Gamma> rx G \<equiv>
  \<lambda>A B. \<forall>s. (G s \<and> \<not> snd (A (st s))) \<longrightarrow>
         (\<forall>t. \<Gamma> \<turnstile> \<langle>B, Normal s\<rangle> \<Rightarrow> t \<longrightarrow>
            (\<exists>s'. t = Normal s' \<and> (Inr (rx s'), st s') \<in> fst (A (st s))))
          \<and> (check_termination \<longrightarrow> \<Gamma> \<turnstile> B \<down> Normal s)"

(* We can merge ccorresE and corresXF to form a ccorresXF statement. *)
lemma ccorresE_corresXF_merge:
  "\<lbrakk> ccorresE st1 ct \<Gamma> \<top> G1 M B;
     corresXF st2 rx ex G2 A M;
     no_throw \<top> A;
     \<And>s. st s = st2 (st1 s);
     \<And>r s. rx' s = rx r (st1 s);
     \<And>s. G s \<longrightarrow> (s \<in> G1 \<and> G2 (st1 s)) \<rbrakk> \<Longrightarrow>
    ac_corres st ct \<Gamma> rx' G A B"
  apply (unfold ac_corres_def)
  apply clarsimp
  apply (clarsimp simp: ccorresE_def)
  apply (clarsimp simp: corresXF_def)
  apply (erule allE, erule impE, force)
  apply (erule allE, erule impE, force)
  apply clarsimp
  apply (erule allE, erule impE, force)
  apply (case_tac t)
     apply clarsimp
     apply (erule (1) my_BallE)
     apply (clarsimp split: sum.splits)
    apply clarsimp
    apply (erule (1) my_BallE)
    apply (clarsimp split: sum.splits)
    apply (drule no_throw_Inr, assumption)
     apply simp
    apply (clarsimp split: sum.splits)
   apply clarsimp
  apply simp
  done

(* We can also merge corresXF statements. *)
lemma corresXF_corresXF_merge:
  "\<lbrakk> corresXF st rx ex P A B; corresXF st' rx' ex' P' B C \<rbrakk> \<Longrightarrow>
    corresXF (st o st') (\<lambda>rv s. rx (rx' rv s) (st' s))
             (\<lambda>rv s. ex (ex' rv s) (st' s)) (\<lambda>s. P' s \<and> P (st' s)) A C "
  apply (clarsimp simp: corresXF_def split: sum.splits)
  apply force
  done

lemma ac_corres_guard_imp:
  "\<lbrakk> ac_corres st ct G rx P A C; \<And>s. P' s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> ac_corres st ct G rx P' A C"
  apply atomize
  apply (clarsimp simp: ac_corres_def)
  done

lemma hoarep_from_ac_corres:
  "\<lbrakk> ac_corres st ct G rx P' A C; \<lbrace> \<lambda>s. P s \<rbrace> A \<lbrace> \<lambda>rv s. Q rv s \<rbrace>, \<lbrace> \<lambda>rv s. True \<rbrace>!; \<And>s. P (st s) \<Longrightarrow> P' s \<rbrakk>
    \<Longrightarrow> hoarep G \<Theta> F {s. P (st s) } C {s. Q (rx s) (st s) } E"
  apply (clarsimp simp: ac_corres_def)
  apply (rule hoare_complete')
  apply (rule allI)
  apply (rule cnvalidI)
  apply (drule execn_to_exec)
  apply clarsimp
  apply (erule_tac x=s in allE)
  apply (erule impE)
   apply (rule conjI)
    apply simp
   apply (clarsimp simp add: validE_NF_alt_def)
   apply (metis validNF_no_fail no_failD)
  apply clarsimp
  apply (erule allE, erule (1) impE)
  apply clarsimp
  apply (drule validE_NF_valid)
  apply (rule imageI)
  apply (rule CollectI)
  apply (clarsimp simp: validE_def valid_def)
  apply force
  done

lemma hoaret_from_ac_corres:
  "\<lbrakk> ac_corres st ct G rx P' A C; \<lbrace> \<lambda>s. P s \<rbrace> A \<lbrace> \<lambda>rv s. Q rv s \<rbrace>, \<lbrace> \<lambda>rv s. True \<rbrace>!;
        \<And>s. P (st s) \<Longrightarrow> P' s; ct \<rbrakk>
    \<Longrightarrow> hoaret G \<Theta> F {s. P (st s) } C {s. Q (rx s) (st s) } E"
  apply (rule TerminationPartial)
   apply (erule (1) hoarep_from_ac_corres, simp)
  apply (clarsimp simp: ac_corres_def validE_NF_def validNF_def no_fail_def)
  done

(*
 * Rules to use the corresXF definitions.
 *)

lemma corresXF_modify_local:
  "\<lbrakk> \<And>s. st s = st (M s); \<And>s. P s \<Longrightarrow> ret () (M s) = x \<rbrakk>
      \<Longrightarrow> corresXF st ret ex P (returnOk x) (modifyE M)"
  apply (monad_eq simp: corresXF_def modifyE_def Ball_def split: sum.splits)
  done

lemma corresXF_modify_global:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> M (st s) = st (M' s) \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (modifyE M) (modifyE M')"
  apply (monad_eq simp: corresXF_def modifyE_def Ball_def split: sum.splits)
  done

lemma corresXF_select_modify:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s); \<And>s. P s \<Longrightarrow> ret () (M s) \<in> x \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (selectE x) (modifyE M)"
  apply (monad_eq simp: corresXF_def modifyE_def selectE_def Ball_def split: sum.splits)
  done

lemma corresXF_select_select:
  "\<lbrakk> \<And>s a. st s = st (M (a::('a \<Rightarrow> ('a::{type}))) s);
         \<And>s x. \<lbrakk> P s; x \<in> b\<rbrakk> \<Longrightarrow> ret x s \<in> a \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (selectE a) (selectE b)"
  apply (monad_eq simp: corresXF_def selectE_def Ball_def split: sum.splits)
  done

lemma corresXF_modify_gets:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s); \<And>s. P s \<Longrightarrow> ret () (M s) = f (st (M s)) \<rbrakk> \<Longrightarrow>
     corresXF st ret ex P (getsE f) (modifyE M)"
  apply (monad_eq simp: corresXF_def getsE_def modifyE_def Ball_def split: sum.splits)
  done

lemma corresXF_guard:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> G' s =  G (st s) \<rbrakk> \<Longrightarrow> corresXF st ret ex P (guardE G) (guardE G')"
  apply (monad_eq simp: corresXF_def guardE_def Ball_def split: sum.splits)
  done

lemma corresXF_fail:
  "corresXF st return_xf exception_xf P fail X"
  apply (monad_eq simp: corresXF_def split: sum.splits)
  done

lemma corresXF_spec:
  "\<lbrakk> \<And>s s'. ((s, s') \<in> A') = ((st s, st s') \<in> A); surj st \<rbrakk>
    \<Longrightarrow>  corresXF st ret ex P (specE A) (specE A')"
  apply (monad_eq simp: corresXF_def specE_def spec_def Ball_def split: sum.splits)
  apply (frule_tac y=s' in surjD)
  apply (clarsimp simp: image_def set_eq_UNIV)
  apply metis
  done

lemma corresXF_throw:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> E B s = A \<rbrakk> \<Longrightarrow> corresXF st V E P (throwError A) (throwError B)"
  apply (monad_eq simp: corresXF_def split: sum.splits)
  done

lemma corresXF_simple_append_gets_abs:
  assumes corres: "corresXF_simple st ret P L R"
  and consistent: "\<lbrace>P\<rbrace> R \<lbrace>\<lambda>r s. M (ret r s) (st s) = ret' r s\<rbrace>"
  shows "corresXF_simple st ret' P (L >>= (\<lambda>r. gets (M r))) R"
  (is "corresXF_simple st ret' P ?lhs R")
proof (clarsimp simp: corresXF_simple_def, rule conjI)
  fix s
   assume P: "P s"
   assume no_fail: "\<not> snd (?lhs (st s))"
   show  "\<forall>(r', t') \<in> fst (R s). (ret' r' t', st t') \<in> fst (?lhs (st s))"
  using no_fail
  apply monad_eq
  apply (metis P use_valid [OF _ consistent]
       corresXF_simple_exec [OF corres, where s=s])
  done
next
   fix s
   assume P: "P s"
   assume no_fail: "\<not> snd (?lhs (st s))"

   have "\<not> snd (L (st s))"
     by (metis no_fail not_snd_bindI1)

   thus  "\<not> snd (R s)"
     by (metis P corres corresXF_simple_fail)
qed

lemma bindE_to_getsE_simp:
    "(L >>=E (\<lambda>x. getsE (F x))) = (L >>= (\<lambda>x. gets (\<lambda>s. case x of Inl a \<Rightarrow> Inl a | Inr b \<Rightarrow> Inr (F b s))))"
  apply (rule ext)+
  apply (monad_eq simp: bindE_def  in_bind_split Bex_def getsE_def in_lift split: sum.splits)
  apply blast
  done

lemma corresXF_append_gets_abs:
  assumes corres: "corresXF st ret ex P L R"
  and consistent: "\<lbrace>P\<rbrace> R \<lbrace>\<lambda>r s. M (ret r s) (st s) = ret' r s \<rbrace>, \<lbrace> \<lambda>_. \<top> \<rbrace>"
  shows "corresXF st ret' ex P (L >>=E (\<lambda>r. getsE (M r))) R"
  apply (insert corres consistent)
  apply (clarsimp simp: corresXF_simple_corresXF[symmetric] bindE_to_getsE_simp)
  apply (erule corresXF_simple_append_gets_abs)
  apply (clarsimp simp: validE_def valid_def split: sum.splits)
  done

lemma corresXF_skipE:
  "corresXF st ret ex P skipE skipE"
  apply (monad_eq simp: corresXF_def skipE_def)
  done

lemma corresXF_id:
    "corresXF id (\<lambda>r s. r) (\<lambda>r s. r) P M M"
  by (fastforce simp: corresXF_def split: sum.splits)

lemma corresXF_cong:
  "\<lbrakk> \<And>s. st s = st' s;
     \<And>s r. ret_xf r s = ret_xf' r s;
     \<And>s r. ex_xf r s = ex_xf' r s;
     \<And>s. P s = P' s;
     \<And>s s'. P' s' \<Longrightarrow> A s = A' s;
     \<And>s. P' s \<Longrightarrow> C s = C' s \<rbrakk> \<Longrightarrow>
           corresXF st ret_xf ex_xf P A C = corresXF st' ret_xf' ex_xf' P' A' C'"
   apply atomize
   apply (clarsimp simp: corresXF_def split: sum.splits)
   apply (case_tac "Ex P")
    apply presburger
   apply force
   done

lemma corresXF_exec_abs_select:
  "\<lbrakk> x \<in> Q; x \<in> Q \<Longrightarrow> corresXF id rx ex P (A x) A' \<rbrakk> \<Longrightarrow> corresXF id rx ex P (selectE Q >>=E A) A'"
  apply (clarsimp simp: corresXF_def)
  apply (erule_tac x=s in allE)
  apply (erule impE)
   apply (monad_eq simp: selectE_def Ball_def split: sum.splits)
   apply blast
  apply clarsimp
  apply (monad_eq simp: selectE_def Ball_def split: sum.splits)
  apply blast
  done

end
