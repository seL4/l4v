(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WhileLoopRules
imports "NonDetMonadVCG"
begin

section "Well-ordered measures"

(* A version of "measure" that takes any wellorder, instead of
 * being fixed to "nat". *)
definition measure' :: "('a \<Rightarrow> 'b::wellorder) => ('a \<times> 'a) set"
where "measure' = (\<lambda>f. {(a, b). f a < f b})"

lemma in_measure'[simp, code_unfold]:
    "((x,y) : measure' f) = (f x < f y)"
  by (simp add:measure'_def)

lemma wf_measure' [iff]: "wf (measure' f)"
  apply (clarsimp simp: measure'_def)
  apply (insert wf_inv_image [OF wellorder_class.wf, where f=f])
  apply (clarsimp simp: inv_image_def)
  done

lemma wf_wellorder_measure: "wf {(a, b). (M a :: 'a :: wellorder) < M b}"
  apply (subgoal_tac "wf (inv_image ({(a, b). a < b}) M)")
   apply (clarsimp simp: inv_image_def)
  apply (rule wf_inv_image)
  apply (rule wellorder_class.wf)
  done


section "whileLoop lemmas"

text {*
  The following @{const whileLoop} definitions with additional
  invariant/variant annotations allow the user to annotate
  @{const whileLoop} terms with information that can be used
  by automated tools.
*}
definition
  "whileLoop_inv (C :: 'a \<Rightarrow> 'b \<Rightarrow> bool) B x (I :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (R :: (('a \<times> 'b) \<times> ('a \<times> 'b)) set) \<equiv> whileLoop C B x"

definition
  "whileLoopE_inv (C :: 'a \<Rightarrow> 'b \<Rightarrow> bool) B x (I :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (R :: (('a \<times> 'b) \<times> ('a \<times> 'b)) set) \<equiv> whileLoopE C B x"

lemma whileLoop_add_inv: "whileLoop B C = (\<lambda>x. whileLoop_inv B C x I (measure' M))"
  by (clarsimp simp: whileLoop_inv_def)

lemma whileLoopE_add_inv: "whileLoopE B C = (\<lambda>x. whileLoopE_inv B C x I (measure' M))"
  by (clarsimp simp: whileLoopE_inv_def)

subsection "Simple base rules"

lemma whileLoop_terminates_unfold:
  "\<lbrakk> whileLoop_terminates C B r s; (r', s') \<in> fst (B r s); C r s \<rbrakk>
        \<Longrightarrow> whileLoop_terminates C B r' s'"
  apply (erule whileLoop_terminates.cases)
   apply simp
  apply force
  done

lemma snd_whileLoop_first_step: "\<lbrakk> \<not> snd (whileLoop C B r s); C r s \<rbrakk> \<Longrightarrow> \<not> snd (B r s)"
  apply (subst (asm) whileLoop_unroll)
  apply (clarsimp simp: bind_def condition_def)
  done

lemma snd_whileLoopE_first_step: "\<lbrakk> \<not> snd (whileLoopE C B r s); C r s \<rbrakk> \<Longrightarrow> \<not> snd (B r s)"
  apply (subgoal_tac "\<lbrakk> \<not> snd (whileLoopE C B r s); C r s \<rbrakk> \<Longrightarrow> \<not> snd ((lift B (Inr r)) s)")
   apply (clarsimp simp: lift_def)
  apply (unfold whileLoopE_def)
  apply (erule snd_whileLoop_first_step)
  apply clarsimp
  done

lemma snd_whileLoop_unfold:
      "\<lbrakk> \<not> snd (whileLoop C B r s); C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> \<not> snd (whileLoop C B r' s')"
  apply (clarsimp simp: whileLoop_def)
  apply (auto simp: elim: whileLoop_results.cases whileLoop_terminates.cases
     intro: whileLoop_results.intros whileLoop_terminates.intros)
  done

lemma snd_whileLoopE_unfold:
      "\<lbrakk> \<not> snd (whileLoopE C B r s); (Inr r', s') \<in> fst (B r s); C r s \<rbrakk> \<Longrightarrow> \<not> snd (whileLoopE C B r' s')"
  apply (clarsimp simp: whileLoopE_def)
  apply (drule snd_whileLoop_unfold)
    apply clarsimp
   apply (clarsimp simp: lift_def)
   apply assumption
  apply (clarsimp simp: lift_def)
  done

lemma whileLoop_results_cong [cong]:
  assumes C:  "\<And>r s. C r s = C' r s"
  and B:"\<And>(r :: 'r) (s :: 's). C' r s \<Longrightarrow> B r s = B' r s"
  shows "whileLoop_results C B = whileLoop_results C' B'"
proof -
  {
    fix x y C B C' B'
    have  "\<lbrakk> (x, y) \<in> whileLoop_results C B;
                 \<And>(r :: 'r) (s :: 's). C r s = C' r s;
                 \<And>r s. C' r s \<Longrightarrow> B r s = B' r s \<rbrakk>
               \<Longrightarrow> (x, y) \<in> whileLoop_results C' B'"
      apply (induct rule: whileLoop_results.induct)
         apply clarsimp
        apply clarsimp
       apply (rule whileLoop_results.intros, auto)[1]
      apply clarsimp
      apply (rule whileLoop_results.intros, auto)[1]
      done
  }

  thus ?thesis
    apply -
    apply (rule set_eqI, rule iffI)
     apply (clarsimp split: prod.splits)
     apply (clarsimp simp: C B split: prod.splits)
    apply (clarsimp split: prod.splits)
    apply (clarsimp simp: C [symmetric] B [symmetric] split: prod.splits)
  done
qed

lemma whileLoop_terminates_cong [cong]:
  assumes r: "r = r'"
  and s: "s = s'"
  and C: "\<And>r s. C r s = C' r s"
  and B: "\<And>r s. C' r s \<Longrightarrow> B r s = B' r s"
  shows "whileLoop_terminates C B r s = whileLoop_terminates C' B' r' s'"
proof (rule iffI)
  assume T: "whileLoop_terminates C B r s"
  show "whileLoop_terminates C' B' r' s'"
    apply (insert T r s)
    apply (induct arbitrary: r' s' rule: whileLoop_terminates.induct)
     apply (clarsimp simp: C)
     apply (erule whileLoop_terminates.intros)
    apply (clarsimp simp: C B split: prod.splits)
    apply (rule whileLoop_terminates.intros, assumption)
    apply (clarsimp simp: C B split: prod.splits)
    done
next
  assume T: "whileLoop_terminates C' B' r' s'"
  show "whileLoop_terminates C B r s"
    apply (insert T r s)
    apply (induct arbitrary: r s rule: whileLoop_terminates.induct)
     apply (rule whileLoop_terminates.intros)
     apply (clarsimp simp: C)
    apply (rule whileLoop_terminates.intros, fastforce simp: C)
    apply (clarsimp simp: C B split: prod.splits)
    done
qed

lemma whileLoop_cong [cong]:
  "\<lbrakk> \<And>r s. C r s = C' r s; \<And>r s. C r s \<Longrightarrow> B r s = B' r s \<rbrakk> \<Longrightarrow> whileLoop C B = whileLoop C' B'"
  apply (rule ext, clarsimp simp: whileLoop_def)
  done

lemma whileLoopE_cong [cong]:
  "\<lbrakk> \<And>r s. C r s = C' r s ; \<And>r s. C r s \<Longrightarrow> B r s = B' r s \<rbrakk>
                 \<Longrightarrow> whileLoopE C B = whileLoopE C' B'"
  apply (clarsimp simp: whileLoopE_def)
  apply (rule whileLoop_cong [THEN arg_cong])
    apply (clarsimp split: sum.splits)
   apply (clarsimp split: sum.splits)
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  done

lemma whileLoop_terminates_wf:
    "wf {(x, y). C (fst y) (snd y) \<and> x \<in> fst (B (fst y) (snd y)) \<and> whileLoop_terminates C B (fst y) (snd y)}"
  apply (rule wfI [where A="UNIV" and B="{(r, s). whileLoop_terminates C B r s}"])
   apply clarsimp
  apply clarsimp
  apply (erule whileLoop_terminates.induct)
   apply blast
  apply blast
  done

subsection "Basic induction helper lemmas"

lemma whileLoop_results_induct_lemma1:
    "\<lbrakk> (a, b) \<in> whileLoop_results C B; b = Some (x, y) \<rbrakk> \<Longrightarrow> \<not> C x y"
    apply (induct rule: whileLoop_results.induct, auto)
    done

lemma whileLoop_results_induct_lemma1':
    "\<lbrakk> (a, b) \<in> whileLoop_results C B; a \<noteq> b \<rbrakk> \<Longrightarrow> \<exists>x. a = Some x \<and> C (fst x) (snd x)"
    apply (induct rule: whileLoop_results.induct, auto)
    done

lemma whileLoop_results_induct_lemma2 [consumes 1]:
  "\<lbrakk> (a, b) \<in> whileLoop_results C B;
     a = Some (x :: 'a \<times> 'b); b = Some y;
     P x; \<And>s t. \<lbrakk> P s; t \<in> fst (B (fst s) (snd s)); C (fst s) (snd s) \<rbrakk> \<Longrightarrow> P t \<rbrakk> \<Longrightarrow> P y"
  apply (induct arbitrary: x y rule: whileLoop_results.induct)
    apply simp
   apply simp
  apply atomize
  apply fastforce
  done

lemma whileLoop_results_induct_lemma3 [consumes 1]:
  assumes result: "(Some (r, s), Some (r', s')) \<in> whileLoop_results C B"
  and inv_start: "I r s"
  and inv_step: "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> I r' s'"
  shows "I r' s'"
  apply (rule whileLoop_results_induct_lemma2 [where P="case_prod I" and y="(r', s')" and x="(r, s)",
      simplified case_prod_unfold, simplified])
      apply (rule result)
     apply simp
    apply simp
   apply fact
  apply (erule (1) inv_step)
  apply clarsimp
  done

subsection "Inductive reasoning about whileLoop results"

lemma in_whileLoop_induct [consumes 1]:
  assumes in_whileLoop: "(r', s') \<in> fst (whileLoop C B r s)"
  and init_I: "\<And> r s. \<not> C r s \<Longrightarrow> I r s r s"
  and step:
     "\<And>r s r' s' r'' s''.
        \<lbrakk> C r s; (r', s') \<in> fst (B r s);
          (r'', s'') \<in> fst (whileLoop C B r' s');
           I r' s' r'' s'' \<rbrakk> \<Longrightarrow> I r s r'' s''"
  shows "I r s r' s'"
proof cases
  assume "C r s"

  {
    obtain a where a_def: "a = Some (r, s)"
      by blast
    obtain b where b_def: "b = Some (r', s')"
      by blast

    have "\<lbrakk> (a, b) \<in> whileLoop_results C B; \<exists>x. a = Some x;  \<exists>x. b = Some x \<rbrakk>
        \<Longrightarrow> I (fst (the a)) (snd (the a)) (fst (the b)) (snd (the b))"
      apply (induct rule: whileLoop_results.induct)
      apply (auto simp: init_I whileLoop_def intro: step)
      done

    hence "(Some (r, s), Some (r', s')) \<in> whileLoop_results C B
                 \<Longrightarrow> I r s r' s'"
      by (clarsimp simp: a_def b_def)
   }

   thus ?thesis
     using in_whileLoop
     by (clarsimp simp: whileLoop_def)
next
  assume "\<not> C r s"

  hence "r' = r \<and> s' = s"
    using in_whileLoop
    by (subst (asm) whileLoop_unroll,
             clarsimp simp: condition_def return_def)

  thus ?thesis
    by (metis init_I `\<not> C r s`)
qed

lemma snd_whileLoop_induct [consumes 1]:
  assumes induct: "snd (whileLoop C B r s)"
  and terminates: "\<not> whileLoop_terminates C B r s \<Longrightarrow> I r s"
  and init: "\<And> r s. \<lbrakk> snd (B r s); C r s \<rbrakk> \<Longrightarrow> I r s"
  and step: "\<And>r s r' s' r'' s''.
        \<lbrakk> C r s; (r', s') \<in> fst (B r s);
           snd (whileLoop C B r' s');
           I r' s' \<rbrakk> \<Longrightarrow> I r s"
  shows "I r s"
  apply (insert init induct)
  apply atomize
  apply (unfold whileLoop_def)
  apply clarsimp
  apply (erule disjE)
   apply (erule rev_mp)
   apply (induct "Some (r, s)" "None :: ('a \<times> 'b) option"
        arbitrary: r s rule: whileLoop_results.induct)
    apply clarsimp
   apply clarsimp
   apply (erule (1) step)
    apply (clarsimp simp: whileLoop_def)
   apply clarsimp
  apply (metis terminates)
  done

lemma whileLoop_terminatesE_induct [consumes 1]:
  assumes induct: "whileLoop_terminatesE C B r s"
  and init: "\<And>r s. \<not> C r s \<Longrightarrow> I r s"
  and step: "\<And>r s r' s'. \<lbrakk> C r s; \<forall>(v', s') \<in> fst (B r s). case v' of Inl _ \<Rightarrow> True | Inr r' \<Rightarrow> I r' s' \<rbrakk> \<Longrightarrow> I r s"
  shows "I r s"
  apply (insert induct)
  apply (clarsimp simp: whileLoop_terminatesE_def)
  apply (subgoal_tac "(\<lambda>r s. case (Inr r) of Inl x \<Rightarrow> True | Inr x \<Rightarrow> I x s) r s")
   apply simp
  apply (induction rule: whileLoop_terminates.induct)
   apply (case_tac r)
    apply simp
   apply clarsimp
   apply (erule init)
  apply (clarsimp split: sum.splits)
  apply (rule step)
   apply simp
  apply (clarsimp simp: lift_def split: sum.splits)
  apply force
  done

subsection "Direct reasoning about whileLoop components"

lemma fst_whileLoop_cond_false:
  assumes loop_result: "(r', s') \<in> fst (whileLoop C B r s)"
  shows "\<not> C r' s'"
  using loop_result
  by (rule in_whileLoop_induct, auto)

lemma snd_whileLoop:
  assumes init_I: "I r s"
      and cond_I: "C r s"
      and non_term:  "\<And>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<and> \<not> snd (B r s) \<rbrace>
                                   B r \<exists>\<lbrace> \<lambda>r' s'. C r' s' \<and> I r' s' \<rbrace>"
      shows "snd (whileLoop C B r s)"
  apply (clarsimp simp: whileLoop_def)
  apply (rotate_tac)
  apply (insert init_I cond_I)
  apply (induct rule: whileLoop_terminates.induct)
   apply clarsimp
  apply (cut_tac r=r in non_term)
  apply (clarsimp simp: exs_valid_def)
   apply (subst (asm) (2) whileLoop_results.simps)
   apply clarsimp
  apply (insert whileLoop_results.simps)
  apply fast
  done

lemma whileLoop_terminates_inv:
  assumes init_I: "I r s"
  assumes inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> ((r', s'), (r, s)) \<in> R \<rbrace>"
  assumes wf_R: "wf R"
  shows "whileLoop_terminates C B r s"
  apply (insert init_I)
  using wf_R
  apply (induction "(r, s)" arbitrary: r s)
  apply atomize
  apply (subst whileLoop_terminates_simps)
  apply clarsimp
  apply (erule use_valid)
  apply (rule hoare_strengthen_post, rule inv)
   apply force
  apply force
  done

lemma not_snd_whileLoop:
  assumes init_I: "I r s"
      and inv_holds: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> ((r', s'), (r, s)) \<in> R \<rbrace>!"
      and wf_R: "wf R"
      shows "\<not> snd (whileLoop C B r s)"
proof -
  {
    fix x y
    have "\<lbrakk> (x, y) \<in> whileLoop_results C B; x = Some (r, s); y = None \<rbrakk> \<Longrightarrow> False"
      apply (insert init_I)
      apply (induct arbitrary: r s rule: whileLoop_results.inducts)
         apply simp
        apply simp
       apply (insert snd_validNF [OF inv_holds])[1]
       apply blast
      apply (drule use_validNF [OF _ inv_holds])
       apply simp
      apply clarsimp
      apply blast
      done
  }

  also have "whileLoop_terminates C B r s"
     apply (rule whileLoop_terminates_inv [where I=I, OF init_I _ wf_R])
     apply (insert inv_holds)
     apply (clarsimp simp: validNF_def)
     done

  ultimately show ?thesis
     by (clarsimp simp: whileLoop_def, blast)
qed

lemma valid_whileLoop:
  assumes first_step: "\<And>s. P r s \<Longrightarrow> I r s"
      and inv_step: "\<And>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>"
      and final_step: "\<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s"
   shows "\<lbrace> P r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"
proof -
  {
    fix r' s' s
    assume inv: "I r s"
    assume step: "(r', s') \<in> fst (whileLoop C B r s)"

    have "I r' s'"
     using step inv
      apply (induct rule: in_whileLoop_induct)
       apply simp
      apply (drule use_valid, rule inv_step, auto)
      done
  }

  thus ?thesis
    apply (clarsimp simp: valid_def)
    apply (drule first_step)
    apply (rule final_step, simp)
    apply (metis fst_whileLoop_cond_false)
    done
qed

lemma whileLoop_wp:
  "\<lbrakk> \<And>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>;
     \<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s \<rbrakk> \<Longrightarrow>
  \<lbrace> I r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"
  by (rule valid_whileLoop)

lemma whileLoop_wp_inv [wp]:
  "\<lbrakk> \<And>r. \<lbrace>\<lambda>s. I r s \<and> C r s\<rbrace> B r \<lbrace>I\<rbrace>; \<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s \<rbrakk>
      \<Longrightarrow> \<lbrace> I r \<rbrace> whileLoop_inv C B r I M \<lbrace> Q \<rbrace>"
  apply (clarsimp simp: whileLoop_inv_def)
  apply (rule valid_whileLoop [where P=I and I=I], auto)
  done

lemma validE_whileLoopE:
  "\<lbrakk>\<And>s. P r s \<Longrightarrow> I r s;
    \<And>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>,\<lbrace> A \<rbrace>;
    \<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s
   \<rbrakk> \<Longrightarrow> \<lbrace> P r \<rbrace> whileLoopE C B r \<lbrace> Q \<rbrace>,\<lbrace> A \<rbrace>"
  apply (clarsimp simp: whileLoopE_def validE_def)
  apply (rule valid_whileLoop [where I="\<lambda>r s. (case r of Inl x \<Rightarrow> A x s | Inr x \<Rightarrow> I x s)"
             and Q="\<lambda>r s. (case r of Inl x \<Rightarrow> A x s | Inr x \<Rightarrow> Q x s)"])
    apply atomize
    apply (clarsimp simp: valid_def lift_def split: sum.splits)
   apply (clarsimp simp: valid_def lift_def split: sum.splits)
  apply (clarsimp split: sum.splits)
  done

lemma whileLoopE_wp:
  "\<lbrakk> \<And>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>, \<lbrace> A \<rbrace>;
     \<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s \<rbrakk> \<Longrightarrow>
  \<lbrace> I r \<rbrace> whileLoopE C B r \<lbrace> Q \<rbrace>, \<lbrace> A \<rbrace>"
  by (rule validE_whileLoopE)

lemma exs_valid_whileLoop:
 assumes init_T: "\<And>s. P s \<Longrightarrow> T r s"
    and iter_I: "\<And> r s0.
         \<lbrace> \<lambda>s. T r s \<and> C r s \<and> s = s0 \<rbrace>
                B r \<exists>\<lbrace>\<lambda>r' s'. T r' s' \<and> ((r', s'),(r, s0)) \<in> R\<rbrace>"
    and wf_R: "wf R"
    and final_I: "\<And>r s. \<lbrakk> T r s; \<not> C r s  \<rbrakk> \<Longrightarrow> Q r s"
 shows "\<lbrace> P \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace>"
proof (clarsimp simp: exs_valid_def Bex_def)
  fix s
  assume "P s"

  {
    fix x
    have "T (fst x) (snd x) \<Longrightarrow>
             \<exists>r' s'. (r', s') \<in> fst (whileLoop C B (fst x) (snd x)) \<and> T r' s'"
      using wf_R
      apply induction
      apply atomize
      apply (case_tac "C (fst x) (snd x)")
       apply (subst whileLoop_unroll)
       apply (clarsimp simp: condition_def bind_def' split: prod.splits)
       apply (cut_tac ?s0.0=b and r=a in iter_I)
       apply (clarsimp simp: exs_valid_def)
       apply blast
      apply (subst whileLoop_unroll)
      apply (clarsimp simp: condition_def bind_def' return_def)
      done
  }

  thus "\<exists>r' s'. (r', s') \<in> fst (whileLoop C B r s) \<and> Q r' s'"
    by (metis `P s` fst_conv init_T snd_conv
                  final_I fst_whileLoop_cond_false)
qed

lemma empty_fail_whileLoop:
  assumes body_empty_fail: "\<And>r. empty_fail (B r)"
  shows "empty_fail (whileLoop C B r)"
proof -
  {
    fix s A
    assume empty: "fst (whileLoop C B r s) = {}"

    have cond_true: "\<And>x s. fst (whileLoop C B x s) = {} \<Longrightarrow> C x s"
      apply (subst (asm) whileLoop_unroll)
      apply (clarsimp simp: condition_def return_def split: if_split_asm)
      done

    have  "snd (whileLoop C B r s)"
      apply (rule snd_whileLoop [where I="\<lambda>x s. fst (whileLoop C B x s) = {}"])
        apply fact
       apply (rule cond_true, fact)
      apply (clarsimp simp: exs_valid_def)
      apply (case_tac "fst (B r s) = {}")
       apply (metis empty_failD [OF body_empty_fail])
      apply (subst (asm) whileLoop_unroll)
      apply (fastforce simp: condition_def bind_def split_def cond_true)
      done
   }

  thus ?thesis
    by (clarsimp simp: empty_fail_def)
qed

lemma empty_fail_whileLoopE:
  assumes body_empty_fail: "\<And>r. empty_fail (B r)"
  shows "empty_fail (whileLoopE C B r)"
  apply (clarsimp simp: whileLoopE_def)
  apply (rule empty_fail_whileLoop)
  apply (insert body_empty_fail)
  apply (clarsimp simp: empty_fail_def lift_def throwError_def return_def split: sum.splits)
  done

lemma whileLoop_results_bisim:
  assumes base: "(a, b) \<in> whileLoop_results C B"
  and vars1: "Q = (case a of Some (r, s) \<Rightarrow> Some (rt r, st s) | _ \<Rightarrow> None)"
  and vars2: "R = (case b of Some (r, s) \<Rightarrow> Some (rt r, st s) | _ \<Rightarrow> None)"
  and inv_init: "case a of Some (r, s) \<Rightarrow> I r s | _ \<Rightarrow> True"
  and inv_step: "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> I r' s'"
  and cond_match: "\<And>r s. I r s \<Longrightarrow> C r s = C' (rt r) (st s)"
  and fail_step: "\<And>r s. \<lbrakk>C r s; snd (B r s); I r s\<rbrakk>
          \<Longrightarrow> (Some (rt r, st s), None) \<in> whileLoop_results C' B'"
  and refine: "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in>  fst (B r s) \<rbrakk>
                           \<Longrightarrow> (rt r', st s') \<in> fst (B' (rt r) (st s))"
  shows "(Q, R) \<in> whileLoop_results C' B'"
  apply (subst vars1)
  apply (subst vars2)
  apply (insert base inv_init)
  apply (induct rule: whileLoop_results.induct)
    apply clarsimp
    apply (subst (asm) cond_match)
     apply (clarsimp simp: option.splits)
    apply (clarsimp simp: option.splits)
   apply (clarsimp simp: option.splits)
   apply (metis fail_step)
  apply (case_tac z)
   apply (clarsimp simp: option.splits)
  apply (metis cond_match inv_step refine whileLoop_results.intros(3))
   apply (clarsimp simp: option.splits)
 apply (metis cond_match inv_step refine whileLoop_results.intros(3))
 done

lemma whileLoop_terminates_liftE:
  "whileLoop_terminatesE C (\<lambda>r. liftE (B r)) r s = whileLoop_terminates C B r s"
  apply (subst eq_sym_conv)
  apply (clarsimp simp: whileLoop_terminatesE_def)
  apply (rule iffI)
   apply (erule whileLoop_terminates.induct)
    apply (rule whileLoop_terminates.intros)
    apply clarsimp
   apply (clarsimp simp: split_def)
   apply (rule whileLoop_terminates.intros(2))
    apply clarsimp
   apply (clarsimp simp: liftE_def in_bind return_def lift_def [abs_def]
               bind_def lift_def throwError_def o_def split: sum.splits
               cong: sum.case_cong)
   apply (drule (1) bspec)
   apply clarsimp
  apply (subgoal_tac "case (Inr r) of Inl _ \<Rightarrow> True | Inr r \<Rightarrow>
      whileLoop_terminates (\<lambda>r s. (\<lambda>r s. case r of Inl _ \<Rightarrow> False | Inr v \<Rightarrow> C v s) (Inr r) s)
           (\<lambda>r. (lift (\<lambda>r. liftE (B r)) (Inr r)) >>= (\<lambda>x. return (theRight x))) r s")
   apply (clarsimp simp: liftE_def lift_def)
  apply (erule whileLoop_terminates.induct)
   apply (clarsimp simp: liftE_def lift_def split: sum.splits)
   apply (erule whileLoop_terminates.intros)
  apply (clarsimp simp: liftE_def split: sum.splits)
  apply (clarsimp simp: bind_def return_def split_def lift_def)
  apply (erule whileLoop_terminates.intros)
  apply force
  done

lemma snd_X_return [simp]:
     "\<And>A X s. snd ((A >>= (\<lambda>a. return (X a))) s) = snd (A s)"
  by (clarsimp simp: return_def bind_def split_def)

lemma whileLoopE_liftE:
  "whileLoopE C (\<lambda>r. liftE (B r)) r = liftE (whileLoop C B r)"
  apply (rule ext)
  apply (clarsimp simp: whileLoopE_def)
  apply (rule prod_eqI)
   apply (rule set_eqI, rule iffI)
    apply clarsimp
    apply (clarsimp simp: in_bind whileLoop_def liftE_def)
    apply (rule_tac x="b" in exI)
    apply (rule_tac x="theRight a" in exI)
    apply (rule conjI)
     apply (erule whileLoop_results_bisim [where rt=theRight and st="\<lambda>x. x" and I="\<lambda>r s. case r of Inr x \<Rightarrow> True | _ \<Rightarrow> False"],
        auto intro: whileLoop_results.intros simp: bind_def return_def lift_def split: sum.splits)[1]
    apply (drule whileLoop_results_induct_lemma2 [where P="\<lambda>(r, s). case r of Inr x \<Rightarrow> True | _ \<Rightarrow> False"] )
        apply (rule refl)
       apply (rule refl)
      apply clarsimp
     apply (clarsimp simp: return_def bind_def lift_def split: sum.splits)
    apply (clarsimp simp: return_def bind_def lift_def split: sum.splits)
   apply (clarsimp simp: in_bind whileLoop_def liftE_def)
   apply (erule whileLoop_results_bisim [where rt=Inr and st="\<lambda>x. x" and I="\<lambda>r s. True"],
     auto intro: whileLoop_results.intros intro!: bexI simp: bind_def return_def lift_def split: sum.splits)[1]
  apply (rule iffI)
   apply (clarsimp simp: whileLoop_def liftE_def del: notI)
   apply (erule disjE)
    apply (erule whileLoop_results_bisim [where rt=theRight and st="\<lambda>x. x" and I="\<lambda>r s. case r of Inr x \<Rightarrow> True | _ \<Rightarrow> False"],
      auto intro: whileLoop_results.intros simp: bind_def return_def lift_def split: sum.splits)[1]
   apply (subst (asm) whileLoop_terminates_liftE [symmetric])
   apply (fastforce simp: whileLoop_def liftE_def whileLoop_terminatesE_def)
  apply (clarsimp simp: whileLoop_def liftE_def del: notI)
  apply (subst (asm) whileLoop_terminates_liftE [symmetric])
  apply (clarsimp simp: whileLoop_def liftE_def whileLoop_terminatesE_def)
  apply (erule disjE)
   apply (erule whileLoop_results_bisim [where rt=Inr and st="\<lambda>x. x" and I="\<lambda>r s. True"])
         apply (clarsimp split: option.splits)
        apply (clarsimp split: option.splits)
       apply (clarsimp split: option.splits)
      apply (auto intro: whileLoop_results.intros intro!: bexI simp: bind_def return_def lift_def split: sum.splits)
  done

lemma validNF_whileLoop:
  assumes pre: "\<And>s. P r s \<Longrightarrow> I r s"
  and inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> ((r', s'), (r, s)) \<in> R \<rbrace>!"
  and wf: "wf R"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace>P r\<rbrace> whileLoop C B r \<lbrace>Q\<rbrace>!"
  apply rule
   apply (rule valid_whileLoop)
     apply fact
    apply (insert inv, clarsimp simp: validNF_def
        valid_def split: prod.splits, force)[1]
   apply (metis post_cond)
  apply (unfold no_fail_def)
  apply (intro allI impI)
  apply (rule not_snd_whileLoop [where I=I and R=R])
    apply (auto intro: assms)
  done

lemma validNF_whileLoop_inv [wp]:
  assumes inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> ((r', s'), (r, s)) \<in> R \<rbrace>!"
  and wf: "wf R"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace>I r\<rbrace> whileLoop_inv C B r I R \<lbrace>Q\<rbrace>!"
  apply (clarsimp simp: whileLoop_inv_def)
  apply (rule validNF_whileLoop [where I=I and R=R])
     apply simp
    apply (rule inv)
   apply (rule wf)
  apply (metis post_cond)
  done

lemma validNF_whileLoop_inv_measure [wp]:
  assumes inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> M r' s' < M r s \<rbrace>!"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace>I r\<rbrace> whileLoop_inv C B r I (measure' (\<lambda>(r, s). M r s)) \<lbrace>Q\<rbrace>!"
  apply (clarsimp simp: whileLoop_inv_def)
    apply (rule validNF_whileLoop [where R="measure' (\<lambda>(r, s). M r s)" and I=I])
     apply simp
    apply clarsimp
    apply (rule inv)
   apply simp
  apply (metis post_cond)
  done

lemma validNF_whileLoop_inv_measure_twosteps:
  assumes inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<rbrace>!"
  assumes measure: "\<And>r m. \<lbrace>\<lambda>s. I r s \<and> C r s \<and> M r s = m \<rbrace> B r \<lbrace> \<lambda>r' s'. M r' s' < m \<rbrace>"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace>I r\<rbrace> whileLoop_inv C B r I (measure' (\<lambda>(r, s). M r s)) \<lbrace>Q\<rbrace>!"
  apply (rule validNF_whileLoop_inv_measure)
   apply (rule validNF_weaken_pre)
    apply (rule validNF_post_comb_conj_L)
     apply (rule inv)
    apply (rule measure)
   apply fast
  apply (metis post_cond)
  done

lemma wf_custom_measure:
  "\<lbrakk> \<And>a b. (a, b) \<in> R \<Longrightarrow> f a < (f :: 'a \<Rightarrow> nat) b \<rbrakk> \<Longrightarrow>  wf R"
  by (metis in_measure wf_def wf_measure)

lemma validNF_whileLoopE:
  assumes pre: "\<And>s. P r s \<Longrightarrow> I r s"
  and inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> ((r', s'), (r, s)) \<in> R \<rbrace>,\<lbrace> E \<rbrace>!"
  and wf: "wf R"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace> P r \<rbrace> whileLoopE C B r \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>!"
  apply (unfold validE_NF_alt_def whileLoopE_def)
   apply (rule validNF_whileLoop [
     where I="\<lambda>r s. case r of Inl x \<Rightarrow> E x s | Inr x \<Rightarrow> I x s"
     and R="{((r', s'), (r, s)). \<exists>x x'. r' = Inl x' \<and> r = Inr x}
     \<union> {((r', s'), (r, s)). \<exists>x x'. r' = Inr x' \<and> r = Inr x \<and> ((x', s'),(x, s)) \<in> R}"])
     apply (simp add: pre)
    apply (insert inv)[1]
    apply (fastforce simp: lift_def validNF_def valid_def
           validE_NF_def throwError_def no_fail_def return_def
           validE_def split: sum.splits prod.splits)
   apply (rule wf_Un)
     apply (rule wf_custom_measure [where f="\<lambda>(r, s). case r of Inl _ \<Rightarrow> 0 | _ \<Rightarrow> 1"])
     apply clarsimp
    apply (insert wf_inv_image [OF wf, where f="\<lambda>(r, s). (theRight r, s)"])
    apply (drule wf_Int1 [where r'="{((r', s'),(r, s)). (\<exists>x. r = Inr x) \<and> (\<exists>x. r' = Inr x)}"])
    apply (erule wf_subset)
    apply rule
    apply (clarsimp simp: inv_image_def split: prod.splits sum.splits)
   apply clarsimp
   apply rule
    apply rule
    apply clarsimp
   apply clarsimp
  apply (clarsimp split: sum.splits)
  apply (blast intro: post_cond)
  done

lemma validNF_whileLoopE_inv [wp]:
  assumes inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> ((r', s'), (r, s)) \<in> R \<rbrace>,\<lbrace> E \<rbrace>!"
  and wf_R: "wf R"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace>I r\<rbrace> whileLoopE_inv C B r I R \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (clarsimp simp: whileLoopE_inv_def)
  apply (metis validNF_whileLoopE [OF _ inv] post_cond wf_R)
  done

lemma validNF_whileLoopE_inv_measure [wp]:
  assumes inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<and> M r' s' < M r s \<rbrace>, \<lbrace> E \<rbrace>!"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace>I r\<rbrace> whileLoopE_inv C B r I (measure' (\<lambda>(r, s). M r s)) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (rule validNF_whileLoopE_inv)
    apply clarsimp
    apply (rule inv)
   apply clarsimp
  apply (metis post_cond)
  done

lemma validNF_whileLoopE_inv_measure_twosteps:
  assumes inv: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<rbrace> B r \<lbrace> \<lambda>r' s'. I r' s' \<rbrace>, \<lbrace> E \<rbrace>!"
  assumes measure: "\<And>r m. \<lbrace>\<lambda>s. I r s \<and> C r s \<and> M r s = m \<rbrace> B r \<lbrace> \<lambda>r' s'. M r' s' < m \<rbrace>, \<lbrace> \<lambda>_ _. True \<rbrace>"
  and post_cond: "\<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace>I r\<rbrace> whileLoopE_inv C B r I (measure' (\<lambda>(r, s). M r s)) \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!"
  apply (rule validNF_whileLoopE_inv_measure)
   apply (rule validE_NF_weaken_pre)
    apply (rule validE_NF_post_comb_conj_L)
     apply (rule inv)
    apply (rule measure)
   apply fast
  apply (metis post_cond)
  done

lemma whileLoopE_wp_inv [wp]:
  "\<lbrakk> \<And>r. \<lbrace>\<lambda>s. I r s \<and> C r s\<rbrace> B r \<lbrace>I\<rbrace>,\<lbrace>E\<rbrace>; \<And>r s. \<lbrakk>I r s; \<not> C r s\<rbrakk> \<Longrightarrow> Q r s \<rbrakk>
      \<Longrightarrow> \<lbrace> I r \<rbrace> whileLoopE_inv C B r I M \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (clarsimp simp: whileLoopE_inv_def)
  apply (rule validE_whileLoopE [where I=I], auto)
  done

subsection "Stronger whileLoop rules"

lemma whileLoop_rule_strong:
  assumes init_U: "\<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> \<lambda>r s. (r, s) \<in> fst Q \<rbrace>"
  and path_exists: "\<And>r'' s''. \<lbrakk> (r'', s'') \<in> fst Q \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> \<lambda>r s. r = r'' \<and> s = s'' \<rbrace>"
  and loop_fail: "snd Q \<Longrightarrow> snd (whileLoop C B r s)"
  and loop_nofail: "\<not> snd Q \<Longrightarrow> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> \<lambda>_ _. True \<rbrace>!"
  shows "whileLoop C B r s = Q"
  using assms
  apply atomize
  apply (clarsimp simp: valid_def exs_valid_def validNF_def no_fail_def)
  apply rule
    apply blast
   apply blast
  apply blast
  done

lemma whileLoop_rule_strong_no_fail:
  assumes init_U: "\<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> \<lambda>r s. (r, s) \<in> fst Q \<rbrace>!"
  and path_exists: "\<And>r'' s''. \<lbrakk> (r'', s'') \<in> fst Q \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> \<lambda>r s. r = r'' \<and> s = s'' \<rbrace>"
  and loop_no_fail: "\<not> snd Q"
  shows "whileLoop C B r s = Q"
  apply (rule whileLoop_rule_strong)
     apply (metis init_U validNF_valid)
    apply (metis path_exists)
   apply (metis loop_no_fail)
  apply (metis (lifting, no_types) init_U validNF_chain)
  done

subsection "Miscellaneous rules"

(* Failure of one whileLoop implies the failure of another whileloop
 * which will only ever fail more. *)
lemma snd_whileLoop_subset:
    assumes a_fails: "snd (whileLoop C A r s)"
    and b_success_step:
        "\<And>r s r' s'. \<lbrakk> C r s; (r', s') \<in> fst (A r s); \<not> snd (B r s) \<rbrakk>
             \<Longrightarrow> (r', s') \<in> fst (B r s)"
    and b_fail_step: "\<And>r s. \<lbrakk> C r s; snd (A r s) \<rbrakk> \<Longrightarrow> snd (B r s) "
   shows "snd (whileLoop C B r s)"
  apply (insert a_fails)
  apply (induct rule: snd_whileLoop_induct)
    apply (unfold whileLoop_def snd_conv)[1]
    apply (rule disjCI, simp)
    apply rotate_tac
    apply (induct rule: whileLoop_terminates.induct)
     apply (subst (asm) whileLoop_terminates.simps)
     apply simp
    apply (subst (asm) (3) whileLoop_terminates.simps, clarsimp)
    apply (subst whileLoop_results.simps, clarsimp)
    apply (rule classical)
    apply (frule b_success_step, assumption, simp)
    apply (drule (1) bspec)
    apply clarsimp
   apply (frule (1) b_fail_step)
   apply (metis snd_whileLoop_first_step)
  apply (metis b_success_step snd_whileLoop_first_step snd_whileLoop_unfold)
  done

end
