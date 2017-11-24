(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory NonDetMonadVCG
imports
  NonDetMonadLemmas
  "wp/WP"
  "wp/WPC"
  "Strengthen"
begin

(* Wrap up the standard usage pattern of wp/wpc/simp into its own command: *)
method wpsimp uses wp wp_del simp simp_del split split_del cong =
  ((determ \<open>wp add: wp del: wp_del | wpc |
            clarsimp simp: simp simp del: simp_del split: split split del: split_del cong: cong\<close>)+)[1]

declare K_def [simp]

section "Satisfiability"

text {*
  The dual to validity: an existential instead of a universal
  quantifier for the post condition. In refinement, it is
  often sufficient to know that there is one state that
  satisfies a condition.
*}
definition
  exs_valid :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) nondet_monad \<Rightarrow>
                ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace> _ \<exists>\<lbrace>_\<rbrace>")
where
 "exs_valid P f Q \<equiv> (\<forall>s. P s \<longrightarrow> (\<exists>(rv, s') \<in> fst (f s). Q rv s'))"


text {* The above for the exception monad *}
definition
  ex_exs_validE :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'e + 'b) nondet_monad \<Rightarrow>
                    ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
   ("\<lbrace>_\<rbrace> _ \<exists>\<lbrace>_\<rbrace>, \<lbrace>_\<rbrace>")
where
 "ex_exs_validE P f Q E \<equiv>
     exs_valid P f (\<lambda>rv. case rv of Inl e \<Rightarrow> E e | Inr v \<Rightarrow> Q v)"


section "Lemmas"

subsection {* Determinism *}

lemma det_set_iff:
  "det f \<Longrightarrow> (r \<in> fst (f s)) = (fst (f s) = {r})"
  apply (simp add: det_def)
  apply (rule iffI)
  apply (erule_tac x=s in allE)
  apply auto
  done

lemma return_det [iff]:
  "det (return x)"
  by (simp add: det_def return_def)

lemma put_det [iff]:
  "det (put s)"
  by (simp add: det_def put_def)

lemma get_det [iff]:
  "det get"
  by (simp add: det_def get_def)

lemma det_gets [iff]:
  "det (gets f)"
  by (auto simp add: gets_def det_def get_def return_def bind_def)

lemma det_UN:
  "det f \<Longrightarrow> (\<Union>x \<in> fst (f s). g x) = (g (THE x. x \<in> fst (f s)))"
  unfolding det_def
  apply simp
  apply (drule spec [of _ s])
  apply clarsimp
  done

lemma bind_detI [simp, intro!]:
  "\<lbrakk> det f; \<forall>x. det (g x) \<rbrakk> \<Longrightarrow> det (f >>= g)"
  apply (simp add: bind_def det_def split_def)
  apply clarsimp
  apply (erule_tac x=s in allE)
  apply clarsimp
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)
  apply clarsimp
  done

lemma the_run_stateI:
  "fst (M s) = {s'} \<Longrightarrow> the_run_state M s = s'"
  by (simp add: the_run_state_def)

lemma the_run_state_det:
  "\<lbrakk> s' \<in> fst (M s); det M \<rbrakk> \<Longrightarrow> the_run_state M s = s'"
  by (simp add: the_run_stateI det_set_iff)

subsection "Lifting and Alternative Basic Definitions"

lemma liftE_liftM: "liftE = liftM Inr"
  apply (rule ext)
  apply (simp add: liftE_def liftM_def)
  done

lemma liftME_liftM: "liftME f = liftM (case_sum Inl (Inr \<circ> f))"
  apply (rule ext)
  apply (simp add: liftME_def liftM_def bindE_def returnOk_def lift_def)
  apply (rule_tac f="bind x" in arg_cong)
  apply (rule ext)
  apply (case_tac xa)
   apply (simp_all add: lift_def throwError_def)
  done

lemma liftE_bindE:
  "(liftE a) >>=E b = a >>= b"
  apply (simp add: liftE_def bindE_def lift_def bind_assoc)
  done

lemma liftM_id[simp]: "liftM id = id"
  apply (rule ext)
  apply (simp add: liftM_def)
  done

lemma liftM_bind:
  "(liftM t f >>= g) = (f >>= (\<lambda>x. g (t x)))"
  by (simp add: liftM_def bind_assoc)

lemma gets_bind_ign: "gets f >>= (\<lambda>x. m) = m"
  apply (rule ext)
  apply (simp add: bind_def simpler_gets_def)
  done

lemma get_bind_apply: "(get >>= f) x = f x x"
  by (simp add: get_def bind_def)

lemma exec_gets:
  "(gets f >>= m) s = m (f s) s"
  by (simp add: simpler_gets_def bind_def)

lemma exec_get:
  "(get >>= m) s = m s s"
  by (simp add: get_def bind_def)

lemma bind_eqI:
  "\<lbrakk> f = f'; \<And>x. g x = g' x \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  apply (rule ext)
  apply (simp add: bind_def)
  apply (auto simp: split_def)
  done

subsection "Simplification Rules for Lifted And/Or"

lemma pred_andE[elim!]: "\<lbrakk> (A and B) x; \<lbrakk> A x; B x \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by(simp add:pred_conj_def)

lemma pred_andI[intro!]: "\<lbrakk> A x; B x \<rbrakk> \<Longrightarrow> (A and B) x"
  by(simp add:pred_conj_def)

lemma pred_conj_app[simp]: "(P and Q) x = (P x \<and> Q x)"
  by(simp add:pred_conj_def)

lemma bipred_andE[elim!]: "\<lbrakk> (A And B) x y; \<lbrakk> A x y; B x y \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by(simp add:bipred_conj_def)

lemma bipred_andI[intro!]: "\<lbrakk> A x y; B x y \<rbrakk> \<Longrightarrow> (A And B) x y"
  by (simp add:bipred_conj_def)

lemma bipred_conj_app[simp]: "(P And Q) x = (P x and Q x)"
  by(simp add:pred_conj_def bipred_conj_def)

lemma pred_disjE[elim!]: "\<lbrakk> (P or Q) x; P x \<Longrightarrow> R; Q x \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (fastforce simp: pred_disj_def)

lemma pred_disjI1[intro]: "P x \<Longrightarrow> (P or Q) x"
  by (simp add: pred_disj_def)

lemma pred_disjI2[intro]: "Q x \<Longrightarrow> (P or Q) x"
  by (simp add: pred_disj_def)

lemma pred_disj_app[simp]: "(P or Q) x = (P x \<or> Q x)"
  by auto

lemma bipred_disjI1[intro]: "P x y \<Longrightarrow> (P Or Q) x y"
  by (simp add: bipred_disj_def)

lemma bipred_disjI2[intro]: "Q x y \<Longrightarrow> (P Or Q) x y"
  by (simp add: bipred_disj_def)

lemma bipred_disj_app[simp]: "(P Or Q) x = (P x or Q x)"
  by(simp add:pred_disj_def bipred_disj_def)

lemma pred_notnotD[simp]: "(not not P) = P"
  by(simp add:pred_neg_def)

lemma pred_and_true[simp]: "(P and \<top>) = P"
  by(simp add:pred_conj_def)

lemma pred_and_true_var[simp]: "(\<top> and P) = P"
  by(simp add:pred_conj_def)

lemma pred_and_false[simp]: "(P and \<bottom>) = \<bottom>"
  by(simp add:pred_conj_def)

lemma pred_and_false_var[simp]: "(\<bottom> and P) = \<bottom>"
  by(simp add:pred_conj_def)

subsection "Hoare Logic Rules"

lemma validE_def2:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(r,s') \<in> fst (f s). case r of Inr b \<Rightarrow> Q b s'
                                                              | Inl a \<Rightarrow> R a s')"
  by (unfold valid_def validE_def)

lemma seq':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>;
     \<forall>x. P x \<longrightarrow> \<lbrace>C\<rbrace> g x \<lbrace>D\<rbrace>;
     \<forall>x s. B x s \<longrightarrow> P x \<and> C s \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>D\<rbrace>"
  apply (clarsimp simp: valid_def bind_def)
  apply fastforce
  done

lemma seq:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>"
  assumes g_valid: "\<And>x. P x \<Longrightarrow> \<lbrace>C\<rbrace> g x \<lbrace>D\<rbrace>"
  assumes bind:  "\<And>x s. B x s \<Longrightarrow> P x \<and> C s"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>D\<rbrace>"
apply (insert f_valid g_valid bind)
apply (blast intro: seq')
done

lemma seq_ext':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>;
     \<forall>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>"
  by (fastforce simp: valid_def bind_def Let_def split_def)

lemma seq_ext:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>"
  assumes g_valid: "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>"
 apply(insert f_valid g_valid)
 apply(blast intro: seq_ext')
done

lemma seqE':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>;
     \<forall>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> doE x \<leftarrow> f; g x odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  apply(simp add:bindE_def lift_def bind_def Let_def split_def)
  apply(clarsimp simp:validE_def2)
  apply (fastforce simp add: throwError_def return_def lift_def
                  split: sum.splits)
  done

lemma seqE:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>"
  assumes g_valid: "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>A\<rbrace> doE x \<leftarrow> f; g x odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  apply(insert f_valid g_valid)
  apply(blast intro: seqE')
  done

lemma hoare_TrueI: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>"
  by (simp add: valid_def)

lemma hoareE_TrueI: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>r. \<top>\<rbrace>"
  by (simp add: validE_def valid_def)

lemma hoare_True_E_R [simp]:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. True\<rbrace>, -"
  by (auto simp add: validE_R_def validE_def valid_def split: sum.splits)

lemma hoare_post_conj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace>; \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> Q And R \<rbrace>"
  by (fastforce simp: valid_def split_def bipred_conj_def)

lemma hoare_pre_disj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>; \<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> P or Q \<rbrace> a \<lbrace> R \<rbrace>"
  by (simp add:valid_def pred_disj_def)

lemma hoare_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>Q And Q'\<rbrace>"
  unfolding valid_def by auto

lemma hoare_post_taut: "\<lbrace> P \<rbrace> a \<lbrace> \<top>\<top> \<rbrace>"
  by (simp add:valid_def)

lemma wp_post_taut: "\<lbrace>\<lambda>r. True\<rbrace> f \<lbrace>\<lambda>r s. True\<rbrace>"
  by (rule hoare_post_taut)

lemma wp_post_tautE: "\<lbrace>\<lambda>r. True\<rbrace> f \<lbrace>\<lambda>r s. True\<rbrace>,\<lbrace>\<lambda>f s. True\<rbrace>"
proof -
  have P: "\<And>r. (case r of Inl a \<Rightarrow> True | _ \<Rightarrow> True) = True"
    by (case_tac r, simp_all)
  show ?thesis
    by (simp add: validE_def P wp_post_taut)
qed

lemma hoare_pre_cont [simp]: "\<lbrace> \<bottom> \<rbrace> a \<lbrace> P \<rbrace>"
  by (simp add:valid_def)


subsection {* Strongest Postcondition Rules *}

lemma get_sp:
  "\<lbrace>P\<rbrace> get \<lbrace>\<lambda>a s. s = a \<and> P s\<rbrace>"
  by(simp add:get_def valid_def)

lemma put_sp:
  "\<lbrace>\<top>\<rbrace> put a \<lbrace>\<lambda>_ s. s = a\<rbrace>"
  by(simp add:put_def valid_def)

lemma return_sp:
  "\<lbrace>P\<rbrace> return a \<lbrace>\<lambda>b s. b = a \<and> P s\<rbrace>"
  by(simp add:return_def valid_def)

lemma assert_sp:
  "\<lbrace> P \<rbrace> assert Q \<lbrace> \<lambda>r s. P s \<and> Q \<rbrace>"
  by (simp add: assert_def fail_def return_def valid_def)

lemma hoare_gets_sp:
  "\<lbrace>P\<rbrace> gets f \<lbrace>\<lambda>rv s. rv = f s \<and> P s\<rbrace>"
  by (simp add: valid_def simpler_gets_def)

lemma hoare_return_drop_var [iff]: "\<lbrace> Q \<rbrace> return x \<lbrace> \<lambda>r. Q \<rbrace>"
  by (simp add:valid_def return_def)

lemma hoare_gets [intro!]: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q (f s) s \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> gets f \<lbrace> Q \<rbrace>"
  by (simp add:valid_def gets_def get_def bind_def return_def)

lemma hoare_modifyE_var [intro!]:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q (f s) \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> modify f \<lbrace> \<lambda>r s. Q s \<rbrace>"
  by(simp add: valid_def modify_def put_def get_def bind_def)

lemma hoare_if [intro!]:
  "\<lbrakk> P \<Longrightarrow> \<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace>; \<not> P \<Longrightarrow> \<lbrace> Q \<rbrace> b \<lbrace> R \<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace> Q \<rbrace> if P then a else b \<lbrace> R \<rbrace>"
  by (simp add:valid_def)

lemma hoare_pre_subst: "\<lbrakk> A = B; \<lbrace>A\<rbrace> a \<lbrace>C\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>B\<rbrace> a \<lbrace>C\<rbrace>"
  by(clarsimp simp:valid_def split_def)

lemma hoare_post_subst: "\<lbrakk> B = C; \<lbrace>A\<rbrace> a \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> a \<lbrace>C\<rbrace>"
  by(clarsimp simp:valid_def split_def)

lemma hoare_pre_tautI: "\<lbrakk> \<lbrace>A and P\<rbrace> a \<lbrace>B\<rbrace>; \<lbrace>A and not P\<rbrace> a \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> a \<lbrace>B\<rbrace>"
  by(fastforce simp:valid_def split_def pred_conj_def pred_neg_def)

lemma hoare_pre_imp: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q s; \<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by (fastforce simp add:valid_def)

lemma hoare_post_imp: "\<lbrakk> \<And>r s. Q r s \<Longrightarrow> R r s; \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by(fastforce simp:valid_def split_def)

lemma hoare_post_impErr': "\<lbrakk> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>;
                           \<forall>r s. Q r s \<longrightarrow> R r s;
                           \<forall>e s. E e s \<longrightarrow> F e s \<rbrakk> \<Longrightarrow>
                         \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>"
 apply (simp add: validE_def)
 apply (rule_tac Q="\<lambda>r s. case r of Inl a \<Rightarrow> E a s | Inr b \<Rightarrow> Q b s" in hoare_post_imp)
  apply (case_tac r)
   apply simp_all
 done

lemma hoare_post_impErr: "\<lbrakk> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>;
                          \<And>r s. Q r s \<Longrightarrow> R r s;
                          \<And>e s. E e s \<Longrightarrow> F e s \<rbrakk> \<Longrightarrow>
                         \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>"
 apply (blast intro: hoare_post_impErr')
 done

lemma hoare_validE_cases:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>, \<lbrace> \<lambda>_ _. True \<rbrace>; \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_ _. True \<rbrace>, \<lbrace> R \<rbrace> \<rbrakk>
  \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>, \<lbrace> R \<rbrace>"
  by (simp add: validE_def valid_def split: sum.splits) blast

lemma hoare_post_imp_dc:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. Q\<rbrace>; \<And>s. Q s \<Longrightarrow> R s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. R\<rbrace>,\<lbrace>\<lambda>r. R\<rbrace>"
  by (simp add: validE_def valid_def split: sum.splits) blast

lemma hoare_post_imp_dc2:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. Q\<rbrace>; \<And>s. Q s \<Longrightarrow> R s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. R\<rbrace>,\<lbrace>\<lambda>r s. True\<rbrace>"
  by (simp add: validE_def valid_def split: sum.splits) blast

lemma hoare_post_imp_dc2E:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. Q\<rbrace>; \<And>s. Q s \<Longrightarrow> R s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>r s. True\<rbrace>, \<lbrace>\<lambda>r. R\<rbrace>"
  by (simp add: validE_def valid_def split: sum.splits) fast

lemma hoare_post_imp_dc2E_actual:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. R\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>r s. True\<rbrace>, \<lbrace>\<lambda>r. R\<rbrace>"
  by (simp add: validE_def valid_def split: sum.splits) fast

lemma hoare_post_imp_dc2_actual:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. R\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>\<lambda>r. R\<rbrace>, \<lbrace>\<lambda>r s. True\<rbrace>"
  by (simp add: validE_def valid_def split: sum.splits) fast

lemma hoare_post_impE: "\<lbrakk> \<And>r s. Q r s \<Longrightarrow> R r s; \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by (fastforce simp:valid_def split_def)

lemma hoare_conjD1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and R rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_conjD2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv and R rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. R rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_post_disjI1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv or R rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_post_disjI2:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. R rv\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q rv or R rv\<rbrace>"
  unfolding valid_def by auto

lemma hoare_weaken_pre:
  "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  apply (rule hoare_pre_imp)
   prefer 2
   apply assumption
  apply blast
  done

lemma hoare_strengthen_post:
  "\<lbrakk>\<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>; \<And>r s. Q r s \<Longrightarrow> R r s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply assumption
  apply blast
  done

lemma use_valid: "\<lbrakk>(r, s') \<in> fst (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; P s \<rbrakk> \<Longrightarrow> Q r s'"
  apply (simp add: valid_def)
  apply blast
  done

lemma use_validE_norm: "\<lbrakk> (Inr r', s') \<in> fst (B s); \<lbrace> P \<rbrace> B \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>; P s \<rbrakk> \<Longrightarrow> Q r' s'"
  apply (clarsimp simp: validE_def valid_def)
  apply force
  done

lemma use_validE_except: "\<lbrakk> (Inl r', s') \<in> fst (B s); \<lbrace> P \<rbrace> B \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>; P s \<rbrakk> \<Longrightarrow> E r' s'"
  apply (clarsimp simp: validE_def valid_def)
  apply force
  done

lemma in_inv_by_hoareD:
  "\<lbrakk> \<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>; (x,s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> s' = s"
  by (auto simp add: valid_def) blast

subsection "Satisfiability"

lemma exs_hoare_post_imp: "\<lbrakk>\<And>r s. Q r s \<Longrightarrow> R r s; \<lbrace>P\<rbrace> a \<exists>\<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<exists>\<lbrace>R\<rbrace>"
  apply (simp add: exs_valid_def)
  apply safe
  apply (erule_tac x=s in allE, simp)
  apply blast
  done

lemma use_exs_valid: "\<lbrakk>\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>; P s \<rbrakk> \<Longrightarrow> \<exists>(r, s') \<in> fst (f s). Q r s'"
  by (simp add: exs_valid_def)

definition "exs_postcondition P f \<equiv> (\<lambda>a b. \<exists>(rv, s)\<in> f a b. P rv s)"

lemma exs_valid_is_triple:
  "exs_valid P f Q = triple_judgement P f (exs_postcondition Q (\<lambda>s f. fst (f s)))"
  by (simp add: triple_judgement_def exs_postcondition_def exs_valid_def)

lemmas [wp_trip] = exs_valid_is_triple

lemma exs_valid_weaken_pre [wp_comb]:
  "\<lbrakk> \<lbrace> P' \<rbrace> f \<exists>\<lbrace> Q \<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<exists>\<lbrace> Q \<rbrace>"
  apply atomize
  apply (clarsimp simp: exs_valid_def)
  done

lemma exs_valid_chain:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<exists>\<lbrace> Q \<rbrace>; \<And>s. R s \<Longrightarrow> P s; \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow> \<lbrace> R \<rbrace> f \<exists>\<lbrace> S \<rbrace>"
  apply atomize
  apply (fastforce simp: exs_valid_def Bex_def)
  done

lemma exs_valid_assume_pre:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> \<lbrace> P \<rbrace> f \<exists>\<lbrace> Q \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<exists>\<lbrace> Q \<rbrace>"
  apply (fastforce simp: exs_valid_def)
  done

lemma exs_valid_bind [wp_split]:
    "\<lbrakk> \<And>x. \<lbrace>B x\<rbrace> g x \<exists>\<lbrace>C\<rbrace>; \<lbrace>A\<rbrace> f \<exists>\<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> A \<rbrace> f >>= (\<lambda>x. g x) \<exists>\<lbrace> C \<rbrace>"
  apply atomize
  apply (clarsimp simp: exs_valid_def bind_def')
  apply blast
  done

lemma exs_valid_return [wp]:
    "\<lbrace> Q v \<rbrace> return v \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: exs_valid_def return_def)

lemma exs_valid_select [wp]:
    "\<lbrace> \<lambda>s. \<exists>r \<in> S. Q r s \<rbrace> select S \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: exs_valid_def select_def)

lemma exs_valid_get [wp]:
    "\<lbrace> \<lambda>s. Q s s \<rbrace> get \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: exs_valid_def get_def)

lemma exs_valid_gets [wp]:
    "\<lbrace> \<lambda>s. Q (f s) s \<rbrace> gets f \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: gets_def) wp

lemma exs_valid_put [wp]:
    "\<lbrace> Q v \<rbrace> put v \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: put_def exs_valid_def)

lemma exs_valid_state_assert [wp]:
    "\<lbrace> \<lambda>s. Q () s \<and> G s \<rbrace> state_assert G \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: state_assert_def exs_valid_def get_def
           assert_def bind_def' return_def)

lemmas exs_valid_guard = exs_valid_state_assert

lemma exs_valid_fail [wp]:
    "\<lbrace> \<lambda>_. False \<rbrace> fail \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: fail_def exs_valid_def)

lemma exs_valid_condition [wp]:
    "\<lbrakk> \<lbrace> P \<rbrace> L \<exists>\<lbrace> Q \<rbrace>; \<lbrace> P' \<rbrace> R \<exists>\<lbrace> Q \<rbrace> \<rbrakk> \<Longrightarrow>
          \<lbrace> \<lambda>s. (C s \<and> P s) \<or> (\<not> C s \<and> P' s) \<rbrace> condition C L R \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: condition_def exs_valid_def split: sum.splits)


subsection MISC

lemma hoare_return_simp:
  "\<lbrace>P\<rbrace> return x \<lbrace>Q\<rbrace> = (\<forall>s. P s \<longrightarrow> Q x s)"
  by (simp add: valid_def return_def)

lemma hoare_gen_asm:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp add: valid_def)

lemma hoare_gen_asm_lk:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>K P and P'\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp add: valid_def)

lemma hoare_when_wp [wp]:
 "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>if P then Q else R ()\<rbrace> when P f \<lbrace>R\<rbrace>"
  by (clarsimp simp: when_def valid_def return_def)

lemma hoare_conjI:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> R r s\<rbrace>"
  unfolding valid_def by blast

lemma hoare_disjI1:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<or>  R r s \<rbrace>"
  unfolding valid_def by blast

lemma hoare_disjI2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<or>  R r s \<rbrace>"
  unfolding valid_def by blast

lemma hoare_assume_pre:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: valid_def)

lemma hoare_returnOk_sp:
  "\<lbrace>P\<rbrace> returnOk x \<lbrace>\<lambda>r s. r = x \<and> P s\<rbrace>, \<lbrace>Q\<rbrace>"
  by (simp add: valid_def validE_def returnOk_def return_def)

lemma hoare_assume_preE:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
  by (auto simp: valid_def validE_def)

lemma hoare_allI:
  "(\<And>x. \<lbrace>P\<rbrace>f\<lbrace>Q x\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>\<lambda>r s. \<forall>x. Q x r s\<rbrace>"
  by (simp add: valid_def) blast

lemma validE_allI:
  "(\<And>x. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q x r s\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<forall>x. Q x r s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: valid_def validE_def split: sum.splits)

lemma hoare_exI:
  "\<lbrace>P\<rbrace> f \<lbrace>Q x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<exists>x. Q x r s\<rbrace>"
  by (simp add: valid_def) blast

lemma hoare_impI:
  "(R \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>\<lambda>r s. R \<longrightarrow> Q r s\<rbrace>"
  by (simp add: valid_def) blast

lemma validE_impI:
  " \<lbrakk>\<And>E. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>E\<rbrace>; (P' \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>)\<rbrakk> \<Longrightarrow>
         \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. P' \<longrightarrow> Q r s\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_case_option_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f None \<lbrace>Q\<rbrace>;
     \<And>x.  \<lbrace>P' x\<rbrace> f (Some x) \<lbrace>Q' x\<rbrace> \<rbrakk>
  \<Longrightarrow> \<lbrace>case_option P P' v\<rbrace> f v \<lbrace>\<lambda>rv. case v of None \<Rightarrow> Q rv | Some x \<Rightarrow> Q' x rv\<rbrace>"
  by (cases v) auto

subsection "Reasoning directly about states"

lemma in_throwError:
  "((v, s') \<in> fst (throwError e s)) = (v = Inl e \<and> s' = s)"
  by (simp add: throwError_def return_def)

lemma in_returnOk:
  "((v', s') \<in> fst (returnOk v s)) = (v' = Inr v \<and> s' = s)"
  by (simp add: returnOk_def return_def)

lemma in_bind:
  "((r,s') \<in> fst ((do x \<leftarrow> f; g x od) s)) =
   (\<exists>s'' x. (x, s'') \<in> fst (f s) \<and> (r, s') \<in> fst (g x s''))"
  apply (simp add: bind_def split_def)
  apply force
  done

lemma in_bindE_R:
  "((Inr r,s') \<in> fst ((doE x \<leftarrow> f; g x odE) s)) =
  (\<exists>s'' x. (Inr x, s'') \<in> fst (f s) \<and> (Inr r, s') \<in> fst (g x s''))"
  apply (simp add: bindE_def lift_def split_def bind_def)
  apply (clarsimp simp: throwError_def return_def lift_def split: sum.splits)
  apply safe
   apply (case_tac a)
    apply fastforce
   apply fastforce
  apply force
  done

lemma in_bindE_L:
  "((Inl r, s') \<in> fst ((doE x \<leftarrow> f; g x odE) s)) \<Longrightarrow>
  (\<exists>s'' x. (Inr x, s'') \<in> fst (f s) \<and> (Inl r, s') \<in> fst (g x s'')) \<or> ((Inl r, s') \<in> fst (f s))"
  apply (simp add: bindE_def lift_def bind_def)
  apply safe
  apply (simp add: return_def throwError_def lift_def split_def split: sum.splits if_split_asm)
  apply force
  done

lemma in_liftE:
  "((v, s') \<in> fst (liftE f s)) = (\<exists>v'. v = Inr v' \<and> (v', s') \<in> fst (f s))"
  by (force simp add: liftE_def bind_def return_def split_def)

lemma in_whenE:  "((v, s') \<in> fst (whenE P f s)) = ((P \<longrightarrow> (v, s') \<in> fst (f s)) \<and>
                                                   (\<not>P \<longrightarrow> v = Inr () \<and> s' = s))"
  by (simp add: whenE_def in_returnOk)

lemma inl_whenE:
  "((Inl x, s') \<in> fst (whenE P f s)) = (P \<and> (Inl x, s') \<in> fst (f s))"
  by (auto simp add: in_whenE)

lemma in_fail:
  "r \<in> fst (fail s) = False"
  by (simp add: fail_def)

lemma in_return:
  "(r, s') \<in> fst (return v s) = (r = v \<and> s' = s)"
  by (simp add: return_def)

lemma in_assert:
  "(r, s') \<in> fst (assert P s) = (P \<and> s' = s)"
  by (simp add: assert_def return_def fail_def)

lemma in_assertE:
  "(r, s') \<in> fst (assertE P s) = (P \<and> r = Inr () \<and> s' = s)"
  by (simp add: assertE_def returnOk_def return_def fail_def)

lemma in_assert_opt:
  "(r, s') \<in> fst (assert_opt v s) = (v = Some r \<and> s' = s)"
  by (auto simp: assert_opt_def in_fail in_return split: option.splits)

lemma in_get:
  "(r, s') \<in> fst (get s) = (r = s \<and> s' = s)"
  by (simp add: get_def)

lemma in_gets:
  "(r, s') \<in> fst (gets f s) = (r = f s \<and> s' = s)"
  by (simp add: simpler_gets_def)

lemma in_put:
  "(r, s') \<in> fst (put x s) = (s' = x \<and> r = ())"
  by (simp add: put_def)

lemma in_when:
  "(v, s') \<in> fst (when P f s) = ((P \<longrightarrow> (v, s') \<in> fst (f s)) \<and> (\<not>P \<longrightarrow> v = () \<and> s' = s))"
  by (simp add: when_def in_return)

lemma in_modify:
  "(v, s') \<in> fst (modify f s) = (s'=f s \<and> v = ())"
  by (simp add: modify_def bind_def get_def put_def)

lemma gets_the_in_monad:
  "((v, s') \<in> fst (gets_the f s)) = (s' = s \<and> f s = Some v)"
  by (auto simp: gets_the_def in_bind in_gets in_assert_opt split: option.split)

lemma in_alternative:
  "(r,s') \<in> fst ((f \<sqinter> g) s) = ((r,s') \<in> fst (f s) \<or> (r,s') \<in> fst (g s))"
  by (simp add: alternative_def)

lemmas in_monad = inl_whenE in_whenE in_liftE in_bind in_bindE_L
                  in_bindE_R in_returnOk in_throwError in_fail
                  in_assertE in_assert in_return in_assert_opt
                  in_get in_gets in_put in_when unlessE_whenE
                  unless_when in_modify gets_the_in_monad
                  in_alternative

subsection "Non-Failure"

lemma no_failD:
  "\<lbrakk> no_fail P m; P s \<rbrakk> \<Longrightarrow> \<not>(snd (m s))"
  by (simp add: no_fail_def)

lemma non_fail_modify [wp,simp]:
  "no_fail \<top> (modify f)"
  by (simp add: no_fail_def modify_def get_def put_def bind_def)

lemma non_fail_gets_simp[simp]:
  "no_fail P (gets f)"
  unfolding no_fail_def gets_def get_def return_def bind_def
  by simp

lemma non_fail_gets:
  "no_fail \<top> (gets f)"
  by simp

lemma non_fail_select [simp]:
  "no_fail \<top> (select S)"
  by (simp add: no_fail_def select_def)

lemma no_fail_pre:
  "\<lbrakk> no_fail P f; \<And>s. Q s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> no_fail Q f"
  by (simp add: no_fail_def)

lemma no_fail_alt [wp]:
  "\<lbrakk> no_fail P f; no_fail Q g \<rbrakk> \<Longrightarrow> no_fail (P and Q) (f OR g)"
  by (simp add: no_fail_def alternative_def)

lemma no_fail_return [simp, wp]:
  "no_fail \<top> (return x)"
  by (simp add: return_def no_fail_def)

lemma no_fail_get [simp, wp]:
  "no_fail \<top> get"
  by (simp add: get_def no_fail_def)

lemma no_fail_put [simp, wp]:
  "no_fail \<top> (put s)"
  by (simp add: put_def no_fail_def)

lemma no_fail_when [wp]:
  "(P \<Longrightarrow> no_fail Q f) \<Longrightarrow> no_fail (if P then Q else \<top>) (when P f)"
  by (simp add: when_def)

lemma no_fail_unless [wp]:
  "(\<not>P \<Longrightarrow> no_fail Q f) \<Longrightarrow> no_fail (if P then \<top> else Q) (unless P f)"
  by (simp add: unless_def when_def)

lemma no_fail_fail [simp, wp]:
  "no_fail \<bottom> fail"
  by (simp add: fail_def no_fail_def)

lemmas [wp] = non_fail_gets

lemma no_fail_assert [simp, wp]:
  "no_fail (\<lambda>_. P) (assert P)"
  by (simp add: assert_def)

lemma no_fail_assert_opt [simp, wp]:
  "no_fail (\<lambda>_. P \<noteq> None) (assert_opt P)"
  by (simp add: assert_opt_def split: option.splits)

lemma no_fail_case_option [wp]:
  assumes f: "no_fail P f"
  assumes g: "\<And>x. no_fail (Q x) (g x)"
  shows "no_fail (if x = None then P else Q (the x)) (case_option f g x)"
  by (clarsimp simp add: f g)

lemma no_fail_if [wp]:
  "\<lbrakk> P \<Longrightarrow> no_fail Q f; \<not>P \<Longrightarrow> no_fail R g \<rbrakk> \<Longrightarrow>
  no_fail (if P then Q else R) (if P then f else g)"
  by simp

lemma no_fail_apply [wp]:
  "no_fail P (f (g x)) \<Longrightarrow> no_fail P (f $ g x)"
  by simp

lemma no_fail_undefined [simp, wp]:
  "no_fail \<bottom> undefined"
  by (simp add: no_fail_def)

lemma no_fail_returnOK [simp, wp]:
  "no_fail \<top> (returnOk x)"
  by (simp add: returnOk_def)

text {* Empty results implies non-failure *}

lemma empty_fail_modify [simp]:
  "empty_fail (modify f)"
  by (simp add: empty_fail_def simpler_modify_def)

lemma empty_fail_gets [simp]:
  "empty_fail (gets f)"
  by (simp add: empty_fail_def simpler_gets_def)

lemma empty_failD:
  "\<lbrakk> empty_fail m; fst (m s) = {} \<rbrakk> \<Longrightarrow> snd (m s)"
  by (simp add: empty_fail_def)

lemma empty_fail_select_f [simp]:
  assumes ef: "fst S = {} \<Longrightarrow> snd S"
  shows "empty_fail (select_f S)"
  by (fastforce simp add: empty_fail_def select_f_def intro: ef)

lemma empty_fail_bind [simp]:
  "\<lbrakk> empty_fail a; \<And>x. empty_fail (b x) \<rbrakk> \<Longrightarrow> empty_fail (a >>= b)"
  apply (simp add: bind_def empty_fail_def split_def)
  apply clarsimp
  apply (case_tac "fst (a s) = {}")
   apply blast
  apply (clarsimp simp: ex_in_conv [symmetric])
  done

lemma empty_fail_return [simp]:
  "empty_fail (return x)"
  by (simp add: empty_fail_def return_def)

lemma empty_fail_mapM [simp]:
  assumes m: "\<And>x. empty_fail (m x)"
  shows "empty_fail (mapM m xs)"
proof (induct xs)
  case Nil
  thus ?case by (simp add: mapM_def sequence_def)
next
  case Cons
  have P: "\<And>m x xs. mapM m (x # xs) = (do y \<leftarrow> m x; ys \<leftarrow> (mapM m xs); return (y # ys) od)"
    by (simp add: mapM_def sequence_def Let_def)
  from Cons
  show ?case by (simp add: P m)
qed

lemma empty_fail [simp]:
  "empty_fail fail"
  by (simp add: fail_def empty_fail_def)

lemma empty_fail_assert_opt [simp]:
  "empty_fail (assert_opt x)"
  by (simp add: assert_opt_def split: option.splits)

lemma empty_fail_mk_ef:
  "empty_fail (mk_ef o m)"
  by (simp add: empty_fail_def mk_ef_def)

subsection "Failure"

lemma fail_wp: "\<lbrace>\<lambda>x. True\<rbrace> fail \<lbrace>Q\<rbrace>"
  by (simp add: valid_def fail_def)

lemma failE_wp: "\<lbrace>\<lambda>x. True\<rbrace> fail \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validE_def fail_wp)

lemma fail_update [iff]:
  "fail (f s) = fail s"
  by (simp add: fail_def)


text {* We can prove postconditions using hoare triples *}

lemma post_by_hoare: "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; P s; (r, s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> Q r s'"
  apply (simp add: valid_def)
  apply blast
  done

text {* Weakest Precondition Rules *}

lemma hoare_vcg_prop:
  "\<lbrace>\<lambda>s. P\<rbrace> f \<lbrace>\<lambda>rv s. P\<rbrace>"
  by (simp add: valid_def)

lemma return_wp:
  "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>"
  by(simp add:valid_def return_def)

lemma get_wp:
  "\<lbrace>\<lambda>s. P s s\<rbrace> get \<lbrace>P\<rbrace>"
  by(simp add:valid_def split_def get_def)

lemma gets_wp:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>P\<rbrace>"
  by(simp add:valid_def split_def gets_def return_def get_def bind_def)

lemma modify_wp:
  "\<lbrace>\<lambda>s. P () (f s)\<rbrace> modify f \<lbrace>P\<rbrace>"
  by(simp add:valid_def split_def modify_def get_def put_def bind_def)

lemma put_wp:
 "\<lbrace>\<lambda>s. P () x\<rbrace> put x \<lbrace>P\<rbrace>"
 by(simp add:valid_def put_def)

lemma returnOk_wp:
  "\<lbrace>P x\<rbrace> returnOk x \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
 by(simp add:validE_def2 returnOk_def return_def)

lemma throwError_wp:
  "\<lbrace>E e\<rbrace> throwError e \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  by(simp add:validE_def2 throwError_def return_def)

lemma returnOKE_R_wp : "\<lbrace>P x\<rbrace> returnOk x \<lbrace>P\<rbrace>, -"
  by (simp add: validE_R_def validE_def valid_def returnOk_def return_def)

lemma liftE_wp:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by(clarsimp simp:valid_def validE_def2 liftE_def split_def Let_def bind_def return_def)

lemma catch_wp:
  "\<lbrakk> \<And>x. \<lbrace>E x\<rbrace> handler x \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> catch f handler \<lbrace>Q\<rbrace>"
 apply (unfold catch_def valid_def validE_def return_def)
 apply (fastforce simp: bind_def split: sum.splits)
 done

lemma handleE'_wp:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle2> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
 apply (unfold handleE'_def valid_def validE_def return_def)
 apply (fastforce simp: bind_def split: sum.splits)
 done

lemma handleE_wp:
  assumes x: "\<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f <handle> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: handleE_def handleE'_wp [OF x y])

lemma hoare_vcg_if_split:
 "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>"
  by simp

lemma hoare_vcg_if_splitE:
 "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>,\<lbrace>E\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemma hoare_liftM_subst: "\<lbrace>P\<rbrace> liftM f m \<lbrace>Q\<rbrace> = \<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace>"
  apply (simp add: liftM_def bind_def return_def split_def)
  apply (simp add: valid_def Ball_def)
  apply (rule_tac f=All in arg_cong)
  apply (rule ext)
  apply fastforce
  done

lemma liftE_validE[simp]: "\<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> = \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (simp add: liftE_liftM validE_def hoare_liftM_subst o_def)
  done

lemma liftM_wp: "\<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftM f m \<lbrace>Q\<rbrace>"
  by (simp add: hoare_liftM_subst)

lemma hoare_liftME_subst: "\<lbrace>P\<rbrace> liftME f m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> = \<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: validE_def liftME_liftM hoare_liftM_subst o_def)
  apply (rule_tac f="valid P m" in arg_cong)
  apply (rule ext)+
  apply (case_tac x, simp_all)
  done

lemma liftME_wp: "\<lbrace>P\<rbrace> m \<lbrace>Q \<circ> f\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftME f m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: hoare_liftME_subst)

(* FIXME: Move *)
lemma o_const_simp[simp]: "(\<lambda>x. C) \<circ> f = (\<lambda>x. C)"
  by (simp add: o_def)

lemma hoare_vcg_split_case_option:
 "\<lbrakk> \<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace> f x \<lbrace>R x\<rbrace>;
    \<And>x y. x = Some y \<Longrightarrow> \<lbrace>Q x y\<rbrace> g x y \<lbrace>R x\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (x = None \<longrightarrow> P x s) \<and>
       (\<forall>y. x = Some y \<longrightarrow> Q x y s)\<rbrace>
  case x of None \<Rightarrow> f x
          | Some y \<Rightarrow> g x y
  \<lbrace>R x\<rbrace>"
 apply(simp add:valid_def split_def)
 apply(case_tac x, simp_all)
done

lemma hoare_vcg_split_case_optionE:
 assumes none_case: "\<And>x. x = None \<Longrightarrow> \<lbrace>P x\<rbrace> f x \<lbrace>R x\<rbrace>,\<lbrace>E x\<rbrace>"
 assumes some_case: "\<And>x y. x = Some y \<Longrightarrow> \<lbrace>Q x y\<rbrace> g x y \<lbrace>R x\<rbrace>,\<lbrace>E x\<rbrace>"
 shows "\<lbrace>\<lambda>s. (x = None \<longrightarrow> P x s) \<and>
             (\<forall>y. x = Some y \<longrightarrow> Q x y s)\<rbrace>
        case x of None \<Rightarrow> f x
                | Some y \<Rightarrow> g x y
        \<lbrace>R x\<rbrace>,\<lbrace>E x\<rbrace>"
 apply(case_tac x, simp_all)
  apply(rule none_case, simp)
 apply(rule some_case, simp)
done

lemma hoare_vcg_split_case_sum:
 "\<lbrakk> \<And>x a. x = Inl a \<Longrightarrow> \<lbrace>P x a\<rbrace> f x a \<lbrace>R x\<rbrace>;
    \<And>x b. x = Inr b \<Longrightarrow> \<lbrace>Q x b\<rbrace> g x b \<lbrace>R x\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (\<forall>a. x = Inl a \<longrightarrow> P x a s) \<and>
       (\<forall>b. x = Inr b \<longrightarrow> Q x b s) \<rbrace>
  case x of Inl a \<Rightarrow> f x a
          | Inr b \<Rightarrow> g x b
  \<lbrace>R x\<rbrace>"
 apply(simp add:valid_def split_def)
 apply(case_tac x, simp_all)
done

lemma hoare_vcg_split_case_sumE:
  assumes left_case: "\<And>x a. x = Inl a \<Longrightarrow> \<lbrace>P x a\<rbrace> f x a \<lbrace>R x\<rbrace>"
  assumes right_case: "\<And>x b. x = Inr b \<Longrightarrow> \<lbrace>Q x b\<rbrace> g x b \<lbrace>R x\<rbrace>"
  shows "\<lbrace>\<lambda>s. (\<forall>a. x = Inl a \<longrightarrow> P x a s) \<and>
              (\<forall>b. x = Inr b \<longrightarrow> Q x b s) \<rbrace>
         case x of Inl a \<Rightarrow> f x a
                 | Inr b \<Rightarrow> g x b
         \<lbrace>R x\<rbrace>"
 apply(case_tac x, simp_all)
  apply(rule left_case, simp)
 apply(rule right_case, simp)
done

lemma hoare_vcg_precond_imp:
 "\<lbrakk> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>"
  by (fastforce simp add:valid_def)

lemma hoare_vcg_precond_impE:
 "\<lbrakk> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp add:validE_def2)

lemma hoare_seq_ext:
  assumes g_valid: "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>"
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>"
 apply(insert f_valid g_valid)
 apply(blast intro: seq_ext')
done

lemma hoare_vcg_seqE:
  assumes g_valid: "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>A\<rbrace> doE x \<leftarrow> f; g x odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
 apply(insert f_valid g_valid)
 apply(blast intro: seqE')
done

lemma hoare_seq_ext_nobind:
  "\<lbrakk> \<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>;
     \<lbrace>A\<rbrace> f \<lbrace>\<lambda>r s. B s\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> do f; g od \<lbrace>C\<rbrace>"
  apply (clarsimp simp: valid_def bind_def Let_def split_def)
  apply fastforce
done

lemma hoare_seq_ext_nobindE:
  "\<lbrakk> \<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>;
     \<lbrace>A\<rbrace> f \<lbrace>\<lambda>r s. B s\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> doE f; g odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp:validE_def)
  apply (simp add:bindE_def Let_def split_def bind_def lift_def)
  apply (fastforce simp add: valid_def throwError_def return_def lift_def
                  split: sum.splits)
  done

lemma hoare_chain:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>;
    \<And>s. R s \<Longrightarrow> P s;
    \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>"
  by(fastforce simp add:valid_def split_def)

lemma validE_weaken:
  "\<lbrakk> \<lbrace>P'\<rbrace> A \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s; \<And>r s. Q' r s \<Longrightarrow> Q r s; \<And>r s. E' r s \<Longrightarrow> E r s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> A \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def2 split: sum.splits)

lemmas hoare_chainE = validE_weaken

lemma hoare_vcg_handle_elseE:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>;
     \<And>e. \<lbrace>E e\<rbrace> g e \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>;
     \<And>x. \<lbrace>Q x\<rbrace> h x \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle> g <else> h \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>"
  apply (simp add: handle_elseE_def validE_def)
  apply (rule seq_ext)
   apply assumption
  apply (case_tac x, simp_all)
  done

lemma alternative_valid:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> f' \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f OR f' \<lbrace>Q\<rbrace>"
  apply (simp add: valid_def alternative_def)
  apply safe
   apply (simp add: post_by_hoare [OF x])
  apply (simp add: post_by_hoare [OF y])
  done

lemma alternative_wp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P and P'\<rbrace> f OR f' \<lbrace>Q\<rbrace>"
  apply (rule alternative_valid)
   apply (rule hoare_pre_imp [OF _ x], simp)
  apply (rule hoare_pre_imp [OF _ y], simp)
  done

lemma alternativeE_wp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" and y: "\<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>P and P'\<rbrace> f OR f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (unfold validE_def)
  apply (wp add: x y alternative_wp | simp | fold validE_def)+
  done

lemma alternativeE_R_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f' \<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f OR f' \<lbrace>Q\<rbrace>,-"
  apply (simp add: validE_R_def)
  apply (rule alternativeE_wp)
   apply assumption+
  done

lemma alternative_R_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> g -,\<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<sqinter> g -, \<lbrace>Q\<rbrace>"
  by (fastforce simp: alternative_def validE_E_def validE_def valid_def)

lemma select_wp: "\<lbrace>\<lambda>s. \<forall>x \<in> S. Q x s\<rbrace> select S \<lbrace>Q\<rbrace>"
  by (simp add: select_def valid_def)

lemma select_f_wp:
  "\<lbrace>\<lambda>s. \<forall>x\<in>fst S. Q x s\<rbrace> select_f S \<lbrace>Q\<rbrace>"
  by (simp add: select_f_def valid_def)

lemma state_select_wp [wp]: "\<lbrace> \<lambda>s. \<forall>t. (s, t) \<in> f \<longrightarrow> P () t \<rbrace> state_select f \<lbrace> P \<rbrace>"
  apply (clarsimp simp: state_select_def)
  apply (clarsimp simp: valid_def)
  done

lemma condition_wp [wp]:
  "\<lbrakk> \<lbrace> Q \<rbrace> A \<lbrace> P \<rbrace>;  \<lbrace> R \<rbrace> B \<lbrace> P \<rbrace>  \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s. if C s then Q s else R s \<rbrace> condition C A B \<lbrace> P \<rbrace>"
  apply (clarsimp simp: condition_def)
  apply (clarsimp simp: valid_def pred_conj_def pred_neg_def split_def)
  done

lemma conditionE_wp [wp]:
  "\<lbrakk> \<lbrace> P \<rbrace> A \<lbrace> Q \<rbrace>,\<lbrace> R \<rbrace>; \<lbrace> P' \<rbrace> B \<lbrace> Q \<rbrace>,\<lbrace> R \<rbrace> \<rbrakk> \<Longrightarrow>  \<lbrace> \<lambda>s. if C s then P s else P' s \<rbrace> condition C A B \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
  apply (clarsimp simp: condition_def)
  apply (clarsimp simp: validE_def valid_def)
  done

lemma state_assert_wp [wp]: "\<lbrace> \<lambda>s. f s \<longrightarrow> P () s \<rbrace> state_assert f \<lbrace> P \<rbrace>"
  apply (clarsimp simp: state_assert_def get_def
    assert_def bind_def valid_def return_def fail_def)
  done

text {* The weakest precondition handler which works on conjunction *}

lemma hoare_vcg_conj_lift:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  apply (subst bipred_conj_def[symmetric], rule hoare_post_conj)
   apply (rule hoare_pre_imp [OF _ x], simp)
  apply (rule hoare_pre_imp [OF _ y], simp)
  done

lemma hoare_vcg_conj_liftE1:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def validE_R_def validE_def
  apply (clarsimp simp: split_def split: sum.splits)
  apply (erule allE, erule (1) impE)
  apply (erule allE, erule (1) impE)
  apply (drule (1) bspec)
  apply (drule (1) bspec)
  apply clarsimp
  done

lemma hoare_vcg_disj_lift:
  assumes x: "\<lbrace>P\<rbrace>  f \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>"
  apply (simp add: valid_def)
  apply safe
   apply (erule(1) post_by_hoare [OF x])
  apply (erule notE)
  apply (erule(1) post_by_hoare [OF y])
  done

lemma hoare_vcg_const_Ball_lift:
  "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x\<in>S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x\<in>S. Q x rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_vcg_const_Ball_lift_R:
 "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,- \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. \<forall>x \<in> S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> S. Q x rv s\<rbrace>,-"
  apply (simp add: validE_R_def validE_def)
  apply (rule hoare_strengthen_post)
   apply (erule hoare_vcg_const_Ball_lift)
  apply (simp split: sum.splits)
  done

lemma hoare_vcg_all_lift:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_vcg_all_lift_R:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>, -"
  by (rule hoare_vcg_const_Ball_lift_R[where S=UNIV, simplified])


lemma hoare_vcg_imp_lift:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply (erule(1) hoare_vcg_disj_lift)
  done

lemma hoare_vcg_imp_lift':
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<not> P' s \<longrightarrow> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply simp
  apply (erule (1) hoare_vcg_imp_lift)
  done

lemma hoare_absorb_imp:
  "\<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> R rv s  \<rbrace> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s \<rbrace>"
  by (erule hoare_post_imp[rotated], blast)

lemma hoare_weaken_imp:
  "\<lbrakk> \<And>rv s. Q rv s \<Longrightarrow> Q' rv s ;  \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> R rv s\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s\<rbrace>"
  by (clarsimp simp: NonDetMonad.valid_def split_def)

lemma hoare_vcg_const_imp_lift:
  "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> m \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>"
  by (cases P, simp_all add: hoare_vcg_prop)

lemma hoare_vcg_const_imp_lift_R:
  "(P \<Longrightarrow> \<lbrace>Q\<rbrace> m \<lbrace>R\<rbrace>,-) \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>,-"
  by (fastforce simp: validE_R_def validE_def valid_def split_def split: sum.splits)

lemma hoare_weak_lift_imp:
  "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> P' s\<rbrace> f \<lbrace>\<lambda>rv s. P \<longrightarrow> Q rv s\<rbrace>"
  by (auto simp add: valid_def split_def)

lemma hoare_vcg_weaken_imp:
  "\<lbrakk> \<And>rv s. Q rv s \<Longrightarrow> Q' rv s ; \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> R rv s\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s\<rbrace>"
  by (clarsimp simp: valid_def split_def)

lemma hoare_vcg_ex_lift:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>"
  by (clarsimp simp: valid_def, blast)

lemma hoare_vcg_ex_lift_R1:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (fastforce simp: valid_def validE_R_def validE_def split: sum.splits)

(* for instantiations *)
lemma hoare_triv:    "\<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>" .
lemma hoare_trivE:   "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" .
lemma hoare_trivE_R: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-" .
lemma hoare_trivR_R: "\<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>" .

lemma hoare_weaken_preE_E:
  "\<lbrakk> \<lbrace>P'\<rbrace> f -,\<lbrace>Q\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace>"
  by (fastforce simp add: validE_E_def validE_def valid_def)

lemma hoare_vcg_E_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>\<lambda>rv s. E rv s \<and> E' rv s\<rbrace>"
  apply (unfold validE_def validE_E_def)
  apply (rule hoare_post_imp [OF _ hoare_vcg_conj_lift], simp_all)
  apply (case_tac r, simp_all)
  done

lemma hoare_vcg_E_elim:
  "\<lbrakk> \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,- \<rbrakk>
    \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (rule hoare_post_impErr [OF hoare_vcg_E_conj],
      (simp add: validE_R_def)+)

lemma hoare_vcg_R_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk>
    \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,-"
  apply (unfold validE_R_def validE_def)
  apply (rule hoare_post_imp [OF _ hoare_vcg_conj_lift], simp_all)
  apply (case_tac r, simp_all)
  done

lemma valid_validE:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: validE_def)
  done

lemma valid_validE2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q'\<rbrace>; \<And>s. Q' s \<Longrightarrow> Q s; \<And>s. Q' s \<Longrightarrow> E s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>_. E\<rbrace>"
  unfolding valid_def validE_def
  by (clarsimp split: sum.splits) blast

lemma validE_valid: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,\<lbrace>\<lambda>rv. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (unfold validE_def)
  apply (rule hoare_post_imp)
   defer
   apply assumption
  apply (case_tac r, simp_all)
  done

lemma valid_validE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,-"
  by (simp add: validE_R_def hoare_post_impErr [OF valid_validE])

lemma valid_validE_E:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>\<lambda>rv. Q\<rbrace>"
  by (simp add: validE_E_def hoare_post_impErr [OF valid_validE])

lemma validE_validE_R: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by (simp add: validE_R_def)

lemma validE_R_validE: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  by (simp add: validE_R_def)

lemma hoare_post_imp_R: "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,-; \<And>r s. Q' r s \<Longrightarrow> Q r s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  apply (unfold validE_R_def)
  apply (rule hoare_post_impErr, simp+)
  done

lemma hoare_post_comb_imp_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  apply (rule hoare_pre_imp)
   defer
   apply (rule hoare_vcg_conj_lift)
    apply assumption+
  apply simp
  done

lemma hoare_vcg_precond_impE_R: "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,-; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by (unfold validE_R_def, rule hoare_vcg_precond_impE, simp+)

lemma valid_is_triple:
  "valid P f Q = triple_judgement P f (postcondition Q (\<lambda>s f. fst (f s)))"
  by (simp add: triple_judgement_def valid_def postcondition_def)

lemma validE_is_triple:
  "validE P f Q E = triple_judgement P f
    (postconditions (postcondition Q (\<lambda>s f. {(rv, s'). (Inr rv, s') \<in> fst (f s)}))
          (postcondition E (\<lambda>s f. {(rv, s'). (Inl rv, s') \<in> fst (f s)})))"
  apply (simp add: validE_def triple_judgement_def valid_def postcondition_def
                   postconditions_def split_def split: sum.split)
  apply fastforce
  done

lemma validE_R_is_triple:
  "validE_R P f Q = triple_judgement P f
     (postcondition Q (\<lambda>s f. {(rv, s'). (Inr rv, s') \<in> fst (f s)}))"
  by (simp add: validE_R_def validE_is_triple postconditions_def postcondition_def)

lemma validE_E_is_triple:
  "validE_E P f E = triple_judgement P f
     (postcondition E (\<lambda>s f. {(rv, s'). (Inl rv, s') \<in> fst (f s)}))"
  by (simp add: validE_E_def validE_is_triple postconditions_def postcondition_def)

lemmas hoare_wp_combs =
  hoare_post_comb_imp_conj hoare_vcg_precond_imp hoare_vcg_conj_lift

lemmas hoare_wp_combsE =
  hoare_vcg_precond_impE
  hoare_vcg_precond_impE_R
  validE_validE_R
  hoare_vcg_R_conj
  hoare_vcg_E_elim
  hoare_vcg_E_conj

lemmas hoare_wp_state_combsE =
  hoare_vcg_precond_impE[OF valid_validE]
  hoare_vcg_precond_impE_R[OF valid_validE_R]
  valid_validE_R
  hoare_vcg_R_conj[OF valid_validE_R]
  hoare_vcg_E_elim[OF valid_validE_E]
  hoare_vcg_E_conj[OF valid_validE_E]

lemmas hoare_wp_splits [wp_split] =
  hoare_seq_ext hoare_vcg_seqE handleE'_wp handleE_wp
  validE_validE_R [OF hoare_vcg_seqE [OF validE_R_validE]]
  validE_validE_R [OF handleE'_wp [OF validE_R_validE]]
  validE_validE_R [OF handleE_wp [OF validE_R_validE]]
  catch_wp hoare_vcg_if_split hoare_vcg_if_splitE
  validE_validE_R [OF hoare_vcg_if_splitE [OF validE_R_validE validE_R_validE]]
  liftM_wp liftME_wp
  validE_validE_R [OF liftME_wp [OF validE_R_validE]]
  validE_valid

lemmas [wp_comb] = hoare_wp_state_combsE hoare_wp_combsE  hoare_wp_combs

lemmas [wp] = hoare_vcg_prop
              wp_post_taut
              return_wp
              put_wp
              get_wp
              gets_wp
              modify_wp
              returnOk_wp
              throwError_wp
              fail_wp
              failE_wp
              liftE_wp
              select_f_wp

lemmas [wp_trip] = valid_is_triple validE_is_triple validE_E_is_triple validE_R_is_triple


text {* Simplifications on conjunction *}

lemma hoare_post_eq: "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by simp
lemma hoare_post_eqE1: "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp
lemma hoare_post_eqE2: "\<lbrakk> E = E'; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp
lemma hoare_post_eqE_R: "\<lbrakk> Q = Q'; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by simp

lemma pred_conj_apply_elim: "(\<lambda>r. Q r and Q' r) = (\<lambda>r s. Q r s \<and> Q' r s)"
  by (simp add: pred_conj_def)
lemma pred_conj_conj_elim: "(\<lambda>r s. (Q r and Q' r) s \<and> Q'' r s) = (\<lambda>r s. Q r s \<and> Q' r s \<and> Q'' r s)"
  by simp
lemma conj_assoc_apply: "(\<lambda>r s. (Q r s \<and> Q' r s) \<and> Q'' r s) = (\<lambda>r s. Q r s \<and> Q' r s \<and> Q'' r s)"
  by simp
lemma all_elim: "(\<lambda>rv s. \<forall>x. P rv s) = P"
  by simp
lemma all_conj_elim: "(\<lambda>rv s. (\<forall>x. P rv s) \<and> Q rv s) = (\<lambda>rv s. P rv s \<and> Q rv s)"
  by simp

lemmas vcg_rhs_simps = pred_conj_apply_elim pred_conj_conj_elim
          conj_assoc_apply all_elim all_conj_elim

lemma if_apply_reduct: "\<lbrace>P\<rbrace> If P' (f x) (g x) \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> If P' f g x \<lbrace>Q\<rbrace>"
  by (cases P', simp_all)
lemma if_apply_reductE: "\<lbrace>P\<rbrace> If P' (f x) (g x) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> If P' f g x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (cases P', simp_all)
lemma if_apply_reductE_R: "\<lbrace>P\<rbrace> If P' (f x) (g x) \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> If P' f g x \<lbrace>Q\<rbrace>,-"
  by (cases P', simp_all)

lemmas hoare_wp_simps [wp_split] =
  vcg_rhs_simps [THEN hoare_post_eq] vcg_rhs_simps [THEN hoare_post_eqE1]
  vcg_rhs_simps [THEN hoare_post_eqE2] vcg_rhs_simps [THEN hoare_post_eqE_R]
  if_apply_reduct if_apply_reductE if_apply_reductE_R TrueI

schematic_goal if_apply_test: "\<lbrace>?Q\<rbrace> (if A then returnOk else K fail) x \<lbrace>P\<rbrace>,\<lbrace>E\<rbrace>"
  by wpsimp

lemma hoare_elim_pred_conj:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>"
  by (unfold pred_conj_def)

lemma hoare_elim_pred_conjE1:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>,\<lbrace>E\<rbrace>"
  by (unfold pred_conj_def)

lemma hoare_elim_pred_conjE2:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>x s. E x s \<and> E' x s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>x. E x and E' x\<rbrace>"
  by (unfold pred_conj_def)

lemma hoare_elim_pred_conjE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>,-"
  by (unfold pred_conj_def)

lemmas hoare_wp_pred_conj_elims =
  hoare_elim_pred_conj hoare_elim_pred_conjE1
  hoare_elim_pred_conjE2 hoare_elim_pred_conjE_R

lemmas hoare_weaken_preE = hoare_vcg_precond_impE

lemmas hoare_pre [wp_pre] =
  hoare_weaken_pre
  hoare_weaken_preE
  hoare_vcg_precond_impE_R
  hoare_weaken_preE_E

declare no_fail_pre [wp_pre]

bundle no_pre = hoare_pre [wp_pre del] no_fail_pre [wp_pre del]

text {* Miscellaneous lemmas on hoare triples *}

lemma hoare_vcg_mp:
  assumes a: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes b: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<longrightarrow> Q' r s\<rbrace>"
  shows "\<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  using assms
  by (auto simp: valid_def split_def)

(* note about this precond stuff: rules get a chance to bind directly
   before any of their combined forms. As a result, these precondition
   implication rules are only used when needed. *)

lemma hoare_add_post:
  assumes r: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>"
  assumes impP: "\<And>s. P s \<Longrightarrow> P' s"
  assumes impQ: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace>"
  shows "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule r)
    apply (rule impQ)
   apply simp
   apply (erule impP)
  apply simp
  done

lemma hoare_whenE_wp:
  "(P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>if P then Q else R ()\<rbrace> whenE P f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding whenE_def by clarsimp wp

lemma hoare_gen_asmE:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,-) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (simp add: validE_R_def validE_def valid_def) blast

lemma hoare_list_case:
  assumes P1: "\<lbrace>P1\<rbrace> f f1 \<lbrace>Q\<rbrace>"
  assumes P2: "\<And>y ys. xs = y#ys \<Longrightarrow> \<lbrace>P2 y ys\<rbrace> f (f2 y ys) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>case xs of [] \<Rightarrow> P1 | y#ys \<Rightarrow> P2 y ys\<rbrace>
         f (case xs of [] \<Rightarrow> f1 | y#ys \<Rightarrow> f2 y ys)
         \<lbrace>Q\<rbrace>"
  apply (cases xs; simp)
   apply (rule P1)
  apply (rule P2)
  apply simp
  done

lemma hoare_unless_wp:
  "(\<not>P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>) \<Longrightarrow> \<lbrace>if P then R () else Q\<rbrace> unless P f \<lbrace>R\<rbrace>"
  unfolding unless_def by wp auto

lemma hoare_use_eq:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m \<lbrace>\<lambda>rv s. P (f s)\<rbrace>"
  assumes y: "\<And>f. \<lbrace>\<lambda>s. P f s\<rbrace> m \<lbrace>\<lambda>rv s. Q f s\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (f s) s\<rbrace> m \<lbrace>\<lambda>rv s. Q (f s :: 'c :: type) s \<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. \<exists>f'. f' = f s \<and> Q f' s" in hoare_post_imp)
   apply simp
  apply (wpsimp wp: hoare_vcg_ex_lift x y)
  done

lemma hoare_return_sp:
  "\<lbrace>P\<rbrace> return x \<lbrace>\<lambda>r. P and K (r = x)\<rbrace>"
  by (simp add: valid_def return_def)

lemma hoare_fail_any [simp]:
  "\<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>" by wp

lemma hoare_failE [simp]: "\<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" by  wp

lemma hoare_FalseE [simp]:
  "\<lbrace>\<lambda>s. False\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: valid_def validE_def)

lemma hoare_K_bind [wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> K_bind f x \<lbrace>Q\<rbrace>"
  by simp

text {* Setting up the precondition case splitter. *}

lemma wpc_helper_valid:
  "\<lbrace>Q\<rbrace> g \<lbrace>S\<rbrace> \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> g \<lbrace>S\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)

lemma wpc_helper_validE:
  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)

lemma wpc_helper_validE_R:
  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,-"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)

lemma wpc_helper_validR_R:
  "\<lbrace>Q\<rbrace> f -,\<lbrace>E\<rbrace> \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> f -,\<lbrace>E\<rbrace>"
  by (clarsimp simp: wpc_helper_def elim!: hoare_pre)

lemma wpc_helper_no_fail_final:
  "no_fail Q f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (no_fail P f)"
  by (clarsimp simp: wpc_helper_def elim!: no_fail_pre)

lemma wpc_helper_empty_fail_final:
  "empty_fail f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (empty_fail f)"
  by (clarsimp simp: wpc_helper_def)

lemma wpc_helper_validNF:
  "\<lbrace>Q\<rbrace> g \<lbrace>S\<rbrace>! \<Longrightarrow> wpc_helper (P, P') (Q, Q') \<lbrace>P\<rbrace> g \<lbrace>S\<rbrace>!"
  apply (clarsimp simp: wpc_helper_def)
  by (metis hoare_wp_combs(2) no_fail_pre validNF_def)

wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>" wpc_helper_valid
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>" wpc_helper_validE
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,-" wpc_helper_validE_R
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m -,\<lbrace>E\<rbrace>" wpc_helper_validR_R
wpc_setup "\<lambda>m. no_fail P m" wpc_helper_no_fail_final
wpc_setup "\<lambda>m. empty_fail m" wpc_helper_empty_fail_final
wpc_setup "\<lambda>m. \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>!" wpc_helper_validNF

lemma in_liftM:
 "((r, s') \<in> fst (liftM t f s)) = (\<exists>r'. (r', s') \<in> fst (f s) \<and> r = t r')"
  apply (simp add: liftM_def return_def bind_def)
  apply (simp add: Bex_def)
  done

(* FIXME: eliminate *)
lemmas handy_liftM_lemma = in_liftM

lemma hoare_fun_app_wp[wp]:
  "\<lbrace>P\<rbrace> f' x \<lbrace>Q'\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f' $ x \<lbrace>Q'\<rbrace>"
  "\<lbrace>P\<rbrace> f x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f $ x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  "\<lbrace>P\<rbrace> f x \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f $ x \<lbrace>Q\<rbrace>,-"
  "\<lbrace>P\<rbrace> f x -,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f $ x -,\<lbrace>E\<rbrace>"
  by simp+

lemma hoare_validE_pred_conj:
  "\<lbrakk> \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace>f\<lbrace>R\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>Q And R\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def validE_def by (simp add: split_def split: sum.splits)

lemma hoare_validE_conj:
  "\<lbrakk> \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>P\<rbrace>f\<lbrace>R\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> R r s\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding valid_def validE_def by (simp add: split_def split: sum.splits)

lemma hoare_valid_validE:
  "\<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. Q\<rbrace>,\<lbrace>\<lambda>r. Q\<rbrace>"
  unfolding valid_def validE_def by (simp add: split_def split: sum.splits)

lemma liftE_validE_E [wp]:
  "\<lbrace>\<top>\<rbrace> liftE f -, \<lbrace>Q\<rbrace>"
  by (clarsimp simp: validE_E_def valid_def)

lemma validE_validE_E [wp_comb]:
  "\<lbrace>P\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>, \<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -, \<lbrace>E\<rbrace>"
  by (simp add: validE_E_def)

lemma validE_E_validE:
  "\<lbrace>P\<rbrace> f -, \<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: validE_E_def)

(*
 * if_validE_E:
 *
 * \<lbrakk>?P1 \<Longrightarrow> \<lbrace>?Q1\<rbrace> ?f1 -, \<lbrace>?E\<rbrace>; \<not> ?P1 \<Longrightarrow> \<lbrace>?R1\<rbrace> ?g1 -, \<lbrace>?E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. (?P1 \<longrightarrow> ?Q1 s) \<and> (\<not> ?P1 \<longrightarrow> ?R1 s)\<rbrace> if ?P1 then ?f1 else ?g1 -, \<lbrace>?E\<rbrace>
 *)
lemmas if_validE_E [wp_split] =
  validE_validE_E [OF hoare_vcg_if_splitE [OF validE_E_validE validE_E_validE]]

lemma returnOk_E [wp]:
  "\<lbrace>\<top>\<rbrace> returnOk r -, \<lbrace>Q\<rbrace>"
  by (simp add: validE_E_def) wp

lemma hoare_drop_imp:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp: valid_def)

lemma hoare_drop_impE:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q s\<rbrace>, \<lbrace>E\<rbrace>"
  by (simp add: validE_weaken)

lemma hoare_drop_impE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>, -"
  by (auto simp: validE_R_def validE_def valid_def split_def split: sum.splits)

lemma hoare_drop_impE_E:
  "\<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>\<lambda>r s. R r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp: validE_E_def validE_def valid_def split_def split: sum.splits)

lemmas hoare_drop_imps = hoare_drop_imp hoare_drop_impE_R hoare_drop_impE_E

lemma bind_det_exec:
  "fst (a s) = {(r,s')} \<Longrightarrow> fst ((a >>= b) s) = fst (b r s')"
  by (simp add: bind_def)

lemma in_bind_det_exec:
  "fst (a s) = {(r,s')} \<Longrightarrow> (s'' \<in> fst ((a >>= b) s)) = (s'' \<in> fst (b r s'))"
  by (simp add: bind_def)

lemma exec_put:
  "(put s' >>= m) s = m () s'"
  by (simp add: bind_def put_def)

lemma bind_execI:
  "\<lbrakk> (r'',s'') \<in> fst (f s); \<exists>x \<in> fst (g r'' s''). P x \<rbrakk> \<Longrightarrow>
  \<exists>x \<in> fst ((f >>= g) s). P x"
  by (force simp: in_bind split_def bind_def)

lemma True_E_E [wp]: "\<lbrace>\<top>\<rbrace> f -,\<lbrace>\<top>\<top>\<rbrace>"
  by (auto simp: validE_E_def validE_def valid_def split: sum.splits)

(*
 * \<lbrakk>\<And>x. \<lbrace>?B1 x\<rbrace> ?g1 x -, \<lbrace>?E\<rbrace>; \<lbrace>?P\<rbrace> ?f1 \<lbrace>?B1\<rbrace>, \<lbrace>?E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>?P\<rbrace> ?f1 >>=E ?g1 -, \<lbrace>?E\<rbrace>
 *)
lemmas [wp_split] =
  validE_validE_E [OF hoare_vcg_seqE [OF validE_E_validE]]

lemma case_option_wp:
  assumes x: "\<And>x. \<lbrace>P x\<rbrace> m x \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> m' \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>\<lambda>s. (x = None \<longrightarrow> P' s) \<and> (x \<noteq> None \<longrightarrow> P (the x) s)\<rbrace>
                case_option m' m x \<lbrace>Q\<rbrace>"
  apply (cases x; simp)
   apply (rule y)
  apply (rule x)
  done

lemma case_option_wpE:
  assumes x: "\<And>x. \<lbrace>P x\<rbrace> m x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> m' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>\<lambda>s. (x = None \<longrightarrow> P' s) \<and> (x \<noteq> None \<longrightarrow> P (the x) s)\<rbrace>
                case_option m' m x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (cases x; simp)
   apply (rule y)
  apply (rule x)
  done

lemma in_bindE:
  "(rv, s') \<in> fst ((f >>=E (\<lambda>rv'. g rv')) s) =
  ((\<exists>ex. rv = Inl ex \<and> (Inl ex, s') \<in> fst (f s)) \<or>
  (\<exists>rv' s''. (rv, s') \<in> fst (g rv' s'') \<and> (Inr rv', s'') \<in> fst (f s)))"
  apply (rule iffI)
   apply (clarsimp simp: bindE_def bind_def)
   apply (case_tac a)
    apply (clarsimp simp: lift_def throwError_def return_def)
   apply (clarsimp simp: lift_def)
  apply safe
   apply (clarsimp simp: bindE_def bind_def)
   apply (erule rev_bexI)
   apply (simp add: lift_def throwError_def return_def)
  apply (clarsimp simp: bindE_def bind_def)
  apply (erule rev_bexI)
  apply (simp add: lift_def)
  done

(*
 * \<lbrace>?P\<rbrace> ?m1 -, \<lbrace>?E\<rbrace> \<Longrightarrow> \<lbrace>?P\<rbrace> liftME ?f1 ?m1 -, \<lbrace>?E\<rbrace>
 *)
lemmas [wp_split] = validE_validE_E [OF liftME_wp, simplified, OF validE_E_validE]

lemma assert_A_True[simp]: "assert True = return ()"
  by (simp add: assert_def)

lemma assert_wp [wp]: "\<lbrace>\<lambda>s. P \<longrightarrow> Q () s\<rbrace> assert P \<lbrace>Q\<rbrace>"
  by (cases P, (simp add: assert_def | wp)+)

lemma list_cases_wp:
  assumes a: "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>"
  assumes b: "\<And>x xs. ts = x#xs \<Longrightarrow> \<lbrace>P_B x xs\<rbrace> b x xs \<lbrace>Q\<rbrace>"
  shows "\<lbrace>case_list P_A P_B ts\<rbrace> case ts of [] \<Rightarrow> a | x # xs \<Rightarrow> b x xs \<lbrace>Q\<rbrace>"
  by (cases ts, auto simp: a b)

(* FIXME: make wp *)
lemma whenE_throwError_wp:
  "\<lbrace>\<lambda>s. \<not>Q \<longrightarrow> P s\<rbrace> whenE Q (throwError e) \<lbrace>\<lambda>rv. P\<rbrace>, -"
  unfolding whenE_def by wpsimp

lemma select_throwError_wp:
  "\<lbrace>\<lambda>s. \<forall>x\<in>S. Q x s\<rbrace> select S >>= throwError -, \<lbrace>Q\<rbrace>"
  by (simp add: bind_def throwError_def return_def select_def validE_E_def
                validE_def valid_def)


section "validNF Rules"

subsection "Basic validNF theorems"

lemma validNF [intro?]:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>; no_fail P f \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def)

lemma validNF_valid: "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  by (clarsimp simp: validNF_def)

lemma validNF_no_fail: "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>! \<rbrakk> \<Longrightarrow> no_fail P f"
  by (clarsimp simp: validNF_def)

lemma snd_validNF:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!; P s \<rbrakk> \<Longrightarrow> \<not> snd (f s)"
  by (clarsimp simp: validNF_def no_fail_def)

lemma use_validNF:
  "\<lbrakk> (r', s') \<in> fst (f s); \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!; P s \<rbrakk> \<Longrightarrow> Q r' s'"
  by (fastforce simp: validNF_def valid_def)

subsection "validNF weakest pre-condition rules"

lemma validNF_return [wp]:
  "\<lbrace> P x \<rbrace> return x \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_get [wp]:
  "\<lbrace> \<lambda>s. P s s  \<rbrace> get \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_put [wp]:
  "\<lbrace> \<lambda>s. P () x  \<rbrace> put x \<lbrace> P \<rbrace>!"
  by (wp validNF)+

lemma validNF_K_bind [wp]:
  "\<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> K_bind x f \<lbrace> Q \<rbrace>!"
  by simp

lemma validNF_fail [wp]:
  "\<lbrace> \<lambda>s. False \<rbrace> fail \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def fail_def no_fail_def)

lemma validNF_prop [wp_unsafe]:
  "\<lbrakk> no_fail (\<lambda>s. P) f \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s. P \<rbrace> f \<lbrace> \<lambda>rv s. P \<rbrace>!"
  by (wp validNF)+

lemma validNF_post_conj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace>!; \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> Q And R \<rbrace>!"
  by (clarsimp simp: validNF_def)

lemma no_fail_or:
  "\<lbrakk>no_fail P a; no_fail Q a\<rbrakk> \<Longrightarrow> no_fail (P or Q) a"
  by (clarsimp simp: no_fail_def)

lemma validNF_pre_disj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>!; \<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P or Q \<rbrace> a \<lbrace> R \<rbrace>!"
  by (rule validNF) (auto dest: validNF_valid validNF_no_fail intro: no_fail_or)

(*
 * Set up combination rules for WP, which also requires
 * a "wp_trip" rule for validNF.
 *)

definition "validNF_property Q s b \<equiv> \<not> snd (b s) \<and> (\<forall>(r', s') \<in> fst (b s). Q r' s')"

lemma validNF_is_triple [wp_trip]:
  "validNF P f Q = triple_judgement P f (validNF_property Q)"
  apply (clarsimp simp: validNF_def triple_judgement_def validNF_property_def)
  apply (auto simp: no_fail_def valid_def)
  done

lemma validNF_weaken_pre [wp_comb]:
  "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>!; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>!"
  by (metis hoare_pre_imp no_fail_pre validNF_def)

lemma validNF_post_comb_imp_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>!; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  by (fastforce simp: validNF_def valid_def)

lemma validNF_post_comb_conj_L:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply force
  done

lemma validNF_post_comb_conj_R:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply force
  done

lemma validNF_post_comb_conj:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply force
  done

lemma validNF_if_split [wp_split]:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>!; \<not> P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>!"
  by simp

lemma validNF_vcg_conj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow>
      \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>!"
  apply (subst bipred_conj_def[symmetric], rule validNF_post_conj)
   apply (erule validNF_weaken_pre, fastforce)
  apply (erule validNF_weaken_pre, fastforce)
  done

lemma validNF_vcg_disj_lift:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>! \<rbrakk> \<Longrightarrow>
       \<lbrace>\<lambda>s. P s \<or> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<or> Q' rv s\<rbrace>!"
  apply (clarsimp simp: validNF_def)
  apply safe
   apply (auto intro!: hoare_vcg_disj_lift)[1]
  apply (clarsimp simp: no_fail_def)
  done

lemma validNF_vcg_all_lift [wp]:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>!"
  apply atomize
  apply (rule validNF)
   apply (clarsimp simp: validNF_def)
   apply (rule hoare_vcg_all_lift)
   apply force
  apply (clarsimp simp: no_fail_def validNF_def)
  done

lemma validNF_bind [wp_split]:
  "\<lbrakk> \<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>!; \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>! \<rbrakk> \<Longrightarrow>
       \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>!"
  apply (rule validNF)
   apply (metis validNF_valid hoare_seq_ext)
  apply (clarsimp simp: no_fail_def validNF_def bind_def' valid_def)
  apply blast
  done

lemmas validNF_seq_ext = validNF_bind

subsection "validNF compound rules"

lemma validNF_state_assert [wp]:
  "\<lbrace> \<lambda>s. P () s \<and> G s  \<rbrace> state_assert G \<lbrace> P \<rbrace>!"
  apply (rule validNF)
   apply wpsimp
  apply (clarsimp simp: no_fail_def state_assert_def
              bind_def' assert_def return_def get_def)
  done

lemma validNF_modify [wp]:
  "\<lbrace> \<lambda>s. P () (f s) \<rbrace> modify f \<lbrace> P \<rbrace>!"
  apply (clarsimp simp: modify_def)
  apply wp
  done

lemma validNF_gets [wp]:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>P\<rbrace>!"
  apply (clarsimp simp: gets_def)
  apply wp
  done

lemma validNF_condition [wp]:
  "\<lbrakk> \<lbrace> Q \<rbrace> A \<lbrace>P\<rbrace>!; \<lbrace> R \<rbrace> B \<lbrace>P\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. if C s then Q s else R s\<rbrace> condition C A B \<lbrace>P\<rbrace>!"
  apply rule
   apply (drule validNF_valid)+
   apply (erule (1) condition_wp)
  apply (drule validNF_no_fail)+
  apply (clarsimp simp: no_fail_def condition_def)
  done

lemma validNF_alt_def:
  "validNF P m Q = (\<forall>s. P s \<longrightarrow> ((\<forall>(r', s') \<in> fst (m s). Q r' s') \<and> \<not> snd (m s)))"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_assert [wp]:
    "\<lbrace> (\<lambda>s. P) and (R ()) \<rbrace> assert P \<lbrace> R \<rbrace>!"
  apply (rule validNF)
   apply (clarsimp simp: valid_def in_return)
  apply (clarsimp simp: no_fail_def return_def)
  done

lemma validNF_false_pre:
  "\<lbrace> \<lambda>_. False \<rbrace> P \<lbrace> Q \<rbrace>!"
  by (clarsimp simp: validNF_def no_fail_def)

lemma validNF_chain:
   "\<lbrakk>\<lbrace>P'\<rbrace> a \<lbrace>R'\<rbrace>!; \<And>s. P s \<Longrightarrow> P' s; \<And>r s. R' r s \<Longrightarrow> R r s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def Ball_def)

lemma validNF_case_prod [wp]:
  "\<lbrakk> \<And>x y. validNF (P x y) (B x y) Q \<rbrakk> \<Longrightarrow> validNF (case_prod P v) (case_prod (\<lambda>x y. B x y) v) Q"
  by (metis prod.exhaust split_conv)

lemma validE_NF_case_prod [wp]:
    "\<lbrakk> \<And>a b. \<lbrace>P a b\<rbrace> f a b \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow>
          \<lbrace>case x of (a, b) \<Rightarrow> P a b\<rbrace> case x of (a, b) \<Rightarrow> f a b \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def)
  apply (erule validNF_case_prod)
  done

lemma no_fail_is_validNF_True: "no_fail P s = (\<lbrace> P \<rbrace> s \<lbrace> \<lambda>_ _. True \<rbrace>!)"
  by (clarsimp simp: no_fail_def validNF_def valid_def)

subsection "validNF reasoning in the exception monad"

lemma validE_NF [intro?]:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>; no_fail P f \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_def)
  done

lemma validE_NF_valid:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (clarsimp simp: validE_NF_def)
  done

lemma validE_NF_no_fail:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> no_fail P f"
  apply (clarsimp simp: validE_NF_def)
  done

lemma validE_NF_weaken_pre [wp_comb]:
   "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>!; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def)
  apply (erule validNF_weaken_pre)
  apply simp
  done

lemma validE_NF_post_comb_conj_L:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace> E \<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace> \<lambda>_ _. True \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def validE_def validNF_def
          valid_def no_fail_def split: sum.splits)
  apply force
  done

lemma validE_NF_post_comb_conj_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace> \<lambda>_ _. True \<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def validE_def validNF_def
          valid_def no_fail_def split: sum.splits)
  apply force
  done

lemma validE_NF_post_comb_conj:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace> E \<rbrace>!; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace> E \<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, \<lbrace> E \<rbrace>!"
  apply (clarsimp simp: validE_NF_alt_def validE_def validNF_def
          valid_def no_fail_def split: sum.splits)
  apply force
  done

lemma validE_NF_chain:
   "\<lbrakk>\<lbrace>P'\<rbrace> a \<lbrace>R'\<rbrace>,\<lbrace>E'\<rbrace>!;
    \<And>s. P s \<Longrightarrow> P' s;
    \<And>r' s'. R' r' s' \<Longrightarrow> R r' s';
    \<And>r'' s''. E' r'' s'' \<Longrightarrow> E r'' s''\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<rbrace> a \<lbrace>\<lambda>r' s'. R r' s'\<rbrace>,\<lbrace>\<lambda>r'' s''. E r'' s''\<rbrace>!"
  by (fastforce simp: validE_NF_def validE_def2 no_fail_def Ball_def split: sum.splits)

lemma validE_NF_bind_wp [wp]:
  "\<lbrakk>\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>!; \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>, \<lbrace>E\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> f >>=E (\<lambda>x. g x) \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>!"
  apply (unfold validE_NF_alt_def bindE_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  apply wpsimp
  done

lemma validNF_catch [wp]:
  "\<lbrakk>\<And>x. \<lbrace>E x\<rbrace> handler x \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f <catch> (\<lambda>x. handler x) \<lbrace>Q\<rbrace>!"
  apply (unfold validE_NF_alt_def catch_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  apply wp
  done

lemma validNF_throwError [wp]:
  "\<lbrace>E e\<rbrace> throwError e \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
  by (unfold validE_NF_alt_def throwError_def o_def) wpsimp

lemma validNF_returnOk [wp]:
  "\<lbrace>P e\<rbrace> returnOk e \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
  by (clarsimp simp: validE_NF_alt_def returnOk_def) wpsimp

lemma validNF_whenE [wp]:
  "(P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!) \<Longrightarrow> \<lbrace>if P then Q else R ()\<rbrace> whenE P f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!"
  unfolding whenE_def by clarsimp wp

lemma validNF_nobindE [wp]:
  "\<lbrakk> \<lbrace>B\<rbrace> g \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>!;
     \<lbrace>A\<rbrace> f \<lbrace>\<lambda>r s. B s\<rbrace>,\<lbrace>E\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> doE f; g odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>!"
  by clarsimp wp

(*
 * Setup triple rules for validE_NF so that we can use the
 * "wp_comb" attribute.
 *)

definition "validE_NF_property Q E s b \<equiv> \<not> snd (b s)
       \<and> (\<forall>(r', s') \<in> fst (b s). case r' of Inl x \<Rightarrow> E x s' | Inr x \<Rightarrow> Q x s')"

lemma validE_NF_is_triple [wp_trip]:
  "validE_NF P f Q E = triple_judgement P f (validE_NF_property Q E)"
  apply (clarsimp simp: validE_NF_def validE_def2 no_fail_def triple_judgement_def
           validE_NF_property_def split: sum.splits)
  apply blast
  done

lemmas [wp_comb] = validE_NF_weaken_pre

lemma validNF_cong:
   "\<lbrakk> \<And>s. P s = P' s; \<And>s. P s \<Longrightarrow> m s = m' s;
           \<And>r' s' s. \<lbrakk> P s; (r', s') \<in> fst (m s) \<rbrakk> \<Longrightarrow> Q r' s' = Q' r' s' \<rbrakk> \<Longrightarrow>
     (\<lbrace> P \<rbrace> m \<lbrace> Q \<rbrace>!) = (\<lbrace> P' \<rbrace> m' \<lbrace> Q' \<rbrace>!)"
  by (fastforce simp: validNF_alt_def)

lemma validE_NF_liftE [wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>! \<Longrightarrow> \<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  by (wpsimp simp: validE_NF_alt_def liftE_def)

lemma validE_NF_handleE' [wp]:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle2> (\<lambda>x. handler x) \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (unfold validE_NF_alt_def handleE'_def)
  apply (rule validNF_bind [rotated])
   apply assumption
  apply (clarsimp split: sum.splits)
  apply wpsimp
  done

lemma validE_NF_handleE [wp]:
  "\<lbrakk> \<And>x. \<lbrace>F x\<rbrace> handler x \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>F\<rbrace>! \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f <handle> handler \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>!"
  apply (unfold handleE_def)
  apply (metis validE_NF_handleE')
  done

lemma validE_NF_condition [wp]:
  "\<lbrakk> \<lbrace> Q \<rbrace> A \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!; \<lbrace> R \<rbrace> B \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!\<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>s. if C s then Q s else R s\<rbrace> condition C A B \<lbrace>P\<rbrace>,\<lbrace> E \<rbrace>!"
  apply rule
   apply (drule validE_NF_valid)+
   apply wp
  apply (drule validE_NF_no_fail)+
  apply (clarsimp simp: no_fail_def condition_def)
  done

text {* Strengthen setup. *}

context strengthen_implementation begin

lemma strengthen_hoare [strg]:
  "(\<And>r s. st F (op \<longrightarrow>) (Q r s) (R r s))
    \<Longrightarrow> st F (op \<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>)"
  by (cases F, auto elim: hoare_strengthen_post)

lemma strengthen_validE_R_cong[strg]:
  "(\<And>r s. st F (op \<longrightarrow>) (Q r s) (R r s))
    \<Longrightarrow> st F (op \<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, -)"
  by (cases F, auto intro: hoare_post_imp_R)

lemma strengthen_validE_cong[strg]:
  "(\<And>r s. st F (op \<longrightarrow>) (Q r s) (R r s))
    \<Longrightarrow> (\<And>r s. st F (op \<longrightarrow>) (S r s) (T r s))
    \<Longrightarrow> st F (op \<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_post_impErr)

lemma strengthen_validE_E_cong[strg]:
  "(\<And>r s. st F (op \<longrightarrow>) (S r s) (T r s))
    \<Longrightarrow> st F (op \<longrightarrow>) (\<lbrace>P\<rbrace> f -, \<lbrace>S\<rbrace>) (\<lbrace>P\<rbrace> f -, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_post_impErr simp: validE_E_def)

end

end
