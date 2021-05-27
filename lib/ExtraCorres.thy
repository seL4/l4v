(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ExtraCorres
imports Corres_UL
begin

lemma corres_mapM:
  assumes x: "r [] []"
  assumes y: "\<And>x xs y ys. \<lbrakk> r xs ys; r' x y \<rbrakk> \<Longrightarrow> r (x # xs) (y # ys)"
  assumes z: "\<And>x y. (x, y) \<in> S \<Longrightarrow> corres_underlying R nf nf' r' P P' (f x) (f' y)"
  assumes w: "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
             "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P'\<rbrace> f' y \<lbrace>\<lambda>rv. P'\<rbrace>"
  shows      "\<lbrakk> length xs = length ys; set (zip xs ys) \<subseteq> S \<rbrakk> \<Longrightarrow>
                   corres_underlying R nf nf' r P P' (mapM f xs) (mapM f' ys)"
proof (induct xs ys rule: list_induct2)
  case Nil
  show ?case
    by (simp add: mapM_def sequence_def x)
next
  case (Cons a as b bs)
  from Cons have P: "(a, b) \<in> S"
    by simp
  from Cons have Q: "corres_underlying R nf nf' r P P' (mapM f as) (mapM f' bs)"
    by simp
  show ?case
    apply (simp add: mapM_Cons)
    apply (rule corres_guard_imp)
      apply (rule corres_split_deprecated[OF _ z [OF P] w [OF P]])
      apply (rule corres_split' [OF Q])
        apply (rule corres_trivial, simp add: y)
       apply (wp | simp)+
    done
qed

(* list_all2 has _much_ nicer simps than set (zip _ _).
    See KernelInit_R: corres_init_objs for an example *)
lemma corres_mapM_list_all2:
  assumes rn: "r [] []"
  and     rc: "\<And>x xs y ys. \<lbrakk> r xs ys; r' x y \<rbrakk> \<Longrightarrow> r (x # xs) (y # ys)"
  and   corr: "\<And>x xs y ys. \<lbrakk> S x y; list_all2 S xs ys \<rbrakk>
               \<Longrightarrow> corres_underlying sr nf nf' r' (Q (x # xs)) (Q' (y # ys)) (f x) (f' y)"
  and     ha: "\<And>x xs y. \<lbrakk> S x y; suffix (x#xs) as \<rbrakk> \<Longrightarrow> \<lbrace>Q  (x # xs)\<rbrace> f x \<lbrace>\<lambda>r. Q xs\<rbrace>"
  and     hc: "\<And>x y ys. \<lbrakk> S x y; suffix (y#ys) cs \<rbrakk> \<Longrightarrow> \<lbrace>Q' (y # ys) \<rbrace> f' y \<lbrace>\<lambda>r. Q' ys\<rbrace>"
  and   lall: "list_all2 S as cs"
  shows       "corres_underlying sr nf nf' r (Q as) (Q' cs) (mapM f as) (mapM f' cs)"
  using lall
proof (induct rule: list_all2_induct_suffixeq)
  case Nil
  thus ?case
    unfolding mapM_def sequence_def by (auto intro: rn)
next
  case  (Cons x xs y ys)

  have corr': "corres_underlying sr nf nf' r' (Q (x # xs)) (Q' (y # ys)) (f x) (f' y)"
  proof (rule corr)
    show "list_all2 S xs ys" by (simp add: Cons)
  qed fact+

  show ?case
    apply (simp add: mapM_Cons)
    apply (rule corres_split' [OF corr' _ ha [OF Cons(2)] hc [OF Cons(2)]])
    apply (rule corres_split' [OF Cons(3) _ hoare_post_taut hoare_post_taut])
    apply (simp add: rc)
    apply (rule Cons.hyps)+
    done
qed

lemma corres_mapM_x:
  assumes x: "\<And>x y. (x, y) \<in> S \<Longrightarrow> corres_underlying sr nf nf' dc P P' (f x) (f' y)"
  assumes y: "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
             "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P'\<rbrace> f' y \<lbrace>\<lambda>rv. P'\<rbrace>"
  assumes z: "length xs = length ys"
  assumes w: "set (zip xs ys) \<subseteq> S"
  shows      "corres_underlying sr nf nf' dc P P' (mapM_x f xs) (mapM_x f' ys)"
  apply (simp add: mapM_x_mapM)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_trivial, simp)
      apply (rule corres_mapM [OF _ _ x y z w])
          apply (simp | wp)+
  done

lemma corres_mapM_scheme:
  assumes x: "r [] []"
  assumes z: "\<And>x y. (x, y) \<in> S
                \<Longrightarrow> corres_underlying R nf nf' r' (Q x and P) (Q' y and P') (f x) (f' y)"
  assumes y: "\<And>x xs y ys. \<lbrakk> r xs ys; r' x y \<rbrakk> \<Longrightarrow> r (x # xs) (y # ys)"
  assumes w: "\<And>x y x'. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q x' and K (x' \<noteq> x)\<rbrace> f x \<lbrace>\<lambda>_. Q x'\<rbrace>"
             "\<And>x y y'. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q' y' and K (y' \<noteq> y)\<rbrace> f' y \<lbrace>\<lambda>_. Q' y'\<rbrace>"
  assumes w': "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q x and P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
              "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q' y and P'\<rbrace> f' y \<lbrace>\<lambda>rv. P'\<rbrace>"
  shows      "\<lbrakk> length xs = length ys; set (zip xs ys) \<subseteq> S; distinct xs; distinct ys \<rbrakk>
              \<Longrightarrow> corres_underlying R nf nf' r
                                    ((\<lambda>s. \<forall>t\<in>set xs. Q t s) and P) ((\<lambda>s. \<forall>t\<in>set ys. Q' t s) and P')
                                    (mapM f xs) (mapM f' ys)"
  apply (rule corres_guard_imp)
    apply (rule corres_mapM_list_all2[where Q="\<lambda>xs s. P s \<and> list_all (\<lambda>x. Q x s) xs \<and> distinct xs"
                                        and Q'="\<lambda>xs s. P' s \<and> list_all (\<lambda>x. Q' x s) xs \<and> distinct xs"
                                        and S="\<lambda>x y. (x,y) \<in> S"])
         apply (rule x)
        apply (erule (1) y)
       apply (rule corres_guard_imp[OF z]; fastforce simp: list_all2_iff)
      apply (wpsimp wp: w w' hoare_vcg_ball_lift simp: list_all_iff)
     apply (wpsimp wp: w w' hoare_vcg_ball_lift simp: list_all_iff)
    apply (fastforce simp: list_all2_iff)
   apply (cases xs; fastforce simp: list_all_iff)
  apply (cases ys; fastforce simp: list_all_iff)
  done

lemma corres_mapM_x_scheme:
  assumes x: "\<And>x y. (x, y) \<in> S
                \<Longrightarrow> corres_underlying sr nf nf' dc (Q x and P) (Q' y and P') (f x) (f' y)"
  assumes y: "\<And>x y x'. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q x' and K (x' \<noteq> x)\<rbrace> f x \<lbrace>\<lambda>_. Q x'\<rbrace>"
             "\<And>x y y'. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q' y' and K (y' \<noteq> y)\<rbrace> f' y \<lbrace>\<lambda>_. Q' y'\<rbrace>"
  assumes y': "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q x and P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>"
              "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>Q' y and P'\<rbrace> f' y \<lbrace>\<lambda>_. P'\<rbrace>"
  assumes z: "length xs = length ys"
  assumes w: "set (zip xs ys) \<subseteq> S"
  assumes v: "distinct xs"
             "distinct ys"
  shows "corres_underlying sr nf nf' dc
                           ((\<lambda>s. \<forall>t\<in>set xs. Q t s) and P) ((\<lambda>s. \<forall>t\<in>set ys. Q' t s) and P')
                           (mapM_x f xs) (mapM_x f' ys)"
  apply (subst mapM_x_mapM)+
    apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ corres_mapM_scheme[OF _ x, where S=S]])
                 apply (rule corres_return_trivial)
                apply (wpsimp wp: y y' simp: z w v)+
  done

lemma corres_mapME:
  assumes x: "r [] []"
  assumes y: "\<And>x xs y ys. \<lbrakk> r xs ys; r' x y \<rbrakk> \<Longrightarrow> r (x # xs) (y # ys)"
  assumes z: "\<And>x y. (x, y) \<in> S \<Longrightarrow> corres_underlying R nf nf' (F \<oplus> r') P P' (f x) (f' y)"
  assumes w: "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
             "\<And>x y. (x, y) \<in> S \<Longrightarrow> \<lbrace>P'\<rbrace> f' y \<lbrace>\<lambda>rv. P'\<rbrace>"
  shows      "\<lbrakk> length xs = length ys; set (zip xs ys) \<subseteq> S \<rbrakk> \<Longrightarrow>
                   corres_underlying R nf nf' (F \<oplus> r) P P' (mapME f xs) (mapME f' ys)"
proof (induct xs ys rule: list_induct2)
  case Nil
  show ?case
    by (simp add: mapME_def sequenceE_def x returnOk_def)
next
  case (Cons a as b bs)
  from Cons have P: "(a, b) \<in> S"
    by simp
  from Cons have Q: "corres_underlying R nf nf' (F \<oplus> r) P P' (mapME f as) (mapME f' bs)"
    by simp
  show ?case
    apply (simp add: mapME_Cons)
    apply (rule corres_guard_imp)
    apply (unfold bindE_def validE_def)
      apply (rule corres_underlying_split [OF z [OF P]])
        prefer 3
        apply clarify
       apply (simp add: lift_def)
      apply (case_tac rv)
       apply (clarsimp simp: throwError_def)
       apply clarsimp
        apply (rule corres_split_deprecated[OF _ Q])
          apply (rule corres_trivial)
          apply (case_tac rv)
           apply (clarsimp simp add: lift_def throwError_def)
          apply (clarsimp simp add: y lift_def returnOk_def throwError_def)
         apply (wpsimp wp: w P)+
  done
qed

lemma corres_Id:
  "\<lbrakk> f = g; \<And>rv. r rv rv; nf' \<Longrightarrow> no_fail P' g \<rbrakk> \<Longrightarrow> corres_underlying Id nf nf' r \<top> P' f g"
  apply (clarsimp simp: corres_underlying_def Ball_def no_fail_def)
  apply (rule rev_bexI, assumption)
  apply simp
  done

lemma select_pick_corres_underlying:
  "corres_underlying sr nf nf' r P Q (f x) g
     \<Longrightarrow> corres_underlying sr nf nf' r (P and (\<lambda>s. x \<in> S)) Q (select S >>= f) g"
  by (fastforce simp: corres_underlying_def select_def bind_def)

lemma select_pick_corres:
  "corres_underlying sr nf nf' r P Q (f x) g
     \<Longrightarrow> corres_underlying sr nf nf' r (P and (\<lambda>s. x \<in> S)) Q (select S >>= f) g"
  by (fastforce simp: intro: select_pick_corres_underlying)

lemma select_pick_corresE:
  "corres_underlying sr nf nf' r P Q (f x) g
     \<Longrightarrow> corres_underlying sr nf nf' r (P and (\<lambda>s. x \<in> S)) Q (liftE (select S) >>=E f) g"
  by (fastforce simp: liftE_bindE intro: select_pick_corres)

lemma corres_modify:
  assumes rl:
  "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> (f s, g s') \<in> sr"
  shows "corres_underlying sr nf nf' dc P P' (modify f) (modify g)"
  by (simp add: simpler_modify_def corres_singleton rl)

lemma gets_the_corres:
 "\<lbrakk>no_ofail P a; no_ofail P' b\<rbrakk> \<Longrightarrow>
   corres_underlying sr False True r P P' (gets_the a) (gets_the b)
   = (\<forall> s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<longrightarrow> r (the (a s)) (the (b s')))"
  by (fastforce simp: gets_the_def no_ofail_def corres_underlying_def split_def exec_gets
                      assert_opt_def fail_def return_def
               split: option.split)

lemma corres_gets_the:
  assumes x: "corres_underlying sr nf nf' (r \<circ> the) P P' (gets f) y"
  shows      "corres_underlying sr nf nf' r (P and (\<lambda>s. f s \<noteq> None)) P' (gets_the f) y"
proof -
  have z: "corres_underlying sr nf nf' (\<lambda>x y. \<exists>x'. x = Some x' \<and> r x' y)
                 (P and (\<lambda>s. f s \<noteq> None)) P' (gets f) y"
    apply (subst corres_cong [OF refl refl refl refl])
     defer
     apply (rule corres_guard_imp[OF x], simp+)
    apply (clarsimp simp: simpler_gets_def)
    done
  show ?thesis
    apply (rule corres_guard_imp)
      apply (unfold gets_the_def)
      apply (subst bind_return[symmetric], rule corres_split_deprecated [OF _ z])
        apply (rule corres_trivial, clarsimp simp: assert_opt_def)
       apply (wp | simp)+
  done
qed

lemma corres_gets_the':
  assumes x: "corres_underlying sr nf nf' (\<lambda>x y. r x (the y)) P P' f (gets g)"
  shows      "corres_underlying sr nf nf' r P (P' and (\<lambda>s. g s \<noteq> None)) f (gets_the g) "
proof -
  have z: "corres_underlying sr nf nf' (\<lambda>x y. \<exists>y'. y = Some y' \<and> r x y')
                 P (P' and (\<lambda>s. g s \<noteq> None)) f (gets g)"
    apply (subst corres_cong [OF refl refl refl refl])
     defer
     apply (rule corres_guard_imp[OF x], simp+)
    apply (clarsimp simp: simpler_gets_def)
    done
  show ?thesis
    apply (rule corres_guard_imp)
      apply (unfold gets_the_def)
      apply (subst bind_return[symmetric], rule corres_split [OF z])
        apply (rule corres_trivial, clarsimp simp: assert_opt_def)
       apply (wp | simp)+
  done
qed

lemma corres_u_nofail:
  "corres_underlying S nf True r P P' f g \<Longrightarrow> (nf \<Longrightarrow> no_fail P f) \<Longrightarrow>
  no_fail (\<lambda>s'. \<exists>s. (s,s') \<in> S \<and> P s \<and> P' s') g"
  apply (clarsimp simp add: corres_underlying_def no_fail_def)
  apply fastforce
  done

lemma wp_from_corres_u:
  "\<lbrakk> corres_underlying R nf nf' r G G' f f'; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f' \<lbrace>Q'\<rbrace>; nf \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s'. \<exists>s. (s,s') \<in> R \<and> P s \<and> G s \<and> P' s' \<and> G' s'\<rbrace> f' \<lbrace>\<lambda>rv' s'. \<exists>rv s. (s,s') \<in> R \<and> r rv rv' \<and> Q rv s \<and> Q' rv' s'\<rbrace>"
  apply (fastforce simp: corres_underlying_def valid_def no_fail_def)
  done

lemma wp_from_corres_u_unit:
  "\<lbrakk> corres_underlying R nf nf' r G G' f f'; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>; \<lbrace>P'\<rbrace> f' \<lbrace>\<lambda>_. Q'\<rbrace>; nf \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s'. \<exists>s. (s,s') \<in> R \<and> P s \<and> G s \<and> P' s' \<and> G' s'\<rbrace>
  f' \<lbrace>\<lambda>_ s'. \<exists>s. (s,s') \<in> R \<and> Q s \<and> Q' s'\<rbrace>"
  apply (fastforce dest: wp_from_corres_u elim: hoare_strengthen_post)
  done

lemma corres_nofail:
  "corres_underlying state_relation nf True r P P' f g \<Longrightarrow> (nf \<Longrightarrow> no_fail P f) \<Longrightarrow>
  no_fail (\<lambda>s'. \<exists>s. (s,s') \<in> state_relation \<and> P s \<and> P' s') g"
  by (rule corres_u_nofail)

lemma wp_from_corres_unit:
  "\<lbrakk> corres_underlying state_relation nf nf' r G G' f f';
     \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>; \<lbrace>P'\<rbrace> f' \<lbrace>\<lambda>_. Q'\<rbrace>; nf \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s'. \<exists>s. (s,s') \<in> state_relation \<and> P s \<and> G s \<and> P' s' \<and> G' s'\<rbrace>
  f' \<lbrace>\<lambda>_ s'. \<exists>s. (s,s') \<in> state_relation \<and> Q s \<and> Q' s'\<rbrace>"
  by (auto intro!: wp_from_corres_u_unit)

lemma corres_whileLoop_results:
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P s; P' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
           "\<And>r r'. rrel r r'
                    \<Longrightarrow> corres_underlying srel False nf' rrel (P and A and C r) (P' and A' and C' r') (B r) (B' r')"
  assumes body_inv: "\<And>r. \<lbrace>P and A and C r\<rbrace> B r \<lbrace>\<lambda>_. P\<rbrace>" "\<And>r'. \<lbrace>P' and A' and C' r'\<rbrace> B' r' \<lbrace>\<lambda>_. P'\<rbrace>"
  assumes cross: "\<And>s s'. \<lbrakk>(s, s') \<in> srel; P s; P' s'\<rbrakk> \<Longrightarrow> A s \<and> A' s'"
  shows "(rv', t') \<in> fst (whileLoop C' B' r' s')
         \<Longrightarrow> \<forall>s r. (s,s') \<in> srel \<and> rrel r r' \<and> P s \<and> P' s'
                   \<longrightarrow> (\<exists>rv t. (rv, t) \<in> fst (whileLoop C B r s) \<and> (t,t') \<in> srel \<and> rrel rv rv')"
  apply (rule_tac r=r' and B=B' and C=C' in in_whileLoop_induct)
    apply simp
   apply clarsimp
   apply (rename_tac r_conc s_conc s_abs r_abs)
   apply (prop_tac "\<not> C r_abs s_abs")
    apply (fastforce simp: cond)
   apply (force simp: whileLoop_def)
  apply (thin_tac "_ \<in> fst _")
  apply (rename_tac r s' r' t' r'' u')
  apply clarsimp
  apply (prop_tac "A s \<and> A' s'")
   apply (fastforce dest: cross)
  apply (rename_tac s r_abs)
  apply (insert body_corres)
  apply (drule_tac x=r_abs in meta_spec)
  apply (drule_tac x=r in meta_spec)
  apply clarsimp
  apply (prop_tac "C r_abs s")
   apply (fastforce dest: cond)
  apply (prop_tac "\<exists>rv t. (rv,t) \<in> fst (B r_abs s) \<and> rrel rv r' \<and> (t,t') \<in> srel")
   apply (fastforce simp: corres_underlying_def)
  apply clarsimp
  apply (rename_tac rv t)
  apply (clarsimp simp: pred_conj_def)
  apply (prop_tac "P t \<and> P' t'")
   apply (metis body_inv pred_andI use_valid)
  apply (drule_tac x=t and y=rv in spec2)
  apply clarsimp
  apply (rename_tac rv' t'')
  apply (rule_tac x=rv' in exI)
  apply (rule_tac x=t'' in exI)
  apply (simp add: cond whileLoop_def whileLoop_results.intros)
  done

lemmas corres_whileLoop_results_inv = corres_whileLoop_results[where A=\<top> and A'=\<top>, simplified]

lemma whileLoop_no_fail:
  assumes body_guard: "\<And>r'. \<lbrace>P' and C' r'\<rbrace> B' r' \<lbrace>\<lambda>_. P'\<rbrace>"
  assumes nf': "\<And>r'. no_fail (P' and C' r') (B' r')"
  assumes termin: "\<And>r' s'. P' s' \<Longrightarrow> C' r' s' \<Longrightarrow> whileLoop_terminates C' B' r' s'"
  shows "no_fail P' (whileLoop C' B' r')"
  apply (simp add: no_fail_def)
  apply (intro allI impI)
  apply (rule_tac I="\<lambda>_ s. P' s"
              and R="{((r', s'), r, s). C' r s \<and> (r', s') \<in> fst (B' r s)
                                        \<and> whileLoop_terminates C' B' r s}"
               in not_snd_whileLoop)
    apply simp
   apply (clarsimp simp: validNF_def)
   apply (intro conjI)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
      apply (insert assms)
      apply (fastforce simp: valid_def)
     apply (clarsimp simp: valid_def)
    apply wpsimp
   apply (fastforce intro: no_fail_pre)
  apply (fastforce intro: wf_subset[OF whileLoop_terminates_wf[where C=C' and B=B']])
  done

(* note: I think that the relationship between I' and P' and A' could potentially be weakened *)
(* note: A and A' can be as strong as you like so long as the cross assumption holds. *)
lemma corres_whileLoop:
  assumes cond:
          "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; (P and A) s; (P' and A') s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
          "\<And>r r'. rrel r r'
                  \<Longrightarrow> corres_underlying srel False nf' rrel (P and A and C r) (P' and A' and C' r') (B r) (B' r')"
  assumes body_guard: "\<And>r. \<lbrace>P and A and C r\<rbrace> B r \<lbrace>\<lambda>_. P\<rbrace>" "\<And>r'. \<lbrace>P' and A' and C' r'\<rbrace> B' r' \<lbrace>\<lambda>_. P'\<rbrace>"
  assumes rel: "rrel r r'"
  assumes nf': "\<And>r'. no_fail (I' and C' r') (B' r')"
  assumes termin: "\<And>r' s'. \<lbrakk>nf'; I' s'; C' r' s'\<rbrakk> \<Longrightarrow> whileLoop_terminates C' B' r' s'"
  assumes body_guard3: "\<And>r'. \<lbrace>I' and C' r'\<rbrace> B' r' \<lbrace>\<lambda>_. I'\<rbrace>"
  assumes cross: "\<And>s s'. \<lbrakk>(s, s') \<in> srel; P s; P' s'\<rbrakk> \<Longrightarrow> A s \<and> A' s'"
  assumes weaken: "\<And>s'. (P' and A') s' \<Longrightarrow> I' s'"
  shows "corres_underlying srel False nf' rrel P P' (whileLoop C B r) (whileLoop C' B' r')"
  apply (rule corres_cross_add_guard[where Q=A'])
   apply (fastforce dest: cross)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply (rule whileLoop_no_fail)
      apply (rule body_guard3)
     apply (rule nf')
    apply (erule (2) termin)
   apply (simp add: weaken)
  apply clarsimp
  apply (frule_tac C=C and C'=C' and A="A" and A'="A'" and B=B and rrel=rrel and srel=srel and
                   P=P and P'=P'
         in corres_whileLoop_results[rotated 5])
       apply (erule (1) cond)
        apply (fastforce dest: cross)
       apply (fastforce dest: cross)
      apply (erule body_corres)
     apply (rule body_guard(1))
    apply (rule body_guard(2))
   apply (fastforce dest: cross)
  apply (drule_tac x=a and y=r in spec2, clarsimp simp: rel)
  apply (fastforce simp: rel)
  done

lemma corres_whileLoop_inv:
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P s; P' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
           "\<And>r r'. rrel r r'
                    \<Longrightarrow> corres_underlying srel False nf' rrel (P and C r) (P' and C' r') (B r) (B' r')"
  assumes body_guard: "\<And>r. \<lbrace>P and C r\<rbrace> B r \<lbrace>\<lambda>_. P\<rbrace>" "\<And>r'. \<lbrace>P' and C' r'\<rbrace> B' r' \<lbrace>\<lambda>_. P'\<rbrace>"
  assumes rel: "rrel r r'"
  assumes nf': "\<And>r'. no_fail (P' and C' r') (B' r')"
  assumes termin: "\<And>r' s'. P' s' \<Longrightarrow> whileLoop_terminates C' B' r' s'"
  shows "corres_underlying srel False nf' rrel P P' (whileLoop C B r) (whileLoop C' B' r')"
  apply (rule corres_whileLoop[where A=\<top> and A'=\<top> and I'=P'])
  using assms by simp+

end
