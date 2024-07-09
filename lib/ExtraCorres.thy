(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ExtraCorres
imports Corres_UL DetWPLib
begin

(* FIXME: the S in this rule is mainly to make the induction work, we don't actually need it in
   application. This means, this form should be hidden and the main form should be resolving the
   last assumption with order_refl. *)

(* The lemma looks weaker than in it could be -- the guards P and P' are not allowed to depend on
   list elements. This is fine, because P/P' are a loop invariants that need to be supplied
   manually anyway, and we want these to be true for all loop iterations. An instance such as
   "\<lambda>s. \<forall>x \<in> set xs. P x s" is possible and covers the cases the (not really) stronger formulation
   would cover. *)
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
      apply (rule corres_split[OF z[OF P] _ w[OF P]])
      apply (rule corres_underlying_split[OF Q])
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
    apply (rule corres_underlying_split [OF corr' _ ha [OF Cons(2)] hc [OF Cons(2)]])
    apply (rule corres_underlying_split [OF Cons(3) _ hoare_TrueI hoare_TrueI])
    apply (simp add: rc)
    apply (rule Cons.hyps)+
    done
qed

(* FIXME: see comment for mapM rule. Same applies for lemma strength *)
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
       apply (rule corres_mapM [OF _ _ x y z w])
           apply (simp | wp)+
  done

lemmas corres_mapM_x' = corres_mapM_x[OF _ _ _ _ order_refl]

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
    apply (rule corres_split[OF corres_mapM_scheme[OF _ x, where S=S]])
                 apply (rule corres_return_trivial)
                apply (wpsimp wp: y y' simp: z w v)+
  done

(* FIXME: see comment for mapM rule. Same applies for lemma strength *)
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
      apply (rule corres_underlying_split[OF z[OF P]])
        apply (case_tac rv)
         apply (clarsimp simp: throwError_def)
        apply clarsimp
        apply (rule corres_split[OF Q])
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
      apply (subst bind_return[symmetric], rule corres_split [OF z])
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

text \<open>Some results concerning the interaction of abstract and concrete states\<close>

definition ex_abs_underlying :: "('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool" where
  "ex_abs_underlying sr P s' \<equiv> \<exists>s. (s,s') \<in> sr \<and> P s"

lemma ex_absI[intro!]:
  "(s, s') \<in> sr \<Longrightarrow> P s \<Longrightarrow> ex_abs_underlying sr P s'"
  by (auto simp add: ex_abs_underlying_def)

lemma corres_u_nofail:
  "\<lbrakk>corres_underlying S nf True r P P' f g; nf \<Longrightarrow> no_fail P f\<rbrakk>
   \<Longrightarrow> no_fail (P' and ex_abs_underlying S P) g"
  by (fastforce simp: corres_underlying_def ex_abs_underlying_def no_fail_def)

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
  by (fastforce intro: no_fail_pre corres_u_nofail simp: ex_abs_underlying_def)

lemma wp_from_corres_unit:
  "\<lbrakk> corres_underlying state_relation nf nf' r G G' f f';
     \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>; \<lbrace>P'\<rbrace> f' \<lbrace>\<lambda>_. Q'\<rbrace>; nf \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s'. \<exists>s. (s,s') \<in> state_relation \<and> P s \<and> G s \<and> P' s' \<and> G' s'\<rbrace>
  f' \<lbrace>\<lambda>_ s'. \<exists>s. (s,s') \<in> state_relation \<and> Q s \<and> Q' s'\<rbrace>"
  by (auto intro!: wp_from_corres_u_unit)

lemma corres_underlying_split_ex_abs:
  assumes ac: "corres_underlying srel nf nf' r' G G' a c"
  assumes bd: "\<forall>rv rv'. r' rv rv' \<longrightarrow>
                        corres_underlying srel nf nf' r (P rv) (P' rv') (b rv) (d rv')"
  assumes valid: "\<lbrace>G\<rbrace> a \<lbrace>P\<rbrace>" "\<lbrace>G' and ex_abs_underlying srel G\<rbrace> c \<lbrace>P'\<rbrace>"
  shows "corres_underlying srel nf nf' r G G' (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using assms
  apply (clarsimp simp: corres_underlying_def bind_def)
  apply (clarsimp simp: Bex_def Ball_def valid_def ex_abs_underlying_def)
  by meson

lemma hoare_from_abs:
  assumes corres: "corres_underlying srel nf nf' rrel G G' f f'"
  assumes cross2: "\<And>s s' r r'. \<lbrakk>(s, s') \<in> srel; rrel r r'; Q r s; S s\<rbrakk> \<Longrightarrow> Q' r' s'"
  assumes abs_valid: "\<lbrace>P and R\<rbrace> f \<lbrace>\<lambda>rv. Q rv and S\<rbrace>"
  assumes cross1: "\<And>s s'. \<lbrakk>(s, s') \<in> srel; P' s'; R' s'\<rbrakk> \<Longrightarrow> P s"
  assumes nf: "nf \<Longrightarrow> no_fail (P and R and G) f"
  shows "\<lbrace>P' and G' and R' and ex_abs_underlying srel (G and R)\<rbrace> f' \<lbrace>Q'\<rbrace>"
  using assms
  apply (clarsimp simp: valid_def ex_abs_underlying_def corres_underlying_def no_fail_def)
  by fast

lemma hoare_from_abs_inv:
  assumes abs_valid: "f \<lbrace>P\<rbrace>"
  assumes cross: "\<And>s s'. (s, s') \<in> srel \<Longrightarrow> P s = P' s'"
  assumes corres: "corres_underlying srel nf nf' rrel G G' f f'"
  assumes nf: "nf \<Longrightarrow> no_fail (P and G) f"
  shows "\<lbrace>P' and G' and ex_abs_underlying srel G\<rbrace> f' \<lbrace>\<lambda>_. P'\<rbrace>"
  using assms
  by (fastforce intro: hoare_from_abs[where R=\<top> and S=\<top> and R'=\<top> and Q="\<lambda>_. P" , simplified])

lemma corres_from_valid:
  assumes nf': "nf' \<Longrightarrow> no_fail (P' and ex_abs_underlying srel P) f'"
  assumes
    "\<And>s. \<lbrace>\<lambda>s'. P s \<and> P' s' \<and> (s, s') \<in> srel\<rbrace>
          f' \<lbrace>\<lambda>rv' t'. \<exists>(rv, t) \<in> fst (f s). (t, t') \<in> srel \<and> rrel rv rv'\<rbrace>"
  shows "corres_underlying srel nf nf' rrel P P' f f'"
  using assms
  by (fastforce simp: corres_underlying_def valid_def no_fail_def)

lemma corres_from_valid_det:
  assumes det: "det_wp P f"
  assumes nf': "nf' \<Longrightarrow> no_fail (P' and ex_abs_underlying srel P) f'"
  assumes valid:
    "\<And>s rv t.
      \<lbrakk>fst (f s) = {(rv, t)}; P s\<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>s'. P' s' \<and> (s, s') \<in> srel\<rbrace> f' \<lbrace>\<lambda>rv' t'. (t, t') \<in> srel \<and> rrel rv rv'\<rbrace>"
  shows "corres_underlying srel nf nf' rrel P P' f f'"
  apply (clarsimp simp: corres_underlying_def)
  apply (intro conjI)
   apply (insert det)
   apply (clarsimp simp: det_wp_def)
   apply (force dest: use_valid[OF _ valid])
  apply (fastforce dest: nf' simp: no_fail_def ex_abs_underlying_def)
  done

lemma corres_noop_ex_abs:
  assumes P: "\<And>s. P s \<Longrightarrow> \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> f \<lbrace>\<lambda>rv s'. (s, s') \<in> sr \<and> r x rv\<rbrace>"
  assumes nf': "nf' \<Longrightarrow> no_fail (P' and ex_abs_underlying sr P) f"
  shows "corres_underlying sr nf nf' r P P' (return x) f"
  apply (simp add: corres_underlying_def return_def)
  apply clarsimp
  apply (frule P)
  apply (insert nf')
  apply (fastforce simp: valid_def no_fail_def ex_abs_underlying_def)
  done

lemma corres_symb_exec_r_conj_ex_abs:
  assumes z: "\<And>rv. corres_underlying sr nf nf' r Q (R' rv) x (y rv)"
  assumes y: "\<lbrace>Q'\<rbrace> m \<lbrace>R'\<rbrace>"
  assumes x: "\<And>s. P s \<Longrightarrow> \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> m \<lbrace>\<lambda>rv s'. (s, s') \<in> sr\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail (P' and ex_abs_underlying sr P) m"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') x (m >>= (\<lambda>rv. y rv))"
proof -
  have P: "corres_underlying sr nf nf' dc P P' (return undefined) m"
    apply (rule corres_noop_ex_abs)
     apply (simp add: x)
    apply (erule nf)
    done
  show ?thesis
    apply (rule corres_guard_imp)
      apply (subst return_bind[symmetric], rule corres_split[OF P])
        apply (rule z)
       apply wp
      apply (rule y)
     apply simp+
    done
qed

lemmas corres_symb_exec_r_conj_ex_abs_forwards =
  corres_symb_exec_r_conj_ex_abs[where P'=P' and Q'=P' for P', simplified]

lemma gets_the_corres_ex_abs':
 "\<lbrakk>no_ofail P a; no_ofail (P' and ex_abs_underlying sr P) b\<rbrakk> \<Longrightarrow>
   corres_underlying sr False True r P P' (gets_the a) (gets_the b)
   = (\<forall>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<longrightarrow> r (the (a s)) (the (b s')))"
  by (fastforce simp: gets_the_def no_ofail_def corres_underlying_def split_def exec_gets
                      assert_opt_def fail_def return_def ex_abs_underlying_def)

lemmas gets_the_corres_ex_abs = gets_the_corres_ex_abs'[THEN iffD2]

lemma gets_the_corres':
 "\<lbrakk>no_ofail P a; no_ofail P' b\<rbrakk> \<Longrightarrow>
   corres_underlying sr False True r P P' (gets_the a) (gets_the b)
   = (\<forall>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<longrightarrow> r (the (a s)) (the (b s')))"
  apply (erule gets_the_corres_ex_abs')
  apply (fastforce intro: no_ofail_pre_imp)
  done

lemmas gets_the_corres = gets_the_corres'[THEN iffD2]

lemma gets_the_corres_relation:
 "\<lbrakk>no_ofail P f; corres_underlying sr False True r P P' (gets_the f) (gets_the f');
   P s; P' s'; (s, s') \<in> sr\<rbrakk>
  \<Longrightarrow> r (the (f s)) (the (f' s'))"
  apply (rule_tac P=P and a=f and b=f' and P'=P'
               in gets_the_corres_ex_abs'[THEN iffD1, rule_format];
         fastforce?)
  apply (rule no_ofail_gets_the_eq[THEN iffD2])
  apply (fastforce intro: corres_u_nofail)
  done


\<comment> \<open>Some @{term corres_underlying} rules for @{term whileLoop}\<close>

lemma in_whileLoop_corres:
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes result: "(rv', t') \<in> fst (whileLoop C' B' r' s')"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "\<forall>s r. (s, s') \<in> srel \<and> rrel r r' \<and> P r s \<and> P' r' s'
                \<longrightarrow> (\<exists>rv t. (rv, t) \<in> fst (whileLoop C B r s) \<and> (t, t') \<in> srel \<and> rrel rv rv')"
  apply (rule in_whileLoop_induct[OF result])
   apply (force simp: cond whileLoop_def)
  apply clarsimp
  apply (frule (1) corres_underlyingD2[OF body_corres];
         (fastforce dest: nf simp: cond no_fail_def)?)
  apply clarsimp
  apply (frule use_valid[OF _ body_inv(1)])
   apply (fastforce dest: cond)
  apply (frule use_valid[OF _ body_inv(2)])
   apply fastforce
  apply (fastforce simp: whileLoop_def intro: whileLoop_results.intros(3) dest: cond)
  done

lemma corres_whileLoop_ret:
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel False nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes rel: "rrel r r'"
  assumes nf': "\<And>r'. no_fail (P' r' and C' r') (B' r')"
  assumes termin: "\<And>r' s'. \<lbrakk>P' r' s'; C' r' s'\<rbrakk> \<Longrightarrow> whileLoop_terminates C' B' r' s'"
  shows "corres_underlying srel False nf' rrel (P r) (P' r') (whileLoop C B r) (whileLoop C' B' r')"
  apply (rule corres_no_failI)
   apply (simp add: no_fail_def)
   apply (intro impI allI)
   apply (erule_tac I="\<lambda>r' s'. P' r' s'"
                    and R="{((r', s'), r, s). C' r s \<and> (r', s') \<in> fst (B' r s)
                                              \<and> whileLoop_terminates C' B' r s}"
                    in not_snd_whileLoop)
    apply (clarsimp simp: validNF_def)
    apply (rule conjI)
     apply (intro hoare_vcg_conj_lift_pre_fix; wpsimp?)
       using body_inv
       apply (fastforce simp: valid_def)
      apply (clarsimp simp: valid_def)
     apply (insert termin)[1]
     apply wpsimp
    apply (fastforce intro: no_fail_pre nf')
   apply (fastforce intro: wf_subset[OF whileLoop_terminates_wf[where C=C']])
  apply clarsimp
  apply (frule in_whileLoop_corres[OF body_corres body_inv]; (fastforce dest: cond)?)
  apply (fastforce intro: assms)
  done

lemmas corres_whileLoop =
  corres_whileLoop_ret[where P="\<lambda>_. P" for P, where P'="\<lambda>_. P'" for P', simplified]

lemma whileLoop_terminates_cross:
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes abs_termination: "\<And>r s. \<lbrakk>P r s; C r s\<rbrakk> \<Longrightarrow> whileLoop_terminates C B r s"
  assumes ex_abs: "ex_abs_underlying srel (P r) s'"
  assumes rrel: "rrel r r'"
  assumes P': "P' r' s'"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "whileLoop_terminates C' B' r' s'"
proof -
  have helper: "\<And>s. P r s \<and> C r s \<Longrightarrow> \<forall>r' s'. rrel r r' \<and> (s, s') \<in> srel \<and> P r s \<and> P' r' s'
                                               \<longrightarrow> whileLoop_terminates C' B' r' s'"
       (is "\<And>s. _ \<Longrightarrow> ?I r s")
    apply (rule_tac P="?I" in whileLoop_terminates.induct)
      apply (fastforce intro: abs_termination)
     apply (fastforce simp: whileLoop_terminates.intros dest: cond)
    apply (subst whileLoop_terminates.simps)
    apply clarsimp
    apply (frule (1) corres_underlyingD2[OF body_corres], (fastforce dest: nf simp: no_fail_def)+)
    apply (fastforce dest: use_valid intro: body_inv)
    done

  show ?thesis
    apply (insert assms helper)
    apply (cases "C' r' s'")
     apply (fastforce simp: ex_abs_underlying_def)
    apply (simp add: whileLoop_terminates.intros(1))
    done
qed

lemma corres_whileLoop_abs_ret:
  assumes cond: "\<And>r r' s s'. \<lbrakk>rrel r r'; (s, s') \<in> srel; P r s; P' r' s'\<rbrakk> \<Longrightarrow> C r s = C' r' s'"
  assumes body_corres:
    "\<And>r r'. rrel r r' \<Longrightarrow>
             corres_underlying srel nf nf' rrel (P r and C r) (P' r' and C' r') (B r) (B' r')"
  assumes rrel: "rrel r r'"
  assumes body_inv:
    "\<And>r. \<lbrace>P r and C r\<rbrace> B r \<lbrace>P\<rbrace>"
    "\<And>r'. \<lbrace>P' r' and C' r'\<rbrace> B' r' \<lbrace>P'\<rbrace>"
  assumes abs_termination: "\<And>r s. \<lbrakk>P r s; C r s\<rbrakk> \<Longrightarrow> whileLoop_terminates C B r s"
  assumes nf: "\<And>r. nf \<Longrightarrow> no_fail (P r and C r) (B r)"
  shows "corres_underlying srel nf nf' rrel (P r) (P' r') (whileLoop C B r) (whileLoop C' B' r')"
  apply (rule corres_underlyingI)
   apply (frule in_whileLoop_corres[OF body_corres body_inv];
          (fastforce intro: body_corres body_inv rrel dest: nf cond))
  apply (rule_tac I="\<lambda>rv' s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv rv' \<and> P rv s \<and> P' rv' s'"
              and R="{((r', s'), r, s). C' r s \<and> (r', s') \<in> fst (B' r s)
                                        \<and> whileLoop_terminates C' B' r s}"
               in not_snd_whileLoop)
    apply (fastforce intro: rrel)
   apply (rename_tac s s' conc_r new_s)
   apply (clarsimp simp: validNF_def)
   apply (rule conjI)
    apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
      apply (rule_tac Q="\<lambda>s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv conc_r
                                     \<and> P rv s \<and> (P' conc_r s' \<and> C' conc_r s') \<and> s' = new_s"
                   in hoare_weaken_pre[rotated])
       apply clarsimp
      apply (rule hoare_ex_pre)
      apply (rename_tac abs_r)
      apply (rule hoare_weaken_pre)
       apply (rule_tac G="rrel abs_r conc_r" in hoare_grab_asm)
       apply (wpsimp wp: wp_from_corres_u[OF body_corres] body_inv)
       apply (fastforce dest: nf)
      apply (fastforce dest: cond)
     apply (fastforce simp: valid_def)
    apply wpsimp
    apply (rule whileLoop_terminates_cross[OF body_corres];
           (fastforce dest: nf cond intro: body_inv abs_termination))
   apply (rule_tac P="\<lambda>s'. \<exists>rv s. (s, s') \<in> srel \<and> rrel rv conc_r
                                  \<and> P rv s \<and> (P' conc_r s' \<and> C' conc_r s') \<and> s' = new_s"
                in no_fail_pre[rotated])
    apply fastforce
   apply (rule no_fail_ex_lift)
   apply (rename_tac abs_r)
   apply (rule no_fail_pre)
    apply (rule_tac G="rrel abs_r conc_r" in no_fail_grab_asm)
    apply (fastforce intro: corres_u_nofail dest: body_corres nf)
   apply (fastforce simp: cond)
  apply (fastforce intro: wf_subset[OF whileLoop_terminates_wf[where C=C']])
  done

lemmas corres_whileLoop_abs =
  corres_whileLoop_abs_ret[where P="\<lambda>_. P" for P, where P'="\<lambda>_. P'" for P', simplified]

text \<open>Some corres_underlying rules for monadic combinators\<close>

lemma ifM_corres:
  assumes   test: "corres_underlying srel nf nf' (=) A A' test test'"
  and          l: "corres_underlying srel nf nf' rrel Q Q' a a'"
  and          r: "corres_underlying srel nf nf' rrel R R' b b'"
  and  abs_valid: "\<lbrace>B\<rbrace> test \<lbrace>\<lambda>c s. c \<longrightarrow> Q s\<rbrace>"
                  "\<lbrace>C\<rbrace> test \<lbrace>\<lambda>c s. \<not> c \<longrightarrow> R s\<rbrace>"
  and conc_valid: "\<lbrace>B'\<rbrace> test' \<lbrace>\<lambda>c s. c \<longrightarrow> Q' s\<rbrace>"
                  "\<lbrace>C'\<rbrace> test' \<lbrace>\<lambda>c s. \<not> c \<longrightarrow> R' s\<rbrace>"
  shows "corres_underlying srel nf nf' rrel (A and B and C) (A' and B' and C')
           (ifM test a b) (ifM test' a' b')"
  unfolding ifM_def
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF test])
      apply (erule corres_if[OF _ l r])
     apply (wpsimp wp: abs_valid conc_valid hoare_vcg_if_lift2)+
  done

lemmas ifM_corres' =
  ifM_corres[where A=A and B=A and C=A for A, simplified,
             where A'=A' and B'=A' and C'=A' for A', simplified]

lemma orM_corres:
  "\<lbrakk>corres_underlying srel nf nf' (=) A A' a a'; corres_underlying srel nf nf' (=) R R' b b';
    \<lbrace>B\<rbrace> a \<lbrace>\<lambda>c s. \<not> c \<longrightarrow> R s\<rbrace>; \<lbrace>B'\<rbrace> a' \<lbrace>\<lambda>c s. \<not> c \<longrightarrow> R' s\<rbrace>\<rbrakk>
   \<Longrightarrow> corres_underlying srel nf nf' (=) (A and B) (A' and B') (orM a b) (orM a' b')"
  unfolding orM_def
  apply (rule corres_guard_imp)
    apply (rule ifM_corres[where Q=\<top> and Q'=\<top>])
        apply (wpsimp | fastforce)+
  done

lemmas orM_corres' =
  orM_corres[where A=A and B=A for A, simplified, where A'=A' and B'=A' for A', simplified]

lemma andM_corres:
  "\<lbrakk>corres_underlying srel nf nf' (=) A A' a a'; corres_underlying srel nf nf' (=) Q Q' b b';
    \<lbrace>B\<rbrace> a \<lbrace>\<lambda>c s. c \<longrightarrow> Q s\<rbrace>; \<lbrace>B'\<rbrace> a' \<lbrace>\<lambda>c s. c \<longrightarrow> Q' s\<rbrace>\<rbrakk>
   \<Longrightarrow> corres_underlying srel nf nf' (=) (A and B) (A' and B') (andM a b) (andM a' b')"
  unfolding andM_def
  apply (rule corres_guard_imp)
    apply (erule (1) ifM_corres[where R=\<top> and R'=\<top>])
        apply (wpsimp | assumption)+
  done

lemma notM_corres:
  "corres_underlying srel nf nf' (=) G G' a a'
   \<Longrightarrow> corres_underlying srel nf nf' (=) G G' (notM a) (notM a')"
  unfolding notM_def
  apply (rule corres_guard_imp)
    apply (erule corres_split)
      apply wpsimp+
  done

lemma ifM_to_top_of_bind:
  "((ifM test true false) >>= z) = ifM test (true >>= z) (false >>= z)"
  by (force simp: ifM_def bind_def split: if_splits)

end
