(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
      apply (rule corres_split[OF _ z [OF P] w [OF P]])
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
        apply (rule corres_split[OF _ Q])
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
      apply (subst bind_return[symmetric], rule corres_split [OF _ z])
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

end
