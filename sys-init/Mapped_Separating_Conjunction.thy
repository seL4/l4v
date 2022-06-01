(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Utility lemmas related to the mapping of separating conjunctions over sets and lists *)

theory Mapped_Separating_Conjunction
imports
  Sep_Algebra.Extended_Separation_Algebra
  "HOL-Library.Multiset"
begin

lemmas sep_map_set_conj_set_cong = arg_cong[where f="sep_map_set_conj P" for P]

lemma sep_map_set_conj_set_elim:
  "sep_map_set_conj P xs s \<Longrightarrow> \<lbrakk> \<And>x s. x \<in> xs \<Longrightarrow> P x s = Q x s\<rbrakk> \<Longrightarrow>  sep_map_set_conj Q xs s"
  apply (induct xs arbitrary: s rule: infinite_finite_induct)
    apply fastforce
   apply fastforce
  apply clarsimp
  apply (erule sep_conj_impl; blast)
  done

lemma split_filter_set: "xs = {x \<in> xs. P x} \<union> {x \<in> xs. \<not>P x}"
  by blast

lemma set_minus_not_filter[simp]: "{x \<in> xs. P x} - {x \<in> xs. \<not>P x} = {x \<in> xs. P x}"
  by blast

lemma set_minus_not_filter'[simp]: "{x \<in> xs. \<not>P x} - {x \<in> xs. P x} = {x \<in> xs. \<not>P x}"
  by blast

lemma set_inter_not_filter[simp]: "{x \<in> xs. P x} \<inter> {x \<in> xs. \<not>P x} = {}"
  by blast

declare sep_list_conj_map_add[simp]

lemma sep_map_list_conj_decomp[simp]:
  "sep_map_list_conj (\<lambda>(x, y). P x y \<and>* Q x y) xs =
     (sep_map_list_conj (\<lambda>(x, y). P x y) xs \<and>* sep_map_list_conj (\<lambda>(x , y). Q x y) xs)"
  apply (intro ext iffI)
   apply (induct xs; clarsimp)
   apply sep_cancel+
   apply fastforce
  apply (induct xs; clarsimp)
  apply sep_cancel+
  apply fastforce
  done

lemma image_insertD: "insert (P x) (P ` S) = Q ` S' \<Longrightarrow> \<exists>s\<in>S'. Q s = P x "
  by (metis imageE insertI1)

lemma sep_map_set_inj_eqI:
  "inj_on P xs \<Longrightarrow> inj_on Q ys \<Longrightarrow> P ` xs = Q ` ys \<Longrightarrow>
   sep_map_set_conj P xs = sep_map_set_conj Q ys"
  apply (induct xs arbitrary: ys rule: infinite_finite_induct)
    apply clarsimp
    defer
    apply clarsimp+
   apply (frule image_insertD)
   apply clarsimp
   apply atomize
   apply (erule_tac x="ys - {s}" in allE)
   apply (drule mp)
    apply (simp add: inj_on_diff)
   apply (drule mp)
    apply (metis (no_types, opaque_lifting) image_insert inj_on_insert insert_Diff_single
                                       insert_absorb insert_ident)
   apply clarsimp
   apply (subgoal_tac "finite ys")
    apply (simp add: sep.prod.remove)
   apply (metis finite.insertI finite_image_iff)
  apply (subgoal_tac "infinite ys", clarsimp)
  using finite_image_iff by fastforce

lemma add_mset_eq_mem:
  "add_mset (P x) (image_mset P (mset_set F)) = image_mset Q (mset_set S')
   \<Longrightarrow> \<exists>y. Q y = P x \<and> y \<in> S'"
  apply (drule union_single_eq_member)
  apply clarsimp
  by (metis elem_mset_set empty_iff infinite_set_mset_mset_set)

lemma sep_map_set_conj_mset_eq:
  "\<lbrakk>image_mset P (mset_set S) = image_mset Q (mset_set S');
    finite S; finite S'\<rbrakk>
   \<Longrightarrow> sep_map_set_conj P S = sep_map_set_conj Q S'"
  apply (induction S arbitrary: S' rule: infinite_finite_induct; clarsimp)
   apply (simp add: mset_set_empty_iff)
  apply (subgoal_tac "\<exists>y. y \<in> S' \<and> Q y = P x")
   apply (clarsimp simp: sep.prod.remove mset_set.remove)
  by (fastforce dest: union_single_eq_member)

lemma sep_map_set_conj_multisetE:
  "\<lbrakk>sep_map_set_conj P S s; finite S; finite S';
    image_mset P (mset_set S) = image_mset Q (mset_set S')\<rbrakk>
   \<Longrightarrow> sep_map_set_conj Q S' s"
  by (subst sep_map_set_conj_mset_eq; fastforce)

lemma not_in_image_vimage: "x \<notin> P ` S \<Longrightarrow> P -` {x} \<inter> S = {}"
  by blast

lemma bij_image_mset_eq:
  "\<lbrakk>finite S; finite S'; P ` S = Q ` S';
    (\<And>x. x \<in> P ` S \<Longrightarrow> \<exists>f. bij_betw f (P -` {x} \<inter> S) (Q -` {x} \<inter> S'))\<rbrakk>
   \<Longrightarrow> image_mset P (mset_set S) = image_mset Q (mset_set S')"
  apply (rule multiset_eqI)
  apply (clarsimp simp: count_image_mset)
  apply (case_tac "x \<in> Q ` S'"; clarsimp simp: bij_betw_iff_card not_in_image_vimage )
  done

lemma sep_map_set_elim:
  "\<lbrakk>sep_map_set_conj P xs s;
    xs = ys;
    (\<And>x s. x \<in> xs \<Longrightarrow> P x s \<Longrightarrow> Q x s)\<rbrakk>
   \<Longrightarrow> sep_map_set_conj Q ys s"
  apply clarsimp
  apply (case_tac "finite xs")
   apply clarsimp
   apply (erule sep_map_set_conj_impl)
    apply atomize
    apply (erule_tac x=x in allE)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

lemma sep_map_set_conj_Union:
  "\<lbrakk>\<forall>s \<in> S. finite s;
    \<forall>s s'. s \<in> S \<and> s' \<in> S \<longrightarrow> s \<noteq> s' \<longrightarrow> s \<inter> s' = {}\<rbrakk>
   \<Longrightarrow> sep_map_set_conj (sep_map_set_conj P) S = sep_map_set_conj P (\<Union> S) "
  apply (induct S rule: infinite_finite_induct; clarsimp)
   apply (metis (no_types) finite_UnionD sep.prod.infinite)
  apply (subst sep.prod.union_disjoint; clarsimp?)
  by blast

lemma sep_map_set_quotient_split:
  "\<lbrakk>finite xs; equiv xs R\<rbrakk>
   \<Longrightarrow> sep_map_set_conj P xs = sep_map_set_conj (sep_map_set_conj P ) (xs//R) "
  apply (subst sep_map_set_conj_Union; clarsimp)
    apply (meson in_quotient_imp_subset infinite_super)
   apply (fastforce dest: quotient_disj)
  by (simp add: Union_quotient)

lemma sep_map_set_conj_congE:
  "\<lbrakk>sep_map_set_conj (sep_map_set_conj P) xs s;
    finite xs;
    finite ys;
    xs - {{}} = ys - {{}}\<rbrakk>
   \<Longrightarrow> sep_map_set_conj (sep_map_set_conj P) ys s"
  apply clarsimp
  apply (induct xs arbitrary:ys s rule: infinite_finite_induct)
    apply clarsimp+
   apply (subgoal_tac "ys = {{}} \<or> ys = {}")
    apply (erule disjE; clarsimp)
   apply blast
  apply clarsimp
  apply (case_tac "x = {}")
   apply (metis Diff_idemp Diff_insert_absorb Sep_Tactic_Helpers.sep_conj_empty sep.prod.empty)
  apply (subgoal_tac "x \<in> ys")
   apply (clarsimp simp: sep.prod.remove)
   apply sep_cancel
   apply (metis Diff_insert Diff_insert2 Diff_insert_absorb finite_Diff)
  apply blast
  done

lemma sep_map_set_conj_cong_empty_eq:
  "\<lbrakk>finite xs;
    finite ys;
    xs - {{}} = ys - {{}}\<rbrakk>
   \<Longrightarrow> sep_map_set_conj (sep_map_set_conj P) xs = sep_map_set_conj (sep_map_set_conj P) ys "
  apply clarsimp
  apply (intro ext iffI; erule sep_map_set_conj_congE)
  by blast+

lemma sep_map_set_conj_match:
  "sep_map_set_conj P S s \<Longrightarrow> (\<And>x s. x \<in> S \<Longrightarrow> P x s \<Longrightarrow> Q x s) \<Longrightarrow> sep_map_set_conj Q S s"
  apply (induct rule: infinite_finite_induct; clarsimp)
  apply (erule sep_conj_impl)
   apply blast
  by (metis sep_map_set_elim)

lemma sep_map_set_squash:
  "\<lbrakk>\<forall>x y. x \<in> S \<longrightarrow> y \<in> S \<longrightarrow> x \<noteq> y \<longrightarrow> f x = f y \<longrightarrow> f x = {}; finite S\<rbrakk>
   \<Longrightarrow> sep_map_set_conj (\<lambda>v. sep_map_set_conj P (f v)) S =
      sep_map_set_conj (sep_map_set_conj P) (f ` S)"
  apply (induction S rule: infinite_finite_induct; clarsimp)
  apply (case_tac "f x \<in> f ` F"; clarsimp)
  apply (subgoal_tac "f x = {}")
   apply clarsimp
  apply blast
  done

lemma sep_map_set_conj_subst:
  "(\<And>x. x \<in> S \<Longrightarrow> Q x = Q' x) \<Longrightarrow> sep_map_set_conj Q S = sep_map_set_conj Q' S"
  by clarsimp

lemma sep_map_zip_fst:
  "(\<And>* map (\<lambda>(a,b). f a) (zip xs ys)) s =
   (\<And>* map (\<lambda>a. f (fst a)) (zip xs ys)) s"
  by (simp add: case_prod_unfold)

lemma sep_map_zip_snd:
  "(\<And>* map (\<lambda>(a, b). f b) (zip xs ys)) s =
   (\<And>* map (\<lambda>a. f (snd a)) (zip xs ys)) s"
  by (simp add: case_prod_unfold)

declare sep_map_zip_fst[THEN iffD1, sep_cancel] sep_map_zip_fst[THEN iffD2, sep_cancel]
        sep_map_zip_snd[THEN iffD1, sep_cancel] sep_map_zip_snd[THEN iffD2, sep_cancel]

lemma precise_non_dup: "precise P \<Longrightarrow> \<not>P 0  \<Longrightarrow> \<not> (P \<and>* P) (s :: ('a :: cancellative_sep_algebra))"
  apply (rule ccontr, simp)
  apply (clarsimp simp: sep_conj_def)
  apply (clarsimp simp: precise_def)
  apply (erule_tac x="x+y" in allE)
  apply (erule_tac x=x in allE)
  apply (erule_tac x=y in allE)
  apply (clarsimp)
  apply (drule mp)
  using sep_disj_commuteI sep_substate_disj_add sep_substate_disj_add' apply blast
  apply (clarsimp)
  by (metis disjoint_zero_sym sep_add_cancel sep_add_zero_sym sep_disj_positive)

lemma duplicate_inj: "finite S \<Longrightarrow> sep_map_set_conj f S s \<Longrightarrow> (\<And>s. \<forall>x\<in>(f ` S). \<not>(x \<and>* x) s) \<Longrightarrow> inj_on f S"
 apply (clarsimp simp: inj_on_def)
 apply (erule contrapos_pp[where Q="f _ = f _"])
 apply (clarsimp simp: sep.prod.remove)
 apply (subst (asm) sep.prod.remove[where x=y])
 apply (clarsimp)+
 by (metis sep_conj_assoc sep_conj_false_left sep_globalise)

lemma inj_on_sep_set_conj: "inj_on f S \<Longrightarrow> sep_map_set_conj f S = sep_set_conj (f ` S)"
  by (simp add: sep.prod.reindex_cong sep_set_conj_def)

lemma image_remove: "(f ` (S - {x. f x = \<box>})) = (f ` S - {\<box>})"
 apply (intro set_eqI iffI; clarsimp )
done

lemma sep_prod_setdiff_sep_empty: "finite S \<Longrightarrow> sep.Prod (f ` (S - {x. f x = \<box>})) s \<Longrightarrow> sep.Prod (f ` S) s"
 apply (subst sep.prod.setdiff_irrelevant[symmetric]; clarsimp simp: image_remove)
done

lemma "sep_map_set_conj f S s \<Longrightarrow> finite S \<Longrightarrow> (\<forall>P\<in>(f ` S) - {\<box>}. precise P) \<Longrightarrow> sep_set_conj (f ` S) s"
  apply (subst (asm)  sep.prod.setdiff_irrelevant[symmetric])
   apply (clarsimp)
  apply (frule duplicate_inj[rotated])
    apply (clarsimp)
    apply (erule_tac x="f x" in ballE)
     apply (frule precise_non_dup)
      apply (clarsimp simp: sep_empty_def)
  apply (metis (mono_tags, opaque_lifting) disjoint_zero_sym precise_def sep_add_zero
                                      sep_disj_zero sep_substate_disj_add')
     apply (fastforce)
    apply (blast)
   apply (blast)
  apply (clarsimp simp: inj_on_sep_set_conj)
  apply (clarsimp simp: sep_set_conj_def)
  apply (erule (1) sep_prod_setdiff_sep_empty)
done

end
