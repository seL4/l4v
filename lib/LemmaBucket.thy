(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory LemmaBucket
imports
  HaskellLemmaBucket
  SpecValid_R
  SubMonadLib
begin

lemma corres_underlying_trivial:
  "\<lbrakk> nf' \<Longrightarrow> no_fail P' f \<rbrakk> \<Longrightarrow> corres_underlying Id nf nf' (=) \<top> P' f f"
  by (auto simp add: corres_underlying_def Id_def no_fail_def)

lemma hoare_spec_gen_asm:
  "\<lbrakk> F \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P and K F\<rbrace> f \<lbrace>Q\<rbrace>"
  "\<lbrakk> F \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P and K F\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding spec_valid_def spec_validE_def validE_def
  apply (clarsimp simp only: pred_conj_def conj_assoc[symmetric]
               intro!: hoare_gen_asm[unfolded pred_conj_def])+
  done

lemma spec_validE_fail:
  "s \<turnstile> \<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by wp+

lemma mresults_fail: "mresults fail = {}"
  by (simp add: mresults_def fail_def)

lemma gets_symb_exec_l:
  "corres_underlying sr nf nf' dc P P' (gets f) (return x)"
  by (simp add: corres_underlying_def return_def simpler_gets_def split_def)

lemmas mapM_x_wp_inv = mapM_x_wp[where S=UNIV, simplified]

lemma mapM_wp_inv:
  "(\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule  valid_return_unit)
  apply (fold mapM_x_mapM)
  apply (erule mapM_x_wp_inv)
  done

lemmas mapM_x_wp' = mapM_x_wp [OF _ subset_refl]

lemma corres_underlying_similar:
  "\<lbrakk> a = a'; b = b'; nf' \<Longrightarrow> no_fail \<top> (f a b) \<rbrakk>
         \<Longrightarrow> corres_underlying Id nf nf' dc \<top> \<top> (f a b) (f a' b')"
  by (simp add: corres_underlying_def no_fail_def, blast)

lemma corres_underlying_gets_pre_lhs:
  "(\<And>x. corres_underlying S nf nf' r (P x) P' (g x) g') \<Longrightarrow>
  corres_underlying S nf nf' r (\<lambda>s. P (f s) s) P' (gets f >>= (\<lambda>x. g x)) g'"
  apply (simp add: simpler_gets_def bind_def split_def corres_underlying_def)
  apply force
  done

lemma mapM_x_inv_wp:
  assumes x: "\<And>s. I s \<Longrightarrow> Q s"
  assumes y: "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. I\<rbrace>"
  assumes z: "\<And>s. I s \<Longrightarrow> P s"
  shows      "\<lbrace>I\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (rule hoare_post_imp)
   apply (erule x)
  apply (rule mapM_x_wp)
   apply (rule hoare_pre_imp [OF _ y])
    apply (erule z)
   apply assumption
  apply simp
  done


lemma mapM_x_accumulate_checks':
  assumes P:  "\<And>x. x \<in> set xs' \<Longrightarrow> \<lbrace>\<top>\<rbrace> f x \<lbrace>\<lambda>rv. P x\<rbrace>"
  assumes P': "\<And>x y. \<lbrakk> x \<in> set xs'; y \<in> set xs' \<rbrakk>
                   \<Longrightarrow> \<lbrace>P y\<rbrace> f x \<lbrace>\<lambda>rv. P y\<rbrace>"
  shows       "set xs \<subseteq> set xs' \<Longrightarrow>
               \<lbrace>\<top>\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv s. \<forall>x \<in> set xs. P x s\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
  apply (simp add: mapM_x_Cons)
  apply (rule hoare_pre)
   apply (wp mapM_x_wp'[OF P'])
      apply blast
     apply simp
    apply assumption
   apply simp
   apply (rule P)
   apply simp
  apply simp
  done

lemmas mapM_x_accumulate_checks
    = mapM_x_accumulate_checks'[OF _ _ subset_refl]

(* Other *)

lemma isRight_rel_sum_comb2:
  "\<lbrakk> (f \<oplus> r) v v'; isRight v' \<rbrakk>
       \<Longrightarrow> isRight v \<and> r (theRight v) (theRight v')"
  by (clarsimp simp: isRight_def)

lemma isRight_case_sum: "isRight x \<Longrightarrow> case_sum f g x = g (theRight x)"
  by (clarsimp simp add: isRight_def)

lemma enumerate_append:"enumerate i (xs @ ys) = enumerate i xs @ enumerate (i + length xs) ys"
  apply (induct xs arbitrary:ys i)
   apply clarsimp+
  done

lemma enumerate_bound:"(a, b) \<in> set (enumerate n xs) \<Longrightarrow> a < n + length xs"
  by (metis add.commute in_set_enumerate_eq prod.sel(1))

lemma enumerate_exceed:"(n + length xs, b) \<notin> set (enumerate n xs)"
  by (metis enumerate_bound less_not_refl)

lemma all_pair_unwrap:"(\<forall>a. P (fst a) (snd a)) = (\<forall>a b. P a b)"
  by force

lemma if_fold[simp]:"(if P then Q else if P then R else S) = (if P then Q else S)"
  by presburger

lemma disjoint_subset_both:"\<lbrakk>A' \<subseteq> A; B' \<subseteq> B; A \<inter> B = {}\<rbrakk> \<Longrightarrow> A' \<inter> B' = {}"
  by blast

lemma union_split: "\<lbrakk>A \<inter> C = {}; B \<inter> C = {}\<rbrakk> \<Longrightarrow> (A \<union> B) \<inter> C = {}"
  by (simp add: inf_sup_distrib2)

lemma dom_expand: "dom (\<lambda>x. if P x then Some y else None) = {x. P x}"
  using if_option_Some by fastforce

lemma range_translate: "(range f = range g) = ((\<forall>x. \<exists>y. f x = g y) \<and> (\<forall>x. \<exists>y. f y = g x))"
  by (rule iffI,
       rule conjI,
        clarsimp,
        blast,
       clarsimp,
       metis f_inv_into_f range_eqI,
      clarsimp,
      subst set_eq_subset,
      rule conjI,
       clarsimp,
       rename_tac arg,
       erule_tac x=arg and P="\<lambda>x. (\<exists>y. f x = g y)" in allE,
       clarsimp,
      clarsimp,
      rename_tac arg,
      erule_tac x=arg and P="\<lambda>x. (\<exists>y. f y = g x)" in allE,
      clarsimp,
      metis range_eqI)

lemma ran_expand: "\<exists>x. P x \<Longrightarrow> ran (\<lambda>x. if P x then Some y else None) = {y}"
  by (rule subset_antisym,
       (clarsimp simp:ran_def)+)

lemma map_upd_expand: "f(x \<mapsto> y) = f ++ (\<lambda>z. if z = x then Some y else None)"
  by (rule ext, rename_tac w,
      case_tac "w = x",
       simp,
      simp add:map_add_def)

lemma map_upd_subI: "\<lbrakk>f \<subseteq>\<^sub>m g; f x = None\<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>m g(x \<mapsto> y)"
  by (rule_tac f="\<lambda>i. if i = x then Some y else None" in map_add_le_mapE,
      simp add:map_le_def,
      rule ballI, rename_tac a,
      rule conjI,
       erule_tac x=x in ballE,
        clarsimp,
        erule disjE,
         clarsimp,
        clarsimp simp:map_add_def,
       clarsimp,
       erule disjE,
        clarsimp,
       clarsimp simp:map_add_def,
      clarsimp simp:map_add_def,
      erule_tac x=a in ballE,
       erule disjE,
        (case_tac "g a"; simp_all),
       clarsimp+)

lemma all_ext: "\<forall>x. f x = g x \<Longrightarrow> f = g"
  by presburger

lemma conjI2: "\<lbrakk>B; B \<longrightarrow> A\<rbrakk> \<Longrightarrow> A \<and> B"
  by auto

(* Trivial lemmas for dealing with messy CNode obligations. *)
lemma Least2: "\<lbrakk>\<not>P 0; \<not>P 1; P (2::nat)\<rbrakk> \<Longrightarrow> Least P = 2"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least3: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; P (3::nat)\<rbrakk> \<Longrightarrow> Least P = 3"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least4: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; P (4::nat)\<rbrakk> \<Longrightarrow> Least P = 4"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least5: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; P (5::nat)\<rbrakk> \<Longrightarrow> Least P = 5"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least6: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; P (6::nat)\<rbrakk> \<Longrightarrow> Least P = 6"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least7: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; P (7::nat)\<rbrakk> \<Longrightarrow> Least P = 7"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least8: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; P (8::nat)\<rbrakk> \<Longrightarrow> Least P = 8"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least9: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; P (9::nat)\<rbrakk> \<Longrightarrow> Least P = 9"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least10: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; P (10::nat)\<rbrakk> \<Longrightarrow> Least P
                 = 10"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least11: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; P (11::nat)\<rbrakk> \<Longrightarrow>
                 Least P = 11"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least12: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; P
                 (12::nat)\<rbrakk> \<Longrightarrow> Least P = 12"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least13: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; P
                 (13::nat)\<rbrakk> \<Longrightarrow> Least P = 13"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least14: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; P (14::nat)\<rbrakk> \<Longrightarrow> Least P = 14"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least15: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; P (15::nat)\<rbrakk> \<Longrightarrow> Least P = 15"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least16: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; P (16::nat)\<rbrakk> \<Longrightarrow> Least P = 16"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least17: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; P (17::nat)\<rbrakk> \<Longrightarrow> Least P = 17"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least18: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; P (18::nat)\<rbrakk> \<Longrightarrow> Least P = 18"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least19: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; P (19::nat)\<rbrakk> \<Longrightarrow> Least P = 19"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least20: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; P (20::nat)\<rbrakk> \<Longrightarrow> Least P = 20"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least21: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; P (21::nat)\<rbrakk> \<Longrightarrow> Least P = 21"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least22: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; \<not>P 21; P (22::nat)\<rbrakk> \<Longrightarrow> Least P
                 = 22"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least23: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; \<not>P 21; \<not>P 22; P (23::nat)\<rbrakk> \<Longrightarrow>
                 Least P = 23"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least24: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; \<not>P 21; \<not>P 22; \<not>P 23; P
                 (24::nat)\<rbrakk> \<Longrightarrow> Least P = 24"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least25: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; \<not>P 21; \<not>P 22; \<not>P 23; \<not>P 24; P
                 (25::nat)\<rbrakk> \<Longrightarrow> Least P = 25"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least26: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; \<not>P 21; \<not>P 22; \<not>P 23; \<not>P 24; \<not>P
                 25; P (26::nat)\<rbrakk> \<Longrightarrow> Least P = 26"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least27: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; \<not>P 21; \<not>P 22; \<not>P 23; \<not>P 24; \<not>P
                 25; \<not>P 26; P (27::nat)\<rbrakk> \<Longrightarrow> Least P = 27"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))
lemma Least28: "\<lbrakk>\<not>P 0; \<not>P 1; \<not>P 2; \<not>P 3; \<not>P 4; \<not>P 5; \<not>P 6; \<not>P 7; \<not>P 8; \<not>P 9; \<not>P 10; \<not>P 11; \<not>P 12; \<not>P
                 13; \<not>P 14; \<not>P 15; \<not>P 16; \<not>P 17; \<not>P 18; \<not>P 19; \<not>P 20; \<not>P 21; \<not>P 22; \<not>P 23; \<not>P 24; \<not>P
                 25; \<not>P 26; \<not>P 27; P (28::nat)\<rbrakk> \<Longrightarrow> Least P = 28"
  by (simp add: Least_Suc eval_nat_numeral(2) eval_nat_numeral(3))

lemma map_add_discard: "\<not> cond x \<Longrightarrow> (f ++ (\<lambda>x. if cond x then (g x) else None)) x = f x"
  by (simp add: map_add_def)

lemma dom_split:"\<lbrakk>\<forall>x \<in> S. \<exists>y. f x = Some y; \<forall>x. x \<notin> S \<longrightarrow> f x = None\<rbrakk> \<Longrightarrow> dom f = S"
  by (auto simp:dom_def)

lemma map_set_in: "x \<in> f ` S = (\<exists>y\<in>S. f y = x)"
  by blast

lemma map_length_split:
  "map (length \<circ> (\<lambda>(a, b). P a b # map (f a b) (Q a b))) xs = map (\<lambda>(a, b). 1 + length (Q a b)) xs"
  by clarsimp

lemma sum_suc: "(\<Sum>x \<leftarrow> xs. Suc (f x)) = length xs + (\<Sum>x \<leftarrow> xs. f x)"
  apply (induct xs)
   by clarsimp+

lemma sum_suc_pair: "(\<Sum>(a, b) \<leftarrow> xs. Suc (f a b)) = length xs + (\<Sum>(a, b) \<leftarrow> xs. f a b)"
  apply (induct xs)
   by clarsimp+

lemma fold_add_sum: "fold (+) ((map (\<lambda>(a, b). f a b) xs)::nat list) 0 = (\<Sum>(a, b) \<leftarrow> xs. f a b)"
  apply (subst fold_plus_sum_list_rev)
  apply (subst sum_list_rev)
  by clarsimp

lemma set_of_enumerate:"card (set (enumerate n xs)) = length xs"
  by (metis distinct_card distinct_enumerate length_enumerate)

lemma collapse_fst: "fst ` (\<lambda>x. (f x, g x)) ` s = f ` s"
  by force

lemma collapse_fst2: "fst ` (\<lambda>(x, y). (f x, g y)) ` s = (\<lambda>x. f (fst x)) ` s"
  by force

lemma collapse_fst3: "(\<lambda>x. f (fst x)) ` set (enumerate n xs) = f ` set [n..<n + length xs]"
  by (metis image_image list.set_map map_fst_enumerate)

lemma card_of_dom_bounded:
  fixes f :: "'a \<Rightarrow> 'b option"
  assumes "finite (UNIV::'a set)"
  shows "card (dom f) \<le> CARD('a)"
  by (simp add: assms card_mono)

lemma third_in: "(a, b, c) \<in> S \<Longrightarrow> c \<in> (snd \<circ> snd) ` S"
  by (metis (erased, hide_lams) map_set_in image_comp snd_conv)

lemma third_in2: "(a \<in> (snd \<circ> snd) ` (set (enumerate i xs))) = (a \<in> snd ` (set xs))"
  by (metis map_map map_snd_enumerate set_map)

lemma map_of_enum: "map_of (enumerate n xs) x = Some y \<Longrightarrow> y \<in> set xs"
  apply (clarsimp)
  by (metis enumerate_eq_zip in_set_zipE)

lemma map_of_append:
  "(map_of xs ++ map_of ys) x = (case map_of ys x of None \<Rightarrow> map_of xs x | Some x' \<Rightarrow> Some x')"
  by (simp add: map_add_def)

lemma map_of_append2:
  "(map_of xs ++ map_of ys ++ map_of zs) x =
     (case map_of zs x of None \<Rightarrow> (case map_of ys x of None \<Rightarrow> map_of xs x
                                                     | Some x' \<Rightarrow> Some x')
                        | Some x' \<Rightarrow> Some x')"
  by (simp add: map_add_def)

lemma map_of_in_set_map: "map_of (map (\<lambda>(n, y). (f n, y)) xs) x = Some z \<Longrightarrow> z \<in> snd ` set xs"
  proof -
    assume "map_of (map (\<lambda>(n, y). (f n, y)) xs) x = Some z"
    hence "(x, z) \<in> (\<lambda>(uu, y). (f uu, y)) ` set xs" using map_of_SomeD by fastforce
    thus "z \<in> snd ` set xs" using map_set_in by fastforce
  qed

lemma pair_in_enum: "(a, b) \<in> set (enumerate x ys) \<Longrightarrow> b \<in> set ys"
  by (metis enumerate_eq_zip in_set_zip2)

lemma distinct_inj:
  "inj f \<Longrightarrow> distinct xs = distinct (map f xs)"
  apply (induct xs)
   apply simp
  apply (simp add: inj_image_mem_iff)
  done

lemma distinct_map_via_ran: "distinct (map fst xs) \<Longrightarrow> ran (map_of xs) = set (map snd xs)"
  apply (cut_tac xs="map fst xs" and ys="map snd xs" in ran_map_of_zip[symmetric])
    apply clarsimp+
  by (simp add: ran_distinct)

lemma in_ran_in_set: "x \<in> ran (map_of xs) \<Longrightarrow> x \<in> set (map snd xs)"
  by (metis (mono_tags, hide_lams) map_set_in map_of_SomeD ranE set_map snd_conv)

lemma in_ran_map_app: "x \<in> ran (xs ++ ys ++ zs) \<Longrightarrow> x \<in> ran xs \<or> x \<in> ran ys \<or> x \<in> ran zs"
  proof -
    assume a1: "x \<in> ran (xs ++ ys ++ zs)"
    obtain bb :: "'a \<Rightarrow> ('b \<Rightarrow> 'a option) \<Rightarrow> 'b" where
      "\<forall>x0 x1. (\<exists>v2. x1 v2 = Some x0) = (x1 (bb x0 x1) = Some x0)"
      by moura
    hence f2: "\<forall>f a. (\<not> (\<exists>b. f b = Some a) \<or> f (bb a f) = Some a) \<and> ((\<exists>b. f b = Some a) \<or> (\<forall>b. f b \<noteq> Some a))"
      by blast
    have "\<exists>b. (xs ++ ys ++ zs) b = Some x"
      using a1 by (simp add: ran_def)
    hence f3: "(xs ++ ys ++ zs) (bb x (xs ++ ys ++ zs)) = Some x"
      using f2 by meson
    { assume "ys (bb x (xs ++ ys ++ zs)) \<noteq> None \<or> xs (bb x (xs ++ ys ++ zs)) \<noteq> Some x"
      { assume "ys (bb x (xs ++ ys ++ zs)) \<noteq> Some x \<and> (ys (bb x (xs ++ ys ++ zs)) \<noteq> None \<or> xs (bb x (xs ++ ys ++ zs)) \<noteq> Some x)"
        hence "\<exists>b. zs b = Some x"
          using f3 by auto
        hence ?thesis
          by (simp add: ran_def) }
      hence ?thesis
        using ran_def by fastforce }
    thus ?thesis
      using ran_def by fastforce
  qed

lemma none_some_map: "None \<notin> S \<Longrightarrow> Some x \<in> S = (x \<in> the ` S)"
  apply (rule iffI)
   apply force
  apply (subst in_these_eq[symmetric])
  apply (clarsimp simp:Option.these_def)
  apply (case_tac "\<exists>y. xa = Some y")
   by clarsimp+

lemma none_some_map2: "the ` Set.filter (\<lambda>s. \<not> Option.is_none s) (range f) = ran f"
  apply (rule subset_antisym)
   apply clarsimp
   apply (case_tac "f x", simp_all)
   apply (simp add: ranI)
  apply clarsimp
  apply (subst none_some_map[symmetric])
   apply clarsimp+
  apply (erule ranE)
  by (metis range_eqI)

lemma prop_map_of_prop:"\<lbrakk>\<forall>z \<in> set xs. P (g z); map_of (map (\<lambda>x. (f x, g x)) xs) y = Some a\<rbrakk> \<Longrightarrow> P a"
  using map_of_SomeD by fastforce

lemma range_subsetI2: "\<forall>y\<in>A. \<exists>x. f x = y \<Longrightarrow> A \<subseteq> range f"
 by fast

lemma insert_strip: "x \<noteq> y \<Longrightarrow> (x \<in> insert y S) = (x \<in> S)"
  by simp

lemma dom_map_add: "dom ys = A \<Longrightarrow> dom (xs ++ ys) = A \<union> dom xs"
  by simp

lemma set_compre_unwrap: "({x. P x} \<subseteq> S) = (\<forall>x. P x \<longrightarrow> x \<in> S)"
  by blast

lemma map_add_same: "\<lbrakk>xs = ys; zs = ws\<rbrakk> \<Longrightarrow> xs ++ zs = ys ++ ws"
  by simp

lemma map_add_find_left: "n k = None \<Longrightarrow> (m ++ n) k = m k"
  by (simp add:map_add_def)

lemma map_length_split_triple:
  "map (length \<circ> (\<lambda>(a, b, c). P a b c # map (f a b c) (Q a b c))) xs =
     map (\<lambda>(a, b, c). 1 + length (Q a b c)) xs"
  by fastforce

lemma sum_suc_triple: "(\<Sum>(a, b, c)\<leftarrow>xs. Suc (f a b c)) = length xs + (\<Sum>(a, b, c)\<leftarrow>xs. f a b c)"
  by (induct xs; clarsimp)

lemma sum_enumerate: "(\<Sum>(a, b)\<leftarrow>enumerate n xs. P b) = (\<Sum>b\<leftarrow>xs. P b)"
  by (induct xs arbitrary:n; clarsimp)

lemma dom_map_fold:"dom (fold (++) (map (\<lambda>x. [f x \<mapsto> g x]) xs) ms) = dom ms \<union> set (map f xs)"
  by (induct xs arbitrary:f g ms; clarsimp)

lemma list_ran_prop:"map_of (map (\<lambda>x. (f x, g x)) xs) i = Some t \<Longrightarrow> \<exists>x \<in> set xs. g x = t"
  by (induct xs arbitrary:f g t i; clarsimp split:if_split_asm)

lemma in_set_enumerate_eq2:"(a, b) \<in> set (enumerate n xs) \<Longrightarrow> (b = xs ! (a - n))"
  by (simp add: in_set_enumerate_eq)

lemma subset_eq_notI: "\<lbrakk>a\<in> B;a\<notin> C\<rbrakk> \<Longrightarrow> \<not> B \<subseteq> C"
  by auto

lemma nat_divide_less_eq:
  fixes b :: nat
  shows "0 < c \<Longrightarrow> (b div c < a) = (b < a * c)"
  using td_gal_lt by blast

lemma strengthen_imp_same_first_conj:
  "(b \<and> (a \<longrightarrow> c) \<and> (a' \<longrightarrow> c')) \<Longrightarrow> ((a \<longrightarrow> b \<and> c) \<and> (a' \<longrightarrow> b \<and> c'))"
  by blast

lemma conj_impD:
  "a \<and> b \<Longrightarrow> a \<longrightarrow> b"
  by blast

lemma set_list_mem_nonempty:
  "x \<in> set xs \<Longrightarrow> xs \<noteq> []"
  by auto

lemma strenghten_False_imp:
  "\<not>P \<Longrightarrow> P \<longrightarrow> Q"
  by blast

lemma foldl_fun_or_alt:
  "foldl (\<lambda>x y. x \<or> f y) b ls = foldl (\<or>) b (map f ls)"
  apply (induct ls)
   apply clarsimp
  apply clarsimp
  by (simp add: foldl_map)

lemma sorted_imp_sorted_filter:
  "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (metis filter_sort sorted_sort sorted_sort_id)

lemma sorted_list_of_set_already_sorted:
  "\<lbrakk> distinct xs; sorted xs \<rbrakk> \<Longrightarrow> sorted_list_of_set (set xs) = xs"
  by (simp add: sorted_list_of_set_sort_remdups distinct_remdups_id sorted_sort_id)

end
