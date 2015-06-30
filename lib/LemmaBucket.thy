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
  "\<lbrakk> nf \<Longrightarrow> no_fail P' f \<rbrakk> \<Longrightarrow> corres_underlying Id nf op = \<top> P' f f"
  by (auto simp add: corres_underlying_def Id_def no_fail_def)

(* Strengthen *)

lemma strengthen_imp [strg]:
  "A \<longrightarrow> A' \<Longrightarrow> (B \<longrightarrow> A) \<longrightarrow> (B \<longrightarrow> A')" by clarsimp
  
lemma strengthen_hoare [strg]:
  "(\<And>r s. Q r s \<longrightarrow> R r s) \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace> \<longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  apply (rule)
  apply (erule hoare_strengthen_post)
  apply clarsimp
  done

lemma strengthen_validE_R_cong[strg]:
  "\<lbrakk> \<And>rv s. Q rv s \<longrightarrow> R rv s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>,-"
  by (auto intro: hoare_post_imp_R)

lemma strengthen_all[strg]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x)"
  by simp

lemma strengthen_ex[strg]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<exists>x. P x) \<longrightarrow> (\<exists>x. Q x)"
  by fastforce

lemma strengthen_Ball[strg]:
  "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<forall>x \<in> S. P x) \<longrightarrow> (\<forall>x \<in> S. Q x)"
  by simp

lemma hoare_spec_gen_asm:
  "\<lbrakk> F \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P and K F\<rbrace> f \<lbrace>Q\<rbrace>"
  "\<lbrakk> F \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> s \<turnstile> \<lbrace>P and K F\<rbrace> f' \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding spec_valid_def spec_validE_def validE_def
  apply (clarsimp simp only: pred_conj_def conj_assoc[symmetric] 
               intro!: hoare_gen_asm[unfolded pred_conj_def])+
  done

lemma spec_validE_fail:
  "s \<turnstile> \<lbrace>P\<rbrace> fail \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by wp

lemma mresults_fail: "mresults fail = {}"
  by (simp add: mresults_def fail_def)

lemma gets_symb_exec_l:
  "corres_underlying sr nf dc P P' (gets f) (return x)"
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
  "\<lbrakk> a = a'; b = b'; nf \<Longrightarrow> no_fail \<top> (f a b) \<rbrakk>
         \<Longrightarrow> corres_underlying Id nf dc \<top> \<top> (f a b) (f a' b')"
  by (simp add: corres_underlying_def no_fail_def, blast)

lemma corres_underlying_gets_pre_lhs:
  "(\<And>x. corres_underlying S nf r (P x) P' (g x) g') \<Longrightarrow>
  corres_underlying S nf r (\<lambda>s. P (f s) s) P' (gets f >>= (\<lambda>x. g x)) g'"
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

end