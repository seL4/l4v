(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory DistinctPropLemmaBucket
imports
  Lib
  MoreDivides
  Aligned
  HOLLemmaBucket
  DistinctProp
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/Prefix_Order"

begin


lemma n_less_equal_power_2 [simp]:
  "n < 2 ^ n"
  by (induct_tac n, simp_all)

lemma drop_Suc_nth:
  "n < length xs \<Longrightarrow> drop n xs = xs!n # drop (Suc n) xs"
  apply (induct xs arbitrary: n)
   apply simp
  apply simp
  apply (case_tac "n = length xs")
   apply simp
   apply (case_tac xs, simp)
   apply (simp add: nth_append)
  apply (case_tac n, simp)
  apply simp
  done

lemma minus_Suc_0_lt:
  "a \<noteq> 0 \<Longrightarrow> a - Suc 0 < a"
  by simp

lemma map_length_cong:
  "\<lbrakk> length xs = length ys; \<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x = g y \<rbrakk>
     \<Longrightarrow> map f xs = map g ys"
  apply atomize
  apply (erule rev_mp, erule list_induct2)
   apply auto
  done

(* FIXME: duplicate *)
lemma zip_take_triv2:
  "n \<ge> length as \<Longrightarrow> zip as (take n bs) = zip as bs"
  apply (induct as arbitrary: n bs)
   apply simp
  apply simp
  apply (case_tac n, simp_all)
  apply (case_tac bs, simp_all)
  done

lemma zip_is_empty:
  "(zip xs ys = []) = (xs = [] \<or> ys = [])"
  apply (case_tac xs, simp_all)
  apply (case_tac ys, simp_all)
  done

lemma fst_last_zip_upt:
  "zip [0 ..< m] xs \<noteq> [] \<Longrightarrow>
   fst (last (zip [0 ..< m] xs))
    = (if length xs < m then length xs - 1 else m - 1)"
  apply (subst last_conv_nth, assumption)
  apply (simp only: One_nat_def)
  apply (subst nth_zip)
    apply (rule order_less_le_trans[OF minus_Suc_0_lt])
     apply (simp add: zip_is_empty)
    apply simp
   apply (rule order_less_le_trans[OF minus_Suc_0_lt])
    apply (simp add: zip_is_empty)
   apply simp
  apply (simp add: min_def zip_is_empty)
  done

lemma not_prefixI:
  fixes xs :: "'a list"
  shows "\<lbrakk> xs \<noteq> ys; length xs = length ys\<rbrakk> \<Longrightarrow> \<not> xs \<le> ys"
  apply (erule contrapos_nn)
  apply (erule prefixE)
  apply simp
  done


lemma less_1_helper:
  "n \<le> m \<Longrightarrow> (n - 1 :: int) < m"
  by arith

lemma power_sub_int:
  "\<lbrakk> m \<le> n; 0 < b \<rbrakk> \<Longrightarrow> b ^ n div b ^ m = (b ^ (n - m) :: int)"
  apply (subgoal_tac "\<exists>n'. n = m + n'")
   apply (clarsimp simp: power_add)
  apply (rule exI[where x="n - m"])
  apply simp
  done

lemma split_state_strg:
  "(\<exists>x. f s = x \<and> P x s) \<longrightarrow> P (f s) s" by clarsimp

lemma theD:
  "\<lbrakk>the (f x) = y;  x \<in> dom f \<rbrakk> \<Longrightarrow> f x = Some y"
  by (auto simp add: dom_def)

lemma bspec_split:
  "\<lbrakk> \<forall>(a, b) \<in> S. P a b; (a, b) \<in> S \<rbrakk> \<Longrightarrow> P a b"
  by fastforce

lemma set_zip_same:
  "set (zip xs xs) = Id \<inter> (set xs \<times> set xs)"
  apply (induct xs, simp_all)
  apply safe
  done

lemma univ_eq_obvious:
  "\<not> (\<forall>x. y \<noteq> x)"
  by simp

lemma ball_ran_updI:
  "(\<forall>x \<in> ran m. P x) \<Longrightarrow> P v \<Longrightarrow> (\<forall>x \<in> ran (m (y \<mapsto> v)). P x)"
  by (auto simp add: ran_def)

lemma not_psubset_eq:
  "\<lbrakk> \<not> A \<subset> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> A = B"
  by blast

primrec
  opt_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> bool"
where
  "opt_rel f  None    y = (y = None)"
| "opt_rel f (Some x) y = (\<exists>y'. y = Some y' \<and> f x y')"

lemma opt_rel_None_rhs[simp]:
  "opt_rel f x None = (x = None)"
  by (cases x, simp_all)

lemma opt_rel_Some_rhs[simp]:
  "opt_rel f x (Some y) = (\<exists>x'. x = Some x' \<and> f x' y)"
  by (cases x, simp_all)

lemma in_image_op_plus:
  "(x + y \<in> op + x ` S) = ((y :: 'a :: ring) \<in> S)"
  by (simp add: image_def)

lemma insert_subtract_new:
  "x \<notin> S \<Longrightarrow> (insert x S - S) = {x}"
  by auto

lemma replicate_eq:
  "(replicate n x = replicate m y) = (n = m \<and> (n \<noteq> 0 \<longrightarrow> x = y))"
  apply (induct n arbitrary: m)
   apply simp
   apply (case_tac m, simp_all)[1]
  apply (case_tac m, simp_all)
  apply auto
  done

lemma bspec_upd_None:
  "\<lbrakk> \<forall>c\<in>ran (f (x := None)). P c; f y = Some c; y \<noteq> x \<rbrakk>
     \<Longrightarrow> P c"
  apply (erule bspec)
  apply (simp add: fun_upd_def)
  apply (rule ranI)
  apply (subst if_not_P, assumption)
  apply assumption
  done

lemma distinct_prefix:
  "\<lbrakk> distinct xs; ys \<le> xs \<rbrakk> \<Longrightarrow> distinct ys"
  apply (clarsimp simp: less_eq_list_def)
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply simp
  apply clarsimp
  apply (drule set_mono_prefixeq)
  apply fastforce
  done

primrec
  distinct_sets :: "'a set list \<Rightarrow> bool"
where
  "distinct_sets [] = True"
| "distinct_sets (x#xs) = (x \<inter> \<Union>set xs = {} \<and> distinct_sets xs)"

lemma distinct_sets_prop:
  "distinct_sets xs = distinct_prop (\<lambda>x y. x \<inter> y = {}) xs"
  by (induct xs) auto

lemma distinct_take_strg:
  "distinct xs \<longrightarrow> distinct (take n xs)"
  by simp

lemma map_fst_zip_prefix:
  "map fst (zip xs ys) \<le> xs"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply simp
  apply simp
  done


lemma distinct_prop_prefixE:
  "\<lbrakk> distinct_prop P ys; prefixeq xs ys \<rbrakk> \<Longrightarrow> distinct_prop P xs"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply simp
  apply clarsimp
  apply (drule set_mono_prefixeq)
  apply (drule(1) subsetD)
  apply clarsimp
  done

lemma inj_Pair:
  "inj_on (Pair x) S"
  by (rule inj_onI, simp)

lemma inj_on_split:
  "inj_on f S \<Longrightarrow> inj_on (\<lambda>x. (z, f x)) S"
  by (auto simp: inj_on_def)

lemma less_Suc_unat_less_bound:
  "n < Suc (unat (x :: ('a :: len) word)) \<Longrightarrow> n < 2 ^ len_of TYPE('a)"
  apply (erule order_less_le_trans)
  apply (rule Suc_leI)
  apply simp
  done

lemma map_snd_zip_prefix:
  "map snd (zip xs ys) \<le> ys"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply simp
  apply simp
  done



(****************************************
 * Take, drop, zip, list_all etc rules. *
 ****************************************)

lemma nth_upt_0 [simp]:
  "i < length xs \<Longrightarrow> [0..<length xs] ! i = i"
  by simp

lemma take_insert_nth:
  "i < length xs\<Longrightarrow>
  insert (xs ! i) (set (take i xs)) = set (take (Suc i) xs)"
  by (subst take_Suc_conv_app_nth, assumption, fastforce)

lemma zip_take_drop:
  "\<lbrakk>n < length xs; length ys = length xs\<rbrakk> \<Longrightarrow>
    zip xs (take n ys @ a # drop (Suc n) ys) =
    zip (take n xs) (take n ys) @ (xs ! n, a) #  zip (drop (Suc n) xs) (drop (Suc n) ys)"
  by (subst id_take_nth_drop, assumption, simp)

lemma take_nth_distinct:
  "\<lbrakk>distinct xs; n < length xs; xs ! n \<in> set (take n xs)\<rbrakk> \<Longrightarrow> False"
  by (fastforce simp: distinct_conv_nth in_set_conv_nth)

lemma take_drop_append:
  "drop a xs = take b (drop a xs) @ drop (a + b) xs"
  by (metis append_take_drop_id drop_drop add.commute)

lemma drop_take_drop:
  "drop a (take (b + a) xs) @ drop (b + a) xs = drop a xs"
  by (metis add.commute take_drop take_drop_append)

lemma map_fst_zip':
  "length xs \<le> length ys \<Longrightarrow> map fst (zip xs ys) = xs"
  by (metis length_map length_zip map_fst_zip_prefix min_absorb1 not_prefixI)

lemma zip_take_length:
  "zip xs (take (length xs) ys) = zip xs ys"
  by (metis order_refl zip_take_triv2)

lemma zip_singleton:
  "ys \<noteq> [] \<Longrightarrow> zip [a] ys = [(a, ys ! 0)]"
   by (case_tac ys, simp_all)

lemma zip_append_singleton:
  "\<lbrakk>i = length xs; length xs < length ys\<rbrakk>
  \<Longrightarrow> zip (xs @ [a]) ys = (zip xs ys) @ [(a,ys ! i)]"
  apply (induct xs)
   apply (case_tac ys, simp_all)
  apply (case_tac ys, simp_all)
  apply (clarsimp simp: zip_append1 zip_take_length zip_singleton)
  done

lemma ran_map_of_zip:
  "\<lbrakk>length xs = length ys; distinct xs\<rbrakk> \<Longrightarrow> ran (map_of (zip xs ys)) = set ys"
  by (induct rule: list_induct2, simp_all)

lemma map_of_zip_range:
  "\<lbrakk>length xs = length ys; distinct xs\<rbrakk>
  \<Longrightarrow> (\<lambda>x. (the (map_of (zip xs ys) x))) ` set xs = set ys"
  apply (clarsimp simp: image_def)
  apply (subst ran_map_of_zip [symmetric, where xs=xs and ys=ys], simp+)
  apply (clarsimp simp: ran_def)
  apply (rule)
   apply clarsimp
   apply (frule_tac x=xa in map_of_zip_is_Some, clarsimp)
   apply fast
  apply (clarsimp simp: set_zip)
  by (metis domI dom_map_of_zip nth_mem ranE ran_map_of_zip option.sel)

lemma map_zip_fst:
  "length xs = length ys \<Longrightarrow> map (\<lambda>(x, y). f x) (zip xs ys) = map f xs"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys, clarsimp+)
  done

lemma map_zip_fst':
  "length xs \<le> length ys \<Longrightarrow> map (\<lambda>(x, y). f x) (zip xs ys) = map f xs"
  by (metis length_map map_fst_zip' map_zip_fst zip_map_fst_snd)

lemma map_zip_snd:
  "length xs = length ys \<Longrightarrow> map (\<lambda>(x, y). f y) (zip xs ys) = map f ys"
  apply (induct ys arbitrary: xs)
   apply simp
  apply (case_tac xs, clarsimp+)
  done

lemma map_zip_snd':
  "length ys \<le> length xs \<Longrightarrow> map (\<lambda>(x, y). f y) (zip xs ys) = map f ys"
  apply (induct ys arbitrary: xs)
   apply simp
  apply (case_tac xs, clarsimp+)
  done

lemma map_of_zip_tuple_in:
  "\<lbrakk>(x, y) \<in> set (zip xs ys); distinct xs\<rbrakk> \<Longrightarrow> map_of (zip xs ys) x = Some y"
  apply (induct xs arbitrary: ys, simp_all)
  apply (case_tac ys, clarsimp+)
  apply (rule conjI)
   apply (metis in_set_zipE)
  apply clarsimp
  done

lemma in_set_zip1:
  "(x, y) \<in> set (zip xs ys) \<Longrightarrow> x \<in> set xs"
  by (metis in_set_zipE)

lemma in_set_zip2:
  "(x, y) \<in> set (zip xs ys) \<Longrightarrow> y \<in> set ys"
  by (metis in_set_zipE)

lemma map_zip_snd_take:
  "map (\<lambda>(x, y). f y) (zip xs ys) = map f (take (length xs) ys)"
  apply (subst map_zip_snd' [symmetric, where xs=xs and ys="take (length xs) ys"])
   apply simp
  apply (subst zip_take_length [symmetric], simp)
  done

lemma map_of_zip_is_index:
  "\<lbrakk>length xs = length ys; x \<in> set xs\<rbrakk>
  \<Longrightarrow> \<exists>i. (map_of (zip xs ys)) x = Some (ys ! i)"
  apply (induct rule: list_induct2, simp_all)
  apply (rule conjI)
   apply clarsimp
   apply (metis nth_Cons_0)
  apply clarsimp
  apply (metis nth_Cons_Suc)
  done

lemma map_of_zip_take_update:
  "\<lbrakk>i < length xs; length xs \<le> length ys; distinct xs\<rbrakk>
  \<Longrightarrow> map_of (zip (take i xs) ys)(xs ! i \<mapsto> (ys ! i)) =
      map_of (zip (take (Suc i) xs) ys)"
  apply (rule ext)
  apply (case_tac "x=xs ! i", simp_all)
   apply clarsimp
   apply (rule map_of_is_SomeI[symmetric])
    apply (simp add: map_fst_zip')
   apply (simp add: set_zip)
   apply (rule_tac x=i in exI)
   apply clarsimp
  apply (clarsimp simp: take_Suc_conv_app_nth zip_append_singleton map_add_def
                 split: option.splits)
  done

(* A weaker version of map_of_zip_is_Some (from HOL). *)
lemma map_of_zip_is_Some':
  "length xs \<le> length ys \<Longrightarrow> (x \<in> set xs) = (\<exists>y. map_of (zip xs ys) x = Some y)"
  apply (subst zip_take_length[symmetric])
  apply (rule map_of_zip_is_Some)
  by (metis length_take min_absorb2)

lemma map_of_zip_inj:
  "\<lbrakk>distinct xs; distinct ys; length xs = length ys\<rbrakk>
    \<Longrightarrow> inj_on (\<lambda>x. (the (map_of (zip xs ys) x))) (set xs)"
  apply (clarsimp simp: inj_on_def)
  apply (subst (asm) map_of_zip_is_Some, assumption)+
  apply clarsimp
  apply (clarsimp simp: set_zip)
  by (metis nth_eq_iff_index_eq)

lemma map_of_zip_inj':
  "\<lbrakk>distinct xs; distinct ys; length xs \<le> length ys\<rbrakk>
    \<Longrightarrow> inj_on (\<lambda>x. (the (map_of (zip xs ys) x))) (set xs)"
  apply (subst zip_take_length[symmetric])
  apply (erule map_of_zip_inj, simp)
  by (metis length_take min_absorb2)

lemma list_all_nth:
  "\<lbrakk>list_all P xs; i < length xs\<rbrakk> \<Longrightarrow> P (xs ! i)"
  by (metis list_all_length)

lemma list_all_update:
  "\<lbrakk>list_all P xs; i < length xs; \<And>x. P x \<Longrightarrow> P (f x)\<rbrakk>
  \<Longrightarrow> list_all P (xs [i := f (xs ! i)])"
  by (metis length_list_update list_all_length nth_list_update)

lemma list_allI:
  "\<lbrakk>list_all P xs; \<And>x. P x \<Longrightarrow> P' x\<rbrakk> \<Longrightarrow> list_all P' xs"
  by (metis list_all_length)

lemma list_all_imp_filter:
  "list_all (\<lambda>x. f x \<longrightarrow> g x) xs
  = list_all (\<lambda>x. g x) [x\<leftarrow>xs . f x]"
  by (fastforce simp: Ball_set_list_all[symmetric])

lemma list_all_imp_filter2:
  "list_all (\<lambda>x. f x \<longrightarrow> g x) xs
  = list_all (\<lambda>x. \<not>f x) [x\<leftarrow>xs . (\<lambda>x. \<not>g x) x]"
  by (fastforce simp: Ball_set_list_all[symmetric])

lemma list_all_imp_chain:
  "\<lbrakk>list_all (\<lambda>x. f x \<longrightarrow> g x) xs; list_all (\<lambda>x. f' x \<longrightarrow> f x) xs\<rbrakk>
  \<Longrightarrow>
   list_all (\<lambda>x. f' x \<longrightarrow> g x) xs"
  by (clarsimp simp: Ball_set_list_all [symmetric])

(***********************
 * distinct_sets rules *
 ***********************)

lemma distinct_sets_union_sub:
  "\<lbrakk>x \<in> A; distinct_sets [A,B]\<rbrakk> \<Longrightarrow> A \<union> B - {x} = A - {x} \<union> B"
  by (auto simp: distinct_sets_def)

lemma distinct_sets_append:
  "distinct_sets (xs @ ys) \<Longrightarrow> distinct_sets xs \<and> distinct_sets ys"
  apply (subst distinct_sets_prop)+
  apply (subst (asm) distinct_sets_prop)
  apply (subst (asm) distinct_prop_append)
  apply clarsimp
  done

lemma distinct_sets_append1:
  "distinct_sets (xs @ ys) \<Longrightarrow> distinct_sets xs"
  by (drule distinct_sets_append, simp)


lemma distinct_sets_append2:
  "distinct_sets (xs @ ys) \<Longrightarrow> distinct_sets ys"
  by (drule distinct_sets_append, simp)

lemma distinct_sets_append_Cons:
  "distinct_sets (xs @ a # ys) \<Longrightarrow> distinct_sets (xs @ ys)"
  apply (subst distinct_sets_prop)+
  apply (subst (asm) distinct_sets_prop)
  apply (subst distinct_prop_append)
  apply (subst (asm) distinct_prop_append)
  apply clarsimp
  done

lemma distinct_sets_append_Cons_disjoint:
  "distinct_sets (xs @ a # ys) \<Longrightarrow>  a \<inter> \<Union>set xs = {} "
  apply (subst (asm) distinct_sets_prop)
  apply (subst (asm) distinct_prop_append)
  apply (subst Int_commute)
  apply (subst Union_disjoint)
  apply clarsimp
  done

lemma distinct_prop_take:
  "\<lbrakk>distinct_prop P xs; i < length xs\<rbrakk>
 \<Longrightarrow> distinct_prop P (take i xs)"
  by (metis take_is_prefixeq distinct_prop_prefixE)

lemma distinct_sets_take:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk>
 \<Longrightarrow> distinct_sets (take i xs)"
  by (simp add: distinct_sets_prop distinct_prop_take)

lemma distinct_prop_take_Suc:
  "\<lbrakk>distinct_prop P xs; i < length xs\<rbrakk>
 \<Longrightarrow> distinct_prop P (take (Suc i) xs)"
  by (metis distinct_prop_take not_less take_all)

lemma distinct_sets_take_Suc:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk>
 \<Longrightarrow> distinct_sets (take (Suc i) xs)"
  by (simp add: distinct_sets_prop distinct_prop_take_Suc)

lemma distinct_prop_rev:
  "distinct_prop P (rev xs) = distinct_prop (\<lambda>y x. P x y) xs"
  apply (induct xs)
   apply clarsimp
  apply clarsimp
  apply rule
   apply (subst (asm) distinct_prop_append, simp)
  apply (subst distinct_prop_append, simp)
  done

lemma distinct_sets_rev [simp]:
  "distinct_sets (rev xs) = distinct_sets xs"
  apply (unfold distinct_sets_prop)
  apply (subst distinct_prop_rev)
  apply (subst Int_commute)
  apply clarsimp
  done

lemma distinct_sets_drop:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk>
 \<Longrightarrow> distinct_sets (drop i xs)"
  apply (case_tac "i=0", simp)
  apply (subst distinct_sets_rev [symmetric])
  apply (subst rev_drop)
  apply (subst distinct_sets_take, simp_all)
  done

lemma distinct_sets_drop_Suc:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk>
 \<Longrightarrow> distinct_sets (drop (Suc i) xs)"
  apply (subst distinct_sets_rev [symmetric])
  apply (subst rev_drop)
  apply (subst distinct_sets_take, simp_all)
  done

lemma distinct_sets_take_nth:
  "\<lbrakk>distinct_sets xs; i < length xs; x \<in> set (take i xs)\<rbrakk> \<Longrightarrow> x \<inter> xs ! i = {}"
  apply (drule (1) distinct_sets_take_Suc)
  apply (subst (asm) take_Suc_conv_app_nth, assumption)
  apply (unfold distinct_sets_prop)
  apply (subst (asm) distinct_prop_append)
  apply clarsimp
  done

lemma distinct_sets_drop_nth:
  "\<lbrakk>distinct_sets xs; i < length xs; x \<in> set (drop (Suc i) xs)\<rbrakk> \<Longrightarrow> x \<inter> xs ! i = {}"
  apply (drule (1) distinct_sets_drop)
  apply (subst (asm) drop_Suc_nth, assumption)
  apply fastforce
  done

lemma distinct_sets_append_distinct:
  "\<lbrakk>x \<in> set xs; y \<in> set ys; distinct_sets (xs @ ys)\<rbrakk>
  \<Longrightarrow> x \<inter> y = {}"
  apply (unfold distinct_sets_prop)
  apply (clarsimp simp: distinct_prop_append)
  done

lemma distinct_sets_update:
 "\<lbrakk>a \<subseteq> xs ! i; distinct_sets xs; i < length xs\<rbrakk>
  \<Longrightarrow> distinct_sets (xs[i := a])"
  apply (subst distinct_sets_prop)
  apply (subst (asm) distinct_sets_prop)
  apply (subst upd_conv_take_nth_drop)
   apply simp
  apply (subst distinct_prop_append)
  apply (intro conjI)
    apply (erule (1) distinct_prop_take)
   apply (rule conjI|clarsimp)+
    apply (fold distinct_sets_prop)
    apply (drule (1) distinct_sets_drop)
    apply (subst (asm) drop_Suc_nth, assumption)
    apply clarsimp
    apply blast
   apply (drule (1) distinct_sets_drop)
   apply (subst (asm) drop_Suc_nth, assumption)
   apply clarsimp
  apply clarsimp
  apply rule
   apply (drule (2) distinct_sets_take_nth)
   apply blast
  apply clarsimp
  apply (thin_tac "P \<subseteq> Q" for P Q)
  apply (subst (asm) id_take_nth_drop, assumption)
  apply (drule distinct_sets_append_Cons)
  apply (erule (2) distinct_sets_append_distinct)
  done


lemma distinct_sets_map_update:
  "\<lbrakk>distinct_sets (map f xs); i < length xs; f a \<subseteq> f(xs ! i)\<rbrakk>
  \<Longrightarrow> distinct_sets (map f (xs[i := a]))"
  by (metis distinct_sets_update length_map map_update nth_map)

lemma Union_list_update:
  "\<lbrakk>i < length xs; distinct_sets (map f xs)\<rbrakk>
  \<Longrightarrow>
   (\<Union>x\<in>set (xs [i := a]). f x)
 = (\<Union>x\<in>set xs. f x) - f (xs ! i) \<union> f a"
  apply (induct xs arbitrary: i)
   apply clarsimp
  apply clarsimp
  apply (case_tac i)
  apply clarsimp
   apply fastforce
  apply fastforce
  done

lemma if_fold:"(if P then Q else if P then R else S) = (if P then Q else S)"
  by presburger

lemma fold_and_false[simp]:"\<not>(fold (op \<and>) xs False)"
  apply clarsimp
  apply (induct xs)
   apply simp
  apply simp
  done

lemma fold_and_true:"fold (op \<and>) xs True \<Longrightarrow> \<forall>i < length xs. xs ! i"
  apply clarsimp
  apply (induct xs)
   apply simp
  apply (case_tac "i = 0"; simp)
   apply (case_tac a; simp)
  apply (case_tac a; simp)
  done

lemma fold_or_true[simp]:"fold (op \<or>) xs True"
  by (induct xs, simp+)

lemma fold_or_false:"\<not>(fold (op \<or>) xs False) \<Longrightarrow> \<forall>i < length xs. \<not>(xs ! i)"
  apply (induct xs, simp+)
  apply (case_tac a, simp+)
  apply (rule allI, case_tac "i = 0", simp+)
  done

lemma fst_enumerate:"i < length xs \<Longrightarrow> fst (enumerate n xs ! i) = i + n"
  by (metis add.commute fst_conv nth_enumerate_eq)

lemma snd_enumerate:"i < length xs \<Longrightarrow> snd (enumerate n xs ! i) = xs ! i"
  by (metis nth_enumerate_eq snd_conv)

lemma pair_unpack:"((a, b) = x) = (a = fst x \<and> b = snd x)"
  by fastforce

lemma enumerate_member:"i < length xs \<Longrightarrow> (n + i, xs ! i) \<in> set (enumerate n xs)"
  apply (subgoal_tac "(n + i, xs ! i) = enumerate n xs ! i")
   apply clarsimp
  apply (subst pair_unpack)
  apply (rule conjI)
   apply (simp add:fst_enumerate)
  apply (simp add:snd_enumerate)
  done

end
