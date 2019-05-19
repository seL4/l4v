(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter "Distinct Proposition"

theory Distinct_Prop  (* part of non-AFP Word_Lib *)
imports
  "Word_Lib/HOL_Lemmas"
  "HOL-Library.Prefix_Order"
begin

primrec
  distinct_prop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)"
where
  "distinct_prop P [] = True"
| "distinct_prop P (x # xs) = ((\<forall>y\<in>set xs. P x y) \<and> distinct_prop P xs)"

primrec
  distinct_sets :: "'a set list \<Rightarrow> bool"
where
  "distinct_sets [] = True"
| "distinct_sets (x#xs) = (x \<inter> \<Union> (set xs) = {} \<and> distinct_sets xs)"


lemma distinct_prop_map:
  "distinct_prop P (map f xs) = distinct_prop (\<lambda>x y. P (f x) (f y)) xs"
  by (induct xs) auto

lemma distinct_prop_append:
  "distinct_prop P (xs @ ys) =
    (distinct_prop P xs \<and> distinct_prop P ys \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. P x y))"
  by (induct xs arbitrary: ys) (auto simp: conj_comms ball_Un)

lemma distinct_prop_distinct:
  "\<lbrakk> distinct xs; \<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs; x \<noteq> y \<rbrakk> \<Longrightarrow> P x y \<rbrakk> \<Longrightarrow> distinct_prop P xs"
  by (induct xs) auto

lemma distinct_prop_True [simp]:
  "distinct_prop (\<lambda>x y. True) xs"
  by (induct xs, auto)


lemma distinct_prefix:
  "\<lbrakk> distinct xs; ys \<le> xs \<rbrakk> \<Longrightarrow> distinct ys"
  apply (induct xs arbitrary: ys; clarsimp)
  apply (case_tac ys; clarsimp)
  by (fastforce simp: less_eq_list_def dest: set_mono_prefix)

lemma distinct_sets_prop:
  "distinct_sets xs = distinct_prop (\<lambda>x y. x \<inter> y = {}) xs"
  by (induct xs) auto

lemma distinct_take_strg:
  "distinct xs \<longrightarrow> distinct (take n xs)"
  by simp

lemma distinct_prop_prefixE:
  "\<lbrakk> distinct_prop P ys; prefix xs ys \<rbrakk> \<Longrightarrow> distinct_prop P xs"
  apply (induct xs arbitrary: ys; clarsimp)
  apply (case_tac ys; clarsimp)
  by (fastforce dest: set_mono_prefix)


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
  "distinct_sets (xs @ a # ys) \<Longrightarrow>  a \<inter> \<Union> (set xs) = {} "
  apply (subst (asm) distinct_sets_prop)
  apply (subst (asm) distinct_prop_append)
  apply (subst Int_commute)
  apply (subst Union_disjoint)
  apply clarsimp
  done

lemma distinct_prop_take:
  "\<lbrakk>distinct_prop P xs; i < length xs\<rbrakk> \<Longrightarrow> distinct_prop P (take i xs)"
  by (metis take_is_prefix distinct_prop_prefixE)

lemma distinct_sets_take:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk> \<Longrightarrow> distinct_sets (take i xs)"
  by (simp add: distinct_sets_prop distinct_prop_take)

lemma distinct_prop_take_Suc:
  "\<lbrakk>distinct_prop P xs; i < length xs\<rbrakk> \<Longrightarrow> distinct_prop P (take (Suc i) xs)"
  by (metis distinct_prop_take not_less take_all)

lemma distinct_sets_take_Suc:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk> \<Longrightarrow> distinct_sets (take (Suc i) xs)"
  by (simp add: distinct_sets_prop distinct_prop_take_Suc)

lemma distinct_prop_rev:
  "distinct_prop P (rev xs) = distinct_prop (\<lambda>y x. P x y) xs"
  by (induct xs) (auto simp: distinct_prop_append)

lemma distinct_sets_rev [simp]:
  "distinct_sets (rev xs) = distinct_sets xs"
  apply (unfold distinct_sets_prop)
  apply (subst distinct_prop_rev)
  apply (subst Int_commute)
  apply clarsimp
  done

lemma distinct_sets_drop:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk> \<Longrightarrow> distinct_sets (drop i xs)"
  apply (cases "i=0", simp)
  apply (subst distinct_sets_rev [symmetric])
  apply (subst rev_drop)
  apply (subst distinct_sets_take, simp_all)
  done

lemma distinct_sets_drop_Suc:
  "\<lbrakk>distinct_sets xs; i < length xs\<rbrakk> \<Longrightarrow> distinct_sets (drop (Suc i) xs)"
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
  "\<lbrakk>x \<in> set xs; y \<in> set ys; distinct_sets (xs @ ys)\<rbrakk> \<Longrightarrow> x \<inter> y = {}"
  unfolding distinct_sets_prop by (clarsimp simp: distinct_prop_append)

lemma distinct_sets_update:
 "\<lbrakk>a \<subseteq> xs ! i; distinct_sets xs; i < length xs\<rbrakk> \<Longrightarrow> distinct_sets (xs[i := a])"
  apply (subst distinct_sets_prop)
  apply (subst (asm) distinct_sets_prop)
  apply (subst upd_conv_take_nth_drop, simp)
  apply (subst distinct_prop_append)
  apply (intro conjI)
    apply (erule (1) distinct_prop_take)
   apply (rule conjI|clarsimp)+
    apply (fold distinct_sets_prop)
    apply (drule (1) distinct_sets_drop)
    apply (subst (asm) drop_Suc_nth, assumption)
    apply fastforce
   apply (drule (1) distinct_sets_drop)
   apply (subst (asm) drop_Suc_nth, assumption)
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
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
  \<Longrightarrow> (\<Union>x\<in>set (xs [i := a]). f x) = (\<Union>x\<in>set xs. f x) - f (xs ! i) \<union> f a"
  apply (induct xs arbitrary: i; clarsimp)
  apply (case_tac i; (clarsimp, fastforce))
  done

lemma fst_enumerate:
  "i < length xs \<Longrightarrow> fst (enumerate n xs ! i) = i + n"
  by (metis add.commute fst_conv nth_enumerate_eq)

lemma snd_enumerate:
  "i < length xs \<Longrightarrow> snd (enumerate n xs ! i) = xs ! i"
  by (metis nth_enumerate_eq snd_conv)

lemma enumerate_member:
  assumes "i < length xs"
  shows "(n + i, xs ! i) \<in> set (enumerate n xs)"
proof -
  have pair_unpack: "\<And>a b x. ((a, b) = x) = (a = fst x \<and> b = snd x)" by fastforce
  from assms have "(n + i, xs ! i) = enumerate n xs ! i"
    by (auto simp: fst_enumerate snd_enumerate pair_unpack)
  with assms show ?thesis by simp
qed

lemma distinct_prop_nth:
  "\<lbrakk> distinct_prop P ls; n < n'; n' < length ls \<rbrakk> \<Longrightarrow> P (ls ! n) (ls ! n')"
  apply (induct ls arbitrary: n n'; simp)
  apply (case_tac n'; simp)
  apply (case_tac n; simp)
  done

end
