(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
   Miscellaneous library definitions and lemmas.
*)

chapter "Library"

theory Lib
imports "~~/src/HOL/Main"
begin

(* FIXME: eliminate *)
lemma hd_map_simp:
  "b \<noteq> [] \<Longrightarrow> hd (map a b) = a (hd b)"
  by (rule hd_map)

lemma tl_map_simp:
  "tl (map a b) = map a (tl b)"
  by (induct b,auto)

(* FIXME: could be added to Set.thy *)
lemma Collect_eq:
  "{x. P x} = {x. Q x} \<longleftrightarrow> (\<forall>x. P x = Q x)"
  by (rule iffI) auto

(* FIXME: move next to HOL.iff_allI *)
lemma iff_impI: "\<lbrakk>P \<Longrightarrow> Q = R\<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q) = (P \<longrightarrow> R)" by blast

definition
  fun_app :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 10) where
  "f $ x \<equiv> f x"

declare fun_app_def [iff]

lemma fun_app_cong[fundef_cong]:
  "\<lbrakk> f x = f' x' \<rbrakk> \<Longrightarrow> (f $ x) = (f' $ x')"
  by simp

lemma fun_app_apply_cong[fundef_cong]:
  "f x y = f' x' y' \<Longrightarrow> (f $ x) y = (f' $ x') y'"
  by simp

lemma if_apply_cong[fundef_cong]:
  "\<lbrakk> P = P'; x = x'; P' \<Longrightarrow> f x' = f' x'; \<not> P' \<Longrightarrow> g x' = g' x' \<rbrakk>
     \<Longrightarrow> (if P then f else g) x = (if P' then f' else g') x'"
  by simp

lemma case_prod_apply_cong[fundef_cong]:
  "\<lbrakk> f (fst p) (snd p) s = f' (fst p') (snd p') s' \<rbrakk> \<Longrightarrow> case_prod f p s = case_prod f' p' s'"
  by (simp add: split_def)

definition
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "and" 35)
where
  "pred_conj P Q \<equiv> \<lambda>x. P x \<and> Q x"

definition
  pred_disj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "or" 30)
where
  "pred_disj P Q \<equiv> \<lambda>x. P x \<or> Q x"

definition
  pred_neg :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" ("not _" [40] 40)
where
  "pred_neg P \<equiv> \<lambda>x. \<not> P x"

definition "K \<equiv> \<lambda>x y. x"

definition
  zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith f xs ys \<equiv> map (case_prod f) (zip xs ys)"

primrec
  delete :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "delete y [] = []"
| "delete y (x#xs) = (if y=x then xs else x # delete y xs)"

primrec
  find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
where
  "find f [] = None"
| "find f (x # xs) = (if f x then Some x else find f xs)"

definition
 "swp f \<equiv> \<lambda>x y. f y x"

primrec (nonexhaustive)
  theRight :: "'a + 'b \<Rightarrow> 'b" where
  "theRight (Inr x) = x"

primrec (nonexhaustive)
  theLeft :: "'a + 'b \<Rightarrow> 'a" where
  "theLeft (Inl x) = x"

definition
 "isLeft x \<equiv> (\<exists>y. x = Inl y)"

definition
 "isRight x \<equiv> (\<exists>y. x = Inr y)"

definition
 "const x \<equiv> \<lambda>y. x"

lemma tranclD2:
  "(x, y) \<in> R\<^sup>+ \<Longrightarrow> \<exists>z. (x, z) \<in> R\<^sup>* \<and> (z, y) \<in> R"
  by (erule tranclE) auto

lemma linorder_min_same1 [simp]:
  "(min y x = y) = (y \<le> (x::'a::linorder))"
  by (auto simp: min_def linorder_not_less)

lemma linorder_min_same2 [simp]:
  "(min x y = y) = (y \<le> (x::'a::linorder))"
  by (auto simp: min_def linorder_not_le)

text {* A combinator for pairing up well-formed relations.
        The divisor function splits the population in halves,
        with the True half greater than the False half, and
        the supplied relations control the order within the halves. *}

definition
  wf_sum :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
where
  "wf_sum divisor r r' \<equiv>
     ({(x, y). \<not> divisor x \<and> \<not> divisor y} \<inter> r')
   \<union>  {(x, y). \<not> divisor x \<and> divisor y}
   \<union> ({(x, y). divisor x \<and> divisor y} \<inter> r)"

lemma wf_sum_wf:
  "\<lbrakk> wf r; wf r' \<rbrakk> \<Longrightarrow> wf (wf_sum divisor r r')"
  apply (simp add: wf_sum_def)
  apply (rule wf_Un)+
      apply (erule wf_Int2)
     apply (rule wf_subset
             [where r="measure (\<lambda>x. If (divisor x) 1 0)"])
      apply simp
     apply clarsimp
    apply blast
   apply (erule wf_Int2)
  apply blast
  done

abbreviation(input)
 "option_map == map_option"

lemmas option_map_def = map_option_case

lemma False_implies_equals [simp]:
  "((False \<Longrightarrow> P) \<Longrightarrow> PROP Q) \<equiv> PROP Q"
  apply (rule equal_intr_rule)
   apply (erule meta_mp)
   apply simp
  apply simp
  done

lemma split_paired_Ball:
  "(\<forall>x \<in> A. P x) = (\<forall>x y. (x,y) \<in> A \<longrightarrow> P (x,y))"
  by auto

lemma split_paired_Bex:
  "(\<exists>x \<in> A. P x) = (\<exists>x y. (x,y) \<in> A \<and> P (x,y))"
  by auto

end
