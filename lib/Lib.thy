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
imports
  Value_Abbreviation
  Try_Methods
  Extract_Conjunct
  Eval_Bool
  NICTATools
  "~~/src/HOL/Library/Prefix_Order"
begin

(* FIXME: eliminate *)
abbreviation (input)
  split   :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c"
where
  "split == case_prod"

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

lemma prod_injects:
  "(x,y) = p \<Longrightarrow> x = fst p \<and> y = snd p"
  "p = (x,y) \<Longrightarrow> x = fst p \<and> y = snd p"
  by auto

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

lemma delete_remove1:
  "delete x xs = remove1 x xs"
  by (induct xs, auto)

lemma ignore_if:
  "(y and z) s \<Longrightarrow> (if x then y else z) s"
  by (clarsimp simp: pred_conj_def)

lemma zipWith_Nil2 :
  "zipWith f xs [] = []"
  unfolding zipWith_def by simp

lemma isRight_right_map:
  "isRight (case_sum Inl (Inr o f) v) = isRight v"
  by (simp add: isRight_def split: sum.split)

lemma zipWith_nth:
  "\<lbrakk> n < min (length xs) (length ys) \<rbrakk> \<Longrightarrow> zipWith f xs ys ! n = f (xs ! n) (ys ! n)"
  unfolding zipWith_def by simp

lemma length_zipWith [simp]:
  "length (zipWith f xs ys) = min (length xs) (length ys)"
  unfolding zipWith_def by simp


lemma first_in_uptoD:
  "a \<le> b \<Longrightarrow> (a::'a::order) \<in> {a..b}"
  by simp

lemma construct_singleton:
  "\<lbrakk> S \<noteq> {}; \<forall>s\<in>S. \<forall>s'. s \<noteq> s' \<longrightarrow> s' \<notin> S \<rbrakk> \<Longrightarrow> \<exists>x. S = {x}"
  by blast

lemmas insort_com = insort_left_comm

lemma bleeding_obvious:
  "(P \<Longrightarrow> True) \<equiv> (Trueprop True)"
  by (rule, simp_all)

lemma Some_helper:
  "x = Some y \<Longrightarrow> x \<noteq> None"
  by simp

lemma in_empty_interE:
  "\<lbrakk> A \<inter> B = {}; x \<in> A; x \<in> B \<rbrakk> \<Longrightarrow> False"
  by blast

lemma None_upd_eq:
  "g x = None \<Longrightarrow> g(x := None) = g"
  by (rule ext) simp

lemma exx [iff]: "\<exists>x. x" by blast
lemma ExNot [iff]: "Ex Not" by blast

lemma cases_simp2 [simp]:
  "((\<not> P \<longrightarrow> Q) \<and> (P \<longrightarrow> Q)) = Q"
  by blast

lemma a_imp_b_imp_b:
  "((a \<longrightarrow> b) \<longrightarrow> b) = (a \<or> b)"
  by blast

lemma length_neq:
  "length as \<noteq> length bs \<Longrightarrow> as \<noteq> bs" by auto

lemma take_neq_length:
  "\<lbrakk> x \<noteq> y; x \<le> length as; y \<le> length bs\<rbrakk> \<Longrightarrow> take x as \<noteq> take y bs"
  by (rule length_neq, simp)

lemma eq_concat_lenD:
  "xs = ys @ zs \<Longrightarrow> length xs = length ys + length zs"
  by simp

lemma map_upt_reindex': "map f [a ..< b] = map (\<lambda>n. f (n + a - x)) [x ..< x + b - a]"
  by (rule nth_equalityI; clarsimp simp: add.commute)

lemma map_upt_reindex: "map f [a ..< b] = map (\<lambda>n. f (n + a)) [0 ..< b - a]"
  by (subst map_upt_reindex' [where x=0]) clarsimp

lemma notemptyI:
  "x \<in> S \<Longrightarrow> S \<noteq> {}"
  by clarsimp

lemma setcomp_Max_has_prop:
  assumes a: "P x"
  shows "P (Max {(x::'a::{finite,linorder}). P x})"
proof -
  from a have "Max {x. P x} \<in> {x. P x}"
    by - (rule Max_in, auto intro: notemptyI)
  thus ?thesis by auto
qed

lemma cons_set_intro:
  "lst = x # xs \<Longrightarrow> x \<in> set lst"
  by fastforce

lemma list_all2_conj_nth:
  assumes lall: "list_all2 P as cs"
  and       rl: "\<And>n. \<lbrakk>P (as ! n) (cs ! n); n < length as\<rbrakk> \<Longrightarrow> Q (as ! n) (cs ! n)"
  shows   "list_all2 (\<lambda>a b. P a b \<and> Q a b) as cs"
proof (rule list_all2_all_nthI)
  from lall show "length as = length cs" ..
next
  fix n
  assume "n < length as"

  show "P (as ! n) (cs ! n) \<and> Q (as ! n) (cs ! n)"
  proof
    from lall show "P (as ! n) (cs ! n)" by (rule list_all2_nthD) fact
    thus "Q (as ! n) (cs ! n)" by (rule rl) fact
  qed
qed

lemma list_all2_conj:
  assumes lall1: "list_all2 P as cs"
  and     lall2: "list_all2 Q as cs"
  shows   "list_all2 (\<lambda>a b. P a b \<and> Q a b) as cs"
proof (rule list_all2_all_nthI)
  from lall1 show "length as = length cs" ..
next
  fix n
  assume "n < length as"

  show "P (as ! n) (cs ! n) \<and> Q (as ! n) (cs ! n)"
  proof
    from lall1 show "P (as ! n) (cs ! n)" by (rule list_all2_nthD) fact
    from lall2 show "Q (as ! n) (cs ! n)" by (rule list_all2_nthD) fact
  qed
qed

lemma all_set_into_list_all2:
  assumes lall: "\<forall>x \<in> set ls. P x"
  and           "length ls = length ls'"
  shows  "list_all2 (\<lambda>a b. P a) ls ls'"
proof (rule list_all2_all_nthI)
  fix n
  assume "n < length ls"
  from lall show "P (ls ! n)"
    by (rule bspec [OF _ nth_mem]) fact
qed fact

lemma GREATEST_lessE:
  fixes x :: "'a :: order"
  assumes gts: "(GREATEST x. P x) < X"
  and      px: "P x"
  and    gtst: "\<exists>max. P max \<and> (\<forall>z. P z \<longrightarrow> (z \<le> max))"
  shows    "x < X"
proof -
  from gtst obtain max where pm: "P max" and g': "\<And>z. P z \<Longrightarrow> z \<le> max"
    by auto

  hence "(GREATEST x. P x) = max"
    by (auto intro: Greatest_equality)

  moreover have "x \<le> max" using px by (rule g')

  ultimately show ?thesis using gts by simp
qed

lemma set_has_max:
  fixes ls :: "('a :: linorder) list"
  assumes ls: "ls \<noteq> []"
  shows "\<exists>max \<in> set ls. \<forall>z \<in> set ls. z \<le> max"
  using ls
proof (induct ls)
  case Nil thus ?case by simp
next
  case (Cons l ls)

  show ?case
  proof (cases "ls = []")
   case True
   thus ?thesis by simp
 next
   case False
   then obtain max where mv: "max \<in> set ls" and mm: "\<forall>z \<in> set ls. z \<le> max" using Cons.hyps
     by auto
   show ?thesis
   proof (cases "max \<le> l")
     case True
     have "l \<in> set (l # ls)" by simp
     thus ?thesis
     proof
       from mm show "\<forall>z \<in> set (l # ls). z \<le> l" using True by auto
     qed
   next
     case False
     from mv have "max \<in> set (l # ls)" by simp
     thus ?thesis
     proof
       from mm show "\<forall>z \<in> set (l # ls). z \<le> max" using False by auto
     qed
   qed
 qed
qed

lemma True_notin_set_replicate_conv:
  "True \<notin> set ls = (ls = replicate (length ls) False)"
  by (induct ls) simp+

lemma Collect_singleton_eqI:
  "(\<And>x. P x = (x = v)) \<Longrightarrow> {x. P x} = {v}"
  by auto

lemma exEI:
  "\<lbrakk> \<exists>y. P y; \<And>x. P x \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> \<exists>z. Q z"
  by (rule ex_forward)

lemma allEI:
  assumes "\<forall>x. P x"
  assumes "\<And>x. P x \<Longrightarrow> Q x"
  shows   "\<forall>x. Q x"
  using assms by (rule all_forward)

text {* General lemmas that should be in the library *}

lemma dom_ran:
  "x \<in> dom f \<Longrightarrow> the (f x) \<in> ran f"
  by (simp add: dom_def ran_def, erule exE, simp, rule exI, simp)

lemma orthD1:
  "\<lbrakk> S \<inter> S' = {}; x \<in> S\<rbrakk> \<Longrightarrow> x \<notin> S'" by auto

lemma orthD2:
  "\<lbrakk> S \<inter> S' = {}; x \<in> S'\<rbrakk> \<Longrightarrow> x \<notin> S" by auto

lemma distinct_element:
  "\<lbrakk> b \<inter> d = {}; a \<in> b; c \<in> d\<rbrakk>\<Longrightarrow> a \<noteq> c"
  by auto

lemma ball_reorder:
  "(\<forall>x \<in> A. \<forall>y \<in> B. P x y) = (\<forall>y \<in> B. \<forall>x \<in> A.  P x y)"
  by auto

lemma hd_map: "ls \<noteq> [] \<Longrightarrow> hd (map f ls) = f (hd ls)"
  by (cases ls) auto

lemma tl_map: "tl (map f ls) = map f (tl ls)"
  by (cases ls) auto

lemma not_NilE:
  "\<lbrakk> xs \<noteq> []; \<And>x xs'. xs = x # xs' \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (cases xs) auto

lemma length_SucE:
  "\<lbrakk> length xs = Suc n; \<And>x xs'. xs = x # xs' \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (cases xs) auto

lemma map_upt_unfold:
  assumes ab: "a < b"
  shows   "map f [a ..< b] = f a # map f [Suc a ..< b]"
  using assms upt_conv_Cons by auto

lemma image_Collect2:
  "case_prod f ` {x. P (fst x) (snd x)} = {f x y |x y. P x y}"
  by (subst image_Collect) simp

lemma image_id':
  "id ` Y = Y"
  by clarsimp

lemma image_invert:
  assumes r: "f \<circ> g = id"
  and     g: "B = g ` A"
  shows  "A = f ` B"
  by (simp add: g image_comp r)

lemma Collect_image_fun_cong:
  assumes rl: "\<And>a. P a \<Longrightarrow> f a = g a"
  shows   "{f x | x. P x} = {g x | x. P x}"
  using rl by force

lemma inj_on_take:
  shows "inj_on (take n) {x. drop n x = k}"
proof (rule inj_onI)
  fix x y
  assume xv: "x \<in> {x. drop n x = k}"
    and yv: "y \<in> {x. drop n x = k}"
    and tk: "take n x = take n y"

  from xv have "take n x @ k = x"
    using append_take_drop_id mem_Collect_eq by auto
  moreover from yv tk
  have "take n x @ k = y"
    using append_take_drop_id mem_Collect_eq by auto
  ultimately show "x = y" by simp
qed

lemma foldr_upd_dom:
  "dom (foldr (\<lambda>p ps. ps (p \<mapsto> f p)) as g) = dom g \<union> set as"
proof (induct as)
  case Nil thus ?case by simp
next
  case (Cons a as)
  show ?case
  proof (cases "a \<in> set as \<or> a \<in> dom g")
    case True
    hence ain: "a \<in> dom g \<union> set as" by auto
    hence "dom g \<union> set (a # as) = dom g \<union> set as" by auto
    thus ?thesis using Cons by fastforce
  next
    case False
    hence "a \<notin> (dom g \<union> set as)" by simp
    hence "dom g \<union> set (a # as) = insert a (dom g \<union> set as)" by simp
    thus ?thesis using Cons by fastforce
  qed
qed

lemma foldr_upd_app:
  assumes xin: "x \<in> set as"
  shows "(foldr (\<lambda>p ps. ps (p \<mapsto> f p)) as g) x = Some (f x)"
  (is "(?f as g) x = Some (f x)")
  using xin
proof (induct as arbitrary: x)
  case Nil thus ?case by simp
next
  case (Cons a as)
  from Cons.prems show ?case  by (subst foldr.simps) (auto intro: Cons.hyps)
qed

lemma foldr_upd_app_other:
  assumes xin: "x \<notin> set as"
  shows "(foldr (\<lambda>p ps. ps (p \<mapsto> f p)) as g) x = g x"
  (is "(?f as g) x = g x")
  using xin
proof (induct as arbitrary: x)
  case Nil thus ?case by simp
next
  case (Cons a as)
  from Cons.prems show ?case
    by (subst foldr.simps) (auto intro: Cons.hyps)
qed

lemma foldr_upd_app_if:
  "foldr (\<lambda>p ps. ps(p \<mapsto> f p)) as g = (\<lambda>x. if x \<in> set as then Some (f x) else g x)"
  by (auto simp: foldr_upd_app foldr_upd_app_other)

lemma foldl_fun_upd_value:
  "\<And>Y. foldl (\<lambda>f p. f(p := X p)) Y e p = (if p\<in>set e then X p else Y p)"
  by (induct e) simp_all

lemma foldr_fun_upd_value:
  "\<And>Y. foldr (\<lambda>p f. f(p := X p)) e Y p = (if p\<in>set e then X p else Y p)"
  by (induct e) simp_all

lemma foldl_fun_upd_eq_foldr:
  "!!m. foldl (\<lambda>f p. f(p := g p)) m xs = foldr (\<lambda>p f. f(p := g p)) xs m"
  by (rule ext) (simp add: foldl_fun_upd_value foldr_fun_upd_value)

lemma Cons_eq_neq:
  "\<lbrakk> y = x; x # xs \<noteq> y # ys \<rbrakk> \<Longrightarrow> xs \<noteq> ys"
  by simp

lemma map_upt_append:
  assumes lt: "x \<le> y"
  and    lt2: "a \<le> x"
  shows   "map f [a ..< y] = map f [a ..< x] @ map f [x ..< y]"
proof (subst map_append [symmetric], rule arg_cong [where f = "map f"])
  from lt obtain k where ky: "x + k = y"
    by (auto simp: le_iff_add)

  thus "[a ..< y] = [a ..< x] @ [x ..< y]"
    using lt2
    by (auto intro: upt_add_eq_append)
qed

lemma Min_image_distrib:
  assumes minf: "\<And>x y. \<lbrakk> x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> min (f x) (f y) = f (min x y)"
  and       fa: "finite A"
  and      ane: "A \<noteq> {}"
  shows "Min (f ` A) = f (Min A)"
proof -
  have rl: "\<And>F. \<lbrakk> F \<subseteq> A; F \<noteq> {} \<rbrakk> \<Longrightarrow> Min (f ` F) = f (Min F)"
  proof -
    fix F
    assume fa: "F \<subseteq> A" and fne: "F \<noteq> {}"
    have "finite F" by (rule finite_subset) fact+

    thus "?thesis F"
      unfolding min_def using fa fne fa
    proof (induct rule: finite_subset_induct)
      case empty
      thus ?case by simp
    next
      case (insert x F)
      thus ?case
        by (cases "F = {}") (auto dest: Min_in intro: minf)
    qed
  qed

  show ?thesis by (rule rl [OF order_refl]) fact+
qed


lemma min_of_mono':
  assumes "(f a \<le> f c) = (a \<le> c)"
  shows "min (f a) (f c) = f (min a c)"
  unfolding min_def
  by (subst if_distrib [where f = f, symmetric], rule arg_cong [where f = f], rule if_cong [OF _ refl refl]) fact+

lemma nat_diff_less:
  fixes x :: nat
  shows "\<lbrakk> x < y + z; z \<le> x\<rbrakk> \<Longrightarrow> x - z < y"
  using less_diff_conv2 by blast

lemma take_map_Not:
  "(take n (map Not xs) = take n xs) = (n = 0 \<or> xs = [])"
  by (cases n; simp) (cases xs; simp)

lemma union_trans:
  assumes SR: "\<And>x y z. \<lbrakk> (x,y) \<in> S; (y,z) \<in> R \<rbrakk> \<Longrightarrow> (x,z) \<in> S^*"
  shows "(R \<union> S)^* = R^* \<union> R^* O S^*"
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule rtrancl_induct; simp)
   apply (erule disjE)
    apply (erule disjE)
     apply (drule (1) rtrancl_into_rtrancl)
     apply blast
    apply clarsimp
    apply (drule rtranclD [where R=S])
    apply (erule disjE)
     apply simp
    apply (erule conjE)
    apply (drule tranclD2)
    apply (elim exE conjE)
    apply (drule (1) SR)
    apply (drule (1) rtrancl_trans)
    apply blast
   apply (rule disjI2)
   apply (erule disjE)
    apply (blast intro: in_rtrancl_UnI)
   apply clarsimp
   apply (drule (1) rtrancl_into_rtrancl)
   apply (erule (1) relcompI)
  apply (erule disjE)
   apply (blast intro: in_rtrancl_UnI)
  apply clarsimp
  apply (blast intro: in_rtrancl_UnI rtrancl_trans)
  done

lemma trancl_trancl:
  "(R\<^sup>+)\<^sup>+ = R\<^sup>+"
  by auto

lemma if_1_0_0:
  "((if P then 1 else 0) = (0 :: ('a :: zero_neq_one))) = (\<not> P)"
  by (simp split: if_split)

lemma neq_Nil_lengthI:
  "Suc 0 \<le> length xs \<Longrightarrow> xs \<noteq> []"
  by (cases xs, auto)

lemmas ex_with_length = Ex_list_of_length

lemma in_singleton:
  "S = {x} \<Longrightarrow> x \<in> S"
  by simp

lemma singleton_set:
 "x \<in> set [a] \<Longrightarrow> x = a"
  by auto

lemma take_drop_eqI:
  assumes t: "take n xs = take n ys"
  assumes d: "drop n xs = drop n ys"
  shows "xs = ys"
proof -
  have "xs = take n xs @ drop n xs" by simp
  with t d
  have "xs = take n ys @ drop n ys" by simp
  moreover
  have "ys = take n ys @ drop n ys" by simp
  ultimately
  show ?thesis by simp
qed

lemma append_len2:
  "zs = xs @ ys \<Longrightarrow> length xs = length zs - length ys"
  by auto

lemma if_flip:
  "(if \<not>P then T else F) = (if P then F else T)"
  by simp

lemma not_in_domIff:"f x = None = (x \<notin> dom f)"
  by blast

lemma not_in_domD:
  "x \<notin> dom f \<Longrightarrow> f x = None"
  by (simp add:not_in_domIff)

definition
  "graph_of f \<equiv> {(x,y). f x = Some y}"

lemma graph_of_None_update:
  "graph_of (f (p := None)) = graph_of f - {p} \<times> UNIV"
  by (auto simp: graph_of_def split: if_split_asm)

lemma graph_of_Some_update:
  "graph_of (f (p \<mapsto> v)) = (graph_of f - {p} \<times> UNIV) \<union> {(p,v)}"
  by (auto simp: graph_of_def split: if_split_asm)

lemma graph_of_restrict_map:
  "graph_of (m |` S) \<subseteq> graph_of m"
  by (simp add: graph_of_def restrict_map_def subset_iff)

lemma graph_ofD:
  "(x,y) \<in> graph_of f \<Longrightarrow> f x = Some y"
  by (simp add: graph_of_def)

lemma graph_ofI:
  "m x = Some y \<Longrightarrow> (x, y) \<in> graph_of m"
  by (simp add: graph_of_def)

lemma graph_of_empty :
  "graph_of empty = {}"
  by (simp add: graph_of_def)

lemma graph_of_in_ranD: "\<forall>y \<in> ran f. P y \<Longrightarrow> (x,y) \<in> graph_of f \<Longrightarrow> P y"
  by (auto simp: graph_of_def ran_def)

lemma in_set_zip_refl :
  "(x,y) \<in> set (zip xs xs) = (y = x \<and> x \<in> set xs)"
  by (induct xs) auto

lemma map_conv_upd:
  "m v = None \<Longrightarrow> m o (f (x := v)) = (m o f) (x := None)"
  by (rule ext) (clarsimp simp: o_def)

lemma sum_all_ex [simp]:
  "(\<forall>a. x \<noteq> Inl a) = (\<exists>a. x = Inr a)"
  "(\<forall>a. x \<noteq> Inr a) = (\<exists>a. x = Inl a)"
  by (metis Inr_not_Inl sum.exhaust)+

lemma split_distrib: "case_prod (\<lambda>a b. T (f a b)) = (\<lambda>x. T (case_prod (\<lambda>a b. f a b) x))"
  by (clarsimp simp: split_def)

lemma case_sum_triv [simp]:
    "(case x of Inl x \<Rightarrow> Inl x | Inr x \<Rightarrow> Inr x) = x"
  by (clarsimp split: sum.splits)

lemma set_eq_UNIV: "({a. P a} = UNIV) = (\<forall>a. P a)"
  by force

lemma allE2:
  "\<lbrakk>\<forall>x y. P x y; P x y \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by blast

lemma allE3: "\<lbrakk> \<forall>x y z. P x y z; P x y z \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by auto

lemma my_BallE: "\<lbrakk> \<forall>x \<in> A. P x; y \<in> A; P y \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (simp add: Ball_def)

lemma unit_Inl_or_Inr [simp]:
  "\<And>a. (a \<noteq> Inl ()) = (a = Inr ())"
  "\<And>a. (a \<noteq> Inr ()) = (a = Inl ())"
  by (case_tac a; clarsimp)+

lemma disjE_L: "\<lbrakk> a \<or> b; a \<Longrightarrow> R; \<lbrakk> \<not> a; b \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by blast

lemma disjE_R: "\<lbrakk> a \<or> b; \<lbrakk> \<not> b; a \<rbrakk> \<Longrightarrow> R; \<lbrakk> b \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by blast

lemma int_max_thms:
    "(a :: int) \<le> max a b"
    "(b :: int) \<le> max a b"
  by (auto simp: max_def)

lemma sgn_negation [simp]:
  "sgn (-(x::int)) = - sgn x"
  by (clarsimp simp: sgn_if)

lemma sgn_sgn_nonneg [simp]:
  "sgn (a :: int) * sgn a \<noteq> -1"
  by (clarsimp simp: sgn_if)


lemma inj_inj_on:
  "inj f \<Longrightarrow> inj_on f A"
  by (metis injD inj_onI)

lemma ex_eqI:
  "\<lbrakk>\<And>x. f x = g x\<rbrakk> \<Longrightarrow> (\<exists>x. f x) = (\<exists>x. g x)"
  by simp

lemma pre_post_ex:
  "\<lbrakk>\<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> \<exists>x. Q x"
  by auto

lemma ex_conj_increase:
  "((\<exists>x. P x) \<and> Q) = (\<exists>x. P x \<and> Q)"
  "(R \<and> (\<exists>x. S x)) = (\<exists>x. R \<and> S x)"
  by simp+

lemma all_conj_increase:
  "(( \<forall>x. P x) \<and> Q) = (\<forall>x. P x \<and> Q)"
  "(R \<and> (\<forall>x. S x)) = (\<forall>x. R \<and> S x)"
  by simp+

lemma Ball_conj_increase:
  "xs \<noteq> {} \<Longrightarrow> (( \<forall>x \<in> xs. P x) \<and> Q) = (\<forall>x \<in> xs. P x \<and> Q)"
  "xs \<noteq> {} \<Longrightarrow> (R \<and> (\<forall>x \<in> xs. S x)) = (\<forall>x \<in> xs. R \<and> S x)"
  by auto

(***************
 * Union rules *
 ***************)

lemma disjoint_subset:
  assumes "A' \<subseteq> A" and "A \<inter> B = {}"
  shows   "A' \<inter> B = {}"
  using assms by auto

lemma disjoint_subset2:
  assumes "B' \<subseteq> B" and "A \<inter> B = {}"
  shows   "A \<inter> B' = {}"
  using assms by auto

lemma UN_nth_mem:
  "i < length xs \<Longrightarrow> f (xs ! i) \<subseteq> (\<Union>x\<in>set xs. f x)"
  by (metis UN_upper nth_mem)

lemma Union_equal:
  "f ` A = f ` B \<Longrightarrow> (\<Union>x \<in> A. f x) = (\<Union>x \<in> B. f x)"
  by blast

lemma UN_Diff_disjoint:
  "i < length xs \<Longrightarrow> (A - (\<Union>x\<in>set xs. f x)) \<inter> f (xs ! i) = {}"
  by (metis Diff_disjoint Int_commute UN_nth_mem disjoint_subset)

lemma image_list_update:
  "f a = f (xs ! i)
  \<Longrightarrow> f ` set (xs [i := a]) = f ` set xs"
  by (metis list_update_id map_update set_map)

lemma Union_list_update_id:
  "f a = f (xs ! i) \<Longrightarrow> (\<Union>x\<in>set (xs [i := a]). f x) = (\<Union>x\<in>set xs. f x)"
  by (rule Union_equal) (erule image_list_update)

lemma Union_list_update_id':
  "\<lbrakk>i < length xs; \<And>x. g (f x) = g x\<rbrakk>
  \<Longrightarrow> (\<Union>x\<in>set (xs [i := f (xs ! i)]). g x) = (\<Union>x\<in>set xs. g x)"
  by (metis Union_list_update_id)

lemma Union_subset:
  "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> (f x) \<subseteq> (g x)\<rbrakk> \<Longrightarrow> (\<Union>x \<in> A. f x) \<subseteq> (\<Union>x \<in> A. g x)"
  by (metis UN_mono order_refl)

lemma UN_sub_empty:
  "\<lbrakk>list_all P xs; \<And>x. P x \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> (\<Union>x\<in>set xs. f x) - (\<Union>x\<in>set xs. g x) = {}"
  by (metis Ball_set_list_all Diff_cancel SUP_cong)

(*******************
 * bij_betw rules. *
 *******************)

lemma bij_betw_fun_updI:
  "\<lbrakk>x \<notin> A; y \<notin> B; bij_betw f A B\<rbrakk> \<Longrightarrow> bij_betw (f(x := y)) (insert x A) (insert y B)"
  by (clarsimp simp: bij_betw_def fun_upd_image inj_on_fun_updI split: if_split_asm)

definition
  "bij_betw_map f A B \<equiv> bij_betw f A (Some ` B)"

lemma bij_betw_map_fun_updI:
  "\<lbrakk>x \<notin> A; y \<notin> B; bij_betw_map f A B\<rbrakk>
  \<Longrightarrow> bij_betw_map (f(x \<mapsto> y)) (insert x A) (insert y B)"
  unfolding bij_betw_map_def by clarsimp (erule bij_betw_fun_updI; clarsimp)

lemma bij_betw_map_imp_inj_on:
  "bij_betw_map f A B \<Longrightarrow> inj_on f A"
  by (simp add: bij_betw_map_def bij_betw_imp_inj_on)

lemma bij_betw_empty_dom_exists:
  "r = {} \<Longrightarrow> \<exists>t. bij_betw t {} r"
  by (clarsimp simp: bij_betw_def)

lemma bij_betw_map_empty_dom_exists:
  "r = {} \<Longrightarrow> \<exists>t. bij_betw_map t {} r"
  by (clarsimp simp: bij_betw_map_def bij_betw_empty_dom_exists)

(*
 * Function and Relation Powers.
 *)

lemma funpow_add [simp]:
  fixes f :: "'a \<Rightarrow> 'a"
  shows "(f ^^ a) ((f ^^ b) s) = (f ^^ (a + b)) s"
  by (metis comp_apply funpow_add)

lemma funpow_unfold:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes "n > 0"
  shows "f ^^ n = (f ^^ (n - 1)) \<circ> f"
  by (metis Suc_diff_1 assms funpow_Suc_right)

lemma relpow_unfold: "n > 0 \<Longrightarrow> S ^^ n = (S ^^ (n - 1)) O S"
  by (cases n, auto)


(*
 * Equivalence relations.
 *)

(* Convert a projection into an equivalence relation. *)
definition
  equiv_of :: "('s \<Rightarrow> 't) \<Rightarrow> ('s \<times> 's) set"
where
  "equiv_of proj \<equiv> {(a, b). proj a = proj b}"

lemma equiv_of_is_equiv_relation [simp]:
   "equiv UNIV (equiv_of proj)"
  by (auto simp: equiv_of_def intro!: equivI refl_onI symI transI)

lemma in_equiv_of [simp]:
  "((a, b) \<in> equiv_of f) \<longleftrightarrow> (f a = f b)"
  by (clarsimp simp: equiv_of_def)

(* For every equivalence relation R, there exists a projection function
 * "f" such that "f x = f y \<longleftrightarrow> (x, y) \<in> R". That is, you can reason
 * about projections instead of equivalence relations if you so wish. *)
lemma equiv_relation_to_projection:
  fixes R :: "('a \<times> 'a) set"
  assumes equiv: "equiv UNIV R"
  shows "\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>x y. f x = f y \<longleftrightarrow> (x, y) \<in> R"
  apply (rule exI [of _ "\<lambda>x. {y. (x, y) \<in> R}"])
  apply clarsimp
  apply (case_tac "(x, y) \<in> R")
   apply clarsimp
   apply (rule set_eqI)
   apply clarsimp
   apply (metis equivE sym_def trans_def equiv)
  apply (clarsimp)
  apply (metis UNIV_I equiv equivE mem_Collect_eq refl_on_def)
  done

lemma range_constant [simp]:
  "range (\<lambda>_. k) = {k}"
  by (clarsimp simp: image_def)

lemma dom_unpack:
  "dom (map_of (map (\<lambda>x. (f x, g x)) xs)) = set (map (\<lambda>x. f x) xs)"
  by (simp add: dom_map_of_conv_image_fst image_image)

lemma fold_to_disj:
"fold op ++ ms a x = Some y \<Longrightarrow> (\<exists>b \<in> set ms. b x = Some y) \<or> a x = Some y"
  by (induct ms arbitrary:a x y; clarsimp) blast

lemma fold_ignore1:
  "a x = Some y \<Longrightarrow> fold op ++ ms a x = Some y"
  by (induct ms arbitrary:a x y; clarsimp)

lemma fold_ignore2:
  "fold op ++ ms a x = None \<Longrightarrow> a x = None"
  by (metis fold_ignore1 option.collapse)

lemma fold_ignore3:
  "fold op ++ ms a x = None \<Longrightarrow> (\<forall>b \<in> set ms. b x = None)"
  by (induct ms arbitrary:a x; clarsimp) (meson fold_ignore2 map_add_None)

lemma fold_ignore4:
  "b \<in> set ms \<Longrightarrow> b x = Some y \<Longrightarrow> \<exists>y. fold op ++ ms a x = Some y"
  using fold_ignore3 by fastforce

lemma dom_unpack2:
  "dom (fold op ++ ms empty) = \<Union>(set (map dom ms))"
  apply (induct ms; clarsimp simp:dom_def)
  apply (rule equalityI; clarsimp)
   apply (drule fold_to_disj)
   apply (erule disjE)
    apply clarsimp
    apply (rename_tac b)
    apply (erule_tac x=b in ballE; clarsimp)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=y in exI)
   apply (erule fold_ignore1)
  apply clarsimp
  apply (rename_tac y)
  apply (erule_tac y=y in fold_ignore4; clarsimp)
  done

lemma fold_ignore5:"fold op ++ ms a x = Some y \<Longrightarrow> a x = Some y \<or> (\<exists>b \<in> set ms. b x = Some y)"
  by (induct ms arbitrary:a x y; clarsimp) blast

lemma dom_inter_nothing:"dom f \<inter> dom g = {} \<Longrightarrow> \<forall>x. f x = None \<or> g x = None"
  by auto

lemma fold_ignore6:
  "f x = None \<Longrightarrow> fold op ++ ms f x = fold op ++ ms empty x"
  apply (induct ms arbitrary:f x; clarsimp simp:map_add_def)
  by (metis (no_types, lifting) fold_ignore1 option.collapse option.simps(4))

lemma fold_ignore7:
  "m x = m' x \<Longrightarrow> fold op ++ ms m x = fold op ++ ms m' x"
  apply (case_tac "m x")
   apply (frule_tac ms=ms in fold_ignore6)
   apply (cut_tac f=m' and ms=ms and x=x in fold_ignore6)
    apply clarsimp+
  apply (rename_tac a)
  apply (cut_tac ms=ms and a=m and x=x and y=a in fold_ignore1, clarsimp)
  apply (cut_tac ms=ms and a=m' and x=x and y=a in fold_ignore1; clarsimp)
  done

lemma fold_ignore8:
  "fold op ++ ms [x \<mapsto> y] = (fold op ++ ms empty)(x \<mapsto> y)"
  apply (rule ext)
  apply (rename_tac xa)
  apply (case_tac "xa = x")
   apply clarsimp
   apply (rule fold_ignore1)
   apply clarsimp
  apply (subst fold_ignore6; clarsimp)
  done

lemma fold_ignore9:
  "\<lbrakk>fold op ++ ms [x \<mapsto> y] x' = Some z; x = x'\<rbrakk> \<Longrightarrow> y = z"
  by (subst (asm) fold_ignore8) clarsimp

lemma fold_to_map_of:
  "fold op ++ (map (\<lambda>x. [f x \<mapsto> g x]) xs) empty = map_of (map (\<lambda>x. (f x, g x)) xs)"
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac "fold op ++ (map (\<lambda>x. [f x \<mapsto> g x]) xs) Map.empty x")
   apply clarsimp
   apply (drule fold_ignore3)
   apply (clarsimp split:if_split_asm)
   apply (rule sym)
   apply (subst map_of_eq_None_iff)
   apply clarsimp
   apply (rename_tac xa)
   apply (erule_tac x=xa in ballE; clarsimp)
  apply clarsimp
  apply (frule fold_ignore5; clarsimp split:if_split_asm)
  apply (subst map_add_map_of_foldr[where m=empty, simplified])
  apply (induct xs arbitrary:f g; clarsimp split:if_split)
  apply (rule conjI; clarsimp)
   apply (drule fold_ignore9; clarsimp)
  apply (cut_tac ms="map (\<lambda>x. [f x \<mapsto> g x]) xs" and f="[f a \<mapsto> g a]" and x="f b" in fold_ignore6, clarsimp)
  apply auto
  done

lemma if_n_0_0:
  "((if P then n else 0) \<noteq> 0) = (P \<and> n \<noteq> 0)"
  by (simp split: if_split)

lemma insert_dom:
  assumes fx: "f x = Some y"
  shows   "insert x (dom f) = dom f"
  unfolding dom_def using fx by auto

lemma map_comp_subset_dom:
  "dom (prj \<circ>\<^sub>m f) \<subseteq> dom f"
  unfolding dom_def
  by (auto simp: map_comp_Some_iff)

lemmas map_comp_subset_domD = subsetD [OF map_comp_subset_dom]

lemma dom_map_comp:
  "x \<in> dom (prj \<circ>\<^sub>m f) = (\<exists>y z. f x = Some y \<and> prj y = Some z)"
  by (fastforce simp: dom_def map_comp_Some_iff)

lemma map_option_Some_eq2:
  "(Some y = map_option f x) = (\<exists>z. x = Some z \<and> f z = y)"
  by (metis map_option_eq_Some)

lemma map_option_eq_dom_eq:
  assumes ome: "map_option f \<circ> g = map_option f \<circ> g'"
  shows   "dom g = dom g'"
proof (rule set_eqI)
  fix x
  {
    assume "x \<in> dom g"
    hence "Some (f (the (g x))) = (map_option f \<circ> g) x"
      by (auto simp: map_option_case split: option.splits)
    also have "\<dots> = (map_option f \<circ> g') x" by (simp add: ome)
    finally have "x \<in> dom g'"
      by (auto simp: map_option_case split: option.splits)
  } moreover
  {
    assume "x \<in> dom g'"
    hence "Some (f (the (g' x))) = (map_option f \<circ> g') x"
      by (auto simp: map_option_case split: option.splits)
    also have "\<dots> = (map_option f \<circ> g) x" by (simp add: ome)
    finally have "x \<in> dom g"
      by (auto simp: map_option_case split: option.splits)
  } ultimately show "(x \<in> dom g) = (x \<in> dom g')" by auto
qed


lemma cart_singleton_image:
  "S \<times> {s} = (\<lambda>v. (v, s)) ` S"
  by auto

lemma singleton_eq_o2s:
  "({x} = set_option v) = (v = Some x)"
  by (cases v, auto)

lemma option_set_singleton_eq:
  "(set_option opt = {v}) = (opt = Some v)"
  by (cases opt, simp_all)

lemmas option_set_singleton_eqs
    = option_set_singleton_eq
      trans[OF eq_commute option_set_singleton_eq]

lemma map_option_comp2:
  "map_option (f o g) = map_option f o map_option g"
  by (simp add: option.map_comp fun_eq_iff)

lemma compD:
  "\<lbrakk>f \<circ> g = f \<circ> g'; g x = v \<rbrakk> \<Longrightarrow> f (g' x) = f v"
  by (metis comp_apply)

lemma map_option_comp_eqE:
  assumes om: "map_option f \<circ> mp = map_option f \<circ> mp'"
  and     p1: "\<lbrakk> mp x = None; mp' x = None \<rbrakk> \<Longrightarrow> P"
  and     p2: "\<And>v v'. \<lbrakk> mp x = Some v; mp' x = Some v'; f v = f v' \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases "mp x")
  case None
  hence "x \<notin> dom mp" by (simp add: domIff)
  hence "mp' x = None" by (simp add: map_option_eq_dom_eq [OF om] domIff)
  with None show ?thesis by (rule p1)
next
  case (Some v)
  hence "x \<in> dom mp" by clarsimp
  then obtain v' where Some': "mp' x = Some v'" by (clarsimp simp add: map_option_eq_dom_eq [OF om])
  with Some show ?thesis
  proof (rule p2)
    show "f v = f v'" using Some' compD [OF om, OF Some] by simp
  qed
qed

lemma Some_the:
  "x \<in> dom f \<Longrightarrow> f x = Some (the (f x))"
  by clarsimp

lemma map_comp_update:
  "f \<circ>\<^sub>m (g(x \<mapsto> v)) = (f \<circ>\<^sub>m g)(x := f v)"
  by (rule ext, rename_tac y) (case_tac "g y"; simp)

lemma restrict_map_eqI:
  assumes req: "A |` S = B |` S"
  and     mem: "x \<in> S"
  shows   "A x = B x"
proof -
  from mem have "A x = (A |` S) x" by simp
  also have "\<dots> = (B |` S) x" using req by simp
  also have "\<dots> = B x" using mem by simp
  finally show ?thesis .
qed

lemma map_comp_eqI:
  assumes dm: "dom g = dom g'"
  and     fg: "\<And>x. x \<in> dom g' \<Longrightarrow> f (the (g' x)) = f (the (g x))"
  shows  "f \<circ>\<^sub>m g = f \<circ>\<^sub>m g'"
  apply (rule ext)
  apply (case_tac "x \<in> dom g")
   apply (frule subst [OF dm])
   apply (clarsimp split: option.splits)
   apply (frule domI [where m = g'])
   apply (drule fg)
   apply simp
  apply (frule subst [OF dm])
  apply clarsimp
  apply (drule not_sym)
  apply (clarsimp simp: map_comp_Some_iff)
  done


definition
  "modify_map m p f \<equiv> m (p := map_option f (m p))"

lemma modify_map_id:
  "modify_map m p id = m"
  by (auto simp add: modify_map_def map_option_case split: option.splits)

lemma modify_map_addr_com:
  assumes com: "x \<noteq> y"
  shows "modify_map (modify_map m x g) y f = modify_map (modify_map m y f) x g"
  by (rule ext) (simp add: modify_map_def map_option_case com split: option.splits)

lemma modify_map_dom :
  "dom (modify_map m p f) = dom m"
  unfolding modify_map_def by (auto simp: dom_def)

lemma modify_map_None:
  "m x = None \<Longrightarrow> modify_map m x f = m"
  by (rule ext) (simp add: modify_map_def)

lemma modify_map_ndom :
  "x \<notin> dom m \<Longrightarrow> modify_map m x f = m"
  by (rule modify_map_None) clarsimp

lemma modify_map_app:
  "(modify_map m p f) q = (if p = q then map_option f (m p) else m q)"
  unfolding modify_map_def by simp

lemma modify_map_apply:
  "m p = Some x \<Longrightarrow> modify_map m p f = m (p \<mapsto> f x)"
  by (simp add: modify_map_def)

lemma modify_map_com:
  assumes com: "\<And>x. f (g x) = g (f x)"
  shows "modify_map (modify_map m x g) y f = modify_map (modify_map m y f) x g"
  using assms by (auto simp: modify_map_def map_option_case split: option.splits)

lemma modify_map_comp:
  "modify_map m x (f o g) = modify_map (modify_map m x g) x f"
  by (rule ext) (simp add: modify_map_def option.map_comp)

lemma modify_map_exists_eq:
  "(\<exists>cte. modify_map m p' f p= Some cte) = (\<exists>cte. m p = Some cte)"
  by (auto simp: modify_map_def split: if_splits)

lemma modify_map_other:
  "p \<noteq> q \<Longrightarrow> (modify_map m p f) q = (m q)"
  by (simp add: modify_map_app)

lemma modify_map_same:
  "modify_map m p f p = map_option f (m p)"
  by (simp add: modify_map_app)

lemma next_update_is_modify:
  "\<lbrakk> m p = Some cte'; cte = f cte' \<rbrakk> \<Longrightarrow> (m(p \<mapsto> cte)) = modify_map m p f"
  unfolding modify_map_def by simp

lemma nat_power_minus_less:
  "a < 2 ^ (x - n) \<Longrightarrow> (a :: nat) < 2 ^ x"
  by (erule order_less_le_trans) simp

lemma neg_rtranclI:
  "\<lbrakk> x \<noteq> y; (x, y) \<notin> R\<^sup>+ \<rbrakk> \<Longrightarrow> (x, y) \<notin> R\<^sup>*"
  by (meson rtranclD)

lemma neg_rtrancl_into_trancl:
  "\<not> (x, y) \<in> R\<^sup>* \<Longrightarrow> \<not> (x, y) \<in> R\<^sup>+"
  by (erule contrapos_nn, erule trancl_into_rtrancl)

lemma set_neqI:
  "\<lbrakk> x \<in> S; x \<notin> S' \<rbrakk> \<Longrightarrow> S \<noteq> S'"
  by clarsimp

lemma set_pair_UN:
  "{x. P x} = UNION {xa. \<exists>xb. P (xa, xb)} (\<lambda>xa. {xa} \<times> {xb. P (xa, xb)})"
  by fastforce

lemma singleton_elemD: "S = {x} \<Longrightarrow> x \<in> S"
  by simp

lemma singleton_eqD: "A = {x} \<Longrightarrow> x \<in> A"
  by blast

lemma ball_ran_fun_updI:
  "\<lbrakk> \<forall>v \<in> ran m. P v; \<forall>v. y = Some v \<longrightarrow> P v \<rbrakk> \<Longrightarrow> \<forall>v \<in> ran (m (x := y)). P v"
  by (auto simp add: ran_def)

lemma ball_ran_eq:
  "(\<forall>y \<in> ran m. P y) = (\<forall>x y. m x = Some y \<longrightarrow> P y)"
  by (auto simp add: ran_def)

lemma cart_helper:
  "({} = {x} \<times> S) = (S = {})"
  by blast

lemmas converse_trancl_induct' = converse_trancl_induct [consumes 1, case_names base step]

lemma disjCI2: "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by blast

lemma insert_UNIV :
  "insert x UNIV = UNIV"
  by blast

lemma not_singletonE:
  "\<lbrakk> \<forall>p. S \<noteq> {p}; S \<noteq> {}; \<And>p p'. \<lbrakk> p \<noteq> p'; p \<in> S; p' \<in> S \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by blast

lemma not_singleton_oneE:
  "\<lbrakk> \<forall>p. S \<noteq> {p}; p \<in> S; \<And>p'. \<lbrakk> p \<noteq> p'; p' \<in> S \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  using not_singletonE by fastforce

lemma ball_ran_modify_map_eq:
  "\<lbrakk> \<forall>v. m x = Some v \<longrightarrow> P (f v) = P v \<rbrakk>
  \<Longrightarrow> (\<forall>v \<in> ran (modify_map m x f). P v) = (\<forall>v \<in> ran m. P v)"
  by (auto simp: modify_map_def ball_ran_eq)

lemma disj_imp: "(P \<or> Q) = (\<not>P \<longrightarrow> Q)" by blast

lemma eq_singleton_redux:
  "\<lbrakk> S = {x} \<rbrakk> \<Longrightarrow> x \<in> S"
  by simp

lemma if_eq_elem_helperE:
  "\<lbrakk> x \<in> (if P then S else S');  \<lbrakk> P;   x \<in> S  \<rbrakk> \<Longrightarrow> a = b;  \<lbrakk> \<not> P; x \<in> S' \<rbrakk> \<Longrightarrow> a = c \<rbrakk>
  \<Longrightarrow> a = (if P then b else c)"
  by fastforce

lemma if_option_Some:
  "((if P then None else Some x) = Some y) = (\<not>P \<and> x = y)"
  by simp

lemma insert_minus_eq:
  "x \<notin> A \<Longrightarrow> A - S = (A - (S - {x}))"
  by auto

lemma modify_map_K_D:
  "modify_map m p (\<lambda>x. y) p' = Some v \<Longrightarrow> (m (p \<mapsto> y)) p' = Some v"
  by (simp add: modify_map_def split: if_split_asm)

lemma tranclE2:
  assumes trancl: "(a, b) \<in> r\<^sup>+"
  and       base: "(a, b) \<in> r \<Longrightarrow> P"
  and       step: "\<And>c. \<lbrakk>(a, c) \<in> r; (c, b) \<in> r\<^sup>+\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using trancl base step
proof -
  note rl = converse_trancl_induct [where P = "\<lambda>x. x = a \<longrightarrow> P"]
  from trancl have "a = a \<longrightarrow> P"
    by (rule rl, (iprover intro: base step)+)
  thus ?thesis by simp
qed

lemmas tranclE2' = tranclE2 [consumes 1, case_names base trancl]

lemma weak_imp_cong:
  "\<lbrakk> P = R; Q = S \<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q) = (R \<longrightarrow> S)"
  by simp

lemma Collect_Diff_restrict_simp:
  "T - {x \<in> T. Q x} = T - {x. Q x}"
  by (auto intro: Collect_cong)

lemma Collect_Int_pred_eq:
  "{x \<in> S. P x} \<inter> {x \<in> T. P x} = {x \<in> (S \<inter> T). P x}"
  by (simp add: Collect_conj_eq [symmetric] conj_comms)

lemma Collect_restrict_predR:
  "{x. P x} \<inter> T = {} \<Longrightarrow> {x. P x} \<inter> {x \<in> T. Q x} = {}"
  by (fastforce simp: disjoint_iff_not_equal)

lemma Diff_Un2:
  assumes emptyad: "A \<inter> D = {}"
  and     emptybc: "B \<inter> C = {}"
  shows   "(A \<union> B) - (C \<union> D) = (A - C) \<union> (B - D)"
proof -
  have "(A \<union> B) - (C \<union> D) = (A \<union> B - C) \<inter> (A \<union> B - D)"
    by (rule Diff_Un)
  also have "\<dots> = ((A - C) \<union> B) \<inter> (A \<union> (B - D))" using emptyad emptybc
    by (simp add: Un_Diff Diff_triv)
  also have "\<dots> = (A - C) \<union> (B - D)"
  proof -
    have "(A - C) \<inter> (A \<union> (B - D)) = A - C" using  emptyad emptybc
      by (metis Diff_Int2 Diff_Int_distrib2 inf_sup_absorb)
    moreover
    have "B \<inter> (A \<union> (B - D)) = B - D" using emptyad emptybc
      by (metis Int_Diff Un_Diff Un_Diff_Int Un_commute Un_empty_left inf_sup_absorb)
    ultimately show ?thesis
      by (simp add: Int_Un_distrib2)
  qed
  finally show ?thesis .
qed

lemma ballEI:
  "\<lbrakk> \<forall>x \<in> S. Q x; \<And>x. \<lbrakk> x \<in> S; Q x \<rbrakk> \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> \<forall>x \<in> S. P x"
  by auto

lemma dom_if_None:
  "dom (\<lambda>x. if P x then None else f x) = dom f - {x. P x}"
  by (simp add: dom_def) fastforce

lemma restrict_map_Some_iff:
  "((m |` S) x = Some y) = (m x = Some y \<and> x \<in> S)"
  by (cases "x \<in> S", simp_all)

lemma context_case_bools:
  "\<lbrakk> \<And>v. P v \<Longrightarrow> R v; \<lbrakk> \<not> P v; \<And>v. P v \<Longrightarrow> R v \<rbrakk> \<Longrightarrow> R v \<rbrakk> \<Longrightarrow> R v"
  by (cases "P v", simp_all)

lemma inj_on_fun_upd_strongerI:
  "\<lbrakk>inj_on f A; y \<notin> f ` (A - {x})\<rbrakk> \<Longrightarrow> inj_on (f(x := y)) A"
  by (fastforce simp: inj_on_def)

lemma less_handy_casesE:
  "\<lbrakk> m < n; m = 0 \<Longrightarrow> R; \<And>m' n'. \<lbrakk> n = Suc n'; m = Suc m'; m < n \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (case_tac n; simp) (case_tac m; simp)

lemma subset_drop_Diff_strg:
  "(A \<subseteq> C) \<longrightarrow> (A - B \<subseteq> C)"
  by blast

lemma inj_case_bool:
  "inj (case_bool a b) = (a \<noteq> b)"
  by (auto dest: inj_onD[where x=True and y=False] intro: inj_onI split: bool.split_asm)

lemma foldl_fun_upd:
  "foldl (\<lambda>s r. s (r := g r)) f rs = (\<lambda>x. if x \<in> set rs then g x else f x)"
  by (induct rs arbitrary: f) (auto simp: fun_eq_iff)

lemma all_rv_choice_fn_eq_pred:
  "\<lbrakk> \<And>rv. P rv \<Longrightarrow> \<exists>fn. f rv = g fn \<rbrakk> \<Longrightarrow> \<exists>fn. \<forall>rv. P rv \<longrightarrow> f rv = g (fn rv)"
  apply (rule_tac x="\<lambda>rv. SOME h. f rv = g h" in exI)
  apply (clarsimp split: if_split)
  by (meson someI_ex)

lemma ex_const_function:
  "\<exists>f. \<forall>s. f (f' s) = v"
  by force

lemma if_Const_helper:
  "If P (Con x) (Con y) = Con (If P x y)"
  by (simp split: if_split)

lemmas if_Some_helper = if_Const_helper[where Con=Some]

lemma expand_restrict_map_eq:
  "(m |` S = m' |` S) = (\<forall>x. x \<in> S \<longrightarrow> m x = m' x)"
  by (simp add: fun_eq_iff restrict_map_def split: if_split)

lemma disj_imp_rhs:
  "(P \<Longrightarrow> Q) \<Longrightarrow> (P \<or> Q) = Q"
  by blast

lemma remove1_filter:
  "distinct xs \<Longrightarrow> remove1 x xs = filter (\<lambda>y. x \<noteq> y) xs"
  by (induct xs) (auto intro!: filter_True [symmetric])

lemma Int_Union_empty:
  "(\<And>x. x \<in> S \<Longrightarrow> A \<inter> P x = {}) \<Longrightarrow> A \<inter> (\<Union>x \<in> S. P x) = {}"
  by auto

lemma UN_Int_empty:
  "(\<And>x. x \<in> S \<Longrightarrow> P x \<inter> T = {}) \<Longrightarrow> (\<Union>x \<in> S. P x) \<inter> T = {}"
  by auto

lemma disjointI:
  "\<lbrakk>\<And>x y. \<lbrakk> x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> x \<noteq> y \<rbrakk> \<Longrightarrow> A \<inter> B = {}"
  by auto

lemma UN_disjointI:
  assumes rl: "\<And>x y. \<lbrakk> x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> P x \<inter> Q y = {}"
  shows "(\<Union>x \<in> A. P x) \<inter> (\<Union>x \<in> B. Q x) = {}"
  by (auto dest: rl)

lemma UN_set_member:
  assumes sub: "A \<subseteq> (\<Union>x \<in> S. P x)"
  and      nz: "A \<noteq> {}"
  shows    "\<exists>x \<in> S. P x \<inter> A \<noteq> {}"
proof -
  from nz obtain z where zA: "z \<in> A" by fastforce
  with sub obtain x where "x \<in> S" and "z \<in> P x" by auto
  hence "P x \<inter> A \<noteq> {}" using zA by auto
  thus ?thesis using sub nz by auto
qed

lemma append_Cons_cases [consumes 1, case_names pre mid post]:
  "\<lbrakk>(x, y) \<in> set (as @ b # bs);
    (x, y) \<in> set as \<Longrightarrow> R;
    \<lbrakk>(x, y) \<notin> set as; (x, y) \<notin> set bs; (x, y) = b\<rbrakk> \<Longrightarrow> R;
    (x, y) \<in> set bs \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto

lemma cart_singletons:
  "{a} \<times> {b} = {(a, b)}"
  by blast

lemma disjoint_subset_neg1:
  "\<lbrakk> B \<inter> C = {}; A \<subseteq> B; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<not> A \<subseteq> C"
  by auto

lemma disjoint_subset_neg2:
  "\<lbrakk> B \<inter> C = {}; A \<subseteq> C; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<not> A \<subseteq> B"
  by auto

lemma iffE2:
  "\<lbrakk> P = Q; \<lbrakk> P; Q \<rbrakk> \<Longrightarrow> R; \<lbrakk> \<not> P; \<not> Q \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by blast

lemma list_case_If:
  "(case xs of [] \<Rightarrow> P | _ \<Rightarrow> Q) = (if xs = [] then P else Q)"
  by (rule list.case_eq_if)

lemma remove1_Nil_in_set:
  "\<lbrakk> remove1 x xs = []; xs \<noteq> [] \<rbrakk> \<Longrightarrow> x \<in> set xs"
  by (induct xs) (auto split: if_split_asm)

lemma remove1_empty:
  "(remove1 v xs = []) = (xs = [v] \<or> xs = [])"
  by (cases xs; simp)

lemma set_remove1:
  "x \<in> set (remove1 y xs) \<Longrightarrow> x \<in> set xs"
  by (induct xs) (auto split: if_split_asm)

lemma If_rearrage:
  "(if P then if Q then x else y else z) = (if P \<and> Q then x else if P then y else z)"
  by simp

lemma disjI2_strg:
  "Q \<longrightarrow> (P \<or> Q)"
  by simp

lemma eq_imp_strg:
  "P t \<longrightarrow> (t = s \<longrightarrow> P s)"
  by clarsimp

lemma if_both_strengthen:
  "P \<and> Q \<longrightarrow> (if G then P else Q)"
  by simp

lemma if_both_strengthen2:
  "P s \<and> Q s \<longrightarrow> (if G then P else Q) s"
  by simp

lemma if_swap:
  "(if P then Q else R) = (if \<not>P then R else Q)" by simp

lemma imp_consequent:
  "P \<longrightarrow> Q \<longrightarrow> P" by simp

lemma list_case_helper:
  "xs \<noteq> [] \<Longrightarrow> case_list f g xs = g (hd xs) (tl xs)"
  by (cases xs, simp_all)

lemma list_cons_rewrite:
  "(\<forall>x xs. L = x # xs \<longrightarrow> P x xs) = (L \<noteq> [] \<longrightarrow> P (hd L) (tl L))"
  by (auto simp: neq_Nil_conv)

lemma list_not_Nil_manip:
  "\<lbrakk> xs = y # ys; case xs of [] \<Rightarrow> False | (y # ys) \<Rightarrow> P y ys \<rbrakk> \<Longrightarrow> P y ys"
  by simp

lemma ran_ball_triv:
  "\<And>P m S. \<lbrakk> \<forall>x \<in> (ran S). P x ; m \<in> (ran S) \<rbrakk> \<Longrightarrow> P m"
  by blast

lemma singleton_tuple_cartesian:
  "({(a, b)} = S \<times> T) = ({a} = S \<and> {b} = T)"
  "(S \<times> T = {(a, b)}) = ({a} = S \<and> {b} = T)"
  by blast+

lemma strengthen_ignore_if:
  "A s \<and> B s \<longrightarrow> (if P then A else B) s"
  by clarsimp

lemma case_sum_True :
  "(case r of Inl a \<Rightarrow> True | Inr b \<Rightarrow> f b) = (\<forall>b. r = Inr b \<longrightarrow> f b)"
  by (cases r) auto

lemma sym_ex_elim:
  "F x = y \<Longrightarrow> \<exists>x. y = F x"
  by auto

lemma tl_drop_1 :
  "tl xs = drop 1 xs"
  by (simp add: drop_Suc)

lemma upt_lhs_sub_map:
  "[x ..< y] = map (op + x) [0 ..< y - x]"
  by (induct y) (auto simp: Suc_diff_le)

lemma upto_0_to_4:
  "[0..<4] = 0 # [1..<4]"
  by (subst upt_rec) simp

lemma disjEI:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> S \<rbrakk>
     \<Longrightarrow> R \<or> S"
  by fastforce

lemma dom_fun_upd2:
  "s x = Some z \<Longrightarrow> dom (s (x \<mapsto> y)) = dom s"
  by (simp add: insert_absorb domI)

lemma foldl_True :
  "foldl op \<or> True bs"
  by (induct bs) auto

lemma image_set_comp:
  "f ` {g x | x. Q x} = (f \<circ> g) ` {x. Q x}"
  by fastforce

lemma mutual_exE:
  "\<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> \<exists>x. Q x"
  by blast

lemma nat_diff_eq:
  fixes x :: nat
  shows "\<lbrakk> x - y = x - z; y < x\<rbrakk> \<Longrightarrow> y = z"
  by arith

lemma comp_upd_simp:
  "(f \<circ> (g (x := y))) = ((f \<circ> g) (x := f y))"
  by (rule fun_upd_comp)

lemma dom_option_map:
  "dom (map_option f o m) = dom m"
  by (rule dom_map_option_comp)

lemma drop_imp:
  "P \<Longrightarrow> (A \<longrightarrow> P) \<and> (B \<longrightarrow> P)" by blast

lemma inj_on_fun_updI2:
  "\<lbrakk> inj_on f A; y \<notin> f ` (A - {x}) \<rbrakk> \<Longrightarrow> inj_on (f(x := y)) A"
  by (rule inj_on_fun_upd_strongerI)

lemma inj_on_fun_upd_elsewhere:
  "x \<notin> S \<Longrightarrow> inj_on (f (x := y)) S = inj_on f S"
  by (simp add: inj_on_def) blast

lemma not_Some_eq_tuple:
  "(\<forall>y z. x \<noteq> Some (y, z)) = (x = None)"
  by (cases x, simp_all)

lemma ran_option_map:
  "ran (map_option f o m) = f ` ran m"
  by (auto simp add: ran_def)

lemma All_less_Ball:
  "(\<forall>x < n. P x) = (\<forall>x\<in>{..< n}. P x)"
  by fastforce

lemma Int_image_empty:
  "\<lbrakk> \<And>x y. f x \<noteq> g y \<rbrakk>
       \<Longrightarrow> f ` S \<inter> g ` T = {}"
  by auto

lemma Max_prop:
  "\<lbrakk> Max S \<in> S \<Longrightarrow> P (Max S); (S :: ('a :: {finite, linorder}) set) \<noteq> {} \<rbrakk> \<Longrightarrow> P (Max S)"
  by auto

lemma Min_prop:
  "\<lbrakk> Min S \<in> S \<Longrightarrow> P (Min S); (S :: ('a :: {finite, linorder}) set) \<noteq> {} \<rbrakk> \<Longrightarrow> P (Min S)"
  by auto

lemma findSomeD:
  "find P xs = Some x \<Longrightarrow> P x \<and> x \<in> set xs"
  by (induct xs) (auto split: if_split_asm)

lemma findNoneD:
  "find P xs = None \<Longrightarrow> \<forall>x \<in> set xs. \<not>P x"
  by (induct xs) (auto split: if_split_asm)

lemma dom_upd:
  "dom (\<lambda>x. if x = y then None else f x) = dom f - {y}"
  by (rule set_eqI) (auto split: if_split_asm)


definition
  is_inv :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'a) \<Rightarrow> bool" where
  "is_inv f g \<equiv> ran f = dom g \<and> (\<forall>x y. f x = Some y \<longrightarrow> g y = Some x)"

lemma is_inv_NoneD:
  assumes "g x = None"
  assumes "is_inv f g"
  shows "x \<notin> ran f"
proof -
  from assms
  have "x \<notin> dom g" by (auto simp: ran_def)
  moreover
  from assms
  have "ran f = dom g"
    by (simp add: is_inv_def)
  ultimately
  show ?thesis by simp
qed

lemma is_inv_SomeD:
  "\<lbrakk> f x = Some y; is_inv f g \<rbrakk> \<Longrightarrow> g y = Some x"
  by (simp add: is_inv_def)

lemma is_inv_com:
  "is_inv f g \<Longrightarrow> is_inv g f"
  apply (unfold is_inv_def)
  apply safe
    apply (clarsimp simp: ran_def dom_def set_eq_iff)
    apply (erule_tac x=a in allE)
    apply clarsimp
   apply (clarsimp simp: ran_def dom_def set_eq_iff)
   apply blast
  apply (clarsimp simp: ran_def dom_def set_eq_iff)
  apply (erule_tac x=x in allE)
  apply clarsimp
  done

lemma is_inv_inj:
  "is_inv f g \<Longrightarrow> inj_on f (dom f)"
  apply (frule is_inv_com)
  apply (clarsimp simp: inj_on_def)
  apply (drule (1) is_inv_SomeD)
  apply (auto dest: is_inv_SomeD)
  done

lemma ran_upd':
  "\<lbrakk>inj_on f (dom f); f y = Some z\<rbrakk> \<Longrightarrow> ran (f (y := None)) = ran f - {z}"
  by (force simp: ran_def inj_on_def dom_def intro!: set_eqI)

lemma is_inv_None_upd:
  "\<lbrakk> is_inv f g; g x = Some y\<rbrakk> \<Longrightarrow> is_inv (f(y := None)) (g(x := None))"
  apply (subst is_inv_def)
  apply (clarsimp simp: dom_upd)
  apply (drule is_inv_SomeD, erule is_inv_com)
  apply (frule is_inv_inj)
  apply (auto simp: ran_upd' is_inv_def dest: is_inv_SomeD is_inv_inj)
  done

lemma is_inv_inj2:
  "is_inv f g \<Longrightarrow> inj_on g (dom g)"
  using is_inv_com is_inv_inj by blast

lemma range_convergence1:
  "\<lbrakk> \<forall>z. x < z \<and> z \<le> y \<longrightarrow> P z; \<forall>z > y. P (z :: 'a :: linorder) \<rbrakk> \<Longrightarrow> \<forall>z > x. P z"
  using not_le by blast

lemma range_convergence2:
  "\<lbrakk> \<forall>z. x < z \<and> z \<le> y \<longrightarrow> P z; \<forall>z. z > y \<and> z < w \<longrightarrow> P (z :: 'a :: linorder) \<rbrakk>
     \<Longrightarrow> \<forall>z. z > x \<and> z < w \<longrightarrow> P z"
  using range_convergence1[where P="\<lambda>z. z < w \<longrightarrow> P z" and x=x and y=y]
  by auto

lemma zip_upt_Cons:
  "a < b \<Longrightarrow> zip [a ..< b] (x # xs) = (a, x) # zip [Suc a ..< b] xs"
  by (simp add: upt_conv_Cons)

lemma map_comp_eq:
  "f \<circ>\<^sub>m g = case_option None f \<circ> g"
  apply (rule ext)
  apply (case_tac "g x")
  by auto

lemma dom_If_Some:
   "dom (\<lambda>x. if x \<in> S then Some v else f x) = (S \<union> dom f)"
  by (auto split: if_split)

lemma foldl_fun_upd_const:
  "foldl (\<lambda>s x. s(f x := v)) s xs
    = (\<lambda>x. if x \<in> f ` set xs then v else s x)"
  by (induct xs arbitrary: s) auto

lemma foldl_id:
  "foldl (\<lambda>s x. s) s xs = s"
  by (induct xs) auto

lemma SucSucMinus: "2 \<le> n \<Longrightarrow> Suc (Suc (n - 2)) = n" by arith

lemma ball_to_all:
  "(\<And>x. (x \<in> A) = (P x)) \<Longrightarrow> (\<forall>x \<in> A. B x) = (\<forall>x. P x \<longrightarrow> B x)"
  by blast

lemma case_option_If:
  "case_option P (\<lambda>x. Q) v = (if v = None then P else Q)"
  by clarsimp

lemma case_option_If2:
  "case_option P Q v = If (v \<noteq> None) (Q (the v)) P"
  by (simp split: option.split)

lemma if3_fold:
  "(if P then x else if Q then y else x) = (if P \<or> \<not> Q then x else y)"
  by simp

lemma rtrancl_insert:
  assumes x_new: "\<And>y. (x,y) \<notin> R"
  shows "R^* `` insert x S = insert x (R^* `` S)"
proof -
  have "R^* `` insert x S = R^* `` ({x} \<union> S)" by simp
  also
  have "R^* `` ({x} \<union> S) = R^* `` {x} \<union> R^* `` S"
    by (subst Image_Un) simp
  also
  have "R^* `` {x} = {x}"
    by (meson Image_closed_trancl Image_singleton_iff subsetI x_new)
  finally
  show ?thesis by simp
qed

lemma ran_del_subset:
  "y \<in> ran (f (x := None)) \<Longrightarrow> y \<in> ran f"
  by (auto simp: ran_def split: if_split_asm)

lemma trancl_sub_lift:
  assumes sub: "\<And>p p'. (p,p') \<in> r \<Longrightarrow> (p,p') \<in> r'"
  shows "(p,p') \<in> r^+ \<Longrightarrow> (p,p') \<in> r'^+"
  by (fastforce intro: trancl_mono sub)

lemma trancl_step_lift:
  assumes x_step: "\<And>p p'. (p,p') \<in> r' \<Longrightarrow> (p,p') \<in> r \<or> (p = x \<and> p' = y)"
  assumes y_new: "\<And>p'. \<not>(y,p') \<in> r"
  shows "(p,p') \<in> r'^+ \<Longrightarrow> (p,p') \<in> r^+ \<or> ((p,x) \<in> r^+ \<and> p' = y) \<or> (p = x \<and> p' = y)"
  apply (erule trancl_induct)
   apply (drule x_step)
   apply fastforce
  apply (erule disjE)
   apply (drule x_step)
   apply (erule disjE)
    apply (drule trancl_trans, drule r_into_trancl, assumption)
    apply blast
   apply fastforce
  apply (fastforce simp: y_new dest: x_step)
  done

lemma rtrancl_simulate_weak:
  assumes r: "(x,z) \<in> R\<^sup>*"
  assumes s: "\<And>y. (x,y) \<in> R \<Longrightarrow> (y,z) \<in> R\<^sup>* \<Longrightarrow> (x,y) \<in> R' \<and> (y,z) \<in> R'\<^sup>*"
  shows "(x,z) \<in> R'\<^sup>*"
  apply (rule converse_rtranclE[OF r])
   apply simp
  apply (frule (1) s)
  apply clarsimp
  by (rule converse_rtrancl_into_rtrancl)

lemma nat_le_Suc_less_imp:
  "x < y \<Longrightarrow> x \<le> y - Suc 0"
  by arith

lemma list_case_If2:
  "case_list f g xs = If (xs = []) f (g (hd xs) (tl xs))"
  by (simp split: list.split)

lemma length_ineq_not_Nil:
  "length xs > n \<Longrightarrow> xs \<noteq> []"
  "length xs \<ge> n \<Longrightarrow> n \<noteq> 0 \<longrightarrow> xs \<noteq> []"
  "\<not> length xs < n \<Longrightarrow> n \<noteq> 0 \<longrightarrow> xs \<noteq> []"
  "\<not> length xs \<le> n \<Longrightarrow> xs \<noteq> []"
  by auto

lemma numeral_eqs:
  "2 = Suc (Suc 0)"
  "3 = Suc (Suc (Suc 0))"
  "4 = Suc (Suc (Suc (Suc 0)))"
  "5 = Suc (Suc (Suc (Suc (Suc 0))))"
  "6 = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
  by simp+

lemma psubset_singleton:
  "(S \<subset> {x}) = (S = {})"
  by blast

lemma length_takeWhile_ge:
  "length (takeWhile f xs) = n \<Longrightarrow> length xs = n \<or> (length xs > n \<and> \<not> f (xs ! n))"
  by (induct xs arbitrary: n) (auto split: if_split_asm)

lemma length_takeWhile_le:
  "\<not> f (xs ! n) \<Longrightarrow> length (takeWhile f xs) \<le> n"
  by (induct xs arbitrary: n; simp) (case_tac n; simp)

lemma length_takeWhile_gt:
  "n < length (takeWhile f xs)
       \<Longrightarrow> (\<exists>ys zs. length ys = Suc n \<and> xs = ys @ zs \<and> takeWhile f xs = ys @ takeWhile f zs)"
  apply (induct xs arbitrary: n; simp split: if_split_asm)
  apply (case_tac n; simp)
   apply (rule_tac x="[a]" in exI)
   apply simp
  apply (erule meta_allE, drule(1) meta_mp)
  apply clarsimp
  apply (rule_tac x="a # ys" in exI)
  apply simp
  done

lemma hd_drop_conv_nth2:
  "n < length xs \<Longrightarrow> hd (drop n xs) = xs ! n"
  by (rule hd_drop_conv_nth) clarsimp

lemma map_upt_eq_vals_D:
  "\<lbrakk> map f [0 ..< n] = ys; m < length ys \<rbrakk> \<Longrightarrow> f m = ys ! m"
  by clarsimp

lemma length_le_helper:
  "\<lbrakk> n \<le> length xs; n \<noteq> 0 \<rbrakk> \<Longrightarrow> xs \<noteq> [] \<and> n - 1 \<le> length (tl xs)"
  by (cases xs, simp_all)

lemma all_ex_eq_helper:
  "(\<forall>v. (\<exists>v'. v = f v' \<and> P v v') \<longrightarrow> Q v)
      = (\<forall>v'. P (f v') v' \<longrightarrow> Q (f v'))"
  by auto

lemma nat_less_cases':
  "(x::nat) < y \<Longrightarrow> x = y - 1 \<or> x < y - 1"
  by auto

lemma filter_to_shorter_upto:
  "n \<le> m \<Longrightarrow> filter (\<lambda>x. x < n) [0 ..< m] = [0 ..< n]"
  by (induct m) (auto elim: le_SucE)

lemma in_emptyE: "\<lbrakk> A = {}; x \<in> A \<rbrakk> \<Longrightarrow> P" by blast

lemma Ball_emptyI:
  "S = {} \<Longrightarrow> (\<forall>x \<in> S. P x)"
  by simp

lemma allfEI:
  "\<lbrakk> \<forall>x. P x; \<And>x. P (f x) \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> \<forall>x. Q x"
  by fastforce

lemma cart_singleton_empty2:
  "({x} \<times> S = {}) = (S = {})"
  "({} = S \<times> {e}) = (S = {})"
  by auto

lemma cases_simp_conj:
  "((P \<longrightarrow> Q) \<and> (\<not> P \<longrightarrow> Q) \<and> R) = (Q \<and> R)"
  by fastforce

lemma domE :
  "\<lbrakk> x \<in> dom m; \<And>r. \<lbrakk>m x = Some r\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by clarsimp

lemma dom_eqD:
  "\<lbrakk> f x = Some v; dom f = S \<rbrakk> \<Longrightarrow> x \<in> S"
  by clarsimp

lemma exception_set_finite_1:
  "finite {x. P x} \<Longrightarrow> finite {x. (x = y \<longrightarrow> Q x) \<and> P x}"
  by (simp add: Collect_conj_eq)

lemma exception_set_finite_2:
  "finite {x. P x} \<Longrightarrow> finite {x. x \<noteq> y \<longrightarrow> P x}"
  by (simp add: imp_conv_disj)

lemmas exception_set_finite = exception_set_finite_1 exception_set_finite_2

lemma exfEI:
  "\<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q (f x) \<rbrakk> \<Longrightarrow> \<exists>x. Q x"
  by fastforce

lemma Collect_int_vars:
  "{s. P rv s} \<inter> {s. rv = xf s} = {s. P (xf s) s} \<inter> {s. rv = xf s}"
  by auto

lemma if_0_1_eq:
  "((if P then 1 else 0) = (case Q of True \<Rightarrow> of_nat 1 | False \<Rightarrow> of_nat 0)) = (P = Q)"
  by (simp split: if_split bool.split)

lemma modify_map_exists_cte :
  "(\<exists>cte. modify_map m p f p' = Some cte) = (\<exists>cte. m p' = Some cte)"
  by (simp add: modify_map_def)

lemma dom_eqI:
  assumes c1: "\<And>x y. P x = Some y \<Longrightarrow> \<exists>y. Q x = Some y"
  and     c2: "\<And>x y. Q x = Some y \<Longrightarrow> \<exists>y. P x = Some y"
  shows "dom P = dom Q"
  unfolding dom_def by (auto simp: c1 c2)

lemma dvd_reduce_multiple:
  fixes k :: nat
  shows "(k dvd k * m + n) = (k dvd n)"
  by (induct m) (auto simp: add_ac)

lemma image_iff2:
  "inj f \<Longrightarrow> f x \<in> f ` S = (x \<in> S)"
  by (rule inj_image_mem_iff)

lemma map_comp_restrict_map_Some_iff:
  "((g \<circ>\<^sub>m (m |` S)) x = Some y) = ((g \<circ>\<^sub>m m) x = Some y \<and> x \<in> S)"
  by (auto simp add: map_comp_Some_iff restrict_map_Some_iff)

lemma range_subsetD:
  fixes a :: "'a :: order"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; a \<le> b \<rbrakk> \<Longrightarrow> c \<le> a \<and> b \<le> d"
  by simp

lemma case_option_dom:
  "(case f x of None \<Rightarrow> a | Some v \<Rightarrow> b v) = (if x \<in> dom f then b (the (f x)) else a)"
  by (auto split: option.split)

lemma contrapos_imp:
  "P \<longrightarrow> Q \<Longrightarrow> \<not> Q \<longrightarrow> \<not> P"
  by clarsimp

lemma filter_eq_If:
  "distinct xs \<Longrightarrow> filter (\<lambda>v. v = x) xs = (if x \<in> set xs then [x] else [])"
  by (induct xs) auto

lemma (in semigroup_add) foldl_assoc:
shows "foldl op+ (x+y) zs = x + (foldl op+ y zs)"
  by (induct zs arbitrary: y) (simp_all add:add.assoc)

lemma (in monoid_add) foldl_absorb0:
shows "x + (foldl op+ 0 zs) = foldl op+ x zs"
  by (induct zs) (simp_all add:foldl_assoc)

lemma foldl_conv_concat:
  "foldl (op @) xs xss = xs @ concat xss"
proof (induct xss arbitrary: xs)
  case Nil show ?case by simp
next
  interpret monoid_add "op @" "[]" proof qed simp_all
  case Cons then show ?case by (simp add: foldl_absorb0)
qed

lemma foldl_concat_concat:
  "foldl op @ [] (xs @ ys) = foldl op @ [] xs @ foldl op @ [] ys"
  by (simp add: foldl_conv_concat)

lemma foldl_does_nothing:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> f s x = s \<rbrakk> \<Longrightarrow> foldl f s xs = s"
  by (induct xs) auto

lemma foldl_use_filter:
  "\<lbrakk> \<And>v x. \<lbrakk> \<not> g x; x \<in> set xs \<rbrakk> \<Longrightarrow> f v x = v \<rbrakk> \<Longrightarrow> foldl f v xs = foldl f v (filter g xs)"
  by (induct xs arbitrary: v) auto

lemma map_comp_update_lift:
  assumes fv: "f v = Some v'"
  shows "(f \<circ>\<^sub>m (g(ptr \<mapsto> v))) = ((f \<circ>\<^sub>m g)(ptr \<mapsto> v'))"
  by (simp add: fv map_comp_update)

lemma restrict_map_cong:
  assumes sv: "S = S'"
  and     rl: "\<And>p. p \<in> S' \<Longrightarrow> mp p = mp' p"
  shows   "mp |` S = mp' |` S'"
  using expand_restrict_map_eq rl sv by auto

lemma case_option_over_if:
  "case_option P Q (if G then None else Some v)
        = (if G then P else Q v)"
  "case_option P Q (if G then Some v else None)
        = (if G then Q v else P)"
  by (simp split: if_split)+

lemma map_length_cong:
  "\<lbrakk> length xs = length ys; \<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x = g y \<rbrakk>
     \<Longrightarrow> map f xs = map g ys"
  apply atomize
  apply (erule rev_mp, erule list_induct2)
   apply auto
  done

lemma take_min_len:
  "take (min (length xs) n) xs = take n xs"
  by (simp add: min_def)

lemmas interval_empty = atLeastatMost_empty_iff

lemma fold_and_false[simp]:
  "\<not>(fold (op \<and>) xs False)"
  apply clarsimp
  apply (induct xs)
   apply simp
  apply simp
  done

lemma fold_and_true:
  "fold (op \<and>) xs True \<Longrightarrow> \<forall>i < length xs. xs ! i"
  apply clarsimp
  apply (induct xs)
   apply simp
  apply (case_tac "i = 0"; simp)
   apply (case_tac a; simp)
  apply (case_tac a; simp)
  done

lemma fold_or_true[simp]:
  "fold (op \<or>) xs True"
  by (induct xs, simp+)

lemma fold_or_false:
  "\<not>(fold (op \<or>) xs False) \<Longrightarrow> \<forall>i < length xs. \<not>(xs ! i)"
  apply (induct xs, simp+)
  apply (case_tac a, simp+)
  apply (rule allI, case_tac "i = 0", simp+)
  done



section \<open> Take, drop, zip, list_all etc rules \<close>

method two_induct for xs ys =
  ((induct xs arbitrary: ys; simp?), (case_tac ys; simp)?)

lemma map_fst_zip_prefix:
  "map fst (zip xs ys) \<le> xs"
  by (two_induct xs ys)

lemma map_snd_zip_prefix:
  "map snd (zip xs ys) \<le> ys"
  by (two_induct xs ys)

lemma nth_upt_0 [simp]:
  "i < length xs \<Longrightarrow> [0..<length xs] ! i = i"
  by simp

lemma take_insert_nth:
  "i < length xs\<Longrightarrow> insert (xs ! i) (set (take i xs)) = set (take (Suc i) xs)"
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

lemma not_prefixI:
  "\<lbrakk> xs \<noteq> ys; length xs = length ys\<rbrakk> \<Longrightarrow> \<not> xs \<le> ys"
  by (auto elim: prefixE)

lemma map_fst_zip':
  "length xs \<le> length ys \<Longrightarrow> map fst (zip xs ys) = xs"
  by (metis length_map length_zip map_fst_zip_prefix min_absorb1 not_prefixI)

lemma zip_take_triv:
  "n \<ge> length bs \<Longrightarrow> zip (take n as) bs = zip as bs"
  apply (induct bs arbitrary: n as; simp)
  apply (case_tac n; simp)
  apply (case_tac as; simp)
  done

lemma zip_take_triv2:
  "length as \<le> n \<Longrightarrow> zip as (take n bs) = zip as bs"
  apply (induct as arbitrary: n bs; simp)
  apply (case_tac n; simp)
  apply (case_tac bs; simp)
  done

lemma zip_take_length:
  "zip xs (take (length xs) ys) = zip xs ys"
  by (metis order_refl zip_take_triv2)

lemma zip_singleton:
  "ys \<noteq> [] \<Longrightarrow> zip [a] ys = [(a, ys ! 0)]"
  by (case_tac ys, simp_all)

lemma zip_append_singleton:
  "\<lbrakk>i = length xs; length xs < length ys\<rbrakk> \<Longrightarrow> zip (xs @ [a]) ys = (zip xs ys) @ [(a,ys ! i)]"
  by (induct xs; case_tac ys; simp)
     (clarsimp simp: zip_append1 zip_take_length zip_singleton)

lemma ran_map_of_zip:
  "\<lbrakk>length xs = length ys; distinct xs\<rbrakk> \<Longrightarrow> ran (map_of (zip xs ys)) = set ys"
  by (induct rule: list_induct2) auto

lemma ranE:
  "\<lbrakk> v \<in> ran f; \<And>x. f x = Some v \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp: ran_def)

lemma ran_map_option_restrict_eq:
  "\<lbrakk> x \<in> ran (map_option f o g); x \<notin> ran (map_option f o (g |` (- {y}))) \<rbrakk>
        \<Longrightarrow> \<exists>v. g y = Some v \<and> f v = x"
  apply (clarsimp simp: elim!: ranE)
  apply (rename_tac w z)
  apply (case_tac "w = y")
   apply clarsimp
  apply (erule notE, rule_tac a=w in ranI)
  apply (simp add: restrict_map_def)
  done

lemma map_of_zip_range:
  "\<lbrakk>length xs = length ys; distinct xs\<rbrakk> \<Longrightarrow> (\<lambda>x. (the (map_of (zip xs ys) x))) ` set xs = set ys"
  apply (clarsimp simp: image_def)
  apply (subst ran_map_of_zip [symmetric, where xs=xs and ys=ys]; simp?)
  apply (clarsimp simp: ran_def)
  apply (rule equalityI)
   apply clarsimp
   apply (rename_tac x)
   apply (frule_tac x=x in map_of_zip_is_Some; fastforce)
  apply (clarsimp simp: set_zip)
  by (metis domI dom_map_of_zip nth_mem ranE ran_map_of_zip option.sel)

lemma map_zip_fst:
  "length xs = length ys \<Longrightarrow> map (\<lambda>(x, y). f x) (zip xs ys) = map f xs"
  by (two_induct xs ys)

lemma map_zip_fst':
  "length xs \<le> length ys \<Longrightarrow> map (\<lambda>(x, y). f x) (zip xs ys) = map f xs"
  by (metis length_map map_fst_zip' map_zip_fst zip_map_fst_snd)

lemma map_zip_snd:
  "length xs = length ys \<Longrightarrow> map (\<lambda>(x, y). f y) (zip xs ys) = map f ys"
  by (two_induct xs ys)

lemma map_zip_snd':
  "length ys \<le> length xs \<Longrightarrow> map (\<lambda>(x, y). f y) (zip xs ys) = map f ys"
  by (two_induct xs ys)

lemma map_of_zip_tuple_in:
  "\<lbrakk>(x, y) \<in> set (zip xs ys); distinct xs\<rbrakk> \<Longrightarrow> map_of (zip xs ys) x = Some y"
  by (two_induct xs ys) (auto intro: in_set_zipE)

lemma in_set_zip1:
  "(x, y) \<in> set (zip xs ys) \<Longrightarrow> x \<in> set xs"
  by (erule in_set_zipE)

lemma in_set_zip2:
  "(x, y) \<in> set (zip xs ys) \<Longrightarrow> y \<in> set ys"
  by (erule in_set_zipE)

lemma map_zip_snd_take:
  "map (\<lambda>(x, y). f y) (zip xs ys) = map f (take (length xs) ys)"
  apply (subst map_zip_snd' [symmetric, where xs=xs and ys="take (length xs) ys"], simp)
  apply (subst zip_take_length [symmetric], simp)
  done

lemma map_of_zip_is_index:
  "\<lbrakk>length xs = length ys; x \<in> set xs\<rbrakk> \<Longrightarrow> \<exists>i. (map_of (zip xs ys)) x = Some (ys ! i)"
  apply (induct rule: list_induct2; simp)
  apply (rule conjI; clarsimp)
   apply (metis nth_Cons_0)
  apply (metis nth_Cons_Suc)
  done

lemma map_of_zip_take_update:
  "\<lbrakk>i < length xs; length xs \<le> length ys; distinct xs\<rbrakk>
  \<Longrightarrow> map_of (zip (take i xs) ys)(xs ! i \<mapsto> (ys ! i)) = map_of (zip (take (Suc i) xs) ys)"
  apply (rule ext, rename_tac x)
  apply (case_tac "x=xs ! i"; clarsimp)
   apply (rule map_of_is_SomeI[symmetric])
    apply (simp add: map_fst_zip')
   apply (force simp add: set_zip)
  apply (clarsimp simp: take_Suc_conv_app_nth zip_append_singleton map_add_def split: option.splits)
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
  "list_all (\<lambda>x. f x \<longrightarrow> g x) xs = list_all (\<lambda>x. g x) [x\<leftarrow>xs . f x]"
  by (fastforce simp: Ball_set_list_all[symmetric])

lemma list_all_imp_filter2:
  "list_all (\<lambda>x. f x \<longrightarrow> g x) xs = list_all (\<lambda>x. \<not>f x) [x\<leftarrow>xs . (\<lambda>x. \<not>g x) x]"
  by (fastforce simp: Ball_set_list_all[symmetric])

lemma list_all_imp_chain:
  "\<lbrakk>list_all (\<lambda>x. f x \<longrightarrow> g x) xs; list_all (\<lambda>x. f' x \<longrightarrow> f x) xs\<rbrakk>
  \<Longrightarrow>  list_all (\<lambda>x. f' x \<longrightarrow> g x) xs"
  by (clarsimp simp: Ball_set_list_all [symmetric])





lemma inj_Pair:
  "inj_on (Pair x) S"
  by (rule inj_onI, simp)

lemma inj_on_split:
  "inj_on f S \<Longrightarrow> inj_on (\<lambda>x. (z, f x)) S"
  by (auto simp: inj_on_def)

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
  by (induct xs) auto

lemma ball_ran_updI:
  "(\<forall>x \<in> ran m. P x) \<Longrightarrow> P v \<Longrightarrow> (\<forall>x \<in> ran (m (y \<mapsto> v)). P x)"
  by (auto simp add: ran_def)

lemma not_psubset_eq:
  "\<lbrakk> \<not> A \<subset> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> A = B"
  by blast


lemma in_image_op_plus:
  "(x + y \<in> op + x ` S) = ((y :: 'a :: ring) \<in> S)"
  by (simp add: image_def)

lemma insert_subtract_new:
  "x \<notin> S \<Longrightarrow> (insert x S - S) = {x}"
  by auto

lemma zip_is_empty:
  "(zip xs ys = []) = (xs = [] \<or> ys = [])"
  by (cases xs; simp) (cases ys; simp)

lemma minus_Suc_0_lt:
  "a \<noteq> 0 \<Longrightarrow> a - Suc 0 < a"
  by simp

lemma fst_last_zip_upt:
  "zip [0 ..< m] xs \<noteq> [] \<Longrightarrow>
   fst (last (zip [0 ..< m] xs)) = (if length xs < m then length xs - 1 else m - 1)"
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

lemma neq_into_nprefix:
  "\<lbrakk> x \<noteq> take (length x) y \<rbrakk> \<Longrightarrow> \<not> x \<le> y"
  by (clarsimp simp: prefix_def less_eq_list_def)

lemma suffix_eqI:
  "\<lbrakk> suffix xs as; suffix xs bs; length as = length bs;
    take (length as - length xs) as \<le> take (length bs - length xs) bs\<rbrakk> \<Longrightarrow> as = bs"
  by (clarsimp elim!: prefixE suffixE)

lemma suffix_Cons_mem:
  "suffix (x # xs) as \<Longrightarrow> x \<in> set as"
  by (drule suffix_set_subset) simp

lemma distinct_imply_not_in_tail:
  "\<lbrakk> distinct list; suffix (y # ys) list\<rbrakk> \<Longrightarrow> y \<notin> set ys"
  by (clarsimp simp:suffix_def)

lemma list_induct_suffix [case_names Nil Cons]:
  assumes nilr: "P []"
  and    consr: "\<And>x xs. \<lbrakk>P xs; suffix (x # xs) as \<rbrakk> \<Longrightarrow> P (x # xs)"
  shows  "P as"
proof -
  def as' == as

  have "suffix as as'" unfolding as'_def by simp
  then show ?thesis
  proof (induct as)
    case Nil show ?case by fact
  next
    case (Cons x xs)

    show ?case
    proof (rule consr)
      from Cons.prems show "suffix (x # xs) as" unfolding as'_def .
      then have "suffix xs as'" by (auto dest: suffix_ConsD simp: as'_def)
      then show "P xs" using Cons.hyps by simp
    qed
  qed
qed

text \<open>Parallel etc. and lemmas for list prefix\<close>

lemma prefix_induct [consumes 1, case_names Nil Cons]:
  fixes prefix
  assumes np: "prefix \<le> lst"
  and base:   "\<And>xs. P [] xs"
  and rl:     "\<And>x xs y ys. \<lbrakk> x = y; xs \<le> ys; P xs ys \<rbrakk> \<Longrightarrow> P (x#xs) (y#ys)"
  shows "P prefix lst"
  using np
proof (induct prefix arbitrary: lst)
  case Nil show ?case by fact
next
  case (Cons x xs)

  have prem: "(x # xs) \<le> lst" by fact
  then obtain y ys where lv: "lst = y # ys"
    by (rule prefixE, auto)

  have ih: "\<And>lst. xs \<le> lst \<Longrightarrow> P xs lst" by fact

  show ?case using prem
    by (auto simp: lv intro!: rl ih)
qed

lemma not_prefix_cases:
  fixes prefix
  assumes pfx: "\<not> prefix \<le> lst"
  and c1: "\<lbrakk> prefix \<noteq> []; lst = [] \<rbrakk> \<Longrightarrow> R"
  and c2: "\<And>a as x xs. \<lbrakk> prefix = a#as; lst = x#xs; x = a; \<not> as \<le> xs\<rbrakk> \<Longrightarrow> R"
  and c3: "\<And>a as x xs. \<lbrakk> prefix = a#as; lst = x#xs; x \<noteq> a\<rbrakk> \<Longrightarrow> R"
  shows "R"
proof (cases prefix)
  case Nil then show ?thesis using pfx by simp
next
  case (Cons a as)

  have c: "prefix = a#as" by fact

  show ?thesis
  proof (cases lst)
    case Nil then show ?thesis
      by (intro c1, simp add: Cons)
  next
    case (Cons x xs)
    show ?thesis
    proof (cases "x = a")
      case True
      show ?thesis
      proof (intro c2)
        show "\<not> as \<le> xs" using pfx c Cons True
          by simp
      qed fact+
    next
      case False
      show ?thesis by (rule c3) fact+
    qed
  qed
qed

lemma not_prefix_induct [consumes 1, case_names Nil Neq Eq]:
  fixes prefix
  assumes np: "\<not> prefix \<le> lst"
  and base:   "\<And>x xs. P (x#xs) []"
  and r1:     "\<And>x xs y ys. x \<noteq> y \<Longrightarrow> P (x#xs) (y#ys)"
  and r2:     "\<And>x xs y ys. \<lbrakk> x = y; \<not> xs \<le> ys; P xs ys \<rbrakk> \<Longrightarrow> P (x#xs) (y#ys)"
  shows "P prefix lst"
  using np
proof (induct lst arbitrary: prefix)
  case Nil then show ?case
    by (auto simp: neq_Nil_conv elim!: not_prefix_cases intro!: base)
next
  case (Cons y ys)

  have npfx: "\<not> prefix \<le> (y # ys)" by fact
  then obtain x xs where pv: "prefix = x # xs"
    by (rule not_prefix_cases) auto

  have ih: "\<And>prefix. \<not> prefix \<le> ys \<Longrightarrow> P prefix ys" by fact

  show ?case using npfx
    by (simp only: pv) (erule not_prefix_cases, auto intro: r1 r2 ih)
qed

lemma rsubst:
  "\<lbrakk> P s; s = t \<rbrakk> \<Longrightarrow> P t"
  by simp

lemma ex_impE: "((\<exists>x. P x) \<longrightarrow> Q) \<Longrightarrow> P x \<Longrightarrow> Q"
  by blast

end
