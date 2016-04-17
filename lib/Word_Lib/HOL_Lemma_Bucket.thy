(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory HOL_Lemma_Bucket
imports Main
begin

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

(******** GeneralLib ****************)

(* these sometimes crop up in simplified terms and should be blown away *)
lemma exx [iff]: "\<exists>x. x" by blast
lemma ExNot [iff]: "Ex Not" by blast

lemma cases_simp2 [simp]:
  "((\<not> P \<longrightarrow> Q) \<and> (P \<longrightarrow> Q)) = Q"
  by blast

(* FIXME : Should probably be in the simpset, but would cause too much
 * legacy breakage. *)
lemma a_imp_b_imp_b:
  "((a \<longrightarrow> b) \<longrightarrow> b) = (a \<or> b)"
  by blast

(* List stuff *)

lemma length_neq:
  "length as \<noteq> length bs \<Longrightarrow> as \<noteq> bs" by auto

lemma take_neq_length:
  "\<lbrakk> x \<noteq> y; x \<le> length as; y \<le> length bs\<rbrakk> \<Longrightarrow> take x as \<noteq> take y bs"
  by (rule length_neq, simp)

lemma zip_map:
  "zip (map f as) bs = map (\<lambda>(a, b). (f a, b)) (zip as bs)"
proof (induct as arbitrary: bs)
  case Nil thus ?case by simp
next
  case Cons
  thus ?case by (clarsimp simp: zip_Cons1 split: list.split)
qed

lemma eq_concat_lenD:
  "xs = ys @ zs \<Longrightarrow> length xs = length ys + length zs"
  by simp

lemma map_upt_reindex': "map f [a ..< b] = map (\<lambda>n. f (n + a - x)) [x ..< x + b - a]"
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp: add.commute)
  done

lemma map_upt_reindex: "map f [a ..< b] = map (\<lambda>n. f (n + a)) [0 ..< b - a]"
  apply (subst map_upt_reindex' [where x=0])
  apply clarsimp
  done

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

lemma takeWhile_take_has_property:
  "n \<le> length (takeWhile P xs) \<Longrightarrow> \<forall>x \<in> set (take n xs). P x"
  apply (induct xs arbitrary: n)
   apply simp
  apply (simp split: split_if_asm)
  apply (case_tac n, simp_all)
  done

lemma takeWhile_take_has_property_nth:
  "\<lbrakk> n < length (takeWhile P xs) \<rbrakk> \<Longrightarrow> P (xs ! n)"
  apply (induct xs arbitrary: n, simp)
  apply (simp split: split_if_asm)
  apply (case_tac n, simp_all)
  done

lemma takeWhile_replicate:
  "takeWhile f (replicate len x) = (if f x then replicate len x else [])"
  by (induct_tac len) auto

lemma takeWhile_replicate_empty:
  "\<not> f x \<Longrightarrow> takeWhile f (replicate len x) = []"
  by (simp add: takeWhile_replicate)

lemma takeWhile_replicate_id:
  "f x \<Longrightarrow> takeWhile f (replicate len x) = replicate len x"
  by (simp add: takeWhile_replicate)

(* These aren't used, but are generally useful *)

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

  hence "(GREATEST x. P x) = max" unfolding Greatest_def
    by (auto intro: GreatestM_equality)

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

text {* Bits *}

lemma True_notin_set_replicate_conv: "True \<notin> set ls = (ls = replicate (length ls) False)"
  by (induct ls) simp+

lemma Collect_singleton_eqI:
  "(\<And>x. P x = (x = v)) \<Longrightarrow> {x. P x} = {v}"
  apply (subst singleton_conv [symmetric])
  apply (rule Collect_cong)
  apply simp
  done

lemma exEI:
  "\<lbrakk> \<exists>y. P y; \<And>x. P x \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> \<exists>z. Q z"
  apply (erule exE)
  apply (rule_tac x = y in exI)
  apply simp
  done

lemma allEI:
  assumes x: "\<forall>x. P x"
  assumes y: "\<And>x. P x \<Longrightarrow> Q x"
  shows      "\<forall>x. Q x"
  by (rule allI, rule y, rule spec, rule x)

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

lemma ball_reorder: "(\<forall>x \<in> A. \<forall>y \<in> B. P x y) = (\<forall>y \<in> B. \<forall>x \<in> A.  P x y)" by auto

lemma map_id: "map id = id"
  by (rule List.map.id)

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

lemma le_imp_diff_le:
  fixes j :: nat
  shows "j \<le> k \<Longrightarrow> j - n \<le> k" by simp

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
  by (subst image_id' [symmetric], (subst g image_comp)+)
(rule image_cong [OF _ arg_cong [OF r, symmetric]], rule refl)

lemma Collect_image_fun_cong:
  assumes rl: "\<And>a. P a \<Longrightarrow> f a = g a"
  shows   "{f x | x. P x} = {g x | x. P x}"
  apply (rule Collect_cong)
  apply rule
   apply (erule exEI)
   apply (clarsimp simp: rl)
  apply (erule exEI)
  apply (clarsimp simp: rl)
done

lemma inj_on_take:
  shows "inj_on (take n) {x. drop n x = k}"
proof (rule inj_onI)
  fix x y
  assume xv: "x \<in> {x. drop n x = k}"
    and yv: "y \<in> {x. drop n x = k}"
    and tk: "take n x = take n y"

  from xv have "take n x @ k = x"
    apply simp
    apply (erule subst, subst append_take_drop_id)
    apply (rule refl)
    done

  moreover from yv tk have "take n x @ k = y"
    apply simp
    apply (erule subst, subst append_take_drop_id)
    apply (rule refl)
    done

  ultimately show "x = y" by simp
qed

lemma power_sub:
  fixes a :: nat
  assumes lt: "n \<le> m"
  and     av: "0 < a"
  shows "a ^ (m - n) = a ^ m div a ^ n"
proof (subst nat_mult_eq_cancel1 [symmetric])
  show "(0::nat) < a ^ n" using av by simp
next
  from lt obtain q where mv: "n + q = m"
    by (auto simp: le_iff_add)

  have "a ^ n * (a ^ m div a ^ n) = a ^ m"
  proof (subst mult.commute)
    have "a ^ m = (a ^ m div a ^ n) * a ^ n + a ^ m mod a ^ n"
      by (rule  mod_div_equality [symmetric])

    moreover have "a ^ m mod a ^ n = 0"
      by (subst mod_eq_0_iff, rule exI [where x = "a ^ q"],
      (subst power_add [symmetric] mv)+, rule refl)

    ultimately show "(a ^ m div a ^ n) * a ^ n = a ^ m" by simp
  qed

  thus "a ^ n * a ^ (m - n) = a ^ n * (a ^ m div a ^ n)" using lt
    by (simp add: power_add [symmetric])
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
    thus ?thesis
      apply (rule ssubst)
      apply (subst foldr.simps[unfolded o_def])
      apply (subst dom_fun_upd)
      apply (subst Cons.hyps)+
      apply simp
      apply (rule insert_absorb [OF ain])
      done
  next
    case False
    hence "a \<notin> (dom g \<union> set as)" by simp
    hence "dom g \<union> set (a # as) = insert a (dom g \<union> set as)" by simp
    thus ?thesis
      apply (rule ssubst)
      apply (subst foldr.simps[unfolded o_def])
      apply (subst dom_fun_upd)
      apply (subst Cons.hyps)+
      apply simp
      done
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
  "(foldr (\<lambda>p ps. ps(p \<mapsto> f p)) as g) = (\<lambda>x. if x \<in> set as then Some (f x) else g x)"
  apply (rule ext)
  apply (case_tac "x \<in> set as")
   apply (simp add: foldr_upd_app)
  apply (simp add: foldr_upd_app_other)
  done

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
  "\<lbrakk> y = x; x # xs \<noteq> y # ys \<rbrakk> \<Longrightarrow> xs \<noteq> ys" by simp

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

(* Other word lemmas *)

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
  apply (subst nat_add_left_cancel_less [where k = z, symmetric])
  apply (subst add_diff_assoc)
  apply assumption
  apply simp
  done

definition
  strict_part_mono :: "'a set \<Rightarrow> ('a :: order \<Rightarrow> 'b :: order) \<Rightarrow> bool" where
 "strict_part_mono S f \<equiv> \<forall>A\<in>S. \<forall>B\<in>S. A < B \<longrightarrow> f A < f B"

lemma strict_part_mono_by_steps:
  "strict_part_mono {..n :: nat} f
    = (n \<noteq> 0 \<longrightarrow> f (n - 1) < f n \<and> strict_part_mono {.. n - 1} f)"
  apply (cases n)
   apply (simp add: strict_part_mono_def)
  apply (simp add: strict_part_mono_def)
  apply safe
    apply simp
   apply simp
  apply clarsimp
  apply (case_tac "B = Suc nat")
   apply (case_tac "A = nat")
    apply simp
   apply clarsimp
   apply (rule order_less_trans)
    prefer 2
    apply assumption
   apply simp
  apply simp
  done

lemma strict_part_mono_singleton[simp]:
  "strict_part_mono {x} f"
  by (simp add: strict_part_mono_def)

lemma strict_part_mono_lt:
  "\<lbrakk> x < f 0; strict_part_mono {.. n :: nat} f \<rbrakk>
     \<Longrightarrow> \<forall>m \<le> n. x < f m"
  apply (simp add: strict_part_mono_def)
  apply clarsimp
  apply (case_tac m)
   apply simp
  apply (erule order_less_trans)
  apply simp
  done

lemma strict_part_mono_reverseE:
  "\<lbrakk> f n \<le> f m; strict_part_mono {.. N :: nat} f; n \<le> N \<rbrakk> \<Longrightarrow> n \<le> m"
  apply (rule ccontr)
  apply (clarsimp simp: linorder_not_le strict_part_mono_def)
  apply (drule bspec)
   prefer 2
   apply (drule bspec)
    prefer 2
     apply (drule(1) mp)
     apply simp+
  done

lemma take_map_Not:
  "(take n (map Not xs) = take n xs) = (n = 0 \<or> xs = [])"
  apply (cases n, simp_all)
  apply (cases xs, simp_all)
  done

lemma nat_power_0 [simp]:
  "((x::nat) ^ n = 0) = (x = 0 \<and> 0 < n)"
  by (induct n) auto

lemma union_trans:
  assumes SR: "\<And>x y z. \<lbrakk> (x,y) \<in> S; (y,z) \<in> R \<rbrakk> \<Longrightarrow> (x,z) \<in> S^*"
  shows "(R \<union> S)^* = R^* \<union> R^* O S^*"
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule rtrancl_induct)
    apply simp
   apply simp
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
  by (simp split: split_if)

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
  "(if (\<not> P) then T else F) = (if P then F else T)"
  by simp

lemma not_in_domIff:"f x = None = (x \<notin> dom f)"
  by blast

lemma not_in_domD:
  "x \<notin> dom f \<Longrightarrow> f x = None"
  by (simp add:not_in_domIff)

definition
  "graph_of f \<equiv> {(x,y). f x = Some y}"

(* ArchAcc_R.thy:graph_of_None_update line 2021 *)
lemma graph_of_None_update:
  "graph_of (f (p := None)) = graph_of f - {p} \<times> UNIV"
  by (auto simp: graph_of_def split: split_if_asm)

(* ArchAcc_R.thy:graph_of_Some_update line 2023 *)
lemma graph_of_Some_update:
  "graph_of (f (p \<mapsto> v)) = (graph_of f - {p} \<times> UNIV) \<union> {(p,v)}"
  by (auto simp: graph_of_def split: split_if_asm)

(* ArchAcc_R.thy:graph_of_restrict_map line 2568 *)
lemma graph_of_restrict_map:
  "graph_of (m |` S) \<subseteq> graph_of m"
  by (simp add: graph_of_def restrict_map_def subset_iff)

(* Wellformed.thy:graph_ofD line 5613 *)
lemma graph_ofD:
  "(x,y) \<in> graph_of f \<Longrightarrow> f x = Some y"
  by (simp add: graph_of_def)

(* Wellformed.thy:graph_ofI line 5706 *)
lemma graph_ofI:
  "m x = Some y \<Longrightarrow> (x, y) \<in> graph_of m"
  by (simp add: graph_of_def)

lemma graph_of_empty :
  "graph_of empty = {}"
  by (simp add: graph_of_def)

lemma in_set_zip_refl :
  "(x,y) \<in> set (zip xs xs) = (y = x \<and> x \<in> set xs)"
  by (induct xs) auto

lemma map_conv_upd:
  "m v = None \<Longrightarrow> m o (f (x := v)) = (m o f) (x := None)"
  by (rule ext) (clarsimp simp: o_def)

lemma sum_all_ex [simp]:
    "(\<forall>a. x \<noteq> Inl a) = (\<exists>a. x = Inr a)"
    "(\<forall>a. x \<noteq> Inr a) = (\<exists>a. x = Inl a)"
   apply (metis Inr_not_Inl sum.exhaust)
  apply (metis Inl_not_Inr sum.exhaust)
  done

lemma split_distrib: "case_prod (\<lambda>a b. T (f a b)) = (\<lambda>x. T (case_prod (\<lambda>a b. f a b) x))"
  apply (clarsimp simp: split_def)
  done

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
  apply (case_tac a, auto)[1]
  apply (case_tac a, auto)[1]
  done

lemma disjE_L: "\<lbrakk> a \<or> b; a \<Longrightarrow> R; \<lbrakk> \<not> a; b \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by blast

lemma disjE_R: "\<lbrakk> a \<or> b; \<lbrakk> \<not> b; a \<rbrakk> \<Longrightarrow> R; \<lbrakk> b \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by blast

lemma int_max_thms:
    "(a :: int) \<le> max a b"
    "(b :: int) \<le> max a b"
  by (auto simp: max_def)

lemma sgn_negation [simp]: "sgn (-(x::int)) = - sgn x"
  apply (clarsimp simp: sgn_if)
  done

lemma sgn_sgn_nonneg [simp]: "sgn (a :: int) * sgn a \<noteq> -1"
  apply (clarsimp simp: sgn_if)
  done


lemma inj_inj_on:
  "inj f \<Longrightarrow> inj_on f A"
  by (metis injD inj_onI)

lemma ex_eqI:
  "\<lbrakk>\<And>x. f x = g x\<rbrakk> \<Longrightarrow> (\<exists>x. f x) = (\<exists>x. g x)"
  by simp

lemma min_simps [simp]:
  "(a::nat) \<le> b \<Longrightarrow> min b a = a"
  "a \<le> b \<Longrightarrow> min a b = a"
  by (auto simp: min_def)+

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
  assumes aa: "A' \<subseteq> A"
  and     ab: "A \<inter> B = {}"
  shows   "A' \<inter> B = {}"
  using aa ab by auto

lemma disjoint_subset2:
  assumes aa: "B' \<subseteq> B"
  and     ab: "A \<inter> B = {}"
  shows   "A \<inter> B' = {}"
  using aa ab by auto

lemma UN_nth_mem:
  "i < length xs \<Longrightarrow> f (xs ! i) \<subseteq> (\<Union>x\<in>set xs. f x)"
  by (metis UN_upper nth_mem)

lemma Union_equal:
  "f ` A = f ` B \<Longrightarrow> (\<Union>x \<in> A. f x) = (\<Union>x \<in> B. f x)"
  apply (subst Union_image_eq [symmetric])+
  apply simp
  done

lemma UN_Diff_disjoint:
  "i < length xs \<Longrightarrow> (A - (\<Union>x\<in>set xs. f x)) \<inter> f (xs ! i) = {}"
  by (metis Diff_disjoint Int_commute UN_nth_mem disjoint_subset)

lemma image_list_update:
  "f a = f (xs ! i)
  \<Longrightarrow> f ` set (xs [i := a]) = f ` set xs"
  by (metis list_update_id map_update set_map)

lemma Union_list_update_id:
  "f a = f (xs ! i)
  \<Longrightarrow> (\<Union>x\<in>set (xs [i := a]). f x) = (\<Union>x\<in>set xs. f x)"
  apply (rule Union_equal)
  apply (erule image_list_update)
  done

lemma Union_list_update_id':
  "\<lbrakk>i < length xs; \<And>x. g (f x) = g x\<rbrakk>
  \<Longrightarrow> (\<Union>x\<in>set (xs [i := f (xs ! i)]). g x) = (\<Union>x\<in>set xs. g x)"
  by (metis Union_list_update_id)

lemma union_sub:
  "\<lbrakk>B \<subseteq> A; C \<subseteq> B\<rbrakk> \<Longrightarrow> (A - B) \<union> (B - C) = (A - C)"
  by fastforce

lemma insert_sub:
  "x \<in> xs \<Longrightarrow> (insert x (xs - ys)) = (xs - (ys - {x}))"
  by blast

lemma Union_subset:
  "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> (f x) \<subseteq> (g x)\<rbrakk> \<Longrightarrow> (\<Union>x \<in> A. f x) \<subseteq> (\<Union>x \<in> A. g x)"
  by (metis UN_mono order_refl)

lemma UN_sub_empty:
  "\<lbrakk>list_all P xs; \<And>x. P x \<Longrightarrow> f x = g x\<rbrakk>
  \<Longrightarrow> (\<Union>x\<in>set xs. f x) - (\<Union>x\<in>set xs. g x) = {}"
  by (metis Ball_set_list_all Diff_cancel SUP_cong)

(*******************
 * bij_betw rules. *
 *******************)

lemma bij_betw_fun_updI:
  "\<lbrakk>x \<notin> A; y \<notin> B; bij_betw f A B\<rbrakk>
  \<Longrightarrow> bij_betw (f(x := y)) (insert x A) (insert y B)"
  by (clarsimp simp: bij_betw_def fun_upd_image inj_on_fun_updI
              split: split_if_asm)

definition
  "bij_betw_map f A B \<equiv> bij_betw f A (Some ` B)"

lemma bij_betw_map_fun_updI:
  "\<lbrakk>x \<notin> A; y \<notin> B; bij_betw_map f A B\<rbrakk>
  \<Longrightarrow> bij_betw_map (f(x \<mapsto> y)) (insert x A) (insert y B)"
  apply (clarsimp simp: bij_betw_map_def)
  apply (erule bij_betw_fun_updI, clarsimp+)
  done

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


(*
 * Misc
 *)

lemma range_constant [simp]: "range (\<lambda>_. k) = {k}"
  by (clarsimp simp: image_def)

lemma dom_unpack:"dom (map_of (map (\<lambda>x. (f x, g x)) xs)) = set (map (\<lambda>x. f x) xs)"
  by (simp add: dom_map_of_conv_image_fst image_image)

lemma fold_to_disj:"fold op ++ ms a x = Some y \<Longrightarrow> (\<exists>b \<in> set ms. b x = Some y) \<or> a x = Some y"
  apply (induct ms arbitrary:a x y; clarsimp)
  apply blast
  done

lemma fold_ignore1:"a x = Some y \<Longrightarrow> fold op ++ ms a x = Some y"
  by (induct ms arbitrary:a x y; clarsimp)

lemma fold_ignore2:"fold op ++ ms a x = None \<Longrightarrow> a x = None"
  by (metis fold_ignore1 option.collapse)

lemma fold_ignore3:"fold op ++ ms a x = None \<Longrightarrow> (\<forall>b \<in> set ms. b x = None)"
  apply (induct ms arbitrary:a x; clarsimp)
  by (meson fold_ignore2 map_add_None)

lemma fold_ignore4:"b \<in> set ms \<Longrightarrow> b x = Some y \<Longrightarrow> \<exists>y. fold op ++ ms a x = Some y"
  apply (rule ccontr)
  apply (subst (asm) not_ex)
  apply clarsimp
  apply (drule fold_ignore3)
  apply fastforce
  done

lemma dom_unpack2:"dom (fold op ++ ms empty) = \<Union>(set (map dom ms))"
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
  apply (rename_tac a ms x xa y)
  apply (erule_tac y=y in fold_ignore4; clarsimp)
  done

lemma fold_ignore5:"fold op ++ ms a x = Some y \<Longrightarrow> a x = Some y \<or> (\<exists>b \<in> set ms. b x = Some y)"
  apply (induct ms arbitrary:a x y; clarsimp)
  apply blast
  done

lemma dom_inter_nothing:"dom f \<inter> dom g = {} \<Longrightarrow> \<forall>x. f x = None \<or> g x = None"
  by auto

lemma fold_ignore6:"f x = None \<Longrightarrow> fold op ++ ms f x = fold op ++ ms empty x"
  apply (induct ms arbitrary:f x; clarsimp simp:map_add_def)
  by (metis (no_types, lifting) fold_ignore1 option.collapse option.simps(4))

lemma fold_ignore7:"m x = m' x \<Longrightarrow> fold op ++ ms m x = fold op ++ ms m' x"
  apply (case_tac "m x")
   apply (frule_tac ms=ms in fold_ignore6)
   apply (cut_tac f=m' and ms=ms and x=x in fold_ignore6)
    apply clarsimp+
  apply (rename_tac a)
  apply (cut_tac ms=ms and a=m and x=x and y=a in fold_ignore1, clarsimp)
  apply (cut_tac ms=ms and a=m' and x=x and y=a in fold_ignore1; clarsimp)
  done

lemma fold_ignore8:"fold op ++ ms [x \<mapsto> y] = (fold op ++ ms empty)(x \<mapsto> y)"
  apply (rule ext)
  apply (rename_tac xa)
  apply (case_tac "xa = x")
   apply clarsimp
   apply (rule fold_ignore1)
   apply clarsimp
  apply (subst fold_ignore6)
   apply clarsimp+
  done

lemma fold_ignore9:"\<lbrakk>fold op ++ ms [x \<mapsto> y] x' = Some z; x = x'\<rbrakk> \<Longrightarrow> y = z"
  apply (subst (asm) fold_ignore8)
  apply clarsimp
  done

lemma fold_to_map_of:"fold op ++ (map (\<lambda>x. [f x \<mapsto> g x]) xs) empty = map_of (map (\<lambda>x. (f x, g x)) xs)"
  apply (rule ext)
  apply (rename_tac x)
  apply (case_tac "fold op ++ (map (\<lambda>x. [f x \<mapsto> g x]) xs) Map.empty x")
   apply clarsimp
   apply (drule fold_ignore3)
   apply (clarsimp split:split_if_asm)
   apply (rule sym)
   apply (subst map_of_eq_None_iff)
   apply clarsimp
   apply (rename_tac xa)
   apply (erule_tac x=xa in ballE; clarsimp)
  apply clarsimp
  apply (frule fold_ignore5; clarsimp split:split_if_asm)
  apply (subst map_add_map_of_foldr[where m=empty, simplified])
  apply (induct xs arbitrary:f g; clarsimp split:split_if)
  apply (rule conjI; clarsimp)
   apply (drule fold_ignore9; clarsimp)
  apply (cut_tac ms="map (\<lambda>x. [f x \<mapsto> g x]) xs" and f="[f a \<mapsto> g a]" and x="f b" in fold_ignore6, clarsimp)
  apply clarsimp
  apply (erule disjE; clarsimp)
  done



lemma if_n_0_0:
  "((if P then n else 0) \<noteq> 0) = (P \<and> n \<noteq> 0)"
  by (simp split: split_if)

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
  apply clarsimp
  apply (subgoal_tac "(f (g x)) = (f \<circ> g) x")
   apply simp
  apply (simp (no_asm))
  done

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
  apply (rule ext)
  apply clarsimp
  apply (case_tac "g xa")
   apply simp
  apply simp
  done

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
  by (rule ext)
     (simp add: modify_map_def map_option_case com split: option.splits)

lemma modify_map_dom :
  "dom (modify_map m p f) = dom m"
  unfolding modify_map_def
  apply (cases "m p")
   apply simp
   apply (simp add: dom_def)
  apply simp
  apply (rule insert_absorb)
  apply (simp add: dom_def)
  done

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
  apply (erule order_less_le_trans)
  apply simp
  done

lemma neg_rtranclI:
  "\<lbrakk> x \<noteq> y; (x, y) \<notin> R\<^sup>+ \<rbrakk> \<Longrightarrow> (x, y) \<notin> R\<^sup>*"
  apply (erule contrapos_nn)
  apply (drule rtranclD)
  apply simp
  done

lemma neg_rtrancl_into_trancl:
  "\<not> (x, y) \<in> R\<^sup>* \<Longrightarrow> \<not> (x, y) \<in> R\<^sup>+"
  by (erule contrapos_nn, erule trancl_into_rtrancl)

lemma set_neqI:
  "\<lbrakk> x \<in> S; x \<notin> S' \<rbrakk> \<Longrightarrow> S \<noteq> S'"
  by clarsimp

lemma set_pair_UN:
  "{x. P x} = UNION {xa. \<exists>xb. P (xa, xb)} (\<lambda>xa. {xa} \<times> {xb. P (xa, xb)})"
  apply safe
  apply (rule_tac a=a in UN_I)
   apply blast+
  done

lemma singleton_elemD:
  "S = {x} \<Longrightarrow> x \<in> S"
  by simp

lemma singleton_eqD: "A = {x} \<Longrightarrow> x \<in> A" by blast

lemma ball_ran_fun_updI:
  "\<lbrakk> \<forall>v \<in> ran m. P v; \<forall>v. y = Some v \<longrightarrow> P v \<rbrakk>
        \<Longrightarrow> \<forall>v \<in> ran (m (x := y)). P v"
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
  apply (erule not_singletonE)
   apply clarsimp
  apply (case_tac "p = p'")
   apply fastforce
  apply fastforce
  done

lemma ball_ran_modify_map_eq:
  "\<lbrakk> \<forall>v. m x = Some v \<longrightarrow> P (f v) = P v \<rbrakk>
        \<Longrightarrow> (\<forall>v \<in> ran (modify_map m x f). P v) = (\<forall>v \<in> ran m. P v)"
  apply (simp add: ball_ran_eq)
  apply (rule iff_allI)
  apply (auto simp: modify_map_def)
  done

lemma disj_imp: "(P \<or> Q) = (\<not>P \<longrightarrow> Q)" by blast

lemma eq_singleton_redux:
  "\<lbrakk> S = {x} \<rbrakk> \<Longrightarrow> x \<in> S"
  by simp

lemma if_eq_elem_helperE:
  "\<lbrakk> x \<in> (if P then S else S');
    \<lbrakk> P;   x \<in> S  \<rbrakk> \<Longrightarrow> a = b;
    \<lbrakk> \<not> P; x \<in> S' \<rbrakk> \<Longrightarrow> a = c
   \<rbrakk> \<Longrightarrow> a = (if P then b else c)"
  by fastforce

lemma if_option_Some :
  "((if P then None else Some x) = Some y) = (\<not>P \<and> x = y)"
  by simp

lemma insert_minus_eq:
  "x \<notin> A \<Longrightarrow> A - S = (A - (S - {x}))"
  by auto

lemma modify_map_K_D:
  "modify_map m p (\<lambda>x. y) p' = Some v \<Longrightarrow> (m (p \<mapsto> y)) p' = Some v"
  by (simp add: modify_map_def split: split_if_asm)

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
  apply (subst Collect_conj_eq [symmetric])
  apply (simp add: disjoint_iff_not_equal)
  apply rule
  apply (drule_tac x = x in spec)
  apply clarsimp
  apply (drule (1) bspec)
  apply simp
  done

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
  "dom (\<lambda>x. if P x then None else f x)
     = dom f - {x. P x}"
  by (simp add: dom_def, fastforce)

lemma restrict_map_Some_iff:
  "((m |` S) x = Some y) = (m x = Some y \<and> x \<in> S)"
  by (cases "x \<in> S", simp_all)

lemma context_case_bools:
  "\<lbrakk> \<And>v. P v \<Longrightarrow> R v; \<lbrakk> \<not> P v; \<And>v. P v \<Longrightarrow> R v \<rbrakk> \<Longrightarrow> R v \<rbrakk> \<Longrightarrow> R v"
  by (cases "P v", simp_all)

lemma inj_on_fun_upd_strongerI:
  "\<lbrakk>inj_on f A; y \<notin> f ` (A - {x})\<rbrakk> \<Longrightarrow> inj_on (f(x := y)) A"
  apply (simp add: inj_on_def)
  apply blast
  done

lemma less_handy_casesE:
  "\<lbrakk> m < n; m = 0 \<Longrightarrow> R;
     \<And>m' n'. \<lbrakk> n = Suc n'; m = Suc m'; m < n \<rbrakk> \<Longrightarrow> R \<rbrakk>
     \<Longrightarrow> R"
  apply (case_tac n, simp_all)
  apply (case_tac m, simp_all)
  done

lemma subset_drop_Diff_strg:
  "(A \<subseteq> C) \<longrightarrow> (A - B \<subseteq> C)"
  by blast

lemma inj_case_bool:
  "inj (case_bool a b) = (a \<noteq> b)"
  by (auto dest: inj_onD[where x=True and y=False]
          intro: inj_onI split: bool.split_asm)

lemma zip_map2:
  "zip as (map f bs) = map (\<lambda>(a, b). (a, f b)) (zip as bs)"
  apply (induct bs arbitrary: as)
   apply simp
  apply (case_tac as)
   apply simp
  apply simp
  done

lemma zip_same: "zip xs xs = map (\<lambda>v. (v, v)) xs"
  by (induct xs, simp+)

lemma foldl_fun_upd:
  "foldl (\<lambda>s r. s (r := g r)) f rs
     = (\<lambda>x. if x \<in> set rs then g x else f x)"
  apply (induct rs arbitrary: f)
   apply simp
  apply (auto simp: fun_eq_iff split: split_if)
  done

lemma all_rv_choice_fn_eq_pred:
  "\<lbrakk> \<And>rv. P rv \<Longrightarrow> \<exists>fn. f rv = g fn \<rbrakk>
    \<Longrightarrow> \<exists>fn. \<forall>rv. P rv \<longrightarrow> f rv = g (fn rv)"
  apply (rule_tac x="\<lambda>rv. SOME h. f rv = g h" in exI)
  apply (clarsimp split: split_if)
  apply (erule meta_allE, drule(1) meta_mp, elim exE)
  apply (erule someI)
  done

lemma ex_const_function:
  "\<exists>f. \<forall>s. f (f' s) = v"
  by force

lemma if_Const_helper:
  "If P (Con x) (Con y) = Con (If P x y)"
  by (simp split: split_if)

lemmas if_Some_helper = if_Const_helper[where Con=Some]

lemma expand_restrict_map_eq:
  "(m |` S = m' |` S) = (\<forall>x. x \<in> S \<longrightarrow> m x = m' x)"
  by (simp add: fun_eq_iff restrict_map_def split: split_if)


lemma disj_imp_rhs:
  "(P \<Longrightarrow> Q) \<Longrightarrow> (P \<or> Q) = Q"
  by blast

lemma remove1_filter:
  "distinct xs \<Longrightarrow> remove1 x xs = filter (\<lambda>y. x \<noteq> y) xs"
  apply (induct xs)
   apply simp
  apply clarsimp
  apply (rule sym, rule filter_True)
  apply clarsimp
  done

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
  apply (rule disjointI)
  apply clarsimp
  apply (drule (1) rl)
  apply auto
  done

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
  (x, y) \<in> set bs \<Longrightarrow> R\<rbrakk>
  \<Longrightarrow> R" by auto

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
  "(case xs of [] \<Rightarrow> P | _ \<Rightarrow> Q)
    = (if xs = [] then P else Q)"
  by (clarsimp simp: neq_Nil_conv)

lemma remove1_Nil_in_set:
  "\<lbrakk> remove1 x xs = []; xs \<noteq> [] \<rbrakk> \<Longrightarrow> x \<in> set xs"
  by (induct xs) (auto split: split_if_asm)

lemma remove1_empty:
  "(remove1 v xs = []) = (xs = [v] \<or> xs = [])"
  by (cases xs, simp_all)

lemma set_remove1:
  "x \<in> set (remove1 y xs) \<Longrightarrow> x \<in> set xs"
  apply (induct xs)
   apply simp
  apply (case_tac "y = a")
   apply clarsimp+
  done

lemma If_rearrage:
  "(if P then if Q then x else y else z)
     = (if P \<and> Q then x else if P then y else z)"
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
  "(case r of Inl a \<Rightarrow> True | Inr b \<Rightarrow> f b)
  = (\<forall>b. r = Inr b \<longrightarrow> f b)"
  by (cases r) auto

lemma sym_ex_elim:
  "F x = y \<Longrightarrow> \<exists>x. y = F x"
  by auto

lemma tl_drop_1 :
  "tl xs = drop 1 xs"
  by (simp add: drop_Suc)

lemma upt_lhs_sub_map:
  "[x ..< y] = map (op + x) [0 ..< y - x]"
  apply (induct y)
   apply simp
  apply (clarsimp simp: Suc_diff_le)
  done

lemma upto_0_to_4:
  "[0..<4] = 0 # [1..<4]"
  apply (subst upt_rec)
  apply simp
  done

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
  apply (simp add: inj_on_def)
  apply blast
  done

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
  apply (erule meta_mp)
  apply (rule Max_in)
   apply simp
  apply assumption
  done

lemma Min_prop:
  "\<lbrakk> Min S \<in> S \<Longrightarrow> P (Min S); (S :: ('a :: {finite, linorder}) set) \<noteq> {} \<rbrakk> \<Longrightarrow> P (Min S)"
  apply (erule meta_mp)
  apply (rule Min_in)
   apply simp
  apply assumption
  done

lemma findSomeD:
  "find P xs = Some x \<Longrightarrow> P x \<and> x \<in> set xs"
  by (induct xs) (auto split: split_if_asm)

lemma findNoneD:
  "find P xs = None \<Longrightarrow> \<forall>x \<in> set xs. \<not>P x"
  by (induct xs) (auto split: split_if_asm)

lemma dom_upd:
  "dom (\<lambda>x. if x = y then None else f x) = dom f - {y}"
  by (rule set_eqI) (auto split: split_if_asm)

lemma ran_upd:
  "\<lbrakk> inj_on f (dom f); f y = Some z \<rbrakk> \<Longrightarrow> ran (\<lambda>x. if x = y then None else f x) = ran f - {z}"
  apply (rule set_eqI)
  apply (unfold ran_def)
  apply simp
  apply (rule iffI)
   apply clarsimp
   apply (rule conjI, blast)
   apply clarsimp
   apply (drule_tac x=a and y=y in inj_onD, simp)
     apply blast
    apply blast
   apply simp
  apply clarsimp
  apply (rule_tac x=a in exI)
  apply clarsimp
  done

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
  apply (drule_tac f=f in is_inv_SomeD, assumption)
  apply simp
  done

lemma ran_upd':
  "\<lbrakk>inj_on f (dom f); f y = Some z\<rbrakk>
  \<Longrightarrow> ran (f (y := None)) = ran f - {z}"
  apply (drule (1) ran_upd)
  apply (simp add: ran_def)
  done

lemma is_inv_None_upd:
  "\<lbrakk> is_inv f g; g x = Some y\<rbrakk> \<Longrightarrow> is_inv (f(y := None)) (g(x := None))"
  apply (subst is_inv_def)
  apply (clarsimp simp add: dom_upd)
  apply (drule is_inv_SomeD, erule is_inv_com)
  apply (frule is_inv_inj)
  apply (simp add: ran_upd')
  apply (rule conjI)
   apply (simp add: is_inv_def)
  apply (drule (1) is_inv_SomeD)
  apply (clarsimp simp: is_inv_def)
  done

lemma is_inv_inj2:
  "is_inv f g \<Longrightarrow> inj_on g (dom g)"
  apply (drule is_inv_com)
  apply (erule is_inv_inj)
  done

lemma range_convergence1:
  "\<lbrakk> \<forall>z. x < z \<and> z \<le> y \<longrightarrow> P z; \<forall>z > y. P (z :: 'a :: linorder) \<rbrakk>
     \<Longrightarrow> \<forall>z > x. P z"
  apply clarsimp
  apply (case_tac "z \<le> y")
   apply simp
  apply (simp add: linorder_not_le)
  done

lemma range_convergence2:
  "\<lbrakk> \<forall>z. x < z \<and> z \<le> y \<longrightarrow> P z; \<forall>z. z > y \<and> z < w \<longrightarrow> P (z :: 'a :: linorder) \<rbrakk>
     \<Longrightarrow> \<forall>z. z > x \<and> z < w \<longrightarrow> P z"
  apply (cut_tac range_convergence1[where P="\<lambda>z. z < w \<longrightarrow> P z" and x=x and y=y])
    apply simp
   apply simp
  apply simp
  done

lemma zip_upt_Cons:
  "a < b \<Longrightarrow> zip [a ..< b] (x # xs)
        = (a, x) # zip [Suc a ..< b] xs"
  by (simp add: upt_conv_Cons)

lemma map_comp_eq:
  "(f \<circ>\<^sub>m g) = (case_option None f \<circ> g)"
  apply (rule ext)
  apply (case_tac "g x")
   apply simp
  apply simp
  done

lemma dom_If_Some:
   "dom (\<lambda>x. if x \<in> S then Some v else f x) = (S \<union> dom f)"
  by (auto split: split_if)

lemma foldl_fun_upd_const:
  "foldl (\<lambda>s x. s(f x := v)) s xs
    = (\<lambda>x. if x \<in> f ` set xs then v else s x)"
  apply (induct xs arbitrary: s)
   apply simp
  apply (rule ext, simp)
  done

lemma foldl_id:
  "foldl (\<lambda>s x. s) s xs = s"
  apply (induct xs)
   apply simp
  apply simp
  done

lemma SucSucMinus: "2 \<le> n \<Longrightarrow> Suc (Suc (n - 2)) = n" by arith

lemma ball_to_all:
  "(\<And>x. (x \<in> A) = (P x)) \<Longrightarrow> (\<forall>x \<in> A. B x) = (\<forall>x. P x \<longrightarrow> B x)"
  by blast

lemma if_apply_def2:
  "(if P then F else G) = (\<lambda>x. (P \<longrightarrow> F x) \<and> (\<not> P \<longrightarrow> G x))"
  by simp

lemma case_bool_If:
  "case_bool P Q b = (if b then P else Q)"
  by simp

lemma case_option_If:
  "case_option P (\<lambda>x. Q) v = (if v = None then P else Q)"
  by clarsimp

lemma case_option_If2:
  "case_option P Q v = If (v \<noteq> None) (Q (the v)) P"
  by (simp split: option.split)

lemma if3_fold:
  "(if P then x else if Q then y else x)
     = (if P \<or> \<not> Q then x else y)"
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
    apply (clarsimp simp: Image_singleton)
    apply (rule set_eqI, clarsimp)
    apply (rule iffI)
     apply (drule rtranclD)
     apply (erule disjE, simp)
     apply clarsimp
     apply (drule tranclD)
     apply (clarsimp simp: x_new)
    apply fastforce
    done
  finally
  show ?thesis by simp
qed

lemma ran_del_subset:
  "y \<in> ran (f (x := None)) \<Longrightarrow> y \<in> ran f"
  by (auto simp: ran_def split: split_if_asm)

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
   apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (drule x_step)
   apply (erule disjE)
    apply (simp add: y_new)
   apply simp
  apply clarsimp
  apply (drule x_step)
  apply (simp add: y_new)
  done

lemma sum_to_zero:
  "(a :: 'a :: ring) + b = 0 \<Longrightarrow> a = (- b)"
  by (drule arg_cong[where f="\<lambda> x. x - a"], simp)

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
  "length (takeWhile f xs) = n
     \<Longrightarrow> length xs = n \<or> (length xs > n \<and> \<not> f (xs ! n))"
  apply (induct xs arbitrary: n)
   apply simp
  apply (simp split: split_if_asm)
  apply (case_tac n, simp_all)
  done

lemma length_takeWhile_le:
  "\<not> f (xs ! n) \<Longrightarrow>
     length (takeWhile f xs) \<le> n"
  apply (induct xs arbitrary: n)
   apply simp
  apply (clarsimp split: split_if)
  apply (case_tac n, simp_all)
  done

lemma length_takeWhile_gt:
  "n < length (takeWhile f xs)
       \<Longrightarrow> (\<exists>ys zs. length ys = Suc n \<and> xs = ys @ zs \<and> takeWhile f xs = ys @ takeWhile f zs)"
  apply (induct xs arbitrary: n)
   apply simp
  apply (simp split: split_if_asm)
  apply (case_tac n, simp_all)
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
  apply (induct m)
   apply simp
  apply clarsimp
  apply (erule le_SucE)
   apply simp
  apply simp
  done

lemma in_emptyE: "\<lbrakk> A = {}; x \<in> A \<rbrakk> \<Longrightarrow> P" by blast

lemma Ball_emptyI:
  "S = {} \<Longrightarrow> (\<forall>x \<in> S. P x)"
  by simp

lemma allfEI:
  "\<lbrakk> \<forall>x. P x; \<And>x. P (f x) \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> \<forall>x. Q x"
  by fastforce

lemma arith_is_1:
  "\<lbrakk> x \<le> Suc 0; x > 0 \<rbrakk> \<Longrightarrow> x = 1"
  by arith

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

lemma exception_set_finite:
  "finite {x. P x} \<Longrightarrow> finite {x. (x = y \<longrightarrow> Q x) \<and> P x}"
  "finite {x. P x} \<Longrightarrow> finite {x. x \<noteq> y \<longrightarrow> P x}"
   apply (simp add: Collect_conj_eq)
  apply (subst imp_conv_disj, subst Collect_disj_eq)
  apply simp
  done

lemma exfEI:
  "\<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q (f x) \<rbrakk> \<Longrightarrow> \<exists>x. Q x"
  by fastforce

lemma if_f:
  "(if a then f b else f c) = f (if a then b else c)"
  by simp

lemma interval_empty:
  "({m..n} = {}) = (\<not> m \<le> (n::'a::order))"
  by auto

lemma Collect_int_vars:
  "{s. P rv s} \<inter> {s. rv = xf s} = {s. P (xf s) s} \<inter> {s. rv = xf s}"
  by auto

lemma if_0_1_eq:
  "((if P then 1 else 0) = (case Q of True \<Rightarrow> of_nat 1 | False \<Rightarrow> of_nat 0)) = (P = Q)"
  by (simp add: case_bool_If split: split_if)

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

lemma image_iff:
  "inj f \<Longrightarrow> f x \<in> f ` S = (x \<in> S)"
  by (rule inj_image_mem_iff)

lemma map_comp_restrict_map_Some_iff:
  "((g \<circ>\<^sub>m (m |` S)) x = Some y) = ((g \<circ>\<^sub>m m) x = Some y \<and> x \<in> S)"
  by (auto simp add: map_comp_Some_iff restrict_map_Some_iff)

lemma range_subsetD:
  fixes a :: "'a :: order"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; a \<le> b \<rbrakk> \<Longrightarrow> c \<le> a \<and> b \<le> d"
  apply (rule conjI)
   apply (drule subsetD [where c = a])
    apply simp
   apply simp
  apply (drule subsetD [where c = b])
   apply simp
  apply simp
  done

lemma case_option_dom:
  "(case f x of None \<Rightarrow> a | Some v \<Rightarrow> b v)
      = (if x \<in> dom f then b (the (f x)) else a)"
  by (auto split: split_if option.split)

lemma contrapos_imp:
  "P \<longrightarrow> Q \<Longrightarrow> \<not> Q \<longrightarrow> \<not> P"
  by clarsimp

lemma filter_eq_If:
  "distinct xs \<Longrightarrow> filter (\<lambda>v. v = x) xs = (if x \<in> set xs then [x] else [])"
  apply (induct xs)
   apply simp
  apply (clarsimp split: split_if)
  done

(*FIXME: isabelle-2012 *)
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
  by (induct xs, simp_all)

lemma foldl_use_filter:
  "\<lbrakk> \<And>v x. \<lbrakk> \<not> g x; x \<in> set xs \<rbrakk> \<Longrightarrow> f v x = v \<rbrakk>
     \<Longrightarrow>
    foldl f v xs = foldl f v (filter g xs)"
  apply (induct xs arbitrary: v)
   apply simp
  apply (simp split: split_if)
  done

lemma upt_add_eq_append':
  assumes "i \<le> j" and "j \<le> k"
  shows "[i..<k] = [i..<j] @ [j..<k]"
  using assms le_Suc_ex upt_add_eq_append by blast

lemma split_upt_on_n:
  "n < m \<Longrightarrow> [0 ..< m] = [0 ..< n] @ [n] @ [Suc n ..< m]"
  by (metis append_Cons append_Nil less_Suc_eq_le less_imp_le_nat upt_add_eq_append'
            upt_rec zero_less_Suc)

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
  by (simp split: split_if)+

end
