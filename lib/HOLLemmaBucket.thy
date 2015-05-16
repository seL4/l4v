(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory HOLLemmaBucket
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

lemma ranE:
  "\<lbrakk> v \<in> ran f; \<And>x. f x = Some v \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp: ran_def)

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
proof (cases b)
  case 0 thus ?thesis using ab by auto
next
  case (Suc n)
  thus ?thesis using ab
    apply (simp add: upt_conv_Cons)
    apply rule
    apply (rule arg_cong [where f = f])
    apply simp
    done
qed

lemma le_imp_diff_le:
  fixes j :: nat
  shows "j \<le> k \<Longrightarrow> j - n \<le> k" by simp

lemma image_Collect2:
  "split f ` {x. P (fst x) (snd x)} = {f x y |x y. P x y}"
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

definition
  "bl_pad_to bl sz \<equiv> bl @ (replicate (sz - length bl) False)"

lemma bl_pad_to_length:
  assumes lbl: "length bl \<le> sz"
  shows   "length (bl_pad_to bl sz) = sz"
  using lbl by (simp add: bl_pad_to_def)

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

lemma ex_with_length:
  "\<exists>x. length x = n"
  apply (rule exI[where x="replicate n arbitrary"])
  apply simp
  done

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

lemma not_in_domD:
  "x \<notin> dom f \<Longrightarrow> f x = None"
  by auto

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

lemma split_distrib: "split (\<lambda>a b. T (f a b)) = (\<lambda>x. T (split (\<lambda>a b. f a b) x))"
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

end
