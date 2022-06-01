(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Many_More
  imports
    Main
    "HOL-Library.Word"
    More_Word
    Even_More_List
begin

lemma nat_less_mult_monoish: "\<lbrakk> a < b; c < (d :: nat) \<rbrakk> \<Longrightarrow> (a + 1) * (c + 1) <= b * d"
  apply (drule Suc_leI)+
  apply (drule(1) mult_le_mono)
  apply simp
  done

context
  includes bit_operations_syntax
begin

lemma if_and_helper:
  "(If x v v') AND v'' = If x (v AND v'') (v' AND v'')"
  by (rule if_distrib)

end

lemma eq_eqI:
  "a = b \<Longrightarrow> (a = x) = (b = x)"
  by simp

lemma map2_Cons_2_3:
  "(map2 f xs (y # ys) = (z # zs)) = (\<exists>x xs'. xs = x # xs' \<and> f x y = z \<and> map2 f xs' ys = zs)"
  by (case_tac xs, simp_all)

lemma map2_xor_replicate_False:
  "map2 (\<lambda>x y. x \<longleftrightarrow> \<not> y) xs (replicate n False) = take n xs"
  apply (induct xs arbitrary: n, simp)
  apply (case_tac n; simp)
  done

lemma plus_Collect_helper:
  "(+) x ` {xa. P (xa :: 'a :: len word)} = {xa. P (xa - x)}"
  by (fastforce simp add: image_def)

lemma plus_Collect_helper2:
  "(+) (- x) ` {xa. P (xa :: 'a :: len word)} = {xa. P (x + xa)}"
  using plus_Collect_helper [of "- x" P] by (simp add: ac_simps)

lemma range_subset_eq2:
  "{a :: 'a :: len word .. b} \<noteq> {} \<Longrightarrow> ({a .. b} \<subseteq> {c .. d}) = (c \<le> a \<and> b \<le> d)"
  by simp

lemma nat_mod_power_lem:
  fixes a :: nat
  shows "1 < a \<Longrightarrow> a ^ n mod a ^ m = (if m \<le> n then 0 else a ^ n)"
  apply (clarsimp)
  apply (clarsimp simp add: le_iff_add power_add)
  done

lemma i_hate_words_helper:
  "i \<le> (j - k :: nat) \<Longrightarrow> i \<le> j"
  by simp

lemma i_hate_words:
  "unat (a :: 'a word) \<le> unat (b :: 'a :: len word) - Suc 0
    \<Longrightarrow> a \<noteq> -1"
  apply (frule i_hate_words_helper)
  apply (subst(asm) word_le_nat_alt[symmetric])
  apply (clarsimp simp only: word_minus_one_le)
  apply (simp only: linorder_not_less[symmetric])
  apply (erule notE)
  apply (rule diff_Suc_less)
  apply (subst neq0_conv[symmetric])
  apply (subst unat_eq_0)
  apply (rule notI, drule arg_cong[where f="(+) 1"])
  apply simp
  done

lemma If_eq_obvious:
  "x \<noteq> z \<Longrightarrow> ((if P then x else y) = z) = (\<not> P \<and> y = z)"
  by simp

lemma Some_to_the:
  "v = Some x \<Longrightarrow> x = the v"
  by simp

lemma dom_if_Some:
  "dom (\<lambda>x. if P x then Some (f x) else g x) = {x. P x} \<union> dom g"
  by fastforce

lemma dom_insert_absorb:
  "x \<in> dom f \<Longrightarrow> insert x (dom f) = dom f"
  by (fact insert_absorb)

lemma emptyE2:
  "\<lbrakk> S = {}; x \<in> S \<rbrakk> \<Longrightarrow> P"
  by simp

lemma ptr_add_image_multI:
  "\<lbrakk> \<And>x y. (x * val = y * val') = (x * val'' = y); x * val'' \<in> S \<rbrakk> \<Longrightarrow>
     ptr_add ptr (x * val) \<in> (\<lambda>p. ptr_add ptr (p * val')) ` S"
  by (auto simp add: image_iff) metis

lemmas map_prod_split_imageI'
  = map_prod_imageI[where f="case_prod f" and g="case_prod g"
                    and a="(a, b)" and b="(c, d)" for a b c d f g]
lemmas map_prod_split_imageI = map_prod_split_imageI'[simplified]

lemma dom_if:
  "dom (\<lambda>a. if a \<in> addrs then Some (f a) else g a)  = addrs \<union> dom g"
  by (auto simp: dom_def split: if_split)

lemmas arg_cong_Not = arg_cong [where f=Not]

lemma drop_append_miracle:
  "n = length xs \<Longrightarrow> drop n (xs @ ys) = ys"
  by simp

lemma foldr_does_nothing_to_xf:
  "\<lbrakk> \<And>x s. x \<in> set xs \<Longrightarrow> xf (f x s) = xf s \<rbrakk> \<Longrightarrow> xf (foldr f xs s) = xf s"
  by (induct xs, simp_all)

lemma mod_mod_power_int:
  fixes k :: int
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
  by (fact mod_exp_eq)

lemma le_step_down_nat:"\<lbrakk>(i::nat) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma le_step_down_int:"\<lbrakk>(i::int) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma replicate_numeral [simp]: "replicate (numeral k) x = x # replicate (pred_numeral k) x"
  by (simp add: numeral_eq_Suc)

lemma list_exhaust_size_gt0:
  assumes "\<And>a list. y = a # list \<Longrightarrow> P"
  shows "0 < length y \<Longrightarrow> P"
  apply (cases y)
   apply simp
  apply (rule assms)
  apply fastforce
  done

lemma list_exhaust_size_eq0:
  assumes "y = [] \<Longrightarrow> P"
  shows "length y = 0 \<Longrightarrow> P"
  apply (cases y)
   apply (rule assms)
   apply simp
  apply simp
  done

lemma size_Cons_lem_eq: "y = xa # list \<Longrightarrow> size y = Suc k \<Longrightarrow> size list = k"
  by auto

lemma takeWhile_take_has_property:
  "n \<le> length (takeWhile P xs) \<Longrightarrow> \<forall>x \<in> set (take n xs). P x"
  by (induct xs arbitrary: n; simp split: if_split_asm) (case_tac n, simp_all)

lemma takeWhile_take_has_property_nth:
  "\<lbrakk> n < length (takeWhile P xs) \<rbrakk> \<Longrightarrow> P (xs ! n)"
  by (induct xs arbitrary: n; simp split: if_split_asm) (case_tac n, simp_all)

lemma takeWhile_replicate:
  "takeWhile f (replicate len x) = (if f x then replicate len x else [])"
  by (induct_tac len) auto

lemma takeWhile_replicate_empty:
  "\<not> f x \<Longrightarrow> takeWhile f (replicate len x) = []"
  by (simp add: takeWhile_replicate)

lemma takeWhile_replicate_id:
  "f x \<Longrightarrow> takeWhile f (replicate len x) = replicate len x"
  by (simp add: takeWhile_replicate)

lemma nth_rev: "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - 1 - n)"
  using rev_nth by simp

lemma nth_rev_alt: "n < length ys \<Longrightarrow> ys ! n = rev ys ! (length ys - Suc n)"
  by (simp add: nth_rev)

lemma hd_butlast: "length xs > 1 \<Longrightarrow> hd (butlast xs) = hd xs"
  by (cases xs) auto

lemma split_upt_on_n:
  "n < m \<Longrightarrow> [0 ..< m] = [0 ..< n] @ [n] @ [Suc n ..< m]"
  by (metis append_Cons append_Nil less_Suc_eq_le less_imp_le_nat upt_add_eq_append'
            upt_rec zero_less_Suc)

lemma drop_eq_mono:
  assumes le: "m \<le> n"
  assumes drop: "drop m xs = drop m ys"
  shows "drop n xs = drop n ys"
proof -
  have ex: "\<exists>p. n = p + m" by (rule exI[of _ "n - m"]) (simp add: le)
  then obtain p where p: "n = p + m" by blast
  show ?thesis unfolding p drop_drop[symmetric] drop by simp
qed

lemma drop_Suc_nth:
  "n < length xs \<Longrightarrow> drop n xs = xs!n # drop (Suc n) xs"
  by (simp add: Cons_nth_drop_Suc)

lemma and_len: "xs = ys \<Longrightarrow> xs = ys \<and> length xs = length ys"
  by auto

lemma tl_if: "tl (if p then xs else ys) = (if p then tl xs else tl ys)"
  by auto

lemma hd_if: "hd (if p then xs else ys) = (if p then hd xs else hd ys)"
  by auto

lemma if_single: "(if xc then [xab] else [an]) = [if xc then xab else an]"
  by auto

\<comment> \<open>note -- \<open>if_Cons\<close> can cause blowup in the size, if \<open>p\<close> is complex, so make a simproc\<close>
lemma if_Cons: "(if p then x # xs else y # ys) = If p x y # If p xs ys"
  by auto

lemma list_of_false:
  "True \<notin> set xs \<Longrightarrow> xs = replicate (length xs) False"
  by (induct xs, simp_all)

lemma list_all2_induct [consumes 1, case_names Nil Cons]:
  assumes lall: "list_all2 Q xs ys"
  and     nilr: "P [] []"
  and    consr: "\<And>x xs y ys. \<lbrakk>list_all2 Q xs ys; Q x y; P xs ys\<rbrakk> \<Longrightarrow> P (x # xs) (y # ys)"
  shows  "P xs ys"
  using lall
proof (induct rule: list_induct2 [OF list_all2_lengthD [OF lall]])
  case 1 then show ?case by auto fact+
next
  case (2 x xs y ys)

  show ?case
  proof (rule consr)
    from "2.prems" show "list_all2 Q xs ys" and "Q x y" by simp_all
    then show "P xs ys" by (intro "2.hyps")
  qed
qed

lemma replicate_minus:
  "k < n \<Longrightarrow> replicate n False = replicate (n - k) False @ replicate k False"
  by (subst replicate_add [symmetric]) simp

lemma cart_singleton_empty:
  "(S \<times> {e} = {}) = (S = {})"
  by blast

lemma MinI:
  assumes fa: "finite A"
  and     ne: "A \<noteq> {}"
  and     xv: "m \<in> A"
  and    min: "\<forall>y \<in> A. m \<le> y"
  shows "Min A = m" using fa ne xv min
proof (induct A arbitrary: m rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case (insert y F)

  from insert.prems have yx: "m \<le> y" and fx: "\<forall>y \<in> F. m \<le> y" by auto
  have "m \<in> insert y F" by fact
  then show ?case
  proof
    assume mv: "m = y"

    have mlt: "m \<le> Min F"
      by (rule iffD2 [OF Min_ge_iff [OF insert.hyps(1) insert.hyps(2)] fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mv [symmetric])
      apply (auto simp: min_def mlt)
      done
  next
    assume "m \<in> F"
    then have mf: "Min F = m"
      by (rule insert.hyps(4) [OF _ fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mf)
      apply (rule iffD2 [OF _ yx])
      apply (auto simp: min_def)
      done
  qed
qed

lemma power_numeral: "a ^ numeral k = a * a ^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma funpow_numeral [simp]: "f ^^ numeral k = f \<circ> f ^^ (pred_numeral k)"
  by (simp add: numeral_eq_Suc)

lemma funpow_minus_simp: "0 < n \<Longrightarrow> f ^^ n = f \<circ> f ^^ (n - 1)"
  by (auto dest: gr0_implies_Suc)

lemma rco_alt: "(f \<circ> g) ^^ n \<circ> f = f \<circ> (g \<circ> f) ^^ n"
  apply (rule ext)
  apply (induct n)
   apply (simp_all add: o_def)
  done

lemma union_sub:
  "\<lbrakk>B \<subseteq> A; C \<subseteq> B\<rbrakk> \<Longrightarrow> (A - B) \<union> (B - C) = (A - C)"
  by fastforce

lemma insert_sub:
  "x \<in> xs \<Longrightarrow> (insert x (xs - ys)) = (xs - (ys - {x}))"
  by blast

lemma ran_upd:
  "\<lbrakk> inj_on f (dom f); f y = Some z \<rbrakk> \<Longrightarrow> ran (\<lambda>x. if x = y then None else f x) = ran f - {z}"
  unfolding ran_def
  apply (rule set_eqI)
  apply simp
  by (metis domI inj_on_eq_iff option.sel)

lemma if_apply_def2:
  "(if P then F else G) = (\<lambda>x. (P \<longrightarrow> F x) \<and> (\<not> P \<longrightarrow> G x))"
  by simp

lemma case_bool_If:
  "case_bool P Q b = (if b then P else Q)"
  by simp

lemma if_f:
  "(if a then f b else f c) = f (if a then b else c)"
  by simp

lemma size_if: "size (if p then xs else ys) = (if p then size xs else size ys)"
  by (fact if_distrib)

lemma if_Not_x: "(if p then \<not> x else x) = (p = (\<not> x))"
  by auto

lemma if_x_Not: "(if p then x else \<not> x) = (p = x)"
  by auto

lemma if_same_and: "(If p x y \<and> If p u v) = (if p then x \<and> u else y \<and> v)"
  by auto

lemma if_same_eq: "(If p x y  = (If p u v)) = (if p then x = u else y = v)"
  by auto

lemma if_same_eq_not: "(If p x y = (\<not> If p u v)) = (if p then x = (\<not> u) else y = (\<not> v))"
  by auto

lemma the_elemI: "y = {x} \<Longrightarrow> the_elem y = x"
  by simp

lemma nonemptyE: "S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemmas xtr1 = xtrans(1)
lemmas xtr2 = xtrans(2)
lemmas xtr3 = xtrans(3)
lemmas xtr4 = xtrans(4)
lemmas xtr5 = xtrans(5)
lemmas xtr6 = xtrans(6)
lemmas xtr7 = xtrans(7)
lemmas xtr8 = xtrans(8)

lemmas if_fun_split = if_apply_def2

lemma not_empty_eq:
  "(S \<noteq> {}) = (\<exists>x. x \<in> S)"
  by auto

lemma range_subset_lower:
  fixes c :: "'a ::linorder"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; x \<in> {a..b} \<rbrakk> \<Longrightarrow> c \<le> a"
  apply (frule (1) subsetD)
  apply (rule classical)
  apply clarsimp
  done

lemma range_subset_upper:
  fixes c :: "'a ::linorder"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; x \<in> {a..b} \<rbrakk> \<Longrightarrow> b \<le> d"
  apply (frule (1) subsetD)
  apply (rule classical)
  apply clarsimp
  done

lemma range_subset_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} \<subseteq> {c..d}) = (c \<le> a \<and> b \<le> d)"
  apply (insert non_empty)
  apply (rule iffI)
   apply (frule range_subset_lower [where x=a], simp)
   apply (drule range_subset_upper [where x=a], simp)
   apply simp
  apply auto
  done

lemma range_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} = {c..d}) = (a = c \<and> b = d)"
  by (metis atLeastatMost_subset_iff eq_iff non_empty)

lemma range_strict_subset_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} \<subset> {c..d}) = (c \<le> a \<and> b \<le> d \<and> (a = c \<longrightarrow> b \<noteq> d))"
  apply (insert non_empty)
  apply (subst psubset_eq)
  apply (subst range_subset_eq, assumption+)
  apply (subst range_eq, assumption+)
  apply simp
  done

lemma range_subsetI:
  fixes x :: "'a :: order"
  assumes xX: "X \<le> x"
  and     yY: "y \<le> Y"
  shows   "{x .. y} \<subseteq> {X .. Y}"
  using xX yY by auto

lemma set_False [simp]:
  "(set bs \<subseteq> {False}) = (True \<notin> set bs)" by auto

lemma int_not_emptyD:
  "A \<inter> B \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<in> B"
  by (erule contrapos_np, clarsimp simp: disjoint_iff_not_equal)

definition
  sum_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a + 'c \<Rightarrow> 'b + 'd" where
 "sum_map f g x \<equiv> case x of Inl v \<Rightarrow> Inl (f v) | Inr v' \<Rightarrow> Inr (g v')"

lemma sum_map_simps[simp]:
  "sum_map f g (Inl v) = Inl (f v)"
  "sum_map f g (Inr w) = Inr (g w)"
  by (simp add: sum_map_def)+

lemma if_Some_None_eq_None:
  "((if P then Some v else None) = None) = (\<not> P)"
  by simp

lemma CollectPairFalse [iff]:
  "{(a,b). False} = {}"
  by (simp add: split_def)

lemma if_conj_dist:
  "((if b then w else x) \<and> (if b then y else z) \<and> X) =
  ((if b then w \<and> y else x \<and> z) \<and> X)"
  by simp

lemma if_P_True1:
  "Q \<Longrightarrow> (if P then True else Q)"
  by simp

lemma if_P_True2:
  "Q \<Longrightarrow> (if P then Q else True)"
  by simp

lemmas nat_simps = diff_add_inverse2 diff_add_inverse

lemmas nat_iffs = le_add1 le_add2

lemma nat_min_simps:
  "(a::nat) \<le> b \<Longrightarrow> min b a = a"
  "a \<le> b \<Longrightarrow> min a b = a"
  by simp_all

lemmas zadd_diff_inverse =
  trans [OF diff_add_cancel [symmetric] add.commute]

lemmas add_diff_cancel2 =
  add.commute [THEN diff_eq_eq [THEN iffD2]]

lemmas mcl = mult_cancel_left [THEN iffD1, THEN make_pos_rule]

lemma pl_pl_rels: "a + b = c + d \<Longrightarrow> a \<ge> c \<and> b \<le> d \<or> a \<le> c \<and> b \<ge> d"
  for a b c d :: nat
  by arith

lemmas pl_pl_rels' = add.commute [THEN [2] trans, THEN pl_pl_rels]

lemma iszero_minus:
  \<open>iszero (- z) \<longleftrightarrow> iszero z\<close>
  by (simp add: iszero_def)

lemma diff_le_eq': "a - b \<le> c \<longleftrightarrow> a \<le> b + c"
  for a b c :: int
  by arith

lemma zless2: "0 < (2 :: int)"
  by (fact zero_less_numeral)

lemma zless2p: "0 < (2 ^ n :: int)"
  by arith

lemma zle2p: "0 \<le> (2 ^ n :: int)"
  by arith

lemma ex_eq_or: "(\<exists>m. n = Suc m \<and> (m = k \<or> P m)) \<longleftrightarrow> n = Suc k \<or> (\<exists>m. n = Suc m \<and> P m)"
  by auto

lemma power_minus_simp: "0 < n \<Longrightarrow> a ^ n = a * a ^ (n - 1)"
  by (auto dest: gr0_implies_Suc)

lemma n2s_ths:
  \<open>2 + n = Suc (Suc n)\<close>
  \<open>n + 2 = Suc (Suc n)\<close>
  by (fact add_2_eq_Suc add_2_eq_Suc')+

lemma s2n_ths:
  \<open>Suc (Suc n) = 2 + n\<close>
  \<open>Suc (Suc n) = n + 2\<close>
  by simp_all

lemma gt_or_eq_0: "0 < y \<or> 0 = y"
  for y :: nat
  by arith

lemma sum_imp_diff: "j = k + i \<Longrightarrow> j - i = k"
  for k :: nat
  by simp

lemma le_diff_eq': "a \<le> c - b \<longleftrightarrow> b + a \<le> c"
  for a b c :: int
  by arith

lemma less_diff_eq': "a < c - b \<longleftrightarrow> b + a < c"
  for a b c :: int
  by arith

lemma diff_less_eq': "a - b < c \<longleftrightarrow> a < b + c"
  for a b c :: int
  by arith

lemma axxbyy: "a + m + m = b + n + n \<Longrightarrow> a = 0 \<or> a = 1 \<Longrightarrow> b = 0 \<or> b = 1 \<Longrightarrow> a = b \<and> m = n"
  for a b m n :: int
  by arith

lemma minus_eq: "m - k = m \<longleftrightarrow> k = 0 \<or> m = 0"
  for k m :: nat
  by arith

lemma pl_pl_mm: "a + b = c + d \<Longrightarrow> a - c = d - b"
  for a b c d :: nat
  by arith

lemmas pl_pl_mm' = add.commute [THEN [2] trans, THEN pl_pl_mm]

lemma less_le_mult': "w * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> (w + 1) * c \<le> b * c"
  for b c w :: int
  apply (rule mult_right_mono)
   apply (rule zless_imp_add1_zle)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemma less_le_mult: "w * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> w * c + c \<le> b * c"
  for b c w :: int
  using less_le_mult' [of w c b] by (simp add: algebra_simps)

lemmas less_le_mult_minus = iffD2 [OF le_diff_eq less_le_mult,
  simplified left_diff_distrib]

lemma gen_minus: "0 < n \<Longrightarrow> f n = f (Suc (n - 1))"
  by auto

lemma mpl_lem: "j \<le> i \<Longrightarrow> k < j \<Longrightarrow> i - j + k < i"
  for i j k :: nat
  by arith

lemmas dme = div_mult_mod_eq
lemmas dtle = div_times_less_eq_dividend
lemmas th2 = order_trans [OF order_refl [THEN [2] mult_le_mono] div_times_less_eq_dividend]

lemmas sdl = div_nat_eqI

lemma given_quot: "f > 0 \<Longrightarrow> (f * l + (f - 1)) div f = l"
  for f l :: nat
  by (rule div_nat_eqI) (simp_all)

lemma given_quot_alt: "f > 0 \<Longrightarrow> (l * f + f - Suc 0) div f = l"
  for f l :: nat
  apply (frule given_quot)
  apply (rule trans)
   prefer 2
   apply (erule asm_rl)
  apply (rule_tac f="\<lambda>n. n div f" in arg_cong)
  apply (simp add : ac_simps)
  done

lemma x_power_minus_1:
  fixes x :: "'a :: {ab_group_add, power, numeral, one}"
  shows "x + (2::'a) ^ n - (1::'a) = x + (2 ^ n - 1)" by simp

lemma nat_diff_add:
  fixes i :: nat
  shows "\<lbrakk> i + j = k \<rbrakk> \<Longrightarrow> i = k - j"
  by arith

lemma pow_2_gt: "n \<ge> 2 \<Longrightarrow> (2::int) < 2 ^ n"
  by (induct n) auto

lemma sum_to_zero:
  "(a :: 'a :: ring) + b = 0 \<Longrightarrow> a = (- b)"
  by (drule arg_cong[where f="\<lambda> x. x - a"], simp)

lemma arith_is_1:
  "\<lbrakk> x \<le> Suc 0; x > 0 \<rbrakk> \<Longrightarrow> x = 1"
  by arith

lemma suc_le_pow_2:
  "1 < (n::nat) \<Longrightarrow> Suc n < 2 ^ n"
  by (induct n; clarsimp)
     (case_tac "n = 1"; clarsimp)

lemma nat_le_Suc_less_imp:
  "x < y \<Longrightarrow> x \<le> y - Suc 0"
  by arith

lemma power_sub_int:
  "\<lbrakk> m \<le> n; 0 < b \<rbrakk> \<Longrightarrow> b ^ n div b ^ m = (b ^ (n - m) :: int)"
  apply (subgoal_tac "\<exists>n'. n = m + n'")
   apply (clarsimp simp: power_add)
  apply (rule exI[where x="n - m"])
  apply simp
  done

lemma nat_Suc_less_le_imp:
  "(k::nat) < Suc n \<Longrightarrow> k \<le> n"
  by auto

lemma nat_add_less_by_max:
  "\<lbrakk> (x::nat) \<le> xmax ; y < k - xmax \<rbrakk> \<Longrightarrow> x + y < k"
  by simp

lemma nat_le_Suc_less:
  "0 < y \<Longrightarrow> (x \<le> y - Suc 0) = (x < y)"
  by arith

lemma nat_power_minus_less:
  "a < 2 ^ (x - n) \<Longrightarrow> (a :: nat) < 2 ^ x"
  by (erule order_less_le_trans) simp

lemma less_le_mult_nat':
  "w * c < b * c ==> 0 \<le> c ==> Suc w * c \<le> b * (c::nat)"
  apply (rule mult_right_mono)
   apply (rule Suc_leI)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemma less_le_mult_nat:
  \<open>0 < c \<and> w < b \<Longrightarrow> c + w * c \<le> b * c\<close> for b c w :: nat
  using less_le_mult_nat' [of w c b] by simp

lemma p_assoc_help:
  fixes p :: "'a::{ring,power,numeral,one}"
  shows "p + 2^sz - 1 = p + (2^sz - 1)"
  by simp

lemma pow_mono_leq_imp_lt:
  "x \<le> y \<Longrightarrow> x < 2 ^ y"
  by (simp add: le_less_trans)

lemma small_powers_of_2:
  "x \<ge> 3 \<Longrightarrow> x < 2 ^ (x - 1)"
  by (induct x; simp add: suc_le_pow_2)

lemma nat_less_power_trans2:
  fixes n :: nat
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> n * 2 ^ k  < 2 ^ m"
  by (subst mult.commute, erule (1) nat_less_power_trans)

lemma nat_move_sub_le: "(a::nat) + b \<le> c \<Longrightarrow> a \<le> c - b"
  by arith

lemma plus_minus_one_rewrite:
  "v + (- 1 :: ('a :: {ring, one, uminus})) \<equiv> v - 1"
  by (simp add: field_simps)

lemma Suc_0_lt_2p_len_of: "Suc 0 < 2 ^ LENGTH('a :: len)"
  by (metis One_nat_def len_gt_0 lessI numeral_2_eq_2 one_less_power)

end
