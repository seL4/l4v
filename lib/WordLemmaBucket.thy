(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WordLemmaBucket
imports
  Lib
  MoreDivides
  Aligned
  HOLLemmaBucket
  DistinctPropLemmaBucket
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/Prefix_Order"
begin

(* Setup "quickcheck" to support words. *)

quickcheck_generator word
  constructors:
    "zero_class.zero :: ('a::len) word",
    "numeral :: num \<Rightarrow> ('a::len) word",
    "uminus :: ('a::len) word \<Rightarrow> ('a::len) word"

instantiation Enum.finite_1 :: len
begin
  definition "len_of_finite_1 (x :: Enum.finite_1 itself) \<equiv> (1 :: nat)"
  instance
    by (default, auto simp: len_of_finite_1_def)
end

instantiation Enum.finite_2 :: len
begin
  definition "len_of_finite_2 (x :: Enum.finite_2 itself) \<equiv> (2 :: nat)"
  instance
    by (default, auto simp: len_of_finite_2_def)
end

instantiation Enum.finite_3 :: len
begin
  definition "len_of_finite_3 (x :: Enum.finite_3 itself) \<equiv> (4 :: nat)"
  instance
    by (default, auto simp: len_of_finite_3_def)
end

(* Provide wf and less_induct for word.
   wf may be more useful in loop proofs, less_induct in recursion proofs. *)
lemma word_less_wf: "wf {(a, b). a < (b :: ('a::len) word)}"
  apply (rule wf_subset)
  apply (rule wf_measure)
  apply safe
  apply (subst in_measure)
  apply (erule unat_mono)
  done

lemma word_less_induct:
  "\<lbrakk> \<And>x::('a::len) word. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P a"
  using word_less_wf
  apply induct
  apply blast
  done

instantiation word :: (len) wellorder
begin
instance
  apply (intro_classes)
  apply (metis word_less_induct)
  done
end


lemma word_plus_mono_left:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y \<le> z; x \<le> x + z\<rbrakk> \<Longrightarrow> y + x \<le> z + x"
  by unat_arith

lemma word_2p_mult_inc:
  assumes x: "2 * 2 ^ n < (2::'a::len word) * 2 ^ m"
  assumes suc_n: "Suc n < len_of TYPE('a::len)"
  assumes suc_m: "Suc m < len_of TYPE('a::len)"
  assumes 2: "unat (2::'a::len word) = 2"
  shows "2^n < (2::'a::len word)^m"
proof -
  from suc_n
  have "(2::nat) * 2 ^ n mod 2 ^ len_of TYPE('a::len) = 2 * 2^n"
    apply (subst mod_less)
     apply (subst power_Suc[symmetric])
     apply (rule power_strict_increasing)
      apply simp
     apply simp
    apply simp
    done
  moreover
  from suc_m
  have "(2::nat) * 2 ^ m mod 2 ^ len_of TYPE('a::len) = 2 * 2^m"
    apply (subst mod_less)
     apply (subst power_Suc[symmetric])
     apply (rule power_strict_increasing)
      apply simp
     apply simp
    apply simp
    done
  ultimately
  have "2 * 2 ^ n < (2::nat) * 2 ^ m" using x
    apply (unfold word_less_nat_alt)
    apply simp
    apply (subst (asm) unat_word_ariths(2))+
    apply (subst (asm) 2)+
    apply (subst (asm) word_unat_power, subst (asm) unat_of_nat)+
    apply (simp add: mod_mult_right_eq[symmetric])
    done
  with suc_n suc_m
  show ?thesis
    unfolding word_less_nat_alt
    apply (subst word_unat_power, subst unat_of_nat)+
    apply simp
    done
qed

lemma word_power_increasing:
  assumes x: "2 ^ x < (2 ^ y::'a::len word)" "x < len_of TYPE('a::len)" "y < len_of TYPE('a::len)"
  assumes 2: "unat (2::'a::len word) = 2"
  shows "x < y" using x
  apply (induct x arbitrary: y)
   apply simp
   apply (case_tac y, simp)
   apply simp
  apply clarsimp
  apply (case_tac y)
   apply simp
   apply (subst (asm) power_Suc [symmetric])
   apply (subst (asm) p2_eq_0)
   apply simp
  apply clarsimp
  apply (drule (2) word_2p_mult_inc, rule 2)
  apply simp
  done

lemma word_shiftl_add_distrib:
  fixes x :: "'a :: len word"
  shows "(x + y) << n = (x << n) + (y << n)"
  by (simp add: shiftl_t2n ring_distribs)

lemma upper_bits_unset_is_l2p:
  "n < word_bits \<Longrightarrow> (\<forall>n' \<ge> n. n' < word_bits \<longrightarrow> \<not> p !! n') = ((p::word32) < 2 ^ n)"
  apply (rule iffI)
   prefer 2
   apply (clarsimp simp: word_bits_def)
   apply (drule bang_is_le)
   apply (drule_tac y=p in order_le_less_trans, assumption)
   apply (drule word_power_increasing)
      apply simp
     apply simp
    apply simp
   apply simp
  apply (subst mask_eq_iff_w2p [symmetric])
   apply (clarsimp simp: word_size word_bits_def)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size word_bits_def)
  apply (case_tac "na < n", auto)
  done

lemma up_ucast_inj:
  "\<lbrakk> ucast x = (ucast y::'b::len word); len_of TYPE('a) \<le> len_of TYPE ('b) \<rbrakk> \<Longrightarrow> x = (y::'a::len word)"
  apply (subst (asm) bang_eq)
  apply (fastforce simp: nth_ucast word_size intro: word_eqI)
  done

lemma up_ucast_inj_eq:
  "len_of TYPE('a) \<le> len_of TYPE ('b) \<Longrightarrow> (ucast x = (ucast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_ucast_inj)

lemma ucast_up_inj:
  "\<lbrakk> ucast x = (ucast y :: 'b::len word); len_of TYPE('a) \<le> len_of TYPE('b) \<rbrakk>
  \<Longrightarrow> x = (y :: 'a::len word)"
  apply (subst (asm) bang_eq)
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast)
  apply (erule_tac x=n in allE)
  apply simp
  done

lemma ucast_8_32_inj:
  "inj (ucast ::  8 word \<Rightarrow> 32 word)"
  apply (rule down_ucast_inj)
  apply (clarsimp simp: is_down_def target_size source_size)
  done

lemma no_plus_overflow_neg:
  "(x :: ('a :: len) word) < -y \<Longrightarrow> x \<le> x + y"
  apply (simp add: no_plus_overflow_uint_size
                   word_less_alt uint_word_ariths
                   word_size)
  apply (subst(asm) zmod_zminus1_eq_if)
  apply (simp split: split_if_asm)
  done

lemma ucast_ucast_eq:
  fixes x :: "'a::len word"
  fixes y :: "'b::len word"
  shows
  "\<lbrakk> ucast x = (ucast (ucast y::'a::len word)::'c::len word);
    len_of TYPE('a) \<le> len_of TYPE('b);
    len_of TYPE('b) \<le> len_of TYPE('c) \<rbrakk> \<Longrightarrow>
  x = ucast y"
  apply (rule word_eqI)
  apply (subst (asm) bang_eq)
  apply (erule_tac x=n in allE)
  apply (simp add: nth_ucast word_size)
  done

(******** GeneralLib ****************)


lemma neq_into_nprefixeq:
  "\<lbrakk> x \<noteq> take (length x) y \<rbrakk> \<Longrightarrow> \<not> x \<le> y"
  by (clarsimp simp: prefixeq_def less_eq_list_def)

lemma suffixeq_drop [simp]:
  "suffixeq (drop n as) as"
  unfolding suffixeq_def
  apply (rule exI [where x = "take n as"])
  apply simp
  done

lemma suffixeq_eqI:
  "\<lbrakk> suffixeq xs as; suffixeq xs bs; length as = length bs;
    take (length as - length xs) as \<le> take (length bs - length xs) bs\<rbrakk> \<Longrightarrow> as = bs"
  by (clarsimp elim!: prefixE suffixeqE)

lemma suffixeq_Cons_mem:
  "suffixeq (x # xs) as \<Longrightarrow> x \<in> set as"
  apply (drule suffixeq_set_subset)
  apply simp
  done

lemma distinct_imply_not_in_tail:
  "\<lbrakk> distinct list; suffixeq (y # ys) list\<rbrakk> \<Longrightarrow> y \<notin> set ys"
  by (clarsimp simp:suffixeq_def)

lemma list_induct_suffixeq [case_names Nil Cons]:
  assumes nilr: "P []"
  and    consr: "\<And>x xs. \<lbrakk>P xs; suffixeq (x # xs) as \<rbrakk> \<Longrightarrow> P (x # xs)"
  shows  "P as"
proof -
  def as' == as

  have "suffixeq as as'" unfolding as'_def by simp
  thus ?thesis
  proof (induct as)
    case Nil show ?case by fact
  next
    case (Cons x xs)

    show ?case
    proof (rule consr)
      from Cons.prems show "suffixeq (x # xs) as" unfolding as'_def .
      hence "suffixeq xs as'" by (auto dest: suffixeq_ConsD simp: as'_def)
      thus "P xs" using Cons.hyps by simp
    qed
  qed
qed

text {* Parallel etc. and lemmas for list prefix *}

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
  case Nil thus ?thesis using pfx by simp
next
  case (Cons a as)

  have c: "prefix = a#as" by fact

  show ?thesis
  proof (cases lst)
    case Nil thus ?thesis
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
  case Nil thus ?case
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

text {* right-padding a word to a certain length *}

lemma bl_pad_to_prefix:
  "bl \<le> bl_pad_to bl sz"
  by (simp add: bl_pad_to_def)

lemma same_length_is_parallel:
  assumes len: "\<forall>y \<in> set as. length y = x"
  shows  "\<forall>x \<in> set as. \<forall>y \<in> set as - {x}. x \<parallel> y"
proof (rule, rule)
  fix x y
  assume xi: "x \<in> set as" and yi: "y \<in> set as - {x}"
  from len obtain q where len': "\<forall>y \<in> set as. length y = q" ..

  show "x \<parallel> y"
  proof (rule not_equal_is_parallel)
    from xi yi show "x \<noteq> y" by auto
    from xi yi len' show "length x = length y" by (auto dest: bspec)
  qed
qed

text {* Lemmas about words *}

lemma word_bits_len_of: "len_of TYPE (32) = word_bits"
  by (simp add: word_bits_conv)

lemmas unat_power_lower32 [simp] = unat_power_lower[where 'a=32, unfolded word_bits_len_of]

lemmas and_bang = word_and_nth

lemma of_drop_to_bl:
  "of_bl (drop n (to_bl x)) = (x && mask (size x - n))"
  apply (clarsimp simp: bang_eq test_bit_of_bl rev_nth cong: rev_conj_cong)
  apply (safe, simp_all add: word_size to_bl_nth)
  done

lemma word_add_offset_less:
  fixes x :: "'a :: len word"
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mnv: "sz < len_of TYPE('a :: len)"
  and    xv': "x < 2 ^ (len_of TYPE('a :: len) - n)"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from mnv mn have nv: "n < len_of TYPE('a)" and mv: "m < len_of TYPE('a)"  by auto

  have uy: "unat y < 2 ^ n"
     by (rule order_less_le_trans [OF unat_mono [OF yv] order_eq_refl],
       rule unat_power_lower[OF nv])

  have ux: "unat x < 2 ^ m"
     by (rule order_less_le_trans [OF unat_mono [OF xv] order_eq_refl],
       rule unat_power_lower[OF mv])

  thus "x * 2 ^ n + y < 2 ^ (m + n)" using ux uy nv mnv xv'
  apply (subst word_less_nat_alt)
  apply (subst unat_word_ariths word_bits_len_of)+
  apply (subst mod_less)
   apply simp
   apply (subst mult.commute)
   apply (rule nat_less_power_trans [OF _ order_less_imp_le [OF nv]])
    apply (rule order_less_le_trans [OF unat_mono [OF xv']])
    apply (cases "n = 0")
       apply simp
      apply simp
    apply (subst unat_power_lower[OF nv])
    apply (subst mod_less)
   apply (erule order_less_le_trans [OF nat_add_offset_less], assumption)
    apply (rule mn)
   apply simp
  apply (simp add: mn mnv)
  apply (erule nat_add_offset_less)
  apply simp+
  done
qed

lemma word_less_power_trans:
  fixes n :: "'a :: len word"
  assumes nv: "n < 2 ^ (m - k)"
  and     kv: "k \<le> m"
  and     mv: "m < len_of TYPE ('a)"
  shows "2 ^ k * n < 2 ^ m"
  using nv kv mv
  apply -
  apply (subst word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply simp
   apply (rule nat_less_power_trans)
    apply (erule order_less_trans [OF unat_mono])
    apply simp
   apply simp
  apply simp
  apply (rule nat_less_power_trans)
   apply (subst unat_power_lower[where 'a = 'a, symmetric])
    apply simp
   apply (erule unat_mono)
  apply simp
  done

lemma word_less_sub_le[simp]:
  fixes x :: "'a :: len word"
  assumes nv: "n < len_of TYPE('a)"
  shows "(x \<le> 2 ^ n - 1) = (x < 2 ^ n)"
proof -
  have "Suc (unat ((2::'a word) ^ n - 1)) = unat ((2::'a word) ^ n)" using nv
    by (metis Suc_pred' power_2_ge_iff unat_gt_0 unat_minus_one word_not_simps(1))

  thus ?thesis using nv
    apply -
    apply (subst word_le_nat_alt)
    apply (subst less_Suc_eq_le [symmetric])
    apply (erule ssubst)
    apply (subst word_less_nat_alt)
    apply (rule refl)
    done
qed

lemmas word32_less_sub_le[simp] =
       word_less_sub_le[where 'a = 32, folded word_bits_def]

lemma Suc_unat_diff_1:
  fixes x :: "'a :: len word"
  assumes lt: "1 \<le> x"
  shows "Suc (unat (x - 1)) = unat x"
proof -
  have "0 < unat x"
    by (rule order_less_le_trans [where y = 1], simp, subst unat_1 [symmetric], rule iffD1 [OF word_le_nat_alt lt])

  thus ?thesis
    by ((subst unat_sub [OF lt])+, simp only:  unat_1)
qed

lemma word_div_sub:
  fixes x :: "'a :: len word"
  assumes yx: "y \<le> x"
  and     y0: "0 < y"
  shows "(x - y) div y = x div y - 1"
  apply (rule word_unat.Rep_eqD)
  apply (subst unat_div)
  apply (subst unat_sub [OF yx])
  apply (subst unat_sub)
   apply (subst word_le_nat_alt)
   apply (subst unat_div)
   apply (subst le_div_geq)
     apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
     apply simp
    apply (subst word_le_nat_alt [symmetric], rule yx)
   apply simp
  apply (subst unat_div)
  apply (subst le_div_geq [OF _ iffD1 [OF word_le_nat_alt yx]])
   apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
   apply simp
  apply simp
  done

lemma word_mult_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k < j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto intro: order_less_subst2 simp: word_less_nat_alt elim: mult_less_mono1)

  thus ?thesis using ujk knz ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_less_dest:
  fixes i :: "'a :: len word"
  assumes ij: "i * k < j * k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk ij
  by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem] elim: mult_less_mono1)

lemma word_mult_less_cancel:
  fixes k :: "'a :: len word"
  assumes knz: "0 < k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows "(i * k < j * k) = (i < j)"
  by (rule iffI [OF word_mult_less_dest [OF _ uik ujk] word_mult_less_mono1 [OF _ knz ujk]])

lemma Suc_div_unat_helper:
  assumes szv: "sz < len_of TYPE('a :: len)"
  and   usszv: "us \<le> sz"
  shows "2 ^ (sz - us) = Suc (unat (((2::'a :: len word) ^ sz - 1) div 2 ^ us))"
proof -
  note usv = order_le_less_trans [OF usszv szv]

  from usszv obtain q where qv: "sz = us + q" by (auto simp: le_iff_add)

  have "Suc (unat (((2:: 'a word) ^ sz - 1) div 2 ^ us)) =
    (2 ^ us + unat ((2:: 'a word) ^ sz - 1)) div 2 ^ us"
    apply (subst unat_div unat_power_lower[OF usv])+
    apply (subst div_add_self1, simp+)
    done

  also have "\<dots> = ((2 ^ us - 1) + 2 ^ sz) div 2 ^ us" using szv
    apply (subst unat_minus_one)
     apply (simp add: p2_eq_0)
    apply simp
    done

  also have "\<dots> = 2 ^ q + ((2 ^ us - 1) div 2 ^ us)"
    apply (subst qv)
    apply (subst power_add)
    apply (subst div_mult_self2)
    apply simp
    apply (rule refl)
    done

  also have "\<dots> = 2 ^ (sz - us)" using qv by simp

  finally show ?thesis ..
qed

lemma upto_enum_red':
  assumes lt: "1 \<le> X"
  shows "[(0::'a :: len word) .e. X - 1] =  map of_nat [0 ..< unat X]"
proof -
  have lt': "unat X < 2 ^ len_of TYPE('a)"
    by (rule unat_lt2p)

  show ?thesis
    apply (subst upto_enum_red)
    apply (simp del: upt.simps)
    apply (subst Suc_unat_diff_1 [OF lt])
    apply (rule map_cong [OF refl])
    apply (rule toEnum_of_nat)
    apply simp
    apply (erule order_less_trans [OF _ lt'])
    done
qed

lemma upto_enum_red2:
  assumes szv: "sz < len_of TYPE('a :: len)"
  shows "[(0:: 'a :: len word) .e. 2 ^ sz - 1] =
  map of_nat [0 ..< 2 ^ sz]" using szv
  apply (subst unat_power_lower[OF szv, symmetric])
  apply (rule upto_enum_red')
  apply (subst word_le_nat_alt, simp)
  done

(* FIXME: WordEnum.upto_enum_step_def is fixed to word32. *)
lemma upto_enum_step_red:
  assumes szv: "sz < word_bits"
  and   usszv: "us \<le> sz"
  shows "[0 , 2 ^ us .e. 2 ^ sz - 1] =
  map (\<lambda>x. of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]" using szv
  unfolding upto_enum_step_def
  apply (subst if_not_P)
   apply (rule leD)
   apply (subst word_le_nat_alt)
   apply (subst unat_minus_one)
    apply (simp add: p2_eq_0 word_bits_def)
   apply simp
  apply simp
  apply (subst upto_enum_red)
  apply (simp del: upt.simps)
  apply (subst Suc_div_unat_helper [where 'a = 32, folded word_bits_def, OF szv usszv, symmetric])
  apply clarsimp
  apply (subst toEnum_of_nat)
   apply (subst word_bits_len_of)
   apply (erule order_less_trans)
   using szv
   apply simp
  apply simp
  done

lemma upto_enum_word:
  "[x .e. y] = map of_nat [unat x ..< Suc (unat y)]"
  apply (subst upto_enum_red)
  apply clarsimp
  apply (subst toEnum_of_nat)
   prefer 2
   apply (rule refl)
  apply (erule disjE, simp)
  apply clarsimp
  apply (erule order_less_trans)
  apply simp
  done

text {* Lemmas about upto and upto_enum *}

lemma word_upto_Cons_eq:
  "\<lbrakk>x = z; x < y; Suc (unat y) < 2 ^ len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> [x::'a::len word .e. y] = z # [x + 1 .e. y]"
  apply (subst upto_enum_red)
  apply (subst upt_conv_Cons)
   apply (simp)
   apply (drule unat_mono)
   apply arith
  apply (simp only: list.map)
  apply (subst list.inject)
  apply rule
   apply (rule to_from_enum)
   apply (subst upto_enum_red)
  apply (rule map_cong [OF _ refl])
  apply (rule arg_cong2 [where f = "\<lambda>x y. [x ..< y]"])
   apply unat_arith
  apply simp
  done

lemma distinct_enum_upto:
  "distinct [(0 :: 'a::len word) .e. b]"
proof -
  have "\<And>(b::'a word). [0 .e. b] = sublist enum {..< Suc (fromEnum b)}"
    apply (subst upto_enum_red)
    apply (subst sublist_upt_eq_take)
    apply (subst enum_word_def)
    apply (subst take_map)
    apply (subst take_upt)
     apply (simp only: add_0 fromEnum_unat)
     apply (rule order_trans [OF _ order_eq_refl])
      apply (rule Suc_leI [OF unat_lt2p])
     apply simp
    apply clarsimp
    apply (rule toEnum_of_nat)
    apply (erule order_less_trans [OF _ unat_lt2p])
    done

  thus ?thesis
    by (rule ssubst) (rule distinct_sublistI, simp)
qed

lemma upto_enum_set_conv [simp]:
  fixes a :: "'a :: len word"
  shows "set [a .e. b] = {x. a \<le> x \<and> x \<le> b}"
  apply (subst upto_enum_red)
  apply (subst set_map)
  apply safe
    apply simp
    apply clarsimp
    apply (erule disjE)
     apply simp
     apply (erule iffD2 [OF word_le_nat_alt])
    apply clarsimp
    apply (erule word_unat.Rep_cases [OF unat_le [OF order_less_imp_le]])
    apply simp
    apply (erule iffD2 [OF word_le_nat_alt])
   apply simp

   apply clarsimp
   apply (erule disjE)
    apply simp
   apply clarsimp
   apply (rule word_unat.Rep_cases [OF unat_le  [OF order_less_imp_le]])
    apply assumption
   apply simp
   apply (erule order_less_imp_le [OF iffD2 [OF word_less_nat_alt]])
  apply clarsimp
  apply (rule_tac x="fromEnum x" in image_eqI)
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
   apply (subst word_le_nat_alt [symmetric])
   apply simp
  apply safe
   apply (simp add: word_le_nat_alt [symmetric])
  apply (simp add: word_less_nat_alt [symmetric])
  done

lemma upto_enum_less:
  assumes xin: "x \<in> set [(a::'a::len word).e.2 ^ n - 1]"
  and     nv:  "n < len_of TYPE('a::len)"
  shows   "x < 2 ^ n"
proof (cases n)
  case 0
  thus ?thesis using xin by simp
next
  case (Suc m)
  show ?thesis using xin nv by simp
qed

lemma upto_enum_len_less:
  "\<lbrakk> n \<le> length [a, b .e. c]; n \<noteq> 0 \<rbrakk> \<Longrightarrow> a \<le> c"
  unfolding upto_enum_step_def
  by (simp split: split_if_asm)

lemma length_upto_enum_step:
  fixes x :: word32
  shows "x \<le> z \<Longrightarrow> length [x , y .e. z] = (unat ((z - x) div (y - x))) + 1"
  unfolding upto_enum_step_def
  by (simp add: upto_enum_red)

lemma length_upto_enum_one:
  fixes x :: word32
  assumes lt1: "x < y" and lt2: "z < y" and lt3: "x \<le> z"
  shows "[x , y .e. z] = [x]"
unfolding upto_enum_step_def
proof (subst upto_enum_red, subst if_not_P [OF leD [OF lt3]], clarsimp, rule)
  show "unat ((z - x) div (y - x)) = 0"
  proof (subst unat_div, rule div_less)
    have syx: "unat (y - x) = unat y - unat x"
      by (rule unat_sub [OF order_less_imp_le]) fact
    moreover have "unat (z - x) = unat z - unat x"
      by (rule unat_sub) fact

    ultimately show "unat (z - x) < unat (y - x)"
      using lt3
      apply simp
      apply (rule diff_less_mono[OF unat_mono, OF lt2])
      apply (simp add: word_le_nat_alt[symmetric])
      done
  qed

  thus "toEnum (unat ((z - x) div (y - x))) * (y - x) = 0" by simp
qed

lemma map_length_unfold_one:
  fixes x :: "'a::len word"
  assumes xv: "Suc (unat x) < 2 ^ len_of TYPE('a)"
  and     ax: "a < x"
  shows   "map f [a .e. x] = f a # map f [a + 1 .e. x]"
  by (subst word_upto_Cons_eq, auto, fact+)

lemma upto_enum_triv [simp]:
  "[x .e. x] = [x]"
  unfolding upto_enum_def by simp

lemma upto_enum_set_conv2:
  fixes a :: "'a::len word"
  shows "set [a .e. b] = {a .. b}"
  by auto

lemma of_nat_unat [simp]:
  "of_nat \<circ> unat = id"
  by (rule ext, simp)

lemma Suc_unat_minus_one [simp]:
  "x \<noteq> 0 \<Longrightarrow> Suc (unat (x - 1)) = unat x"
  by (metis Suc_diff_1 unat_gt_0 unat_minus_one)

text {* Lemmas about alignment *}

lemma word_bits_size:
  "size (w::word32) = word_bits"
  by (simp add: word_bits_def word_size)

text {* Lemmas about defs in the specs *}

lemma and_commute:
  "(X and Y) = (Y and X)"
  unfolding pred_conj_def by (auto simp: fun_eq_iff)

lemma ptr_add_0 [simp]:
  "ptr_add ref 0 = ref "
  unfolding ptr_add_def by simp

(* Other word lemmas *)

lemma word_add_le_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k \<le> j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i \<le> j"
  using uik ujk le
  by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem] elim: add_le_mono1)

lemma mask_shift:
  "(x && ~~ mask y) >> y = x >> y"
  apply (rule word_eqI)
  apply (simp add: nth_shiftr word_size)
  apply safe
  apply (drule test_bit.Rep[simplified, rule_format])
  apply (simp add: word_size word_ops_nth_size)
  done

lemma word_add_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k \<le> j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: add_le_mono1)

  thus ?thesis using ujk ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_le_mono2:
  fixes i :: "('a :: len) word"
  shows "\<lbrakk>i \<le> j; unat j + unat k < 2 ^ len_of TYPE('a)\<rbrakk> \<Longrightarrow> k + i \<le> k + j"
  by (subst field_simps, subst field_simps, erule (1) word_add_le_mono1)

lemma word_add_le_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k \<le> j + k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i + k \<le> j + k" by (rule word_add_le_mono1) fact+
next
  assume "i + k \<le> j + k"
  show "i \<le> j" by (rule word_add_le_dest) fact+
qed

lemma word_add_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k < j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_less_nat_alt elim: add_less_mono1)

  thus ?thesis using ujk ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_less_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k < j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk le
  by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem] elim: add_less_mono1)

lemma word_add_less_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k < j + k) = (i < j)"
proof
  assume "i < j"
  show "i + k < j + k" by (rule word_add_less_mono1) fact+
next
  assume "i + k < j + k"
  show "i < j" by (rule word_add_less_dest) fact+
qed

lemma shiftr_div_2n':
  "unat (w >> n) = unat w div 2 ^ n"
  apply (unfold unat_def)
  apply (subst shiftr_div_2n)
  apply (subst nat_div_distrib)
   apply simp
  apply (simp add: nat_power_eq)
  done

lemma shiftl_shiftr_id:
  assumes nv: "n < len_of TYPE('a :: len)"
  and     xv: "x < 2 ^ (len_of TYPE('a :: len) - n)"
  shows "x << n >> n = (x::'a::len word)"
  apply (simp add: shiftl_t2n)
  apply (rule word_unat.Rep_eqD)
  apply (subst shiftr_div_2n')
  apply (cases n)
   apply simp
  apply (subst iffD1 [OF unat_mult_lem])+
   apply (subst unat_power_lower[OF nv])
   apply (rule nat_less_power_trans [OF _ order_less_imp_le [OF nv]])
   apply (rule order_less_le_trans [OF unat_mono [OF xv] order_eq_refl])
   apply (rule unat_power_lower)
   apply simp
  apply (subst unat_power_lower[OF nv])
  apply simp
  done

lemma word_mult_less_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k < j * k) = (i < j)"
proof
  assume "i < j"
  show "i * k < j * k" by (rule word_mult_less_mono1) fact+
next
  assume p: "i * k < j * k"

  have "0 < unat k" using knz by (simp add: word_less_nat_alt)
  thus "i < j" using p
    by (clarsimp simp: word_less_nat_alt iffD1 [OF unat_mult_lem uik]
      iffD1 [OF unat_mult_lem ujk])
qed

lemma word_le_imp_diff_le:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n \<le> m\<rbrakk> \<Longrightarrow> n - k \<le> m"
  by (clarsimp simp: unat_sub word_le_nat_alt intro!: le_imp_diff_le)

lemma word_less_imp_diff_less:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n < m\<rbrakk> \<Longrightarrow> n - k < m"
  by (clarsimp simp: unat_sub word_less_nat_alt
             intro!: less_imp_diff_less)

lemma word_mult_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k \<le> j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: mult_le_mono1)

  thus ?thesis using ujk knz ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_le_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k \<le> j * k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i * k \<le> j * k" by (rule word_mult_le_mono1) fact+
next
  assume p: "i * k \<le> j * k"

  have "0 < unat k" using knz by (simp add: word_less_nat_alt)
  thus "i \<le> j" using p
    by (clarsimp simp: word_le_nat_alt iffD1 [OF unat_mult_lem uik]
      iffD1 [OF unat_mult_lem ujk])
qed

lemma word_diff_less:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>0 < n; 0 < m; n \<le> m\<rbrakk> \<Longrightarrow> m - n < m"
  apply (subst word_less_nat_alt)
  apply (subst unat_sub)
   apply assumption
  apply (rule diff_less)
   apply (simp_all add: word_less_nat_alt)
   done

lemma MinI:
  assumes fa: "finite A"
  and     ne: "A \<noteq> {}"
  and     xv: "m \<in> A"
  and    min: "\<forall>y \<in> A. m \<le> y"
  shows "Min A = m" using fa ne xv min
proof (induct A arbitrary: m rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert y F)

  from insert.prems have yx: "m \<le> y" and fx: "\<forall>y \<in> F. m \<le> y" by auto
  have "m \<in> insert y F" by fact
  thus ?case
  proof
    assume mv: "m = y"

    have mlt: "m \<le> Min F"
      by (rule iffD2 [OF Min_ge_iff [OF insert.hyps(1) insert.hyps(2)] fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mv [symmetric])
      apply (rule iffD2 [OF linorder_min_same1 mlt])
      done
  next
    assume "m \<in> F"
    hence mf: "Min F = m"
      by (rule insert.hyps(4) [OF _ fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mf)
      apply (rule iffD2 [OF linorder_min_same2 yx])
      done
  qed
qed

lemma length_upto_enum [simp]:
  fixes a :: "('a :: len) word"
  shows "length [a .e. b] = Suc (unat b) - unat a"
  apply (simp add: word_le_nat_alt upto_enum_red)
  apply (clarsimp simp: Suc_diff_le)
  done

lemma length_upto_enum_less_one:
  "\<lbrakk>a \<le> b; b \<noteq> 0\<rbrakk>
  \<Longrightarrow> length [a .e. b - 1] = unat (b - a)"
  apply clarsimp
  apply (subst unat_sub[symmetric], assumption)
  apply clarsimp
  done

lemma drop_upto_enum:
  "drop (unat n) [0 .e. m] = [n .e. m]"
  apply (clarsimp simp: upto_enum_def)
  apply (induct m, simp)
  by (metis drop_map drop_upt plus_nat.add_0)

lemma distinct_enum_upto' [simp]:
  "distinct [a::'a::len word .e. b]"
  apply (subst drop_upto_enum [symmetric])
  apply (rule distinct_drop)
  apply (rule distinct_enum_upto)
  done

lemma length_interval:
  "\<lbrakk>set xs = {x. (a::'a::len word) \<le> x \<and> x \<le> b}; distinct xs\<rbrakk>
  \<Longrightarrow> length xs = Suc (unat b) - unat a"
  apply (frule distinct_card)
  apply (subgoal_tac "set xs = set [a .e. b]")
   apply (cut_tac distinct_card [where xs="[a .e. b]"])
    apply (subst (asm) length_upto_enum)
    apply clarsimp
   apply (rule distinct_enum_upto')
  apply simp
  done

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

declare of_nat_power [simp del]

(* TODO: move to word *)
lemma unat_of_bl_length:
  "unat (of_bl xs :: 'a::len word) < 2 ^ (length xs)"
proof (cases "length xs < len_of TYPE('a)")
  case True
  hence "(of_bl xs::'a::len word) < 2 ^ length xs"
    by (simp add: of_bl_length_less)
  with True
  show ?thesis
    by (simp add: word_less_nat_alt word_unat_power unat_of_nat)
next
  case False
  have "unat (of_bl xs::'a::len word) < 2 ^ len_of TYPE('a)"
    by (simp split: unat_split)
  also
  from False
  have "len_of TYPE('a) \<le> length xs" by simp
  hence "2 ^ len_of TYPE('a) \<le> (2::nat) ^ length xs"
    by (rule power_increasing) simp
  finally
  show ?thesis .
qed

lemma is_aligned_0'[simp]:
  "is_aligned 0 n"
  by (simp add: is_aligned_def)

lemma p_assoc_help:
  fixes p :: "'a::{ring,power,numeral,one}"
  shows "p + 2^sz - 1 = p + (2^sz - 1)"
  by simp

lemma word_add_increasing:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p + w \<le> x; p \<le> p + w \<rbrakk> \<Longrightarrow> p \<le> x"
  by unat_arith

lemma word_random:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p \<le> p + x'; x \<le> x' \<rbrakk> \<Longrightarrow> p \<le> p + x"
  by unat_arith

lemma word_sub_mono:
  "\<lbrakk> a \<le> c; d \<le> b; a - b \<le> a; c - d \<le> c \<rbrakk>
    \<Longrightarrow> (a - b) \<le> (c - d :: ('a :: len) word)"
  by unat_arith

lemma power_not_zero:
  "n < len_of TYPE('a::len) \<Longrightarrow> (2 :: 'a word) ^ n \<noteq> 0"
  by (metis p2_gt_0 word_neq_0_conv)

lemma word_gt_a_gt_0:
  "a < n \<Longrightarrow> (0 :: 'a::len word) < n"
  apply (case_tac "n = 0")
   apply clarsimp
  apply (clarsimp simp: word_neq_0_conv)
  done

lemma word_shift_nonzero:
  "\<lbrakk> (x\<Colon>'a\<Colon>len word) \<le> 2 ^ m; m + n < len_of TYPE('a\<Colon>len); x \<noteq> 0\<rbrakk>
   \<Longrightarrow> x << n \<noteq> 0"
  apply (simp only: word_neq_0_conv word_less_nat_alt
                    shiftl_t2n mod_0 unat_word_ariths
                    unat_power_lower word_le_nat_alt)
  apply (subst mod_less)
   apply (rule order_le_less_trans)
    apply (erule mult_le_mono2)
   apply (subst power_add[symmetric])
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply simp
  done

lemma word_power_less_1 [simp]:
  "sz < len_of TYPE('a\<Colon>len) \<Longrightarrow> (2::'a word) ^ sz - 1 < 2 ^ sz"
  apply (simp add: word_less_nat_alt word_bits_def)
  apply (subst unat_minus_one)
  apply (simp add: word_unat.Rep_inject [symmetric])
  apply simp
  done

lemmas word32_power_less_1[simp] =
       word_power_less_1[where 'a = 32, folded word_bits_def]

lemma nasty_split_lt:
  "\<lbrakk> (x :: 'a:: len word) < 2 ^ (m - n); n \<le> m; m < len_of TYPE('a\<Colon>len) \<rbrakk>
     \<Longrightarrow> x * 2 ^ n + (2 ^ n - 1) \<le> 2 ^ m - 1"
  apply (simp only: add_diff_eq word_bits_def)
  apply (subst mult_1[symmetric], subst distrib_right[symmetric])
  apply (rule word_sub_mono)
     apply (rule order_trans)
      apply (rule word_mult_le_mono1)
        apply (rule inc_le)
        apply assumption
       apply (subst word_neq_0_conv[symmetric])
       apply (rule power_not_zero)
       apply (simp add: word_bits_def)
      apply (subst unat_power_lower, simp)+
      apply (subst power_add[symmetric])
      apply (rule power_strict_increasing)
       apply (simp add: word_bits_def)
      apply simp
     apply (subst power_add[symmetric])
     apply simp
    apply simp
   apply (rule word_sub_1_le)
   apply (subst mult.commute)
   apply (subst shiftl_t2n[symmetric])
   apply (rule word_shift_nonzero)
     apply (erule inc_le)
    apply (simp add: word_bits_def)
   apply (unat_arith)
  apply (drule word_power_less_1[unfolded word_bits_def])
  apply simp
  done

lemma nasty_split_less:
  "\<lbrakk>m \<le> n; n \<le> nm; nm < len_of TYPE('a\<Colon>len); x < 2 ^ (nm - n)\<rbrakk>
   \<Longrightarrow> (x :: 'a word) * 2 ^ n + (2 ^ m - 1) < 2 ^ nm"
  apply (simp only: word_less_sub_le[symmetric])
  apply (rule order_trans [OF _ nasty_split_lt])
     apply (rule word_plus_mono_right)
      apply (rule word_sub_mono)
         apply (simp add: word_le_nat_alt)
        apply simp
       apply (simp add: word_sub_1_le[OF power_not_zero])
      apply (simp add: word_sub_1_le[OF power_not_zero])
     apply (rule is_aligned_no_wrap')
      apply (rule is_aligned_mult_triv2)
     apply simp
    apply (erule order_le_less_trans, simp)
   apply simp+
  done

lemma int_not_emptyD:
  "A \<inter> B \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<in> B"
  by (erule contrapos_np, clarsimp simp: disjoint_iff_not_equal)

lemma unat_less_power:
  fixes k :: "'a::len word"
  assumes szv: "sz < len_of TYPE('a)"
  and     kv:  "k < 2 ^ sz"
  shows   "unat k < 2 ^ sz"
  using szv unat_mono [OF kv] by simp

(* This should replace some crud \<dots> search for unat_of_nat *)
lemma unat_mult_power_lem:
  assumes kv: "k < 2 ^ (len_of TYPE('a::len) - sz)"
  shows "unat (2 ^ sz * of_nat k :: (('a::len) word)) = 2 ^ sz * k"
proof cases
  assume szv: "sz < len_of TYPE('a::len)"
  show ?thesis
  proof (cases "sz = 0")
    case True
    thus ?thesis using kv szv
     by (simp add: unat_of_nat)
  next
    case False
    hence sne: "0 < sz" ..

    have uk: "unat (of_nat k :: 'a word) = k"
      apply (subst unat_of_nat)
      apply (simp add: nat_mod_eq less_trans[OF kv] sne)
      done

    show ?thesis using szv
      apply (subst iffD1 [OF unat_mult_lem])
      apply (simp add: uk nat_less_power_trans[OF kv order_less_imp_le [OF szv]])+
      done
  qed
next
  assume "\<not> sz < len_of TYPE('a)"
  with kv show ?thesis by (simp add: not_less power_overflow)
qed

lemma aligned_add_offset_no_wrap:
  fixes off :: "('a::len) word"
  and     x :: "'a word"
  assumes al: "is_aligned x sz"
  and   offv: "off < 2 ^ sz"
  shows  "unat x + unat off < 2 ^ len_of TYPE('a)"
proof cases
  assume szv: "sz < len_of TYPE('a)"
  from al obtain k where xv: "x = 2 ^ sz * (of_nat k)"
    and kl: "k < 2 ^ (len_of TYPE('a) - sz)"
    by (auto elim: is_alignedE)

  show ?thesis using szv
    apply (subst xv)
    apply (subst unat_mult_power_lem[OF kl])
    apply (subst mult.commute, rule nat_add_offset_less)
      apply (rule less_le_trans[OF unat_mono[OF offv, simplified]])
      apply (erule eq_imp_le[OF unat_power_lower])
     apply (rule kl)
    apply simp
   done
next
  assume "\<not> sz < len_of TYPE('a)"
  with offv show ?thesis by (simp add: not_less power_overflow )
qed

lemma aligned_add_offset_mod:
  fixes x :: "('a::len) word"
  assumes al: "is_aligned x sz"
  and     kv: "k < 2 ^ sz"
  shows   "(x + k) mod 2 ^ sz = k"
proof cases
  assume szv: "sz < len_of TYPE('a)"

  have ux: "unat x + unat k < 2 ^ len_of TYPE('a)"
    by (rule aligned_add_offset_no_wrap) fact+

  show ?thesis using al szv
    apply -
    apply (erule is_alignedE)
    apply (subst word_unat.Rep_inject [symmetric])
    apply (subst unat_mod)
    apply (subst iffD1 [OF unat_add_lem], rule ux)
    apply simp
    apply (subst unat_mult_power_lem, assumption+)
    apply (subst mod_add_left_eq)
    apply (simp)
    apply (rule mod_less[OF less_le_trans[OF unat_mono], OF kv])
    apply (erule eq_imp_le[OF unat_power_lower])
    done
next
  assume "\<not> sz < len_of TYPE('a)"
  with al show ?thesis
    by (simp add: not_less power_overflow is_aligned_mask mask_def
                  word_mod_by_0)
qed

lemma word_plus_mcs_4:
  "\<lbrakk>v + x \<le> w + x; x \<le> v + x\<rbrakk> \<Longrightarrow> v \<le> (w::'a::len word)"
  by uint_arith

lemma word_plus_mcs_3:
  "\<lbrakk>v \<le> w; x \<le> w + x\<rbrakk> \<Longrightarrow> v + x \<le> w + (x::'a::len word)"
  by unat_arith

lemma aligned_neq_into_no_overlap:
  fixes x :: "'a::len word"
  assumes neq: "x \<noteq> y"
  and     alx: "is_aligned x sz"
  and     aly: "is_aligned y sz"
  shows  "{x .. x + (2 ^ sz - 1)} \<inter> {y .. y + (2 ^ sz - 1)} = {}"
proof cases
  assume szv: "sz < len_of TYPE('a)"
  show ?thesis
  proof (rule equals0I, clarsimp)
    fix z
    assume xb: "x \<le> z" and xt: "z \<le> x + (2 ^ sz - 1)"
      and yb: "y \<le> z" and yt: "z \<le> y + (2 ^ sz - 1)"

    have rl: "\<And>(p::'a word) k w. \<lbrakk>uint p + uint k < 2 ^ len_of TYPE('a); w = p + k; w \<le> p + (2 ^ sz - 1) \<rbrakk>
      \<Longrightarrow> k < 2 ^ sz"
      apply -
      apply simp
      apply (subst (asm) add.commute, subst (asm) add.commute, drule word_plus_mcs_4)
      apply (subst add.commute, subst no_plus_overflow_uint_size)
      apply (simp add: word_size_bl)
      apply (erule iffD1 [OF word_less_sub_le[OF szv]])
      done

    from xb obtain kx where
      kx: "z = x + kx" and
      kxl: "uint x + uint kx < 2 ^ len_of TYPE('a)"
      by (clarsimp dest!: word_le_exists')

    from yb obtain ky where
      ky: "z = y + ky" and
      kyl: "uint y + uint ky < 2 ^ len_of TYPE('a)"
      by (clarsimp dest!: word_le_exists')

    have "x = y"
    proof -
      have "kx = z mod 2 ^ sz"
      proof (subst kx, rule sym, rule aligned_add_offset_mod)
        show "kx < 2 ^ sz" by (rule rl) fact+
      qed fact+

      also have "\<dots> = ky"
      proof (subst ky, rule aligned_add_offset_mod)
        show "ky < 2 ^ sz"
          using kyl ky yt by (rule rl)
      qed fact+

      finally have kxky: "kx = ky" .
      moreover have "x + kx = y + ky" by (simp add: kx [symmetric] ky [symmetric])
      ultimately show ?thesis by simp
    qed

    thus False using neq by simp
  qed
next
  assume "\<not> sz < len_of TYPE('a)"
  with neq alx aly
  have False by (simp add: is_aligned_mask mask_def power_overflow)
  thus ?thesis ..
qed

lemma less_two_pow_divD:
  "\<lbrakk> (x :: nat) < 2 ^ n div 2 ^ m \<rbrakk>
    \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  apply (rule context_conjI)
   apply (rule ccontr)
   apply (simp add: power_strict_increasing)
  apply (simp add: power_sub)
  done

lemma less_two_pow_divI:
  "\<lbrakk> (x :: nat) < 2 ^ (n - m); m \<le> n \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  by (simp add: power_sub)

lemma word_less_two_pow_divI:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ (n - m); m \<le> n; n < len_of TYPE('a) \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  apply (simp add: word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply (rule order_le_less_trans [OF div_le_dividend])
   apply (rule unat_lt2p)
  apply (simp add: power_sub)
  done

lemma word_less_two_pow_divD:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ n div 2 ^ m \<rbrakk>
     \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  apply (cases "n < len_of TYPE('a)")
   apply (cases "m < len_of TYPE('a)")
    apply (simp add: word_less_nat_alt)
    apply (subst(asm) unat_word_ariths)
    apply (subst(asm) mod_less)
     apply (rule order_le_less_trans [OF div_le_dividend])
     apply (rule unat_lt2p)
    apply (clarsimp dest!: less_two_pow_divD)
   apply (simp add: power_overflow)
   apply (simp add: word_div_def)
  apply (simp add: power_overflow word_div_def)
  done

lemma of_nat_less_two_pow_div_set:
  "\<lbrakk> n < len_of TYPE('a) \<rbrakk> \<Longrightarrow>
   {x. x < (2 ^ n div 2 ^ m :: 'a::len word)}
      = of_nat ` {k. k < 2 ^ n div 2 ^ m}"
  apply (simp add: image_def)
  apply (safe dest!: word_less_two_pow_divD less_two_pow_divD
             intro!: word_less_two_pow_divI)
   apply (rule_tac x="unat x" in exI)
   apply (simp add: power_sub[symmetric])
   apply (subst unat_power_lower[symmetric, where 'a='a])
    apply simp
   apply (erule unat_mono)
  apply (subst word_unat_power)
  apply (rule of_nat_mono_maybe)
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply assumption
  done

(* FIXME: generalise! *)
lemma upto_2_helper:
  "{0..<2 :: word32} = {0, 1}"
  apply (safe, simp_all)
  apply unat_arith
  done

(* TODO: MOVE to word *)
lemma  word_less_power_trans2:
  fixes n :: "'a::len word"
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < len_of TYPE('a)\<rbrakk> \<Longrightarrow> n * 2 ^ k < 2 ^ m"
  by (subst field_simps, rule word_less_power_trans)

lemma ucast_less:
  "len_of TYPE('b) < len_of TYPE('a) \<Longrightarrow>
   (ucast (x :: ('b :: len) word) :: (('a :: len) word)) < 2 ^ len_of TYPE('b)"
  apply (subst mask_eq_iff_w2p[symmetric])
   apply (simp add: word_size)
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast)
  apply safe
  apply (simp add: test_bit.Rep[simplified])
  done

lemma ucast_less_shiftl_helper:
  "\<lbrakk> len_of TYPE('b) + 2 < word_bits;
     2 ^ (len_of TYPE('b) + 2) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: ('b :: len) word) << 2) < (n :: word32)"
  apply (erule order_less_le_trans[rotated])
  apply (cut_tac ucast_less[where x=x and 'a=32])
   apply (simp only: shiftl_t2n field_simps)
   apply (rule word_less_power_trans2)
     apply (simp_all add: word_bits_def)
  done

lemma ucast_range_less:
  "len_of TYPE('a :: len) < len_of TYPE('b :: len) \<Longrightarrow>
   range (ucast :: 'a word \<Rightarrow> 'b word)
       = {x. x < 2 ^ len_of TYPE ('a)}"
  apply safe
   apply (erule ucast_less)
  apply (simp add: image_def)
  apply (rule_tac x="ucast x" in exI)
  apply (drule less_mask_eq)
  apply (rule word_eqI)
  apply (drule_tac x=n in word_eqD)
  apply (simp add: word_size nth_ucast)
  done

lemma word_power_less_diff:
  "\<lbrakk>2 ^ n * q < (2::'a::len word) ^ m; q < 2 ^ (len_of TYPE('a) - n)\<rbrakk> \<Longrightarrow> q < 2 ^ (m - n)"
  apply (case_tac "m \<ge> len_of TYPE('a)")
   apply (simp add: power_overflow)
  apply (case_tac "n \<ge> len_of TYPE('a)")
   apply (simp add: power_overflow)
  apply (cases "n = 0")
   apply simp
  apply (subst word_less_nat_alt)
  apply (subst unat_power_lower)
   apply simp
  apply (rule nat_power_less_diff)
  apply (simp add: word_less_nat_alt)
  apply (subst (asm) iffD1 [OF unat_mult_lem])
   apply (simp add:nat_less_power_trans)
  apply simp
  done

lemmas word_diff_ls' = word_diff_ls [where xa=x and x=x for x, simplified]

lemmas word_l_diffs = word_l_diffs [where xa=x and x=x for x, simplified]

lemma is_aligned_diff:
  fixes m :: "'a::len word"
  assumes alm: "is_aligned m s1"
  and     aln: "is_aligned n s2"
  and    s2wb: "s2 < len_of TYPE('a)"
  and      nm: "m \<in> {n .. n + (2 ^ s2 - 1)}"
  and    s1s2: "s1 \<le> s2"
  and     s10: "0 < s1" (* Probably can be folded into the proof \<dots> *)
  shows  "\<exists>q. m - n = of_nat q * 2 ^ s1 \<and> q < 2 ^ (s2 - s1)"
proof -
  have rl: "\<And>m s. \<lbrakk> m < 2 ^ (len_of TYPE('a) - s); s < len_of TYPE('a) \<rbrakk> \<Longrightarrow> unat ((2::'a word) ^ s * of_nat m) = 2 ^ s * m"
  proof -
    fix m :: nat and  s
    assume m: "m < 2 ^ (len_of TYPE('a) - s)" and s: "s < len_of TYPE('a)"
    hence "unat ((of_nat m) :: 'a word) = m"
      apply (subst unat_of_nat)
      apply (subst mod_less)
       apply (erule order_less_le_trans)
       apply (rule power_increasing)
        apply simp_all
      done

    thus "?thesis m s" using s m
      apply (subst iffD1 [OF unat_mult_lem])
      apply (simp add: nat_less_power_trans)+
      done
  qed
  have s1wb: "s1 < len_of TYPE('a)" using s2wb s1s2 by simp
  from alm obtain mq where mmq: "m = 2 ^ s1 * of_nat mq" and mq: "mq < 2 ^ (len_of TYPE('a) - s1)"
    by (auto elim: is_alignedE simp: field_simps)
  from aln obtain nq where nnq: "n = 2 ^ s2 * of_nat nq" and nq: "nq < 2 ^ (len_of TYPE('a) - s2)"
    by (auto elim: is_alignedE simp: field_simps)
  from s1s2 obtain sq where sq: "s2 = s1 + sq" by (auto simp: le_iff_add)

  note us1 = rl [OF mq s1wb]
  note us2 = rl [OF nq s2wb]

  from nm have "n \<le> m" by clarsimp
  hence "(2::'a word) ^ s2 * of_nat nq \<le> 2 ^ s1 * of_nat mq" using nnq mmq by simp
  hence "2 ^ s2 * nq \<le> 2 ^ s1 * mq" using s1wb s2wb
    by (simp add: word_le_nat_alt us1 us2)
  hence nqmq: "2 ^ sq * nq \<le> mq" using sq by (simp add: power_add)

  have "m - n = 2 ^ s1 * of_nat mq - 2 ^ s2 * of_nat nq" using mmq nnq by simp
  also have "\<dots> = 2 ^ s1 * of_nat mq - 2 ^ s1 * 2 ^ sq * of_nat nq" using sq by (simp add: power_add)
  also have "\<dots> = 2 ^ s1 * (of_nat mq - 2 ^ sq * of_nat nq)" by (simp add: field_simps)
  also have "\<dots> = 2 ^ s1 * of_nat (mq - 2 ^ sq * nq)" using s1wb s2wb us1 us2 nqmq
    by (simp add:  word_unat_power)
  finally have mn: "m - n = of_nat (mq - 2 ^ sq * nq) * 2 ^ s1" by simp
  moreover
  from nm have "m - n \<le> 2 ^ s2 - 1"
    by - (rule word_diff_ls', (simp add: field_simps)+)
  hence "(2::'a word) ^ s1 * of_nat (mq - 2 ^ sq * nq) < 2 ^ s2" using mn s2wb by (simp add: field_simps)
  hence "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (s2 - s1)"
  proof (rule word_power_less_diff)
    have mm: "mq - 2 ^ sq * nq < 2 ^ (len_of TYPE('a) - s1)" using mq by simp
    moreover from s10 have "len_of TYPE('a) - s1 < len_of TYPE('a)"
      by (rule diff_less, simp)
    ultimately show "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (len_of TYPE('a) - s1)"
      apply (simp add: word_less_nat_alt)
      apply (subst unat_of_nat)
      apply (subst mod_less)
       apply (erule order_less_le_trans)
       apply simp+
      done
  qed
  hence "mq - 2 ^ sq * nq < 2 ^ (s2 - s1)" using mq s2wb
    apply (simp add: word_less_nat_alt)
    apply (subst (asm) unat_of_nat)
    apply (subst (asm) mod_less)
    apply (rule order_le_less_trans)
    apply (rule diff_le_self)
    apply (erule order_less_le_trans)
    apply simp
    apply assumption
    done
  ultimately show ?thesis by auto
qed

lemma word_less_sub_1:
  "x < (y :: ('a :: len) word) \<Longrightarrow> x \<le> y - 1"
  apply (erule udvd_minus_le')
   apply (simp add: udvd_def)+
  done

lemma word_sub_mono2:
  "\<lbrakk> a + b \<le> c + d; c \<le> a; b \<le> a + b; d \<le> c + d \<rbrakk>
    \<Longrightarrow> b \<le> (d :: ('a :: len) word)"
  apply (drule(1) word_sub_mono)
    apply simp
   apply simp
  apply simp
  done

lemma word_not_le:
  "(\<not> x \<le> (y :: ('a :: len) word)) = (y < x)"
  by fastforce

lemma word_subset_less:
  "\<lbrakk> {x .. x + r - 1} \<subseteq> {y .. y + s - 1};
     x \<le> x + r - 1; y \<le> y + (s :: ('a :: len) word) - 1;
     s \<noteq> 0 \<rbrakk>
     \<Longrightarrow> r \<le> s"
  apply (frule subsetD[where c=x])
   apply simp
  apply (drule subsetD[where c="x + r - 1"])
   apply simp
  apply (clarsimp simp: add_diff_eq[symmetric])
  apply (drule(1) word_sub_mono2)
    apply (simp_all add: olen_add_eqv[symmetric])
  apply (erule word_le_minus_cancel)
  apply (rule ccontr)
  apply (simp add: word_not_le)
  done

lemma two_power_strict_part_mono:
  "strict_part_mono {..31} (\<lambda>x. (2 :: word32) ^ x)"
  by (simp | subst strict_part_mono_by_steps)+

lemma uint_power_lower:
  "n < len_of TYPE('a) \<Longrightarrow> uint (2 ^ n :: 'a :: len word) = (2 ^ n :: int)"
  by (simp add: uint_nat int_power)

lemma power_le_mono:
  "\<lbrakk>2 ^ n \<le> (2::'a::len word) ^ m; n < len_of TYPE('a); m < len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> n \<le> m"
  apply (clarsimp simp add: le_less)
  apply safe
  apply (simp add: word_less_nat_alt)
  apply (simp only: uint_arith_simps(3))
  apply (drule uint_power_lower)+
  apply simp
  done

lemma sublist_equal_part:
  "xs \<le> ys \<Longrightarrow> take (length xs) ys = xs"
  by (clarsimp simp: prefixeq_def less_eq_list_def)

lemma take_n_subset_le:
  "\<lbrakk> {x. take n (to_bl x) = take n xs} \<subseteq> {y :: word32. take m (to_bl y) = take m ys};
     n \<le> 32; m \<le> 32; length xs = 32; length ys = 32 \<rbrakk>
    \<Longrightarrow> m \<le> n"
  apply (rule ccontr, simp add: le_def)
  apply (simp add: subset_iff)
  apply (drule spec[where x="of_bl (take n xs @ take (32 - n) (map Not (drop n ys)))"])
  apply (simp add: word_bl.Abs_inverse)
  apply (subgoal_tac "\<exists>p. m = n + p")
   apply clarsimp
   apply (simp add: take_add take_map_Not)
  apply (rule exI[where x="m - n"])
  apply simp
  done

lemma two_power_eq:
  "\<lbrakk>n < len_of TYPE('a); m < len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> ((2::'a::len word) ^ n = 2 ^ m) = (n = m)"
  apply safe
  apply (rule order_antisym)
   apply (simp add: power_le_mono[where 'a='a])+
  done

lemma less_list_def': "(xs < ys) = (prefix xs ys)"
  apply (metis prefix_order.eq_iff prefix_def less_list_def less_eq_list_def)
  done

lemma prefix_length_less:
  "xs < ys \<Longrightarrow> length xs < length ys"
  apply (clarsimp simp: less_list_def' prefix_def)
  apply (frule prefixeq_length_le)
  apply (rule ccontr, simp)
  apply (clarsimp simp: prefixeq_def)
  done

lemmas strict_prefix_simps [simp, code] = prefix_simps [folded less_list_def']
lemmas take_strict_prefix = take_prefix [folded less_list_def']

lemma not_prefix_longer:
  "\<lbrakk> length xs > length ys \<rbrakk> \<Longrightarrow> \<not> xs \<le> ys"
  by (clarsimp dest!: prefix_length_le)

lemma of_bl_length:
  "length xs < len_of TYPE('a) \<Longrightarrow> of_bl xs < (2 :: 'a::len word) ^ length xs"
  by (simp add: of_bl_length_less)

(* FIXME: do we need this? *)
lemma power_overflow_simp [simp]:
  "(2 ^ n = (0::'a :: len word)) = (len_of TYPE ('a) \<le> n)"
  by (rule WordLib.p2_eq_0)

lemma unat_of_nat_eq:
  "x < 2 ^ len_of TYPE('a) \<Longrightarrow> unat (of_nat x ::'a::len word) = x"
  by (simp add: unat_of_nat)

lemmas unat_of_nat32 = unat_of_nat_eq[where 'a=32, unfolded word_bits_len_of]

lemma unat_eq_of_nat:
  "n < 2 ^ len_of TYPE('a) \<Longrightarrow> (unat (x :: 'a::len word) = n) = (x = of_nat n)"
  by (subst unat_of_nat_eq[where x=n, symmetric], simp+)

lemma unat_less_helper:
  "x < of_nat n \<Longrightarrow> unat x < n"
  apply (simp add: word_less_nat_alt)
  apply (erule order_less_le_trans)
  apply (simp add: unat_of_nat)
  done

lemma of_nat_0:
  "\<lbrakk>of_nat n = (0::('a::len) word); n < 2 ^ len_of (TYPE('a))\<rbrakk> \<Longrightarrow> n = 0"
  by (drule unat_of_nat_eq, simp)

lemma of_nat32_0:
  "\<lbrakk>of_nat n = (0::word32); n < 2 ^ word_bits\<rbrakk> \<Longrightarrow> n = 0"
  by (erule of_nat_0, simp add: word_bits_def)

lemma unat_mask_2_less_4:
  "unat (p && mask 2 :: word32) < 4"
  apply (rule unat_less_helper)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_def)
  done

lemma minus_one_helper3:
  "x < y \<Longrightarrow> x \<le> (y :: ('a :: len) word) - 1"
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst unat_minus_one)
   apply clarsimp
  apply arith
  done

lemma minus_one_helper:
  "\<lbrakk> x \<le> y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x - 1 < (y :: ('a :: len) word)"
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst unat_minus_one)
   apply assumption
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma minus_one_helper5:
  fixes x :: "'a::len word"
  shows "\<lbrakk>y \<noteq> 0; x \<le> y - 1 \<rbrakk> \<Longrightarrow> x < y"
  by (metis leD minus_one_helper not_leE)

lemma plus_one_helper[elim!]:
  "x < n + (1 :: ('a :: len) word) \<Longrightarrow> x \<le> n"
  apply (simp add: word_less_nat_alt word_le_nat_alt field_simps)
  apply (case_tac "1 + n = 0")
   apply simp
  apply (subst(asm) unatSuc, assumption)
  apply arith
  done

lemma plus_one_helper2:
  "\<lbrakk> x \<le> n; n + 1 \<noteq> 0 \<rbrakk> \<Longrightarrow> x < n + (1 :: ('a :: len) word)"
  by (simp add: word_less_nat_alt word_le_nat_alt field_simps
                unatSuc)

lemma not_greatest_aligned:
  "\<lbrakk> x < y; is_aligned x n; is_aligned y n \<rbrakk>
      \<Longrightarrow> x + 2 ^ n \<noteq> 0"
  apply (rule notI)
  apply (erule is_aligned_get_word_bits[where p=y])
   apply (simp add: eq_diff_eq[symmetric])
   apply (frule minus_one_helper3)
   apply (drule le_minus'[where a="x" and c="y - x" and b="- 1" for x y, simplified])
   apply (simp add: field_simps)
   apply (frule is_aligned_less_sz[where a=y])
     apply clarsimp
   apply (erule notE)
   apply (rule minus_one_helper5)
    apply simp
   apply (metis is_aligned_no_overflow minus_one_helper3 order_le_less_trans)
  apply simp
  done

lemma of_nat_inj:
  "\<lbrakk>x < 2 ^ len_of TYPE('a); y < 2 ^ len_of TYPE('a)\<rbrakk> \<Longrightarrow>
   (of_nat x = (of_nat y :: 'a :: len word)) = (x = y)"
  by (simp add: word_unat.norm_eq_iff [symmetric])

lemma map_prefixI:
  "xs \<le> ys \<Longrightarrow> map f xs \<le> map f ys"
  by (clarsimp simp: less_eq_list_def prefixeq_def)

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

lemma list_all2_induct [consumes 1, case_names Nil Cons]:
  assumes lall: "list_all2 Q xs ys"
  and     nilr: "P [] []"
  and    consr: "\<And>x xs y ys. \<lbrakk>list_all2 Q xs ys; Q x y; P xs ys\<rbrakk> \<Longrightarrow> P (x # xs) (y # ys)"
  shows  "P xs ys"
  using lall
proof (induct rule: list_induct2 [OF list_all2_lengthD [OF lall]])
  case 1 thus ?case by auto fact+
next
  case (2 x xs y ys)

  show ?case
  proof (rule consr)
    from "2.prems" show "list_all2 Q xs ys" and "Q x y" by simp_all
    thus "P xs ys" by (intro "2.hyps")
  qed
qed

lemma list_all2_induct_suffixeq [consumes 1, case_names Nil Cons]:
  assumes lall: "list_all2 Q as bs"
  and     nilr: "P [] []"
  and    consr: "\<And>x xs y ys.
  \<lbrakk>list_all2 Q xs ys; Q x y; P xs ys; suffixeq (x # xs) as; suffixeq (y # ys) bs\<rbrakk>
  \<Longrightarrow> P (x # xs) (y # ys)"
  shows  "P as bs"
proof -
  def as' == as
  def bs' == bs

  have "suffixeq as as' \<and> suffixeq bs bs'" unfolding as'_def bs'_def by simp
  thus ?thesis using lall
  proof (induct rule: list_induct2 [OF list_all2_lengthD [OF lall]])
    case 1 show ?case by fact
  next
    case (2 x xs y ys)

    show ?case
    proof (rule consr)
      from "2.prems" show "list_all2 Q xs ys" and "Q x y" by simp_all
      thus "P xs ys" using "2.hyps" "2.prems" by (auto dest: suffixeq_ConsD)
      from "2.prems" show "suffixeq (x # xs) as" and "suffixeq (y # ys) bs"
	by (auto simp: as'_def bs'_def)
    qed
  qed
qed

lemma distinct_prop_enum:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<le> stop; y \<le> stop; x \<noteq> y \<rbrakk>
             \<Longrightarrow> P x y \<rbrakk>
     \<Longrightarrow> distinct_prop P [(0 :: word32) .e. stop]"
  apply (simp add: upto_enum_def distinct_prop_map
              del: upt.simps)
  apply (rule distinct_prop_distinct)
   apply simp
  apply (simp add: less_Suc_eq_le del: upt.simps)
  apply (erule_tac x="of_nat x" in meta_allE)
  apply (erule_tac x="of_nat y" in meta_allE)
  apply (frule_tac y=x in unat_le)
  apply (frule_tac y=y in unat_le)
  apply (erule word_unat.Rep_cases)+
  apply (simp add: toEnum_of_nat[OF unat_lt2p]
                   word_le_nat_alt)
  done

lemma distinct_prop_enum_step:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<le> stop div step; y \<le> stop div step; x \<noteq> y \<rbrakk>
             \<Longrightarrow> P (x * step) (y * step) \<rbrakk>
     \<Longrightarrow> distinct_prop P [0, step .e. stop]"
  apply (simp add: upto_enum_step_def distinct_prop_map)
  apply (rule distinct_prop_enum)
  apply simp
  done

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

lemma word32_shift_by_2:
  "x * 4 = (x::word32) << 2"
  by (simp add: shiftl_t2n)

(* TODO: move to Aligned *)
lemma add_mask_lower_bits:
  "\<lbrakk>is_aligned (x :: 'a :: len word) n;
    \<forall>n' \<ge> n. n' < len_of TYPE('a) \<longrightarrow> \<not> p !! n'\<rbrakk> \<Longrightarrow> x + p && ~~mask n = x"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size is_aligned_nth)
   apply (erule_tac x=na in allE)+
   apply simp
  apply (rule word_eqI)
  apply (clarsimp simp: word_size is_aligned_nth word_ops_nth_size)
  apply (erule_tac x=na in allE)+
  apply (case_tac "na < n")
   apply simp
  apply simp
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

lemma maxBound_word:
  "(maxBound::'a::len word) = -1"
  apply (simp add: maxBound_def enum_word_def)
  apply (subst last_map)
   apply clarsimp
  apply simp
  done

lemma minBound_word:
  "(minBound::'a::len word) = 0"
  apply (simp add: minBound_def enum_word_def)
  apply (subst map_upt_unfold)
   apply simp
  apply simp
  done

lemma maxBound_max_word:
  "(maxBound::'a::len word) = max_word"
  apply (subst maxBound_word)
  apply (subst max_word_minus [symmetric])
  apply (rule refl)
  done

lemma leq_maxBound [simp]:
  "(x::'a::len word) \<le> maxBound"
  by (simp add: maxBound_max_word)

lemma is_aligned_andI1:
  "is_aligned x n \<Longrightarrow> is_aligned (x && y) n"
  by (simp add: is_aligned_nth)

lemma is_aligned_andI2:
  "is_aligned y n \<Longrightarrow> is_aligned (x && y) n"
  by (simp add: is_aligned_nth)

lemma is_aligned_shiftl:
  "is_aligned w (n - m) \<Longrightarrow> is_aligned (w << m) n"
  by (simp add: is_aligned_nth nth_shiftl)

lemma is_aligned_shiftr:
  "is_aligned w (n + m) \<Longrightarrow> is_aligned (w >> m) n"
  by (simp add: is_aligned_nth nth_shiftr)

lemma is_aligned_shiftl_self:
  "is_aligned (p << n) n"
  by (rule is_aligned_shiftl) simp

lemma is_aligned_neg_mask_eq:
  "is_aligned p n \<Longrightarrow> p && ~~ mask n = p"
  apply (simp add: is_aligned_nth)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size word_ops_nth_size)
  apply fastforce
  done

lemma is_aligned_shiftr_shiftl:
  "is_aligned w n \<Longrightarrow> w >> n << n = w"
  apply (simp add: shiftr_shiftl1)
  apply (erule is_aligned_neg_mask_eq)
  done

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

lemma upto_enum_step_shift:
  "\<lbrakk> is_aligned p n \<rbrakk> \<Longrightarrow>
  ([p , p + 2 ^ m .e. p + 2 ^ n - 1])
      = map (op + p) [0, 2 ^ m .e. 2 ^ n - 1]"
  apply (erule is_aligned_get_word_bits)
   prefer 2
   apply (simp add: map_idI)
  apply (clarsimp simp: upto_enum_step_def)
  apply (frule is_aligned_no_overflow)
  apply (simp add: linorder_not_le [symmetric])
  done

lemma upto_enum_step_shift_red:
  "\<lbrakk> is_aligned p sz; sz < word_bits; us \<le> sz \<rbrakk>
     \<Longrightarrow> [p, p + 2 ^ us .e. p + 2 ^ sz - 1]
          = map (\<lambda>x. p + of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]"
  apply (subst upto_enum_step_shift, assumption)
  apply (simp add: upto_enum_step_red)
  done

lemma div_to_mult_word_lt:
  "\<lbrakk> (x :: ('a :: len) word) \<le> y div z \<rbrakk> \<Longrightarrow> x * z \<le> y"
  apply (cases "z = 0")
   apply simp
  apply (simp add: word_neq_0_conv)
  apply (rule order_trans)
   apply (erule(1) word_mult_le_mono1)
   apply (simp add: unat_div)
   apply (rule order_le_less_trans [OF div_mult_le])
   apply simp
  apply (rule word_div_mult_le)
  done

lemma upto_enum_step_subset:
  "set [x, y .e. z] \<subseteq> {x .. z}"
  apply (clarsimp simp: upto_enum_step_def linorder_not_less)
  apply (drule div_to_mult_word_lt)
  apply (rule conjI)
   apply (erule word_random[rotated])
   apply simp
  apply (rule order_trans)
   apply (erule word_plus_mono_right)
   apply simp
  apply simp
  done

lemma shiftr_less_t2n':
  fixes x :: "('a :: len) word"
  shows "\<lbrakk> x && mask (n + m) = x; m < len_of TYPE('a) \<rbrakk>
              \<Longrightarrow> (x >> n) < 2 ^ m"
  apply (subst mask_eq_iff_w2p[symmetric])
   apply (simp add: word_size)
  apply (rule word_eqI)
  apply (drule_tac x="na + n" in word_eqD)
  apply (simp add: nth_shiftr word_size)
  apply safe
  done

lemma shiftr_less_t2n:
  fixes x :: "('a :: len) word"
  shows "x < 2 ^ (n + m) \<Longrightarrow> (x >> n) < 2 ^ m"
  apply (rule shiftr_less_t2n')
   apply (erule less_mask_eq)
  apply (rule ccontr)
  apply (simp add: not_less)
  apply (subst (asm) p2_eq_0[symmetric])
  apply (simp add: power_add)
  done

lemma shiftr_eq_0:
  "n \<ge> len_of TYPE('a :: len) \<Longrightarrow> ((w::('a::len word)) >> n) = 0"
apply (cut_tac shiftr_less_t2n'[of w n 0], simp)
 apply (simp add: mask_eq_iff)
apply (simp add: lt2p_lem)
apply simp
done

lemma shiftr_not_mask_0:
  "n+m\<ge>len_of TYPE('a :: len) \<Longrightarrow> ((w::('a::len word)) >> n) && ~~ mask m = 0"
  apply (simp add: and_not_mask shiftr_less_t2n shiftr_shiftr)
  apply (subgoal_tac "w >> n + m = 0", simp)
  apply (simp add: le_mask_iff[symmetric] mask_def le_def)
  apply (subst (asm) p2_gt_0[symmetric])
  apply (simp add: power_add not_less)
done

lemma shiftl_less_t2n:
  fixes x :: "('a :: len) word"
  shows "\<lbrakk> x < (2 ^ (m - n)); m < len_of TYPE('a) \<rbrakk> \<Longrightarrow> (x << n) < 2 ^ m"
  apply (subst mask_eq_iff_w2p[symmetric])
   apply (simp add: word_size)
  apply (drule less_mask_eq)
  apply (rule word_eqI)
  apply (drule_tac x="na - n" in word_eqD)
  apply (simp add: nth_shiftl word_size)
  apply (cases "n \<le> m")
   apply safe
   apply simp
  apply simp
  done

lemma shiftl_less_t2n':
  "(x::'a::len word) < 2 ^ m \<Longrightarrow> m+n < len_of TYPE('a) \<Longrightarrow> x << n < 2 ^ (m + n)"
by (rule shiftl_less_t2n) simp_all

lemma ucast_ucast_mask:
  "(ucast :: ('a :: len) word \<Rightarrow> ('b :: len) word) (ucast x) = x && mask (len_of TYPE ('a))"
  apply (rule word_eqI)
  apply (simp add: nth_ucast word_size)
  done

lemma ucast_ucast_len:
  "\<lbrakk> x < 2 ^ len_of TYPE('b) \<rbrakk> \<Longrightarrow>
  ucast (ucast x::'b::len word) = (x::'a::len word)"
  apply (subst ucast_ucast_mask)
  apply (erule less_mask_eq)
  done

lemma unat_ucast: "unat (ucast x :: ('a :: len0) word) = unat x mod 2 ^ (len_of TYPE('a))"
  apply (simp add: unat_def ucast_def)
  apply (subst word_uint.eq_norm)
  apply (subst nat_mod_distrib)
    apply simp
   apply simp
  apply (subst nat_power_eq)
   apply simp
  apply simp
  done

lemma ucast_less_ucast:
  "len_of TYPE('a) < len_of TYPE('b) \<Longrightarrow>
   (ucast x < ((ucast (y :: ('a::len) word)) :: ('b::len) word)) = (x < y)"
  apply (simp add: word_less_nat_alt unat_ucast)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply simp
  done

lemma sints_subset:
  "m \<le> n \<Longrightarrow> sints m \<subseteq> sints n"
  apply (simp add: sints_num)
  apply clarsimp
  apply (rule conjI)
   apply (erule order_trans[rotated])
   apply simp
  apply (erule order_less_le_trans)
  apply simp
  done

lemma up_scast_inj:
      "\<lbrakk> scast x = (scast y :: ('b :: len) word); size x \<le> len_of TYPE('b) \<rbrakk>
         \<Longrightarrow> x = y"
  apply (simp add: scast_def)
  apply (subst(asm) word_sint.Abs_inject)
    apply (erule subsetD [OF sints_subset])
    apply (simp add: word_size)
   apply (erule subsetD [OF sints_subset])
   apply (simp add: word_size)
  apply simp
  done

lemma up_scast_inj_eq:
  "len_of TYPE('a) \<le> len_of TYPE ('b) \<Longrightarrow> (scast x = (scast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_scast_inj simp: word_size)

lemma nth_bounded:
  "\<lbrakk>(x :: 'a :: len word) !! n; x < 2 ^ m; m \<le> len_of TYPE ('a)\<rbrakk> \<Longrightarrow> n < m"
  apply (frule test_bit_size)
  apply (clarsimp simp: test_bit_bl word_size)
  apply (simp add: nth_rev)
  apply (subst(asm) is_aligned_add_conv[OF is_aligned_0',
                                        simplified add_0_left, rotated])
   apply assumption+
  apply (simp only: to_bl_0 word_bits_len_of)
  apply (simp add: nth_append split: split_if_asm)
  done

lemma is_aligned_add_or:
  "\<lbrakk>is_aligned p n; d < 2 ^ n\<rbrakk> \<Longrightarrow> p + d = p || d"
  apply (rule word_plus_and_or_coroll)
  apply (erule is_aligned_get_word_bits)
   apply (rule word_eqI)
   apply (clarsimp simp add: is_aligned_nth)
   apply (frule(1) nth_bounded)
    apply simp+
  done

lemma two_power_increasing:
  "\<lbrakk> n \<le> m; m < len_of TYPE('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ n \<le> 2 ^ m"
  by (simp add: word_le_nat_alt)

lemma is_aligned_add_less_t2n:
  "\<lbrakk>is_aligned (p\<Colon>'a\<Colon>len word) n; d < 2^n; n \<le> m; p < 2^m\<rbrakk> \<Longrightarrow> p + d < 2^m"
  apply (case_tac "m < len_of TYPE('a)")
   apply (subst mask_eq_iff_w2p[symmetric])
    apply (simp add: word_size)
   apply (simp add: is_aligned_add_or word_ao_dist less_mask_eq)
   apply (subst less_mask_eq)
    apply (erule order_less_le_trans)
    apply (erule(1) two_power_increasing)
   apply simp
  apply (simp add: power_overflow)
  done

(* FIXME: generalise? *)
lemma le_2p_upper_bits:
  "\<lbrakk> (p::word32) \<le> 2^n - 1; n < word_bits \<rbrakk> \<Longrightarrow> \<forall>n'\<ge>n. n' < word_bits \<longrightarrow> \<not> p !! n'"
  apply (subst upper_bits_unset_is_l2p, assumption)
  apply simp
  done

lemma ran_upd':
  "\<lbrakk>inj_on f (dom f); f y = Some z\<rbrakk>
  \<Longrightarrow> ran (f (y := None)) = ran f - {z}"
  apply (drule (1) ran_upd)
  apply (simp add: ran_def)
  done

(* FIXME: generalise? *)
lemma le2p_bits_unset:
  "p \<le> 2 ^ n - 1 \<Longrightarrow> \<forall>n'\<ge>n. n' < word_bits \<longrightarrow> \<not> (p::word32) !! n'"
  apply (case_tac "n < word_bits")
   apply (frule upper_bits_unset_is_l2p [where p=p])
   apply simp_all
  done

lemma aligned_offset_non_zero:
  "\<lbrakk> is_aligned x n; y < 2 ^ n; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  apply (cases "y = 0")
   apply simp
  apply (subst word_neq_0_conv)
  apply (subst gt0_iff_gem1)
  apply (erule is_aligned_get_word_bits)
   apply (subst field_simps[symmetric], subst plus_le_left_cancel_nowrap)
     apply (rule is_aligned_no_wrap')
      apply simp
     apply (rule minus_one_helper)
      apply simp
     apply assumption
    apply (erule (1) is_aligned_no_wrap')
   apply (simp add: gt0_iff_gem1 [symmetric] word_neq_0_conv)
  apply simp
  done

lemma le_imp_power_dvd_int:
  "n \<le> m \<Longrightarrow> (b ^ n :: int) dvd b ^ m"
  apply (simp add: dvd_def)
  apply (rule exI[where x="b ^ (m - n)"])
  apply (simp add: power_add[symmetric])
  done

    (* FIXME: this is identical to mask_eqs(1), unnecessary? *)
lemma mask_inner_mask:
  "((p && mask n) + q) && mask n
       = (p + q) && mask n"
  apply (rule mask_eqs(1))
  done

lemma mask_add_aligned:
  "is_aligned p n
     \<Longrightarrow> (p + q) && mask n = q && mask n"
  apply (simp add: is_aligned_mask)
  apply (subst mask_inner_mask [symmetric])
  apply simp
  done

lemma take_prefix:
  "(take (length xs) ys = xs) = (xs \<le> ys)"
proof (induct xs arbitrary: ys)
  case Nil thus ?case by simp
next
  case Cons thus ?case by (cases ys) auto
qed

lemma rel_comp_Image:
  "(R O R') `` S = R' `` (R `` S)"
  by blast

lemma trancl_power:
  "x \<in> r^+ = (\<exists>n > 0. x \<in> r^^n)"
  apply (cases x)
  apply simp
  apply (rule iffI)
   apply (drule tranclD2)
   apply (clarsimp simp: rtrancl_is_UN_relpow)
   apply (rule_tac x="Suc n" in exI)
   apply fastforce
  apply clarsimp
  apply (case_tac n, simp)
  apply clarsimp
  apply (drule relpow_imp_rtrancl)
  apply fastforce
  done

lemma take_is_prefix:
  "take n xs \<le> xs"
  apply (simp add: less_eq_list_def prefixeq_def)
  apply (rule_tac x="drop n xs" in exI)
  apply simp
  done

lemma cart_singleton_empty:
  "(S \<times> {e} = {}) = (S = {})"
  by blast

lemma word_div_1:
  "(n :: ('a :: len) word) div 1 = n"
  by (simp add: word_div_def)

lemma word_minus_one_le:
  "-1 \<le> (x :: ('a :: len) word) = (x = -1)"
  apply (insert word_n1_ge[where y=x])
  apply safe
  apply (erule(1) order_antisym)
  done

lemmas word32_minus_one_le =
    word_minus_one_le[where 'a=32, simplified]

lemma mask_out_sub_mask:
  "(x && ~~ mask n) = x - (x && mask n)"
  by (simp add: field_simps word_plus_and_or_coroll2)

lemma is_aligned_addD1:
  assumes al1: "is_aligned (x + y) n"
  and     al2: "is_aligned (x::'a::len word) n"
  shows "is_aligned y n"
  using al2
proof (rule is_aligned_get_word_bits)
  assume "x = 0" thus ?thesis using al1 by simp
next
  assume nv: "n < len_of TYPE('a)"
  from al1 obtain q1
    where xy: "x + y = 2 ^ n * of_nat q1" and "q1 < 2 ^ (len_of TYPE('a) - n)"
    by (rule is_alignedE)
  moreover from al2 obtain q2
    where x: "x = 2 ^ n * of_nat q2" and "q2 < 2 ^ (len_of TYPE('a) - n)"
    by (rule is_alignedE)
  ultimately have "y = 2 ^ n * (of_nat q1 - of_nat q2)"
    by (simp add: field_simps)
  thus ?thesis using nv by (simp add: is_aligned_mult_triv1)
qed

lemmas is_aligned_addD2 =
       is_aligned_addD1[OF subst[OF add.commute,
                                 of "%x. is_aligned x n" for n]]

lemma is_aligned_add:
  "\<lbrakk>is_aligned p n; is_aligned q n\<rbrakk> \<Longrightarrow> is_aligned (p + q) n"
  by (simp add: is_aligned_mask mask_add_aligned)

lemma my_BallE: "\<lbrakk> \<forall>x \<in> A. P x; y \<in> A; P y \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (simp add: Ball_def)

lemma word_le_add:
  fixes x :: "'a :: len word"
  shows "x \<le> y \<Longrightarrow> \<exists>n. y = x + of_nat n"
  apply (rule exI [where x = "unat (y - x)"])
  apply simp
  done

lemma word_plus_mcs_4':
  fixes x :: "'a :: len word"
  shows "\<lbrakk>x + v \<le> x + w; x \<le> x + v\<rbrakk> \<Longrightarrow> v \<le> w"
  apply (rule word_plus_mcs_4)
   apply (simp add: add.commute)
  apply (simp add: add.commute)
  done

lemma zipWith_nth:
  "\<lbrakk> n < min (length xs) (length ys) \<rbrakk> \<Longrightarrow> zipWith f xs ys ! n = f (xs ! n) (ys ! n)"
  unfolding zipWith_def by simp

lemma length_zipWith:
  "length (zipWith f xs ys) = min (length xs) (length ys)"
  unfolding zipWith_def by simp

lemma distinct_prop_nth:
  "\<lbrakk> distinct_prop P ls; n < n'; n' < length ls \<rbrakk> \<Longrightarrow> P (ls ! n) (ls ! n')"
  apply (induct ls arbitrary: n n')
   apply simp
  apply simp
  apply (case_tac n')
   apply simp
  apply simp
  apply (case_tac n)
   apply simp
  apply simp
  done

lemma shiftl_mask_is_0 :
  "(x << n) && mask n = 0"
  apply (rule iffD1 [OF is_aligned_mask])
  apply (rule is_aligned_shiftl_self)
  done

lemma word_power_nonzero:
  "\<lbrakk> (x :: word32) < 2 ^ (word_bits - n); n < word_bits; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x * 2 ^ n \<noteq> 0"
  apply (cases "n = 0")
   apply simp
  apply (simp only: word_neq_0_conv word_less_nat_alt
                    shiftl_t2n mod_0 unat_word_ariths
                    unat_power_lower word_le_nat_alt word_bits_def)
  apply (unfold word_bits_len_of)
  apply (subst mod_less)
   apply (subst mult.commute, erule nat_less_power_trans)
   apply simp
  apply simp
  done

lemmas unat_mult_simple = iffD1 [OF unat_mult_lem [where 'a = 32, unfolded word_bits_len_of]]

definition
  sum_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a + 'c \<Rightarrow> 'b + 'd" where
 "sum_map f g x \<equiv> case x of Inl v \<Rightarrow> Inl (f v) | Inr v' \<Rightarrow> Inr (g v')"

lemma sum_map_simps[simp]:
  "sum_map f g (Inl v) = Inl (f v)"
  "sum_map f g (Inr w) = Inr (g w)"
  by (simp add: sum_map_def)+

lemma if_and_helper:
  "(If x v v') && v'' = If x (v && v'') (v' && v'')"
  by (simp split: split_if)

lemma unat_Suc2:
  fixes n :: "('a :: len) word"
  shows
  "n \<noteq> -1 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  apply (subst add.commute, rule unatSuc)
  apply (subst eq_diff_eq[symmetric], simp add: minus_equation_iff)
  done

lemmas unat_eq_1
    = unat_eq_0 word_unat.Rep_inject[where y=1, simplified]

lemma cart_singleton_image:
  "S \<times> {s} = (\<lambda>v. (v, s)) ` S"
  by auto

lemma singleton_eq_o2s:
  "({x} = set_option v) = (v = Some x)"
  by (cases v, auto)

lemma ran_option_map_restrict_eq:
  "\<lbrakk> x \<in> ran (option_map f o g); x \<notin> ran (option_map f o (g |` (- {y}))) \<rbrakk>
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

lemma option_map_comp2:
  "option_map (f o g) = option_map f o option_map g"
  by (simp add: option.map_comp fun_eq_iff)

lemma rshift_sub_mask_eq:
  "(a >> (size a - b)) && mask b = a >> (size a - b)"
  using shiftl_shiftr2[where a=a and b=0 and c="size a - b"]
  apply (cases "b < size a")
   apply simp
  apply (simp add: linorder_not_less mask_def word_size
                   p2_eq_0[THEN iffD2])
  done

lemma shiftl_shiftr3:
  "b \<le> c \<Longrightarrow> a << b >> c = (a >> c - b) && mask (size a - c)"
  apply (cases "b = c")
   apply (simp add: shiftl_shiftr1)
  apply (simp add: shiftl_shiftr2)
  done

lemma and_mask_shiftr_comm:
  "m\<le>size w \<Longrightarrow> (w && mask m) >> n = (w >> n) && mask (m-n)"
   by (simp add: and_mask shiftr_shiftr) (simp add: word_size shiftl_shiftr3)

lemma and_mask_shiftl_comm:
  "m+n \<le> size w \<Longrightarrow> (w && mask m) << n = (w << n) && mask (m+n)"
  by (simp add: and_mask word_size shiftl_shiftl) (simp add: shiftl_shiftr1)

lemma and_not_mask_twice:
  "(w && ~~ mask n) && ~~ mask m = w && ~~ mask (max m n)"
apply (simp add: and_not_mask)
apply (case_tac "n<m")
 apply (simp_all add: shiftl_shiftr2 shiftl_shiftr1 not_less max_def
                      shiftr_shiftr shiftl_shiftl)
 apply (cut_tac and_mask_shiftr_comm
                [where w=w and m="size w" and n=m, simplified,symmetric])
 apply (simp add: word_size mask_def)
apply (cut_tac and_mask_shiftr_comm
               [where w=w and m="size w" and n=n, simplified,symmetric])
apply (simp add: word_size mask_def)
done

(* FIXME: move *)
lemma word_less_cases:
  "x < y \<Longrightarrow> x = y - 1 \<or> x < y - (1 ::'a::len word)"
  apply (drule word_less_sub_1)
  apply (drule order_le_imp_less_or_eq)
  apply auto
  done

lemma eq_eqI:
  "a = b \<Longrightarrow> (a = x) = (b = x)"
  by simp

lemma mask_and_mask:
  "mask a && mask b = mask (min a b)"
  apply (rule word_eqI)
  apply (simp add: word_size)
  done

lemma mask_eq_0_eq_x:
  "(x && w = 0) = (x && ~~ w = x)"
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

lemma mask_eq_x_eq_0:
  "(x && w = x) = (x && ~~ w = 0)"
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

definition
  "limited_and (x :: ('a :: len) word) y = (x && y = x)"

lemma limited_and_eq_0:
  "\<lbrakk> limited_and x z; y && ~~ z = y \<rbrakk> \<Longrightarrow> x && y = 0"
  unfolding limited_and_def
  apply (subst arg_cong2[where f="op &&"])
    apply (erule sym)+
  apply (simp(no_asm) add: word_bw_assocs word_bw_comms word_bw_lcs)
  done

lemma limited_and_eq_id:
  "\<lbrakk> limited_and x z; y && z = z \<rbrakk> \<Longrightarrow> x && y = x"
  unfolding limited_and_def
  by (erule subst, fastforce simp: word_bw_lcs word_bw_assocs word_bw_comms)

lemma lshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x << n) (z << n)"
  unfolding limited_and_def
  by (simp add: shiftl_over_and_dist[symmetric])

lemma rshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x >> n) (z >> n)"
  unfolding limited_and_def
  by (simp add: shiftr_over_and_dist[symmetric])

lemmas limited_and_simps1 = limited_and_eq_0 limited_and_eq_id

lemmas is_aligned_limited_and
    = is_aligned_neg_mask_eq[unfolded mask_def, folded limited_and_def]

lemma compl_of_1: "~~ 1 = (-2 :: ('a :: len) word)"
  apply (rule word_bool_alg.compl_eq_compl_iff[THEN iffD1])
  apply simp
  done

lemmas limited_and_simps = limited_and_simps1
       limited_and_simps1[OF is_aligned_limited_and]
       limited_and_simps1[OF lshift_limited_and]
       limited_and_simps1[OF rshift_limited_and]
       limited_and_simps1[OF rshift_limited_and, OF is_aligned_limited_and]
       compl_of_1 shiftl_shiftr1[unfolded word_size mask_def]
       shiftl_shiftr2[unfolded word_size mask_def]

lemma isRight_case_sum: "isRight x \<Longrightarrow> case_sum f g x = g (theRight x)"
  by (clarsimp simp add: isRight_def)

lemma split_word_eq_on_mask:
  "(x = y) = (x && m = y && m \<and> x && ~~ m = y && ~~ m)"
  apply safe
  apply (rule word_eqI)
  apply (drule_tac x=n in word_eqD)+
  apply (simp add: word_size word_ops_nth_size)
  apply auto
  done

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

lemma ucast_not_helper:
  fixes a::word8
  assumes a: "a \<noteq> 0xFF"
  shows "ucast a \<noteq> (0xFF::word32)"
proof
  assume "ucast a = (0xFF::word32)"
  also
  have "(0xFF::word32) = ucast (0xFF::word8)" by simp
  finally
  show False using a
    apply -
    apply (drule up_ucast_inj, simp)
    apply simp
    done
qed

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
  by (rule hd_drop_conv_nth, clarsimp+)

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

lemma less_4_cases:
  "(x::word32) < 4 \<Longrightarrow> x=0 \<or> x=1 \<or> x=2 \<or> x=3"
  apply clarsimp
  apply (drule word_less_cases, erule disjE, simp, simp)+
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

lemma option_map_Some_eq2:
  "(Some y = option_map f x) = (\<exists>z. x = Some z \<and> f z = y)"
  by (metis map_option_eq_Some)

lemma option_map_eq_dom_eq:
  assumes ome: "option_map f \<circ> g = option_map f \<circ> g'"
  shows   "dom g = dom g'"
proof (rule set_eqI)
  fix x
  {
    assume "x \<in> dom g"
    hence "Some (f (the (g x))) = (option_map f \<circ> g) x"
      by (auto simp: map_option_case split: option.splits)
    also have "\<dots> = (option_map f \<circ> g') x" by (simp add: ome)
    finally have "x \<in> dom g'"
      by (auto simp: map_option_case split: option.splits)
  } moreover
  {
    assume "x \<in> dom g'"
    hence "Some (f (the (g' x))) = (option_map f \<circ> g') x"
      by (auto simp: map_option_case split: option.splits)
    also have "\<dots> = (option_map f \<circ> g) x" by (simp add: ome)
    finally have "x \<in> dom g"
      by (auto simp: map_option_case split: option.splits)
  } ultimately show "(x \<in> dom g) = (x \<in> dom g')" by auto
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

lemma is_aligned_0:
  "is_aligned 0 n"
  unfolding is_aligned_def
  by simp

lemma compD:
  "\<lbrakk>f \<circ> g = f \<circ> g'; g x = v \<rbrakk> \<Longrightarrow> f (g' x) = f v"
  apply clarsimp
  apply (subgoal_tac "(f (g x)) = (f \<circ> g) x")
   apply simp
  apply (simp (no_asm))
  done

lemma option_map_comp_eqE:
  assumes om: "option_map f \<circ> mp = option_map f \<circ> mp'"
  and     p1: "\<lbrakk> mp x = None; mp' x = None \<rbrakk> \<Longrightarrow> P"
  and     p2: "\<And>v v'. \<lbrakk> mp x = Some v; mp' x = Some v'; f v = f v' \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases "mp x")
  case None
  hence "x \<notin> dom mp" by (simp add: domIff)
  hence "mp' x = None" by (simp add: option_map_eq_dom_eq [OF om] domIff)
  with None show ?thesis by (rule p1)
next
  case (Some v)
  hence "x \<in> dom mp" by clarsimp
  then obtain v' where Some': "mp' x = Some v'" by (clarsimp simp add: option_map_eq_dom_eq [OF om])
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

lemma word_or_zero:
  "(a || b = 0) = (a = 0 \<and> b = 0)"
  apply (safe, simp_all)
   apply (rule word_eqI, drule_tac x=n in word_eqD, simp)+
  done

lemma aligned_shiftr_mask_shiftl:
  "is_aligned x n \<Longrightarrow> ((x >> n) && mask v) << n = x && mask (v + n)"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftl nth_shiftr)
  apply (subgoal_tac "\<forall>m. x !! m \<longrightarrow> m \<ge> n")
   apply auto[1]
  apply (clarsimp simp: is_aligned_mask)
  apply (drule_tac x=m in word_eqD)
  apply (frule test_bit_size)
  apply (simp add: word_size)
  done

lemma word_and_1_shiftl:
  fixes x :: "('a :: len) word" shows
  "x && (1 << n) = (if x !! n then (1 << n) else 0)"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftl split: split_if del: shiftl_1)
  apply auto
  done

lemmas word_and_1_shiftls
    = word_and_1_shiftl[where n=0, simplified]
      word_and_1_shiftl[where n=1, simplified]
      word_and_1_shiftl[where n=2, simplified]

lemma word_and_mask_shiftl:
  "x && (mask n << m) = ((x >> m) && mask n) << m"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftl nth_shiftr)
  apply auto
  done

lemma toEnum_eq_to_fromEnum_eq:
  fixes v :: "'a :: enum" shows
  "n \<le> fromEnum (maxBound :: 'a) \<Longrightarrow> (toEnum n = v) = (n = fromEnum v)"
  apply (rule iffI)
   apply (drule arg_cong[where f=fromEnum])
   apply simp
  apply (drule arg_cong[where f="toEnum :: nat \<Rightarrow> 'a"])
  apply simp
  done

lemma if_Const_helper:
  "If P (Con x) (Con y) = Con (If P x y)"
  by (simp split: split_if)

lemmas if_Some_helper = if_Const_helper[where Con=Some]

lemma expand_restrict_map_eq:
  "(m |` S = m' |` S) = (\<forall>x. x \<in> S \<longrightarrow> m x = m' x)"
  by (simp add: fun_eq_iff restrict_map_def split: split_if)

lemma unat_ucast_8_32:
  fixes x :: "word8"
  shows "unat (ucast x :: word32) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply simp
  apply simp
  done

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

lemma if_then_1_else_0:
  "((if P then 1 else 0) = (0 :: word32)) = (\<not> P)"
  by simp

lemma if_then_0_else_1:
  "((if P then 0 else 1) = (0 :: word32)) = (P)"
  by simp

lemmas if_then_simps = if_then_0_else_1 if_then_1_else_0



lemma nat_less_cases':
  "(x::nat) < y \<Longrightarrow> x = y - 1 \<or> x < y - 1"
  by (fastforce intro: nat_less_cases)

lemma word32_FF_is_mask:
  "0xFF = mask 8 "
  by (simp add: mask_def)

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

lemma ucast_of_nat_small:
  "x < 2 ^ len_of TYPE('a) \<Longrightarrow>
     ucast (of_nat x :: ('a :: len) word) = (of_nat x :: ('b :: len) word)"
  apply (rule sym, subst word_unat.inverse_norm)
  apply (simp add: ucast_def word_of_int[symmetric]
                   of_nat_nat[symmetric] unat_def[symmetric])
  apply (simp add: unat_of_nat)
  done

lemma word_le_make_less:
  fixes x :: "('a :: len) word"
  shows "y \<noteq> -1 \<Longrightarrow> (x \<le> y) = (x < (y + 1))"
  apply safe
  apply (erule plus_one_helper2)
  apply (simp add: eq_diff_eq[symmetric])
  done

lemma Ball_emptyI:
  "S = {} \<Longrightarrow> (\<forall>x \<in> S. P x)"
  by simp

lemma allfEI:
  "\<lbrakk> \<forall>x. P x; \<And>x. P (f x) \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> \<forall>x. Q x"
  by fastforce

lemma arith_is_1:
  "\<lbrakk> x \<le> Suc 0; x > 0 \<rbrakk> \<Longrightarrow> x = 1"
  by arith

(* sjw: combining lemmas here :( *)
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

lemma finite_word: "finite (S :: (('a :: len) word) set)"
  by (rule finite)

lemma if_f:
  "(if a then f b else f c) = f (if a then b else c)"
  by simp

lemma in_16_range:
  "0 \<in> S \<Longrightarrow> r \<in> (\<lambda>x. r + x * (16 :: word32)) ` S"
  "n - 1 \<in> S \<Longrightarrow> (r + (16 * n - 16)) \<in> (\<lambda>x :: word32. r + x * 16) ` S"
  by (clarsimp simp: image_def
              elim!: bexI[rotated])+

definition
  "modify_map m p f \<equiv> m (p := option_map f (m p))"

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
  "(modify_map m p f) q = (if p = q then option_map f (m p) else m q)"
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
  "(modify_map m p f) p = (option_map f (m p))"
  by (simp add: modify_map_app)

lemma next_update_is_modify:
  "\<lbrakk> m p = Some cte'; cte = f cte' \<rbrakk> \<Longrightarrow> (m(p \<mapsto> cte)) = (modify_map m p f)"
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

lemma word_to_1_set:
  "{0 ..< (1 :: ('a :: len) word)} = {0}"
  by fastforce

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

lemma interval_empty:
  "({m..n} = {}) = (\<not> m \<le> (n::'a::order))"
  apply (rule iffI)
   apply clarsimp
  apply auto
  done

lemma range_subset_eq2:
  "{a :: word32 .. b} \<noteq> {} \<Longrightarrow> ({a .. b} \<subseteq> {c .. d}) = (c \<le> a \<and> b \<le> d)"
  by (simp add: interval_empty)

lemma singleton_eqD: "A = {x} \<Longrightarrow> x \<in> A" by blast

lemma ball_ran_fun_updI:
  "\<lbrakk> \<forall>v \<in> ran m. P v; \<forall>v. y = Some v \<longrightarrow> P v \<rbrakk>
        \<Longrightarrow> \<forall>v \<in> ran (m (x := y)). P v"
  by (auto simp add: ran_def)

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

lemma map2_Cons_2_3:
  "(map2 f xs (y # ys) = (z # zs)) = (\<exists>x xs'. xs = x # xs' \<and> f x y = z \<and> map2 f xs' ys = zs)"
  by (case_tac xs, simp_all)

lemma map2_xor_replicate_False:
  "map2 (\<lambda>(x\<Colon>bool) y\<Colon>bool. x = (\<not> y)) xs (replicate n False) = take n xs"
  apply (induct xs arbitrary: n)
   apply simp
  apply (case_tac n)
   apply (simp add: map2_def)
  apply simp
  done

lemma modify_map_K_D:
  "modify_map m p (\<lambda>x. y) p' = Some v \<Longrightarrow> (m (p \<mapsto> y)) p' = Some v"
  by (simp add: modify_map_def split: split_if_asm)

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

lemma notemptyI:
  "x \<in> S \<Longrightarrow> S \<noteq> {}"
  by clarsimp

lemma plus_Collect_helper:
  "op + x ` {xa. P (xa :: ('a :: len) word)} = {xa. P (xa - x)}"
  by (fastforce simp add: image_def)

lemma plus_Collect_helper2:
  "op + (- x) ` {xa. P (xa :: ('a :: len) word)} = {xa. P (x + xa)}"
  by (simp add: field_simps plus_Collect_helper)

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

lemma word32_count_from_top:
  "n \<noteq> 0 \<Longrightarrow> {0 ..< n :: word32} = {0 ..< n - 1} \<union> {n - 1}"
  apply (rule set_eqI, rule iffI)
   apply simp
   apply (drule minus_one_helper3)
   apply (rule disjCI)
   apply simp
  apply simp
  apply (erule minus_one_helper5)
  apply fastforce
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

lemma minus_one_helper2:
  "\<lbrakk> x - 1 < y \<rbrakk> \<Longrightarrow> x \<le> (y :: ('a :: len) word)"
  apply (cases "x = 0")
   apply simp
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst(asm) unat_minus_one)
   apply (simp add: word_less_nat_alt)
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma mod_mod_power:
  fixes k :: nat
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
proof (cases "m \<le> n")
  case True

  hence "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ m"
    apply -
    apply (subst mod_less [where n = "2 ^ n"])
    apply (rule order_less_le_trans [OF mod_less_divisor])
    apply simp+
    done
  also have "\<dots> = k mod  2 ^ (min m n)" using True by simp
  finally show ?thesis .
next
  case False
  hence "n < m" by simp
  then obtain d where md: "m = n + d"
    by (auto dest: less_imp_add_positive)
  hence "k mod 2 ^ m = 2 ^ n * (k div 2 ^ n mod 2 ^ d) + k mod 2 ^ n"
    by (simp add: mod_mult2_eq power_add)
  hence "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ n"
    by (simp add: mod_add_left_eq)
  thus ?thesis using False
    by simp
qed
lemma word_div_less:
  fixes m :: "'a :: len word"
  shows "m < n \<Longrightarrow> m div n = 0"
  apply (rule word_unat.Rep_eqD)
  apply (simp add: word_less_nat_alt unat_div)
  done

lemma word_must_wrap:
  "\<lbrakk> x \<le> n - 1; n \<le> x \<rbrakk> \<Longrightarrow> n = (0 :: ('a :: len) word)"
  apply (rule ccontr)
  apply (drule(1) order_trans)
  apply (drule word_sub_1_le)
  apply (drule(1) order_antisym)
  apply simp
  done

lemma upt_add_eq_append':
  assumes a1: "i \<le> j" and a2: "j \<le> k"
  shows "[i..<k] = [i..<j] @ [j..<k]"
  using a1 a2
  by (clarsimp simp: le_iff_add intro!:  upt_add_eq_append)

lemma range_subset_card:
  "\<lbrakk> {a :: ('a :: len) word .. b} \<subseteq> {c .. d}; b \<ge> a \<rbrakk>
     \<Longrightarrow> d \<ge> c \<and> d - c \<ge> b - a"
  apply (subgoal_tac "a \<in> {a .. b}")
   apply (frule(1) range_subset_lower)
   apply (frule(1) range_subset_upper)
   apply (rule context_conjI, simp)
   apply (rule word_sub_mono, assumption+)
    apply (erule word_sub_le)
   apply (erule word_sub_le)
  apply simp
  done

lemma less_1_simp:
  "n - 1 < m = (n \<le> (m :: ('a :: len) word) \<and> n \<noteq> 0)"
  by unat_arith

lemma alignUp_div_helper:
  fixes a :: "'a::len word"
  assumes kv: "k < 2 ^ (len_of TYPE('a) - n)"
  and     xk: "x = 2 ^ n * of_nat k"
  and    le: "a \<le> x"
  and    sz: "n < len_of TYPE('a)"
  and   anz: "a mod 2 ^ n \<noteq> 0"
  shows "a div 2 ^ n < of_nat k"
proof -
  have kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n)
            < 2 ^ len_of TYPE('a)"
    using xk kv sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst unat_power_lower, simp add: word_bits_def)
    apply (subst mult.commute)
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have "unat a div 2 ^ n * 2 ^ n \<noteq> unat a"
  proof -
    have "unat a = unat a div 2 ^ n * 2 ^ n + unat a mod 2 ^ n"
      by (simp add: mod_div_equality)
    also have "\<dots> \<noteq> unat a div 2 ^ n * 2 ^ n" using sz anz
      by (simp add: unat_arith_simps word_bits_def)
    finally show ?thesis ..
  qed

  hence "a div 2 ^ n * 2 ^ n < a" using sz anz
    apply (subst word_less_nat_alt)
    apply (subst unat_word_ariths)
    apply (subst unat_div)
    apply simp
    apply (rule order_le_less_trans [OF mod_le_dividend])
    apply (erule order_le_neq_trans [OF div_mult_le])
    done

  also from xk le have "\<dots> \<le> of_nat k * 2 ^ n" by (simp add: field_simps)
  finally show ?thesis using sz kv
    apply -
    apply (erule word_mult_less_dest [OF _ _ kn])
    apply (simp add: unat_div)
    apply (rule order_le_less_trans [OF div_mult_le])
    apply (rule unat_lt2p)
    done
qed

lemma nat_mod_power_lem:
  fixes a :: nat
  shows "1 < a \<Longrightarrow> a ^ n mod a ^ m = (if m \<le> n then 0 else a ^ n)"
  apply (clarsimp)
  apply (clarsimp simp add: le_iff_add power_add)
  done

lemma power_mod_div:
  fixes x :: "nat"
  shows "x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)" (is "?LHS = ?RHS")
proof (cases "n \<le> m")
  case True
  hence "?LHS = 0"
    apply -
    apply (rule div_less)
    apply (rule order_less_le_trans [OF mod_less_divisor])
     apply simp
    apply simp
    done
  also have "\<dots> = ?RHS" using True
    by simp
  finally show ?thesis .
next
  case False
  hence lt: "m < n" by simp
  then obtain q where nv: "n = m + q" and "0 < q"
    by (auto dest: less_imp_Suc_add)

  hence "x mod 2 ^ n = 2 ^ m * (x div 2 ^ m mod 2 ^ q) + x mod 2 ^ m"
    by (simp add: power_add mod_mult2_eq)

  hence "?LHS = x div 2 ^ m mod 2 ^ q"
    by (simp add: div_add1_eq)

  also have "\<dots> = ?RHS" using nv
    by simp

  finally show ?thesis .
qed

lemma word_power_mod_div:
  fixes x :: "'a::len word"
  shows "\<lbrakk> n < len_of TYPE('a); m < len_of TYPE('a)\<rbrakk>
  \<Longrightarrow> x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)"
  apply (simp add: word_arith_nat_div unat_mod power_mod_div)
  apply (subst unat_arith_simps(3))
  apply (subst unat_mod)
  apply (subst unat_of_nat)+
  apply (simp add: mod_mod_power min.commute)
  done

(* FIXME: stronger version of GenericLib.p_assoc_help *)
lemma x_power_minus_1:
  fixes x :: "'a :: {ab_group_add, power, numeral, one}"
  shows "x + (2::'a) ^ n - (1::'a) = x + (2 ^ n - 1)" by simp

lemma nat_le_power_trans:
  fixes n :: nat
  shows "\<lbrakk>n \<le> 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> 2 ^ k * n \<le> 2 ^ m"
  apply (drule order_le_imp_less_or_eq)
  apply (erule disjE)
   apply (drule (1) nat_less_power_trans)
   apply (erule order_less_imp_le)
  apply (simp add: power_add [symmetric])
  done

lemma nat_diff_add:
  fixes i :: nat
  shows "\<lbrakk> i + j = k \<rbrakk> \<Longrightarrow> i = k - j"
  by arith

lemma word_range_minus_1':
  fixes a :: "'a :: len word"
  shows "a \<noteq> 0 \<Longrightarrow> {a - 1<..b} = {a..b}"
  by (simp add: greaterThanAtMost_def atLeastAtMost_def greaterThan_def atLeast_def less_1_simp)

lemma word_range_minus_1:
  fixes a :: word32
  shows "b \<noteq> 0 \<Longrightarrow> {a..b - 1} = {a..<b}"
  apply (simp add: atLeastLessThan_def atLeastAtMost_def atMost_def lessThan_def)
  apply (rule arg_cong [where f = "\<lambda>x. {a..} \<inter> x"])
  apply rule
   apply clarsimp
   apply (erule contrapos_pp)
   apply (simp add: linorder_not_less linorder_not_le word_must_wrap)
  apply (clarsimp)
  apply (drule minus_one_helper3)
  apply (auto simp: word_less_sub_1)
  done

lemma ucast_nat_def:
  "of_nat (unat x) = (ucast :: ('a :: len) word \<Rightarrow> ('b :: len) word) x"
  by (simp add: ucast_def word_of_int_nat unat_def)

lemma delete_remove1 :
  "delete x xs = remove1 x xs"
  by (induct xs, auto)

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

lemma cases_simp_left:
  "((P \<longrightarrow> Q) \<and> (\<not> P \<longrightarrow> Q) \<and> R) = (Q \<and> R)"
  by fastforce

lemma disjI2_strg:
  "Q \<longrightarrow> (P \<or> Q)"
  by simp

lemma eq_2_32_0:
  "(2 ^ 32 :: word32) = 0"
  by simp

lemma eq_imp_strg:
  "P t \<longrightarrow> (t = s \<longrightarrow> P s)"
  by clarsimp

lemma if_fun_split:
  "(if P then \<lambda>s. Q s else (\<lambda>s. R s)) = (\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s))"
  by simp

lemma i_hate_words_helper:
  "i \<le> (j - k :: nat) \<Longrightarrow> i \<le> j"
  by simp

lemma i_hate_words:
  "unat (a :: 'a word) \<le> unat (b :: ('a :: len) word) - Suc 0
    \<Longrightarrow> a \<noteq> -1"
  apply (frule i_hate_words_helper)
  apply (subst(asm) word_le_nat_alt[symmetric])
  apply (clarsimp simp only: word_minus_one_le)
  apply (simp only: linorder_not_less[symmetric])
  apply (erule notE)
  apply (rule diff_Suc_less)
  apply (subst neq0_conv[symmetric])
  apply (subst unat_eq_0)
  apply (rule notI, drule arg_cong[where f="op + 1"])
  apply simp
  done

lemma if_both_strengthen:
  "P \<and> Q \<longrightarrow> (if G then P else Q)"
  by simp

lemma if_both_strengthen2:
  "P s \<and> Q s \<longrightarrow> (if G then P else Q) s"
  by simp

lemma if_swap:
  "(if P then Q else R) = (if \<not>P then R else Q)" by simp

lemma ignore_if:
  "(y and z) s \<Longrightarrow> (if x then y else z) s"
  by (clarsimp simp: pred_conj_def)

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
  apply clarsimp
  apply blast
  done

lemma nat_diff_eq:
  fixes x :: nat
  shows "\<lbrakk> x - y = x - z; y < x\<rbrakk> \<Longrightarrow> y = z"
  by arith

lemma overflow_plus_one_self:
  "(1 + p \<le> p) = (p = (-1 :: word32))"
  apply (safe, simp_all)
  apply (rule ccontr)
  apply (drule plus_one_helper2)
   apply (rule notI)
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
  apply (simp add: field_simps)
  done

lemma plus_1_less:
  "(x + 1 \<le> (x :: ('a :: len) word)) = (x = -1)"
  apply (rule iffI)
   apply (rule ccontr)
   apply (cut_tac plus_one_helper2[where x=x, OF order_refl])
    apply simp
   apply clarsimp
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
  apply simp
  done

lemma pos_mult_pos_ge:
  "[|x > (0::int); n>=0 |] ==> n * x >= n*1"
  apply (simp only: mult_left_mono)
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
  "x \<in> dom f \<Longrightarrow> insert x (dom f) = dom f" by auto

lemma emptyE2:
  "\<lbrakk> S = {}; x \<in> S \<rbrakk> \<Longrightarrow> P"
  by simp

lemma mod_div_equality_div_eq:
  "a div b * b = (a - (a mod b) :: int)"
  by (simp add: field_simps)

lemma zmod_helper:
  "n mod m = k \<Longrightarrow> ((n :: int) + a) mod m = (k + a) mod m"
  by (metis add.commute mod_add_right_eq)

lemma int_div_sub_1:
  "\<lbrakk> m \<ge> 1 \<rbrakk> \<Longrightarrow> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)"
  apply (subgoal_tac "m = 0 \<or> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)")
   apply fastforce
  apply (subst mult_cancel_right[symmetric])
  apply (simp only: left_diff_distrib split: split_if)
  apply (simp only: mod_div_equality_div_eq)
  apply (clarsimp simp: field_simps)
  apply (clarsimp simp: dvd_eq_mod_eq_0)
  apply (cases "m = 1")
   apply simp
  apply (subst mod_diff_eq, simp add: zmod_minus1 mod_pos_pos_trivial)
  apply clarsimp
  apply (subst diff_add_cancel[where b=1, symmetric])
  apply (subst push_mods(1))
  apply (simp add: field_simps mod_pos_pos_trivial)
  apply (rule mod_pos_pos_trivial)
   apply (subst add_0_right[where a=0, symmetric])
   apply (rule add_mono)
    apply simp
   apply simp
  apply (cases "(n - 1) mod m = m - 1")
   apply (drule zmod_helper[where a=1])
   apply simp
  apply (subgoal_tac "1 + (n - 1) mod m \<le> m")
   apply simp
  apply (subst field_simps, rule zless_imp_add1_zle)
  apply simp
  done

lemmas nat_less_power_trans_16 =
   subst [OF mult.commute, where P="\<lambda>x. x < v" for v,
          OF nat_less_power_trans[where k=4, simplified]]

lemmas nat_less_power_trans_256 =
   subst [OF mult.commute, where P="\<lambda>x. x < v" for v,
          OF nat_less_power_trans[where k=8, simplified]]
lemmas nat_less_power_trans_4096 =
   subst [OF mult.commute, where P="\<lambda>x. x < v" for v,
          OF nat_less_power_trans[where k=12, simplified]]

lemma ptr_add_image_multI:
  "\<lbrakk> \<And>x y. (x * val = y * val') = (x * val'' = y); x * val'' \<in> S \<rbrakk> \<Longrightarrow>
     ptr_add ptr (x * val) \<in> (\<lambda>p. ptr_add ptr (p * val')) ` S"
  apply (simp add: image_def)
  apply (erule rev_bexI)
  apply (rule arg_cong[where f="ptr_add ptr"])
  apply simp
  done

lemma shift_times_fold:
  "(x :: word32) * (2 ^ n) << m = x << (m + n)"
  by (simp add: shiftl_t2n ac_simps power_add)

lemma word_plus_strict_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y < z; x \<le> x + z\<rbrakk> \<Longrightarrow> x + y < x + z"
  by unat_arith

lemma comp_upd_simp:
  "(f \<circ> (g (x := y))) = ((f \<circ> g) (x := f y))"
  by (rule ext, simp add: o_def)

lemma dom_option_map:
  "dom (option_map f o m) = dom m"
  by (simp add: dom_def)

lemma drop_imp:
  "P \<Longrightarrow> (A \<longrightarrow> P) \<and> (B \<longrightarrow> P)" by blast

lemma inj_on_fun_updI2:
  "\<lbrakk> inj_on f A; y \<notin> f ` (A - {x}) \<rbrakk>
       \<Longrightarrow> inj_on (f(x := y)) A"
  apply (rule inj_onI)
  apply (simp split: split_if_asm)
   apply (erule notE, rule image_eqI, erule sym)
   apply simp
  apply (erule(3) inj_onD)
  done

lemma inj_on_fun_upd_elsewhere:
  "x \<notin> S \<Longrightarrow> inj_on (f (x := y)) S = inj_on f S"
  apply (simp add: inj_on_def)
  apply blast
  done

lemma not_Some_eq_tuple:
  "(\<forall>y z. x \<noteq> Some (y, z)) = (x = None)"
  by (cases x, simp_all)

lemma ran_option_map:
  "ran (option_map f o m) = f ` ran m"
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

lemma replicate_minus:
  "k < n \<Longrightarrow> replicate n False = replicate (n - k) False @ replicate k False"
  by (subst replicate_add [symmetric]) simp

lemmas map_prod_split_imageI
  = map_prod_imageI[where f="split f" and g="split g"
                    and a="(a, b)" and b="(c, d)" for a b c d f g, simplified]

lemma word_div_mult:
  fixes c :: "('a::len) word"
  shows "\<lbrakk>0 < c; a < b * c \<rbrakk> \<Longrightarrow> a div c < b"
  apply (simp add: word_less_nat_alt unat_div)
  apply (subst td_gal_lt [symmetric])
   apply assumption
  apply (erule order_less_le_trans)
  apply (subst unat_word_ariths)
  by (metis Divides.mod_less_eq_dividend)

lemma word_less_power_trans_ofnat:
  "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> of_nat n * 2 ^ k < (2::'a::len word) ^ m"
  apply (subst mult.commute)
  apply (rule word_less_power_trans)
    apply (simp add: word_less_nat_alt)
    apply (subst unat_of_nat_eq)
     apply (erule order_less_trans)
     apply simp+
    done

lemma div_power_helper:
  "\<lbrakk> x \<le> y; y < word_bits \<rbrakk> \<Longrightarrow> (2 ^ y - 1) div (2 ^ x :: word32) = 2 ^ (y - x) - 1"
  apply (rule word_uint.Rep_eqD)
  apply (simp only: uint_word_ariths uint_div uint_power_lower word_bits_len_of)
  apply (subst mod_pos_pos_trivial, fastforce, fastforce)+
  apply (subst mod_pos_pos_trivial)
    apply (simp add: le_diff_eq uint_2p_alt[where 'a=32, unfolded word_bits_len_of])
   apply (rule less_1_helper)
   apply (rule power_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply (subst mod_pos_pos_trivial)
    apply (simp add: uint_2p_alt[where 'a=32, unfolded word_bits_len_of])
   apply (rule less_1_helper)
   apply (rule power_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply (subst int_div_sub_1)
    apply simp
   apply (simp add: uint_2p_alt[where 'a=32, unfolded word_bits_len_of])
  apply (subst power_0[symmetric, where a=2])
  apply (simp add: uint_2p_alt[where 'a=32, unfolded word_bits_len_of]
                   le_imp_power_dvd_int power_sub_int)
  done

lemma n_less_word_bits:
  "(n < word_bits) = (n < 32)"
  by (simp add: word_bits_def)

lemma of_nat_less_pow:
  "\<lbrakk> x < 2 ^ n; n < word_bits \<rbrakk> \<Longrightarrow> of_nat x < (2 :: word32) ^ n"
  apply (subst word_unat_power)
  apply (rule of_nat_mono_maybe)
   apply (rule power_strict_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply assumption
  done

lemma power_helper:
  "\<lbrakk> (x :: word32) < 2 ^ (m - n); n \<le> m; m < word_bits \<rbrakk> \<Longrightarrow> x * (2 ^ n) < 2 ^ m"
  apply (drule word_mult_less_mono1[where k="2 ^ n"])
    apply (simp add: word_neq_0_conv[symmetric] word_bits_def)
   apply (simp only: unat_power_lower[where 'a=32, unfolded word_bits_len_of]
                     power_add[symmetric])
   apply (rule power_strict_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply (simp add: power_add[symmetric])
  done

lemma word_1_le_power:
  "n < len_of TYPE('a) \<Longrightarrow> (1 :: 'a :: len word) \<le> 2 ^ n"
  by (rule inc_le[where i=0, simplified], erule iffD2[OF p2_gt_0])

lemma enum_word_div:
  fixes v :: "('a :: len) word" shows
  "\<exists>xs ys. enum = xs @ [v] @ ys
             \<and> (\<forall>x \<in> set xs. x < v)
             \<and> (\<forall>y \<in> set ys. v < y)"
  apply (simp only: enum_word_def)
  apply (subst upt_add_eq_append'[where j="unat v"])
    apply simp
   apply (rule order_less_imp_le, simp)
  apply (simp add: upt_conv_Cons)
  apply (intro exI conjI)
    apply fastforce
   apply clarsimp
   apply (drule of_nat_mono_maybe[rotated, where 'a='a])
    apply simp
   apply simp
  apply (clarsimp simp: Suc_le_eq)
  apply (drule of_nat_mono_maybe[rotated, where 'a='a])
   apply simp
  apply simp
  done

lemma less_x_plus_1:
  fixes x :: "('a :: len) word" shows
  "x \<noteq> max_word \<Longrightarrow> (y < (x + 1)) = (y < x \<or> y = x)"
  apply (rule iffI)
   apply (rule disjCI)
   apply (drule plus_one_helper)
   apply simp
  apply (subgoal_tac "x < x + 1")
   apply (erule disjE, simp_all)
  apply (rule plus_one_helper2 [OF order_refl])
  apply (rule notI, drule max_word_wrap)
  apply simp
  done

lemma of_bool_nth:
  "of_bool (x !! v) = (x >> v) && 1"
  apply (rule word_eqI)
  apply (simp add: nth_shiftr cong: rev_conj_cong)
  done

lemma unat_1_0:
  "1 \<le> (x::word32) = (0 < unat x)"
  by (auto simp add: word_le_nat_alt)

lemma x_less_2_0_1:
  fixes x :: word32 shows
  "x < 2 \<Longrightarrow> x = 0 \<or> x = 1"
  by unat_arith

lemma x_less_2_0_1':
  fixes x :: "('a::len) word"
  shows "\<lbrakk>len_of TYPE('a) \<noteq> 1; x < 2\<rbrakk> \<Longrightarrow> x = 0 \<or> x = 1"
  apply (induct x)
   apply clarsimp+
  by (metis Suc_eq_plus1 add_lessD1 less_irrefl one_add_one unatSuc word_less_nat_alt)

lemma Collect_int_vars:
  "{s. P rv s} \<inter> {s. rv = xf s} = {s. P (xf s) s} \<inter> {s. rv = xf s}"
  by auto

lemma if_0_1_eq:
  "((if P then 1 else 0) = (case Q of True \<Rightarrow> of_nat 1 | False \<Rightarrow> of_nat 0)) = (P = Q)"
  by (simp add: case_bool_If split: split_if)

lemma modify_map_exists_cte :
  "(\<exists>cte. modify_map m p f p' = Some cte) = (\<exists>cte. m p' = Some cte)"
  by (simp add: modify_map_def)

lemmas word_add_le_iff2 = word_add_le_iff [folded no_olen_add_nat]

lemma mask_32_max_word :
  shows "mask 32 = (max_word :: word32)"
  unfolding mask_def
  by (simp add: max_word_def)

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

lemma of_nat_power:
  shows "\<lbrakk> p < 2 ^ x; x < len_of TYPE ('a :: len) \<rbrakk> \<Longrightarrow> of_nat p < (2 :: 'a :: len word) ^ x"
  apply (rule order_less_le_trans)
   apply (rule of_nat_mono_maybe)
    apply (erule power_strict_increasing)
    apply simp
   apply assumption
  apply (simp add: word_unat_power)
  done

lemma of_nat_n_less_equal_power_2:
  "n < len_of TYPE('a::len) \<Longrightarrow> ((of_nat n)::'a word) < 2 ^ n"
  apply (induct n)
   apply clarsimp
  apply clarsimp
  apply (metis WordLemmaBucket.of_nat_power
               n_less_equal_power_2 of_nat_Suc power_Suc)
  done

lemma of_nat32_n_less_equal_power_2:
 "n < 32 \<Longrightarrow> ((of_nat n)::32 word) < 2 ^ n"
  by (rule of_nat_n_less_equal_power_2, clarsimp simp: word_size)

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

lemma eq_mask_less:
  fixes w :: "('a::len) word"
  assumes eqm: "w = w && mask n"
  and      sz: "n < len_of TYPE ('a)"
  shows "w < (2::'a word) ^ n"
  by (subst eqm, rule and_mask_less' [OF sz])

lemma of_nat_mono_maybe':
  fixes Y :: "nat"
  assumes xlt: "X < 2 ^ len_of TYPE ('a :: len)"
  assumes ylt: "Y < 2 ^ len_of TYPE ('a :: len)"
  shows   "(Y < X) = (of_nat Y < (of_nat X :: 'a :: len word))"
  apply (subst word_less_nat_alt)
  apply (subst unat_of_nat)+
  apply (subst mod_less)
   apply (rule ylt)
  apply (subst mod_less)
   apply (rule xlt)
  apply simp
  done

(* FIXME: MOVE *)
lemma shiftr_mask_eq:
  fixes x :: "'a :: len word"
  shows "(x >> n) && mask (size x - n) = x >> n"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr)
  apply (rule iffI)
   apply clarsimp
  apply (clarsimp)
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

(* FIXME: move *)
lemma shiftr_mask_eq':
  fixes x :: "'a :: len word"
  shows "m = (size x - n) \<Longrightarrow> (x >> n) && mask m = x >> n"
  by (simp add: shiftr_mask_eq)

lemma zipWith_Nil2 :
  "zipWith f xs [] = []"
  unfolding zipWith_def by simp

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

lemma bang_big: "n \<ge> size (x::'a::len0 word) \<Longrightarrow> (x !! n) = False"
  by (simp add: test_bit_bl word_size)

lemma bang_conj_lt:
  fixes x :: "'a :: len word"
  shows "(x !! m \<and> m < len_of TYPE('a)) = x !! m"
  apply (cases "m < len_of TYPE('a)")
   apply simp
  apply (simp add: not_less bang_big  word_size)
  done

lemma dom_if:
  "dom (\<lambda>a. if a \<in> addrs then Some (f a) else g a)  = addrs \<union> dom g"
  by (auto simp: dom_def split: split_if)

lemma less_is_non_zero_p1:
  fixes a :: "'a :: len word"
  shows "a < k \<Longrightarrow> a + 1 \<noteq> 0"
  apply (erule contrapos_pn)
  apply (drule max_word_wrap)
  apply (simp add: not_less)
  done

lemma lt_word_bits_lt_pow:
  "sz < word_bits \<Longrightarrow> sz < 2 ^ word_bits"
  by (simp add: word_bits_conv)

(* FIXME: shadows an existing thm *)
lemma of_nat_mono_maybe_le:
  "\<lbrakk>X < 2 ^ len_of TYPE('a); Y < 2 ^ len_of TYPE('a)\<rbrakk> \<Longrightarrow>
   (Y \<le> X) = ((of_nat Y :: 'a :: len word) \<le> of_nat X)"
  apply (clarsimp simp: le_less)
  apply (rule disj_cong)
   apply (rule of_nat_mono_maybe', assumption+)
  apply (simp add: word_unat.norm_eq_iff [symmetric])
  done

lemma neg_mask_bang:
  "(~~ mask n :: 'a :: len word) !! m = (n \<le> m \<and> m < len_of TYPE('a))"
  apply (cases "m < len_of TYPE('a)")
   apply (simp add: word_ops_nth_size word_size not_less)
  apply (simp add: not_less bang_big  word_size)
  done

lemma mask_AND_NOT_mask:
  "(w && ~~ mask n) && mask n = 0"
by (rule word_eqI) (clarsimp simp add: word_size neg_mask_bang)

lemma AND_NOT_mask_plus_AND_mask_eq:
  "(w && ~~ mask n) + (w && mask n) = w"
apply (rule word_eqI)
apply (rename_tac m)
apply (simp add: word_size)
apply (cut_tac word_plus_and_or_coroll[of "w && ~~ mask n" "w && mask n"])
 apply (simp add: word_ao_dist2[symmetric] word_size neg_mask_bang)
apply (rule word_eqI)
apply (rename_tac m)
apply (simp add: word_size neg_mask_bang)
done

lemma mask_eqI:
  fixes x :: "'a :: len word"
  assumes m1: "x && mask n = y && mask n"
  and     m2: "x && ~~ mask n = y && ~~ mask n"
  shows "x = y"
proof (subst bang_eq, rule allI)
  fix m

  show "x !! m = y !! m"
  proof (cases "m < n")
    case True
    hence "x !! m = ((x && mask n) !! m)"
      by (simp add: word_size bang_conj_lt)
    also have "\<dots> = ((y && mask n) !! m)" using m1 by simp
    also have "\<dots> = y !! m" using True
      by (simp add: word_size bang_conj_lt)
    finally show ?thesis .
  next
    case False
    hence "x !! m = ((x && ~~ mask n) !! m)"
      by (simp add: neg_mask_bang bang_conj_lt)
    also have "\<dots> = ((y && ~~ mask n) !! m)" using m2 by simp
    also have "\<dots> = y !! m" using False
      by (simp add: neg_mask_bang bang_conj_lt)
    finally show ?thesis .
  qed
qed

lemma nat_less_power_trans2:
  fixes n :: nat
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> n * 2 ^ k  < 2 ^ m"
  by (subst mult.commute, erule (1) nat_less_power_trans)

lemma nat_move_sub_le: "(a::nat) + b \<le> c \<Longrightarrow> a \<le> c - b" by arith

lemma neq_0_no_wrap:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x \<le> x + y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  by clarsimp

lemma plus_minus_one_rewrite:
  "v + (- 1 :: ('a :: {ring, one, uminus})) \<equiv> v - 1"
  by (simp add: field_simps)

lemma power_minus_is_div:
  "b \<le> a \<Longrightarrow> (2 :: nat) ^ (a - b) = 2 ^ a div 2 ^ b"
  apply (induct a arbitrary: b)
   apply simp
  apply (erule le_SucE)
   apply (clarsimp simp:Suc_diff_le le_iff_add power_add)
  apply simp
  done

lemma two_pow_div_gt_le:
  "v < 2 ^ n div (2 ^ m :: nat) \<Longrightarrow> m \<le> n"
  by (clarsimp dest!: less_two_pow_divD)

lemma unatSuc2:
  fixes n :: "'a :: len word"
  shows "n + 1 \<noteq> 0 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  by (simp add: add.commute unatSuc)

lemma unat_less_word_bits:
  fixes y :: word32
  shows "x < unat y \<Longrightarrow> x < 2 ^ word_bits"
  unfolding word_bits_def
  by (rule order_less_trans [OF _ unat_lt2p])

lemma word_add_power_off:
  fixes a :: word32
  assumes ak: "a < k"
  and kw: "k < 2 ^ (word_bits - m)"
  and mw: "m < word_bits"
  and off: "off < 2 ^ m"
  shows "(a * 2 ^ m) + off < k * 2 ^ m"
proof (cases "m = 0")
  case True
  thus ?thesis using off ak by simp
next
  case False

  from ak have ak1: "a + 1 \<le> k" by (rule inc_le)
  hence "(a + 1) * 2 ^ m \<noteq> 0"
    apply -
    apply (rule word_power_nonzero)
    apply (erule order_le_less_trans  [OF _ kw])
    apply (rule mw)
    apply (rule less_is_non_zero_p1 [OF ak])
    done
  hence "(a * 2 ^ m) + off < ((a + 1) * 2 ^ m)" using kw mw
    apply -
    apply (simp add: distrib_right)
    apply (rule word_plus_strict_mono_right [OF off])
    apply (rule is_aligned_no_overflow'')
    apply (rule is_aligned_mult_triv2)
    apply assumption
    done
  also have "\<dots> \<le> k * 2 ^ m" using ak1 mw kw False
    apply -
    apply (erule word_mult_le_mono1)
    apply (simp add: p2_gt_0 word_bits_def)
    apply (simp add: word_bits_len_of word_less_nat_alt word_bits_def)
    apply (rule nat_less_power_trans2[where m=32, simplified])
    apply (simp add: word_less_nat_alt)
    apply simp
    done
  finally show ?thesis .
qed

lemma word_of_nat_less:
  "\<lbrakk> n < unat x \<rbrakk> \<Longrightarrow> of_nat n < x"
  apply (simp add: word_less_nat_alt)
  apply (erule order_le_less_trans[rotated])
  apply (simp add: unat_of_nat)
  done

lemma word_rsplit_0:
  "word_rsplit (0 :: word32) = [0, 0, 0, 0 :: word8]"
  apply (simp add: word_rsplit_def bin_rsplit_def Let_def)
  done

lemma word_of_nat_le:
  "n \<le> unat x \<Longrightarrow> of_nat n \<le> x"
  apply (simp add: word_le_nat_alt unat_of_nat)
  apply (erule order_trans[rotated])
  apply simp
  done

lemma word_unat_less_le:
   "a \<le> of_nat b \<Longrightarrow> unat a \<le> b"
   by (metis eq_iff le_cases le_unat_uoi word_of_nat_le)

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

lemma split_upt_on_n:
  "n < m \<Longrightarrow> [0 ..< m] = [0 ..< n] @ [n] @ [Suc n ..< m]"
  apply (subst upt_add_eq_append', simp, erule order_less_imp_le)
  apply (simp add: upt_conv_Cons)
  done

lemma unat_ucast_10_32 :
  fixes x :: "10 word"
  shows "unat (ucast x :: word32) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply simp
  apply simp
  done

lemma map_comp_update_lift:
  assumes fv: "f v = Some v'"
  shows "(f \<circ>\<^sub>m (g(ptr \<mapsto> v))) = ((f \<circ>\<^sub>m g)(ptr \<mapsto> v'))"
  unfolding map_comp_def
  apply (rule ext)
  apply (simp add: fv)
  done

lemma restrict_map_cong:
  assumes sv: "S = S'"
  and     rl: "\<And>p. p \<in> S' \<Longrightarrow> mp p = mp' p"
  shows   "mp |` S = mp' |` S'"
  apply (simp add: sv)
  apply (rule ext)
  apply (case_tac "x \<in> S'")
   apply (simp add: rl )
  apply simp
  done

lemma and_eq_0_is_nth:
  fixes x :: "('a :: len) word"
  shows "y = 1 << n \<Longrightarrow> ((x && y) = 0) = (\<not> (x !! n))"
  apply safe
   apply (drule_tac u="(x && (1 << n))" and x=n in word_eqD)
   apply (simp add: nth_w2p)
   apply (simp add: test_bit_bin)
  apply (rule word_eqI)
  apply (simp add: nth_w2p)
  done

lemmas and_neq_0_is_nth = arg_cong [where f=Not, OF and_eq_0_is_nth, simplified]

lemma ucast_le_ucast_8_32:
  "(ucast x \<le> (ucast y :: word32)) = (x \<le> (y :: word8))"
  by (simp add: word_le_nat_alt unat_ucast_8_32)

lemma mask_Suc_0 : "mask (Suc 0) = 1"
  by (simp add: mask_def)

lemma ucast_ucast_add:
  fixes x :: "('a :: len) word"
  fixes y :: "('b :: len) word"
  shows
  "len_of TYPE('b) \<ge> len_of TYPE('a) \<Longrightarrow>
    ucast (ucast x + y) = x + ucast y"
  apply (rule word_unat.Rep_eqD)
  apply (simp add: unat_ucast unat_word_ariths mod_mod_power
                   min.absorb2 unat_of_nat)
  apply (subst mod_add_left_eq)
  apply (simp add: mod_mod_power min.absorb2)
  apply (subst mod_add_right_eq)
  apply simp
  done

lemma word_shift_zero:
  "\<lbrakk> x << n = 0; x \<le> 2^m; m + n < len_of TYPE('a)\<rbrakk> \<Longrightarrow> (x::'a::len word) = 0"
  apply (rule ccontr)
  apply (drule (2) word_shift_nonzero)
  apply simp
  done

lemma neg_mask_mono_le:
  "(x :: 'a :: len word) \<le> y \<Longrightarrow> x && ~~ mask n \<le> y && ~~ mask n"
proof (rule ccontr, simp add: linorder_not_le, cases "n < len_of TYPE('a)")
  case False
  show "y && ~~ mask n < x && ~~ mask n \<Longrightarrow> False"
    using False
    by (simp add: mask_def linorder_not_less
                  power_overflow)
next
  case True
  assume a: "x \<le> y" and b: "y && ~~ mask n < x && ~~ mask n"
  have word_bits:
    "n < len_of TYPE('a)"
    using True by assumption
  have "y \<le> (y && ~~ mask n) + (y && mask n)"
    by (simp add: word_plus_and_or_coroll2 add.commute)
  also have "\<dots> \<le> (y && ~~ mask n) + 2 ^ n"
    apply (rule word_plus_mono_right)
     apply (rule order_less_imp_le, rule and_mask_less_size)
     apply (simp add: word_size word_bits)
    apply (rule is_aligned_no_overflow'',
           simp_all add: is_aligned_neg_mask word_bits)
    apply (rule not_greatest_aligned, rule b)
     apply (simp_all add: is_aligned_neg_mask)
    done
  also have "\<dots> \<le> x && ~~ mask n"
    using b
    apply -
    apply (subst add.commute, rule le_plus)
     apply (rule aligned_at_least_t2n_diff,
            simp_all add: is_aligned_neg_mask)
    apply (rule ccontr, simp add: linorder_not_le)
    apply (drule aligned_small_is_0[rotated], simp_all add: is_aligned_neg_mask)
    done
  also have "\<dots> \<le> x"
    by (rule word_and_le2)
  also have "x \<le> y" by fact
finally
  show "False" using b
    by simp
qed

lemma isRight_right_map:
  "isRight (case_sum Inl (Inr o f) v) = isRight v"
  by (simp add: isRight_def split: sum.split)

lemma bool_mask [simp]:
  fixes x :: word32
  shows "(0 < x && 1) = (x && 1 = 1)"
  apply (rule iffI)
   prefer 2
   apply simp
  apply (subgoal_tac "x && mask 1 < 2^1")
   prefer 2
   apply (rule and_mask_less_size)
   apply (simp add: word_size)
  apply (simp add: mask_def)
  apply (drule word_less_cases [where y=2])
  apply (erule disjE, simp)
  apply simp
  done

lemma case_option_over_if:
  "case_option P Q (if G then None else Some v)
        = (if G then P else Q v)"
  "case_option P Q (if G then Some v else None)
        = (if G then Q v else P)"
  by (simp split: split_if)+

lemma sint_eq_uint:
  "\<not> msb x \<Longrightarrow> sint x = uint x"
  apply (rule word_uint.Abs_eqD, subst word_sint.Rep_inverse)
    apply simp_all
  apply (cut_tac x=x in word_sint.Rep)
  apply (clarsimp simp add: uints_num sints_num)
  apply (rule conjI)
   apply (rule ccontr)
   apply (simp add: linorder_not_le word_msb_sint[symmetric])
  apply (erule order_less_le_trans)
  apply simp
  done

lemma scast_eq_ucast:
  "\<not> msb x \<Longrightarrow> scast x = ucast x"
  by (simp add: scast_def ucast_def sint_eq_uint)

(* MOVE *)

lemma lt1_neq0:
  fixes x :: "'a :: len word"
  shows "(1 \<le> x) = (x \<noteq> 0)" by unat_arith

lemma word_plus_one_nonzero:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>x \<le> x + y; y \<noteq> 0\<rbrakk> \<Longrightarrow> x + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (erule word_random)
  apply (simp add: lt1_neq0)
  done

lemma word_sub_plus_one_nonzero:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>n' \<le> n; n' \<noteq> 0\<rbrakk> \<Longrightarrow> (n - n') + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (rule word_random [where x' = n'])
   apply simp
   apply (erule word_sub_le)
  apply (simp add: lt1_neq0)
  done

lemma word_le_minus_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> z \<le> y; y \<le> x; z \<le> x \<rbrakk> \<Longrightarrow> x - y \<le> x - z"
  apply (rule word_sub_mono)
     apply simp
    apply assumption
   apply (erule word_sub_le)
  apply (erule word_sub_le)
  done

lemma drop_append_miracle:
  "n = length xs \<Longrightarrow> drop n (xs @ ys) = ys"
  by simp

lemma foldr_does_nothing_to_xf:
  "\<lbrakk> \<And>x s. x \<in> set xs \<Longrightarrow> xf (f x s) = xf s \<rbrakk> \<Longrightarrow> xf (foldr f xs s) = xf s"
  by (induct xs, simp_all)

lemma nat_less_mult_monoish: "\<lbrakk> a < b; c < (d :: nat) \<rbrakk> \<Longrightarrow> (a + 1) * (c + 1) <= b * d"
  apply (drule Suc_leI)+
  apply (drule(1) mult_le_mono)
  apply simp
  done

lemma word_0_sle_from_less[unfolded word_size]:
  "\<lbrakk> x < 2 ^ (size x - 1) \<rbrakk>  \<Longrightarrow> 0 <=s x"
  apply (clarsimp simp: word_sle_msb_le)
  apply (simp add: word_msb_nth)
  apply (subst (asm) word_test_bit_def [symmetric])
  apply (drule less_mask_eq)
  apply (drule_tac x="size x - 1" in word_eqD)
  apply (simp add: word_size)
  done

lemma not_msb_from_less:
  "(v :: 'a word) < 2 ^ (len_of TYPE('a :: len) - 1) \<Longrightarrow> \<not> msb v"
  apply (clarsimp simp add: msb_nth)
  apply (drule less_mask_eq)
  apply (drule word_eqD, drule(1) iffD2)
  apply simp
  done

lemma distinct_lemma: "f x \<noteq> f y \<Longrightarrow> x \<noteq> y" by auto


lemma ucast_sub_ucast:
  fixes x :: "'a::len word"
  assumes "y \<le> x"
  assumes T: "len_of TYPE('a) \<le> len_of TYPE('b)"
  shows "ucast (x - y) = (ucast x - ucast y :: 'b::len word)"
proof -
  from T
  have P: "unat x < 2 ^ len_of TYPE('b)" "unat y < 2 ^ len_of TYPE('b)"
    by (fastforce intro!: less_le_trans[OF unat_lt2p])+
  thus ?thesis
    by (simp add: unat_arith_simps unat_ucast assms[simplified unat_arith_simps])
qed

lemma word_1_0:
  "\<lbrakk>a + (1::('a::len) word) \<le> b; a < of_nat ((2::nat) ^ len_of TYPE(32) - 1)\<rbrakk> \<Longrightarrow> a < b"
  by unat_arith

lemma unat_of_nat_less:"\<lbrakk> a < b; unat b = c \<rbrakk> \<Longrightarrow> a < of_nat c"
  by fastforce

lemma word_le_plus_1: "\<lbrakk> (y::('a::len) word) < y + n; a < n \<rbrakk> \<Longrightarrow> y + a \<le> y + a + 1"
  by unat_arith

lemma word_le_plus:"\<lbrakk>(a::('a::len) word) < a + b; c < b\<rbrakk> \<Longrightarrow> a \<le> a + c"
by (metis order_less_imp_le word_random)

(*
 * Basic signed arithemetic properties.
 *)

lemma sint_minus1 [simp]: "(sint x = -1) = (x = -1)"
  by (metis sint_n1 word_sint.Rep_inverse')

lemma sint_0 [simp]: "(sint x = 0) = (x = 0)"
  by (metis sint_0 word_sint.Rep_inverse')

(* It is not always that case that "sint 1 = 1", because of 1-bit word sizes.
 * This lemma produces the different cases. *)
lemma sint_1_cases:
  "\<lbrakk> \<lbrakk> len_of TYPE ('a::len) = 1; (a::'a word) = 0; sint a = 0 \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> len_of TYPE ('a) = 1; a = 1; sint (1 :: 'a word) = -1 \<rbrakk> \<Longrightarrow> P;
      \<lbrakk> len_of TYPE ('a) > 1; sint (1 :: 'a word) = 1 \<rbrakk> \<Longrightarrow> P \<rbrakk>
                \<Longrightarrow> P"
   apply atomize_elim
  apply (case_tac "len_of TYPE ('a) = 1")
   apply clarsimp
   apply (subgoal_tac "(UNIV :: 'a word set) = {0, 1}")
    apply (metis UNIV_I insert_iff singletonE)
   apply (subst word_unat.univ)
   apply (clarsimp simp: unats_def image_def)
   apply (rule set_eqI, rule iffI)
    apply clarsimp
    apply (metis One_nat_def less_2_cases of_nat_1 semiring_1_class.of_nat_0)
   apply clarsimp
   apply (metis Abs_fnat_hom_0 Suc_1 lessI of_nat_1 zero_less_Suc)
  apply clarsimp
  apply (metis One_nat_def arith_is_1 le_def len_gt_0)
  done

lemma sint_int_min:
  "sint (- (2 ^ (len_of TYPE('a) - Suc 0)) :: ('a::len) word) = - (2 ^ (len_of TYPE('a) - Suc 0))"
  apply (subst word_sint.Abs_inverse' [where r="- (2 ^ (len_of TYPE('a) - Suc 0))"])
    apply (clarsimp simp: sints_num)
   apply (clarsimp simp: wi_hom_syms word_of_int_2p)
  apply clarsimp
  done

lemma sint_int_max_plus_1:
  "sint (2 ^ (len_of TYPE('a) - Suc 0) :: ('a::len) word) = - (2 ^ (len_of TYPE('a) - Suc 0))"
  apply (subst word_of_int_2p [symmetric])
  apply (subst int_word_sint)
  apply clarsimp
  apply (metis Suc_pred int_word_uint len_gt_0 power_Suc uint_eq_0 word_of_int_2p word_pow_0)
  done

lemma word32_bounds:
  "- (2 ^ (size (x :: word32) - 1)) = (-2147483648 :: int)"
  "((2 ^ (size (x :: word32) - 1)) - 1) = (2147483647 :: int)"
  "- (2 ^ (size (y :: 32 signed word) - 1)) = (-2147483648 :: int)"
  "((2 ^ (size (y :: 32 signed word) - 1)) - 1) = (2147483647 :: int)"
  by (simp_all add: word_size)

lemma sbintrunc_eq_in_range:
  "(sbintrunc n x = x) = (x \<in> range (sbintrunc n))"
  "(x = sbintrunc n x) = (x \<in> range (sbintrunc n))"
  apply (simp_all add: image_def)
  apply (metis sbintrunc_sbintrunc)+
  done

lemma sbintrunc_If:
  "- 3 * (2 ^ n) \<le> x \<and> x < 3 * (2 ^ n)
    \<Longrightarrow> sbintrunc n x = (if x < - (2 ^ n) then x + 2 * (2 ^ n)
        else if x \<ge> 2 ^ n then x - 2 * (2 ^ n) else x)"
  apply (simp add: no_sbintr_alt2, safe)
    apply (simp add: mod_pos_geq mod_pos_pos_trivial)
   apply (subst mod_add_self1[symmetric], simp)
   apply (simp add: mod_pos_pos_trivial)
  apply (simp add: mod_pos_pos_trivial)
  done

lemma signed_arith_eq_checks_to_ord:
  "(sint a + sint b = sint (a + b ))
    = ((a <=s a + b) = (0 <=s b))"
  "(sint a - sint b = sint (a - b ))
    = ((0 <=s a - b) = (b <=s a))"
  "(- sint a = sint (- a)) = (0 <=s (- a) = (a <=s 0))"
  using sint_range'[where x=a] sint_range'[where x=b]
  apply (simp_all add: sint_word_ariths
                word_sle_def word_sless_alt sbintrunc_If)
  apply arith+
  done

(* Basic proofs that signed word div/mod operations are
 * truncations of their integer counterparts. *)

lemma signed_div_arith:
    "sint ((a::('a::len) word) sdiv b) = sbintrunc (len_of TYPE('a) - 1) (sint a sdiv sint b)"
  apply (subst word_sbin.norm_Rep [symmetric])
  apply (subst bin_sbin_eq_iff' [symmetric])
   apply simp
  apply (subst uint_sint [symmetric])
  apply (clarsimp simp: sdiv_int_def sdiv_word_def)
  apply (metis word_ubin.eq_norm)
  done

lemma signed_mod_arith:
    "sint ((a::('a::len) word) smod b) = sbintrunc (len_of TYPE('a) - 1) (sint a smod sint b)"
  apply (subst word_sbin.norm_Rep [symmetric])
  apply (subst bin_sbin_eq_iff' [symmetric])
   apply simp
  apply (subst uint_sint [symmetric])
  apply (clarsimp simp: smod_int_def smod_word_def)
  apply (metis word_ubin.eq_norm)
  done

(* Signed word arithmetic overflow constraints. *)

lemma signed_arith_ineq_checks_to_eq:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a + sint b = sint (a + b ))"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a - sint b = sint (a - b))"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    = ((- sint a) = sint (- a))"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a * sint b = sint (a * b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a sdiv sint b = sint (a sdiv b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a smod sint b = sint (a smod b))"
  by (auto simp: sint_word_ariths word_size signed_div_arith signed_mod_arith
                    sbintrunc_eq_in_range range_sbintrunc)

lemmas signed_arith_ineq_checks_to_eq_word32
    = signed_arith_ineq_checks_to_eq[where 'a=32, unfolded word32_bounds]
      signed_arith_ineq_checks_to_eq[where 'a="32 signed", unfolded word32_bounds]

lemma signed_arith_sint:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a + b) = (sint a + sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a - b) = (sint a - sint b)"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    \<Longrightarrow> sint (- a) = (- sint a)"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a * b) = (sint a * sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a sdiv b) = (sint a sdiv sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a smod b) = (sint a smod sint b)"
  by (metis signed_arith_ineq_checks_to_eq)+

lemma signed_mult_eq_checks_double_size:
  assumes mult_le: "(2 ^ (len_of TYPE ('a) - 1) + 1) ^ 2
       \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
    and le: "2 ^ (len_of TYPE('a) - 1) \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
  shows
  "(sint (a :: ('a :: len) word) * sint b = sint (a * b))
    = (scast a * scast b = (scast (a * b) :: ('b :: len) word))"
proof -
  have P: "sbintrunc (size a - 1) (sint a * sint b) \<in> range (sbintrunc (size a - 1))"
    by simp

  have abs: "!! x :: 'a word. abs (sint x) < 2 ^ (size a - 1) + 1"
    apply (cut_tac x=x in sint_range')
    apply (simp add: abs_le_iff word_size)
    done
  have abs_ab: "abs (sint a * sint b) < 2 ^ (len_of TYPE('b) - 1)"
    using abs_mult_less[OF abs[where x=a] abs[where x=b]] mult_le
    by (simp add: abs_mult power2_eq_square word_size)
  show ?thesis
    using P[unfolded range_sbintrunc] abs_ab le
    apply (simp add: sint_word_ariths scast_def)
    apply (simp add: wi_hom_mult)
    apply (subst word_sint.Abs_inject, simp_all)
     apply (simp add: sints_def range_sbintrunc
                      abs_less_iff)
    apply clarsimp
    apply (simp add: sints_def range_sbintrunc word_size)
    apply (auto elim: order_less_le_trans order_trans[rotated])
    done
qed

lemmas signed_mult_eq_checks32_to_64
    = signed_mult_eq_checks_double_size[where 'a=32 and 'b=64, simplified]
      signed_mult_eq_checks_double_size[where 'a="32 signed" and 'b=64, simplified]

(* Properties about signed division. *)

lemma int_sdiv_simps [simp]:
    "(a :: int) sdiv 1 = a"
    "(a :: int) sdiv 0 = 0"
    "(a :: int) sdiv -1 = -a"
  apply (auto simp: sdiv_int_def sgn_if)
  done

lemma sgn_div_eq_sgn_mult:
    "a div b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) div b) = sgn (a * b)"
  apply (clarsimp simp: sgn_if zero_le_mult_iff neg_imp_zdiv_nonneg_iff not_less)
  apply (metis less_le mult_le_0_iff neg_imp_zdiv_neg_iff not_less pos_imp_zdiv_neg_iff zdiv_eq_0_iff)
  done

lemma sgn_sdiv_eq_sgn_mult:
    "a sdiv b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) sdiv b) = sgn (a * b)"
  apply (clarsimp simp: sdiv_int_def sgn_times)
  apply (subst sgn_div_eq_sgn_mult)
   apply simp
  apply (clarsimp simp: sgn_times)
  apply (metis abs_mult div_0 div_mult_self2_is_id sgn_0_0 sgn_1_pos sgn_times zero_less_abs_iff)
  done

lemma int_sdiv_same_is_1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = a) = (b = 1)"
  apply (rule iffI)
   apply (clarsimp simp: sdiv_int_def)
   apply (subgoal_tac "b > 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if sign_simps)
    apply (clarsimp simp: sign_simps not_less)
    apply (metis int_div_same_is_1 le_neq_trans minus_minus neg_0_le_iff_le neg_equal_0_iff_equal)
   apply (case_tac "a > 0")
    apply (case_tac "b = 0")
     apply (clarsimp simp: sign_simps)
    apply (rule classical)
    apply (clarsimp simp: sign_simps sgn_times not_less)
    apply (metis le_less neg_0_less_iff_less not_less_iff_gr_or_eq pos_imp_zdiv_neg_iff)
   apply (rule classical)
   apply (clarsimp simp: sign_simps sgn_times not_less sgn_if split: if_splits)
   apply (metis antisym less_le neg_imp_zdiv_nonneg_iff)
  apply (clarsimp simp: sdiv_int_def sgn_if)
  done

lemma int_sdiv_negated_is_minus1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = - a) = (b = -1)"
  apply (clarsimp simp: sdiv_int_def)
  apply (rule iffI)
   apply (subgoal_tac "b < 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if sign_simps not_less)
    apply (case_tac "sgn (a * b) = -1")
     apply (clarsimp simp: not_less sign_simps)
    apply (clarsimp simp: sign_simps not_less)
   apply (rule classical)
   apply (case_tac "b = 0")
    apply (clarsimp simp: sign_simps not_less sgn_times)
   apply (case_tac "a > 0")
    apply (clarsimp simp: sign_simps not_less sgn_times)
    apply (metis less_le neg_less_0_iff_less not_less_iff_gr_or_eq pos_imp_zdiv_neg_iff)
   apply (clarsimp simp: sign_simps not_less sgn_times)
   apply (metis div_minus_right eq_iff neg_0_le_iff_le neg_imp_zdiv_nonneg_iff not_leE)
  apply (clarsimp simp: sgn_if)
  done

lemma sdiv_int_range:
    "(a :: int) sdiv b \<in> { - (abs a) .. (abs a) }"
  apply (unfold sdiv_int_def)
  apply (subgoal_tac "(abs a) div (abs b) \<le> (abs a)")
   apply (clarsimp simp: sgn_if)
   apply (metis Divides.transfer_nat_int_function_closures(1) abs_ge_zero
              abs_less_iff abs_of_nonneg less_asym less_minus_iff not_less)
  apply (metis abs_eq_0 abs_ge_zero div_by_0 zdiv_le_dividend zero_less_abs_iff)
  done

lemma word_sdiv_div1 [simp]:
    "(a :: ('a::len) word) sdiv 1 = a"
  apply (rule sint_1_cases [where a=a])
    apply (clarsimp simp: sdiv_word_def sdiv_int_def)
   apply (clarsimp simp: sdiv_word_def sdiv_int_def simp del: sint_minus1)
  apply (clarsimp simp: sdiv_word_def)
  done

lemma sdiv_int_div_0 [simp]:
  "(x :: int) sdiv 0 = 0"
  by (clarsimp simp: sdiv_int_def)

lemma sdiv_int_0_div [simp]:
  "0 sdiv (x :: int) = 0"
  by (clarsimp simp: sdiv_int_def)

lemma word_sdiv_div0 [simp]:
    "(a :: ('a::len) word) sdiv 0 = 0"
  apply (auto simp: sdiv_word_def sdiv_int_def sgn_if)
  done

lemma word_sdiv_div_minus1 [simp]:
    "(a :: ('a::len) word) sdiv -1 = -a"
  apply (auto simp: sdiv_word_def sdiv_int_def sgn_if)
  apply (metis wi_hom_neg word_sint.Rep_inverse')
  done

lemmas word_sdiv_0 = word_sdiv_div0

lemma sdiv_word_min:
    "- (2 ^ (size a - 1)) \<le> sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word)"
  apply (clarsimp simp: word_size)
  apply (cut_tac sint_range' [where x=a])
  apply (cut_tac sint_range' [where x=b])
  apply clarsimp
  apply (insert sdiv_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: max_def abs_if split: split_if_asm)
  done

lemma sdiv_word_max:
    "(sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word) < (2 ^ (size a - 1))) =
          ((a \<noteq> - (2 ^ (size a - 1)) \<or> (b \<noteq> -1)))"
    (is "?lhs = (\<not> ?a_int_min \<or> \<not> ?b_minus1)")
proof (rule classical)
  assume not_thesis: "\<not> ?thesis"

  have not_zero: "b \<noteq> 0"
    using not_thesis
    by (clarsimp)

  have result_range: "sint a sdiv sint b \<in> (sints (size a)) \<union> {2 ^ (size a - 1)}"
    apply (cut_tac sdiv_int_range [where a="sint a" and b="sint b"])
    apply (erule rev_subsetD)
    using sint_range' [where x=a]  sint_range' [where x=b]
    apply (auto simp: max_def abs_if word_size sints_num)
    done

  have result_range_overflow: "(sint a sdiv sint b = 2 ^ (size a - 1)) = (?a_int_min \<and> ?b_minus1)"
    apply (rule iffI [rotated])
     apply (clarsimp simp: sdiv_int_def sgn_if word_size sint_int_min)
    apply (rule classical)
    apply (case_tac "?a_int_min")
     apply (clarsimp simp: word_size sint_int_min)
     apply (metis diff_0_right
              int_sdiv_negated_is_minus1 minus_diff_eq minus_int_code(2)
              power_eq_0_iff sint_minus1 zero_neq_numeral)
    apply (subgoal_tac "abs (sint a) < 2 ^ (size a - 1)")
     apply (insert sdiv_int_range [where a="sint a" and b="sint b"])[1]
     apply (clarsimp simp: word_size)
    apply (insert sdiv_int_range [where a="sint a" and b="sint b"])[1]
    apply (insert word_sint.Rep [where x="a"])[1]
    apply (clarsimp simp: minus_le_iff word_size abs_if sints_num split: split_if_asm)
    apply (metis minus_minus sint_int_min word_sint.Rep_inject)
    done

  have result_range_simple: "(sint a sdiv sint b \<in> (sints (size a))) \<Longrightarrow> ?thesis"
    apply (insert sdiv_int_range [where a="sint a" and b="sint b"])
    apply (clarsimp simp: word_size sints_num sint_int_min)
    done

  show ?thesis
    apply (rule UnE [OF result_range result_range_simple])
     apply simp
    apply (clarsimp simp: word_size)
    using result_range_overflow
    apply (clarsimp simp: word_size)
    done
qed

lemmas sdiv_word_min' = sdiv_word_min [simplified word_size, simplified]
lemmas sdiv_word_max' = sdiv_word_max [simplified word_size, simplified]
lemmas sdiv_word32_max = sdiv_word_max [where 'a=32, simplified word_size, simplified]
    sdiv_word_max [where 'a="32 signed", simplified word_size, simplified]
lemmas sdiv_word32_min = sdiv_word_min [where 'a=32, simplified word_size, simplified]
    sdiv_word_min [where 'a="32 signed", simplified word_size, simplified]

lemmas word_sdiv_numerals_lhs = sdiv_word_def[where a="numeral x" for x]
    sdiv_word_def[where a=0] sdiv_word_def[where a=1]

lemmas word_sdiv_numerals = word_sdiv_numerals_lhs[where b="numeral y" for y]
    word_sdiv_numerals_lhs[where b=0] word_sdiv_numerals_lhs[where b=1]

(*
 * Signed modulo properties.
 *)

lemma smod_int_alt_def:
     "(a::int) smod b = sgn (a) * (abs a mod abs b)"
  apply (clarsimp simp: smod_int_def sdiv_int_def)
  apply (clarsimp simp: zmod_zdiv_equality' abs_sgn sgn_times sgn_if sign_simps)
  done

lemma smod_int_range:
  "b \<noteq> 0 \<Longrightarrow> (a::int) smod b \<in> { - abs b + 1 .. abs b - 1 }"
  apply (case_tac  "b > 0")
   apply (insert pos_mod_conj [where a=a and b=b])[1]
   apply (insert pos_mod_conj [where a="-a" and b=b])[1]
   apply (clarsimp simp: smod_int_alt_def sign_simps sgn_if
              abs_if not_less add1_zle_eq [simplified add.commute])
   apply (metis add_le_cancel_left monoid_add_class.add.right_neutral
             int_one_le_iff_zero_less less_le_trans mod_minus_right neg_less_0_iff_less
             neg_mod_conj not_less pos_mod_conj)
  apply (insert neg_mod_conj [where a=a and b="b"])[1]
  apply (insert neg_mod_conj [where a="-a" and b="b"])[1]
  apply (clarsimp simp: smod_int_alt_def sign_simps sgn_if
            abs_if not_less add1_zle_eq [simplified add.commute])
  apply (metis neg_0_less_iff_less neg_mod_conj not_le not_less_iff_gr_or_eq order_trans pos_mod_conj)
  done

lemma smod_int_compares:
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b < b"
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> -b < (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b < - b"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> b \<le> (a :: int) smod b"
  apply (insert smod_int_range [where a=a and b=b])
  apply (auto simp: add1_zle_eq smod_int_alt_def sgn_if)
  done

lemma smod_int_mod_0 [simp]:
  "x smod (0 :: int) = x"
  by (clarsimp simp: smod_int_def)

lemma smod_int_0_mod [simp]:
  "0 smod (x :: int) = 0"
  by (clarsimp simp: smod_int_alt_def)

lemma smod_word_mod_0 [simp]:
  "x smod (0 :: ('a::len) word) = x"
  by (clarsimp simp: smod_word_def)

lemma smod_word_0_mod [simp]:
  "0 smod (x :: ('a::len) word) = 0"
  by (clarsimp simp: smod_word_def)

lemma smod_word_max:
    "sint (a::'a word) smod sint (b::'a word) < 2 ^ (len_of TYPE('a::len) - Suc 0)"
  apply (case_tac "b = 0")
   apply (insert word_sint.Rep [where x=a, simplified sints_num])[1]
   apply (clarsimp)
  apply (insert word_sint.Rep [where x="b", simplified sints_num])[1]
  apply (insert smod_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: abs_if split: split_if_asm)
  done

lemma smod_word_min:
    "- (2 ^ (len_of TYPE('a::len) - Suc 0)) \<le> sint (a::'a word) smod sint (b::'a word)"
  apply (case_tac "b = 0")
   apply (insert word_sint.Rep [where x=a, simplified sints_num])[1]
   apply clarsimp
  apply (insert word_sint.Rep [where x=b, simplified sints_num])[1]
  apply (insert smod_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: abs_if add1_zle_eq split: split_if_asm)
  done

lemma smod_word_alt_def:
  "(a :: ('a::len) word) smod b = a - (a sdiv b) * b"
  apply (case_tac "a \<noteq> - (2 ^ (len_of TYPE('a) - 1)) \<or> b \<noteq> -1")
   apply (clarsimp simp: smod_word_def sdiv_word_def smod_int_def
             minus_word.abs_eq [symmetric] times_word.abs_eq [symmetric])
  apply (clarsimp simp: smod_word_def smod_int_def)
  done

lemmas word_smod_numerals_lhs = smod_word_def[where a="numeral x" for x]
    smod_word_def[where a=0] smod_word_def[where a=1]

lemmas word_smod_numerals = word_smod_numerals_lhs[where b="numeral y" for y]
    word_smod_numerals_lhs[where b=0] word_smod_numerals_lhs[where b=1]

lemma sint_of_int_eq:
  "\<lbrakk> - (2 ^ (len_of TYPE('a) - 1)) \<le> x; x < 2 ^ (len_of TYPE('a) - 1) \<rbrakk> \<Longrightarrow> sint (of_int x :: ('a::len) word) = x"
  apply (clarsimp simp: word_of_int int_word_sint)
  apply (subst int_mod_eq')
    apply simp
   apply (subst (2) power_minus_simp)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

lemmas sint32_of_int_eq = sint_of_int_eq [where 'a=32, simplified]

lemma of_int_sint [simp]:
    "of_int (sint a) = a"
  apply (insert word_sint.Rep [where x=a])
  apply (clarsimp simp: word_of_int)
  done


lemma ucast_of_nats [simp]:
     "(ucast (of_nat x :: word32) :: sword32) = (of_nat x)"
     "(ucast (of_nat x :: word32) :: sword16) = (of_nat x)"
     "(ucast (of_nat x :: word32) :: sword8) = (of_nat x)"
     "(ucast (of_nat x :: word16) :: sword16) = (of_nat x)"
     "(ucast (of_nat x :: word16) :: sword8) = (of_nat x)"
     "(ucast (of_nat x :: word8) :: sword8) = (of_nat x)"
  apply (auto simp: ucast_of_nat is_down)
  done

lemma nth_w2p_scast [simp]:
  "((scast ((2::'a::len signed word) ^ n) :: 'a word) !! m)
         \<longleftrightarrow> ((((2::'a::len  word) ^ n) :: 'a word) !! m)"
  apply (subst nth_w2p)
  apply (case_tac "n \<ge> len_of TYPE('a)")
   apply (subst power_overflow, simp)
   apply clarsimp
  apply (metis nth_w2p scast_def bang_conj_lt
               len_signed nth_word_of_int word_sint.Rep_inverse)
  done

lemma scast_2_power [simp]: "scast ((2 :: 'a::len signed word) ^ x) = ((2 :: 'a word) ^ x)"
  by (clarsimp simp: word_eq_iff)

lemma scast_bit_test [simp]:
    "scast ((1 :: 'a::len signed word) << n) = (1 :: 'a word) << n"
  by (clarsimp simp: word_eq_iff)

lemma ucast_nat_def':
  "of_nat (unat x) = (ucast :: ('a :: len) word \<Rightarrow> ('b :: len) signed word) x"
  by (simp add: ucast_def word_of_int_nat unat_def)

lemma mod_mod_power_int:
  fixes k :: int
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
  by (metis bintrunc_bintrunc_min bintrunc_mod2p min.commute)

(* Normalise combinations of scast and ucast. *)

lemma ucast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ len_of TYPE('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ len_of TYPE('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ len_of TYPE('b))) (y mod (2 ^ len_of TYPE('b)))) mod (2 ^ len_of TYPE('b))
                               = (L x y) mod (2 ^ len_of TYPE('b))"
  assumes is_down: "is_down (ucast :: 'a word \<Rightarrow> 'b word)"
  shows "ucast (M a b) = M' (ucast a) (ucast b)"
  apply (clarsimp simp: word_of_int ucast_def)
  apply (subst lift_M)
  apply (subst of_int_uint [symmetric], subst lift_M')
  apply (subst (1 2) int_word_uint)
  apply (subst word_of_int)
  apply (subst word.abs_eq_iff)
  apply (subst (1 2) bintrunc_mod2p)
  apply (insert is_down)
  apply (unfold is_down_def)
  apply (clarsimp simp: target_size source_size)
  apply (clarsimp simp: mod_mod_power_int min_def)
  apply (rule distrib [symmetric])
  done

lemma ucast_down_add:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) + b) = (ucast a + ucast b :: 'b::len word)"
  by (rule ucast_distrib [where L="op +"], (clarsimp simp: uint_word_ariths)+, presburger, simp)

lemma ucast_down_minus:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) - b) = (ucast a - ucast b :: 'b::len word)"
  apply (rule ucast_distrib [where L="op -"], (clarsimp simp: uint_word_ariths)+)
  apply (metis zdiff_zmod_left zdiff_zmod_right)
  apply simp
  done

lemma ucast_down_mult:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) * b) = (ucast a * ucast b :: 'b::len word)"
  apply (rule ucast_distrib [where L="op *"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_mult_eq)
  apply simp
  done

lemma scast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ len_of TYPE('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ len_of TYPE('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ len_of TYPE('b))) (y mod (2 ^ len_of TYPE('b)))) mod (2 ^ len_of TYPE('b))
                               = (L x y) mod (2 ^ len_of TYPE('b))"
  assumes is_down: "is_down (scast :: 'a word \<Rightarrow> 'b word)"
  shows "scast (M a b) = M' (scast a) (scast b)"
  apply (subst (1 2 3) down_cast_same [symmetric])
   apply (insert is_down)
   apply (clarsimp simp: is_down_def target_size source_size is_down)
  apply (rule ucast_distrib [where L=L, OF lift_M lift_M' distrib])
  apply (insert is_down)
  apply (clarsimp simp: is_down_def target_size source_size is_down)
  done

lemma scast_down_add:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) + b) = (scast a + scast b :: 'b::len word)"
  by (rule scast_distrib [where L="op +"], (clarsimp simp: uint_word_ariths)+, presburger, simp)

lemma scast_down_minus:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) - b) = (scast a - scast b :: 'b::len word)"
  apply (rule scast_distrib [where L="op -"], (clarsimp simp: uint_word_ariths)+)
  apply (metis zdiff_zmod_left zdiff_zmod_right)
  apply simp
  done

lemma scast_down_mult:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) * b) = (scast a * scast b :: 'b::len word)"
  apply (rule scast_distrib [where L="op *"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_mult_eq)
  apply simp
  done

lemma scast_ucast_1:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma scast_ucast_3:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma scast_ucast_4:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma scast_scast_b:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_def sint_up_scast)

lemma ucast_scast_1:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_def ucast_down_wi)

lemma ucast_scast_3:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_def ucast_down_wi)

lemma ucast_scast_4:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis down_cast_same scast_def sint_up_scast)

lemma ucast_ucast_a:
  "\<lbrakk> is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
        (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma ucast_ucast_b:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis ucast_up_ucast)

lemma scast_scast_a:
  "\<lbrakk> is_down (scast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  apply (clarsimp simp: scast_def)
  apply (metis down_cast_same is_up_down scast_def ucast_down_wi)
  done

lemma scast_down_wi [OF refl]:
  "uc = scast \<Longrightarrow> is_down uc \<Longrightarrow> uc (word_of_int x) = word_of_int x"
  by (metis down_cast_same is_up_down ucast_down_wi)

lemmas cast_simps =
  is_down is_up
  scast_down_add scast_down_minus scast_down_mult
  ucast_down_add ucast_down_minus ucast_down_mult
  scast_ucast_1 scast_ucast_3 scast_ucast_4
  ucast_scast_1 ucast_scast_3 ucast_scast_4
  ucast_ucast_a ucast_ucast_b
  scast_scast_a scast_scast_b
  ucast_down_bl
  ucast_down_wi scast_down_wi
  ucast_of_nat scast_of_nat
  uint_up_ucast sint_up_scast
  up_scast_surj up_ucast_surj

lemma smod_mod_positive:
    "\<lbrakk> 0 \<le> (a :: int); 0 \<le> b \<rbrakk> \<Longrightarrow> a smod b = a mod b"
  by (clarsimp simp: smod_int_alt_def zsgn_def)

lemmas signed_shift_guard_simpler_32
    = power_strict_increasing_iff[where b="2 :: nat" and y=31, simplified]

lemma nat_mult_power_less_eq:
  "b > 0 \<Longrightarrow> (a * b ^ n < (b :: nat) ^ m) = (a < b ^ (m - n))"
  using mult_less_cancel2[where m = a and k = "b ^ n" and n="b ^ (m - n)"]
        mult_less_cancel2[where m="a * b ^ (n - m)" and k="b ^ m" and n=1]
  apply (simp only: power_add[symmetric] nat_minus_add_max)
  apply (simp only: power_add[symmetric] nat_minus_add_max ac_simps)
  apply (simp add: max_def split: split_if_asm)
  done

lemma signed_shift_guard_to_word:
  "\<lbrakk> n < len_of TYPE ('a); n > 0 \<rbrakk>
    \<Longrightarrow> (unat (x :: ('a :: len) word) * 2 ^ y < 2 ^ n)
    = (x = 0 \<or> x < (1 << n >> y))"
  apply (simp only: nat_mult_power_less_eq)
  apply (cases "y \<le> n")
   apply (simp only: shiftl_shiftr1)
   apply (subst less_mask_eq)
    apply (simp add: word_less_nat_alt word_size)
    apply (rule order_less_le_trans[rotated], rule power_increasing[where n=1])
      apply simp
     apply simp
    apply simp
   apply (simp add: nat_mult_power_less_eq word_less_nat_alt word_size)
   apply auto[1]
  apply (simp only: shiftl_shiftr2, simp add: unat_eq_0)
  done

lemma word32_31_less:
  "31 < len_of TYPE (32 signed)" "31 > (0 :: nat)"
  "31 < len_of TYPE (32)" "31 > (0 :: nat)"
  by auto

lemmas signed_shift_guard_to_word_32
    = signed_shift_guard_to_word[OF word32_31_less(1-2)]
    signed_shift_guard_to_word[OF word32_31_less(3-4)]

lemma sint_ucast_eq_uint:
    "\<lbrakk> \<not> is_down (ucast :: ('a::len word \<Rightarrow> 'b::len word)) \<rbrakk>
            \<Longrightarrow> sint ((ucast :: ('a::len word \<Rightarrow> 'b::len word)) x) = uint x"
  apply (subst sint_eq_uint)
   apply (clarsimp simp: msb_nth nth_ucast is_down)
   apply (metis Suc_leI Suc_pred bang_conj_lt len_gt_0)
  apply (clarsimp simp: uint_up_ucast is_up is_down)
  done

lemma word_less_nowrapI':
  "(x :: 'a :: len0 word) \<le> z - k \<Longrightarrow> k \<le> z \<Longrightarrow> 0 < k \<Longrightarrow> x < x + k"
  by uint_arith

lemma mask_plus_1:
  "mask n + 1 = 2 ^ n"
  by (clarsimp simp: mask_def)

lemma unat_inj: "inj unat"
  by (metis eq_iff injI word_le_nat_alt)

lemma unat_ucast_upcast:
  "is_up (ucast :: 'b word \<Rightarrow> 'a word)
      \<Longrightarrow> unat (ucast x :: ('a::len) word) = unat (x :: ('b::len) word)"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply (clarsimp simp: is_up)
  apply simp
  done

lemma ucast_mono:
  "\<lbrakk> (x :: 'b :: len word) < y; y < 2 ^ len_of TYPE('a) \<rbrakk>
   \<Longrightarrow> ucast x < ((ucast y) :: ('a :: len) word)"
  apply (simp add: ucast_nat_def [symmetric])
  apply (rule of_nat_mono_maybe)
  apply (rule unat_less_helper)
  apply (simp add: Power.of_nat_power)
  apply (simp add: word_less_nat_alt)
  done

lemma ucast_mono_le:
  "\<lbrakk>x \<le> y; y < 2 ^ len_of TYPE('b)\<rbrakk> \<Longrightarrow> (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> ucast y"
  apply (simp add: ucast_nat_def [symmetric])
  apply (subst of_nat_mono_maybe_le[symmetric])
    apply (rule unat_less_helper)
    apply (simp add: Power.of_nat_power)
   apply (rule unat_less_helper)
   apply (erule le_less_trans)
   apply (simp add: Power.of_nat_power)
  apply (simp add: word_le_nat_alt)
  done

lemma zero_sle_ucast_up:
  "\<not> is_down (ucast :: 'a word \<Rightarrow> 'b signed word) \<Longrightarrow>
          (0 <=s ((ucast (b::('a::len) word)) :: ('b::len) signed word))"
  apply (subgoal_tac "\<not> msb (ucast b :: 'b signed word)")
   apply (clarsimp simp: word_sle_msb_le)
  apply (clarsimp simp: is_down not_le msb_nth nth_ucast)
  apply (subst (asm) bang_conj_lt [symmetric])
  apply clarsimp
  apply arith
  done

lemma msb_ucast_eq:
    "len_of TYPE('a) = len_of TYPE('b) \<Longrightarrow>
         msb (ucast x :: ('a::len) word) = msb (x :: ('b::len) word)"
  apply (clarsimp simp: word_msb_alt)
  apply (subst ucast_down_drop [where n=0])
   apply (clarsimp simp: source_size_def target_size_def word_size)
  apply clarsimp
  done

lemma msb_big:
     "msb (a :: ('a::len) word) = (a \<ge> 2 ^ (len_of TYPE('a)  - Suc 0))"
  apply (rule iffI)
   apply (clarsimp simp: msb_nth)
   apply (drule bang_is_le)
   apply simp
  apply (rule ccontr)
  apply (subgoal_tac "a = a && mask (len_of TYPE('a) - Suc 0)")
   apply (cut_tac and_mask_less' [where w=a and n="len_of TYPE('a) - Suc 0"])
    apply (clarsimp simp: word_not_le [symmetric])
   apply clarsimp
  apply (rule sym, subst and_mask_eq_iff_shiftr_0)
  apply (clarsimp simp: msb_shift)
  done

lemma zero_sle_ucast:
  "(0 <=s ((ucast (b::('a::len) word)) :: ('a::len) signed word))
                = (uint b < 2 ^ (len_of (TYPE('a)) - 1))"
  apply (case_tac "msb b")
   apply (clarsimp simp: word_sle_msb_le not_less msb_ucast_eq del: notI)
   apply (clarsimp simp: msb_big word_le_def uint_2p_alt)
  apply (clarsimp simp: word_sle_msb_le not_less msb_ucast_eq del: notI)
  apply (clarsimp simp: msb_big word_le_def uint_2p_alt)
  done


(* to_bool / from_bool. *)

definition
  from_bool :: "bool \<Rightarrow> 'a::len word" where
  "from_bool b \<equiv> case b of True \<Rightarrow> of_nat 1
                         | False \<Rightarrow> of_nat 0"

lemma from_bool_0:
  "(from_bool x = 0) = (\<not> x)"
  by (simp add: from_bool_def split: bool.split)

definition
  to_bool :: "'a::len word \<Rightarrow> bool" where
  "to_bool \<equiv> (op \<noteq>) 0"

lemma to_bool_and_1:
  "to_bool (x && 1) = (x !! 0)"
  apply (simp add: to_bool_def)
  apply (rule iffI)
   apply (rule classical, erule notE, rule word_eqI)
   apply clarsimp
   apply (case_tac n, simp_all)[1]
  apply (rule notI, drule word_eqD[where x=0])
  apply simp
  done

lemma to_bool_from_bool:
  "to_bool (from_bool r) = r"
  unfolding from_bool_def to_bool_def
  by (simp split: bool.splits)

lemma from_bool_neq_0:
  "(from_bool b \<noteq> 0) = b"
  by (simp add: from_bool_def split: bool.splits)

lemma from_bool_mask_simp:
  "((from_bool r) :: word32) && 1 = from_bool r"
  unfolding from_bool_def
  apply (clarsimp split: bool.splits)
  done

lemma scast_from_bool:
  "scast (from_bool P::word32) = (from_bool P::word32)"
  by (clarsimp simp: from_bool_def scast_id split: bool.splits)

lemma from_bool_1:
  "(from_bool P = 1) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma ge_0_from_bool:
  "(0 < from_bool P) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma limited_and_from_bool:
  "limited_and (from_bool b) 1"
  by (simp add: from_bool_def limited_and_def split: bool.split)

lemma to_bool_1 [simp]: "to_bool 1" by (simp add: to_bool_def)
lemma to_bool_0 [simp]: "\<not>to_bool 0" by (simp add: to_bool_def)

lemma from_bool_eq_if:
  "(from_bool Q = (if P then 1 else 0)) = (P = Q)"
  by (simp add: case_bool_If from_bool_def split: split_if)

lemma to_bool_eq_0:
  "(\<not> to_bool x) = (x = 0)"
  by (simp add: to_bool_def)

lemma to_bool_neq_0:
  "(to_bool x) = (x \<noteq> 0)"
  by (simp add: to_bool_def)

lemma from_bool_all_helper:
  "(\<forall>bool. from_bool bool = val \<longrightarrow> P bool)
      = ((\<exists>bool. from_bool bool = val) \<longrightarrow> P (val \<noteq> 0))"
  by (auto simp: from_bool_0)

lemma word_rsplit_upt:
  "\<lbrakk> size x = len_of TYPE('a :: len) * n; n \<noteq> 0 \<rbrakk>
    \<Longrightarrow> word_rsplit x = map (\<lambda>i. ucast (x >> i * len_of TYPE ('a)) :: 'a word) (rev [0 ..< n])"
  apply (subgoal_tac "length (word_rsplit x :: 'a word list) = n")
   apply (rule nth_equalityI, simp)
   apply (intro allI word_eqI impI)
   apply (simp add: test_bit_rsplit_alt word_size)
   apply (simp add: nth_ucast nth_shiftr nth_rev field_simps)
  apply (simp add: length_word_rsplit_exp_size)
  apply (metis mult.commute given_quot_alt word_size word_size_gt_0)
  done

lemma aligned_shift:
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> x + y >> n = y >> n"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: is_aligned_nth)
   apply (drule(1) nth_bounded)
    apply simp
   apply simp
  apply (rule word_eqI)
  apply (simp add: nth_shiftr)
  apply safe
  apply (drule(1) nth_bounded)
  apply simp+
  done

lemma aligned_shift':
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> y + x >> n = y >> n"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: is_aligned_nth)
   apply (drule(1) nth_bounded)
    apply simp
   apply simp
  apply (rule word_eqI)
  apply (simp add: nth_shiftr)
  apply safe
  apply (drule(1) nth_bounded)
  apply simp+
done

lemma neg_mask_add_mask:
  "((x:: 'a :: len word) && ~~ mask n) + (2 ^ n - 1) = x || mask n"
  apply (simp add:mask_2pm1[symmetric])
  apply (rule word_eqI)
  apply (rule iffI)
    apply (clarsimp simp:word_size not_less)
    apply (cut_tac w = "((x && ~~ mask n) + mask n)" and
      m = n and n = "na - n" in nth_shiftr[symmetric])
    apply clarsimp
    apply (subst (asm) aligned_shift')
  apply (simp add:mask_lt_2pn nth_shiftr is_aligned_neg_mask word_size word_bits_def )+
  apply (case_tac "na<n")
    apply clarsimp
    apply (subst word_plus_and_or_coroll)
    apply (rule iffD1[OF is_aligned_mask])
    apply (simp add:is_aligned_neg_mask word_size not_less)+
  apply (cut_tac w = "((x && ~~ mask n) + mask n)" and
      m = n and n = "na - n" in nth_shiftr[symmetric])
  apply clarsimp
  apply (subst (asm) aligned_shift')
  apply (simp add:mask_lt_2pn is_aligned_neg_mask word_bits_def nth_shiftr neg_mask_bang)+
done

lemma subtract_mask:
  "p - (p && mask n) = (p && ~~ mask n)"
  "p - (p && ~~ mask n) = (p && mask n)"
  by (simp add: field_simps word_plus_and_or_coroll2)+

lemma and_neg_mask_plus_mask_mono: "(p && ~~ mask n) + mask n \<ge> p"
  apply (rule word_le_minus_cancel[where x = "p && ~~ mask n"])
   apply (clarsimp simp: subtract_mask)
   using word_and_le1[where a = "mask n" and y = p]
   apply (clarsimp simp: mask_def word_le_less_eq)
  apply (rule is_aligned_no_overflow'[folded mask_2pm1])
  apply (clarsimp simp: is_aligned_neg_mask)
  done

lemma word_neg_and_le:
  "ptr \<le> (ptr && ~~ mask n) + (2 ^ n - 1)"
  by (simp add: and_neg_mask_plus_mask_mono mask_2pm1[symmetric])

lemma aligned_less_plus_1:
  "\<lbrakk> is_aligned x n; n > 0 \<rbrakk> \<Longrightarrow> x < x + 1"
  apply (rule plus_one_helper2)
   apply (rule order_refl)
  apply (clarsimp simp: field_simps)
  apply (drule arg_cong[where f="\<lambda>x. x - 1"])
  apply (clarsimp simp: is_aligned_mask)
  apply (drule word_eqD[where x=0])
  apply simp
  done

lemma aligned_add_offset_less:
  "\<lbrakk>is_aligned x n; is_aligned y n; x < y; z < 2 ^ n\<rbrakk> \<Longrightarrow> x + z < y"
  apply (cases "y = 0")
   apply simp
  apply (erule is_aligned_get_word_bits[where p=y], simp_all)
  apply (cases "z = 0", simp_all)
  apply (drule(2) aligned_at_least_t2n_diff[rotated -1])
  apply (drule plus_one_helper2)
   apply (rule less_is_non_zero_p1)
   apply (rule aligned_less_plus_1)
    apply (erule aligned_sub_aligned[OF _ _ order_refl],
           simp_all add: is_aligned_triv)[1]
   apply (cases n, simp_all)[1]
  apply (simp only: trans[OF diff_add_eq diff_diff_eq2[symmetric]])
  apply (drule word_less_add_right)
   apply (rule ccontr, simp add: linorder_not_le)
   apply (drule aligned_small_is_0, erule order_less_trans)
    apply (clarsimp simp: power_overflow)
   apply simp
  apply (erule order_le_less_trans[rotated],
         rule word_plus_mono_right)
   apply (erule minus_one_helper3)
  apply (simp add: is_aligned_no_wrap' is_aligned_no_overflow field_simps)
  done

lemma is_aligned_add_helper:
  "\<lbrakk> is_aligned p n; d < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p + d && mask n = d) \<and> (p + d && (~~ mask n) = p)"
  apply (subst(asm) is_aligned_mask)
  apply (drule less_mask_eq)
  apply (rule context_conjI)
   apply (subst word_plus_and_or_coroll)
    apply (rule word_eqI)
    apply (drule_tac x=na in word_eqD)+
    apply (simp add: word_size)
    apply blast
   apply (rule word_eqI)
   apply (drule_tac x=na in word_eqD)+
   apply (simp add: word_ops_nth_size word_size)
   apply blast
  apply (insert word_plus_and_or_coroll2[where x="p + d" and w="mask n"])
  apply simp
  done

lemma is_aligned_sub_helper:
  "\<lbrakk> is_aligned (p - d) n; d < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p && mask n = d) \<and> (p && (~~ mask n) = p - d)"
  by (drule(1) is_aligned_add_helper, simp)

lemma mask_twice:
  "(x && mask n) && mask m = x && mask (min m n)"
  apply (rule word_eqI)
  apply (simp add: word_size conj_comms)
  done

lemma is_aligned_after_mask:
  "\<lbrakk>is_aligned k m;m\<le> n\<rbrakk> \<Longrightarrow> is_aligned (k && mask n) m"
  by (metis is_aligned_andI1)

lemma and_mask_plus:
  "\<lbrakk>is_aligned ptr m; m \<le> n; n < 32; a < 2 ^ m\<rbrakk>
   \<Longrightarrow> (ptr) + a && mask n = (ptr && mask n) + a"
  apply (rule mask_eqI[where n = m])
   apply (simp add:mask_twice min_def)
    apply (simp add:is_aligned_add_helper)
    apply (subst is_aligned_add_helper[THEN conjunct1])
      apply (erule is_aligned_after_mask)
     apply simp
    apply simp
   apply simp
  apply (subgoal_tac "(ptr + a && mask n) && ~~ mask m
     = (ptr + a && ~~ mask m ) && mask n")
   apply (simp add:is_aligned_add_helper)
   apply (subst is_aligned_add_helper[THEN conjunct2])
     apply (simp add:is_aligned_after_mask)
    apply simp
   apply simp
  apply (simp add:word_bw_comms word_bw_lcs)
  done

lemma le_step_down_word:"\<lbrakk>(i::('a::len) word) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply unat_arith
  done

lemma le_step_down_word_2:
  fixes x :: "'a::len word"
  shows "\<lbrakk>x \<le>  y; x \<noteq> y\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (subst (asm) word_le_less_eq,
      clarsimp,
      simp add: minus_one_helper3)

lemma le_step_down_word_3:
  fixes x :: "32 word"
  shows "\<lbrakk>x \<le>  y; x \<noteq> y; y < 2 ^ 32 - 1\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (rule le_step_down_word_2, assumption+)

lemma NOT_mask_AND_mask[simp]: "(w && mask n) && ~~ mask n = 0"
  apply (clarsimp simp:mask_def)
  by (metis word_bool_alg.conj_cancel_right word_bool_alg.conj_zero_right word_bw_comms(1) word_bw_lcs(1))

lemma and_and_not[simp]:"(a && b) && ~~ b = 0"
  apply (subst word_bw_assocs(1))
  apply clarsimp
  done

lemma mask_shift_and_negate[simp]:"(w && mask n << m) && ~~ (mask n << m) = 0"
  apply (clarsimp simp:mask_def)
  by (metis (erased, hide_lams) mask_eq_x_eq_0 shiftl_over_and_dist word_bool_alg.conj_absorb word_bw_assocs(1))

lemma shiftr_1[simplified]:"(x::word32) >> 1 = 0 \<Longrightarrow> x < 2"
  apply word_bitwise apply clarsimp
  done

lemma le_step_down_nat:"\<lbrakk>(i::nat) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply arith
  done

lemma le_step_down_int:"\<lbrakk>(i::int) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma mask_step_down:"(b::32word) && 0x1 = (1::32word) \<Longrightarrow> (\<exists>x. x < 32 \<and> mask x = b >> 1) \<Longrightarrow> (\<exists>x. mask x = b)"
  apply clarsimp
  apply (rule_tac x="x + 1" in exI)
  apply (subgoal_tac "x \<le> 31")
   apply (erule le_step_down_nat, clarsimp simp:mask_def, word_bitwise, clarsimp+)+
   apply (clarsimp simp:mask_def, word_bitwise, clarsimp)
  apply clarsimp
  done

lemma mask_1[simp]: "(\<exists>x. mask x = 1)"
  apply (rule_tac x=1 in exI)
  apply (simp add:mask_def)
  done

lemma not_switch:"~~ a = x \<Longrightarrow> a = ~~ x"
  by auto

(* The seL4 bitfield generator produces functions containing mask and shift operations, such that
 * invoking two of them consecutively can produce something like the following. Note that it is
 * unlikely you'll be able to use this lemma directly, hence the second one below.
 *)
lemma bitfield_op_twice':"(x && ~~ (mask n << m) || ((y && mask n) << m)) && ~~ (mask n << m) = x && ~~ (mask n << m)"
  apply (induct n arbitrary: m)
   apply simp 
  apply (subst word_ao_dist)
  apply (simp add:AND_twice)
  done

(* Helper to get bitfield_op_twice' to apply to code produced by the bitfield generator as it
 * appears in the wild. You'll probably need e.g.
 *  apply (clarsimp simp:bitfield_op_twice[unfolded mask_def, where n=5 and m=3, simplified])
 *)
lemma bitfield_op_twice:
  "((x::word32) && ~~ (mask n << m) || ((y && mask n) << m)) && ~~ (mask n << m) = x && ~~ (mask n << m)"
  by (rule bitfield_op_twice')

lemma bitfield_op_twice'': "\<lbrakk>~~ a = b << c; \<exists>x. b = mask x\<rbrakk> \<Longrightarrow> (x && a || (y && b << c)) && a = x && a"
  apply clarsimp
  apply (cut_tac n=xa and m=c and x=x and y=y in bitfield_op_twice')
  apply (clarsimp simp:mask_def)
  apply (drule not_switch)
  apply clarsimp
  done

lemma bit_twiddle_min:" (y::sword32) xor (((x::sword32) xor y) && (if x < y then -1 else 0)) = min x y"
  by (metis (mono_tags) min_def word_bitwise_m1_simps(2) word_bool_alg.xor_left_commute word_bool_alg.xor_self word_bool_alg.xor_zero_right word_bw_comms(1) word_le_less_eq word_log_esimps(7))

lemma bit_twiddle_max:"(x::sword32) xor (((x::sword32) xor y) && (if x < y then -1 else 0)) = max x y"
  by (metis (mono_tags) max_def word_bitwise_m1_simps(2) word_bool_alg.xor_left_self word_bool_alg.xor_zero_right word_bw_comms(1) word_le_less_eq word_log_esimps(7))
   
lemma has_zero_byte:
  "~~ (((((v::word32) && 0x7f7f7f7f) + 0x7f7f7f7f) || v) || 0x7f7f7f7f) \<noteq> 0
    \<Longrightarrow> v && 0xff000000 = 0 \<or> v && 0xff0000 = 0 \<or> v && 0xff00 = 0 \<or> v && 0xff = 0"
  apply clarsimp
  apply word_bitwise
  by metis

lemma swap_with_xor:"\<lbrakk>(x::word32) = a xor b; y = b xor x; z = x xor y\<rbrakk> \<Longrightarrow> z = b \<and> y = a"
  by (metis word_bool_alg.xor_assoc word_bool_alg.xor_commute word_bool_alg.xor_self word_bool_alg.xor_zero_right)

lemma scast_nop_1:"((scast ((of_int x)::('a::len) word))::'a sword) = of_int x"
  apply (clarsimp simp:scast_def word_of_int)
  by (metis len_signed sint_sbintrunc' word_sint.Rep_inverse)

lemma scast_nop_2:"((scast ((of_int x)::('a::len) sword))::'a word) = of_int x"
  apply (clarsimp simp:scast_def word_of_int)
  by (metis len_signed sint_sbintrunc' word_sint.Rep_inverse)

lemmas scast_nop[simp] = scast_nop_1 scast_nop_2 scast_id

lemma le_mask_imp_and_mask:"(x::word32) \<le> mask n \<Longrightarrow> x && mask n = x"
  by (metis and_mask_eq_iff_le_mask)

lemma or_not_mask_nop:"((x::word32) || ~~ mask n) && mask n = x && mask n"
  by (metis word_and_not word_ao_dist2 word_bw_comms(1) word_log_esimps(3))

lemma mask_exceed:"n \<ge> 32 \<Longrightarrow> (x::word32) && ~~ mask n = 0"
  apply (metis (erased, hide_lams) is_aligned_neg_mask is_aligned_neg_mask_eq mask_32_max_word
                                   word_bool_alg.compl_one word_bool_alg.conj_zero_right)
  done

lemma mask_subsume:"\<lbrakk>n \<le> m\<rbrakk> \<Longrightarrow> ((x::word32) || y && mask n) && ~~ mask m = x && ~~ mask m"
  apply (subst word_ao_dist)
  apply (subgoal_tac "(y && mask n) && ~~ mask m = 0")
   apply simp
  by (metis (no_types, hide_lams) is_aligned_mask is_aligned_weaken word_and_not word_bool_alg.conj_zero_right word_bw_comms(1) word_bw_lcs(1))

lemma mask_twice2:"n \<le> m \<Longrightarrow> ((x::word32) && mask m) && mask n = x && mask n"
  by (metis mask_twice min_def)

(* Helper for dealing with casts of IPC buffer message register offsets.
 * XXX: There is almost certainly a more pleasant way to do this proof.
 *)
lemma unat_nat:"\<lbrakk>i \<ge> 0; i \<le>2 ^ 31\<rbrakk> \<Longrightarrow> (unat ((of_int i)::sword32)) = nat i"
  unfolding unat_def apply (subst eq_nat_nat_iff, clarsimp+)
  apply (subst Int.ring_1_class.of_nat_nat[symmetric], clarsimp+,
         subst Word.word_of_int_nat[symmetric], clarsimp+)
  apply (rule Word.word_uint.Abs_inverse)
  apply clarsimp
  apply (subst Word.uints_unats)
  apply (induct i, (simp add:unats_def)+)
  done

(* FIXME: MOVE *)
lemma pow_2_gt:"n \<ge> 2 \<Longrightarrow> (2::int) < 2 ^ n"
  apply (induct n)
   apply simp+
  done

lemma uint_2_id:"len_of TYPE('a) \<ge> 2 \<Longrightarrow> uint (2::('a::len) word) = 2"
  apply clarsimp
  apply (subgoal_tac "2 \<in> uints (len_of TYPE('a))")
   apply (subst (asm) Word.word_ubin.set_iff_norm)
   apply simp
  apply (subst word_uint.set_iff_norm)
  apply clarsimp
  apply (rule int_mod_eq')
   apply simp
  apply (rule pow_2_gt)
  apply simp
  done

(* FIXME: MOVE *)
lemma bintrunc_id:"\<lbrakk>of_nat n \<ge> m; m > 0\<rbrakk> \<Longrightarrow> bintrunc n m = m"
  apply (subst bintrunc_mod2p)
  apply (rule int_mod_eq')
   apply simp+
  apply (induct n arbitrary:m)
   apply simp+
  by force

lemma shiftr1_unfold:"shiftr1 x = x >> 1"
  by (metis One_nat_def comp_apply funpow.simps(1) funpow.simps(2) id_apply shiftr_def)

lemma shiftr1_is_div_2:"(x::('a::len) word) >> 1 = x div 2"
  apply (case_tac "len_of TYPE('a) = 1")
   apply simp
   apply (subgoal_tac "x = 0 \<or> x = 1")
    apply (erule disjE)
     apply (clarsimp simp:word_div_def)+
   apply (metis One_nat_def less_irrefl_nat sint_1_cases)
  apply clarsimp
  apply (subst word_div_def)
  apply clarsimp
  apply (subst bintrunc_id)
    apply (subgoal_tac "2 \<le> len_of TYPE('a)")
     apply simp
    apply (metis (no_types) le_0_eq le_SucE lens_not_0(2) not_less_eq_eq numeral_2_eq_2)
   apply simp
  apply (subst bin_rest_def[symmetric])
  apply (subst shiftr1_def[symmetric])
  apply (clarsimp simp:shiftr1_unfold)
  done

lemma shiftl1_is_mult: "(x << 1) = (x :: 'a::len word) * 2"
  by (metis One_nat_def mult_2 mult_2_right one_add_one
        power_0 power_Suc shiftl_t2n)

lemma div_of_0_id[simp]:"(0::('a::len) word) div n = 0"
  by (simp add: word_div_def)

lemma degenerate_word:"len_of TYPE('a) = 1 \<Longrightarrow> (x::('a::len) word) = 0 \<or> x = 1"
  by (metis One_nat_def less_irrefl_nat sint_1_cases)

lemma div_by_0_word:"(x::('a::len) word) div 0 = 0"
  by (metis div_0 div_by_0 unat_0 word_arith_nat_defs(6) word_div_1)

lemma div_less_dividend_word:"\<lbrakk>x \<noteq> 0; n \<noteq> 1\<rbrakk> \<Longrightarrow> (x::('a::len) word) div n < x"
  apply (case_tac "n = 0")
   apply clarsimp
   apply (subst div_by_0_word)
   apply (simp add:word_neq_0_conv)
  apply (subst word_arith_nat_div)
  apply (rule word_of_nat_less)
  apply (rule div_less_dividend)
   apply (metis (poly_guards_query) One_nat_def less_one nat_neq_iff unat_eq_1(2) unat_eq_zero)
  apply (simp add:unat_gt_0)
  done

lemma shiftr1_lt:"x \<noteq> 0 \<Longrightarrow> (x::('a::len) word) >> 1 < x"
  apply (subst shiftr1_is_div_2)
  apply (rule div_less_dividend_word)
   apply simp+
  done

lemma word_less_div:
  fixes x :: "('a::len) word"
    and y :: "('a::len) word"
  shows "x div y = 0 \<Longrightarrow> y = 0 \<or> x < y"
  apply (case_tac "y = 0", clarsimp+)
  by (metis One_nat_def Suc_le_mono le0 le_div_geq not_less unat_0 unat_div unat_gt_0 word_less_nat_alt zero_less_one)

lemma not_degenerate_imp_2_neq_0:"len_of TYPE('a) > 1 \<Longrightarrow> (2::('a::len) word) \<noteq> 0"
  by (metis numerals(1) power_not_zero power_zero_numeral)

lemma shiftr1_0_or_1:"(x::('a::len) word) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x = 1"
  apply (subst (asm) shiftr1_is_div_2)
  apply (drule word_less_div)
  apply (case_tac "len_of TYPE('a) = 1")
   apply (simp add:degenerate_word)
  apply (erule disjE)
   apply (subgoal_tac "(2::'a word) \<noteq> 0")
    apply simp
   apply (rule not_degenerate_imp_2_neq_0)
   apply (subgoal_tac "len_of TYPE('a) \<noteq> 0")
    apply arith
   apply simp
  apply (rule x_less_2_0_1', simp+)
  done

lemma word_overflow:"(x::('a::len) word) + 1 > x \<or> x + 1 = 0"
  apply clarsimp
  by (metis diff_0 eq_diff_eq less_x_plus_1 max_word_max plus_1_less)

lemma word_overflow_unat:"unat ((x::('a::len) word) + 1) = unat x + 1 \<or> x + 1 = 0"
  by (metis Suc_eq_plus1 add.commute unatSuc)

lemma even_word_imp_odd_next:"even (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> odd (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma odd_word_imp_even_next:"odd (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> even (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma overflow_imp_lsb:"(x::('a::len) word) + 1 = 0 \<Longrightarrow> x !! 0"
  by (metis add.commute add_left_cancel max_word_max not_less word_and_1 word_bool_alg.conj_one_right word_bw_comms(1) word_overflow zero_neq_one)

lemma word_lsb_nat:"lsb w = (unat w mod 2 = 1)"
  unfolding word_lsb_def bin_last_def
  by (metis (no_types, hide_lams) nat_mod_distrib nat_numeral not_mod_2_eq_1_eq_0 numeral_One uint_eq_0 uint_nonnegative unat_0 unat_def zero_le_numeral)

lemma odd_iff_lsb:"odd (unat (x::('a::len) word)) = x !! 0"
  apply (simp add:even_iff_mod_2_eq_zero)
  apply (subst word_lsb_nat[unfolded One_nat_def, symmetric])
  apply (rule word_lsb_alt)
  done

lemma of_nat_neq_iff_word:
      "x mod 2 ^ len_of TYPE('a) \<noteq> y mod 2 ^ len_of TYPE('a) \<Longrightarrow>
         (((of_nat x)::('a::len) word) \<noteq> of_nat y) = (x \<noteq> y)"
  apply (rule iffI)
   apply (case_tac "x = y")
   apply (subst (asm) of_nat_eq_iff[symmetric])
   apply simp+
  apply (case_tac "((of_nat x)::('a::len) word) = of_nat y")
   apply (subst (asm) word_unat.norm_eq_iff[symmetric])
   apply simp+
  done

lemma shiftr1_irrelevant_lsb:"(x::('a::len) word) !! 0 \<or> x >> 1 = (x + 1) >> 1"
  apply (case_tac "len_of TYPE('a) = 1")
   apply clarsimp
   apply (drule_tac x=x in degenerate_word[unfolded One_nat_def])
   apply (erule disjE)
    apply clarsimp+
  apply (subst (asm) shiftr1_is_div_2[unfolded One_nat_def])+
  apply (subst (asm) word_arith_nat_div)+
  apply clarsimp
  apply (subst (asm) bintrunc_id)
    apply (subgoal_tac "len_of TYPE('a) > 0")
     apply linarith
    apply clarsimp+
  apply (subst (asm) bintrunc_id)
    apply (subgoal_tac "len_of TYPE('a) > 0")
     apply linarith
    apply clarsimp+
  apply (case_tac "x + 1 = 0")
   apply (clarsimp simp:overflow_imp_lsb)
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  apply (case_tac "even (unat x)")
   apply (subgoal_tac "unat x div 2 = Suc (unat x) div 2")
    apply metis
   apply (subst numeral_2_eq_2)+
   apply simp
  apply (simp add:odd_iff_lsb)
  done

lemma shiftr1_0_imp_only_lsb:"((x::('a::len) word) + 1) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x + 1 = 0"
  by (metis One_nat_def shiftr1_0_or_1 word_less_1 word_overflow)

lemma shiftr1_irrelevant_lsb':"\<not>((x::('a::len) word) !! 0) \<Longrightarrow> x >> 1 = (x + 1) >> 1"
  by (metis shiftr1_irrelevant_lsb)

lemma lsb_this_or_next:"\<not>(((x::('a::len) word) + 1) !! 0) \<Longrightarrow> x !! 0"
  by (metis (poly_guards_query) even_word_imp_odd_next odd_iff_lsb overflow_imp_lsb)

(* Bit population count. Equivalent of __builtin_popcount.
 * FIXME: MOVE
 *)
definition
  pop_count :: "('a::len) word \<Rightarrow> nat"
where
  "pop_count w \<equiv> length (filter id (to_bl w))"

lemma pop_count_0[simp]:"pop_count 0 = 0"
  by (clarsimp simp:pop_count_def)

lemma pop_count_1[simp]:"pop_count 1 = 1"
  by (clarsimp simp:pop_count_def to_bl_1)

lemma pop_count_0_imp_0:"(pop_count w = 0) = (w = 0)"
  apply (rule iffI)
   apply (clarsimp simp:pop_count_def)
   apply (subst (asm) filter_empty_conv)
   apply (clarsimp simp:eq_zero_set_bl)
   apply fast
  apply simp
  done

(* Perhaps this one should be a simp lemma, but it seems a little dangerous. *)
lemma cast_chunk_assemble_id:
  "\<lbrakk>n = len_of TYPE('a::len); m = len_of TYPE('b::len); n * 2 = m\<rbrakk> \<Longrightarrow>
  (((ucast ((ucast (x::'b word))::'a word))::'b word) || (((ucast ((ucast (x >> n))::'a word))::'b word) << n)) = x"
  apply (subgoal_tac "((ucast ((ucast (x >> n))::'a word))::'b word) = x >> n")
   apply clarsimp
   apply (subst and_not_mask[symmetric])
   apply (subst ucast_ucast_mask)
   apply (subst word_ao_dist2[symmetric])
   apply clarsimp
  apply (rule ucast_ucast_len)
  apply (rule shiftr_less_t2n')
   apply (subst and_mask_eq_iff_le_mask)
   apply (clarsimp simp:mask_def)
   apply (metis max_word_eq max_word_max mult_2_right)
  apply (metis add_diff_cancel_left' diff_less len_gt_0 mult_2_right)
  done

(* Helper for packing then unpacking a 64-bit variable. *)
lemma cast_chunk_assemble_id_64[simp]:
  "(((ucast ((ucast (x::64 word))::32 word))::64 word) || (((ucast ((ucast (x >> 32))::32 word))::64 word) << 32)) = x"
  by (simp add:cast_chunk_assemble_id)

lemma cast_chunk_scast_assemble_id:
  "\<lbrakk>n = len_of TYPE('a::len); m = len_of TYPE('b::len); n * 2 = m\<rbrakk> \<Longrightarrow>
  (((ucast ((scast (x::'b word))::'a word))::'b word) || (((ucast ((scast (x >> n))::'a word))::'b word) << n)) = x"
  apply (subgoal_tac "((scast x)::'a word) = ((ucast x)::'a word)")
   apply (subgoal_tac "((scast (x >> n))::'a word) = ((ucast (x >> n))::'a word)")
    apply (simp add:cast_chunk_assemble_id)
   apply (subst down_cast_same[symmetric], subst is_down, arith, simp)+
  done

(* Another variant of packing and unpacking a 64-bit variable. *)
lemma cast_chunk_assemble_id_64'[simp]:
  "(((ucast ((scast (x::64 word))::32 word))::64 word) || (((ucast ((scast (x >> 32))::32 word))::64 word) << 32)) = x"
  by (simp add:cast_chunk_scast_assemble_id)

(* Specialiasations of down_cast_same for adding to local simpsets. *)
lemma cast_down_u64: "(scast::64 word \<Rightarrow> 32 word) = (ucast::64 word \<Rightarrow> 32 word)"
  apply (subst down_cast_same[symmetric])
   apply (simp add:is_down)+
  done
lemma cast_down_s64: "(scast::64 sword \<Rightarrow> 32 word) = (ucast::64 sword \<Rightarrow> 32 word)"
  apply (subst down_cast_same[symmetric])
   apply (simp add:is_down)+
  done

lemma mask_or_not_mask:"x && mask n || x && ~~ mask n = x"
  apply (subst word_oa_dist)
  apply simp
  apply (subst word_oa_dist2)
  apply simp
  done

lemma is_aligned_add_not_aligned:
    "\<lbrakk>is_aligned (p::word32) n; \<not> is_aligned (q::word32) n\<rbrakk> \<Longrightarrow>
          \<not> is_aligned (p + q) n"
  by (metis is_aligned_addD1)

lemma dvd_not_suc:"\<lbrakk> 2 ^ n dvd (p::nat); n > 0; i > 0; i < 2 ^ n; p + i > p; n < 32\<rbrakk> \<Longrightarrow>
          \<not> (2 ^ n dvd (p + i))"
  by (metis dvd_def dvd_reduce_multiple nat_dvd_not_less)

lemma word32_gr0_conv_Suc:"(m::word32) > 0 \<Longrightarrow> \<exists>n. m = n + 1"
  by (metis add.commute add_minus_cancel)

lemma offset_not_aligned:
  "\<lbrakk> is_aligned (p::word32) n; i > 0; i < 2 ^ n; n < 32\<rbrakk>
     \<Longrightarrow> \<not> is_aligned (p + of_nat i) n"
  apply (erule is_aligned_add_not_aligned)
  unfolding is_aligned_def apply clarsimp
  apply (subst (asm) unat_of_nat_len)
   apply (metis len32 unat_less_word_bits unat_power_lower32 word_bits_conv)
  apply (metis nat_dvd_not_less)
  done

lemma neg_mask_add_aligned:
  "\<lbrakk> is_aligned p n; q < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p + q) && ~~ mask n = p && ~~ mask n"
  by (metis is_aligned_add_helper is_aligned_neg_mask_eq)

lemma word_sless_sint_le:"x <s y \<Longrightarrow> sint x \<le> sint y - 1"
  by (metis word_sless_alt zle_diff1_eq)

lemma word_ge_min:"sint (x::32 word) \<ge> -2147483648"
  by (metis sint_ge word32_bounds(1) word_size)

lemma set_enum_word8_def:
  "((set enum)::word8 set) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                              20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
                              37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
                              54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
                              71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
                              88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103,
                              104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
                              118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
                              132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                              146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
                              160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                              174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
                              188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
                              202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215,
                              216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
                              230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243,
                              244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255}"
  by (eval)

lemma word8_exhaust:
  fixes x :: word8
  shows "\<lbrakk>x \<noteq> 0; x \<noteq> 1; x \<noteq> 2; x \<noteq> 3; x \<noteq> 4; x \<noteq> 5; x \<noteq> 6; x \<noteq> 7; x \<noteq> 8; x \<noteq> 9; x \<noteq> 10; x \<noteq> 11; x \<noteq>
          12; x \<noteq> 13; x \<noteq> 14; x \<noteq> 15; x \<noteq> 16; x \<noteq> 17; x \<noteq> 18; x \<noteq> 19; x \<noteq> 20; x \<noteq> 21; x \<noteq> 22; x \<noteq>
          23; x \<noteq> 24; x \<noteq> 25; x \<noteq> 26; x \<noteq> 27; x \<noteq> 28; x \<noteq> 29; x \<noteq> 30; x \<noteq> 31; x \<noteq> 32; x \<noteq> 33; x \<noteq>
          34; x \<noteq> 35; x \<noteq> 36; x \<noteq> 37; x \<noteq> 38; x \<noteq> 39; x \<noteq> 40; x \<noteq> 41; x \<noteq> 42; x \<noteq> 43; x \<noteq> 44; x \<noteq>
          45; x \<noteq> 46; x \<noteq> 47; x \<noteq> 48; x \<noteq> 49; x \<noteq> 50; x \<noteq> 51; x \<noteq> 52; x \<noteq> 53; x \<noteq> 54; x \<noteq> 55; x \<noteq>
          56; x \<noteq> 57; x \<noteq> 58; x \<noteq> 59; x \<noteq> 60; x \<noteq> 61; x \<noteq> 62; x \<noteq> 63; x \<noteq> 64; x \<noteq> 65; x \<noteq> 66; x \<noteq>
          67; x \<noteq> 68; x \<noteq> 69; x \<noteq> 70; x \<noteq> 71; x \<noteq> 72; x \<noteq> 73; x \<noteq> 74; x \<noteq> 75; x \<noteq> 76; x \<noteq> 77; x \<noteq>
          78; x \<noteq> 79; x \<noteq> 80; x \<noteq> 81; x \<noteq> 82; x \<noteq> 83; x \<noteq> 84; x \<noteq> 85; x \<noteq> 86; x \<noteq> 87; x \<noteq> 88; x \<noteq>
          89; x \<noteq> 90; x \<noteq> 91; x \<noteq> 92; x \<noteq> 93; x \<noteq> 94; x \<noteq> 95; x \<noteq> 96; x \<noteq> 97; x \<noteq> 98; x \<noteq> 99; x \<noteq>
          100; x \<noteq> 101; x \<noteq> 102; x \<noteq> 103; x \<noteq> 104; x \<noteq> 105; x \<noteq> 106; x \<noteq> 107; x \<noteq> 108; x \<noteq> 109; x \<noteq>
          110; x \<noteq> 111; x \<noteq> 112; x \<noteq> 113; x \<noteq> 114; x \<noteq> 115; x \<noteq> 116; x \<noteq> 117; x \<noteq> 118; x \<noteq> 119; x \<noteq>
          120; x \<noteq> 121; x \<noteq> 122; x \<noteq> 123; x \<noteq> 124; x \<noteq> 125; x \<noteq> 126; x \<noteq> 127; x \<noteq> 128; x \<noteq> 129; x \<noteq>
          130; x \<noteq> 131; x \<noteq> 132; x \<noteq> 133; x \<noteq> 134; x \<noteq> 135; x \<noteq> 136; x \<noteq> 137; x \<noteq> 138; x \<noteq> 139; x \<noteq>
          140; x \<noteq> 141; x \<noteq> 142; x \<noteq> 143; x \<noteq> 144; x \<noteq> 145; x \<noteq> 146; x \<noteq> 147; x \<noteq> 148; x \<noteq> 149; x \<noteq>
          150; x \<noteq> 151; x \<noteq> 152; x \<noteq> 153; x \<noteq> 154; x \<noteq> 155; x \<noteq> 156; x \<noteq> 157; x \<noteq> 158; x \<noteq> 159; x \<noteq>
          160; x \<noteq> 161; x \<noteq> 162; x \<noteq> 163; x \<noteq> 164; x \<noteq> 165; x \<noteq> 166; x \<noteq> 167; x \<noteq> 168; x \<noteq> 169; x \<noteq>
          170; x \<noteq> 171; x \<noteq> 172; x \<noteq> 173; x \<noteq> 174; x \<noteq> 175; x \<noteq> 176; x \<noteq> 177; x \<noteq> 178; x \<noteq> 179; x \<noteq>
          180; x \<noteq> 181; x \<noteq> 182; x \<noteq> 183; x \<noteq> 184; x \<noteq> 185; x \<noteq> 186; x \<noteq> 187; x \<noteq> 188; x \<noteq> 189; x \<noteq>
          190; x \<noteq> 191; x \<noteq> 192; x \<noteq> 193; x \<noteq> 194; x \<noteq> 195; x \<noteq> 196; x \<noteq> 197; x \<noteq> 198; x \<noteq> 199; x \<noteq>
          200; x \<noteq> 201; x \<noteq> 202; x \<noteq> 203; x \<noteq> 204; x \<noteq> 205; x \<noteq> 206; x \<noteq> 207; x \<noteq> 208; x \<noteq> 209; x \<noteq>
          210; x \<noteq> 211; x \<noteq> 212; x \<noteq> 213; x \<noteq> 214; x \<noteq> 215; x \<noteq> 216; x \<noteq> 217; x \<noteq> 218; x \<noteq> 219; x \<noteq>
          220; x \<noteq> 221; x \<noteq> 222; x \<noteq> 223; x \<noteq> 224; x \<noteq> 225; x \<noteq> 226; x \<noteq> 227; x \<noteq> 228; x \<noteq> 229; x \<noteq>
          230; x \<noteq> 231; x \<noteq> 232; x \<noteq> 233; x \<noteq> 234; x \<noteq> 235; x \<noteq> 236; x \<noteq> 237; x \<noteq> 238; x \<noteq> 239; x \<noteq>
          240; x \<noteq> 241; x \<noteq> 242; x \<noteq> 243; x \<noteq> 244; x \<noteq> 245; x \<noteq> 246; x \<noteq> 247; x \<noteq> 248; x \<noteq> 249; x \<noteq>
          250; x \<noteq> 251; x \<noteq> 252; x \<noteq> 253; x \<noteq> 254; x \<noteq> 255\<rbrakk> \<Longrightarrow> P"
  by (subgoal_tac "x \<in> set enum",
       subst (asm) set_enum_word8_def,
       simp,
      simp)

lemma upper_trivial:
  fixes x :: "'a::len word"
  shows "x \<noteq> 2 ^ len_of TYPE('a) - 1 \<Longrightarrow> x < 2 ^ len_of TYPE('a) - 1"
  by (cut_tac n=x and 'a='a in max_word_max,
      clarsimp simp:max_word_def,
      simp add: less_le)

lemma constraint_expand:
  fixes x :: "'a::len word"
  shows "x \<in> {y. lower \<le> y \<and> y \<le> upper} = (lower \<le> x \<and> x \<le> upper)"
  by simp

lemma card_map_elide:
  "n \<le> CARD(32 word) \<Longrightarrow> card ((of_nat::nat \<Rightarrow> 32 word) ` {0..<n}) = card {0..<n}"
  apply clarsimp
  apply (induct n)
   apply clarsimp+
  apply (subgoal_tac "{0..<Suc n} = {0..<n} \<union> {n}")
   prefer 2
   apply clarsimp
   apply fastforce
  apply clarsimp
  apply (subst card_insert_disjoint)
    apply clarsimp
   apply (subst atLeast0LessThan)
   apply (subgoal_tac "(of_nat::nat \<Rightarrow> 32 word) ` {..<n} = {..<of_nat n}")
    prefer 2
    apply (rule equalityI)
     apply clarsimp
     apply (subst (asm) card_word)
     apply clarsimp
     apply (rule of_nat_mono_maybe)
      apply clarsimp+
      apply (subgoal_tac "x \<in> of_nat ` {..<n} = (\<exists>y\<in>{..<n}. of_nat y = x)")
       prefer 2
       apply blast
      apply simp
      apply (rule bexI) (* sorry for schematics *)
       apply (rule word_unat.Rep_inverse')
       apply force
      apply clarsimp 
      apply (subst (asm) card_word)
      apply clarsimp
      apply (metis (erased, hide_lams) Divides.mod_less_eq_dividend order_less_le_trans unat_of_nat word_less_nat_alt)
     by clarsimp+

lemma card_map_elide2: "n \<le> CARD(32 word) \<Longrightarrow> card ((of_nat::nat \<Rightarrow> 32 word) ` {0..<n}) = n"
  apply (subst card_map_elide)
   by clarsimp+

lemma le_max_word_ucast_id:
  "(x::'a::len word) \<le> ucast (max_word::'b::len word) \<Longrightarrow> ucast ((ucast x)::'b word) = x"
  apply (unfold ucast_def)
  apply (subst word_ubin.eq_norm)
  apply (subst and_mask_bintr[symmetric])
  apply (subst and_mask_eq_iff_le_mask)
  apply (clarsimp simp:max_word_def mask_def)
  proof -
    assume a1: "x \<le> word_of_int (uint (word_of_int (2 ^ len_of (TYPE('b)\<Colon>'b itself) - 1)\<Colon>'b word))"
    have f2: "((\<exists>i ia. (0\<Colon>int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or> \<not> (0\<Colon>int) \<le> - 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself) \<or> (0\<Colon>int) \<le> - 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself) + - 1 * 2 ^ len_of (TYPE('b)\<Colon>'b itself) \<or> (- (1\<Colon>int) + 2 ^ len_of (TYPE('b)\<Colon>'b itself)) mod 2 ^ len_of (TYPE('b)\<Colon>'b itself) = - 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself)) = ((\<exists>i ia. (0\<Colon>int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or> \<not> (1\<Colon>int) \<le> 2 ^ len_of (TYPE('b)\<Colon>'b itself) \<or> 2 ^ len_of (TYPE('b)\<Colon>'b itself) + - (1\<Colon>int) * ((- 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself)) mod 2 ^ len_of (TYPE('b)\<Colon>'b itself)) = 1)"
      by force
    have f3: "\<forall>i ia. \<not> (0\<Colon>int) \<le> i \<or> 0 \<le> i + - 1 * ia \<or> i mod ia = i"
      using mod_pos_pos_trivial by force
    have "(1\<Colon>int) \<le> 2 ^ len_of (TYPE('b)\<Colon>'b itself)"
      by simp
    hence "2 ^ len_of (TYPE('b)\<Colon>'b itself) + - (1\<Colon>int) * ((- 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself)) mod 2 ^ len_of (TYPE('b)\<Colon>'b itself)) = 1"
      using f3 f2 by blast
    hence f4: "- (1\<Colon>int) + 2 ^ len_of (TYPE('b)\<Colon>'b itself) = (- 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself)) mod 2 ^ len_of (TYPE('b)\<Colon>'b itself)"
      by linarith
    have f5: "x \<le> word_of_int (uint (word_of_int (- 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself))\<Colon>'b word))"
      using a1 by force
    have f6: "2 ^ len_of (TYPE('b)\<Colon>'b itself) + - (1\<Colon>int) = - 1 + 2 ^ len_of (TYPE('b)\<Colon>'b itself)"
      by force
    have f7: "- (1\<Colon>int) * 1 = - 1"
      by auto
    have "\<forall>x0 x1. (x1\<Colon>int) - x0 = x1 + - 1 * x0"
      by force
    thus "x \<le> 2 ^ len_of (TYPE('b)\<Colon>'b itself) - 1"
      using f7 f6 f5 f4 by (metis uint_word_of_int wi_homs(2) word_arith_wis(8) word_of_int_2p)
  qed

(*enumerations of words*)
lemma remdups_enum_upto: fixes s::"'a::len word" shows "remdups [s .e. e] = [s .e. e]" by(simp)

lemma card_enum_upto: fixes s::"'a::len word" shows "card (set [s .e. e]) = Suc (unat e) - unat s"
  apply(subst List.card_set)
  apply(simp add: remdups_enum_upto)
  done

end
