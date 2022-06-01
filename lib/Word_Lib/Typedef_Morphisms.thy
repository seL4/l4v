(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
  Author: Jeremy Dawson and Gerwin Klein, NICTA

  Consequences of type definition theorems, and of extended type definition.
*)

section \<open>Type Definition Theorems\<close>

theory Typedef_Morphisms
  imports Main "HOL-Library.Word" Bit_Comprehension Bits_Int
begin

subsection "More lemmas about normal type definitions"

lemma tdD1: "type_definition Rep Abs A \<Longrightarrow> \<forall>x. Rep x \<in> A"
  and tdD2: "type_definition Rep Abs A \<Longrightarrow> \<forall>x. Abs (Rep x) = x"
  and tdD3: "type_definition Rep Abs A \<Longrightarrow> \<forall>y. y \<in> A \<longrightarrow> Rep (Abs y) = y"
  by (auto simp: type_definition_def)

lemma td_nat_int: "type_definition int nat (Collect ((\<le>) 0))"
  unfolding type_definition_def by auto

context type_definition
begin

declare Rep [iff] Rep_inverse [simp] Rep_inject [simp]

lemma Abs_eqD: "Abs x = Abs y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y"
  by (simp add: Abs_inject)

lemma Abs_inverse': "r \<in> A \<Longrightarrow> Abs r = a \<Longrightarrow> Rep a = r"
  by (safe elim!: Abs_inverse)

lemma Rep_comp_inverse: "Rep \<circ> f = g \<Longrightarrow> Abs \<circ> g = f"
  using Rep_inverse by auto

lemma Rep_eqD [elim!]: "Rep x = Rep y \<Longrightarrow> x = y"
  by simp

lemma Rep_inverse': "Rep a = r \<Longrightarrow> Abs r = a"
  by (safe intro!: Rep_inverse)

lemma comp_Abs_inverse: "f \<circ> Abs = g \<Longrightarrow> g \<circ> Rep = f"
  using Rep_inverse by auto

lemma set_Rep: "A = range Rep"
proof (rule set_eqI)
  show "x \<in> A \<longleftrightarrow> x \<in> range Rep" for x
    by (auto dest: Abs_inverse [of x, symmetric])
qed

lemma set_Rep_Abs: "A = range (Rep \<circ> Abs)"
proof (rule set_eqI)
  show "x \<in> A \<longleftrightarrow> x \<in> range (Rep \<circ> Abs)" for x
    by (auto dest: Abs_inverse [of x, symmetric])
qed

lemma Abs_inj_on: "inj_on Abs A"
  unfolding inj_on_def
  by (auto dest: Abs_inject [THEN iffD1])

lemma image: "Abs ` A = UNIV"
  by (fact Abs_image)

lemmas td_thm = type_definition_axioms

lemma fns1: "Rep \<circ> fa = fr \<circ> Rep \<or> fa \<circ> Abs = Abs \<circ> fr \<Longrightarrow> Abs \<circ> fr \<circ> Rep = fa"
  by (auto dest: Rep_comp_inverse elim: comp_Abs_inverse simp: o_assoc)

lemmas fns1a = disjI1 [THEN fns1]
lemmas fns1b = disjI2 [THEN fns1]

lemma fns4: "Rep \<circ> fa \<circ> Abs = fr \<Longrightarrow> Rep \<circ> fa = fr \<circ> Rep \<and> fa \<circ> Abs = Abs \<circ> fr"
  by auto

end

interpretation nat_int: type_definition int nat "Collect ((\<le>) 0)"
  by (rule td_nat_int)

declare
  nat_int.Rep_cases [cases del]
  nat_int.Abs_cases [cases del]
  nat_int.Rep_induct [induct del]
  nat_int.Abs_induct [induct del]


subsection "Extended form of type definition predicate"

lemma td_conds:
  "norm \<circ> norm = norm \<Longrightarrow>
    fr \<circ> norm = norm \<circ> fr \<longleftrightarrow> norm \<circ> fr \<circ> norm = fr \<circ> norm \<and> norm \<circ> fr \<circ> norm = norm \<circ> fr"
  apply safe
    apply (simp_all add: comp_assoc)
   apply (simp_all add: o_assoc)
  done

lemma fn_comm_power: "fa \<circ> tr = tr \<circ> fr \<Longrightarrow> fa ^^ n \<circ> tr = tr \<circ> fr ^^ n"
  apply (rule ext)
  apply (induct n)
   apply (auto dest: fun_cong)
  done

lemmas fn_comm_power' =
  ext [THEN fn_comm_power, THEN fun_cong, unfolded o_def]


locale td_ext = type_definition +
  fixes norm
  assumes eq_norm: "\<And>x. Rep (Abs x) = norm x"
begin

lemma Abs_norm [simp]: "Abs (norm x) = Abs x"
  using eq_norm [of x] by (auto elim: Rep_inverse')

lemma td_th: "g \<circ> Abs = f \<Longrightarrow> f (Rep x) = g x"
  by (drule comp_Abs_inverse [symmetric]) simp

lemma eq_norm': "Rep \<circ> Abs = norm"
  by (auto simp: eq_norm)

lemma norm_Rep [simp]: "norm (Rep x) = Rep x"
  by (auto simp: eq_norm' intro: td_th)

lemmas td = td_thm

lemma set_iff_norm: "w \<in> A \<longleftrightarrow> w = norm w"
  by (auto simp: set_Rep_Abs eq_norm' eq_norm [symmetric])

lemma inverse_norm: "Abs n = w \<longleftrightarrow> Rep w = norm n"
  apply (rule iffI)
   apply (clarsimp simp add: eq_norm)
  apply (simp add: eq_norm' [symmetric])
  done

lemma norm_eq_iff: "norm x = norm y \<longleftrightarrow> Abs x = Abs y"
  by (simp add: eq_norm' [symmetric])

lemma norm_comps:
  "Abs \<circ> norm = Abs"
  "norm \<circ> Rep = Rep"
  "norm \<circ> norm = norm"
  by (auto simp: eq_norm' [symmetric] o_def)

lemmas norm_norm [simp] = norm_comps

lemma fns5: "Rep \<circ> fa \<circ> Abs = fr \<Longrightarrow> fr \<circ> norm = fr \<and> norm \<circ> fr = fr"
  by (fold eq_norm') auto

text \<open>
  following give conditions for converses to \<open>td_fns1\<close>
  \<^item> the condition \<open>norm \<circ> fr \<circ> norm = fr \<circ> norm\<close> says that
    \<open>fr\<close> takes normalised arguments to normalised results
  \<^item> \<open>norm \<circ> fr \<circ> norm = norm \<circ> fr\<close> says that \<open>fr\<close>
    takes norm-equivalent arguments to norm-equivalent results
  \<^item> \<open>fr \<circ> norm = fr\<close> says that \<open>fr\<close>
    takes norm-equivalent arguments to the same result
  \<^item> \<open>norm \<circ> fr = fr\<close> says that \<open>fr\<close> takes any argument to a normalised result
\<close>
lemma fns2: "Abs \<circ> fr \<circ> Rep = fa \<Longrightarrow> norm \<circ> fr \<circ> norm = fr \<circ> norm \<longleftrightarrow> Rep \<circ> fa = fr \<circ> Rep"
  apply (fold eq_norm')
  apply safe
   prefer 2
   apply (simp add: o_assoc)
  apply (rule ext)
  apply (drule_tac x="Rep x" in fun_cong)
  apply auto
  done

lemma fns3: "Abs \<circ> fr \<circ> Rep = fa \<Longrightarrow> norm \<circ> fr \<circ> norm = norm \<circ> fr \<longleftrightarrow> fa \<circ> Abs = Abs \<circ> fr"
  apply (fold eq_norm')
  apply safe
   prefer 2
   apply (simp add: comp_assoc)
  apply (rule ext)
  apply (drule_tac f="a \<circ> b" for a b in fun_cong)
  apply simp
  done

lemma fns: "fr \<circ> norm = norm \<circ> fr \<Longrightarrow> fa \<circ> Abs = Abs \<circ> fr \<longleftrightarrow> Rep \<circ> fa = fr \<circ> Rep"
  apply safe
   apply (frule fns1b)
   prefer 2
   apply (frule fns1a)
   apply (rule fns3 [THEN iffD1])
     prefer 3
     apply (rule fns2 [THEN iffD1])
       apply (simp_all add: comp_assoc)
   apply (simp_all add: o_assoc)
  done

lemma range_norm: "range (Rep \<circ> Abs) = A"
  by (simp add: set_Rep_Abs)

end

lemmas td_ext_def' =
  td_ext_def [unfolded type_definition_def td_ext_axioms_def]


subsection \<open>Type-definition locale instantiations\<close>

definition uints :: "nat \<Rightarrow> int set"
  \<comment> \<open>the sets of integers representing the words\<close>
  where "uints n = range (take_bit n)"

definition sints :: "nat \<Rightarrow> int set"
  where "sints n = range (signed_take_bit (n - 1))"

lemma uints_num: "uints n = {i. 0 \<le> i \<and> i < 2 ^ n}"
  by (simp add: uints_def range_bintrunc)

lemma sints_num: "sints n = {i. - (2 ^ (n - 1)) \<le> i \<and> i < 2 ^ (n - 1)}"
  by (simp add: sints_def range_sbintrunc)

definition unats :: "nat \<Rightarrow> nat set"
  where "unats n = {i. i < 2 ^ n}"

\<comment> \<open>naturals\<close>
lemma uints_unats: "uints n = int ` unats n"
  apply (unfold unats_def uints_num)
  apply safe
    apply (rule_tac image_eqI)
     apply (erule_tac nat_0_le [symmetric])
  by auto

lemma unats_uints: "unats n = nat ` uints n"
  by (auto simp: uints_unats image_iff)

lemma td_ext_uint:
  "td_ext (uint :: 'a word \<Rightarrow> int) word_of_int (uints (LENGTH('a::len)))
    (\<lambda>w::int. w mod 2 ^ LENGTH('a))"
  apply (unfold td_ext_def')
  apply transfer
  apply (simp add: uints_num take_bit_eq_mod)
  done

interpretation word_uint:
  td_ext
    "uint::'a::len word \<Rightarrow> int"
    word_of_int
    "uints (LENGTH('a::len))"
    "\<lambda>w. w mod 2 ^ LENGTH('a::len)"
  by (fact td_ext_uint)

lemmas td_uint = word_uint.td_thm
lemmas int_word_uint = word_uint.eq_norm

lemma td_ext_ubin:
  "td_ext (uint :: 'a word \<Rightarrow> int) word_of_int (uints (LENGTH('a::len)))
    (take_bit (LENGTH('a)))"
  apply standard
  apply transfer
  apply simp
  done

interpretation word_ubin:
  td_ext
    "uint::'a::len word \<Rightarrow> int"
    word_of_int
    "uints (LENGTH('a::len))"
    "take_bit (LENGTH('a::len))"
  by (fact td_ext_ubin)

lemma td_ext_unat [OF refl]:
  "n = LENGTH('a::len) \<Longrightarrow>
    td_ext (unat :: 'a word \<Rightarrow> nat) of_nat (unats n) (\<lambda>i. i mod 2 ^ n)"
  apply (standard; transfer)
     apply (simp_all add: unats_def take_bit_of_nat take_bit_nat_eq_self_iff
      flip: take_bit_eq_mod)
  done

lemmas unat_of_nat = td_ext_unat [THEN td_ext.eq_norm]

interpretation word_unat:
  td_ext
    "unat::'a::len word \<Rightarrow> nat"
    of_nat
    "unats (LENGTH('a::len))"
    "\<lambda>i. i mod 2 ^ LENGTH('a::len)"
  by (rule td_ext_unat)

lemmas td_unat = word_unat.td_thm

lemma unat_le: "y \<le> unat z \<Longrightarrow> y \<in> unats (LENGTH('a))"
  for z :: "'a::len word"
  apply (unfold unats_def)
  apply clarsimp
  apply (metis le_unat_uoi unsigned_less)
  done

lemma td_ext_sbin:
  "td_ext (sint :: 'a word \<Rightarrow> int) word_of_int (sints (LENGTH('a::len)))
    (signed_take_bit (LENGTH('a) - 1))"
  by (standard; transfer) (auto simp add: sints_def)

lemma td_ext_sint:
  "td_ext (sint :: 'a word \<Rightarrow> int) word_of_int (sints (LENGTH('a::len)))
     (\<lambda>w. (w + 2 ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('a) -
         2 ^ (LENGTH('a) - 1))"
  using td_ext_sbin [where ?'a = 'a] by (simp add: no_sbintr_alt2)

text \<open>
  We do \<open>sint\<close> before \<open>sbin\<close>, before \<open>sint\<close> is the user version
  and interpretations do not produce thm duplicates. I.e.
  we get the name \<open>word_sint.Rep_eqD\<close>, but not \<open>word_sbin.Req_eqD\<close>,
  because the latter is the same thm as the former.
\<close>
interpretation word_sint:
  td_ext
    "sint ::'a::len word \<Rightarrow> int"
    word_of_int
    "sints (LENGTH('a::len))"
    "\<lambda>w. (w + 2^(LENGTH('a::len) - 1)) mod 2^LENGTH('a::len) -
      2 ^ (LENGTH('a::len) - 1)"
  by (rule td_ext_sint)

interpretation word_sbin:
  td_ext
    "sint ::'a::len word \<Rightarrow> int"
    word_of_int
    "sints (LENGTH('a::len))"
    "signed_take_bit (LENGTH('a::len) - 1)"
  by (rule td_ext_sbin)

lemmas int_word_sint = td_ext_sint [THEN td_ext.eq_norm]

lemmas td_sint = word_sint.td

lemma uints_mod: "uints n = range (\<lambda>w. w mod 2 ^ n)"
  by (fact uints_def [unfolded no_bintr_alt1])

lemmas bintr_num =
  word_ubin.norm_eq_iff [of "numeral a" "numeral b", symmetric, folded word_numeral_alt] for a b
lemmas sbintr_num =
  word_sbin.norm_eq_iff [of "numeral a" "numeral b", symmetric, folded word_numeral_alt] for a b

lemmas uint_div_alt = word_div_def [THEN trans [OF uint_cong int_word_uint]]
lemmas uint_mod_alt = word_mod_def [THEN trans [OF uint_cong int_word_uint]]

interpretation test_bit:
  td_ext
    "bit :: 'a::len word \<Rightarrow> nat \<Rightarrow> bool"
    set_bits
    "{f. \<forall>i. f i \<longrightarrow> i < LENGTH('a::len)}"
    "(\<lambda>h i. h i \<and> i < LENGTH('a::len))"
  by standard (auto simp add: bit_imp_le_length bit_set_bits_word_iff set_bits_bit_eq)

lemmas td_nth = test_bit.td_thm

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

lemma uints_mono_iff: "uints l \<subseteq> uints m \<longleftrightarrow> l \<le> m"
  using power_increasing_iff[of "2::int" l m]
  apply (auto simp: uints_num subset_iff simp del: power_increasing_iff)
  apply (meson less_irrefl not_le zero_le_numeral zero_le_power)
  done

lemmas uints_monoI = uints_mono_iff[THEN iffD2]

lemma Bit_in_uints_Suc: "of_bool c + 2 * w \<in> uints (Suc m)" if "w \<in> uints m"
  using that
  by (auto simp: uints_num)

lemma Bit_in_uintsI: "of_bool c + 2 * w \<in> uints m" if "w \<in> uints (m - 1)" "m > 0"
  using Bit_in_uints_Suc[OF that(1)] that(2)
  by auto

lemma bin_cat_in_uintsI:
  \<open>concat_bit n b a \<in> uints m\<close> if \<open>a \<in> uints l\<close> \<open>m \<ge> l + n\<close>
proof -
  from \<open>m \<ge> l + n\<close> obtain q where \<open>m = l + n + q\<close>
    using le_Suc_ex by blast
  then have \<open>(2::int) ^ m = 2 ^ n * 2 ^ (l + q)\<close>
    by (simp add: ac_simps power_add)
  moreover have \<open>a mod 2 ^ (l + q) = a\<close>
    using \<open>a \<in> uints l\<close>
    by (auto simp add: uints_def take_bit_eq_mod power_add Divides.mod_mult2_eq)
  ultimately have \<open>concat_bit n b a = take_bit m (concat_bit n b a)\<close>
    by (simp add: concat_bit_eq take_bit_eq_mod push_bit_eq_mult Divides.mod_mult2_eq)
  then show ?thesis
    by (simp add: uints_def)
qed

end
