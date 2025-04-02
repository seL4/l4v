(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson and Gerwin Klein, NICTA *)

section \<open>Splitting words into lists\<close>

theory Rsplit
  imports More_Word Bit_Shifts_Infix_Syntax


begin

lemmas th_if_simp1 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct1, THEN mp] for l
lemmas th_if_simp2 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct2, THEN mp] for l


definition bin_split :: \<open>nat \<Rightarrow> int \<Rightarrow> int \<times> int\<close>
  where [simp]: \<open>bin_split n k = (drop_bit n k, take_bit n k)\<close>

lemma [code]:
  "bin_split (Suc n) w = (let (w1, w2) = bin_split n (w div 2) in (w1, of_bool (odd w) + 2 * w2))"
  "bin_split 0 w = (w, 0)"
  by (simp_all add: drop_bit_Suc take_bit_Suc mod_2_eq_odd)

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split n c
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

fun bin_rsplitl_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplitl_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split (min m n) c
      in bin_rsplitl_aux n (m - n) a (b # bs))"

definition bin_rsplitl :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplitl n w = bin_rsplitl_aux n (fst w) (snd w) []"

declare bin_rsplit_aux.simps [simp del]
declare bin_rsplitl_aux.simps [simp del]

lemma bin_nth_split:
  "bin_split n c = (a, b) \<Longrightarrow>
    (\<forall>k. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) a k = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) c (n + k)) \<and>
    (\<forall>k. (bit :: int \<Rightarrow> nat \<Rightarrow> bool) b k = (k < n \<and> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) c k))"
  by (force simp add: bit_simps)

lemma split_bintrunc: "bin_split n c = (a, b) \<Longrightarrow> b = (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n c"
  by simp

lemma bin_cat_split: "bin_split n w = (u, v) \<Longrightarrow> w = (\<lambda>k n l. concat_bit n l k) u n v"
  using bits_ident [of n w]
  by (metis Pair_inject add.commute bin_split_def concat_bit_eq concat_bit_take_bit_eq)

lemma bin_split_cat: "bin_split n ((\<lambda>k n l. concat_bit n l k) v n w) = (v, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w)"
  by (metis bin_cat_split bin_split_def concat_bit_eq_iff concat_bit_take_bit_eq)

lemma bin_split_zero [simp]: "bin_split n 0 = (0, 0)"
  by simp

lemma bin_split_minus1 [simp]:
  "bin_split n (- 1) = (- 1, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n (- 1))"
  by simp

lemma bin_split_trunc:
  "bin_split (min m n) c = (a, b) \<Longrightarrow>
    bin_split n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m c) = ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (m - n) a, b)"
  by (cases \<open>n \<le> m\<close>) (auto simp add: drop_bit_take_bit ac_simps)+

lemma bin_split_trunc1:
  "bin_split n c = (a, b) \<Longrightarrow>
    bin_split n ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m c) = ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) (m - n) a, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m b)"
  by (force simp add: drop_bit_take_bit ac_simps)

lemma bin_split_num: "bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  by (simp add: drop_bit_eq_div take_bit_eq_mod)

lemmas bin_rsplit_aux_simps = bin_rsplit_aux.simps bin_rsplitl_aux.simps
lemmas rsplit_aux_simps = bin_rsplit_aux_simps

lemmas rsplit_aux_simp1s = rsplit_aux_simps [THEN th_if_simp1]

lemmas rsplit_aux_simp2ls = rsplit_aux_simps [THEN th_if_simp2]
\<comment> \<open>these safe to \<open>[simp add]\<close> as require calculating \<open>m - n\<close>\<close>
lemmas bin_rsplit_aux_simp2s [simp] = rsplit_aux_simp2ls [unfolded Let_def]
lemmas rbscl = bin_rsplit_aux_simp2s (2)

lemmas rsplit_aux_0_simps [simp] =
  rsplit_aux_simp1s [OF disjI1] rsplit_aux_simp1s [OF disjI2]

lemma bin_rsplit_aux_append: "bin_rsplit_aux n m c (bs @ cs) = bin_rsplit_aux n m c bs @ cs"
proof (induct n m c bs rule: bin_rsplit_aux.induct)
  case (1 n m c bs)
  then show ?case
    by (simp add: rsplit_aux_simps)
qed

lemma bin_rsplitl_aux_append: "bin_rsplitl_aux n m c (bs @ cs) = bin_rsplitl_aux n m c bs @ cs"
proof (induct n m c bs rule: bin_rsplitl_aux.induct)
  case (1 n m c bs)
  then show ?case
    by (simp add: rsplit_aux_simps)
qed

lemmas rsplit_aux_apps [where bs = "[]"] =
  bin_rsplit_aux_append bin_rsplitl_aux_append

lemmas rsplit_def_auxs = bin_rsplit_def bin_rsplitl_def

lemmas rsplit_aux_alts = rsplit_aux_apps
  [unfolded append_Nil rsplit_def_auxs [symmetric]]

lemma bin_split_minus: "0 < n \<Longrightarrow> bin_split (Suc (n - 1)) w = bin_split n w"
  by auto

lemma bin_split_pred_simp [simp]:
  "(0::nat) < numeral bin \<Longrightarrow>
    bin_split (numeral bin) w =
      (let (w1, w2) = bin_split (numeral bin - 1) ((\<lambda>k::int. k div 2) w)
       in (w1, of_bool (odd w) + 2 * w2))"
  by (simp add: take_bit_rec drop_bit_rec mod_2_eq_odd)

lemma bin_rsplit_aux_simp_alt:
  "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else let (a, b) = bin_split n c in bin_rsplit n (m - n, a) @ b # bs)"
  apply (simp add: rsplit_def_auxs)
  using rsplit_aux_alts(1) by blast

lemmas bin_rsplit_simp_alt =
  trans [OF bin_rsplit_def bin_rsplit_aux_simp_alt]

lemmas bthrs = bin_rsplit_simp_alt [THEN [2] trans]

lemma bin_rsplit_size_sign':
  "n > 0 \<Longrightarrow> rev sw = bin_rsplit n (nw, w) \<Longrightarrow> v\<in>set sw \<Longrightarrow> (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n v = v"
proof (induct sw arbitrary: nw w)
  case Nil
  then show ?case by auto
next
  case (Cons a sw)
  then show ?case
    by (force dest: bthrs split: if_split_asm)
qed

lemmas bin_rsplit_size_sign = bin_rsplit_size_sign' [OF asm_rl
  rev_rev_ident [THEN trans] set_rev [THEN equalityD2 [THEN subsetD]]]

lemma bin_nth_rsplit:
  "\<lbrakk>n > 0; m < n; rev sw = bin_rsplit n (nw, w); k < size sw\<rbrakk>
   \<Longrightarrow> (bit :: int \<Rightarrow> nat \<Rightarrow> bool) (sw ! k) m = (bit :: int \<Rightarrow> nat \<Rightarrow> bool) w (k * n + m)"
proof (induct sw arbitrary: w k nw)
  case Nil
  then show ?case by auto
next
  case (Cons a sw w k nw)
  have "bit ((take_bit n w # sw) ! k) m = bit w (k * n + m)"
    if "rev sw = bin_rsplit n (nw - n, drop_bit n w)"
    using that Cons
    by (cases k) (simp_all add: bit_take_bit_iff bit_drop_bit_eq ac_simps)
  with Cons show ?case
    by (force dest: bthrs split: if_split_asm)
qed

lemma bin_rsplit_all: "0 < nw \<Longrightarrow> nw \<le> n \<Longrightarrow> bin_rsplit n (nw, w) = [(take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n w]"
  by (auto simp: bin_rsplit_def rsplit_aux_simp2ls split: prod.split dest!: split_bintrunc)

lemma bin_rsplit_l [rule_format]:
  "bin_rsplitl n (m, bin) = bin_rsplit n (m, (take_bit :: nat \<Rightarrow> int \<Rightarrow> int) m bin)"
  using wf_less_than
proof (induct m arbitrary: bin rule: wf_induct_rule)
  case (less m)
  then have "bin_rsplitl_aux n (m - n) (drop_bit (min m n) bin) []
           = bin_rsplit_aux n (m - n) (drop_bit n (take_bit m bin)) []"
    if "0 < m" and "0 < n"
    using that  by (simp add: drop_bit_take_bit min_def rsplit_def_auxs)
  then show ?case
    unfolding bin_rsplitl_def bin_rsplit_def
    apply (subst bin_rsplitl_aux.simps)
    apply (clarsimp simp: Let_def ac_simps split: prod.split)
    by (metis rsplit_aux_alts)
qed

lemma bin_rsplit_lemma: "sc - n + (n + lb * n) \<le> m * n \<longleftrightarrow> sc + lb * n \<le> m * n"
  if "0 < sc" for sc m n lb :: nat
proof (cases "sc \<ge> n")
  case False
  with that show ?thesis
    using linorder_le_less_linear [of m lb]
    by (smt (verit, ccfv_SIG) Nat.le_diff_conv2 add_leD2 diff_is_0_eq' le0 mult_Suc mult_le_cancel2 not_less_eq_eq order_trans)
qed auto

lemma bin_rsplit_aux_len_le:
  "n \<noteq> 0 \<Longrightarrow> ws = bin_rsplit_aux n nw w bs \<Longrightarrow>
    length ws \<le> m \<longleftrightarrow> nw + length bs * n \<le> m * n"
proof (induct n nw w bs rule: bin_rsplit_aux.induct)
  case (1 n m c bs)
  then show ?case
    by (simp add: bin_rsplit_aux_simps bin_rsplit_lemma Let_def)
qed

lemma bin_rsplit_len_le: "n \<noteq> 0 \<longrightarrow> ws = bin_rsplit n (nw, w) \<longrightarrow> length ws \<le> m \<longleftrightarrow> nw \<le> m * n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len_le)

lemma bin_rsplit_aux_len:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit_aux n nw w cs) = (nw + n - 1) div n + length cs"
proof (induct n nw w cs rule: bin_rsplit_aux.induct)
  case (1 n m c bs)
  have "\<lbrakk>0 < n; 0 < m\<rbrakk> \<Longrightarrow> Suc ((m - n + n - Suc 0) div n) = (m + n - Suc 0) div n"
    using div_if by force
  with 1 show ?case
    by (auto simp: bin_rsplit_aux.simps)
qed

lemma bin_rsplit_len: "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, w)) = (nw + n - 1) div n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len)

lemma bin_rsplit_aux_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length bs = length cs \<Longrightarrow>
    length (bin_rsplit_aux n nw v bs) =
    length (bin_rsplit_aux n nw w cs)"
proof (induct n nw w cs arbitrary: v bs rule: bin_rsplit_aux.induct)
  case (1 n m w cs v bs)
  show ?case
  proof (cases "m = 0")
    case True
    with \<open>length bs = length cs\<close> show ?thesis by simp
  next
    case False
    from "1.hyps" [of \<open>bin_split n w\<close> \<open>drop_bit n w\<close> \<open>take_bit n w\<close>] \<open>m \<noteq> 0\<close> \<open>n \<noteq> 0\<close>
    have hyp: "\<And>v bs. length bs = Suc (length cs) \<Longrightarrow>
      length (bin_rsplit_aux n (m - n) v bs) =
      length (bin_rsplit_aux n (m - n) (drop_bit n w) (take_bit n w # cs))"
      using bin_rsplit_aux_len by fastforce
    from \<open>length bs = length cs\<close> \<open>n \<noteq> 0\<close> show ?thesis
      by (auto simp add: bin_rsplit_aux_simp_alt Let_def bin_rsplit_len split: prod.split)
  qed
qed

lemma bin_rsplit_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, v)) = length (bin_rsplit n (nw, w))"
  using bin_rsplit_len by presburger

lemma split_uint_lem: "bin_split n (uint w) = (a, b) \<Longrightarrow>
    a = take_bit (LENGTH('a) - n) a \<and> b = take_bit (LENGTH('a)) b"
  for w :: "'a::len word"
  by transfer (simp add: drop_bit_take_bit ac_simps)


definition word_rsplit :: "'a::len word \<Rightarrow> 'b::len word list"
  where "word_rsplit w = map word_of_int (bin_rsplit LENGTH('b) (LENGTH('a), uint w))"

lemma word_rsplit_no:
  "(word_rsplit (numeral bin :: 'b::len word) :: 'a word list) =
    map word_of_int (bin_rsplit (LENGTH('a::len))
      (LENGTH('b), take_bit (LENGTH('b)) (numeral bin)))"
  by (simp add: word_rsplit_def of_nat_take_bit)

lemmas word_rsplit_no_cl [simp] = word_rsplit_no
  [unfolded bin_rsplitl_def bin_rsplit_l [symmetric]]

text \<open>
  This odd result arises from the fact that the statement of the
  result implies that the decoded words are of the same type,
  and therefore of the same length, as the original word.\<close>

lemma word_rsplit_same: "word_rsplit w = [w]"
  by (simp add: word_rsplit_def bintr_uint bin_rsplit_all)

lemma word_rsplit_empty_iff_size: "word_rsplit w = [] \<longleftrightarrow> size w = 0"
  by (simp add: word_rsplit_def bin_rsplit_def word_size bin_rsplit_aux_simp_alt Let_def
      split: prod.split)

lemma test_bit_rsplit [OF refl]:
  fixes sw :: "'a::len word list"
  assumes "sw = word_rsplit w" "m < size (hd sw)" "k < length sw"
    shows "bit (rev sw ! k) m = bit w (k * size (hd sw) + m)"
proof -
  have "bit (rev sw ! k) m = bit (map uint (rev sw) ! k) m"
    by (simp add: assms(3) word_test_bit_def)
  also have "... = bit (uint w) (k * size (hd sw) + m)"
    using assms
    by (simp add: bin_nth_rsplit bit_take_bit_iff rev_map unsigned_of_int
        word_rsplit_def word_size)
  also have "... = bit w (k * size (hd sw) + m)"
    by (simp add: test_bit_def')
  finally show ?thesis .
qed

lemma test_bit_rsplit_alt:
  \<open>bit ((word_rsplit w  :: 'b::len word list) ! i) m \<longleftrightarrow>
    bit w ((length (word_rsplit w :: 'b::len word list) - Suc i) * size (hd (word_rsplit w :: 'b::len word list)) + m)\<close>
  if \<open>i < length (word_rsplit w :: 'b::len word list)\<close> \<open>m < size (hd (word_rsplit w :: 'b::len word list))\<close> \<open>0 < length (word_rsplit w :: 'b::len word list)\<close>
  for w :: \<open>'a::len word\<close>
  by (metis diff_Suc_less length_rev rev_nth rev_rev_ident test_bit_rsplit that)

lemma word_rsplit_len_indep [OF refl refl refl refl]:
  "[u,v] = p \<Longrightarrow> [su,sv] = q \<Longrightarrow> word_rsplit u = su \<Longrightarrow>
    word_rsplit v = sv \<Longrightarrow> length su = length sv"
  by (auto simp: word_rsplit_def bin_rsplit_len_indep)

lemma length_word_rsplit_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) \<le> m \<longleftrightarrow> size w \<le> m * n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len_le)

lemmas length_word_rsplit_lt_size =
  length_word_rsplit_size [unfolded Not_eq_iff linorder_not_less [symmetric]]

lemma length_word_rsplit_exp_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = (size w + n - 1) div n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len)

lemma length_word_rsplit_even_size:
  "n = LENGTH('a::len) \<Longrightarrow> size w = m * n \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = m"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: length_word_rsplit_exp_size div_nat_eqI)

lemmas length_word_rsplit_exp_size' = refl [THEN length_word_rsplit_exp_size]

\<comment> \<open>alternative proof of \<open>word_rcat_rsplit\<close>\<close>
lemmas tdle = times_div_less_eq_dividend
lemmas dtle = xtrans(4) [OF tdle mult.commute]

lemma word_rcat_rsplit: "word_rcat (word_rsplit w) = w"
proof (rule word_eqI)
  fix n
  assume "n < size (word_rcat (word_rsplit w::'b word list)::'a word)"
  then have n: "n < LENGTH('a)"
    by (simp add: word_size)
  show "bit (word_rcat (word_rsplit w::'b word list)::'a word) n = bit w n"
  proof -
    have "\<forall>k. k * (n div k) < LENGTH('a)"
      by (metis (no_types) n order_le_less_trans times_div_less_eq_dividend)
    with n show ?thesis
      by (simp add: length_word_rsplit_lt_size mult.commute test_bit_rcat test_bit_rsplit word_size)
  qed
qed

lemma size_word_rsplit_rcat_size:
  "word_rcat ws = frcw \<Longrightarrow> size frcw = length ws * LENGTH('a)
    \<Longrightarrow> length (word_rsplit frcw::'a word list) = length ws"
  for ws :: "'a::len word list" and frcw :: "'b::len word"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: word_size length_word_rsplit_exp_size' div_nat_eqI)

lemma word_rsplit_rcat_size:
  fixes ws :: "'a::len word list"
  defines "frcw \<equiv> word_rcat ws"
  assumes "size frcw = length ws * LENGTH('a)"
  shows "word_rsplit frcw = ws"
proof (intro nth_equalityI word_eqI)
  show "length (word_rsplit frcw::'a word list) = length ws"
    using size_word_rsplit_rcat_size assms by blast
next
  fix i n
  assume \<section>: "i < length (word_rsplit frcw::'a word list)"
    "n < size (word_rsplit frcw ! i::'a word)"
  then have n: "n < LENGTH('a)"
    by (simp add: word_size)
  then have *: "(length ws - Suc i) * LENGTH('a) + n < length ws * LENGTH('a)"
    using assms div_eq_0_iff td_gal_lt by fastforce
  have i: "i < length ws"
    by (metis \<section> assms(2) length_word_rsplit_even_size)
  then have **: "bit (word_rcat ws :: 'b word) ((length ws - Suc i) * LENGTH('a) + n)
      = bit (ws ! i) n"
    using n assms *
    by (auto simp add: test_bit_rcat [OF refl refl] rev_nth word_size)
  then show "bit (word_rsplit frcw ! i::'a word) n = bit (ws ! i) n"
    using n i assms test_bit_rsplit_alt
    by (metis (mono_tags, lifting) len_gt_0 length_word_rsplit_even_size
         word_size zero_less_mult_pos2)
qed

lemma word_rsplit_upt:
  assumes "size x = LENGTH('a :: len) * n" and "n \<noteq> 0"
  shows "word_rsplit x = map (\<lambda>i. ucast (x >> (i * LENGTH('a))) :: 'a word) (rev [0 ..< n])"
proof -
  have "length (word_rsplit x :: 'a word list) = n"
    by (simp add: assms length_word_rsplit_even_size)
  then show ?thesis
    using assms
    by (intro nth_equalityI word_eqI) (auto simp add: test_bit_rsplit_alt word_size bit_simps rev_nth)
qed

end