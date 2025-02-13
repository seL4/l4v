(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
Proofs tidied by LCP, 2024-09
 *)

section \<open>Misc word operations\<close>

theory More_Word_Operations
  imports
    "HOL-Library.Word"
    Aligned Reversed_Bit_Lists More_Misc Signed_Words
    Word_Lemmas Many_More Word_EqI

begin

context
  includes bit_operations_syntax
begin

definition
  ptr_add :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "ptr_add ptr n \<equiv> ptr + of_nat n"

definition
  alignUp :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
 "alignUp x n \<equiv> x + 2 ^ n - 1 AND NOT (2 ^ n - 1)"

lemma alignUp_unfold:
  \<open>alignUp w n = (w + mask n) AND NOT (mask n)\<close>
  by (simp add: alignUp_def mask_eq_exp_minus_1 add_mask_fold)

(* standard notation for blocks of 2^n-1 words, usually aligned;
   abbreviation so it simplifies directly *)
abbreviation mask_range :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word set" where
  "mask_range p n \<equiv> {p .. p + mask n}"

definition
  w2byte :: "'a :: len word \<Rightarrow> 8 word" where
  "w2byte \<equiv> ucast"

(* Count leading zeros  *)
definition
  word_clz :: "'a::len word \<Rightarrow> nat"
where
  "word_clz w \<equiv> length (takeWhile Not (to_bl w))"

(* Count trailing zeros  *)
definition
  word_ctz :: "'a::len word \<Rightarrow> nat"
where
  "word_ctz w \<equiv> length (takeWhile Not (rev (to_bl w)))"

lemma word_ctz_unfold:
  \<open>word_ctz w = length (takeWhile (Not \<circ> bit w) [0..<LENGTH('a)])\<close> for w :: \<open>'a::len word\<close>
  by (simp add: word_ctz_def rev_to_bl_eq takeWhile_map)

lemma word_ctz_unfold':
  \<open>word_ctz w = Min (insert LENGTH('a) {n. bit w n})\<close> for w :: \<open>'a::len word\<close>
proof (cases \<open>\<exists>n. bit w n\<close>)
  case True
  then obtain n where \<open>bit w n\<close> ..
  then have "Min (Collect (bit w)) = min LENGTH('a) (Min (Collect (bit w)))"
    by (metis Collect_empty_eq Min_in finite_bit_word mem_Collect_eq min.absorb4 test_bit_conj_lt)
  with \<open>bit w n\<close> show ?thesis
    unfolding word_ctz_unfold
    by (metis Collect_empty_eq Min.insert Min_eq_length_takeWhile finite_bit_word test_bit_conj_lt)
next
  case False
  then have \<open>bit w = bot\<close>
    by auto
  then have \<open>word_ctz w = LENGTH('a)\<close>
    by (simp add: word_ctz_def rev_to_bl_eq bot_fun_def map_replicate_const)
  with \<open>bit w = bot\<close> show ?thesis
    by simp
qed

lemma word_ctz_le: "word_ctz (w :: ('a::len word)) \<le> LENGTH('a)"
proof -
  have "length (takeWhile Not (rev (to_bl w))) \<le> LENGTH('a)"
    by (metis length_rev length_takeWhile_le word_bl_Rep')
  then show ?thesis
    by (simp add: word_ctz_def)
qed

lemma word_ctz_less:
  assumes "w \<noteq> 0"
  shows "word_ctz (w :: ('a::len word)) < LENGTH('a)"
proof -
  have "length (takeWhile Not (rev (to_bl w))) < LENGTH('a)"
    if "True \<in> set (to_bl w)"
    using that by (metis length_rev length_takeWhile_less set_rev word_bl_Rep')
  with assms show ?thesis
    by (auto simp: word_ctz_def eq_zero_set_bl)
qed

lemma take_bit_word_ctz_eq [simp]:
  \<open>take_bit LENGTH('a) (word_ctz w) = word_ctz w\<close>
  for w :: \<open>'a::len word\<close>
  by (force simp: take_bit_nat_eq_self_iff word_ctz_def to_bl_unfold intro: le_less_trans [OF length_takeWhile_le])

lemma word_ctz_not_minus_1:
  \<open>word_of_nat (word_ctz (w :: 'a :: len word)) \<noteq> (- 1 :: 'a::len word)\<close> if \<open>1 < LENGTH('a)\<close>
proof -
  note word_ctz_le
  also from that have \<open>LENGTH('a) < mask LENGTH('a)\<close>
    by (simp add: less_mask)
  finally have \<open>word_ctz w < mask LENGTH('a)\<close> .
  then have \<open>word_of_nat (word_ctz w) < (word_of_nat (mask LENGTH('a)) :: 'a word)\<close>
    by (simp add: of_nat_word_less_iff)
  also have \<open>\<dots> = - 1\<close>
    by (rule bit_word_eqI) (simp add: bit_simps)
  finally show ?thesis
    by simp
qed

lemma unat_of_nat_ctz_mw:
  "unat (of_nat (word_ctz (w :: 'a :: len word)) :: 'a :: len word) = word_ctz w"
  by (simp add: unsigned_of_nat)

lemma unat_of_nat_ctz_smw:
  "unat (of_nat (word_ctz (w :: 'a :: len word)) :: 'a :: len signed word) = word_ctz w"
  by (simp add: unsigned_of_nat)

definition
  word_log2 :: "'a::len word \<Rightarrow> nat"
where
  "word_log2 (w::'a::len word) \<equiv> size w - 1 - word_clz w"

(* Bit population count. Equivalent of __builtin_popcount. *)
definition
  pop_count :: "('a::len) word \<Rightarrow> nat"
where
  "pop_count w \<equiv> length (filter id (to_bl w))"

(* Sign extension from bit n *)
definition
  sign_extend :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word"
where
  "sign_extend n w \<equiv> if bit w n then w OR NOT (mask n) else w AND mask n"

lemma sign_extend_eq_signed_take_bit:
  \<open>sign_extend = signed_take_bit\<close>
proof (rule ext)+
  fix n and w :: \<open>'a::len word\<close>
  show \<open>sign_extend n w = signed_take_bit n w\<close>
  proof (rule bit_word_eqI)
    fix q
    assume \<open>q < LENGTH('a)\<close>
    then show \<open>bit (sign_extend n w) q \<longleftrightarrow> bit (signed_take_bit n w) q\<close>
      by (simp add: bit.disj_conj_distrib2 sign_extend_def signed_take_bit_eq_if_negative
          signed_take_bit_eq_if_positive take_bit_eq_mask)
  qed
qed

definition
  sign_extended :: "nat \<Rightarrow> 'a::len word \<Rightarrow> bool"
where
  "sign_extended n w \<equiv> \<forall>i. n < i \<longrightarrow> i < size w \<longrightarrow> bit w i = bit w n"

lemma ptr_add_0 [simp]:
  "ptr_add ref 0 = ref "
  unfolding ptr_add_def by simp

lemma pop_count_0[simp]:
  "pop_count 0 = 0"
  by (clarsimp simp:pop_count_def)

lemma pop_count_1[simp]:
  "pop_count 1 = 1"
  by (clarsimp simp:pop_count_def to_bl_1)

lemma pop_count_0_imp_0:
  "(pop_count w = 0) = (w = 0)"
proof
  assume "pop_count w = 0"
  then have "\<forall>x\<in>set (to_bl w). \<not> id x"
    by (auto simp: pop_count_def filter_empty_conv)
  then show "w = 0"
    using eq_zero_set_bl by fastforce
qed auto

lemma word_log2_zero_eq [simp]:
  \<open>word_log2 0 = 0\<close>
  by (simp add: word_log2_def word_clz_def word_size)

lemma word_log2_unfold:
  \<open>word_log2 w = (if w = 0 then 0 else Max {n. bit w n})\<close>
  for w :: \<open>'a::len word\<close>
proof (cases \<open>w = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  then obtain r where \<open>bit w r\<close>
    by (auto simp add: bit_eq_iff)
  then have \<open>Max {m. bit w m} = LENGTH('a) - Suc (length
    (takeWhile (Not \<circ> bit w) (rev [0..<LENGTH('a)])))\<close>
    by (subst Max_eq_length_takeWhile [of _ \<open>LENGTH('a)\<close>])
      (auto simp add: bit_imp_le_length)
  then have \<open>word_log2 w = Max {x. bit w x}\<close>
    by (simp add: word_log2_def word_clz_def word_size to_bl_unfold rev_map takeWhile_map)
  with \<open>w \<noteq> 0\<close> show ?thesis
    by simp
qed

lemma word_log2_eqI:
  \<open>word_log2 w = n\<close>
  if \<open>w \<noteq> 0\<close> \<open>bit w n\<close> \<open>\<And>m. bit w m \<Longrightarrow> m \<le> n\<close>
  for w :: \<open>'a::len word\<close>
proof -
  from \<open>w \<noteq> 0\<close> have \<open>word_log2 w = Max {n. bit w n}\<close>
    by (simp add: word_log2_unfold)
  also have \<open>Max {n. bit w n} = n\<close>
    using that by (auto intro: Max_eqI)
  finally show ?thesis .
qed

lemma bit_word_log2:
  \<open>bit w (word_log2 w)\<close> if \<open>w \<noteq> 0\<close>
proof -
  from \<open>w \<noteq> 0\<close> have \<open>\<exists>r. bit w r\<close>
    by (auto intro: bit_eqI)
  then obtain r where \<open>bit w r\<close> ..
  from \<open>w \<noteq> 0\<close> have \<open>word_log2 w = Max {n. bit w n}\<close>
    by (simp add: word_log2_unfold)
  also have \<open>Max {n. bit w n} \<in> {n. bit w n}\<close>
    using \<open>bit w r\<close> by (subst Max_in) auto
  finally show ?thesis
    by simp
qed

lemma word_log2_maximum:
  \<open>n \<le> word_log2 w\<close> if \<open>bit w n\<close>
proof -
  have \<open>n \<le> Max {n. bit w n}\<close>
    using that by (auto intro: Max_ge)
  also from that have \<open>w \<noteq> 0\<close>
    by force
  then have \<open>Max {n. bit w n} = word_log2 w\<close>
    by (simp add: word_log2_unfold)
  finally show ?thesis .
qed

lemma word_log2_nth_not_set:
  "\<lbrakk> word_log2 w < i ; i < size w \<rbrakk> \<Longrightarrow> \<not> bit w i"
  using word_log2_maximum [of w i] by auto

lemma word_log2_max:
  "word_log2 w < size w"
  by (metis bit_word_log2 test_bit_size word_log2_zero_eq word_size_gt_0)

lemma word_clz_0[simp]:
  "word_clz (0::'a::len word) = LENGTH('a)"
  unfolding word_clz_def by simp

lemma word_clz_minus_one[simp]:
  "word_clz (-1::'a::len word) = 0"
  unfolding word_clz_def by simp

lemma is_aligned_alignUp[simp]:
  "is_aligned (alignUp p n) n"
  by (simp add: alignUp_def is_aligned_mask mask_eq_decr_exp word_bw_assocs)

lemma alignUp_le[simp]:
  "alignUp p n \<le> p + 2 ^ n - 1"
  unfolding alignUp_def by (rule word_and_le2)

lemma alignUp_idem:
  fixes a :: "'a::len word"
  assumes "is_aligned a n" "n < LENGTH('a)"
  shows "alignUp a n = a"
  using assms unfolding alignUp_def
  by (metis add_cancel_right_right add_diff_eq and_mask_eq_iff_le_mask mask_eq_decr_exp mask_out_add_aligned order_refl word_plus_and_or_coroll2)

lemma alignUp_not_aligned_eq:
  fixes a :: "'a :: len word"
  assumes al: "\<not> is_aligned a n"
  and     sz: "n < LENGTH('a)"
  shows   "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
proof -
  from \<open>n < LENGTH('a)\<close> have \<open>(2::int) ^ n < 2 ^ LENGTH('a)\<close>
    by simp
  have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz) fact+
  then have um: "unat (a mod 2 ^ n - 1) div 2 ^ n = 0"
    by (simp add: sz less_imp_diff_less p2_gt_0 unat_less_power unat_minus_one word_mod_less_divisor)
  have "a + 2 ^ n - 1 = (a div 2 ^ n) * 2 ^ n + (a mod 2 ^ n) + 2 ^ n - 1"
    by (simp add: word_mod_div_equality)
  also have "\<dots> = (a mod 2 ^ n - 1) + (a div 2 ^ n + 1) * 2 ^ n"
    by (simp add: field_simps)
  finally have \<section>: "a + 2 ^ n - 1 = a mod 2 ^ n - 1 + (a div 2 ^ n + 1) * 2 ^ n" .
  have "2 ^ n + word_of_nat (unat a div 2 ^ n) * 2 ^ n
           = (word_of_nat (unat a div 2 ^ n) + 1) * 2 ^ n"
    by (smt (verit) sz add.commute mult.commute mult_Suc_right of_nat_Suc of_nat_add of_nat_mult word_unat_power)
  then show "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n" using sz
    unfolding alignUp_def
    apply (simp add: \<section> flip: mask_eq_decr_exp)
    by (smt (verit) div_eq_0_iff add.commute is_alignedI mult.commute power_eq_0_iff um
        unat_is_aligned_add word_eq_unatI zero_neq_numeral)
qed

lemma alignUp_ge:
  fixes a :: "'a :: len word"
  assumes sz: "n < LENGTH('a)"
  and nowrap: "alignUp a n \<noteq> 0"
  shows "a \<le> alignUp a n"
proof (cases "is_aligned a n")
  case True
  then show ?thesis using sz
    by (subst alignUp_idem, simp_all)
next
  case False

  have lt0: "unat a div 2 ^ n < 2 ^ (LENGTH('a) - n)" using sz
    by (metis le_add_diff_inverse2 less_mult_imp_div_less order_less_imp_le power_add unsigned_less)

  have eq0: "\<lbrakk>2 ^ n * (unat a div 2 ^ n + 1) = 2 ^ LENGTH('a)\<rbrakk>
             \<Longrightarrow> (a div 2 ^ n + 1) * 2 ^ n = 0"
    by (smt (verit) sz mult.commute of_nat_1 of_nat_add of_nat_mult unat_power_lower word_arith_nat_div word_exp_length_eq_0 word_unat_power)
  have"2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ LENGTH('a)" using sz
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right lt0 nat_le_power_trans nat_less_le)
  moreover have "2 ^ n * (unat a div 2 ^ n + 1) \<noteq> 2 ^ LENGTH('a)" using nowrap sz
    using eq0 alignUp_not_aligned_eq [OF False sz] by argo
  ultimately have lt: "2 ^ n * (unat a div 2 ^ n + 1) < 2 ^ LENGTH('a)" by simp

  have "a = a div 2 ^ n * 2 ^ n + a mod 2 ^ n" by (rule word_mod_div_equality [symmetric])
  also have "\<dots> < (a div 2 ^ n + 1) * 2 ^ n" using sz lt
    by (simp add: field_simps lt0 p2_gt_0 unat_mult_power_lem word_add_less_mono1 word_arith_nat_div word_mod_less_divisor)
  also have "\<dots> =  alignUp a n"
    by (rule alignUp_not_aligned_eq [symmetric]) fact+
  finally show ?thesis by (rule order_less_imp_le)
qed

lemma alignUp_le_greater_al:
  fixes x :: "'a :: len word"
  assumes le: "a \<le> x"
  and     sz: "n < LENGTH('a)"
  and     al: "is_aligned x n"
  shows   "alignUp a n \<le> x"
proof (cases "is_aligned a n")
  case True
  then show ?thesis using sz le by (simp add: alignUp_idem)
next
  case False
  then have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz)
  from al obtain k where xk: "x = 2 ^ n * of_nat k" and kv: "k < 2 ^ (LENGTH('a) - n)"
    by (auto elim!: is_alignedE)
  then have kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ LENGTH('a)"
    using sz
    by (metis nat_mult_power_less_eq nat_power_minus_less unat_of_nat_len unat_power_lower zero_less_numeral)
  have au: "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
    by (rule alignUp_not_aligned_eq) fact+
  also have "\<dots> \<le> of_nat k * 2 ^ n"
  proof (rule word_mult_le_mono1 [OF inc_le _ kn])
    show "a div 2 ^ n < of_nat k" using kv xk le sz anz
      by (simp add: alignUp_div_helper)
    show "(0:: 'a word) < 2 ^ n" using sz by (simp add: p2_gt_0 sz)
  qed

  finally show ?thesis using xk by (simp add: field_simps)
qed

lemma alignUp_is_aligned_nz:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < LENGTH('a)"
  and     ax: "a \<le> x"
  and     az: "a \<noteq> 0"
  shows   "alignUp (a::'a :: len word) n \<noteq> 0"
proof (cases "is_aligned a n")
  case True
  then have "alignUp a n = a" using sz by (simp add: alignUp_idem)
  then show ?thesis using az by simp
next
  case False
  then have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz)

  {
    assume asm: "alignUp a n = 0"

    have lt0: "unat a div 2 ^ n < 2 ^ (LENGTH('a) - n)" using sz
      by (metis le_add_diff_inverse2 less_mult_imp_div_less order_less_imp_le power_add unsigned_less)

    have leq: "2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ LENGTH('a)" using sz
      by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right lt0 nat_le_power_trans
                order_less_imp_le)

    from al obtain k where  kv: "k < 2 ^ (LENGTH('a) - n)" and xk: "x = 2 ^ n * of_nat k"
      by (auto elim!: is_alignedE)

    then have "a div 2 ^ n < of_nat k" using ax sz anz
      by (rule alignUp_div_helper)

    then have r: "unat a div 2 ^ n < k" using sz
      by (simp flip: drop_bit_eq_div unat_drop_bit_eq) (metis leI le_unat_uoi unat_mono)

    have "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
      by (rule alignUp_not_aligned_eq) fact+

    then have "\<dots> = 0" using asm by simp
    then have "2 ^ LENGTH('a) dvd 2 ^ n * (unat a div 2 ^ n + 1)"
      using sz by (simp add: unat_arith_simps ac_simps)
                  (simp add: unat_word_ariths mod_simps mod_eq_0_iff_dvd)
    with leq have "2 ^ n * (unat a div 2 ^ n + 1) = 2 ^ LENGTH('a)"
      by (force elim!: le_SucE)
    then have "unat a div 2 ^ n = 2 ^ LENGTH('a) div 2 ^ n - 1"
      by (metis (no_types, opaque_lifting) Groups.add_ac(2) add.right_neutral
                add_diff_cancel_left' div_le_dividend div_mult_self4 gr_implies_not0
                le_neq_implies_less power_eq_0_iff zero_neq_numeral)
    then have "unat a div 2 ^ n = 2 ^ (LENGTH('a) - n) - 1"
      using sz by (simp add: power_sub)
    then have "2 ^ (LENGTH('a) - n) - 1 < k" using r
      by simp
    then have False using kv by simp
  } then show ?thesis by clarsimp
qed

lemma alignUp_ar_helper:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < LENGTH('a)"
  and    sub: "{x..x + 2 ^ n - 1} \<subseteq> {a..b}"
  and    anz: "a \<noteq> 0"
  shows "a \<le> alignUp a n \<and> alignUp a n + 2 ^ n - 1 \<le> b"
proof
  from al have xl: "x \<le> x + 2 ^ n - 1" by (simp add: is_aligned_no_overflow)

  from xl sub have ax: "a \<le> x"
    by auto

  show "a \<le> alignUp a n"
  proof (rule alignUp_ge)
    show "alignUp a n \<noteq> 0" using al sz ax anz
      by (rule alignUp_is_aligned_nz)
  qed fact+

  show "alignUp a n + 2 ^ n - 1 \<le> b"
  proof (rule order_trans)
    from xl show tp: "x + 2 ^ n - 1 \<le> b" using sub
      by auto

    from ax have "alignUp a n \<le> x"
      by (rule alignUp_le_greater_al) fact+
    then have "alignUp a n + (2 ^ n - 1) \<le> x + (2 ^ n - 1)"
      using xl al is_aligned_no_overflow' olen_add_eqv word_plus_mcs_3 by blast
    then show "alignUp a n + 2 ^ n - 1 \<le> x + 2 ^ n - 1"
      by (simp add: field_simps)
  qed
qed

lemma alignUp_def2:
  "alignUp a sz = a + 2 ^ sz - 1 AND NOT (mask sz)"
  by (simp add: alignUp_def flip: mask_eq_decr_exp)

lemma alignUp_def3:
  "alignUp a sz = 2^ sz + (a - 1 AND NOT (mask sz))"
  by (simp add: alignUp_def2 is_aligned_triv field_simps mask_out_add_aligned)

lemma  alignUp_plus:
  "is_aligned w us \<Longrightarrow> alignUp (w + a) us  = w + alignUp a us"
  by (clarsimp simp: alignUp_def2 mask_out_add_aligned field_simps)

lemma alignUp_distance:
  "alignUp (q :: 'a :: len word) sz - q \<le> mask sz"
  by (metis (no_types) add.commute add_diff_cancel_left alignUp_def2 diff_add_cancel
                       mask_2pm1 subtract_mask(2) word_and_le1 word_sub_le_iff)

lemma is_aligned_diff_neg_mask:
  assumes "is_aligned p sz"
  shows "(p - q AND NOT (mask sz)) = (p - ((alignUp q sz) AND NOT (mask sz)))"
proof -
  have "- q AND NOT (mask sz) = - (alignUp q sz AND NOT (mask sz))"
    by (simp add: eq_neg_iff_add_eq_0 add.commute alignUp_distance is_aligned_neg_mask_eq mask_out_add_aligned and_mask_eq_iff_le_mask flip: mask_eq_x_eq_0)
  with assms show ?thesis
    by (metis diff_conv_add_uminus mask_out_add_aligned)
qed

lemma word_clz_max: "word_clz w \<le> size (w::'a::len word)"
  unfolding word_clz_def
  by (metis length_takeWhile_le word_size_bl)

lemma word_clz_nonzero_max:
  fixes w :: "'a::len word"
  assumes nz: "w \<noteq> 0"
  shows "word_clz w < size (w::'a::len word)"
proof -
  {
    assume a: "word_clz w = size (w::'a::len word)"
    hence "length (takeWhile Not (to_bl w)) = length (to_bl w)"
      by (simp add: word_clz_def word_size)
    hence allj: "\<forall>j\<in>set(to_bl w). \<not> j"
      by (metis a length_takeWhile_less less_irrefl_nat word_clz_def)
    hence "to_bl w = replicate (length (to_bl w)) False"
      using eq_zero_set_bl nz by fastforce
    hence "w = 0"
      by (metis to_bl_0 word_bl.Rep_eqD word_bl_Rep')
    with nz have False by simp
  }
  thus ?thesis using word_clz_max
    by (fastforce intro: le_neq_trans)
qed

(* Sign extension from bit n. *)

lemma bin_sign_extend_iff [bit_simps]:
  \<open>bit (sign_extend e w) i \<longleftrightarrow> bit w (min e i)\<close>
  if \<open>i < LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  using that by (simp add: sign_extend_def bit_simps min_def)

lemma sign_extend_bitwise_if:
  "i < size w \<Longrightarrow> bit (sign_extend e w) i \<longleftrightarrow> (if i < e then bit w i else bit w e)"
  by (simp add: word_size bit_simps)

lemma sign_extend_bitwise_if'  [word_eqI_simps]:
  \<open>i < LENGTH('a) \<Longrightarrow> bit (sign_extend e w) i \<longleftrightarrow> (if i < e then bit w i else bit w e)\<close>
  for w :: \<open>'a::len word\<close>
  using sign_extend_bitwise_if [of i w e] by (simp add: word_size)

lemma sign_extend_bitwise_disj:
  "i < size w \<Longrightarrow> bit (sign_extend e w) i \<longleftrightarrow> i \<le> e \<and> bit w i \<or> e \<le> i \<and> bit w e"
  by (auto simp: sign_extend_bitwise_if)

lemma sign_extend_bitwise_cases:
  "i < size w \<Longrightarrow> bit (sign_extend e w) i \<longleftrightarrow> (i \<le> e \<longrightarrow> bit w i) \<and> (e \<le> i \<longrightarrow> bit w e)"
  by (auto simp: sign_extend_bitwise_if)

lemmas sign_extend_bitwise_disj' = sign_extend_bitwise_disj[simplified word_size]
lemmas sign_extend_bitwise_cases' = sign_extend_bitwise_cases[simplified word_size]

(* Often, it is easier to reason about an operation which does not overwrite
   the bit which determines which mask operation to apply. *)
lemma sign_extend_def':
  "sign_extend n w = (if bit w n then w OR NOT (mask (Suc n)) else w AND mask (Suc n))"
  by (rule bit_word_eqI) (auto simp add: bit_simps sign_extend_eq_signed_take_bit min_def less_Suc_eq_le)

lemma sign_extended_sign_extend:
  "sign_extended n (sign_extend n w)"
  by (clarsimp simp: sign_extended_def word_size sign_extend_bitwise_if)

lemma sign_extended_iff_sign_extend:
  "sign_extended n w \<longleftrightarrow> sign_extend n w = w"
  by (metis linorder_not_le sign_extend_bitwise_cases sign_extend_bitwise_disj sign_extended_def word_eqI)

lemma sign_extended_weaken:
  "sign_extended n w \<Longrightarrow> n \<le> m \<Longrightarrow> sign_extended m w"
  unfolding sign_extended_def by (cases "n < m") auto

lemma sign_extend_sign_extend_eq:
  "sign_extend m (sign_extend n w) = sign_extend (min m n) w"
  by (rule bit_word_eqI) (simp add: sign_extend_eq_signed_take_bit bit_simps)

lemma sign_extended_high_bits:
  "\<lbrakk> sign_extended e p; j < size p; e \<le> i; i < j \<rbrakk> \<Longrightarrow> bit p i = bit p j"
  by (drule (1) sign_extended_weaken; simp add: sign_extended_def)

lemma sign_extend_eq:
  "w AND mask (Suc n) = v AND mask (Suc n) \<Longrightarrow> sign_extend n w = sign_extend n v"
  by (simp flip: take_bit_eq_mask add: sign_extend_eq_signed_take_bit signed_take_bit_eq_iff_take_bit_eq)

lemma sign_extended_add:
  assumes p: "is_aligned p n"
  assumes f: "f < 2 ^ n"
  assumes e: "n \<le> e"
  assumes "sign_extended e p"
  shows "sign_extended e (p + f)"
proof (cases "e < size p")
  case True
  note and_or = is_aligned_add_or[OF p f]
  have "\<not> bit f e"
    using True e less_2p_is_upper_bits_unset[THEN iffD1, OF f]
    by (fastforce simp: word_size)
  hence i: "bit (p + f) e = bit p e"
    by (simp add: and_or bit_simps)
  have fm: "f AND mask e = f"
    by (fastforce intro: subst[where P="\<lambda>f. f AND mask e = f", OF less_mask_eq[OF f]]
                  simp: mask_twice e)
  show ?thesis
    using assms
    by (simp add: and_or bit_or_iff less_2p_is_upper_bits_unset sign_extended_def wsst_TYs(3))
next
  case False thus ?thesis
    by (simp add: sign_extended_def word_size)
qed

lemma sign_extended_neq_mask:
  "\<lbrakk>sign_extended n ptr; m \<le> n\<rbrakk> \<Longrightarrow> sign_extended n (ptr AND NOT (mask m))"
  by (fastforce simp: sign_extended_def word_size neg_mask_test_bit bit_simps)

definition
  "limited_and (x :: 'a :: len word) y \<longleftrightarrow> (x AND y = x)"

lemma limited_and_eq_0:
  "\<lbrakk> limited_and x z; y AND NOT z = y \<rbrakk> \<Longrightarrow> x AND y = 0"
  unfolding limited_and_def
  by (metis and_and_not and_zero_eq word_bw_lcs(1))

lemma limited_and_eq_id:
  "\<lbrakk> limited_and x z; y AND z = z \<rbrakk> \<Longrightarrow> x AND y = x"
  unfolding limited_and_def
  by (erule subst, fastforce simp: word_bw_lcs word_bw_assocs word_bw_comms)

lemma lshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x << n) (z << n)"
  using push_bit_and [of n x z] by (simp add: limited_and_def shiftl_def)

lemma rshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x >> n) (z >> n)"
  using drop_bit_and [of n x z] by (simp add: limited_and_def shiftr_def)

lemmas limited_and_simps1 = limited_and_eq_0 limited_and_eq_id

lemmas is_aligned_limited_and
    = is_aligned_neg_mask_eq[unfolded mask_eq_decr_exp, folded limited_and_def]

lemmas limited_and_simps = limited_and_simps1
       limited_and_simps1[OF is_aligned_limited_and]
       limited_and_simps1[OF lshift_limited_and]
       limited_and_simps1[OF rshift_limited_and]
       limited_and_simps1[OF rshift_limited_and, OF is_aligned_limited_and]
       not_one_eq

definition
  from_bool :: "bool \<Rightarrow> 'a::len word" where
  "from_bool b \<equiv> case b of True \<Rightarrow> of_nat 1
                         | False \<Rightarrow> of_nat 0"

lemma from_bool_eq: \<open>from_bool = of_bool\<close>
  by (simp add: fun_eq_iff from_bool_def)

lemma from_bool_0: "(from_bool x = 0) = (\<not> x)"
  by (simp add: from_bool_def split: bool.split)

lemma from_bool_eq_if':
  "((if P then 1 else 0) = from_bool Q) = (P = Q)"
  by (cases Q) (simp_all add: from_bool_def)

definition
  to_bool :: "'a::len word \<Rightarrow> bool" where
  "to_bool \<equiv> (\<noteq>) 0"

lemma to_bool_and_1:
  "to_bool (x AND 1) \<longleftrightarrow> bit x 0"
  by (simp add: to_bool_def word_and_1)

lemma to_bool_from_bool [simp]: "to_bool (from_bool r) = r"
  unfolding from_bool_def to_bool_def
  by (simp split: bool.splits)

lemma from_bool_neq_0 [simp]: "(from_bool b \<noteq> 0) = b"
  by (simp add: from_bool_def split: bool.splits)

lemma from_bool_mask_simp [simp]:
  "(from_bool r :: 'a::len word) AND 1 = from_bool r"
  unfolding from_bool_def
  by (clarsimp split: bool.splits)

lemma from_bool_1 [simp]: "(from_bool P = 1) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma ge_0_from_bool [simp]: "(0 < from_bool P) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma limited_and_from_bool:
  "limited_and (from_bool b) 1"
  using from_bool_mask_simp limited_and_def by blast

lemma to_bool_1 [simp]: "to_bool 1" by (simp add: to_bool_def)
lemma to_bool_0 [simp]: "\<not>to_bool 0" by (simp add: to_bool_def)

lemma from_bool_eq_if:
  "(from_bool Q = (if P then 1 else 0)) = (P = Q)"
  by (cases Q) (simp_all add: from_bool_def)

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

lemma fold_eq_0_to_bool:
  "(v = 0) = (\<not> to_bool v)"
  by (simp add: to_bool_def)

lemma from_bool_to_bool_iff:
  "w = from_bool b \<longleftrightarrow> to_bool w = b \<and> (w = 0 \<or> w = 1)"
  by (cases b) (auto simp: from_bool_def to_bool_def)

lemma from_bool_eqI:
  "from_bool x = from_bool y \<Longrightarrow> x = y"
  unfolding from_bool_def
  by (auto split: bool.splits)

lemma from_bool_odd_eq_and:
  "from_bool (odd w) = w AND 1"
  unfolding from_bool_def by (simp add: word_and_1 bit_0)

lemma neg_mask_in_mask_range:
  assumes "is_aligned ptr bits"
  shows "(ptr' AND NOT(mask bits) = ptr) = (ptr' \<in> mask_range ptr bits)"
proof -
  have "ptr' AND NOT (mask bits) \<le> ptr'"
    if "ptr = ptr' AND NOT (mask bits)"
    using that word_and_le2 by auto
  moreover have "ptr' \<le> (ptr' AND NOT (mask bits)) + mask bits"
    if "ptr = ptr' AND NOT (mask bits)"
    using that by (simp add: and_neg_mask_plus_mask_mono)
  moreover have "ptr' AND NOT (mask bits) = ptr"
    if "ptr \<le> ptr'" and "ptr' \<le> ptr + mask bits"
    using that assms
    by (meson and_neg_mask_plus_mask_mono order.trans is_aligned_add_step_le is_aligned_neg_mask2 linorder_less_linear word_and_le2)
  ultimately show ?thesis
    using assms atLeastAtMost_iff by blast
qed

lemma aligned_offset_in_range:
  assumes "is_aligned x m"
      and "y < 2 ^ m"
      and "is_aligned p n"
      and "m \<le> n"
    shows "(x + y \<in> {p .. p + mask n}) = (x \<in> mask_range p n)"
proof (subst disjunctive_add)
  fix k show "\<not> bit x k \<or> \<not> bit y k"
    using assms by (metis bit_take_bit_iff is_aligned_nth take_bit_word_eq_self_iff)
next
  have \<open>y AND NOT (mask n) = 0\<close>
    using assms by (metis less_mask_eq mask_overlap_zero)
  with assms show "(x OR y \<in> mask_range p n) = (x \<in> mask_range p n)"
    by (metis less_mask_eq mask_subsume neg_mask_in_mask_range)
qed

lemma mask_range_to_bl':
  assumes "is_aligned (ptr :: 'a :: len word) bits" "bits < LENGTH('a)"
  shows "mask_range ptr bits
       = {x. take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)}"
proof -
  have "take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)"
    if x: "ptr \<le> x" "x \<le> ptr + mask bits"
    for x :: "'a word"
  proof -
    obtain y where "x = ptr + y" "y < 2 ^ bits"
      by (metis x and_mask_less' assms atLeastAtMost_iff bit.double_compl neg_mask_in_mask_range
          word_plus_and_or_coroll2)
    then show ?thesis
      using that assms by (simp add: is_aligned_add_conv)
  qed
  moreover have "ptr \<le> x" "x \<le> ptr + mask bits"
    if x: "take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)"
    for x :: "'a word"
  proof -
    obtain y where y: "y < 2 ^ bits" "to_bl (ptr + y) = to_bl x"
    proof
      let ?y = "of_bl (drop (LENGTH('a) - bits) (to_bl x)) :: 'a word"
      have "length (drop (LENGTH('a) - bits) (to_bl x)) < LENGTH('a)"
        by (simp add: assms)
      then show "?y < 2 ^ bits"
        by (simp add: of_bl_length_less)
      then show "to_bl (ptr + ?y) = to_bl x"
        using x assms is_aligned_add_conv
        by (metis (no_types) append_eq_conv_conj atd_lem bl_and_mask length_replicate
            of_bl_rep_False word_bl.Rep_inverse)
    qed
    show "ptr \<le> x"
      using assms y is_aligned_no_wrap' by auto
    show "x \<le> ptr + mask bits"
      by (metis assms y le_mask_iff_lt_2n word_bl.Rep_eqD word_plus_mono_right
          is_aligned_no_overflow_mask)
  qed
  ultimately show ?thesis
    using assms atLeastAtMost_iff by blast
qed

lemma mask_range_to_bl:
  "is_aligned (ptr :: 'a :: len word) bits
   \<Longrightarrow> mask_range ptr bits
        = {x. take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)}"
  apply (frule is_aligned_get_word_bits, assumption)
  using mask_range_to_bl'
   apply blast
  using power_overflow mask_eq_decr_exp
  by (smt (verit, del_insts) Collect_cong Collect_mem_eq diff_is_0_eq' is_aligned_beyond_length is_aligned_neg_mask2 linorder_not_le mask_range_to_bl' neg_mask_in_mask_range take0)

lemma aligned_mask_range_cases:
  "\<lbrakk> is_aligned (p :: 'a :: len word) n; is_aligned (p' :: 'a :: len word) n' \<rbrakk>
   \<Longrightarrow> mask_range p n \<inter> mask_range p' n' = {} \<or>
       mask_range p n \<subseteq> mask_range p' n' \<or>
       mask_range p n \<supseteq> mask_range p' n'"
  apply (clarsimp simp add: mask_range_to_bl set_eq_iff)
  by (smt (verit, ccfv_threshold) le_refl min.orderE min_le_iff_disj take_take)

lemma aligned_mask_range_offset_subset:
  assumes al: "is_aligned (ptr :: 'a :: len word) sz" and al': "is_aligned x sz'"
  and szv: "sz' \<le> sz"
  and xsz: "x < 2 ^ sz"
  shows "mask_range (ptr+x) sz' \<subseteq> mask_range ptr sz"
  using al
proof (rule is_aligned_get_word_bits)
  assume p0: "ptr = 0" and szv': "LENGTH ('a) \<le> sz"
  then have "(2 ::'a word) ^ sz = 0" by simp
  show ?thesis using p0
    by (simp add: \<open>2 ^ sz = 0\<close> mask_eq_decr_exp)
next
  assume szv': "sz < LENGTH('a)"
  hence blah: "2 ^ (sz - sz') < (2 :: nat) ^ LENGTH('a)"
    using szv by auto
  show ?thesis
  proof -
    have "ptr \<le> ptr + x"
      if "ptr + x \<le> ptr + x + mask sz'"
      using that al xsz is_aligned_no_wrap' by blast
    moreover have "ptr + x + mask sz' \<le> ptr + mask sz"
      if "ptr + x \<le> ptr + x + mask sz'"
      using that aligned_add_aligned aligned_mask_step
    proof -
      have "ptr \<le> ptr + mask sz"
        by (simp add: al is_aligned_no_overflow_mask)
      moreover have "x \<le> mask sz"
        using xsz le_mask_iff_lt_2n szv' by blast
      moreover have "is_aligned (ptr + x) sz'"
        using al al' aligned_add_aligned szv by blast
      ultimately show ?thesis
        using al aligned_mask_step szv word_plus_mono_right by blast
    qed
    ultimately show ?thesis
      by auto
  qed
qed

lemma aligned_mask_ranges_disjoint:
  "\<lbrakk> is_aligned (p :: 'a :: len word) n; is_aligned (p' :: 'a :: len word) n';
     p AND NOT(mask n') \<noteq> p'; p' AND NOT(mask n) \<noteq> p \<rbrakk>
   \<Longrightarrow> mask_range p n \<inter> mask_range p' n' = {}"
  using aligned_mask_range_cases
  by (auto simp: neg_mask_in_mask_range)

lemma aligned_mask_ranges_disjoint2:
  assumes "is_aligned p n"
      and "is_aligned ptr bits"
      and "m \<le> n"
      and "n < size p"
      and "m \<le> bits"
      and "\<forall>y<2 ^ (n - m). p + (y << m) \<notin> mask_range ptr bits"
    shows "mask_range p n \<inter> mask_range ptr bits = {}"
proof -
  have False
    if xp: "p \<le> x" "x \<le> p + mask n"
      and xptr: "ptr \<le> x" "x \<le> ptr + mask bits"
    for x :: "'a word"
  proof -
    have eq_p: "x AND NOT (mask n) = p"
      by (simp add: assms(1) neg_mask_in_mask_range xp)
    have eq_ptr: "x AND NOT (mask bits) = ptr"
      by (simp add: assms(2) neg_mask_in_mask_range xptr)
    have *: "x AND mask n >> m < 2 ^ (n - m)"
      using that assms
      by (metis and_mask_less' le_add_diff_inverse shiftr_less_t2n wsst_TYs(3))
    then have "take_bit (n - m) (drop_bit m x) < 2 ^ (n - m)"
      by (metis drop_bit_take_bit shiftr_def take_bit_eq_mask)
    then have "p + (x AND mask n >> m << m) AND NOT (mask bits) = ptr"
      using assms
      by (smt (verit) AND_NOT_mask_plus_AND_mask_eq and_not_mask eq_p eq_ptr is_aligned_neg_mask_weaken
          word_bw_assocs(1) word_bw_comms(1))
    then show ?thesis
      using * assms(2,6) neg_mask_in_mask_range by blast
  qed
  then show ?thesis
    using range_inter by blast
qed

lemma word_clz_sint_upper[simp]:
  "LENGTH('a) \<ge> 3 \<Longrightarrow> sint (of_nat (word_clz (w :: 'a :: len word)) :: 'a sword) \<le> int (LENGTH('a))"
  using word_clz_max [of w]
  by (smt (verit, ccfv_SIG) id_apply of_int_eq_id of_nat_le_0_iff of_nat_mono semiring_1_class.of_nat_0
      signed_of_nat signed_take_bit_int_eq_self sint_range' wsst_TYs(3))

lemma word_clz_sint_lower[simp]:
  assumes "LENGTH('a) \<ge> 3"
  shows "- sint (of_nat (word_clz (w :: 'a :: len word)) :: 'a signed word) \<le> int (LENGTH('a))"
proof -
  have "\<forall>w. \<not> 2 ^ (LENGTH('a) - 1) < - sint (w::'a signed word)"
    by (smt (verit, ccfv_SIG) len_signed sint_ge)
  have "word_clz w < 2 ^ LENGTH('a)"
    by (metis pow_mono_leq_imp_lt word_clz_max wsst_TYs(3))
  then show ?thesis
    using assms small_powers_of_2 len_signed negative_zle order_le_less_trans
    by (smt (verit, best) int_eq_sint word_clz_max wsst_TYs(3))
qed

lemma mask_range_subsetD:
  "\<lbrakk> p' \<in> mask_range p n; x' \<in> mask_range p' n'; n' \<le> n; is_aligned p n; is_aligned p' n' \<rbrakk> \<Longrightarrow>
   x' \<in> mask_range p n"
  using aligned_mask_step by fastforce

lemma add_mult_in_mask_range:
  "\<lbrakk> is_aligned (base :: 'a :: len word) n; n < LENGTH('a); bits \<le> n; x < 2 ^ (n - bits) \<rbrakk>
   \<Longrightarrow> base + x * 2^bits \<in> mask_range base n"
  by (simp add: is_aligned_no_wrap' mask_2pm1 nasty_split_lt word_less_power_trans2
                word_plus_mono_right)

lemma from_to_bool_last_bit:
  "from_bool (to_bool (x AND 1)) = x AND 1"
  by (metis from_bool_to_bool_iff word_and_1)

lemma sint_ctz:
  \<open>0 \<le> sint (of_nat (word_ctz (x :: 'a :: len word)) :: 'a signed word)
     \<and> sint (of_nat (word_ctz x) :: 'a signed word) \<le> int (LENGTH('a))\<close> (is \<open>?P \<and> ?Q\<close>)
  if \<open>LENGTH('a) > 2\<close>
proof
  have *: \<open>word_ctz x \<le> LENGTH('a)\<close>
    by (simp add: word_ctz_le)
  also have \<open>\<dots> < 2 ^ (LENGTH('a) - Suc 0)\<close>
    using that small_powers_of_2 by simp
  finally have \<open>int (word_ctz x) div 2 ^ (LENGTH('a) - Suc 0) = 0\<close>
    by simp
  then show ?P by (simp add: signed_of_nat bit_iff_odd)
  show ?Q
    by (smt (verit, best) "*" id_apply of_int_eq_id of_nat_0_le_iff of_nat_mono signed_of_nat
        signed_take_bit_int_eq_self sint_range')
qed

lemma unat_of_nat_word_log2:
  "LENGTH('a) < 2 ^ LENGTH('b)
   \<Longrightarrow> unat (of_nat (word_log2 (n :: 'a :: len word)) :: 'b :: len word) = word_log2 n"
  by (metis less_trans unat_of_nat_eq word_log2_max word_size)

lemma aligned_mask_diff:
  "\<lbrakk> is_aligned (dest :: 'a :: len word) bits; is_aligned (ptr :: 'a :: len word) sz;
     bits \<le> sz; sz < LENGTH('a); dest < ptr \<rbrakk>
   \<Longrightarrow> mask bits + dest < ptr"
  by (simp add: add.commute aligned_add_mask_less_eq is_aligned_weaken)

lemma Suc_mask_eq_mask:
  "\<not>bit a n \<Longrightarrow> a AND mask (Suc n) = a AND mask n" for a::"'a::len word"
  by (metis sign_extend_def sign_extend_def')

lemma word_less_high_bits:
  fixes a::"'a::len word"
  assumes high_bits: "\<forall>i > n. bit a i = bit b i"
  assumes less: "a AND mask (Suc n) < b AND mask (Suc n)"
  shows "a < b"
proof -
  let ?masked = "\<lambda>x. x AND NOT (mask (Suc n))"
  from high_bits
  have "?masked a = ?masked b"
    by - word_eqI_solve
  then
  have "?masked a + (a AND mask (Suc n)) < ?masked b + (b AND mask (Suc n))"
    by (metis AND_NOT_mask_plus_AND_mask_eq less word_and_le2 word_plus_strict_mono_right)
  then
  show ?thesis
    by (simp add: AND_NOT_mask_plus_AND_mask_eq)
qed

lemma word_less_bitI:
  fixes a :: "'a::len word"
  assumes hi_bits: "\<forall>i > n. bit a i = bit b i"
  assumes a_bits: "\<not>bit a n"
  assumes b_bits: "bit b n" "n < LENGTH('a)"
  shows "a < b"
proof -
  from b_bits
  have "a AND mask n < b AND mask (Suc n)"
    by (metis bit_mask_iff impossible_bit le2p_bits_unset leI lessI less_Suc_eq_le mask_eq_decr_exp
              word_and_less' word_ao_nth)
  with a_bits
  have "a AND mask (Suc n) < b AND mask (Suc n)"
    by (simp add: Suc_mask_eq_mask)
  with hi_bits
  show ?thesis
    by (rule word_less_high_bits)
qed

lemma word_less_bitD:
  fixes a::"'a::len word"
  assumes less: "a < b"
  shows "\<exists>n. (\<forall>i > n. bit a i = bit b i) \<and> \<not>bit a n \<and> bit b n"
proof -
  define xs where "xs \<equiv> zip (to_bl a) (to_bl b)"
  define tk where "tk \<equiv> length (takeWhile (\<lambda>(x,y). x = y) xs)"
  define  n where  "n \<equiv> LENGTH('a) - Suc tk"
  have n_less: "n < LENGTH('a)"
    by (simp add: n_def)
  moreover
  { fix i
    have "\<not> i < LENGTH('a) \<Longrightarrow> bit a i = bit b i"
      using bit_imp_le_length by blast
    moreover
    assume "i > n"
    with n_less
    have "i < LENGTH('a) \<Longrightarrow> LENGTH('a) - Suc i < tk"
      unfolding n_def by arith
    hence "i < LENGTH('a) \<Longrightarrow> bit a i = bit b i"
      unfolding n_def tk_def xs_def
      by (fastforce dest: takeWhile_take_has_property_nth simp: rev_nth simp flip: nth_rev_to_bl)
    ultimately
    have "bit a i = bit b i"
      by blast
  }
  note all = this
  moreover
  from less
  have "a \<noteq> b" by simp
  then
  obtain i where "to_bl a ! i \<noteq> to_bl b ! i"
    using nth_equalityI word_bl.Rep_eqD word_rotate.lbl_lbl by blast
  then
  have "tk \<noteq> length xs"
    unfolding tk_def xs_def
    by (metis length_takeWhile_less list_eq_iff_zip_eq nat_neq_iff word_rotate.lbl_lbl)
  then
  have "tk < length xs"
    using length_takeWhile_le order_le_neq_trans tk_def by blast
  from nth_length_takeWhile[OF this[unfolded tk_def]]
  have "fst (xs ! tk) \<noteq> snd (xs ! tk)"
    by (clarsimp simp: tk_def)
  with `tk < length xs`
  have "bit a n \<noteq> bit b n"
    by (clarsimp simp: xs_def n_def tk_def nth_rev simp flip: nth_rev_to_bl)
  with less all
  have "\<not>bit a n \<and> bit b n"
    by (metis n_less order.asym word_less_bitI)
  ultimately
  show ?thesis by blast
qed

lemma word_less_bit_eq:
  "(a < b) = (\<exists>n < LENGTH('a). (\<forall>i > n. bit a i = bit b i) \<and> \<not>bit a n \<and> bit b n)" for a::"'a::len word"
  by (meson bit_imp_le_length word_less_bitD word_less_bitI)

end

end