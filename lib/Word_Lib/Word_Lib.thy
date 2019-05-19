(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "Additional Word Operations"

theory Word_Lib
imports
  Word_Syntax
begin

definition
  ptr_add :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "ptr_add ptr n \<equiv> ptr + of_nat n"

definition
  complement :: "'a :: len word \<Rightarrow> 'a word"  where
 "complement x \<equiv> ~~ x"

definition
  alignUp :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
 "alignUp x n \<equiv> x + 2 ^ n - 1 && complement (2 ^ n - 1)"

(* Haskellish names/syntax *)
notation (input)
  test_bit ("testBit")

definition
  w2byte :: "'a :: len word \<Rightarrow> 8 word" where
  "w2byte \<equiv> ucast"


(*
 * Signed division: when the result of a division is negative,
 * we will round towards zero instead of towards minus infinity.
 *)
class signed_div =
  fixes sdiv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "sdiv" 70)
  fixes smod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "smod" 70)

instantiation int :: signed_div
begin
definition "(a :: int) sdiv b \<equiv> sgn (a * b) * (abs a div abs b)"
definition "(a :: int) smod b \<equiv> a - (a sdiv b) * b"
instance ..
end

instantiation word :: (len) signed_div
begin
definition "(a :: ('a::len) word) sdiv b = word_of_int (sint a sdiv sint b)"
definition "(a :: ('a::len) word) smod b = word_of_int (sint a smod sint b)"
instance ..
end

(* Tests *)
lemma
  "( 4 :: word32) sdiv  4 =  1"
  "(-4 :: word32) sdiv  4 = -1"
  "(-3 :: word32) sdiv  4 =  0"
  "( 3 :: word32) sdiv -4 =  0"
  "(-3 :: word32) sdiv -4 =  0"
  "(-5 :: word32) sdiv -4 =  1"
  "( 5 :: word32) sdiv -4 = -1"
  by (simp_all add: sdiv_word_def sdiv_int_def)

lemma
  "( 4 :: word32) smod  4 =   0"
  "( 3 :: word32) smod  4 =   3"
  "(-3 :: word32) smod  4 =  -3"
  "( 3 :: word32) smod -4 =   3"
  "(-3 :: word32) smod -4 =  -3"
  "(-5 :: word32) smod -4 =  -1"
  "( 5 :: word32) smod -4 =   1"
  by (simp_all add: smod_word_def smod_int_def sdiv_int_def)


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
  "sign_extend n w \<equiv> if w !! n then w || ~~mask n else w && mask n"

definition
  sign_extended :: "nat \<Rightarrow> 'a::len word \<Rightarrow> bool"
where
  "sign_extended n w \<equiv> \<forall>i. n < i \<longrightarrow> i < size w \<longrightarrow> w !! i = w !! n"


lemma ptr_add_0 [simp]:
  "ptr_add ref 0 = ref "
  unfolding ptr_add_def by simp

lemma shiftl_power:
  "(shiftl1 ^^ x) (y::'a::len word) = 2 ^ x * y"
  apply (induct x)
   apply simp
  apply (simp add: shiftl1_2t)
  done

lemmas of_bl_reasoning = to_bl_use_of_bl of_bl_append

lemma uint_of_bl_is_bl_to_bin_drop:
  "length (dropWhile Not l) \<le> LENGTH('a) \<Longrightarrow> uint (of_bl l :: 'a::len word) = bl_to_bin l"
  apply (simp add: of_bl_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num bl_to_bin_ge0)
  apply (rule order_less_le_trans)
  apply (rule bl_to_bin_lt2p_drop)
  apply (simp)
  done

corollary uint_of_bl_is_bl_to_bin:
  "length l\<le>LENGTH('a) \<Longrightarrow> uint ((of_bl::bool list\<Rightarrow> ('a :: len) word) l) = bl_to_bin l"
  apply(rule uint_of_bl_is_bl_to_bin_drop)
  using le_trans length_dropWhile_le by blast


lemma bin_to_bl_or:
  "bin_to_bl n (a OR b) = map2 (\<or>) (bin_to_bl n a) (bin_to_bl n b)"
  using bl_or_aux_bin[where n=n and v=a and w=b and bs="[]" and cs="[]"]
  by simp

lemma word_ops_nth [simp]:
  shows
  word_or_nth:  "(x || y) !! n = (x !! n \<or> y !! n)" and
  word_and_nth: "(x && y) !! n = (x !! n \<and> y !! n)" and
  word_xor_nth: "(x xor y) !! n = (x !! n \<noteq> y !! n)"
  by ((cases "n < size x",
      auto dest: test_bit_size simp: word_ops_nth_size word_size)[1])+

(* simp del to avoid warning on the simp add in iff *)
declare test_bit_1 [simp del, iff]

(* test: *)
lemma "1 < (1024::32 word) \<and> 1 \<le> (1024::32 word)" by simp

lemma and_not_mask:
  "w AND NOT mask n = (w >> n) << n"
  apply (rule word_eqI)
  apply (simp add : word_ops_nth_size word_size)
  apply (simp add : nth_shiftr nth_shiftl)
  by auto

lemma and_mask:
  "w AND mask n = (w << (size w - n)) >> (size w - n)"
  apply (rule word_eqI)
  apply (simp add : word_ops_nth_size word_size)
  apply (simp add : nth_shiftr nth_shiftl)
  by auto

lemma AND_twice [simp]:
  "(w && m) && m = w && m"
  by (simp add: word_eqI)

lemma word_combine_masks:
  "w && m = z \<Longrightarrow> w && m' = z' \<Longrightarrow> w && (m || m') = (z || z')"
  by (auto simp: word_eq_iff)

lemma nth_w2p_same:
  "(2^n :: 'a :: len word) !! n = (n < LENGTH('a))"
  by (simp add : nth_w2p)

lemma p2_gt_0:
  "(0 < (2 ^ n :: 'a :: len word)) = (n < LENGTH('a))"
  apply (simp add : word_gt_0)
  apply safe
   apply (erule swap)
   apply (rule word_eqI)
   apply (simp add : nth_w2p)
  apply (drule word_eqD)
  apply simp
  apply (erule notE)
  apply (erule nth_w2p_same [THEN iffD2])
  done

lemmas uint_2p_alt = uint_2p [unfolded p2_gt_0]

lemma shiftr_div_2n_w: "n < size w \<Longrightarrow> w >> n = w div (2^n :: 'a :: len word)"
  apply (unfold word_div_def)
  apply (simp add : uint_2p_alt word_size)
  apply (rule word_uint.Rep_inverse' [THEN sym])
  apply (rule shiftr_div_2n)
  done

lemmas less_def = less_eq [symmetric]
lemmas le_def = not_less [symmetric, where ?'a = nat]

lemmas p2_eq_0 [simp] = trans [OF eq_commute
  iffD2 [OF Not_eq_iff p2_gt_0, folded le_def, unfolded word_gt_0 not_not]]

lemma neg_mask_is_div':
  "n < size w \<Longrightarrow> w AND NOT mask n = ((w div (2 ^ n)) * (2 ^ n))"
  by (simp add : and_not_mask shiftr_div_2n_w shiftl_t2n word_size)

lemma neg_mask_is_div:
  "w AND NOT mask n = (w div 2^n) * 2^n"
  apply (cases "n < size w")
   apply (erule neg_mask_is_div')
  apply (simp add: word_size)
  apply (frule p2_gt_0 [THEN Not_eq_iff [THEN iffD2], THEN iffD2])
  apply (simp add: word_gt_0  del: p2_eq_0)
  apply (rule word_eqI)
  apply (simp add: word_ops_nth_size word_size)
  done

lemma and_mask_arith':
  "0 < n \<Longrightarrow> w AND mask n = (w * 2^(size w - n)) div 2^(size w - n)"
  by (simp add: and_mask shiftr_div_2n_w shiftl_t2n word_size mult.commute)

lemmas p2len = iffD2 [OF p2_eq_0 order_refl]

lemma and_mask_arith:
  "w AND mask n = (w * 2^(size w - n)) div 2^(size w - n)"
  apply (cases "0 < n")
   apply (erule and_mask_arith')
  apply (simp add: word_size)
  apply (simp add: word_of_int_hom_syms word_div_def)
  done

lemma mask_2pm1: "mask n = 2 ^ n - 1"
  by (simp add : mask_def)

lemma word_and_mask_le_2pm1: "w && mask n \<le> 2 ^ n - 1"
  by (simp add: mask_2pm1[symmetric] word_and_le1)

lemma is_aligned_AND_less_0:
  "u && mask n = 0 \<Longrightarrow> v < 2^n \<Longrightarrow> u && v = 0"
  apply (drule less_mask_eq)
  apply (simp add: mask_2pm1)
  apply (rule word_eqI)
  apply (clarsimp simp add: word_size)
  apply (drule_tac x=na in word_eqD)
  apply (drule_tac x=na in word_eqD)
  apply simp
  done

lemma le_shiftr1:
  "u <= v \<Longrightarrow> shiftr1 u <= shiftr1 v"
  apply (unfold word_le_def shiftr1_def word_ubin.eq_norm)
  apply (unfold bin_rest_trunc_i
                trans [OF bintrunc_bintrunc_l word_ubin.norm_Rep,
                          unfolded word_ubin.norm_Rep,
                       OF order_refl [THEN le_SucI]])
  apply (case_tac "uint u" rule: bin_exhaust)
  apply (rename_tac bs bit)
  apply (case_tac "uint v" rule: bin_exhaust)
  apply (rename_tac bs' bit')
  apply (case_tac "bit")
   apply (case_tac "bit'", auto simp: less_eq_int_code le_Bits)[1]
  apply (case_tac bit')
   apply (simp add: le_Bits less_eq_int_code)
  apply (auto simp: le_Bits less_eq_int_code)
  done

lemma le_shiftr:
  "u \<le> v \<Longrightarrow> u >> (n :: nat) \<le> (v :: 'a :: len0 word) >> n"
  apply (unfold shiftr_def)
  apply (induct_tac "n")
   apply auto
  apply (erule le_shiftr1)
  done

lemma shiftr_mask_le:
  "n <= m \<Longrightarrow> mask n >> m = 0"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr)
  done

lemmas shiftr_mask = order_refl [THEN shiftr_mask_le, simp]

lemma word_leI:
  "(\<And>n.  \<lbrakk>n < size (u::'a::len0 word); u !! n \<rbrakk> \<Longrightarrow> (v::'a::len0 word) !! n) \<Longrightarrow> u <= v"
  apply (rule xtr4)
   apply (rule word_and_le2)
  apply (rule word_eqI)
  apply (simp add: word_ao_nth)
  apply safe
    apply assumption
   apply (erule_tac [2] asm_rl)
  apply (unfold word_size)
  by auto

lemma le_mask_iff:
  "(w \<le> mask n) = (w >> n = 0)"
  apply safe
   apply (rule word_le_0_iff [THEN iffD1])
   apply (rule xtr3)
    apply (erule_tac [2] le_shiftr)
   apply simp
  apply (rule word_leI)
  apply (rename_tac n')
  apply (drule_tac x = "n' - n" in word_eqD)
  apply (simp add : nth_shiftr word_size)
  apply (case_tac "n <= n'")
  by auto

lemma and_mask_eq_iff_shiftr_0:
  "(w AND mask n = w) = (w >> n = 0)"
  apply (unfold test_bit_eq_iff [THEN sym])
  apply (rule iffI)
   apply (rule ext)
   apply (rule_tac [2] ext)
   apply (auto simp add : word_ao_nth nth_shiftr)
    apply (drule arg_cong)
    apply (drule iffD2)
     apply assumption
    apply (simp add : word_ao_nth)
   prefer 2
   apply (simp add : word_size test_bit_bin)
  apply (drule_tac f = "%u. u !! (x - n)" in arg_cong)
  apply (simp add : nth_shiftr)
  apply (case_tac "n <= x")
   apply auto
  done

lemmas and_mask_eq_iff_le_mask = trans
  [OF and_mask_eq_iff_shiftr_0 le_mask_iff [THEN sym]]

lemma mask_shiftl_decompose:
  "mask m << n = mask (m + n) && ~~ mask n"
  by (auto intro!: word_eqI simp: and_not_mask nth_shiftl nth_shiftr word_size)

lemma one_bit_shiftl: "set_bit 0 n True = (1 :: 'a :: len word) << n"
  apply (rule word_eqI)
  apply (auto simp add: test_bit_set_gen nth_shiftl word_size
              simp del: word_set_bit_0 shiftl_1)
  done

lemmas one_bit_pow = trans [OF one_bit_shiftl shiftl_1]

lemmas bin_sc_minus_simps =
  bin_sc_simps (2,3,4) [THEN [2] trans, OF bin_sc_minus [THEN sym]]

lemma NOT_eq:
  "NOT (x :: 'a :: len word) = - x - 1"
  apply (cut_tac x = "x" in word_add_not)
  apply (drule add.commute [THEN trans])
  apply (drule eq_diff_eq [THEN iffD2])
  by simp

lemma NOT_mask: "NOT (mask n) = -(2 ^ n)"
  by (simp add : NOT_eq mask_2pm1)

lemma le_m1_iff_lt: "(x > (0 :: 'a :: len word)) = ((y \<le> x - 1) = (y < x))"
  by uint_arith

lemmas gt0_iff_gem1 = iffD1 [OF iffD1 [OF iff_left_commute le_m1_iff_lt] order_refl]

lemmas power_2_ge_iff = trans [OF gt0_iff_gem1 [THEN sym] p2_gt_0]

lemma le_mask_iff_lt_2n:
  "n < len_of TYPE ('a) = (((w :: 'a :: len word) \<le> mask n) = (w < 2 ^ n))"
  unfolding mask_2pm1 by (rule trans [OF p2_gt_0 [THEN sym] le_m1_iff_lt])

lemmas mask_lt_2pn =
  le_mask_iff_lt_2n [THEN iffD1, THEN iffD1, OF _ order_refl]

lemma bang_eq:
  fixes x :: "'a::len0 word"
  shows "(x = y) = (\<forall>n. x !! n = y !! n)"
  by (subst test_bit_eq_iff[symmetric]) fastforce

lemma word_unat_power:
  "(2 :: 'a :: len word) ^ n = of_nat (2 ^ n)"
  by simp

lemma of_nat_mono_maybe:
  assumes xlt: "x < 2 ^ len_of TYPE ('a)"
  shows   "y < x \<Longrightarrow> of_nat y < (of_nat x :: 'a :: len word)"
  apply (subst word_less_nat_alt)
  apply (subst unat_of_nat)+
  apply (subst mod_less)
   apply (erule order_less_trans [OF _ xlt])
  apply (subst mod_less [OF xlt])
  apply assumption
  done

lemma shiftl_over_and_dist:
  fixes a::"'a::len word"
  shows "(a AND b) << c = (a << c) AND (b << c)"
  apply(rule word_eqI)
  apply(simp add: word_ao_nth nth_shiftl, safe)
  done

lemma shiftr_over_and_dist:
  fixes a::"'a::len word"
  shows "a AND b >> c = (a >> c) AND (b >> c)"
  apply(rule word_eqI)
  apply(simp add:nth_shiftr word_ao_nth)
  done

lemma sshiftr_over_and_dist:
  fixes a::"'a::len word"
  shows "a AND b >>> c = (a >>> c) AND (b >>> c)"
  apply(rule word_eqI)
  apply(simp add:nth_sshiftr word_ao_nth word_size)
  done

lemma shiftl_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b << c = (a << c) OR (b << c)"
  apply(rule word_eqI)
  apply(simp add:nth_shiftl word_ao_nth, safe)
  done

lemma shiftr_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b >> c = (a >> c) OR (b >> c)"
  apply(rule word_eqI)
  apply(simp add:nth_shiftr word_ao_nth)
  done

lemma sshiftr_over_or_dist:
  fixes a::"'a::len word"
  shows "a OR b >>> c = (a >>> c) OR (b >>> c)"
  apply(rule word_eqI)
  apply(simp add:nth_sshiftr word_ao_nth word_size)
  done

lemmas shift_over_ao_dists =
  shiftl_over_or_dist shiftr_over_or_dist
  sshiftr_over_or_dist shiftl_over_and_dist
  shiftr_over_and_dist sshiftr_over_and_dist

lemma shiftl_shiftl:
  fixes a::"'a::len word"
  shows "a << b << c = a << (b + c)"
  apply(rule word_eqI)
  apply(auto simp:word_size nth_shiftl add.commute add.left_commute)
  done

lemma shiftr_shiftr:
  fixes a::"'a::len word"
  shows "a >> b >> c = a >> (b + c)"
  apply(rule word_eqI)
  apply(simp add:word_size nth_shiftr add.left_commute add.commute)
  done

lemma shiftl_shiftr1:
  fixes a::"'a::len word"
  shows "c \<le> b \<Longrightarrow> a << b >> c = a AND (mask (size a - b)) << (b - c)"
  apply(rule word_eqI)
  apply(auto simp:nth_shiftr nth_shiftl word_size word_ao_nth)
  done

lemma shiftl_shiftr2:
  fixes a::"'a::len word"
  shows "b < c \<Longrightarrow> a << b >> c = (a >> (c - b)) AND (mask (size a - c))"
  apply(rule word_eqI)
  apply(auto simp:nth_shiftr nth_shiftl word_size word_ao_nth)
  done

lemma shiftr_shiftl1:
  fixes a::"'a::len word"
  shows "c \<le> b \<Longrightarrow> a >> b << c = (a >> (b - c)) AND (NOT mask c)"
  apply(rule word_eqI)
  apply(auto simp:nth_shiftr nth_shiftl word_size word_ops_nth_size)
  done

lemma shiftr_shiftl2:
  fixes a::"'a::len word"
  shows "b < c \<Longrightarrow> a >> b << c = (a << (c - b)) AND (NOT mask c)"
  apply(rule word_eqI)
  apply(auto simp:nth_shiftr nth_shiftl word_size word_ops_nth_size)
  done

lemmas multi_shift_simps =
  shiftl_shiftl shiftr_shiftr
  shiftl_shiftr1 shiftl_shiftr2
  shiftr_shiftl1 shiftr_shiftl2

lemma word_and_max_word:
  fixes a::"'a::len word"
  shows "x = max_word \<Longrightarrow> a AND x = a"
  by simp

(* Simplifying with word_and_max_word and max_word_def works for arbitrary word sizes,
   but the conditional rewrite can be slow when combined with other common rewrites on
   word expressions. If we are willing to limit our attention to common word sizes,
   the following will usually be much faster. *)
lemmas word_and_max_simps[simplified max_word_def, simplified] =
  word_and_max[where 'a=8] word_and_max[where 'a=16] word_and_max[where 'a=32] word_and_max[where 'a=64]

lemma word_and_1:
  fixes x::"'a::len word"
  shows "(x AND 1) = (if x!!0 then 1 else 0)"
  apply(rule word_eqI)
  apply(simp add:word_ao_nth)
  apply(rule conjI)
   apply(auto)[1]
  apply clarsimp
  apply (case_tac n)
   apply simp
  apply simp
  done

lemma word_and_1_bl:
  fixes x::"'a::len word"
  shows "(x AND 1) = of_bl [x !! 0]"
  by (simp add: word_and_1)

lemma word_1_and_bl:
  fixes x::"'a::len word"
  shows "(1 AND x) = of_bl [x !! 0]"
  by (subst word_bw_comms) (simp add: word_and_1)

lemma scast_scast_id [simp]:
  "scast (scast x :: ('a::len) signed word) = (x :: 'a word)"
  "scast (scast y :: ('a::len) word) = (y :: 'a signed word)"
  by (auto simp: is_up scast_up_scast_id)

lemma scast_ucast_id [simp]:
    "scast (ucast (x :: 'a::len word) :: 'a signed word) = x"
  by (metis down_cast_same is_down len_signed order_refl scast_scast_id(1))

lemma ucast_scast_id [simp]:
    "ucast (scast (x :: 'a::len signed word) :: 'a word) = x"
  by (metis scast_scast_id(2) scast_ucast_id)

lemma scast_of_nat [simp]:
    "scast (of_nat x :: 'a::len signed word) = (of_nat x :: 'a word)"
  by (metis (hide_lams, no_types) len_signed scast_def uint_sint
         word_of_nat word_ubin.Abs_norm word_ubin.eq_norm)

lemma ucast_of_nat:
  "is_down (ucast :: 'a :: len word \<Rightarrow> 'b :: len word)
    \<Longrightarrow> ucast (of_nat n :: 'a word) = (of_nat n :: 'b word)"
  apply (rule sym)
  apply (subst word_unat.inverse_norm)
  apply (simp add: ucast_def word_of_int[symmetric]
                   of_nat_nat[symmetric] unat_def[symmetric])
  apply (simp add: unat_of_nat)
  apply (rule nat_int.Rep_eqD)
  apply (simp only: zmod_int)
  apply (rule mod_mod_cancel)
  by (simp add: is_down le_imp_power_dvd)

(* shortcut for some specific lengths *)
lemma word_fixed_sint_1[simp]:
  "sint (1::8 word) = 1"
  "sint (1::16 word) = 1"
  "sint (1::32 word) = 1"
  "sint (1::64 word) = 1"
  by (auto simp: sint_word_ariths)

lemma word_sint_1 [simp]:
  "sint (1::'a::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  apply (case_tac "LENGTH('a) \<le> 1")
   apply (metis diff_is_0_eq sbintrunc_0_numeral(1) sint_n1 word_1_wi
           word_m1_wi word_msb_1 word_msb_n1 word_sbin.Abs_norm)
  apply (metis bin_nth_1 diff_is_0_eq neq0_conv sbintrunc_minus_simps(4)
            sint_word_ariths(8) uint_1 word_msb_1 word_msb_nth)
  done

lemma scast_1':
  "(scast (1::'a::len word) :: 'b::len word) =
   (word_of_int (sbintrunc (LENGTH('a::len) - Suc 0) (1::int)))"
  by (metis One_nat_def scast_def sint_word_ariths(8))

lemma scast_1 [simp]:
  "(scast (1::'a::len word) :: 'b::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  by (clarsimp simp: scast_1')
     (metis Suc_pred len_gt_0 nat.exhaust sbintrunc_Suc_numeral(1) uint_1 word_uint.Rep_inverse')

lemma scast_eq_scast_id [simp]:
  "((scast (a :: 'a::len signed word) :: 'a word) = scast b) = (a = b)"
  by (metis ucast_scast_id)

lemma ucast_eq_ucast_id [simp]:
  "((ucast (a :: 'a::len word) :: 'a signed word) = ucast b) = (a = b)"
  by (metis scast_ucast_id)

lemma scast_ucast_norm [simp]:
  "(ucast (a :: 'a::len word) = (b :: 'a signed word)) = (a = scast b)"
  "((b :: 'a signed word) = ucast (a :: 'a::len word)) = (a = scast b)"
  by (metis scast_ucast_id ucast_scast_id)+

lemma of_bl_drop:
  "of_bl (drop n xs) = (of_bl xs && mask (length xs - n))"
  apply (clarsimp simp: bang_eq test_bit_of_bl rev_nth cong: rev_conj_cong)
  apply (safe; simp add: word_size to_bl_nth)
  done

lemma of_int_uint [simp]:
  "of_int (uint x) = x"
  by (metis word_of_int word_uint.Rep_inverse')

lemma shiftr_mask2:
  "n \<le> LENGTH('a) \<Longrightarrow> (mask n >> m :: ('a :: len) word) = mask (n - m)"
  apply (rule word_eqI)
  apply (simp add: nth_shiftr word_size)
  apply arith
  done

corollary word_plus_and_or_coroll:
  "x && y = 0 \<Longrightarrow> x + y = x || y"
  using word_plus_and_or[where x=x and y=y]
  by simp

corollary word_plus_and_or_coroll2:
  "(x && w) + (x && ~~ w) = x"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI, simp add: word_size word_ops_nth_size)
  apply (rule word_eqI, simp add: word_size word_ops_nth_size)
  apply blast
  done

lemma less_le_mult_nat':
  "w * c < b * c ==> 0 \<le> c ==> Suc w * c \<le> b * (c::nat)"
  apply (rule mult_right_mono)
   apply (rule Suc_leI)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemmas less_le_mult_nat = less_le_mult_nat'[simplified distrib_right, simplified]

(* FIXME: these should eventually be moved to HOL/Word. *)
lemmas extra_sle_sless_unfolds [simp] =
    word_sle_def[where a=0 and b=1]
    word_sle_def[where a=0 and b="numeral n"]
    word_sle_def[where a=1 and b=0]
    word_sle_def[where a=1 and b="numeral n"]
    word_sle_def[where a="numeral n" and b=0]
    word_sle_def[where a="numeral n" and b=1]
    word_sless_alt[where a=0 and b=1]
    word_sless_alt[where a=0 and b="numeral n"]
    word_sless_alt[where a=1 and b=0]
    word_sless_alt[where a=1 and b="numeral n"]
    word_sless_alt[where a="numeral n" and b=0]
    word_sless_alt[where a="numeral n" and b=1]
  for n


lemma to_bl_1:
  "to_bl (1::'a::len word) = replicate (LENGTH('a) - 1) False @ [True]"
proof -
  have "to_bl (1 :: 'a::len word) = to_bl (mask 1 :: 'a::len word)"
    by (simp add: mask_def)

  also have "\<dots> = replicate (LENGTH('a) - 1) False @ [True]"
    by (cases "LENGTH('a)"; clarsimp simp: to_bl_mask)

  finally show ?thesis .
qed

lemma list_of_false:
  "True \<notin> set xs \<Longrightarrow> xs = replicate (length xs) False"
  by (induct xs, simp_all)

lemma eq_zero_set_bl:
  "(w = 0) = (True \<notin> set (to_bl w))"
  using list_of_false word_bl.Rep_inject by fastforce

lemma diff_diff_less:
  "(i < m - (m - (n :: nat))) = (i < m \<and> i < n)"
  by auto

lemma pop_count_0[simp]:
  "pop_count 0 = 0"
  by (clarsimp simp:pop_count_def)

lemma pop_count_1[simp]:
  "pop_count 1 = 1"
  by (clarsimp simp:pop_count_def to_bl_1)

lemma pop_count_0_imp_0:
  "(pop_count w = 0) = (w = 0)"
  apply (rule iffI)
   apply (clarsimp simp:pop_count_def)
   apply (subst (asm) filter_empty_conv)
   apply (clarsimp simp:eq_zero_set_bl)
   apply fast
  apply simp
  done

end
