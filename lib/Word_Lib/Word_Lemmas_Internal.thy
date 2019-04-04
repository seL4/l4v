(*
 * Copyright 2018, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

section "L4V-Internal Word Lemmas"

text \<open>
  This is a holding area for Word utility lemmas that are too specific or unpolished for the
  AFP, but which are reusable enough to be collected together for the rest of L4V. New
  utility lemmas that only prove facts about words should be added here (in preference to being
  kept where they were first needed).
\<close>

theory Word_Lemmas_Internal
imports Word_Lemmas
begin

(* FIXME: move out of Word_Lib *)
lemma disjCI2:
  "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q"
  by blast

(* FIXME: move out of Word_Lib *)
lemma nat_power_minus_less:
  "a < 2 ^ (x - n) \<Longrightarrow> (a :: nat) < 2 ^ x"
  by (erule order_less_le_trans) simp

(* FIXME: move out of Word_Lib *)
lemma pow_mono_leq_imp_lt:
  "x \<le> y \<Longrightarrow> x < 2 ^ y"
  by (simp add: le_less_trans)

(* FIXME: move out of Word_Lib *)
lemma small_powers_of_2:
  "x \<ge> 3 \<Longrightarrow> x < 2 ^ (x - 1)"
  apply (induct x)
   apply simp
  by (simp add: suc_le_pow_2)

(* FIXME: move out of Word_Lib *)
lemma nat_diff_diff_le_lhs:
  "a + c - b \<le> d \<Longrightarrow> a - (b - c) \<le> (d :: nat)"
  by arith

(* FIXME: move out of Word_Lib *)
lemma nat_le_Suc_less:
  "0 < y \<Longrightarrow> (x \<le> y - Suc 0) = (x < y)"
  by arith

lemma is_aligned_obvious_no_wrap':
  "\<lbrakk> is_aligned ptr sz; x = 2 ^ sz - 1 \<rbrakk>
   \<Longrightarrow> ptr \<le> ptr + x"
  by (fastforce simp: field_simps intro: is_aligned_no_overflow)

lemma mask_zero:
  "is_aligned x a \<Longrightarrow> x && mask a = 0"
  by (metis is_aligned_mask)

lemma fold_eq_0_to_bool:
  "(v = 0) = (\<not> to_bool v)"
  by (simp add: to_bool_def)

lemma is_aligned_neg_mask_eq_concrete:
  "\<lbrakk> is_aligned p n; msk && ~~ mask n = ~~ mask n \<rbrakk>
   \<Longrightarrow> p && msk = p"
  by (metis word_bw_assocs(1) word_bw_comms(1) is_aligned_neg_mask_eq)

lemmas add_ge0_weak = add_increasing[where 'a=int and b=0]

lemma less_diff_gt0:
  "a < b \<Longrightarrow> (0 :: 'a :: len word) < b - a"
  by unat_arith

lemma unat_plus_gt:
  "unat ((a:: 'a :: len word) + b) \<le>  (unat a + unat b)"
  by (clarsimp simp: unat_plus_if_size)

lemma is_aligned_and_not_zero:
  "\<lbrakk> is_aligned n k; n \<noteq> 0 \<rbrakk>
   \<Longrightarrow> 2 ^ k \<le> n"
  by (metis aligned_small_is_0 word_not_le)

lemma const_less:
  "\<lbrakk> (a :: 'a :: len word) - 1 < b; a \<noteq> b \<rbrakk>
   \<Longrightarrow> a < b"
  by (metis less_1_simp word_le_less_eq)

lemma is_aligned_and_2_to_k:
  "(n && 2 ^ k - 1) = 0
   \<Longrightarrow> is_aligned (n :: 'a :: len word) k"
  by (simp add: is_aligned_mask mask_def)

lemma is_aligned_power2:
  "b \<le> a \<Longrightarrow> is_aligned (2 ^ a) b"
  by (metis is_aligned_triv is_aligned_weaken)

lemma add_mult_aligned_neg_mask:
  "\<lbrakk> m && (2 ^ n - 1) = (0 :: 'a :: len word) \<rbrakk>
   \<Longrightarrow> (x + y * m) && ~~ mask n = (x && ~~ mask n) + y * m"
  apply (subgoal_tac "is_aligned (y * m) n")
   apply (subst field_simps, subst mask_out_add_aligned[symmetric], assumption)
   apply (simp add: field_simps)
  apply (simp add: is_aligned_mask mask_2pm1[symmetric])
  apply (simp add:mask_eqs(5)[symmetric])
  done

lemma unat_of_nat_minus_1:
  "\<lbrakk> n < 2 ^ LENGTH('a); n \<noteq> 0 \<rbrakk>
   \<Longrightarrow> (unat (((of_nat n):: 'a :: len word) - 1)) = n - 1"
  apply (subst unat_minus_one)
   apply (rule of_nat_neq_0)
     apply simp
    apply simp
   by (simp add: unat_of_nat_eq)

lemma word_eq_zeroI:
  "a \<le> a - 1 \<Longrightarrow> a = (0:: 'a :: len word)"
  apply (rule ccontr)
  apply (subst (asm) le_m1_iff_lt[THEN iffD1])
   apply unat_arith
  apply simp
  done

lemma sint_eq_uint_2pl:
  "\<lbrakk> (a :: 'a :: len word) < 2 ^ (LENGTH('a) - 1) \<rbrakk>
   \<Longrightarrow> sint a = uint a"
  by (simp add: not_msb_from_less sint_eq_uint word_2p_lem word_size)

lemma aligned_sub_aligned:
  "\<lbrakk> is_aligned (a :: 'a :: len word) n; is_aligned b n; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> is_aligned (a - b) n"
  by (simp add: Aligned.aligned_sub_aligned)

lemma word_add_format:
  "(-1 :: 'a :: len  word) + b + c = b + (c - 1)"
  by simp

lemma upto_enum_word_nth:
  "\<lbrakk> i \<le> j; k \<le> unat (j - i) \<rbrakk>
   \<Longrightarrow> [i .e. j] ! k = i + of_nat k"
  apply (clarsimp simp: upto_enum_def nth_append)
  apply (clarsimp simp: word_le_nat_alt[symmetric])
  apply (rule conjI, clarsimp)
   apply (subst toEnum_of_nat, unat_arith)
   apply unat_arith
  apply (clarsimp simp: not_less unat_sub[symmetric])
  apply unat_arith
  done

lemma upto_enum_step_nth:
  "\<lbrakk> a \<le> c; n \<le> unat ((c - a) div (b - a)) \<rbrakk>
   \<Longrightarrow> [a, b .e. c] ! n = a + of_nat n * (b - a)"
  by (clarsimp simp: upto_enum_step_def not_less[symmetric] upto_enum_word_nth)

lemma neg_mask_add:
  "y && mask n = 0 \<Longrightarrow> x + y && ~~ mask n = (x && ~~ mask n) + y"
  by (clarsimp simp: mask_out_sub_mask mask_eqs(7)[symmetric] mask_twice)

lemma minus_minus_swap:
  "\<lbrakk> a \<le> c; b \<le> d; b \<le> a; d \<le> c ; (d :: nat) - b = c - a \<rbrakk>
   \<Longrightarrow> a - b = c - d"
  by arith

lemma minus_minus_swap':
  "\<lbrakk> c \<le> a; d \<le> b; b \<le> a; d \<le> c ; (b :: nat) - d = a - c \<rbrakk>
   \<Longrightarrow> a - b = c - d"
  by arith

lemma shiftr_shiftl_shiftr[simp]:
  "(x :: 'a :: len word)  >> a << a >> a = x >> a"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr nth_shiftl)
  apply safe
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

lemma add_right_shift:
  "\<lbrakk> x && mask n = 0; y && mask n = 0; x \<le> x + y \<rbrakk>
   \<Longrightarrow> (x + y :: ('a :: len) word) >> n = (x >> n) + (y >> n)"
  apply (simp add: no_olen_add_nat is_aligned_mask[symmetric])
  apply (simp add: unat_arith_simps shiftr_div_2n' split del: if_split)
  apply (subst if_P)
   apply (erule order_le_less_trans[rotated])
   apply (simp add: add_mono)
  apply (simp add: shiftr_div_2n' is_aligned_def)
  done

lemma sub_right_shift:
  "\<lbrakk> x && mask n = 0; y && mask n = 0; y \<le> x \<rbrakk>
   \<Longrightarrow> (x - y) >> n = (x >> n :: 'a :: len word) - (y >> n)"
  using add_right_shift[where x="x - y" and y=y and n=n]
  by (simp add: aligned_sub_aligned is_aligned_mask[symmetric]
                word_sub_le Aligned.aligned_sub_aligned)

lemma and_and_mask_simple:
  "(y && mask n) = mask n \<Longrightarrow> ((x && y) && mask n) = x && mask n"
  by (simp add: word_bool_alg.conj.assoc)

lemma and_and_mask_simple_not:
  "(y && mask n) = 0 \<Longrightarrow> ((x && y) && mask n) = 0"
  by (simp add: word_bool_alg.conj.assoc)

lemma word_and_le':
  "b \<le> c \<Longrightarrow> (a :: 'a :: len word) && b \<le> c"
  by (metis word_and_le1 order_trans)

lemma word_and_less':
  "b < c \<Longrightarrow> (a :: 'a :: len word) && b < c"
  by (metis word_and_le1 xtr7)

lemma shiftr_w2p:
  "x < LENGTH('a)
   \<Longrightarrow> 2 ^ x = (2 ^ (LENGTH('a) - 1) >> (LENGTH('a) - 1 - x) :: 'a :: len word)"
  apply simp
  apply (rule word_eqI)
  apply (auto intro: simp: word_size nth_shiftr nth_w2p)
  done

lemma t2p_shiftr:
  "\<lbrakk> b \<le> a; a < LENGTH('a) \<rbrakk>
   \<Longrightarrow> (2 :: 'a :: len word) ^ a >> b = 2 ^ (a - b)"
  apply (subst shiftr_w2p)
   apply assumption
  apply (subst shiftr_w2p[where x = "a - b"])
   apply arith
  apply (simp add:shiftr_shiftr)
  done

lemma scast_1[simp]:
  "scast (1 :: 'a :: len signed word) = (1 :: 'a word)"
  by simp

lemma ucast_ucast_mask_eq:
  "\<lbrakk> (ucast :: ('a :: len) word \<Rightarrow> ('b :: len) word) x = y;
     x && mask LENGTH('b) = x \<rbrakk>
   \<Longrightarrow> x = ucast y"
  apply (drule_tac f="ucast :: 'b word \<Rightarrow> 'a word" in arg_cong)
  apply (simp add: ucast_ucast_mask)
  done

lemma ucast_up_eq:
  "\<lbrakk> ucast x = (ucast y::'b::len word);
     LENGTH('a) \<le> LENGTH ('b) \<rbrakk>
   \<Longrightarrow> ucast x = (ucast y::'a::len word)"
  apply (subst (asm) bang_eq)
  apply (fastforce simp: nth_ucast word_size intro: word_eqI)
  done

lemma ucast_up_neq:
  "\<lbrakk> ucast x \<noteq> (ucast y::'b::len word);
     LENGTH('b) \<le> LENGTH ('a) \<rbrakk>
   \<Longrightarrow> ucast x \<noteq> (ucast y::'a::len word)"
  apply (clarsimp)
  apply (drule ucast_up_eq)
    apply simp+
  done

lemma is_aligned_neg_mask_weaken:
  "\<lbrakk> is_aligned p n; m \<le> n \<rbrakk>
   \<Longrightarrow> p && ~~ mask m = p"
   using is_aligned_neg_mask_eq is_aligned_weaken by blast

lemma mask_AND_less_0:
  "\<lbrakk> x && mask n = 0; m \<le> n \<rbrakk>
   \<Longrightarrow> x && mask m = 0"
  apply (case_tac "LENGTH('a) \<le> n")
   using is_aligned_mask is_aligned_weaken apply blast+
  done

lemma mask_len_id [simp]:
  "(x :: 'a :: len word) && mask LENGTH('a) = x"
  using uint_lt2p [of x] by (simp add: mask_eq_iff)

lemma scast_ucast_down_same:
  "LENGTH('b) \<le> LENGTH('a)
   \<Longrightarrow> (scast :: 'a :: len word \<Rightarrow> 'b :: len word) = (ucast :: 'a :: len word \<Rightarrow> 'b :: len word)"
  apply (rule down_cast_same [symmetric])
  apply (simp add: is_down_def target_size_def source_size_def word_size)
  done

lemma aligned_mask_disjoint:
  "\<lbrakk> is_aligned (a :: 'a :: len word) n; b \<le> mask n; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> a && b = 0"
  apply (rule word_eqI)
  apply (clarsimp simp: is_aligned_nth word_size mask_def simp del: word_less_sub_le)
  apply (frule le2p_bits_unset)
  apply (case_tac "na < n")
   apply simp
  apply simp
  done

lemma word_aligned_0_sum:
  "\<lbrakk> a + b = 0; is_aligned (a :: 'a :: len word) n; b \<le> mask n; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> a = 0 \<and> b = 0"
  by (simp add: word_plus_and_or_coroll aligned_mask_disjoint word_or_zero)

lemma mask_eq1_nochoice:
  "\<lbrakk> LENGTH('a) > 1; (x :: 'a :: len word) && 1 = x \<rbrakk>
   \<Longrightarrow> x = 0 \<or> x = 1"
  apply (simp add:mask_eq_iff[where n = 1,unfolded mask_def,simplified])
  apply (drule word_2p_lem[where n = 1 and w = x,symmetric,simplified,THEN iffD1,rotated])
   apply (simp add:word_size)
  by (simp add: x_less_2_0_1')

lemmas word_le_mask_eq = le_mask_imp_and_mask

lemma is_aligned_neg_mask2 [simp]:
  "is_aligned (a && ~~ mask n) n"
  apply (cases "n < LENGTH('a)")
   apply (simp add: and_not_mask)
   apply (subst shiftl_t2n)
   apply (rule is_aligned_mult_triv1)
  apply (simp add: not_less NOT_mask power_overflow)
  done

lemma unat_of_nat_ctz_mw:
  "unat (of_nat (word_ctz (w :: 'a :: len word)) :: 'a :: len word) = word_ctz w"
  using word_ctz_le[where w=w, simplified] unat_of_nat_eq[where x="word_ctz w" and 'a="'a"]
        pow_mono_leq_imp_lt
  by simp

lemma unat_of_nat_ctz_smw:
  "unat (of_nat (word_ctz (w :: 'a :: len word)) :: 'a :: len sword) = word_ctz w"
  using word_ctz_le[where w=w, simplified] unat_of_nat_eq[where x="word_ctz w" and 'a="'a"]
        pow_mono_leq_imp_lt
  by (metis le_unat_uoi le_unat_uoi linorder_neqE_nat nat_less_le scast_of_nat
            word_unat.Rep_inverse)

lemma shiftr_and_eq_shiftl:
  fixes w x y :: "'a:: len word"
  assumes r: "(w >> n) && x = y"
  shows "w && (x << n) = (y << n)"
  using assms
  proof -
    { fix i
      assume i: "i < LENGTH('a)"
      hence "test_bit (w && (x << n)) i \<longleftrightarrow> test_bit (y << n) i"
        using word_eqD[where x="i-n", OF r]
        by (cases "n \<le> i") (auto simp: nth_shiftl nth_shiftr)
    } note bits = this
    show ?thesis
      by (rule word_eqI[rule_format], rule bits, simp add: word_size)
  qed

lemma int_and_leR:
  "0 \<le> b \<Longrightarrow> a AND b \<le> (b :: int)"
  by (clarsimp simp: int_and_le bin_sign_def split: if_split_asm)

lemma int_and_leL:
  "0 \<le> a \<Longrightarrow> a AND b \<le> (a :: int)"
  by (metis int_and_leR int_and_comm)

lemma mask_len_max:
  "mask LENGTH('a) = (max_word :: 'a :: len word)"
  by (simp add: max_word_mask)

lemma if_then_1_else_0:
  "((if P then 1 else 0) = (0 :: ('a :: zero_neq_one))) = (\<not> P)"
  by (simp split: if_split)

lemma if_then_0_else_1:
  "((if P then 0 else 1) = (0 :: 'a :: len word)) = (P)"
  by simp

lemmas if_then_simps = if_then_0_else_1 if_then_1_else_0

lemma add_mask_lower_bits':
  "\<lbrakk> len = LENGTH('a); is_aligned (x :: 'a :: len word) n;
     \<forall>n' \<ge> n. n' < len \<longrightarrow> \<not> p !! n' \<rbrakk>
   \<Longrightarrow> x + p && ~~mask n = x"
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

lemma mask_in_range:
  "is_aligned ptr bits
   \<Longrightarrow> (ptr' && (~~ mask bits) = ptr) = (ptr' \<in> {ptr .. ptr + 2 ^ bits - 1})"
  apply (erule is_aligned_get_word_bits)
   defer
   apply (simp add: power_overflow mask_def)
  apply (rule iffI)
   apply (drule sym)
   apply (simp add: word_and_le2)
   apply (subst field_simps[symmetric], subst mask_2pm1[symmetric])
   apply (subst word_plus_and_or_coroll)
    apply (rule word_eqI, clarsimp simp: word_ops_nth_size)
   apply (subgoal_tac "ptr' && ~~ mask bits || mask bits = ptr' || mask bits")
    apply (simp add: le_word_or2)
   apply (rule word_eqI, clarsimp simp: word_ops_nth_size word_size)
   apply fastforce
  apply (subgoal_tac "\<exists>x. ptr' = ptr || x \<and> x && mask bits = x")
   apply (rule word_eqI)
   apply (clarsimp simp: word_ops_nth_size word_size is_aligned_mask)
   apply (drule_tac x=n in word_eqD)+
   apply (simp add: word_ops_nth_size word_size
                    is_aligned_mask)
   apply safe[1]
  apply (subgoal_tac "\<exists>x. ptr' = ptr + x")
   apply clarsimp
   apply (drule(1) word_le_minus_mono_left[where x=ptr])
   apply simp
   apply (subst conj_commute)
   apply (rule exI, rule context_conjI[OF _ word_plus_and_or_coroll])
    apply (subst mask_eq_iff_w2p)
     apply (simp add: word_size)
    apply (rule minus_one_helper5)
     apply simp
    apply simp
   apply (simp add: is_aligned_mask)
   apply (rule word_eqI)
   apply (drule_tac x=n in word_eqD)+
   apply (clarsimp simp: word_ops_nth_size word_size)
  apply (rule exI[where x="ptr' - ptr"])
  apply simp
  done

lemma aligned_range_offset_mem:
  "\<lbrakk> is_aligned (x :: 'a :: len word) m; y < 2 ^ m; is_aligned p n;
     n \<ge> m; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> (x + y \<in> {p .. p + 2 ^ n - 1}) = (x \<in> {p .. p + 2 ^ n - 1})"
  apply (simp only: mask_in_range[symmetric]
                    is_aligned_add_or)
  apply (simp add: word_ao_dist, simp add: mask_out_sub_mask)
  apply (subst less_mask_eq, erule order_less_le_trans)
   apply (simp add: two_power_increasing)
  apply simp
  done

lemma upto_enum_inc_1_len:
  "a < - 1
   \<Longrightarrow> [(0 :: 'a :: len word) .e. 1 + a] = [0 .e. a] @ [1 + a]"
  apply (simp add: upto_enum_word)
  apply (subgoal_tac "unat (1 +a) = 1 + unat a")
    apply simp
   apply (subst unat_plus_simple[THEN iffD1])
   apply (rule word_plus_mono_right2[where b = "2 ^ LENGTH('a) - 2"])
    apply simp
   using minus_one_helper3 apply force
  apply unat_arith
  done

lemma range_to_bl':
  "\<lbrakk> is_aligned (ptr :: 'a :: len word) bits; bits < LENGTH('a) \<rbrakk>
   \<Longrightarrow> {ptr .. ptr + (2 ^ bits) - 1}
        = {x. take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)}"
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (subgoal_tac "\<exists>y. x = ptr + y \<and> y < 2 ^ bits")
    apply clarsimp
    apply (subst is_aligned_add_conv)
       apply assumption
      apply simp
    apply simp
   apply (rule_tac x="x - ptr" in exI)
   apply (simp add: add_diff_eq[symmetric])
   apply (simp only: word_less_sub_le[symmetric])
   apply (rule word_diff_ls')
    apply (simp add: field_simps)
   apply assumption
  apply simp
  apply (subgoal_tac "\<exists>y. y < 2 ^ bits \<and> to_bl (ptr + y) = to_bl x")
   apply clarsimp
   apply (rule conjI)
    apply (erule(1) is_aligned_no_wrap')
   apply (simp only: add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (rule_tac x="of_bl (drop (LENGTH('a) - bits) (to_bl x))" in exI)
  apply (rule context_conjI)
   apply (rule order_less_le_trans [OF of_bl_length])
    apply simp
   apply simp
  apply (subst is_aligned_add_conv)
     apply assumption
    apply simp
  apply (drule sym)
  apply (simp add: word_rep_drop)
  done

lemma range_to_bl:
  "is_aligned (ptr :: 'a :: len word) bits
   \<Longrightarrow> {ptr..ptr + 2 ^ bits - 1}
        = {x. take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)}"
  apply (erule is_aligned_get_word_bits)
   apply (erule(1) range_to_bl')
  apply (rule set_eqI)
  apply (simp add: power_overflow)
  done

lemma aligned_ranges_subset_or_disjoint:
  "\<lbrakk> is_aligned (p :: 'a :: len word) n; is_aligned (p' :: 'a :: len word) n' \<rbrakk>
   \<Longrightarrow> {p .. p + 2 ^ n - 1} \<inter> {p' .. p' + 2 ^ n' - 1} = {}
        \<or> {p .. p + 2 ^ n - 1} \<subseteq> {p' .. p' + 2 ^ n' - 1}
        \<or> {p .. p + 2 ^ n - 1} \<supseteq> {p' .. p' + 2 ^ n' - 1}"
  apply (simp add: range_to_bl)
  apply (rule disjCI2)
  apply (erule nonemptyE)
  apply simp
  apply (subgoal_tac "(\<exists>n''. LENGTH('a) - n = (LENGTH('a) - n') + n'')
                    \<or> (\<exists>n''. LENGTH('a) - n' = (LENGTH('a) - n) + n'')")
   apply (elim conjE disjE exE)
    apply (rule disjI1)
    apply (clarsimp simp: take_add)
   apply (rule disjI2)
   apply (clarsimp simp: take_add)
  apply arith
  done

lemma aligned_range_offset_subset:
  assumes al: "is_aligned (ptr :: 'a :: len word) sz" and al': "is_aligned x sz'"
  and szv: "sz' \<le> sz"
  and xsz: "x < 2 ^ sz"
  shows "{ptr + x .. (ptr + x) + 2 ^ sz' - 1} \<subseteq> {ptr .. ptr + 2 ^ sz - 1}"
  using al
proof (rule is_aligned_get_word_bits)
  assume p0: "ptr = 0" and szv': "LENGTH ('a) \<le> sz"
  hence "(2 :: 'a word) ^ sz = 0" by simp

  thus ?thesis using p0
    apply -
    apply (erule ssubst)
    apply simp
    done
next
  assume szv': "sz < LENGTH('a)"

  hence blah: "2 ^ (sz - sz') < (2 :: nat) ^ LENGTH('a)"
    using szv
    apply -
    apply (rule power_strict_increasing, simp+)
    done
  show ?thesis using szv szv'
    apply (intro range_subsetI)
     apply (rule is_aligned_no_wrap' [OF al xsz])
    apply (simp only: add_diff_eq[symmetric])
    apply (subst add.assoc, rule word_plus_mono_right)
    apply (subst iffD1 [OF le_m1_iff_lt])
    apply (simp add: p2_gt_0)
    apply (rule is_aligned_add_less_t2n[OF al' _ szv xsz])
    apply simp
    apply (simp add: field_simps szv al is_aligned_no_overflow)
    done
qed

lemma aligned_diff:
  "\<lbrakk> is_aligned (dest :: 'a :: len word) bits; is_aligned (ptr :: 'a :: len word) sz;
     bits \<le> sz; sz < LENGTH('a); dest < ptr \<rbrakk>
   \<Longrightarrow> (2 ^ bits - 1) + dest < ptr"
  apply (frule_tac p' = ptr in aligned_ranges_subset_or_disjoint)
   apply assumption
  apply (elim disjE)
    apply clarsimp
    apply (drule_tac ptr = dest in is_aligned_no_overflow)
     apply simp
    apply (drule is_aligned_no_overflow)
    apply clarsimp
    apply (erule impE)
     apply (erule order_trans[OF less_imp_le])
     apply (clarsimp simp:field_simps)
    apply (clarsimp simp:not_less field_simps not_le)
   apply clarsimp
   apply (drule_tac ptr = dest in is_aligned_no_overflow)
    apply simp
   apply fastforce
  apply clarsimp
  apply (frule is_aligned_no_overflow)
  apply (erule impE)
  apply (frule(1) is_aligned_no_overflow)
  apply (rule ccontr)
  apply (clarsimp simp:not_less p_assoc_help)
  apply (subst (asm) add.commute[where b = "(2^ sz - 1)"])
  apply (subst (asm) add.commute[where b = "(2^ bits - 1)"])+
  apply (drule word_sub_mono2)
   apply (rule word_le_minus_mono_left)
   apply (erule(1) two_power_increasing)
   apply (simp add:word_1_le_power)
   apply (simp add:field_simps is_aligned_no_overflow)+
  done

lemma aligned_ranges_subset_or_disjoint_coroll:
  "\<lbrakk> is_aligned (p :: 'a :: len word) n; is_aligned (p' :: 'a :: len word) n';
     p && ~~ mask n' \<noteq> p'; p' && ~~ mask n \<noteq> p \<rbrakk>
   \<Longrightarrow> {p .. p + 2 ^ n - 1} \<inter> {p' .. p' + 2 ^ n' - 1} = {}"
  using aligned_ranges_subset_or_disjoint
  apply (simp only: mask_in_range)
  apply (subgoal_tac "p \<in> {p .. p + 2 ^ n - 1} \<and> p' \<in> {p' .. p' + 2 ^ n' - 1}")
   apply blast
  using is_aligned_neg_mask_eq mask_in_range by blast

lemma neg_mask_combine:
  "~~ mask a && ~~ mask b = ~~ mask (max a b)"
  by (auto simp: word_ops_nth_size word_size intro!: word_eqI)

lemma neg_mask_twice:
  "x && ~~ mask n && ~~ mask m = x && ~~ mask (max n m)"
  by (metis neg_mask_combine)

lemma multiple_mask_trivia:
  "n \<ge> m \<Longrightarrow> (x && ~~ mask n) + (x && mask n && ~~ mask m) = x && ~~ mask m"
  apply (rule trans[rotated], rule_tac w="mask n" in word_plus_and_or_coroll2)
  apply (simp add: word_bw_assocs word_bw_comms word_bw_lcs neg_mask_twice
                   max_absorb2)
  done

lemma distinct_aligned_addresses_accumulate:
  "\<lbrakk> is_aligned p n; is_aligned ptr bits; n \<ge> m; n < size p; m \<le> bits;
     (\<forall> y < 2 ^ (n - m). p + (y << m) \<notin> {ptr .. ptr + 2 ^ bits - 1}) \<rbrakk>
   \<Longrightarrow> {p .. p + 2 ^ n - 1} \<inter> {ptr .. ptr + 2 ^ bits - 1} = {}"
  apply safe
  apply (simp only: mask_in_range[symmetric])
  apply (drule_tac x="(x && mask n) >> m" in spec)
  apply (simp add: shiftr_shiftl1 word_bw_assocs)
  apply (drule mp, rule shiftr_less_t2n)
   apply (subst add_diff_inverse, simp, rule and_mask_less', simp add: word_size)
  apply (clarsimp simp: multiple_mask_trivia word_bw_assocs neg_mask_twice max_absorb2)
  done

lemma leq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + high_bits)
   \<Longrightarrow> (x >> low_bits) \<le> mask high_bits"
  by (simp add: le_mask_iff shiftr_shiftr)

lemma ucast_ucast_eq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + LENGTH('b))
   \<Longrightarrow> ucast((ucast (x >> low_bits)) :: 'b :: len word) = x >> low_bits"
  by (meson and_mask_eq_iff_le_mask eq_ucast_ucast_eq not_le_imp_less shiftr_less_t2n'
      ucast_ucast_len)

lemma const_le_unat:
  "\<lbrakk> b < 2 ^ LENGTH('a); of_nat b \<le> a \<rbrakk>
   \<Longrightarrow> b \<le> unat (a :: 'a :: len word)"
  by (clarsimp simp: word_le_def uint_nat of_nat_inverse)

lemma createNewCaps_guard:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> unat x = c; b < 2 ^ LENGTH('a) \<rbrakk>
         \<Longrightarrow> (n < of_nat b \<and> n < x) = (n < of_nat (min (min b c) c))"
  apply (erule subst)
  apply (simp add: min.assoc)
  apply (rule iffI)
   apply (simp add: min_def word_less_nat_alt split: if_split)
  apply (simp add: min_def word_less_nat_alt not_le le_unat_uoi split: if_split_asm)
  by (simp add: of_nat_inverse)

lemma upt_enum_offset_trivial:
  "\<lbrakk> x < 2 ^ LENGTH('a) - 1 ; n \<le> unat x \<rbrakk>
   \<Longrightarrow> ([(0 :: 'a :: len word) .e. x] ! n) = of_nat n"
  apply (induct x arbitrary: n)
    apply simp
  by (simp add: upto_enum_word_nth)

lemma word_le_mask_out_plus_2sz:
  "x \<le> (x && ~~ mask sz) + 2 ^ sz - 1"
  using mask_in_range[where ptr'=x and bits=sz,
    OF is_aligned_neg_mask2[where a=x]]
  by simp

lemma bits_2_subtract_ineq:
  "i < (n :: ('a :: len) word)
   \<Longrightarrow> 2 ^ bits + 2 ^ bits * unat (n - (1 + i)) = unat (n - i) * 2 ^ bits"
  apply (simp add: unat_sub minus_one_helper2)
  apply (subst unatSuc)
   apply clarsimp
   apply unat_arith
  apply (simp only: mult_Suc_right[symmetric])
  apply (rule trans[OF mult.commute], rule arg_cong2[where f="(*)"], simp_all)
  apply (simp add: word_less_nat_alt)
  done

lemma ucast_add:
  "ucast (a + (b :: 'a :: len word)) = ucast a + (ucast b :: ('a signed word))"
  apply (case_tac "LENGTH('a) = 1")
   apply (clarsimp simp: ucast_def)
   apply (metis (hide_lams, mono_tags) One_nat_def len_signed plus_word.abs_eq
                                       uint_word_arith_bintrs(1) word_ubin.Abs_norm)
  apply (clarsimp simp: ucast_def)
  apply (metis le_refl len_signed plus_word.abs_eq uint_word_arith_bintrs(1) wi_bintr)
  done

lemma ucast_minus:
  "ucast (a - (b :: 'a :: len word)) = ucast a - (ucast b :: ('a signed word))"
  apply (insert ucast_add[where a=a and b="-b"])
  apply (metis (no_types, hide_lams) add_diff_eq diff_add_cancel ucast_add)
  done

lemma scast_ucast_add_one [simp]:
  "scast (ucast (x :: 'a::len word) + (1 :: 'a signed word)) = x + 1"
  apply (subst ucast_1[symmetric])
  apply (subst ucast_add[symmetric])
  apply clarsimp
  done

lemma word_and_le_plus_one:
  "a > 0 \<Longrightarrow> (x :: 'a :: len word) && (a - 1) < a"
  by (simp add: gt0_iff_gem1 word_and_less')

lemma unat_of_ucast_then_shift_eq_unat_of_shift[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) >> n) = unat (x >> n)"
  by (simp add: shiftr_div_2n' unat_ucast_up_simp)

lemma unat_of_ucast_then_mask_eq_unat_of_mask[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) && mask m) = unat (x && mask m)"
  by (metis ucast_and_mask unat_ucast_up_simp)

lemma word_clz_sint_upper[simp]:
  "LENGTH('a) \<ge> 3
   \<Longrightarrow> sint (of_nat (word_clz (w :: 'a :: len word)) :: 'a signed word) \<le> LENGTH('a)"
  apply (subst sint_eq_uint)
   apply (rule not_msb_from_less)
   apply simp
   apply (rule word_of_nat_less)
   apply simp
   apply (rule order_le_less_trans[OF word_clz_max])
   apply (simp add: word_size)
   using small_powers_of_2 apply simp
  apply (subst uint_nat)
  apply (simp add: unat_of_nat)
  apply (subst Divides.mod_less)
    apply simp
   apply (rule order_le_less_trans[OF word_clz_max[simplified]])
   apply (simp add: word_size)
  by (metis word_clz_max wsst_TYs(3))

lemma word_clz_sint_lower[simp]:
  "LENGTH('a) \<ge> 3
   \<Longrightarrow> - sint (of_nat (word_clz (w :: 'a :: len word)) :: 'a signed word) \<le> LENGTH('a)"
  apply (subst sint_eq_uint)
   using small_powers_of_2 uint_nat
   apply (simp add: order_le_less_trans[OF word_clz_max] not_msb_from_less word_of_nat_less
                    word_size)
  by (simp add: uint_nat)

lemma shiftr_less_t2n3:
  "\<lbrakk> (2 :: 'a word) ^ (n + m) = 0; m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> (x :: 'a :: len word) >> n < 2 ^ m"
  by (fastforce intro: shiftr_less_t2n' simp: mask_def power_overflow)

lemma unat_shiftr_le_bound:
  "\<lbrakk> 2 ^ (LENGTH('a :: len) - n) - 1 \<le> bnd; 0 < n \<rbrakk>
   \<Longrightarrow> unat ((x :: 'a word) >> n) \<le> bnd"
  using less_not_refl3 le_step_down_nat le_trans less_or_eq_imp_le word_shiftr_lt
  by (metis (no_types, lifting))

lemma shiftr_eqD:
  "\<lbrakk> x >> n = y >> n; is_aligned x n; is_aligned y n \<rbrakk>
   \<Longrightarrow> x = y"
  by (metis is_aligned_shiftr_shiftl)

lemma word_shiftr_shiftl_shiftr_eq_shiftr:
  "a \<ge> b \<Longrightarrow> (x :: 'a :: len word) >> a << b >> b = x >> a"
  by (simp add: mask_shift multi_shift_simps(5) shiftr_shiftr)

lemma of_int_uint_ucast:
   "of_int (uint (x :: 'a::len word)) = (ucast x :: 'b::len word)"
  by (simp add: ucast_def word_of_int)

lemma mod_mask_drop:
  "\<lbrakk> m = 2 ^ n; 0 < m; mask n && msk = mask n \<rbrakk>
   \<Longrightarrow> (x mod m) && msk = x mod m"
  by (simp add: word_mod_2p_is_mask word_bw_assocs)

lemma mask_eq_ucast_eq:
  "\<lbrakk> x && mask LENGTH('a) = (x :: ('c :: len word));
     LENGTH('a) \<le> LENGTH('b)\<rbrakk>
    \<Longrightarrow> ucast (ucast x :: ('a :: len word)) = (ucast x :: ('b :: len word))"
  by (metis ucast_and_mask ucast_id ucast_ucast_mask ucast_up_eq)

lemma of_nat_less_t2n:
  "of_nat i < (2 :: ('a :: len) word) ^ n
    \<Longrightarrow> n < LENGTH('a) \<and> unat (of_nat i :: 'a word) < 2 ^ n"
  apply (cases "n < LENGTH('a)")
  by (clarsimp simp: word_less_nat_alt power_overflow)+

lemmas double_neg_mask = neg_mask_combine

lemmas int_unat = uint_nat[symmetric]

lemma two_power_increasing_less_1:
  "\<lbrakk> n \<le> m; m \<le> LENGTH('a) \<rbrakk>
   \<Longrightarrow> (2 :: 'a  :: len word) ^ n - 1 \<le> 2 ^ m - 1"
  apply (cases "m = LENGTH('a)")
   apply simp
  apply (rule word_sub_mono)
     apply (simp add: word_le_nat_alt)
    apply simp
   apply (rule order_less_imp_le)
   apply (rule word_power_less_1)
   apply simp
  apply (rule order_less_imp_le)
  apply (rule word_power_less_1)
  apply simp
  done

lemmas word_sub_mono3 = word_plus_mcs_4'

lemma word_sub_mono4:
  "\<lbrakk> y + x \<le> z + x; (y :: ('a :: len) word) \<le> y + x; z \<le> z + x \<rbrakk>
   \<Longrightarrow> y \<le> z"
  apply (subst(asm) add.commute)
  apply (subst(asm) add.commute,
         erule word_sub_mono2)
    apply simp
   apply (simp add: add.commute)+
  done

lemma eq_or_less_helperD:
  "\<lbrakk> n = unat (2 ^ m - 1 :: 'a :: len word) \<or> n < unat (2 ^ m - 1 :: 'a word);
     m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> n < 2 ^ m"
  apply (simp add: unat_sub word_1_le_power)
  apply (subgoal_tac "2 ^ m \<ge> (1 :: nat)")
   apply arith
  apply simp
  done

lemma mask_sub:
  "n \<le> m \<Longrightarrow> mask m - mask n = mask m && ~~ mask n"
  apply (simp add: field_simps)
  apply (subst word_plus_and_or_coroll)
   apply (metis mask_AND_NOT_mask word_bw_comms(1))
  by (metis (no_types, lifting)
            AND_NOT_mask_plus_AND_mask_eq and_mask_eq_iff_shiftr_0 mask_AND_NOT_mask shiftr_mask_le
            word_bool_alg.conj.commute word_bw_comms(2) word_plus_and_or_coroll)

lemma neg_mask_diff_bound:
  "sz'\<le> sz \<Longrightarrow> (ptr && ~~ mask sz') - (ptr && ~~ mask sz) \<le> 2 ^ sz - 2 ^ sz'"
  (is "_ \<Longrightarrow> ?lhs \<le> ?rhs")
proof -
  assume lt: "sz' \<le> sz"
  hence "?lhs = ptr && (mask sz && (~~ mask sz'))"
    apply (simp add: mask_out_sub_mask field_simps mask_and_mask min.absorb2)
    apply (simp add: mask_sub)
    apply (subst word_plus_and_or_coroll)
     apply (simp add: word_bool_alg.conj_left_commute)
    by (metis (no_types, lifting)
              and_mask_eq_iff_shiftr_0 mask_AND_NOT_mask shiftr_mask_le word_bool_alg.conj.commute
              word_bool_alg.conj_disj_distrib word_plus_and_or_coroll word_plus_and_or_coroll2)
  also have "\<dots> \<le> ?rhs" using lt
    apply (simp add: mask_sub[symmetric])
    apply (simp add: mask_def field_simps word_and_le1)
    done
  finally show ?thesis by simp
qed

lemma shift_distinct_helper:
  "\<lbrakk> (x :: 'a :: len word) < bnd; y < bnd; x \<noteq> y; x << n = y << n; n < LENGTH('a);
     bnd - 1 \<le> 2 ^ (LENGTH('a) - n) - 1 \<rbrakk>
   \<Longrightarrow> P"
  apply (cases "n = 0")
   apply simp
  apply (drule word_plus_mono_right[where x=1])
   apply simp_all
   apply (subst word_le_sub1)
    apply (rule power_not_zero)
    apply simp
   apply simp
  apply (drule(1) order_less_le_trans)+
  apply (clarsimp simp: bang_eq)
  apply (drule_tac x="na + n" in spec)
  apply (simp add: nth_shiftl)
  apply (case_tac "na + n < LENGTH('a)", simp_all)
  apply safe
   apply (drule(1) nth_bounded)
    apply simp
   apply simp
  apply (drule(1) nth_bounded)
   apply simp
  apply simp
  done

lemma of_nat_shift_distinct_helper:
  "\<lbrakk> x < bnd; y < bnd; x \<noteq> y; (of_nat x :: 'a :: len word) << n = of_nat y << n;
     n < LENGTH('a); bnd \<le> 2 ^ (LENGTH('a) - n) \<rbrakk>
   \<Longrightarrow> P"
  apply (cases "n = 0")
   apply (simp add: word_unat.Abs_inject unats_def)
  apply (subgoal_tac "bnd < 2 ^ LENGTH('a)")
   apply (erule(1) shift_distinct_helper[rotated, rotated, rotated])
      defer
      apply (erule(1) of_nat_mono_maybe[rotated])
     apply (erule(1) of_nat_mono_maybe[rotated])
    apply (simp add: word_unat.Abs_inject unats_def)
   apply (erule order_le_less_trans)
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply (simp add: word_less_nat_alt)
  apply (simp add: unat_minus_one [OF of_nat_neq_0]
                   word_unat.Abs_inverse unats_def)
  done

lemma pre_helper2:
  "\<lbrakk> is_aligned (base :: 'a :: len word) n; n < LENGTH('a); bits \<le> n; x < 2 ^ (n - bits) \<rbrakk>
   \<Longrightarrow> base + x * 2^bits \<in> {base .. base + 2 ^ n  - 1}"
  apply (subgoal_tac "x * 2^bits < 2 ^ n")
   apply simp
   apply (rule context_conjI)
    apply (erule(1) is_aligned_no_wrap')
   apply (subst add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (drule_tac k="2^bits" in word_mult_less_mono1)
    apply (simp add: p2_gt_0)
   apply (subst unat_power_lower, simp)+
   apply (simp only: power_add[symmetric])
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply (simp add: power_add[symmetric])
  done

lemma of_bl_length2:
  "length xs + c < LENGTH('a) \<Longrightarrow> of_bl xs * 2^c < (2::'a::len word) ^ (length xs + c)"
  apply (simp add: power_add)
  apply (rule word_mult_less_mono1[OF of_bl_length])
  by (auto simp add: p2_gt_0 power_add[symmetric])

lemma ptr_add_distinct_helper:
  "\<lbrakk> ptr_add (p :: 'a :: len word) (x * 2 ^ n) = ptr_add p (y * 2 ^ n); x \<noteq> y;
     x < bnd; y < bnd; n < LENGTH('a);
     bnd \<le> 2 ^ (LENGTH('a) - n) \<rbrakk>
   \<Longrightarrow> P"
  apply (clarsimp simp: ptr_add_def word_unat_power[symmetric]
                        shiftl_t2n[symmetric, simplified mult.commute])
  using of_nat_shift_distinct_helper
  by blast

lemma mask_out_eq_0:
  "\<lbrakk> idx < 2 ^ sz; sz < LENGTH('a) \<rbrakk>
   \<Longrightarrow> ((of_nat idx) :: 'a :: len word) && ~~ mask sz = 0"
  apply (clarsimp simp: mask_out_sub_mask)
  apply (subst less_mask_eq[symmetric])
   apply (erule(1) of_nat_power)
  apply simp
  done

lemma is_aligned_neg_mask_eq':
  "is_aligned ptr sz = (ptr && ~~ mask sz = ptr)"
  apply (rule iffI)
   apply (erule is_aligned_neg_mask_eq)
  apply (simp add: is_aligned_mask)
  apply (drule sym)
  apply (subst (asm) word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
  apply simp
  done

lemma neg_mask_mask_unat:
  "sz < LENGTH('a)
   \<Longrightarrow> unat ((ptr :: 'a :: len word) && ~~ mask sz) + unat (ptr && mask sz) = unat ptr"
  apply (subst unat_plus_simple[THEN iffD1, symmetric])
   apply (simp add: AND_NOT_mask_plus_AND_mask_eq word_and_le2)
  by (simp add: AND_NOT_mask_plus_AND_mask_eq)

lemma unat_pow_le_intro:
  "LENGTH('a) \<le> n \<Longrightarrow> unat (x :: 'a :: len word) < 2 ^ n"
  by (metis (mono_tags, hide_lams)
            less_imp_le less_irrefl lt2p_lem nat_less_le of_nat_le_iff of_nat_numeral
            semiring_1_class.of_nat_power uint_nat)

lemma unat_shiftl_less_t2n:
  "\<lbrakk> unat (x :: 'a :: len word) < 2 ^ (m - n); m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> unat (x << n) < 2 ^ m"
  by (metis (no_types, lifting)
            Word_Lemmas.of_nat_power diff_le_self le_less_trans shiftl_less_t2n unat_less_power
            unat_lt2p unat_of_nat_eq word_less_nat_alt)

lemma unat_is_aligned_add_helper:
  "\<lbrakk> is_aligned p n; unat d < 2 ^ n \<rbrakk>
   \<Longrightarrow> unat (p + d && mask n) = unat d \<and> unat (p + d && ~~ mask n) = unat p"
  by (metis add.right_neutral and_mask_eq_iff_le_mask and_not_mask le_mask_iff mask_add_aligned
            mask_out_add_aligned mult_zero_right shiftl_t2n shiftr_le_0)

lemma unat_shiftr_shiftl_mask_zero:
  "\<lbrakk> c + a \<ge> LENGTH('a) + b ; c < LENGTH('a) \<rbrakk>
   \<Longrightarrow> unat (((q :: 'a :: len word) >> a << b) && ~~ mask c) = 0"
  by (fastforce intro: unat_is_aligned_add_helper[where p=0 and n=c, simplified, THEN conjunct2]
                       unat_shiftl_less_t2n unat_shiftr_less_t2n unat_pow_le_intro)

lemma of_nat_ucast:
  "is_down (ucast :: ('a :: len) word \<Rightarrow> ('b :: len) word)
    \<Longrightarrow> (of_nat n :: 'b word) = ucast (of_nat n :: 'a word)"
  apply (subst word_unat.inverse_norm)
  apply (simp add: ucast_def word_of_int[symmetric]
                   of_nat_nat[symmetric] unat_def[symmetric])
  apply (simp add: unat_of_nat)
  apply (rule nat_int.Rep_eqD)
  apply (simp only: zmod_int)
  apply (rule mod_mod_cancel)
  apply (subst int_dvd_int_iff)
  apply (rule le_imp_power_dvd)
  apply (simp add: is_down_def target_size_def source_size_def word_size)
  done

lemma shift_then_mask_eq_shift_low_bits:
  "x \<le> mask (low_bits + high_bits)
   \<Longrightarrow> (x >> low_bits) && mask high_bits = x >> low_bits"
  by (simp add: leq_mask_shift word_le_mask_eq)

lemma leq_low_bits_iff_zero:
  "\<lbrakk> x \<le> mask (low bits + high bits); x >> low_bits = 0 \<rbrakk>
   \<Longrightarrow> (x && mask low_bits = 0) = (x = 0)"
  using and_mask_eq_iff_shiftr_0 by force

lemma unat_less_iff:
  "\<lbrakk> unat (a :: 'a :: len word) = b; c < 2 ^ LENGTH('a) \<rbrakk>
   \<Longrightarrow> (a < of_nat c) = (b < c)"
  apply (rule iffI)
    apply (drule unat_less_helper)
    apply simp
  using unat_ucast_less_no_overflow by blast

lemma is_aligned_no_overflow3:
 "\<lbrakk> is_aligned (a :: 'a :: len word) n; n < LENGTH('a); b < 2 ^ n; c \<le> 2 ^ n; b< c \<rbrakk>
  \<Longrightarrow> a + b \<le> a + (c - 1)"
  apply (rule word_plus_mono_right)
   apply (simp add:minus_one_helper3)
  apply (erule is_aligned_no_wrap')
  by (meson le_m1_iff_lt minus_one_helper3 not_less)

lemma unat_sub_le_strg:
  "unat v \<le> v2 \<and> x \<le> v \<and> y \<le> v \<and> y < (x :: ('a :: len) word)
    \<longrightarrow> unat (x + (- 1 - y)) \<le> v2"
  apply clarsimp
  apply (erule order_trans[rotated])
  apply (fold word_le_nat_alt)
  apply (rule order_trans[rotated], assumption)
  apply (rule order_trans[rotated], rule word_sub_le[where y="y + 1"])
   apply (erule Word.inc_le)
  apply (simp add: field_simps)
  done

lemma mask_add_aligned_right:
  "is_aligned p n \<Longrightarrow> (q + p) && mask n = q && mask n"
  by (simp add: mask_add_aligned add.commute)

lemma leq_high_bits_shiftr_low_bits_leq_bits:
  "x \<le> 2 ^ high_bits - 1
   \<Longrightarrow> (x :: 'a :: len word) << low_bits \<le> mask (low_bits + high_bits)"
  by (metis le_mask_shiftl_le_mask mask_2pm1)

lemma from_to_bool_last_bit:
  "from_bool (to_bool (x && 1)) = x && 1"
  apply (simp add: from_bool_def to_bool_and_1
              split: bool.split)
  apply (safe intro!: word_eqI, auto)
  done

lemma word_two_power_neg_ineq:
  "2 ^ m \<noteq> (0 :: 'a word) \<Longrightarrow> 2 ^ n \<le> - (2 ^ m :: ('a :: len) word)"
  apply (cases "n < LENGTH('a)", simp_all add: power_overflow)
  apply (cases "m < LENGTH('a)", simp_all add: power_overflow)
  apply (simp add: word_le_nat_alt Aligned.unat_minus word_size)
  apply (cases "LENGTH('a)", simp_all)
  apply (simp add: less_Suc_eq_le)
  apply (drule power_increasing[where a=2 and n=n]
               power_increasing[where a=2 and n=m], simp)+
  apply (drule(1) add_le_mono)
  apply simp
  done

lemma multi_lessD:
  "\<lbrakk> (a :: nat) * b < c; 0 < a; 0 < b \<rbrakk>
   \<Longrightarrow> a < c \<and> b < c"
  by (cases a, simp_all,cases b,simp_all)

lemmas unat_le_helper = word_unat_less_le

lemmas word_of_nat_plus = of_nat_add[where 'a="'a :: len word"]
lemmas word_of_nat_minus = of_nat_diff[where 'a="'a :: len word"]

lemma unat_shiftl_absorb:
  "\<lbrakk> x \<le> 2 ^ p; p + k < LENGTH('a) \<rbrakk>
   \<Longrightarrow> unat (x :: 'a :: len word) * 2 ^ k = unat (x * 2 ^ k)"
  apply (simp add:unat_word_ariths)
  apply (subst mod_less)
   apply (rule le_less_trans[OF mult_le_mono1])
    apply (erule iffD1[OF word_le_nat_alt])
   apply (clarsimp simp: power_add[symmetric])+
  done

(* this is a bit deceptive: 2 ^ len.. = 0, so really this is relying on 'word_n1_ge': ptr \<le> -1 *)
lemma word_up_bound:
  "(ptr :: 'a :: len word) \<le> 2 ^ LENGTH('a) - 1 "
  by auto

lemma word_plus_mono_right_split:
  "\<lbrakk> unat ((x :: 'a :: len word) && mask sz) + unat z < 2 ^ sz; sz < LENGTH('a) \<rbrakk>
   \<Longrightarrow> x \<le> x + z"
  (is "\<lbrakk> ?bound; ?len \<rbrakk> \<Longrightarrow> ?rhs \<le> ?lhs")
  apply (subgoal_tac "(x && ~~ mask sz) + (x && mask sz)
                        \<le> (x && ~~ mask sz) + ((x && mask sz) + z)")
   apply (simp add:word_plus_and_or_coroll2 field_simps)
  apply (rule word_plus_mono_right)
    apply (simp add:no_olen_add )
    apply (rule less_le_trans)
    apply (simp add:uint_nat)
    apply (subst of_nat_add[symmetric])
    apply (drule iffD2[OF of_nat_less_iff])
    apply simp
    apply (rule less_imp_le)
    apply (rule less_le_trans[where y = "2^LENGTH('a)"] )
    apply simp
   apply simp
  apply (rule word_plus_mono_right2)
    apply (rule is_aligned_no_overflow')
    apply (rule Aligned.is_aligned_neg_mask[OF le_refl])
   apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD2])
   apply (simp add: p2_gt_0)
  apply (rule iffD2[OF word_less_nat_alt])
  apply (auto simp:unat_plus_if_size word_size not_less)
  done

lemma mul_not_mask_eq_neg_shiftl:
  "~~ mask n = (-1) << n"
  by (simp add: NOT_mask shiftl_t2n)

lemma shiftr_mul_not_mask_eq_and_not_mask:
  "(x >> n) * ~~ mask n = - (x && ~~ mask n)"
  by (metis (no_types, hide_lams)
            and_not_mask mul_not_mask_eq_neg_shiftl mult_minus_left semiring_normalization_rules(7)
            shiftl_1 shiftl_t2n)

lemma mask_eq_n1_shiftr:
  "n \<le> LENGTH('a)
   \<Longrightarrow> (mask n :: 'a :: len word) = (-1) >> (LENGTH('a) - n)"
  apply (subst word_bl.Rep_inject[symmetric])
  apply (subst to_bl_mask, simp)
  apply (subst bl_shiftr, simp add: word_size)
  apply (subst to_bl_n1, simp add: word_size)
  done

lemma is_aligned_mask_out_add_eq:
  "is_aligned p n
    \<Longrightarrow> (p + x) && ~~ mask n = p + (x && ~~ mask n)"
  by (simp add: mask_out_sub_mask mask_add_aligned)

lemmas is_aligned_mask_out_add_eq_sub
    = is_aligned_mask_out_add_eq[where x="a - b" for a b, simplified field_simps]

lemma aligned_bump_down:
  "is_aligned x n
    \<Longrightarrow> (x - 1) && ~~ mask n = x - 2 ^ n"
  apply (frule is_aligned_mask_out_add_eq[where x="-1"])
  apply (simp add: NOT_mask)
  done

lemma base_length_minus_one_inequality:
  assumes foo: "wbase \<le> 2 ^ sz - 1"
    "1 \<le> (wlength :: ('a :: len) word)"
    "wlength \<le> 2 ^ sz - wbase"
    "sz < LENGTH ('a)"
  shows "wbase \<le> wbase + wlength - 1"
proof -

  note sz_less = power_strict_increasing[OF foo(4), where a=2]

  from foo have plus: "unat wbase + unat wlength < 2 ^ LENGTH('a)"
    apply -
    apply (rule order_le_less_trans[rotated], rule sz_less, simp)
    apply (simp add: unat_arith_simps split: if_split_asm)
    done

  from foo show ?thesis
   by (simp add: unat_arith_simps plus)
qed

lemma unat_2tp_if:
  "unat (2 ^ n :: ('a :: len) word) = (if n < LENGTH ('a) then 2 ^ n else 0)"
  by (split if_split, simp_all add: power_overflow)

lemma mask_of_mask:
  "mask (n::nat) && mask (m::nat) = mask (min m n)"
  apply (rule word_eqI)
  apply (auto simp:word_size)
  done

lemma unat_signed_ucast_less_ucast:
  "LENGTH('a) \<le> LENGTH('b)
   \<Longrightarrow> unat (ucast (x :: 'a :: len word) :: 'b :: len signed word) = unat x"
  by (simp add: unat_ucast_up_simp)

lemma toEnum_of_ucast:
  "LENGTH('b) \<le> LENGTH('a)
   \<Longrightarrow> (toEnum (unat (b::('b :: len word))):: ('a :: len word)) = of_nat (unat b)"
  apply (subst toEnum_of_nat)
   apply (rule less_le_trans[OF unat_lt2p])
   apply (simp add:power2_nat_le_eq_le)
  apply simp
  done

lemmas unat_ucast_mask = unat_ucast_eq_unat_and_mask[where w=a for a]

lemma length_upto_enum_cases:
  fixes a :: word32
  shows "length [a .e. b] = (if a \<le> b then Suc (unat b) - unat a else 0)"
  apply (case_tac "a \<le> b")
   apply (clarsimp)
  apply (clarsimp simp: upto_enum_def)
  apply unat_arith
  done

lemmas from_bool_to_bool_and_1 = from_to_bool_last_bit[where x=r for r]

lemma t2n_mask_eq_if:
  "(2 ^ n && mask m) = (if n < m then 2 ^ n else 0)"
  by (rule word_eqI, auto simp add: word_size nth_w2p split: if_split)

lemma unat_ucast_le:
  "unat (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> unat x"
  by (simp add: ucast_nat_def unat_le_helper)

lemma ucast_le_up_down_iff:
  "\<lbrakk> LENGTH('a) \<le> LENGTH('b);
     (x :: 'b :: len word) \<le> ucast (max_word :: 'a :: len word) \<rbrakk>
   \<Longrightarrow> (ucast x \<le> (y :: 'a word)) = (x \<le> ucast y)"
  using le_max_word_ucast_id ucast_le_ucast by metis

lemmas max_word_neq_0 = max_word_not_0

lemma ucast_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> ucast (ucast (p && mask a >> b) :: 'a :: len word) = p && mask a >> b"
  by (metis add.commute le_mask_iff shiftr_mask_le ucast_ucast_eq_mask_shift word_and_le')

lemma unat_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> unat (ucast (p && mask a >> b) :: 'a :: len word) = unat (p && mask a >> b)"
  by (metis linear ucast_ucast_mask_shift unat_ucast_up_simp)

lemma mask_overlap_zero:
  "a \<le> b \<Longrightarrow> (p && mask a) && ~~ mask b = 0"
  by (metis NOT_mask_AND_mask mask_lower_twice2 max_def)

lemma mask_shifl_overlap_zero:
  "a + c \<le> b \<Longrightarrow> (p && mask a << c) && ~~ mask b = 0"
  by (metis and_not_mask le_mask_iff mask_shiftl_decompose shiftl_0 shiftl_over_and_dist
            shiftr_mask_le word_and_le' word_bool_alg.conj_commute)

lemma mask_overlap_zero':
  "a \<ge> b \<Longrightarrow> (p && ~~ mask a) && mask b = 0"
  using mask_AND_NOT_mask mask_AND_less_0 by blast

lemma mask_rshift_mult_eq_rshift_lshift:
  "((a :: 'a :: len word) >> b) * (1 << c) = (a >> b << c)"
  by (simp add: shiftl_t2n)

lemma shift_alignment:
  "a \<ge> b \<Longrightarrow> is_aligned (p >> a << a) b"
  using is_aligned_shift is_aligned_weaken by blast

lemma mask_split_sum_twice:
  "a \<ge> b \<Longrightarrow> (p && ~~ mask a) + ((p && mask a) && ~~ mask b) + (p && mask b) = p"
  by (simp add: add.commute multiple_mask_trivia word_bool_alg.conj_commute
                word_bool_alg.conj_left_commute word_plus_and_or_coroll2)

lemma mask_shift_eq_mask_mask:
  "(p && mask a >> b << b) = (p && mask a) && ~~ mask b"
  by (simp add: and_not_mask)

lemma mask_shift_sum:
  "\<lbrakk> a \<ge> b; unat n = unat (p && mask b) \<rbrakk>
   \<Longrightarrow> (p && ~~ mask a) + (p && mask a >> b) * (1 << b) + n = (p :: 'a :: len word)"
  by (metis and_not_mask mask_rshift_mult_eq_rshift_lshift mask_split_sum_twice word_unat.Rep_eqD)

lemmas word_le_p2m1 = word_up_bound[where ptr=w for w]

lemma inj_ucast:
  "\<lbrakk> uc = ucast; is_up uc \<rbrakk>
   \<Longrightarrow> inj uc"
  using down_ucast_inj is_up_down by blast

lemma ucast_eq_0[OF refl]:
  "\<lbrakk> c = ucast; is_up c \<rbrakk>
   \<Longrightarrow> (c x = 0) = (x = 0)"
  by (metis uint_0_iff uint_up_ucast)

lemma is_up_compose':
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> is_up (uc' \<circ> uc)"
  unfolding is_up_def by (simp add: Word.target_size Word.source_size)

lemma is_up_compose:
  "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
   \<Longrightarrow> is_up (uc' \<circ> uc)"
  unfolding is_up_def by (simp add: Word.target_size Word.source_size)

lemma uint_is_up_compose:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast"
    and "uc' = ucast"
    and " uuc = uc' \<circ> uc"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> uint (uuc b) = uint b"
  apply (simp add: assms)
  apply (frule is_up_compose)
   apply (simp_all )
  apply (simp only: Word.uint_up_ucast)
  done

lemma uint_is_up_compose_pred:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast" and "uc' = ucast" and " uuc = uc' \<circ> uc"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> P (uint (uuc b)) \<longleftrightarrow> P( uint b)"
  apply (simp add: assms)
  apply (frule is_up_compose)
   apply (simp_all )
  apply (simp only: Word.uint_up_ucast)
 done

lemma is_down_up_sword:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len sword"
  shows "\<lbrakk> uc = ucast; LENGTH('a) < LENGTH('b) \<rbrakk>
         \<Longrightarrow> is_up uc = (\<not> is_down uc)"
  by (simp add: target_size source_size  is_up_def is_down_def )

lemma is_not_down_compose:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  shows "\<lbrakk> uc = ucast; uc' = ucast; LENGTH('a) < LENGTH('c) \<rbrakk>
         \<Longrightarrow> \<not> is_down (uc' \<circ> uc)"
  unfolding is_down_def
  by (simp add: Word.target_size Word.source_size)

lemma sint_ucast_uint:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast" and " uc' = ucast" and "uuc=uc' \<circ> uc "
    and "LENGTH('a) < LENGTH('c signed)"
  shows "\<lbrakk> is_up uc; is_up uc'\<rbrakk>
         \<Longrightarrow> sint (uuc b) = uint b"
  apply (simp add: assms)
  apply (frule is_up_compose')
   apply simp_all
  apply (simp add: ucast_ucast_b)
  apply (rule sint_ucast_eq_uint)
  apply (insert assms)
  apply (simp add: is_down_def target_size source_size)
  done

lemma sint_ucast_uint_pred:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
    and uuc :: "'a word \<Rightarrow> 'c sword"
  assumes "uc = ucast" and " uc' = ucast" and "uuc=uc' \<circ> uc "
    and "LENGTH('a) < LENGTH('c )"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> P (uint b) \<longleftrightarrow> P (sint (uuc b))"
  apply (simp add: assms )
  apply (insert sint_ucast_uint[where uc=uc and uc'=uc' and uuc=uuc and b = b])
  apply (simp add: assms)
 done

lemma sint_uucast_uint_uucast_pred:
  fixes uc :: "'a :: len word \<Rightarrow> 'b :: len word"
    and uc' :: "'b word \<Rightarrow> 'c :: len sword"
  assumes "uc = ucast" and " uc' = ucast" and "uuc=uc' \<circ> uc "
    and "LENGTH('a) < LENGTH('c )"
  shows "\<lbrakk> is_up uc; is_up uc' \<rbrakk>
         \<Longrightarrow> P (uint(uuc b)) \<longleftrightarrow> P (sint (uuc b))"
  apply (simp add: assms )
  apply (insert sint_ucast_uint[where uc=uc and uc'=uc' and uuc=uuc and b = b])
  apply (insert uint_is_up_compose_pred[where uc=uc and uc'=uc' and uuc=uuc and b=b])
  apply (simp add: assms uint_is_up_compose_pred)
 done

lemma unat_minus':
  fixes x :: "'a :: len word"
  shows "x \<noteq> 0 \<Longrightarrow> unat (-x) = 2 ^ LENGTH('a) - unat x"
  apply (simp add: unat_def word_minus_def)
  apply (simp add: int_word_uint zmod_zminus1_eq_if uint_0_iff)
  apply (subst nat_diff_distrib)
    apply simp
   apply (rule order_less_imp_le [OF uint_lt2p])
   apply (clarsimp simp: nat_power_eq)
   done

lemma word_nth_neq:
  "n < LENGTH('a) \<Longrightarrow> (~~ x :: 'a :: len word) !! n = (\<not> x !! n)"
  by (simp add: word_size word_ops_nth_size)

lemma word_wrap_of_natD:
  fixes x :: "'a :: len word"
  assumes wraps: "\<not> x \<le> x + of_nat n"
  shows   "\<exists>k. x + of_nat k = 0 \<and> k \<le> n"
proof -
  show ?thesis
  proof (rule exI [where x = "unat (- x)"], intro conjI)
    show "x + of_nat (unat (-x)) = 0"
      by simp
  next
    show "unat (-x) \<le> n"
    proof (subst unat_minus')
      from wraps show "x \<noteq> 0"
        by (rule contrapos_pn, simp add: not_le)
    next
      show "2 ^ LENGTH('a) - unat x \<le> n" using wraps
        apply (simp add: no_olen_add_nat le_diff_conv not_less)
        apply (erule order_trans)
        apply (simp add: unat_of_nat)
        done
    qed
  qed
qed

lemma of_int_sint_scast:
  "of_int (sint (x :: 'a :: len word)) = (scast x :: 'b :: len word)"
  by (metis scast_def word_of_int)

lemma scast_of_nat_to_signed [simp]:
  "scast (of_nat x :: 'a :: len word) = (of_nat x :: 'a signed word)"
  by (metis cast_simps(23) scast_scast_id(2))

lemma scast_of_nat_signed_to_unsigned_add:
  "(scast ((of_nat x) + (of_nat y) :: 'a :: len signed word))
    = ((of_nat x) + (of_nat y) :: 'a :: len word)"
  by (metis of_nat_add scast_of_nat)

lemma scast_of_nat_unsigned_to_signed_add:
  "(scast ((of_nat x) + (of_nat y) :: 'a :: len word))
    = ((of_nat x) + (of_nat y) :: 'a :: len signed word)"
  by (metis Abs_fnat_hom_add scast_of_nat_to_signed)

lemma and_mask_cases:
  fixes x :: "'a :: len word"
  assumes len: "n < LENGTH('a)"
  shows "x && mask n \<in> of_nat ` set [0 ..< 2 ^ n]"
proof -
  have "x && mask n \<in> {0 .. 2 ^ n - 1}"
    by (simp add: mask_def word_and_le1)
  also
  have "... = of_nat ` {0 .. 2 ^ n - 1}"
    apply (rule set_eqI, rule iffI)
     apply (clarsimp simp: image_iff)
     apply (rule_tac x="unat x" in bexI; simp)
      using len
      apply (simp add: word_le_nat_alt unat_2tp_if unat_minus_one)
    using len
    apply (clarsimp simp: word_le_nat_alt unat_2tp_if unat_minus_one)
    apply (subst unat_of_nat_eq; simp add: nat_le_Suc_less)
    apply (erule less_le_trans)
    apply simp
    done
  also have "{0::nat .. 2^n - 1} = set [0 ..< 2^n]" by (auto simp: nat_le_Suc_less)
  finally show ?thesis .
qed

lemma two_bits_cases:
  "\<lbrakk> LENGTH('a) > 2; (x :: 'a :: len word) && 3 = 0 \<Longrightarrow> P; x && 3 = 1 \<Longrightarrow> P;
     x && 3 = 2 \<Longrightarrow> P; x && 3 = 3 \<Longrightarrow> P \<rbrakk>
   \<Longrightarrow> P"
  apply (frule and_mask_cases[where n=2 and x=x, simplified mask_def])
  using upt_conv_Cons by auto[1]

lemma sint_of_nat_ge_zero:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (of_nat x :: 'a :: len word) \<ge> 0"
  by (simp add: Word_Lemmas.of_nat_power not_msb_from_less sint_eq_uint)

lemma sint_of_nat_le:
  "\<lbrakk> b < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk>
   \<Longrightarrow> sint (of_nat a :: 'a :: len word) \<le> sint (of_nat b :: 'a :: len word)"
  apply (subst sint_eq_uint) defer
   apply (subst sint_eq_uint) defer
    apply (meson le_less_trans nat_power_minus_less of_nat_mono_maybe_le word_le_def)
   apply (simp add: Word_Lemmas.of_nat_power not_msb_from_less)+
  done

lemma int_eq_sint:
  "\<lbrakk> x < 2 ^ (LENGTH('a) - 1) \<rbrakk>
   \<Longrightarrow> sint (of_nat x :: 'a :: len word) = int x"
  apply (subst sint_eq_uint)
   apply (simp add: Word_Lemmas.of_nat_power not_msb_from_less)
  by (metis int_unat nat_power_minus_less unat_of_nat_eq)

lemma sint_ctz:
  "LENGTH('a) > 2
   \<Longrightarrow> 0 \<le> sint (of_nat (word_ctz (x :: 'a :: len word)) :: 'a signed word)
        \<and> sint (of_nat (word_ctz x) :: 'a signed word) \<le> LENGTH('a)"
  apply (subgoal_tac "LENGTH('a) < 2 ^ (LENGTH('a) - 1)")
  apply (rule conjI)
   apply (metis len_signed order_le_less_trans sint_of_nat_ge_zero word_ctz_le)
   apply (metis int_eq_sint len_signed sint_of_nat_le word_ctz_le)
  by (rule small_powers_of_2, simp)

lemma pow_sub_less:
  "\<lbrakk> a + b \<le> LENGTH('a);  unat (x :: 'a :: len word) = 2 ^ a \<rbrakk>
   \<Longrightarrow> unat (x * 2 ^ b - 1) < 2 ^ (a + b)"
  by (metis (mono_tags, lifting)
            eq_or_less_helperD not_less of_nat_numeral power_add semiring_1_class.of_nat_power
            unat_pow_le_intro word_unat.Rep_inverse)

lemma sle_le_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk>
   \<Longrightarrow> word_sle a b"
  by (simp add: not_msb_from_less word_sle_msb_le)

lemma sless_less_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a < b \<rbrakk>
   \<Longrightarrow> word_sless a b"
  using not_msb_from_less word_sless_msb_less by blast

lemma mask_1_eq_1:
  "mask 1 = 1"
  unfolding mask_def by simp

lemma and_mask2: "w << n >> n = w && mask (size w - n)"
  apply (case_tac "n \<le> size w")
   apply (clarsimp simp: word_and_le2 and_mask shiftl_zero_size)+
  done

lemma zero_OR_eq:
  "y = 0 \<Longrightarrow> (x || y) = x"
  by simp

lemma unat_of_nat_word_log2:
  "LENGTH('a) < 2 ^ LENGTH('b)
   \<Longrightarrow> unat (of_nat (word_log2 (n :: 'a :: len word)) :: 'b :: len word) = word_log2 n"
  apply (subst unat_of_nat_eq)
   apply (rule word_log2_max[THEN less_trans])
   apply (simp add: word_size)
  apply simp
  done

lemma aligned_sub_aligned_simple:
  "\<lbrakk> is_aligned a n; is_aligned b n \<rbrakk>
   \<Longrightarrow> is_aligned (a - b) n"
  by (simp add: Aligned.aligned_sub_aligned)

declare is_aligned_neg_mask_eq[simp]
declare is_aligned_neg_mask_weaken[simp]

lemma minus_one_shift:
  "- (1 << n) = (-1 << n :: 'a::len word)"
  by (simp add: mul_not_mask_eq_neg_shiftl[symmetric] mask_def NOT_eq)

lemma ucast_eq_mask:
  "(UCAST('a::len \<rightarrow> 'b::len) x = UCAST('a \<rightarrow> 'b) y) =
   (x && mask LENGTH('b) = y && mask LENGTH('b))"
  apply (cases "LENGTH('b) < LENGTH('a)")
   apply (auto simp: nth_ucast word_size intro!: word_eqI dest: word_eqD)[1]
  apply (auto simp: shiftr_eq_0 and_mask_eq_iff_shiftr_0[THEN iffD2] dest: ucast_up_inj)
  done

context
  fixes w :: "'a::len word"
begin

private lemma sbintrunc_uint_ucast:
  assumes "Suc n = len_of TYPE('b::len)"
  shows "sbintrunc n (uint (ucast w :: 'b word)) = sbintrunc n (uint w)"
  by (metis assms sbintrunc_bintrunc ucast_def word_ubin.eq_norm)

private lemma test_bit_sbintrunc:
  assumes "i < len_of TYPE('a)"
  shows "(word_of_int (sbintrunc n (uint w)) :: 'a word) !! i
           = (if n < i then w !! n else w !! i)"
  using assms by (simp add: nth_sbintr)
                 (simp add: test_bit_bin)

private lemma test_bit_sbintrunc_ucast:
  assumes len_a: "i < len_of TYPE('a)"
  shows "(word_of_int (sbintrunc (len_of TYPE('b) - 1) (uint (ucast w :: 'b word))) :: 'a word) !! i
          = (if len_of TYPE('b::len) \<le> i then w !! (len_of TYPE('b) - 1) else w !! i)"
  apply (subst sbintrunc_uint_ucast)
   apply simp
  apply (subst test_bit_sbintrunc)
   apply (rule len_a)
  apply (rule if_cong[OF _ refl refl])
  using leD less_linear by fastforce

lemma scast_ucast_high_bits:
  shows "scast (ucast w :: 'b::len word) = w
           \<longleftrightarrow> (\<forall> i \<in> {len_of TYPE('b) ..< size w}. w !! i = w !! (len_of TYPE('b) - 1))"
  unfolding scast_def sint_uint word_size
  apply (subst word_eq_iff)
  apply (rule iffI)
   apply (rule ballI)
   apply (drule_tac x=i in spec)
   apply (subst (asm) test_bit_sbintrunc_ucast; simp)
  apply (rule allI)
  apply (case_tac "n < len_of TYPE('a)")
   apply (subst test_bit_sbintrunc_ucast)
    apply simp
   apply (case_tac "n \<ge> len_of TYPE('b)")
    apply (drule_tac x=n in bspec)
     by auto

lemma scast_ucast_mask_compare:
  shows "scast (ucast w :: 'b::len word) = w
          \<longleftrightarrow> (w \<le> mask (len_of TYPE('b) - 1) \<or> ~~ mask (len_of TYPE('b) - 1) \<le> w)"
  apply (clarsimp simp: le_mask_high_bits neg_mask_le_high_bits scast_ucast_high_bits word_size)
  apply (rule iffI; clarsimp)
  apply (rename_tac i j; case_tac "i = len_of TYPE('b) - 1"; case_tac "j = len_of TYPE('b) - 1")
  by auto

end

end
