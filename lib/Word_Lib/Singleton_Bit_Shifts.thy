theory Singleton_Bit_Shifts
  imports
    "HOL-Library.Word"
    Bit_Shifts_Infix_Syntax
begin

definition shiftl1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>shiftl1 = push_bit 1\<close>

lemma bit_shiftl1_iff [bit_simps]:
  \<open>bit (shiftl1 w) n \<longleftrightarrow> 0 < n \<and> n < LENGTH('a) \<and> bit w (n - 1)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp only: shiftl1_def bit_push_bit_iff) auto

definition shiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>shiftr1 = drop_bit 1\<close>

lemma bit_shiftr1_iff [bit_simps]:
  \<open>bit (shiftr1 w) n \<longleftrightarrow> bit w (Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftr1_def bit_drop_bit_eq)

definition sshiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>sshiftr1 \<equiv> signed_drop_bit 1\<close>

lemma bit_sshiftr1_iff [bit_simps]:
  \<open>bit (sshiftr1 w) n \<longleftrightarrow> bit w (if n = LENGTH('a) - 1 then LENGTH('a) - 1 else Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: sshiftr1_def bit_signed_drop_bit_iff)

lemma shiftr1_1: "shiftr1 (1::'a::len word) = 0"
  by (simp add: shiftr1_def)

lemma sshiftr1_eq:
  \<open>sshiftr1 w = word_of_int (sint w div 2)\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps min_def simp flip: bit_Suc elim: le_SucE)

lemma shiftl1_eq:
  \<open>shiftl1 w = word_of_int (2 * uint w)\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma shiftr1_eq:
  \<open>shiftr1 w = word_of_int (uint w div 2)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps flip: bit_Suc)

lemma shiftl1_rev:
  "shiftl1 w = word_reverse (shiftr1 (word_reverse w))"
  by (rule bit_word_eqI) (auto simp add: bit_simps Suc_diff_Suc simp flip: bit_Suc)

lemma shiftl1_p:
  "shiftl1 w = w + w"
  for w :: "'a::len word"
  by (simp add: shiftl1_def)

lemma shiftr1_bintr:
  "(shiftr1 (numeral w) :: 'a::len word) =
    word_of_int (take_bit LENGTH('a) (numeral w) div 2)"
  by (rule bit_word_eqI) (simp add: bit_simps bit_numeral_iff [where ?'a = int] flip: bit_Suc)

lemma sshiftr1_sbintr:
  "(sshiftr1 (numeral w) :: 'a::len word) =
    word_of_int (signed_take_bit (LENGTH('a) - 1) (numeral w) div 2)"
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp_all
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps min_def simp flip: bit_Suc elim: le_SucE)
  done

lemma shiftl1_wi:
  "shiftl1 (word_of_int w) = word_of_int (2 * w)"
  by (rule bit_word_eqI) (auto simp add: bit_simps)

lemma shiftl1_numeral:
  "shiftl1 (numeral w) = numeral (Num.Bit0 w)"
  unfolding word_numeral_alt shiftl1_wi by simp

lemma shiftl1_neg_numeral:
  "shiftl1 (- numeral w) = - numeral (Num.Bit0 w)"
  unfolding word_neg_numeral_alt shiftl1_wi by simp

lemma shiftl1_0:
  "shiftl1 0 = 0"
  by (simp add: shiftl1_def)

lemma shiftl1_def_u:
  "shiftl1 w = word_of_int (2 * uint w)"
  by (fact shiftl1_eq)

lemma shiftl1_def_s:
  "shiftl1 w = word_of_int (2 * sint w)"
  by (simp add: shiftl1_def)

lemma shiftr1_0:
  "shiftr1 0 = 0"
  by (simp add: shiftr1_def)

lemma sshiftr1_0:
  "sshiftr1 0 = 0"
  by (simp add: sshiftr1_def)

lemma sshiftr1_n1:
  "sshiftr1 (- 1) = - 1"
  by (simp add: sshiftr1_def)

lemma uint_shiftr1:
  "uint (shiftr1 w) = uint w div 2"
  by (rule bit_eqI) (simp add: bit_simps flip: bit_Suc)

lemma shiftr1_div_2:
  "uint (shiftr1 w) = uint w div 2"
  by (fact uint_shiftr1)

lemma sshiftr1_div_2:
  "sint (sshiftr1 w) = sint w div 2"
  by (rule bit_eqI) (auto simp add: bit_simps ac_simps min_def simp flip: bit_Suc elim: le_SucE)

lemma nth_shiftl1:
  "bit (shiftl1 w) n \<longleftrightarrow> n < size w \<and> n > 0 \<and> bit w (n - 1)"
  by (auto simp add: word_size bit_simps)

lemma nth_shiftr1:
  "bit (shiftr1 w) n = bit w (Suc n)"
  by (fact bit_shiftr1_iff)

lemma nth_sshiftr1: "bit (sshiftr1 w) n = (if n = size w - 1 then bit w n else bit w (Suc n))"
  by (auto simp add: word_size bit_simps)

lemma shiftl_power:
  "(shiftl1 ^^ x) (y::'a::len word) = 2 ^ x * y"
  by (induction x) (simp_all add: shiftl1_def)

lemma le_shiftr1:
  \<open>shiftr1 u \<le> shiftr1 v\<close> if \<open>u \<le> v\<close>
  using that by (simp add: word_le_nat_alt unat_div div_le_mono shiftr1_def drop_bit_Suc)

lemma le_shiftr1':
  "\<lbrakk> shiftr1 u \<le> shiftr1 v ; shiftr1 u \<noteq> shiftr1 v \<rbrakk> \<Longrightarrow> u \<le> v"
  by (meson dual_order.antisym le_cases le_shiftr1)

lemma sshiftr_eq_funpow_sshiftr1:
  \<open>w >>> n = (sshiftr1 ^^ n) w\<close>
  apply (rule sym)
  apply (simp add: sshiftr1_def sshiftr_def)
  apply (induction n)
   apply simp_all
  done

end
