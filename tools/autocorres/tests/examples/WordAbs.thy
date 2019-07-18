(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WordAbs
imports "AutoCorres.AutoCorres"
begin

external_file "word_abs.c"
install_C_file "word_abs.c"
autocorres
  [ (*signed_word_abs =
        S_and_S S_or_S S_xor_S not_S
        U_shiftl_U_abs_S U_shiftr_U_abs_S U_shiftl_S_abs_S U_shiftr_S_abs_S
        S_shiftl_U_abs_S S_shiftr_U_abs_S S_shiftl_S_abs_S S_shiftr_S_abs_S
        U_shiftl_U_abs_US U_shiftr_U_abs_US U_shiftl_S_abs_US U_shiftr_S_abs_US
        S_shiftl_U_abs_US S_shiftr_U_abs_US S_shiftl_S_abs_US S_shiftr_S_abs_US
  ,*) no_signed_word_abs =
        U_shiftl_U_no_abs U_shiftr_U_no_abs U_shiftl_S_no_abs U_shiftr_S_no_abs
        S_shiftl_U_no_abs S_shiftr_U_no_abs S_shiftl_S_no_abs S_shiftr_S_no_abs
        U_shiftl_U_abs_U U_shiftr_U_abs_U U_shiftl_S_abs_U U_shiftr_S_abs_U
        S_shiftl_U_abs_U S_shiftr_U_abs_U S_shiftl_S_abs_U S_shiftr_S_abs_U
  , unsigned_word_abs =
        ver366
        U_and_U U_or_U U_xor_U not_U
        U_shiftl_U_abs_U U_shiftr_U_abs_U U_shiftl_S_abs_U U_shiftr_S_abs_U
        S_shiftl_U_abs_U S_shiftr_U_abs_U S_shiftl_S_abs_U S_shiftr_S_abs_U
        U_shiftl_U_abs_US U_shiftr_U_abs_US U_shiftl_S_abs_US U_shiftr_S_abs_US
        S_shiftl_U_abs_US S_shiftr_U_abs_US S_shiftl_S_abs_US S_shiftr_S_abs_US
  , ts_rules = nondet
] "word_abs.c"

context word_abs begin

lemma "\<lbrace> P \<rbrace> ver366' 0 \<lbrace> \<lambda>v s. v = 0 \<and> P s \<rbrace>"
  by (wpsimp simp: ver366'_def)
lemma "\<lbrace> P \<rbrace> ver366' UINT_MAX \<lbrace> \<lambda>v s. v = UINT_MAX-1 \<and> P s \<rbrace>"
  by (wpsimp simp: ver366'_def UINT_MAX_def)

section \<open>Bitwise ops\<close>

thm S_and_S'_def S_or_S'_def S_xor_S'_def not_S'_def
    U_and_U'_def U_or_U'_def U_xor_U'_def not_U'_def
lemma "\<lbrace>P\<rbrace> S_and_S' (x::int) (y::int) \<lbrace>\<lambda>r s. r = x AND y \<and> P s\<rbrace>!"
  by (wpsimp simp: S_and_S'_def)
lemma "\<lbrace>P\<rbrace> S_or_S' (x::int) (y::int) \<lbrace>\<lambda>r s. r = x OR y \<and> P s\<rbrace>!"
  by (wpsimp simp: S_or_S'_def)
lemma "\<lbrace>P\<rbrace> S_xor_S' (x::int) (y::int) \<lbrace>\<lambda>r s. r = x XOR y \<and> P s\<rbrace>!"
  by (wpsimp simp: S_xor_S'_def)
lemma "\<lbrace>P\<rbrace> not_S' (x::int) \<lbrace>\<lambda>r s. r = NOT x \<and> P s\<rbrace>!"
  by (wpsimp simp: not_S'_def)
lemma "\<lbrace>P\<rbrace> U_and_U' (x::nat) (y::nat) \<lbrace>\<lambda>r s. r = x AND y \<and> P s\<rbrace>!"
  by (wpsimp simp: U_and_U'_def)
lemma "\<lbrace>P\<rbrace> U_or_U' (x::nat) (y::nat) \<lbrace>\<lambda>r s. r = x OR y \<and> P s\<rbrace>!"
  by (wpsimp simp: U_or_U'_def)
lemma "\<lbrace>P\<rbrace> U_xor_U' (x::nat) (y::nat) \<lbrace>\<lambda>r s. r = x XOR y \<and> P s\<rbrace>!"
  by (wpsimp simp: U_xor_U'_def)
lemma "\<lbrace>P\<rbrace> not_U' (x::nat) \<lbrace>\<lambda>r s. r = UINT_MAX - x \<and> P s\<rbrace>!"
  by (wpsimp simp: not_U'_def)

section \<open>Left shifts\<close>

thm U_shiftl_U_abs_US'_def U_shiftr_U_abs_US'_def U_shiftl_S_abs_US'_def U_shiftr_S_abs_US'_def
    S_shiftl_U_abs_US'_def S_shiftr_U_abs_US'_def S_shiftl_S_abs_US'_def S_shiftr_S_abs_US'_def
thm U_shiftl_U_abs_U'_def U_shiftr_U_abs_U'_def U_shiftl_S_abs_U'_def U_shiftr_S_abs_U'_def
    S_shiftl_U_abs_U'_def S_shiftr_U_abs_U'_def S_shiftl_S_abs_U'_def S_shiftr_S_abs_U'_def
thm U_shiftl_U_abs_S'_def U_shiftr_U_abs_S'_def U_shiftl_S_abs_S'_def U_shiftr_S_abs_S'_def
    S_shiftl_U_abs_S'_def S_shiftr_U_abs_S'_def S_shiftl_S_abs_S'_def S_shiftr_S_abs_S'_def
thm U_shiftl_U_no_abs'_def U_shiftr_U_no_abs'_def U_shiftl_S_no_abs'_def U_shiftr_S_no_abs'_def
    S_shiftl_U_no_abs'_def S_shiftr_U_no_abs'_def S_shiftl_S_no_abs'_def S_shiftr_S_no_abs'_def

subsection \<open>@{text U_shiftl_U}\<close>

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_U_abs_US' (x :: nat) (n :: nat))"
  by (monad_eq simp: U_shiftl_U_abs_US'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> x << n \<le> UINT_MAX\<rbrace>
         U_shiftl_U_abs_US' (x::nat) (n::nat)
       \<lbrace>\<lambda>r s. r = x << n\<rbrace>!"
  by (wpsimp simp: U_shiftl_U_abs_US'_def UINT_MAX_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_U_abs_U' (x :: nat) (n :: nat))"
  by (monad_eq simp: U_shiftl_U_abs_U'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> x << n \<le> UINT_MAX\<rbrace>
         U_shiftl_U_abs_U' (x::nat) (n::nat)
       \<lbrace>\<lambda>r s. r = x << n\<rbrace>!"
  by (wpsimp simp: U_shiftl_U_abs_U'_def UINT_MAX_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_U_abs_S' (x :: word32) (n :: word32))"
  by (monad_eq simp: U_shiftl_U_abs_S'_def no_fail_def word_le_not_less)
lemma "\<lbrace>\<lambda>s. n < 32\<rbrace>
         U_shiftl_U_abs_S' (x::word32) (n::word32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  by (wpsimp simp: U_shiftl_U_abs_S'_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_U_no_abs' (x :: word32) (n :: word32))"
  by (monad_eq simp: U_shiftl_U_no_abs'_def no_fail_def word_le_not_less)
lemma "\<lbrace>\<lambda>s. n < 32\<rbrace>
         U_shiftl_U_no_abs' (x::word32) (n::word32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  by (wpsimp simp: U_shiftl_U_no_abs'_def)

subsection \<open>@{text U_shiftl_S}\<close>

lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_US' (x :: nat) (n :: int))"
  by (monad_eq simp: U_shiftl_S_abs_US'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_US' (x :: nat) (n :: int))"
  by (monad_eq simp: U_shiftl_S_abs_US'_def no_fail_def)
lemma "x << nat n > UINT_MAX \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_US' (x :: nat) (n :: int))"
  by (monad_eq simp: U_shiftl_S_abs_US'_def no_fail_def UINT_MAX_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32 \<and> x << nat n \<le> UINT_MAX\<rbrace>
         U_shiftl_S_abs_US' (x::nat) (n::int)
       \<lbrace>\<lambda>r s. r = x << nat n\<rbrace>!"
  by (wpsimp simp: U_shiftl_S_abs_US'_def UINT_MAX_def)

lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_U' (x :: nat) (n :: sword32))"
  by (monad_eq simp: U_shiftl_S_abs_U'_def no_fail_def word_sless_alt word_sle_def)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_U' (x :: nat) (n :: sword32))"
  by (monad_eq simp: U_shiftl_S_abs_U'_def no_fail_def word_sless_alt word_sle_def)
lemma "x << unat n > UINT_MAX \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_U' (x :: nat) (n :: sword32))"
  by (monad_eq simp: U_shiftl_S_abs_U'_def no_fail_def
                     word_sless_alt word_sle_def nat_sint UINT_MAX_def)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32 \<and> x << unat n \<le> UINT_MAX\<rbrace>
         U_shiftl_S_abs_U' (x::nat) (n::sword32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  by (wpsimp simp: U_shiftl_S_abs_U'_def UINT_MAX_def nat_sint word_sle_def word_sless_alt)

lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_S' (x :: word32) (n :: int))"
  by (monad_eq simp: U_shiftl_S_abs_S'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_abs_S' (x :: word32) (n :: int))"
  by (monad_eq simp: U_shiftl_S_abs_S'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32\<rbrace>
         U_shiftl_S_abs_S' (x::word32) (n::int)
       \<lbrace>\<lambda>r s. r = x << nat n\<rbrace>!"
  by (wpsimp simp: U_shiftl_S_abs_S'_def UINT_MAX_def unat_of_int)

lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_no_abs' (x :: word32) (n :: sword32))"
  by (monad_eq simp: U_shiftl_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (U_shiftl_S_no_abs' (x :: word32) (n :: sword32))"
  by (monad_eq simp: U_shiftl_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32\<rbrace>
         U_shiftl_S_no_abs' (x :: word32) (n :: sword32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  by (wpsimp simp: U_shiftl_S_no_abs'_def UINT_MAX_def)

subsection \<open>@{text S_shiftl_U}\<close>

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_US' (x :: int) (n :: nat))"
  by (monad_eq simp: S_shiftl_U_abs_US'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_US' (x :: int) (n :: nat))"
  by (monad_eq simp: S_shiftl_U_abs_US'_def no_fail_def)
lemma "x << nat n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_US' (x :: int) (n :: nat))"
  by (monad_eq simp: S_shiftl_U_abs_US'_def no_fail_def INT_MAX_def)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 \<le> x \<and> x << nat n \<le> INT_MAX\<rbrace>
         S_shiftl_U_abs_US' (x::int) (n::nat)
       \<lbrace>\<lambda>r s. r = x << nat n\<rbrace>!"
  apply (wpsimp simp: S_shiftl_U_abs_US'_def INT_MAX_def shiftl_nat_def shiftl_int_def)
  apply (subst unat_of_int)
    apply simp
   apply (drule le_less_trans[where x="x*2^n" and z="2^32"])
    apply simp
   apply (subst mult_less_cancel_left_pos[where c="2^n", symmetric])
    apply simp
   apply (subst (asm) mult.commute)
   apply (erule less_le_trans)
   apply simp
  apply (simp flip: nat_mult_distrib nat_power_eq nat_numeral)
  done

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_U' (x :: sword32) (n :: nat))"
  by (monad_eq simp: S_shiftl_U_abs_U'_def no_fail_def word_sle_def word_sless_alt)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_U' (x :: sword32) (n :: nat))"
  apply (monad_eq simp: S_shiftl_U_abs_U'_def no_fail_def)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>
lemma "sint x << n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_U' (x :: sword32) (n :: nat))"
  by (monad_eq simp: S_shiftl_U_abs_U'_def no_fail_def shiftl_int_def INT_MAX_def
                     nat_int_comparison(2) int_unat_nonneg)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 <=s x \<and> sint x << nat n \<le> INT_MAX\<rbrace>
         S_shiftl_U_abs_U' (x::sword32) (n::nat)
       \<lbrace>\<lambda>r s. r = x << nat n\<rbrace>!"
  by (wpsimp simp: S_shiftl_U_abs_U'_def INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) int_unat_nonneg)

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_S' (x :: int) (n :: word32))"
  by (monad_eq simp: S_shiftl_U_abs_S'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_S' (x :: int) (n :: word32))"
  by (monad_eq simp: S_shiftl_U_abs_S'_def no_fail_def word_le_nat_alt)
lemma "x << unat n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_abs_S' (x :: int) (n :: word32))"
  by (monad_eq simp: S_shiftl_U_abs_S'_def no_fail_def INT_MAX_def)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 \<le> x \<and> x << unat n \<le> INT_MAX\<rbrace>
         S_shiftl_U_abs_S' (x::int) (n::word32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  apply (wpsimp simp: S_shiftl_U_abs_S'_def INT_MAX_def shiftl_nat_def shiftl_int_def
                      word_less_nat_alt)
  apply (subst unat_of_int)
    apply simp
   apply (drule le_less_trans[where x="x*2^unat n" and z="2^32"])
    apply simp
   apply simp
   apply (subst mult_less_cancel_left_pos[where c="2^unat n", symmetric])
    apply simp
   apply (subst (asm) mult.commute)
   apply (erule less_le_trans)
   apply simp
  apply (simp flip: nat_mult_distrib nat_power_eq nat_numeral)
  done

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_no_abs' (x :: sword32) (n :: word32))"
  by (monad_eq simp: S_shiftl_U_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_no_abs' (x :: sword32) (n :: word32))"
  apply (monad_eq simp: S_shiftl_U_no_abs'_def no_fail_def)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>
lemma "sint x << unat n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_U_no_abs' (x :: sword32) (n :: word32))"
  by (monad_eq simp: S_shiftl_U_no_abs'_def no_fail_def shiftl_int_def INT_MAX_def
                     nat_int_comparison(2) int_unat_nonneg)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 <=s x \<and> sint x << unat n \<le> INT_MAX\<rbrace>
         S_shiftl_U_no_abs' (x::sword32) (n::word32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  by (wpsimp simp: S_shiftl_U_no_abs'_def INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) int_unat_nonneg)

subsection \<open>@{text S_shiftl_S}\<close>

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_US' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_US'_def no_fail_def)
lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_US' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_US'_def no_fail_def)
lemma "x << nat n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_US' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_US'_def no_fail_def INT_MAX_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_US' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_US'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32 \<and> 0 \<le> x \<and> x << nat n \<le> INT_MAX\<rbrace>
         S_shiftl_S_abs_US' (x::int) (n::int)
       \<lbrace>\<lambda>r s. r = x << nat n\<rbrace>!"
  apply (wpsimp simp: S_shiftl_S_abs_US'_def INT_MAX_def shiftl_nat_def shiftl_int_def)
  apply (subst unat_of_int)
    apply simp
   apply simp
   apply (drule le_less_trans[where x="x*2^nat n" and z="2^32"])
    apply simp
   apply (subst mult_less_cancel_left_pos[where c="2^nat n", symmetric])
    apply simp
   apply (subst (asm) mult.commute)
   apply (erule less_le_trans)
   apply simp
  apply (subst unat_of_int)
    apply simp
   apply simp
  apply (simp flip: nat_mult_distrib nat_power_eq nat_numeral)
  done

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftl_S_abs_U'_def no_fail_def word_sle_def word_sless_alt)
lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftl_S_abs_U'_def no_fail_def word_sle_def word_sless_alt)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32))"
  apply (monad_eq simp: S_shiftl_S_abs_U'_def no_fail_def word_sle_def word_sless_alt)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>
lemma "sint x << unat n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftl_S_abs_U'_def no_fail_def shiftl_int_def INT_MAX_def
                     nat_int_comparison(2) int_unat_nonneg)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32 \<and> 0 <=s x \<and> sint x << unat n \<le> INT_MAX\<rbrace>
         S_shiftl_S_abs_U' (x::sword32) (n::sword32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  by (wpsimp simp: S_shiftl_S_abs_U'_def INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) int_unat_nonneg)

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_S' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_S'_def no_fail_def)
lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_S' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_S'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_S' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_S'_def no_fail_def)
lemma "x << n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_abs_S' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftl_S_abs_S'_def no_fail_def INT_MAX_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32 \<and> 0 \<le> x \<and> x << n \<le> INT_MAX\<rbrace>
         S_shiftl_S_abs_S' (x::int) (n::int)
       \<lbrace>\<lambda>r s. r = x << nat n\<rbrace>!"
  apply (wpsimp simp: S_shiftl_S_abs_S'_def INT_MAX_def shiftl_nat_def shiftl_int_def)
  apply (subst unat_of_int)
    apply simp
   apply (drule le_less_trans[where x="x*2^n" and z="2^32"])
    apply simp
   apply (subst mult_less_cancel_left_pos[where c="2^n", symmetric])
    apply simp
   apply (subst (asm) mult.commute)
   apply (erule less_le_trans)
   apply simp
  apply (simp add: le_unat_uoi[where z="32"])
  apply (simp flip: nat_mult_distrib nat_power_eq nat_numeral)
  done

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftl_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftl_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32))"
  apply (monad_eq simp: S_shiftl_S_no_abs'_def no_fail_def)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>
lemma "sint x << unat n > INT_MAX \<Longrightarrow> \<not> no_fail \<top> (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftl_S_no_abs'_def no_fail_def shiftl_int_def INT_MAX_def
                     nat_int_comparison(2) int_unat_nonneg)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32 \<and> 0 <=s x \<and> sint x << unat n \<le> INT_MAX\<rbrace>
         S_shiftl_S_no_abs' (x::sword32) (n::sword32)
       \<lbrace>\<lambda>r s. r = x << unat n\<rbrace>!"
  by (wpsimp simp: S_shiftl_S_no_abs'_def INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) int_unat_nonneg)


section \<open>Right shifts\<close>

subsection \<open>@{text U_shiftr_U}\<close>

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_U_abs_US' (x :: nat) (n :: nat))"
  by (monad_eq simp: U_shiftr_U_abs_US'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. n < 32\<rbrace> U_shiftr_U_abs_US' (x::nat) (n::nat) \<lbrace>\<lambda>r s. r = x >> n\<rbrace>!"
  by (wpsimp simp: U_shiftr_U_abs_US'_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_U_abs_U' (x :: nat) (n :: nat))"
  by (monad_eq simp: U_shiftr_U_abs_U'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. n < 32\<rbrace> U_shiftr_U_abs_U' (x::nat) (n::nat) \<lbrace>\<lambda>r s. r = x >> n\<rbrace>!"
  by (wpsimp simp: U_shiftr_U_abs_U'_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_U_abs_S' (x :: word32) (n :: word32))"
  by (monad_eq simp: U_shiftr_U_abs_S'_def no_fail_def word_le_not_less)
lemma "\<lbrace>\<lambda>s. n < 32\<rbrace> U_shiftr_U_abs_S' (x::word32) (n::word32) \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: U_shiftr_U_abs_S'_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_U_no_abs' (x :: word32) (n :: word32))"
  by (monad_eq simp: U_shiftr_U_no_abs'_def no_fail_def word_le_not_less)
lemma "\<lbrace>\<lambda>s. n < 32\<rbrace> U_shiftr_U_no_abs' (x::word32) (n::word32) \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: U_shiftr_U_no_abs'_def)

subsection \<open>@{text U_shiftr_S}\<close>

lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_abs_US' (x :: nat) (n :: int))"
  by (monad_eq simp: U_shiftr_S_abs_US'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_abs_US' (x :: nat) (n :: int))"
  by (monad_eq simp: U_shiftr_S_abs_US'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32\<rbrace> U_shiftr_S_abs_US' (x::nat) (n::int) \<lbrace>\<lambda>r s. r = x >> nat n\<rbrace>!"
  by (wpsimp simp: U_shiftr_S_abs_US'_def)

lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_abs_U' (x :: nat) (n :: sword32))"
  by (monad_eq simp: U_shiftr_S_abs_U'_def no_fail_def word_sless_alt word_sle_def)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_abs_U' (x :: nat) (n :: sword32))"
  by (monad_eq simp: U_shiftr_S_abs_U'_def no_fail_def word_sless_alt word_sle_def)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32\<rbrace> U_shiftr_S_abs_U' (x::nat) (n::sword32) \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: U_shiftr_S_abs_U'_def nat_sint word_sle_def word_sless_alt)

lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_abs_S' (x :: word32) (n :: int))"
  by (monad_eq simp: U_shiftr_S_abs_S'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_abs_S' (x :: word32) (n :: int))"
  by (monad_eq simp: U_shiftr_S_abs_S'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32\<rbrace> U_shiftr_S_abs_S' (x::word32) (n::int) \<lbrace>\<lambda>r s. r = x >> nat n\<rbrace>!"
  by (wpsimp simp: U_shiftr_S_abs_S'_def unat_of_int)

lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_no_abs' (x :: word32) (n :: sword32))"
  by (monad_eq simp: U_shiftr_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (U_shiftr_S_no_abs' (x :: word32) (n :: sword32))"
  by (monad_eq simp: U_shiftr_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32\<rbrace> U_shiftr_S_no_abs' (x :: word32) (n :: sword32) \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: U_shiftr_S_no_abs'_def)

subsection \<open>@{text S_shiftr_U}\<close>

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_abs_US' (x :: int) (n :: nat))"
  by (monad_eq simp: S_shiftr_U_abs_US'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_abs_US' (x :: int) (n :: nat))"
  by (monad_eq simp: S_shiftr_U_abs_US'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 \<le> x\<rbrace> S_shiftr_U_abs_US' (x::int) (n::nat) \<lbrace>\<lambda>r s. r = x >> nat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_U_abs_US'_def)

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_abs_U' (x :: sword32) (n :: nat))"
  by (monad_eq simp: S_shiftr_U_abs_U'_def no_fail_def word_sle_def word_sless_alt)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_abs_U' (x :: sword32) (n :: nat))"
  by (monad_eq simp: S_shiftr_U_abs_U'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 <=s x\<rbrace> S_shiftr_U_abs_U' (x::sword32) (n::nat) \<lbrace>\<lambda>r s. r = x >> nat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_U_abs_U'_def)

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_abs_S' (x :: int) (n :: word32))"
  by (monad_eq simp: S_shiftr_U_abs_S'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_abs_S' (x :: int) (n :: word32))"
  by (monad_eq simp: S_shiftr_U_abs_S'_def no_fail_def word_le_nat_alt)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 \<le> x\<rbrace> S_shiftr_U_abs_S' (x::int) (n::word32) \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_U_abs_S'_def word_less_nat_alt)

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_no_abs' (x :: sword32) (n :: word32))"
  by (monad_eq simp: S_shiftr_U_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_U_no_abs' (x :: sword32) (n :: word32))"
  by (monad_eq simp: S_shiftr_U_no_abs'_def no_fail_def word_le_not_less)
lemma "\<lbrace>\<lambda>s. n < 32 \<and> 0 <=s x\<rbrace> S_shiftr_U_no_abs' (x::sword32) (n::word32) \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_U_no_abs'_def)

subsection \<open>@{text S_shiftr_S}\<close>

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_US' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftr_S_abs_US'_def no_fail_def)
lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_US' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftr_S_abs_US'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_US' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftr_S_abs_US'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32 \<and> 0 \<le> x\<rbrace> S_shiftr_S_abs_US' (x::int) (n::int) \<lbrace>\<lambda>r s. r = x >> nat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_S_abs_US'_def)

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_U' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftr_S_abs_U'_def no_fail_def word_sle_def word_sless_alt)
lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_U' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftr_S_abs_U'_def no_fail_def word_sle_def word_sless_alt)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_U' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftr_S_abs_U'_def no_fail_def word_sle_def word_sless_alt)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32 \<and> 0 <=s x\<rbrace>
         S_shiftr_S_abs_U' (x::sword32) (n::sword32)
       \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_S_abs_U'_def)

lemma "x < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_S' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftr_S_abs_S'_def no_fail_def)
lemma "n < 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_S' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftr_S_abs_S'_def no_fail_def)
lemma "n \<ge> 32 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_abs_S' (x :: int) (n :: int))"
  by (monad_eq simp: S_shiftr_S_abs_S'_def no_fail_def)
lemma "\<lbrace>\<lambda>s. 0 \<le> n \<and> n < 32 \<and> 0 \<le> x\<rbrace>
         S_shiftr_S_abs_S' (x::int) (n::int)
       \<lbrace>\<lambda>r s. r = x >> nat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_S_abs_S'_def)

lemma "x <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_no_abs' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftr_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "n <s 0 \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_no_abs' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftr_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "32 <=s n \<Longrightarrow> \<not> no_fail \<top> (S_shiftr_S_no_abs' (x :: sword32) (n :: sword32))"
  by (monad_eq simp: S_shiftr_S_no_abs'_def no_fail_def word_sle_def word_sless_alt)
lemma "\<lbrace>\<lambda>s. 0 <=s n \<and> n <s 32 \<and> 0 <=s x\<rbrace>
         S_shiftr_S_no_abs' (x::sword32) (n::sword32)
       \<lbrace>\<lambda>r s. r = x >> unat n\<rbrace>!"
  by (wpsimp simp: S_shiftr_S_no_abs'_def)

end

end
