(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Time
imports
  Kernel_Config \<comment> \<open>currently unnecessary, but added in anticipation of future use\<close>
  Eisbach_Tools.Eisbach_Methods
begin

consts maxTimer_us :: "64 word"
consts max_ticks_to_us :: "64 word"
consts max_us_to_ticks :: "64 word"

type_synonym ticks_len = 64

type_synonym ticks = "ticks_len word"
type_synonym time  = "ticks_len word"

abbreviation max_time :: time where
  "max_time \<equiv> max_word"

definition \<mu>s_in_ms :: "64 word" where
  "\<mu>s_in_ms = 1000"

text \<open> This matches @{text "60 * 60 * MS_IN_S * US_IN_MS"} because it should be in micro-seconds. \<close>
definition MAX_PERIOD_US :: "64 word" where
  "MAX_PERIOD_US \<equiv> 60 * 60 * 1000 * 1000"

\<comment> \<open>The following notepad shows that the axioms introduced below, which provide various results
    about several constants and their conversion via us_to_ticks, are consistent.\<close>

notepad begin

define ticks_per_timer_unit :: "64 word" where "ticks_per_timer_unit = of_nat 50"
define timer_unit :: "64 word" where "timer_unit = of_nat 1"
define kernelWCET_us :: "64 word" where "kernelWCET_us = of_nat 100"
define us_to_ticks :: "64 word \<Rightarrow> 64 word" where
  "us_to_ticks = (\<lambda>us. (us * ticks_per_timer_unit) div timer_unit)"

have kernelWCET_us_pos2: "0 < 2 * kernelWCET_us"
  by (simp add: kernelWCET_us_def)

have MIN_BUDGET_le_MAX_PERIOD: "2 * kernelWCET_us \<le> MAX_PERIOD_US"
  by (simp add: kernelWCET_us_def MAX_PERIOD_US_def)

have ticks_per_timer_unit_non_zero: "ticks_per_timer_unit \<noteq> 0"
  by (simp add: ticks_per_timer_unit_def)

have MIN_BUDGET_bound: "2 * unat kernelWCET_us * unat ticks_per_timer_unit < unat max_time"
  apply (subst unat_max_word[symmetric])
  apply clarsimp
  apply (prop_tac "unat kernelWCET_us \<le> 100")
   apply (fastforce simp: kernelWCET_us_def)
  apply (prop_tac "unat ticks_per_timer_unit \<le> 50")
   apply (fastforce simp: ticks_per_timer_unit_def)
  apply (rule_tac y="10000" in le_less_trans)
   apply (rule_tac j1=200 and l1=50 in order.trans[OF mult_le_mono]; fastforce)
  apply simp
  done

have getCurrentTime_buffer_bound:
  "5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit < unat max_time"
  by (fastforce simp: unat_max_word[symmetric] ticks_per_timer_unit_def MAX_PERIOD_US_def)

have kernelWCET_pos': "0 < us_to_ticks kernelWCET_us"
  apply (clarsimp simp: us_to_ticks_def word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have MIN_BUDGET_pos': "0 < 2 * us_to_ticks kernelWCET_us"
  apply (clarsimp simp: us_to_ticks_def word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have init_domain_time_pos: "0 < us_to_ticks (15 * \<mu>s_in_ms)"
  apply (clarsimp simp: us_to_ticks_def word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: \<mu>s_in_ms_def ticks_per_timer_unit_def timer_unit_def unat_minus_one_word)+
  done

have init_domain_time_bound: "15 * unat \<mu>s_in_ms * unat ticks_per_timer_unit < unat max_time"
  by (subst unat_mult_lem'
      | fastforce simp: \<mu>s_in_ms_def ticks_per_timer_unit_def unat_minus_one_word)+

have getCurrentTime_buffer_pos:
  "0 < 5 * us_to_ticks MAX_PERIOD_US"
  by (fastforce simp: us_to_ticks_def word_less_nat_alt MAX_PERIOD_US_def
                      ticks_per_timer_unit_def timer_unit_def)

end (* notepad *)

consts kernelWCET_us :: ticks

axiomatization where
  kernelWCET_us_pos2: "0 < 2 * kernelWCET_us"
and
  MIN_BUDGET_le_MAX_PERIOD: "2 * kernelWCET_us \<le> MAX_PERIOD_US"

consts ticks_per_timer_unit :: ticks
consts timer_unit :: ticks

definition
  "us_to_ticks us = (us * ticks_per_timer_unit) div timer_unit"

definition
  "ticks_to_us ticks = ticks div (ticks_per_timer_unit div timer_unit)"

axiomatization where
  ticks_per_timer_unit_non_zero: "ticks_per_timer_unit \<noteq> 0"
and
  MIN_BUDGET_bound: "2 * unat kernelWCET_us * unat ticks_per_timer_unit < unat max_time"
and
  \<comment> \<open>the 5 is from time_buffer_const (defined below)\<close>
  getCurrentTime_buffer_bound:
    "5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit < unat max_time"
and
  kernelWCET_pos': "0 < us_to_ticks kernelWCET_us"
and
  MIN_BUDGET_pos': "0 < 2 * us_to_ticks kernelWCET_us"
and
  \<comment> \<open>the 15 is from the domain time of the initial state\<close>
  init_domain_time_pos: "0 < us_to_ticks (15 * \<mu>s_in_ms)"
and
  \<comment> \<open>the 15 is from the domain time of the initial state\<close>
  init_domain_time_bound: "15 * unat \<mu>s_in_ms * unat ticks_per_timer_unit < unat max_time"
and
  \<comment> \<open>the 5 is from time_buffer_const (defined below)\<close>
  getCurrentTime_buffer_pos: "0 < 5 * us_to_ticks MAX_PERIOD_US"

definition "MAX_PERIOD = us_to_ticks MAX_PERIOD_US"

lemma kernelWCET_us_pos:
  "0 < kernelWCET_us"
  using kernelWCET_us_pos2 double_eq_zero_iff word_greater_zero_iff by blast

definition
  "kernelWCET_ticks = us_to_ticks kernelWCET_us"

text \<open>
  It is crucial that time does not overflow, and that overflow does not occur when performing any
  operation which modifies the refill lists. We therefore impose a cap on the time that can be
  returned by getCurrentTime, namely getCurrentTime_buffer. This is chosen to be the greatest word
  t such that if a refill list has its head r_time at t, and satisfies valid_refills, then
  when performing any function which does modify the refill list, overflow does not occur. The
  choice depends heavily on the implementation of refill_budget_check.
 \<close>

abbreviation time_buffer_const where "time_buffer_const \<equiv> 5"

abbreviation (input) getCurrentTime_buffer where
  "getCurrentTime_buffer \<equiv> time_buffer_const * MAX_PERIOD"

lemma replicate_no_overflow:
  "n * unat (a :: ticks) \<le> unat (upper_bound :: ticks)
   \<Longrightarrow> unat (of_nat n * a) = n * unat a"
  by (metis (mono_tags, opaque_lifting) le_unat_uoi of_nat_mult word_unat.Rep_inverse)

lemma kernelWCET_ticks_pos2: "0 < 2 * kernelWCET_ticks"
  apply (simp add: kernelWCET_ticks_def)
  using MIN_BUDGET_pos' by simp

lemma getCurrentTime_buffer_nonzero':
  "0 < getCurrentTime_buffer"
  apply (insert getCurrentTime_buffer_pos)
  apply (clarsimp simp: kernelWCET_ticks_def MAX_PERIOD_def)
  done

lemma us_to_ticks_helper:
  "unat a * unat ticks_per_timer_unit \<le> unat max_time
   \<Longrightarrow> unat (us_to_ticks a) \<le> unat a * unat ticks_per_timer_unit"
  apply (clarsimp simp: us_to_ticks_def)
  apply (subst unat_div | subst unat_mult_lem' | simp)+
  done

lemma getCurrentTime_buffer_no_overflow:
  "5 * unat MAX_PERIOD < unat max_time"
  apply (insert getCurrentTime_buffer_bound)
  apply (rule_tac y=" 5 * unat MAX_PERIOD_US * unat ticks_per_timer_unit" in le_less_trans;
         fastforce intro: us_to_ticks_helper simp: MAX_PERIOD_def)
  done

lemma MAX_PERIOD_mult:
  "(n :: 64 word) \<le> 5 \<Longrightarrow> unat (n * MAX_PERIOD) = unat n * unat MAX_PERIOD"
  apply (insert getCurrentTime_buffer_bound)
  apply (insert replicate_no_overflow[where n="unat n" and a=MAX_PERIOD and upper_bound=max_time, atomized])
  apply (elim impE)
   apply (clarsimp simp: MAX_PERIOD_def)
   apply (prop_tac "unat n \<le> (5 :: nat)")
    apply (clarsimp simp: word_le_nat_alt)
   apply (prop_tac "unat (us_to_ticks MAX_PERIOD_US) \<le> unat MAX_PERIOD_US * unat ticks_per_timer_unit")
  apply (simp add: us_to_ticks_helper)
   apply (prop_tac "5 * (unat MAX_PERIOD_US * unat ticks_per_timer_unit) \<le> unat max_time")
    apply linarith
   apply (metis (no_types, opaque_lifting) le_trans mult.commute mult_le_mono1)
  apply (metis word_unat.Rep_inverse)
  done

lemma getCurrentTime_buffer_no_overflow':
  "5 * unat MAX_PERIOD = unat getCurrentTime_buffer"
  apply (subst unat_mult_lem')
   apply (metis MAX_PERIOD_mult add.left_neutral order_refl unat_plus_simple unat_sum_boundE
                word_zero_le)
  apply (fastforce simp: us_to_ticks_helper)
  done

lemma us_to_ticks_zero:
  "us_to_ticks 0 = 0"
  by (clarsimp simp: us_to_ticks_def)

lemma unat_div_helper:
  "a * ticks_per_timer_unit \<le> b * ticks_per_timer_unit
   \<Longrightarrow> unat (a * ticks_per_timer_unit div timer_unit) \<le> unat (b * ticks_per_timer_unit div timer_unit)"
  by (simp add: div_le_mono unat_div_distrib word_le_nat_alt)

lemma us_to_ticks_mono:
  "\<lbrakk>a \<le> b; unat b * unat ticks_per_timer_unit \<le> unat max_time\<rbrakk>
    \<Longrightarrow> us_to_ticks a \<le> us_to_ticks b"
  apply (simp add: us_to_ticks_def)
  apply (clarsimp simp: word_le_nat_alt)
  apply (rule unat_div_helper)
  apply (clarsimp simp: word_le_nat_alt)
  apply (metis (no_types, opaque_lifting) le_unat_uoi mult_le_mono1 word_arith_nat_defs(2))
  done

lemma divide_le_helper:
  "\<lbrakk>unat a * unat b  \<le> unat (max_word :: 'a :: len word)\<rbrakk>
   \<Longrightarrow> (a :: 'a :: len word) * (b  div c) \<le> a * b div c"
  apply (clarsimp simp: word_le_nat_alt)
  apply (subst unat_div | subst unat_mult_lem')+
  apply (blast intro: div_le_dividend le_trans mult_le_mono2)
  apply (subst unat_div | subst unat_mult_lem' | simp)+
  apply (metis (no_types, opaque_lifting) Groups.mult_ac(3) arith_extra_simps(19) div_by_0
                                          div_le_mono mult_le_mono2 nonzero_mult_div_cancel_left
                                          thd)
  done

lemma MIN_BUDGET_helper:
  "2 * us_to_ticks kernelWCET_us \<le> us_to_ticks (2 * kernelWCET_us)"
  apply (clarsimp simp: us_to_ticks_def)
  apply (insert MIN_BUDGET_bound)
  apply (rule_tac order_trans[OF divide_le_helper])
   apply (subst unat_mult_lem' | simp)+
  apply (simp add: mult.assoc)
  done

definition "MAX_RELEASE_TIME = max_time - 5 * MAX_PERIOD"

lemma unat_MAX_RELEASE_TIME:
  "unat MAX_RELEASE_TIME = unat max_time - 5 * unat MAX_PERIOD"
  by (clarsimp simp: MAX_RELEASE_TIME_def unat_sub MAX_PERIOD_mult)

end