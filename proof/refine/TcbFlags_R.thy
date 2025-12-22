(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Lemmas connecting how the design and abstract specifications represent TCB flags.
   That is, bitwise with a word in the design spec and as a set in the abstract spec. *)

theory TcbFlags_R
imports BaseRefine.Include Move_R
begin

lemma ex_tcbFlagToWord_bit:
  "\<exists>n<word_bits. tcbFlagToWord flag = bit n"
  by (force simp: tcbFlagToWord_def word_bits_conv split: tcb_flag.splits simp del: bit_def)

lemma ex_tcbFlagToWord:
  "tcbFlagMask !! n \<Longrightarrow> \<exists>flag. tcbFlagToWord flag = bit n"
  by (auto simp: tcbFlagToWord_def tcbFlagMask_def split: tcb_flag.splits if_splits)

lemma tcbFlagToWord_and_tcbFlagMask_eq:
  "flag \<in> word_to_tcb_flags tcbFlagMask \<Longrightarrow> tcbFlagToWord flag && tcbFlagMask = tcbFlagToWord flag"
  by (cut_tac flag=flag in ex_tcbFlagToWord_bit) (fastforce simp: word_to_tcb_flags_def word_eq_iff)

lemma word_to_tcb_flags_not:
  "word_to_tcb_flags (~~ flags) = word_to_tcb_flags tcbFlagMask - word_to_tcb_flags flags"
  apply (clarsimp simp: word_to_tcb_flags_def intro!: set_eqI)
  apply (cut_tac flag=x in ex_tcbFlagToWord_bit)
  apply (fastforce simp: word_eq_iff)
  done

lemma word_to_tcb_flags_or:
  "word_to_tcb_flags (flags || flags') = word_to_tcb_flags flags \<union> word_to_tcb_flags flags'"
  apply (clarsimp simp: word_to_tcb_flags_def intro!: set_eqI)
  apply (cut_tac flag=x in ex_tcbFlagToWord_bit)
  apply (fastforce simp: word_eq_iff)
  done

lemma word_to_tcb_flags_and:
  "word_to_tcb_flags (flags && flags') = word_to_tcb_flags flags \<inter> word_to_tcb_flags flags'"
  apply (clarsimp simp: word_to_tcb_flags_def intro!: set_eqI)
  apply (cut_tac flag=x in ex_tcbFlagToWord_bit)
  apply (fastforce simp: word_eq_iff)
  done

lemmas word_to_tcb_flags_simps = word_to_tcb_flags_not word_to_tcb_flags_or word_to_tcb_flags_and

lemma word_to_tcb_flags_and_not:
  "flags && tcbFlagMask = flags
   \<Longrightarrow> word_to_tcb_flags (flags && ~~ flags') = word_to_tcb_flags flags - word_to_tcb_flags flags'"
  apply (clarsimp simp: word_to_tcb_flags_def intro!: set_eqI)
  apply (cut_tac flag=x in ex_tcbFlagToWord_bit)
  apply (fastforce simp: word_eq_iff)
  done

lemma word_to_tcb_flags_tcbFlagMask[simp]:
  "word_to_tcb_flags flags \<inter> word_to_tcb_flags tcbFlagMask = word_to_tcb_flags flags"
  apply (clarsimp simp: word_to_tcb_flags_def intro!: set_eqI)
  apply (cut_tac flag=x in ex_tcbFlagToWord_bit)
  apply (fastforce simp: word_eq_iff)
  done

lemma tcb_flags_to_word_id:
  "tcb_flags_to_word (word_to_tcb_flags w) = w && tcbFlagMask"
  unfolding tcb_flags_to_word_def word_to_tcb_flags_def
  apply (rule the_equality; clarsimp simp: Collect_eq word_bw_lcs)
  apply (rule ccontr)
  apply (subst (asm) all_not_ex)
  apply (erule FalseI)
  apply (subst (asm) word_eq_iff)+
  apply clarsimp
  apply (prop_tac "tcbFlagMask !! n")
   apply fastforce
  apply (frule ex_tcbFlagToWord)
  apply clarsimp
  apply (rule_tac x=flag in exI)
  apply (clarsimp simp: not_nth_is_and_eq_0[symmetric] word_bw_assocs[symmetric] word_bw_comms)
  done

lemma isFlagSet_in_word_to_tcb_flags[simp]:
  "flag \<in> word_to_tcb_flags tcbFlagMask \<Longrightarrow> isFlagSet flag flags = (flag \<in> word_to_tcb_flags flags)"
  by (drule tcbFlagToWord_and_tcbFlagMask_eq)
     (clarsimp simp: isFlagSet_def word_to_tcb_flags_def word_bw_lcs intro!: eq_eqI word_bw_comms)

lemma FpuDisabled_in_tcbFlagMask[simp]:
  "config_HAVE_FPU \<Longrightarrow> FpuDisabled \<in> word_to_tcb_flags tcbFlagMask"
  by (clarsimp simp: word_to_tcb_flags_def tcbFlagToWord_def tcbFlagMask_def)

end