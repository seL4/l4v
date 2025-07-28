(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory MachineExports
imports MachineOps
begin

(* Check consistency of machine_word and machine_word_len. *)
term "id :: machine_word \<Rightarrow> machine_word_len word"

arch_requalify_types
  vmfault_type
  hyp_fault_type
  irq
  user_monad
  user_context
  ticks_len
  ticks
  time

arch_requalify_consts
  getActiveIRQ
  maskInterrupt
  freeMemory
  loadWord
  storeWord
  storeWordVM
  setNextPC
  getRestartPC
  setRegister
  getRegister
  initContext
  exceptionMessage
  syscallMessage
  timeoutMessage
  gpRegisters
  frameRegisters
  replyRegister
  nbsendRecvDest
  ackInterrupt
  ackDeadlineIRQ
  resetTimer
  getCurrentTime
  minIRQ
  timerIRQ
  clearMemory
  non_kernel_IRQs
  tlsBaseRegister
  debugPrint
  configureTimer
  initL2Cache
  ptrFromPAddr
  pageBits
  configureTimer
  kernelWCET_us
  kernelWCET_ticks
  maxTimer_us
  max_ticks_to_us
  max_us_to_ticks
  MAX_PERIOD_US
  MAX_PERIOD
  ticks_per_timer_unit
  us_to_ticks
  ticks_to_us
  setDeadline
  max_time
  getCurrentTime_buffer
  time_buffer_const
  \<mu>s_in_ms

arch_requalify_facts
  MAX_PERIOD_US_def
  MAX_PERIOD_def
  kernelWCET_ticks_def
  replicate_no_overflow
  getCurrentTime_buffer_nonzero'
  getCurrentTime_buffer_no_overflow'
  MAX_PERIOD_mult
  ticks_per_timer_unit_non_zero
  MIN_BUDGET_bound
  getCurrentTime_buffer_bound
  kernelWCET_pos'
  MIN_BUDGET_pos'
  init_domain_time_pos
  init_domain_time_bound
  getCurrentTime_buffer_pos
  getCurrentTime_buffer_no_overflow
  us_to_ticks_mono
  MIN_BUDGET_helper
  \<mu>s_in_ms_def
  us_to_ticks_helper
  MIN_BUDGET_le_MAX_PERIOD

definition "MAX_RELEASE_TIME = max_time - 5 * MAX_PERIOD"

lemma unat_MAX_RELEASE_TIME:
  "unat MAX_RELEASE_TIME = unat max_time - 5 * unat MAX_PERIOD"
  apply (clarsimp simp: MAX_RELEASE_TIME_def unat_sub MAX_PERIOD_mult)
  done

(* HERE IS THE PLACE FOR GENERIC WORD LEMMAS FOR ALL ARCHITECTURES *)

lemma Suc_unat_mask_div_obfuscated:
  "Suc (unat (mask sz div (word_size::machine_word))) = 2 ^ (min sz word_bits - word_size_bits)"
  by (rule Suc_unat_mask_div)

lemma word_size_size_bits_nat:
  "2^word_size_bits = (word_size :: nat)"
  by (simp add: word_size_bits_def word_size_def)

lemma word_size_size_bits_word:
  "2^word_size_bits = (word_size :: 'a :: len word)"
  by (simp add: word_size_bits_def word_size_def)

end
