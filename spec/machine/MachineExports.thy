(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory MachineExports
imports "./$L4V_ARCH/MachineOps"
begin

context begin interpretation Arch .

(* Check consistency of machine_word and machine_word_len. *)
term "id :: machine_word \<Rightarrow> machine_word_len word"

requalify_types
  machine_word
  machine_word_len
  vmfault_type
  hyp_fault_type
  irq
  ticks
  time

requalify_consts
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
  maxIRQ
  minIRQ
  timerIRQ
  word_size_bits
  clearMemory
  non_kernel_IRQs
  tlsBaseRegister
  configureTimer
  kernelWCET_us
  kernelWCET_ticks
  maxTimer_us
  max_ticks_to_us
  max_us_to_ticks
  MAX_PERIOD_US
  MAX_PERIOD
  us_to_ticks
  ticks_to_us
  setDeadline
  timerPrecision
requalify_facts
  us_to_ticks_mono
  us_to_ticks_zero
  us_to_ticks_nonzero
  kernelWCET_ticks_no_overflow
  MAX_PERIOD_US_def
  MAX_PERIOD_def
  us_to_ticks_mult
  cur_time_bound_no_overflow
  kernelWCET_ticks_def
  replicate_no_overflow
  cur_time_bound_nonzero'
  cur_time_bound_no_overflow'
  cur_time_bound_minus
  cur_time_bound_minus'

(* HERE IS THE PLACE FOR GENERIC WORD LEMMAS FOR ALL ARCHITECTURES *)

lemma Suc_unat_mask_div_obfuscated:
  "Suc (unat (mask sz div (word_size::machine_word))) = 2 ^ (min sz word_bits - word_size_bits)"
  unfolding word_size_bits_def
  by (rule Suc_unat_mask_div)

lemma word_size_size_bits_nat:
  "2^word_size_bits = (word_size :: nat)"
  by (simp add: word_size_bits_def word_size_def)

lemma word_size_size_bits_word:
  "2^word_size_bits = (word_size :: 'a :: len word)"
  by (simp add: word_size_bits_def word_size_def)

end

end
