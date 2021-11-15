(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory MachineExports
imports MachineOps
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
  gpRegisters
  frameRegisters
  ackInterrupt
  resetTimer
  maxIRQ
  minIRQ
  word_size_bits
  clearMemory
  non_kernel_IRQs
  tlsBaseRegister

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

end
