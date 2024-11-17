(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Utilities for the machine level which are not machine-dependent.
*)

chapter "Machine Accessor Functions"

theory MiscMachine_A
imports Machine_A "ExecSpec.MachineExports"
begin

arch_requalify_types
  user_context
  user_monad

arch_requalify_types (A)
  data
  obj_ref
  asid_high_len
  asid_high_index
  asid_low_len
  asid_low_index
  asid_len
  asid_rep_len
  asid
  cap_ref
  length_type
  vspace_ref

arch_requalify_consts (A)
  nat_to_cref
  msg_info_register
  msg_registers
  cap_register
  badge_register
  frame_registers
  gp_registers
  exception_message
  syscall_message
  new_context
  slot_bits
  oref_to_data
  data_to_oref
  vref_to_data
  data_to_vref
  nat_to_len
  data_to_nat
  data_to_16
  data_to_cptr
  combine_ntfn_badges

(* Needs to be done here after plain type names are exported *)
translations
  (type) "'a user_monad" <= (type) "user_context \<Rightarrow> ('a \<times> user_context) set \<times> bool"

definition
  asid_high_bits :: nat
where
  "asid_high_bits \<equiv> LENGTH(asid_high_len)"

definition
  asid_low_bits :: nat
where
  "asid_low_bits \<equiv> LENGTH(asid_low_len)"

definition
  asid_bits :: nat
where
  "asid_bits \<equiv> LENGTH(asid_len)"

lemmas asid_bits_defs =
  asid_bits_def asid_high_bits_def asid_low_bits_def

(* Sanity checks. *)
lemma asid_bits_len_checks:
  "asid_bits = asid_high_bits + asid_low_bits"
  "asid_bits \<le> LENGTH(asid_rep_len)"
  unfolding asid_bits_defs by auto

definition ipa_size :: nat where
  "ipa_size \<equiv> if config_ARM_PA_SIZE_BITS_40 then 40 else 44"

end
