(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Kernel_C
imports
  "ExecSpec.MachineTypes"
  "CLib.CTranslationNICTA"
  "AsmRefine.CommonOps"
begin

external_file
  "../c/build/$L4V_ARCH/kernel_all.c_pp"

context begin interpretation Arch .

requalify_types
  machine_state
  pt_array_len
  vs_array_len

end

declare [[populate_globals=true]]

context begin interpretation Arch . (*FIXME: arch-split*)

(* Sanity checks for array sizes. ptTranslationBits not yet available at definition site. *)
lemma ptTranslationBits_vs_index_bits:
  "ptTranslationBits VSRootPT_T = vs_index_bits"
  by (simp add: ptTranslationBits_def vs_index_bits_def)

(* FIXME AARCH64: this is guaranteed to always succeed even though config_ARM_PA_SIZE_BITS_40
   is unfolded. It'd be nicer if we could also get something symbolic out of value_type, though *)
lemma ptTranslationBits_vs_array_len':
  "2 ^ ptTranslationBits VSRootPT_T = vs_array_len"
  by (simp add: vs_array_len_val ptTranslationBits_vs_index_bits vs_index_bits_def
                Kernel_Config.config_ARM_PA_SIZE_BITS_40_def)

lemmas ptTranslationBits_vs_array_len = ptTranslationBits_vs_array_len'[unfolded vs_array_len_val]

type_synonym cghost_state =
  "(machine_word \<rightharpoonup> vmpage_size) \<times>   \<comment> \<open>Frame sizes\<close>
   (machine_word \<rightharpoonup> nat) \<times>           \<comment> \<open>CNode sizes\<close>
   (machine_word \<rightharpoonup> pt_type) \<times>       \<comment> \<open>PT types\<close>
   ghost_assertions"                 \<comment> \<open>ASMRefine assertions\<close>

definition gs_clear_region :: "addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_clear_region ptr bits gs \<equiv>
     (\<lambda>x. if x \<in> {ptr..+2 ^ bits} then None else fst gs x,
      \<lambda>x. if x \<in> {ptr..+2 ^ bits} then None else fst (snd gs) x,
      \<lambda>x. if x \<in> {ptr..+2 ^ bits} then None else fst (snd (snd gs)) x,
      snd (snd (snd gs)))"

definition gs_new_frames:: "vmpage_size \<Rightarrow> addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_new_frames sz ptr bits \<equiv> \<lambda>gs.
     if bits < pageBitsForSize sz then gs
     else (\<lambda>x. if \<exists>n\<le>mask (bits - pageBitsForSize sz).
                    x = ptr + n * 2 ^ pageBitsForSize sz then Some sz
               else fst gs x, snd gs)"

definition gs_new_cnodes:: "nat \<Rightarrow> addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_new_cnodes sz ptr bits \<equiv> \<lambda>gs.
     if bits < sz + 4 then gs
     else (fst gs, \<lambda>x. if \<exists>n\<le>mask (bits - sz - 4). x = ptr + n * 2 ^ (sz + 4)
                       then Some sz
                       else fst (snd gs) x, snd (snd gs))"

definition gs_new_pt_t:: "pt_type \<Rightarrow> addr \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_new_pt_t pt_t ptr \<equiv>
     \<lambda>gs. (fst gs, fst (snd gs), (fst (snd (snd gs))) (ptr \<mapsto> pt_t), snd (snd (snd gs)))"

abbreviation gs_get_assn :: "int \<Rightarrow> cghost_state \<Rightarrow> machine_word" where
  "gs_get_assn k \<equiv> ghost_assertion_data_get k (snd \<circ> snd \<circ> snd)"

abbreviation gs_set_assn :: "int \<Rightarrow> machine_word \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_set_assn k v \<equiv> ghost_assertion_data_set k v (apsnd \<circ> apsnd \<circ> apsnd)"

declare [[record_codegen = false]]
declare [[allow_underscore_idents = true]]

end

(* Workaround for the fact that the retype annotations need the vmpage sizes*)
(* create appropriately qualified aliases *)
context begin interpretation Arch . global_naming vmpage_size
requalify_consts ARMSmallPage ARMLargePage ARMHugePage
end

(* Also need pt_type constructors for retype annotations. We leave them available globally for C. *)
context begin interpretation Arch .
requalify_consts NormalPT_T VSRootPT_T
end

definition
  ctcb_size_bits :: nat
where
  "ctcb_size_bits \<equiv> 10"

definition
  ctcb_offset :: "64 word"
where
  "ctcb_offset \<equiv> 2 ^ ctcb_size_bits"

lemmas ctcb_offset_defs = ctcb_offset_def ctcb_size_bits_def

cond_sorry_modifies_proofs SORRY_MODIFIES_PROOFS

install_C_file "../c/build/$L4V_ARCH/kernel_all.c_pp"
  [machinety=machine_state, ghostty=cghost_state]

text \<open>Hide unqualified names conflicting with Kernel_Config names. Force use of Kernel_C prefix
  for these:\<close>
hide_const (open)
  numDomains

text \<open>Add a more usable name for the collection of ThreadState definitions\<close>
lemmas ThreadState_defs = StrictC'_thread_state_defs

(* hide vmpage sizes again *)
hide_const
  vmpage_size.ARMSmallPage
  vmpage_size.ARMLargePage
  vmpage_size.ARMHugePage

(* re-allow fully qualified accesses (for consistency). Slightly clunky *)
context Arch begin
global_naming "AARCH64.vmpage_size" requalify_consts ARMSmallPage ARMLargePage ARMHugePage
global_naming "AARCH64" requalify_consts ARMSmallPage ARMLargePage ARMHugePage
end

end
