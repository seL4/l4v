(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
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

end

declare [[populate_globals=true]]

context begin interpretation Arch . (*FIXME: arch_split*)

type_synonym cghost_state =
  "(machine_word \<rightharpoonup> vmpage_size) * (machine_word \<rightharpoonup> nat) * ghost_assertions *
   (machine_word \<rightharpoonup> nat)"

abbreviation gs_sc_size :: "cghost_state \<Rightarrow> (machine_word \<rightharpoonup> nat)" where
  "gs_sc_size \<equiv> snd \<circ> snd \<circ> snd"

definition
  gs_clear_region :: "addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_clear_region ptr bits gs \<equiv>
   (\<lambda>x. if x \<in> {ptr..+2 ^ bits} then None else fst gs x,
    \<lambda>x. if x \<in> {ptr..+2 ^ bits} then None else fst (snd gs) x,
    fst (snd (snd gs)),
    \<lambda>x. if x \<in> {ptr..+2 ^ bits} then None else gs_sc_size gs x)"

definition
  gs_new_frames:: "vmpage_size \<Rightarrow> addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_new_frames sz ptr bits \<equiv> \<lambda>gs.
   if bits < pageBitsForSize sz then gs
   else (\<lambda>x. if \<exists>n\<le>mask (bits - pageBitsForSize sz).
                  x = ptr + n * 2 ^ pageBitsForSize sz then Some sz
             else fst gs x, snd gs)"

definition
  gs_new_cnodes:: "nat \<Rightarrow> addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_new_cnodes sz ptr bits \<equiv> \<lambda>gs.
   if bits < sz + 4 then gs
   else (fst gs, \<lambda>x. if \<exists>n\<le>mask (bits - sz - 4). x = ptr + n * 2 ^ (sz + 4)
                     then Some sz
                     else fst (snd gs) x, snd (snd gs))"

abbreviation (input) refills_len :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "refills_len userSize struct_size refill_size \<equiv> (2 ^ userSize - struct_size) div refill_size"

definition gs_new_sc_size :: "addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_new_sc_size addr sz \<equiv> \<lambda>(a, b, c, d). (a, b, c, d(addr := Some sz))"

abbreviation
  gs_get_assn :: "int \<Rightarrow> cghost_state \<Rightarrow> machine_word"
  where
  "gs_get_assn k \<equiv> ghost_assertion_data_get k (fst o snd o snd)"

abbreviation
  gs_set_assn :: "int \<Rightarrow> machine_word \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_set_assn k v \<equiv> ghost_assertion_data_set k v (apsnd o apsnd o apfst)"

declare [[record_codegen = false]]
declare [[allow_underscore_idents = true]]

end

(* workaround for the fact that the C parser wants to know the vmpage sizes*)
(* create appropriately qualified aliases *)
context begin interpretation Arch . global_naming vmpage_size
requalify_consts RISCVSmallPage RISCVLargePage RISCVHugePage
end

definition
  ctcb_size_bits :: nat
where
  "ctcb_size_bits \<equiv> 9"

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

(* hide vmpage sizes again *)
hide_const
  vmpage_size.RISCVSmallPage
  vmpage_size.RISCVLargePage
  vmpage_size.RISCVHugePage

(* re-allow fully qualified accesses (for consistency). Slightly clunky *)
context Arch begin
global_naming "RISCV.vmpage_size" requalify_consts RISCVSmallPage RISCVLargePage RISCVHugePage
global_naming "RISCV" requalify_consts RISCVSmallPage RISCVLargePage RISCVHugePage
end

end
