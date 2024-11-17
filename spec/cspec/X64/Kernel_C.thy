(*
 * Copyright 2014, General Dynamics C4 Systems
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

context begin interpretation Arch . (*FIXME: arch-split*)

type_synonym cghost_state = "(machine_word \<rightharpoonup> vmpage_size) * (machine_word \<rightharpoonup> nat)
    * ghost_assertions"

definition
  gs_clear_region :: "addr \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_clear_region ptr bits gs \<equiv>
   (%x. if x \<in> {ptr..+2 ^ bits} then None else fst gs x,
    %x. if x \<in> {ptr..+2 ^ bits} then None else fst (snd gs) x, snd (snd gs))"

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

abbreviation
  gs_get_assn :: "int \<Rightarrow> cghost_state \<Rightarrow> machine_word"
  where
  "gs_get_assn k \<equiv> ghost_assertion_data_get k (snd o snd)"

abbreviation
  gs_set_assn :: "int \<Rightarrow> machine_word \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_set_assn k v \<equiv> ghost_assertion_data_set k v (apsnd o apsnd)"

declare [[record_codegen = false]]
declare [[allow_underscore_idents = true]]

end

(* x86-64 asm statements are not yet supported by the c-parser *)
setup \<open>Context.theory_map (ASM_Ignore_Hooks.add_hook (fn _ => true))\<close>

(* workaround for the fact that the C parser wants to know the vmpage sizes*)
(* create appropriately qualified aliases *)
context begin interpretation Arch . global_naming vmpage_size
requalify_consts X64SmallPage X64LargePage X64HugePage
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
  vmpage_size.X64SmallPage
  vmpage_size.X64LargePage
  vmpage_size.X64HugePage

(* re-allow fully qualified accesses (for consistency). Slightly clunky *)
context Arch begin
global_naming "X64.vmpage_size" requalify_consts X64SmallPage X64LargePage X64HugePage
global_naming "X64" requalify_consts X64SmallPage X64LargePage X64HugePage
end

end
