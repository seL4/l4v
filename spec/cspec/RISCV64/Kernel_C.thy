(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
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
setup {* Context.theory_map (ASM_Ignore_Hooks.add_hook (fn _ => true)) *}

context begin interpretation Arch . global_naming vmpage_size
requalify_consts RISCVSmallPage RISCVLargePage RISCVHugePage
end

definition
  ctcb_size_bits :: nat
where
  "ctcb_size_bits \<equiv> 10" (* FIXME RISCV *)

definition
  ctcb_offset :: "64 word"
where
  "ctcb_offset \<equiv> 2 ^ ctcb_size_bits"

lemmas ctcb_offset_defs = ctcb_offset_def ctcb_size_bits_def

cond_sorry_modifies_proofs SORRY_MODIFIES_PROOFS

install_C_file "../c/build/$L4V_ARCH/kernel_all.c_pp"
  [machinety=machine_state, ghostty=cghost_state]

hide_const
  vmpage_size.RISCVSmallPage
  vmpage_size.RISCVLargePage
  vmpage_size.RISCVHugePage

context Arch begin
global_naming "RISCV.vmpage_size" requalify_consts RISCVSmallPage RISCVLargePage RISCVHugePage
global_naming "RISCV" requalify_consts RISCVSmallPage RISCVLargePage RISCVHugePage
end

end
