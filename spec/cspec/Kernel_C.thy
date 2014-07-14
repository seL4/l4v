(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Kernel_C
imports
  "../machine/ARMMachineTypes"
  "../../lib/CTranslationNICTA"
begin

declare [[populate_globals=true]]

type_synonym cghost_state = "(machine_word \<rightharpoonup> vmpage_size) * (machine_word \<rightharpoonup> nat)"

definition
  gs_clear_region :: "word32 \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state" where
  "gs_clear_region ptr bits gs \<equiv>
   (%x. if x \<in> {ptr..+2 ^ bits} then None else fst gs x,
    %x. if x \<in> {ptr..+2 ^ bits} then None else snd gs x)"

definition
  gs_new_frames:: "vmpage_size \<Rightarrow> word32 \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_new_frames sz ptr bits \<equiv> \<lambda>gs.
   if bits < pageBitsForSize sz then gs
   else (\<lambda>x. if \<exists>n\<le>mask (bits - pageBitsForSize sz).
                  x = ptr + n * 2 ^ pageBitsForSize sz then Some sz
             else fst gs x, snd gs)"

definition
  gs_new_cnodes:: "nat \<Rightarrow> word32 \<Rightarrow> nat \<Rightarrow> cghost_state \<Rightarrow> cghost_state"
  where
  "gs_new_cnodes sz ptr bits \<equiv> \<lambda>gs.
   if bits < sz + 4 then gs
   else (fst gs, \<lambda>x. if \<exists>n\<le>mask (bits - sz - 4). x = ptr + n * 2 ^ (sz + 4)
                     then Some sz
                     else snd gs x)"

declare [[record_codegen = false]]
declare [[allow_underscore_idents = true]]

install_C_file "c/kernel_all.c_pp"
  [machinety=machine_state, ghostty=cghost_state]

end
